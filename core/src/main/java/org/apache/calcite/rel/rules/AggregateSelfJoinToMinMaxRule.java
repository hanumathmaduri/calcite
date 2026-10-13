/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to you under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.apache.calcite.rel.rules;

import org.apache.calcite.plan.RelOptRuleCall;
import org.apache.calcite.plan.RelOptUtil;
import org.apache.calcite.plan.RelRule;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.core.Aggregate;
import org.apache.calcite.rel.core.AggregateCall;
import org.apache.calcite.rel.core.Filter;
import org.apache.calcite.rel.core.Join;
import org.apache.calcite.rel.core.JoinRelType;
import org.apache.calcite.rel.core.Project;
import org.apache.calcite.rel.logical.LogicalAggregate;
import org.apache.calcite.rel.logical.LogicalJoin;
import org.apache.calcite.rel.logical.LogicalProject;
import org.apache.calcite.rel.type.RelDataType;
import org.apache.calcite.rex.RexCall;
import org.apache.calcite.rex.RexInputRef;
import org.apache.calcite.rex.RexLiteral;
import org.apache.calcite.rex.RexNode;
import org.apache.calcite.rex.RexPermuteInputsShuttle;
import org.apache.calcite.rex.RexUtil;
import org.apache.calcite.sql.SqlKind;
import org.apache.calcite.sql.type.SqlTypeUtil;
import org.apache.calcite.tools.RelBuilder;
import org.apache.calcite.util.ImmutableBitSet;
import org.apache.calcite.util.mapping.IntPair;
import org.apache.calcite.util.mapping.Mappings;

import org.checkerframework.checker.nullness.qual.Nullable;
import org.immutables.value.Value;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Planner rule that replaces an inner self-{@link Join} whose condition
 * equates key columns and compares a value, when consumed by an operator that
 * ignores duplicates, with a single grouped scan that compares the extrema of
 * the value.
 *
 * <p>For example, the sub-query in TPC-DS query 95,
 *
 * <blockquote><pre>
 * SELECT DISTINCT ws1.ws_order_number
 * FROM web_sales ws1, web_sales ws2
 * WHERE ws1.ws_order_number = ws2.ws_order_number
 *   AND ws1.ws_warehouse_sk &lt;&gt; ws2.ws_warehouse_sk</pre></blockquote>
 *
 * <p>becomes
 *
 * <blockquote><pre>
 * SELECT ws_order_number
 * FROM web_sales
 * WHERE ws_order_number IS NOT NULL
 * GROUP BY ws_order_number
 * HAVING MIN(ws_warehouse_sk) &lt;&gt; MAX(ws_warehouse_sk)</pre></blockquote>
 *
 * <p>Within a group of rows that share the key, a pair of rows with
 * {@code v1 <> v2} (or {@code v1 < v2}, or {@code v1 > v2}) exists if and only
 * if the group has two distinct non-null values of {@code v}, that is, if
 * {@code MIN(v) <> MAX(v)}. A pair with {@code v1 IS DISTINCT FROM v2} exists
 * if, in addition, the group may have a null and a non-null value. Without
 * such a strict comparison, every row pairs with itself, so the self-join
 * reduces to a filter: a key qualifies if some row with that key has non-null
 * operands of the {@code <=}, {@code >=} and {@code =} comparisons. Keys
 * compared by {@code =} reject nulls; keys compared by
 * {@code IS NOT DISTINCT FROM} match them, as {@code GROUP BY} does.
 *
 * <p>The rewrite preserves the set of key values but not their
 * multiplicities (the join produces a row per qualifying pair), so the rule
 * requires a consumer that ignores duplicates. Each configuration matches one
 * such consumer, in the shapes that {@link SubQueryRemoveRule} and the
 * decorrelators produce for {@code IN}, {@code EXISTS} and {@code NOT IN}:
 *
 * <ul>
 * <li>{@link Config#DEFAULT}: an {@link Aggregate} on the self-join that
 *     groups by key columns and computes nothing but {@code LITERAL_AGG};</li>
 * <li>{@link Config#EXISTENCE}: a semi-, anti- or mark-join (which uses its
 *     right input only to test existence) whose right input is the
 *     self-join;</li>
 * <li>{@link Config#EXISTENCE_PROJECT}: as {@code EXISTENCE}, but the right
 *     input is a projection of the self-join;</li>
 * <li>{@link Config#EXISTENCE_BELOW_JOIN}: as {@code EXISTENCE_PROJECT}, but
 *     the self-join is joined to another relation below the projection (as in
 *     the second {@code IN} of TPC-DS query 95).</li>
 * </ul>
 *
 * <p>When an {@code Aggregate} consumer is above a join of the self-join with
 * another relation, {@link CoreRules#AGGREGATE_JOIN_TRANSPOSE_EXTENDED}
 * pushes it down to the self-join.
 *
 * <p>The rule requires that:
 *
 * <ul>
 * <li>both inputs are the same relational expression, ignoring filters that
 *     only require key columns compared by {@code =} to be not null;</li>
 * <li>each conjunct of the join condition compares a key column of the left
 *     input with the same column of the right input, or a deterministic
 *     expression of the left input with the same expression of the right
 *     input;</li>
 * <li>there is at most one strict comparison ({@code <>}, {@code <},
 *     {@code >} or {@code IS DISTINCT FROM}), and if there is one, no other
 *     comparison of expressions;</li>
 * <li>key columns and compared expressions have types with a total order
 *     consistent with equality (so approximate numeric types are excluded);
 *     </li>
 * <li>the consumer uses only key columns of the self-join.</li>
 * </ul>
 *
 * @see CoreRules#AGGREGATE_SELF_JOIN_TO_MIN_MAX
 * @see CoreRules#EXISTENCE_SELF_JOIN_TO_MIN_MAX
 * @see CoreRules#EXISTENCE_PROJECT_SELF_JOIN_TO_MIN_MAX
 * @see CoreRules#EXISTENCE_BELOW_JOIN_SELF_JOIN_TO_MIN_MAX
 */
@Value.Enclosing
public class AggregateSelfJoinToMinMaxRule
    extends RelRule<AggregateSelfJoinToMinMaxRule.Config>
    implements TransformationRule {

  /** Creates an AggregateSelfJoinToMinMaxRule. */
  protected AggregateSelfJoinToMinMaxRule(Config config) {
    super(config);
  }

  @Override public void onMatch(RelOptRuleCall call) {
    if (call.rel(0) instanceof Aggregate) {
      onMatchAggregate(call);
    } else if (call.rels.length == 7) {
      onMatchExistenceBelowJoin(call);
    } else {
      onMatchExistence(call);
    }
  }

  /** Handles an {@link Aggregate} on a self-join whose calls (if any) are
   * all {@code LITERAL_AGG}, replacing the aggregate. */
  private static void onMatchAggregate(RelOptRuleCall call) {
    final Aggregate aggregate = call.rel(0);
    final Join join = call.rel(1);
    final RelBuilder b = call.builder();
    if (!minMax(b, join, aggregate.getGroupSet().asList())) {
      return;
    }
    if (!aggregate.getAggCallList().isEmpty()) {
      // A LITERAL_AGG has the same value for every group.
      final List<RexNode> projects = new ArrayList<>(b.fields());
      for (AggregateCall aggCall : aggregate.getAggCallList()) {
        projects.add(aggCall.rexList.get(0));
      }
      b.project(projects);
    }
    b.rename(aggregate.getRowType().getFieldNames())
        .convert(aggregate.getRowType(), false);
    call.transformTo(b.build());
  }

  /** Returns whether an aggregate call is a {@code LITERAL_AGG}, whose value
   * does not depend on how many rows are in the group. */
  private static boolean isLiteralAgg(AggregateCall aggCall) {
    return aggCall.getAggregation().getKind() == SqlKind.LITERAL_AGG
        && aggCall.getArgList().isEmpty()
        && aggCall.filterArg < 0
        && aggCall.rexList.size() == 1
        && aggCall.rexList.get(0) instanceof RexLiteral;
  }

  /** Handles a join that uses its right input only for existence (semi-,
   * anti- or mark-join) whose right input is a self-join, or a projection of
   * one, replacing the right input with the distinct values of the columns
   * that the join condition references. */
  private static void onMatchExistence(RelOptRuleCall call) {
    final Join existenceJoin = call.rel(0);
    final RelNode right = call.rel(2);
    final @Nullable Project project =
        right instanceof Project ? (Project) right : null;
    final Join join = project != null ? call.rel(3) : (Join) right;
    if (!existenceJoin.getVariablesSet().isEmpty()) {
      return;
    }
    final int leftCount = existenceJoin.getLeft().getRowType().getFieldCount();
    final int rightCount = right.getRowType().getFieldCount();
    final List<Integer> usedRight =
        RelOptUtil.InputFinder.bits(existenceJoin.getCondition())
            .get(leftCount, leftCount + rightCount).shift(-leftCount).asList();
    if (usedRight.isEmpty()) {
      return;
    }
    final List<Integer> columns = new ArrayList<>();
    final Map<Integer, Integer> map = new HashMap<>();
    for (int i = 0; i < leftCount; i++) {
      map.put(i, i);
    }
    for (int i : usedRight) {
      final int column;
      if (project == null) {
        column = i;
      } else {
        final RexNode e = project.getProjects().get(i);
        if (!(e instanceof RexInputRef)) {
          return;
        }
        column = ((RexInputRef) e).getIndex();
      }
      map.put(leftCount + i, leftCount + columns.size());
      columns.add(column);
    }
    final RelBuilder b = call.builder();
    if (!minMax(b, join, columns)) {
      return;
    }
    final RelNode newRight = b.build();
    final Mappings.TargetMapping mapping =
        Mappings.target(map, leftCount + rightCount,
            leftCount + columns.size());
    final RexNode condition =
        existenceJoin.getCondition().accept(
            new RexPermuteInputsShuttle(mapping, existenceJoin.getLeft(),
                newRight));
    b.push(existenceJoin.getLeft())
        .push(newRight)
        .join(existenceJoin.getJoinType(), condition)
        .convert(existenceJoin.getRowType(), false);
    call.transformTo(b.build());
  }

  /** Handles a join that uses its right input only for existence whose right
   * input is a projection of an inner join, one of whose inputs is a
   * projection of a self-join (the expansion of
   * {@code x IN (SELECT a.c FROM a, (self-join) w WHERE a.k = w.k)} by the
   * top-down decorrelator). Replaces the self-join with a relation that has
   * the same set of values of the columns that are used above it; this is
   * valid because the existence join depends only on the set of values that
   * its condition references. */
  private static void onMatchExistenceBelowJoin(RelOptRuleCall call) {
    final Join existenceJoin = call.rel(0);
    final Project topProject = call.rel(2);
    final Join join = call.rel(3);
    final Project selfProject = call.rel(5);
    final Join selfJoin = call.rel(6);
    if (!existenceJoin.getVariablesSet().isEmpty()
        || !join.getVariablesSet().isEmpty()) {
      return;
    }
    final RelNode outer = existenceJoin.getLeft();
    final RelNode other = join.getLeft();
    final int outerCount = outer.getRowType().getFieldCount();
    final int topCount = topProject.getRowType().getFieldCount();
    final int otherCount = other.getRowType().getFieldCount();
    final int joinCount = join.getRowType().getFieldCount();

    // Columns of the top projection that the existence join uses, and the
    // columns of the inner join that they and its condition use.
    final List<Integer> usedTop =
        RelOptUtil.InputFinder.bits(existenceJoin.getCondition())
            .get(outerCount, outerCount + topCount).shift(-outerCount)
            .asList();
    final ImmutableBitSet.Builder usedJoinBuilder =
        RelOptUtil.InputFinder.bits(join.getCondition()).rebuild();
    for (int i : usedTop) {
      final RexNode e = topProject.getProjects().get(i);
      if (!(e instanceof RexInputRef)) {
        return;
      }
      usedJoinBuilder.set(((RexInputRef) e).getIndex());
    }
    final List<Integer> usedSelf =
        usedJoinBuilder.build().get(otherCount, joinCount).shift(-otherCount)
            .asList();
    if (usedTop.isEmpty() || usedSelf.isEmpty()) {
      return;
    }
    final List<Integer> selfColumns = new ArrayList<>();
    for (int i : usedSelf) {
      final RexNode e = selfProject.getProjects().get(i);
      if (!(e instanceof RexInputRef)) {
        return;
      }
      selfColumns.add(((RexInputRef) e).getIndex());
    }
    final RelBuilder b = call.builder();
    if (!minMax(b, selfJoin, selfColumns)) {
      return;
    }
    final RelNode newSelf = b.build();

    // Inner join: "other" unchanged, used self-join columns compacted.
    final Map<Integer, Integer> joinMap = new HashMap<>();
    for (int i = 0; i < otherCount; i++) {
      joinMap.put(i, i);
    }
    for (int j = 0; j < usedSelf.size(); j++) {
      joinMap.put(otherCount + usedSelf.get(j), otherCount + j);
    }
    final Mappings.TargetMapping joinMapping =
        Mappings.target(joinMap, joinCount, otherCount + usedSelf.size());
    final RelNode newJoin = b.push(other).push(newSelf)
        .join(JoinRelType.INNER,
            join.getCondition().accept(
                new RexPermuteInputsShuttle(joinMapping, other, newSelf)))
        .build();

    // Top projection: only the columns that the existence join uses.
    final List<RexNode> topProjects = new ArrayList<>();
    final Map<Integer, Integer> existenceMap = new HashMap<>();
    for (int i = 0; i < outerCount; i++) {
      existenceMap.put(i, i);
    }
    b.push(newJoin);
    for (int i : usedTop) {
      final int column =
          ((RexInputRef) topProject.getProjects().get(i)).getIndex();
      existenceMap.put(outerCount + i, outerCount + topProjects.size());
      topProjects.add(b.field(joinMapping.getTarget(column)));
    }
    final RelNode newRight = b.project(topProjects).build();
    final Mappings.TargetMapping existenceMapping =
        Mappings.target(existenceMap, outerCount + topCount,
            outerCount + usedTop.size());
    b.push(outer)
        .push(newRight)
        .join(existenceJoin.getJoinType(),
            existenceJoin.getCondition().accept(
                new RexPermuteInputsShuttle(existenceMapping, outer,
                    newRight)))
        .convert(existenceJoin.getRowType(), false);
    call.transformTo(b.build());
  }

  /** If {@code join} is a self-join of the required shape and each of
   * {@code columns} (ordinals of the join's output) is a key column, pushes
   * onto {@code b} the set of distinct values of {@code columns} over
   * qualifying pairs, and returns true; otherwise leaves {@code b} unchanged
   * and returns false. */
  private static boolean minMax(RelBuilder b, Join join,
      List<Integer> columns) {
    final int fieldCount = join.getLeft().getRowType().getFieldCount();
    if (!join.getVariablesSet().isEmpty()
        || join.getRight().getRowType().getFieldCount() != fieldCount) {
      return false;
    }

    // Classify each conjunct as a key equality, a strict inequality (which a
    // row cannot satisfy when paired with itself) or a reflexive inequality
    // (which any row whose operand is not null satisfies when paired with
    // itself).
    // Keys compared by "=" reject nulls; keys compared by
    // "IS NOT DISTINCT FROM" match nulls, as GROUP BY does.
    final ImmutableBitSet.Builder keyBuilder = ImmutableBitSet.builder();
    final ImmutableBitSet.Builder nullSafeKeyBuilder = ImmutableBitSet.builder();
    @Nullable RexNode strict = null;
    boolean strictNullSafe = false;
    final List<RexNode> reflexive = new ArrayList<>();
    int reflexiveCount = 0;
    // SqlToRelConverter expands "a IS DISTINCT FROM b" to
    // "(a IS NOT NULL OR b IS NOT NULL) AND (a = b) IS NOT TRUE".
    final List<RexNode> eitherNotNull = new ArrayList<>();
    final List<RexNode> notEqualOrNull = new ArrayList<>();
    for (RexNode conjunct : RelOptUtil.conjunctions(join.getCondition())) {
      final SqlKind kind = conjunct.getKind();
      switch (kind) {
      case OR:
        final RexNode e0 = eitherNotNull((RexCall) conjunct, fieldCount);
        if (e0 == null) {
          return false;
        }
        eitherNotNull.add(e0);
        continue;
      case IS_NOT_TRUE:
        final RexNode operand = ((RexCall) conjunct).getOperands().get(0);
        final RexNode e1 = operand.getKind() == SqlKind.EQUALS
            ? selfExpression((RexCall) operand, fieldCount) : null;
        if (e1 == null) {
          return false;
        }
        notEqualOrNull.add(e1);
        continue;
      default:
        break;
      }
      switch (kind) {
      case EQUALS:
      case IS_NOT_DISTINCT_FROM:
        final IntPair pair = selfColumnPair(conjunct, fieldCount);
        if (pair != null && pair.source == pair.target) {
          (kind == SqlKind.EQUALS ? keyBuilder : nullSafeKeyBuilder)
              .set(pair.source);
          break;
        }
        // Equality of an expression (not a column) is reflexive, like "<="
        // fall through
      case LESS_THAN_OR_EQUAL:
      case GREATER_THAN_OR_EQUAL:
        final RexNode e = selfExpression((RexCall) conjunct, fieldCount);
        if (e == null) {
          return false;
        }
        ++reflexiveCount;
        if (kind != SqlKind.IS_NOT_DISTINCT_FROM) {
          reflexive.add(e); // holds for a row and itself unless e is null
        }
        break;
      case NOT_EQUALS:
      case LESS_THAN:
      case GREATER_THAN:
      case IS_DISTINCT_FROM:
        if (strict != null) {
          return false; // a second inequality need not hold on the same pair
        }
        strict = selfExpression((RexCall) conjunct, fieldCount);
        if (strict == null) {
          return false;
        }
        strictNullSafe = kind == SqlKind.IS_DISTINCT_FROM;
        break;
      default:
        return false;
      }
    }
    if (!eitherNotNull.equals(notEqualOrNull) || eitherNotNull.size() > 1) {
      return false;
    }
    if (!eitherNotNull.isEmpty()) {
      if (strict != null) {
        return false; // a second inequality need not hold on the same pair
      }
      strict = eitherNotNull.get(0);
      strictNullSafe = true;
    }
    final ImmutableBitSet nullRejectingKeys = keyBuilder.build();
    final ImmutableBitSet keys =
        nullRejectingKeys.union(nullSafeKeyBuilder.build());
    if (keys.isEmpty()
        || strict != null && reflexiveCount > 0
        || strict != null && !hasTotalOrder(strict.getType())
        || !reflexive.stream().allMatch(e -> hasTotalOrder(e.getType()))
        || !keys.asList().stream().allMatch(key ->
            hasTotalOrder(
                join.getLeft().getRowType().getFieldList().get(key)
                    .getType()))) {
      return false;
    }

    // Both inputs must be the same relation, ignoring filters that only
    // reject null keys (which the key equality rejects anyway).
    final RelNode input = stripKeysNotNull(join.getLeft(), nullRejectingKeys);
    if (!input.deepEquals(
        stripKeysNotNull(join.getRight(), nullRejectingKeys))) {
      return false;
    }

    // Each output column must be a key column (from either side of the join,
    // as the two are equal).
    final List<Integer> keyColumns = new ArrayList<>();
    for (int i : columns) {
      final int column = i < fieldCount ? i : i - fieldCount;
      if (!keys.get(column)) {
        return false;
      }
      keyColumns.add(column);
    }

    b.push(input);
    // The join's equality rejects null keys; their group must not survive.
    final List<RexNode> notNulls = new ArrayList<>();
    for (int key : nullRejectingKeys) {
      notNulls.add(b.isNotNull(b.field(key)));
    }
    if (strict == null) {
      // Without a strict inequality, a row paired with itself qualifies if
      // and only if its keys and reflexive operands are not null.
      for (RexNode e : reflexive) {
        notNulls.add(b.isNotNull(e));
      }
      b.filter(notNulls);
      final List<RexNode> projects = new ArrayList<>();
      for (int column : keyColumns) {
        projects.add(b.field(column));
      }
      b.project(projects).distinct();
      return true;
    }
    b.filter(notNulls);
    final int keyCount = keys.cardinality();
    if (strictNullSafe) {
      // "IS DISTINCT FROM" also holds between null and a non-null value:
      // two distinct non-null values, or a null and a non-null value.
      b.aggregate(b.groupKey(keys), b.min(strict), b.max(strict),
          b.countStar(null), b.count(strict));
      final RexNode countStar = b.field(keyCount + 2);
      final RexNode count = b.field(keyCount + 3);
      b.filter(
          b.or(b.notEquals(b.field(keyCount), b.field(keyCount + 1)),
              b.and(b.greaterThan(count, b.literal(0)),
                  b.greaterThan(countStar, count))));
    } else {
      b.aggregate(b.groupKey(keys), b.min(strict), b.max(strict));
      b.filter(b.notEquals(b.field(keyCount), b.field(keyCount + 1)));
    }
    final List<RexNode> projects = new ArrayList<>();
    for (int column : keyColumns) {
      projects.add(b.field(keys.indexOf(column)));
    }
    b.project(projects);
    if (!ImmutableBitSet.of(keyColumns).equals(keys)) {
      b.distinct(); // a subset of the keys
    }
    return true;
  }

  /** Returns the input of {@code rel} if it is a {@link Filter} that only
   * requires some of {@code keys} to be not null, otherwise {@code rel}. */
  private static RelNode stripKeysNotNull(RelNode rel, ImmutableBitSet keys) {
    final RelNode stripped = rel.stripped();
    if (!(stripped instanceof Filter)) {
      return rel;
    }
    final Filter filter = (Filter) stripped;
    for (RexNode conjunct : RelOptUtil.conjunctions(filter.getCondition())) {
      if (conjunct.getKind() != SqlKind.IS_NOT_NULL) {
        return rel;
      }
      final RexNode operand = ((RexCall) conjunct).getOperands().get(0);
      if (!(operand instanceof RexInputRef)
          || !keys.get(((RexInputRef) operand).getIndex())) {
        return rel;
      }
    }
    return filter.getInput();
  }

  /** Returns the pair (left column, right column) if {@code node} is a binary
   * comparison between a column of the left input and a column of the right
   * input of a join whose inputs each have {@code fieldCount} fields, or null
   * otherwise. */
  private static @Nullable IntPair selfColumnPair(RexNode node,
      int fieldCount) {
    if (!(node instanceof RexCall)) {
      return null;
    }
    final List<RexNode> operands = ((RexCall) node).getOperands();
    if (operands.size() != 2
        || !(operands.get(0) instanceof RexInputRef)
        || !(operands.get(1) instanceof RexInputRef)) {
      return null;
    }
    final int i0 = ((RexInputRef) operands.get(0)).getIndex();
    final int i1 = ((RexInputRef) operands.get(1)).getIndex();
    if (i0 < fieldCount && i1 >= fieldCount) {
      return IntPair.of(i0, i1 - fieldCount);
    }
    if (i1 < fieldCount && i0 >= fieldCount) {
      return IntPair.of(i1, i0 - fieldCount);
    }
    return null;
  }

  /** Returns {@code e} if {@code call} compares a deterministic expression
   * {@code e} of the left input with the same expression of the right input
   * of a join whose inputs each have {@code fieldCount} fields, or null
   * otherwise. */
  private static @Nullable RexNode selfExpression(RexCall call,
      int fieldCount) {
    return selfExpression(call.getOperands().get(0),
        call.getOperands().get(1), fieldCount);
  }

  /** As {@link #selfExpression(RexCall, int)}, for two operands. */
  private static @Nullable RexNode selfExpression(RexNode e0, RexNode e1,
      int fieldCount) {
    final ImmutableBitSet left = ImmutableBitSet.range(fieldCount);
    final ImmutableBitSet bits0 = RelOptUtil.InputFinder.bits(e0);
    final ImmutableBitSet bits1 = RelOptUtil.InputFinder.bits(e1);
    if (bits0.isEmpty() || bits1.isEmpty()
        || !RexUtil.isDeterministic(e0)) {
      return null;
    }
    if (left.contains(bits0) && !bits1.intersects(left)) {
      return RexUtil.shift(e1, -fieldCount).equals(e0) ? e0 : null;
    }
    if (left.contains(bits1) && !bits0.intersects(left)) {
      return RexUtil.shift(e0, -fieldCount).equals(e1) ? e1 : null;
    }
    return null;
  }

  /** Returns {@code e} if {@code call} is
   * {@code e(left) IS NOT NULL OR e(right) IS NOT NULL} for a deterministic
   * expression {@code e} of the inputs of a join whose inputs each have
   * {@code fieldCount} fields, or null otherwise. */
  private static @Nullable RexNode eitherNotNull(RexCall call,
      int fieldCount) {
    final List<RexNode> operands = call.getOperands();
    if (operands.size() != 2
        || operands.get(0).getKind() != SqlKind.IS_NOT_NULL
        || operands.get(1).getKind() != SqlKind.IS_NOT_NULL) {
      return null;
    }
    return selfExpression(((RexCall) operands.get(0)).getOperands().get(0),
        ((RexCall) operands.get(1)).getOperands().get(0), fieldCount);
  }

  /** Returns whether values of a type are totally ordered consistently with
   * equality, so that "two distinct values exist" iff {@code MIN <> MAX}. */
  private static boolean hasTotalOrder(RelDataType type) {
    return SqlTypeUtil.isExactNumeric(type)
        || SqlTypeUtil.isCharacter(type)
        || SqlTypeUtil.isBinary(type)
        || SqlTypeUtil.isDatetime(type)
        || SqlTypeUtil.isInterval(type)
        || SqlTypeUtil.isBoolean(type);
  }

  /** Rule configuration. */
  @Value.Immutable
  public interface Config extends RelRule.Config {
    Config DEFAULT = ImmutableAggregateSelfJoinToMinMaxRule.Config.of()
        .withOperandFor(LogicalAggregate.class, LogicalJoin.class);

    /** Configuration for a join that uses its right input only for existence
     * (semi-, anti- or mark-join) whose right input is an inner self-join. */
    Config EXISTENCE = ImmutableAggregateSelfJoinToMinMaxRule.Config.of()
        .withDescription("AggregateSelfJoinToMinMaxRule(Existence)")
        .withOperandSupplier(b0 ->
            b0.operand(LogicalJoin.class)
                .predicate(join -> !join.getJoinType().projectsRight())
                .inputs(b1 -> b1.operand(RelNode.class).anyInputs(),
                    b2 -> b2.operand(LogicalJoin.class)
                        .predicate(join ->
                            join.getJoinType() == JoinRelType.INNER)
                        .anyInputs()))
        .as(Config.class);

    /** As {@link #EXISTENCE}, but the right input is a projection of the
     * self-join. */
    Config EXISTENCE_PROJECT = ImmutableAggregateSelfJoinToMinMaxRule.Config.of()
        .withDescription("AggregateSelfJoinToMinMaxRule(ExistenceProject)")
        .withOperandSupplier(b0 ->
            b0.operand(LogicalJoin.class)
                .predicate(join -> !join.getJoinType().projectsRight())
                .inputs(b1 -> b1.operand(RelNode.class).anyInputs(),
                    b2 -> b2.operand(LogicalProject.class)
                        .oneInput(b3 -> b3.operand(LogicalJoin.class)
                            .predicate(join ->
                                join.getJoinType() == JoinRelType.INNER)
                            .anyInputs())))
        .as(Config.class);

    /** Configuration for a join that uses its right input only for existence
     * whose right input is a projection of an inner join whose right input is
     * a projection of a self-join. */
    Config EXISTENCE_BELOW_JOIN =
        ImmutableAggregateSelfJoinToMinMaxRule.Config.of()
            .withDescription("AggregateSelfJoinToMinMaxRule(ExistenceBelowJoin)")
            .withOperandSupplier(b0 ->
                b0.operand(LogicalJoin.class)
                    .predicate(join -> !join.getJoinType().projectsRight())
                    .inputs(b1 -> b1.operand(RelNode.class).anyInputs(),
                        b2 -> b2.operand(LogicalProject.class)
                            .oneInput(b3 -> b3.operand(LogicalJoin.class)
                                .predicate(join ->
                                    join.getJoinType() == JoinRelType.INNER)
                                .inputs(b4 -> b4.operand(RelNode.class)
                                        .anyInputs(),
                                    b5 -> b5.operand(LogicalProject.class)
                                        .oneInput(b6 ->
                                            b6.operand(LogicalJoin.class)
                                                .predicate(join ->
                                                    join.getJoinType()
                                                        == JoinRelType.INNER)
                                                .anyInputs())))))
            .as(Config.class);

    @Override default AggregateSelfJoinToMinMaxRule toRule() {
      return new AggregateSelfJoinToMinMaxRule(this);
    }

    /** Defines an operand tree for the given classes. */
    default Config withOperandFor(Class<? extends Aggregate> aggregateClass,
        Class<? extends Join> joinClass) {
      return withOperandSupplier(b0 ->
          b0.operand(aggregateClass)
              .predicate(aggregate ->
                  aggregate.getAggCallList().stream()
                      .allMatch(AggregateSelfJoinToMinMaxRule::isLiteralAgg)
                      && aggregate.getGroupType() == Aggregate.Group.SIMPLE
                      && !aggregate.getGroupSet().isEmpty())
              .oneInput(b1 ->
                  b1.operand(joinClass)
                      .predicate(join ->
                          join.getJoinType() == JoinRelType.INNER)
                      .anyInputs()))
          .as(Config.class);
    }
  }
}
