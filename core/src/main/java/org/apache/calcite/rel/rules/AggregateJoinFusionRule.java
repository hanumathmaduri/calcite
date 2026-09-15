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
import org.apache.calcite.rel.AggregateInputSignature;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.core.Aggregate;
import org.apache.calcite.rel.core.AggregateCall;
import org.apache.calcite.rel.core.Join;
import org.apache.calcite.rel.core.JoinInfo;
import org.apache.calcite.rel.core.JoinRelType;
import org.apache.calcite.rel.core.Project;
import org.apache.calcite.rel.logical.LogicalAggregate;
import org.apache.calcite.rel.logical.LogicalJoin;
import org.apache.calcite.rel.logical.LogicalProject;
import org.apache.calcite.rel.type.RelDataType;
import org.apache.calcite.rex.RexBuilder;
import org.apache.calcite.rex.RexInputRef;
import org.apache.calcite.rex.RexNode;
import org.apache.calcite.tools.RelBuilder;
import org.apache.calcite.util.ImmutableBitSet;
import org.apache.calcite.util.mapping.Mappings;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;

import org.checkerframework.checker.nullness.qual.Nullable;
import org.immutables.value.Value;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Planner rule that operates on two adjacent joins to grouped aggregates and
 * either <b>fuses</b> or <b>transposes</b> them, so that repeated application
 * (to a fix-point) merges all fusable aggregates over a common driver — even
 * when they are interleaved with joins to unrelated tables.
 *
 * <p>The rule matches {@code Join( Join(A, aggB), aggC )} (with an optional
 * projection between the two joins, as produced by decorrelation), where
 * {@code aggB} and {@code aggC} are single-group aggregates joined to the same
 * driver {@code A}, and {@code A} is arbitrary. Given a match it does one of:
 *
 * <ul>
 * <li><b>Fuse</b> — if {@code aggB} and {@code aggC} share an
 *     {@link AggregateInputSignature} (same base relation, same group key) and
 *     the same driver key: merge them into one aggregate carrying both call
 *     sets and collapse the two joins into one.</li>
 * <li><b>Transpose</b> — otherwise, if the pair is out of a canonical order
 *     over their signatures: swap the two joins. Both joins are one-to-one on
 *     the driver (the join key is the unique group key), so they commute and
 *     the swap is result-preserving. Transposing is directional (it only ever
 *     moves toward the canonical order) so repeated application terminates
 *     while bubbling equal-signature aggregates adjacent, at which point the
 *     fuse branch merges them.</li>
 * </ul>
 *
 * <p>This is the aggregate-fusion case of
 * <a href="https://issues.apache.org/jira/browse/CALCITE-5631">[CALCITE-5631]
 * Optimization to merge redundant joins</a>. Both INNER and LEFT joins are
 * handled in any mix; a fused join is INNER if either input join is INNER.
 *
 * @see CoreRules#AGGREGATE_JOIN_FUSION
 */
@Value.Enclosing
public class AggregateJoinFusionRule
    extends RelRule<AggregateJoinFusionRule.Config>
    implements TransformationRule {

  /** Creates an AggregateJoinFusionRule. */
  protected AggregateJoinFusionRule(Config config) {
    super(config);
  }

  @Override public void onMatch(RelOptRuleCall call) {
    final Join topJoin = call.rel(0);
    final Aggregate aggC = call.rel(2);
    final Project payloadC = call.rel(3);
    if (!isInnerOrLeft(topJoin) || !isSimpleSingleGroup(aggC)) {
      return;
    }

    // The top join's left is either a Project over the bottom join (the
    // decorrelated shape) or the bottom join directly (explicit joins).
    final RelNode leftRaw = topJoin.getLeft().stripped();
    final @Nullable Project mid;
    final Join bottomJoin;
    if (leftRaw instanceof Project) {
      mid = (Project) leftRaw;
      for (RexNode e : mid.getProjects()) {
        if (!(e instanceof RexInputRef)) {
          return;
        }
      }
      final RelNode below = mid.getInput().stripped();
      if (!(below instanceof Join)) {
        return;
      }
      bottomJoin = (Join) below;
    } else if (leftRaw instanceof Join) {
      mid = null;
      bottomJoin = (Join) leftRaw;
    } else {
      return;
    }
    if (!isInnerOrLeft(bottomJoin)) {
      return;
    }
    final RelNode aggBnode = bottomJoin.getRight().stripped();
    if (!(aggBnode instanceof Aggregate)) {
      return;
    }
    final Aggregate aggB = (Aggregate) aggBnode;
    if (!isSimpleSingleGroup(aggB)) {
      return;
    }
    final RelNode payloadBnode = aggB.getInput().stripped();
    final @Nullable Project payloadB =
        payloadBnode instanceof Project ? (Project) payloadBnode : null;

    final AggregateInputSignature sigB = AggregateInputSignature.of(aggB);
    final AggregateInputSignature sigC = AggregateInputSignature.of(aggC);
    if (sigB == null || sigC == null) {
      return;
    }

    final RelNode driver = bottomJoin.getLeft().stripped();
    final int driverFieldCount = driver.getRowType().getFieldCount();

    // Both joins must be equi-joins whose right key is the aggregate's group
    // column and whose left key is a driver column.
    final Integer dkB = singleDriverKey(bottomJoin);
    if (dkB == null || dkB >= driverFieldCount) {
      return;
    }
    final Integer topKey = singleDriverKey(topJoin);
    if (topKey == null) {
      return;
    }
    final int dkC = mid != null
        ? refIndex(mid.getProjects().get(topKey)) : topKey;
    if (dkC < 0 || dkC >= driverFieldCount) {
      return; // top join is not on a driver column
    }

    if (sigB.equals(sigC) && dkB.intValue() == dkC) {
      fuse(call, topJoin, mid, bottomJoin, driver, dkB, aggB, payloadB, aggC,
          payloadC);
      return;
    }
    // Transpose only toward a canonical order, so the rewrite terminates.
    final String keyB = sigB + "|dk=" + dkB;
    final String keyC = sigC + "|dk=" + dkC;
    if (keyC.compareTo(keyB) < 0) {
      transpose(call, topJoin, mid, bottomJoin, driver, dkB, dkC, aggB, aggC);
    }
  }

  /** Merges {@code aggB} and {@code aggC} (which share a signature and driver
   * key) into a single aggregate and collapses the two joins into one. */
  private static void fuse(RelOptRuleCall call, Join topJoin,
      @Nullable Project mid, Join bottomJoin, RelNode driver, int driverKey,
      Aggregate aggB, @Nullable Project payloadB, Aggregate aggC,
      @Nullable Project payloadC) {
    final RelBuilder relBuilder = call.builder();
    final RexBuilder rexBuilder = relBuilder.getRexBuilder();
    final RelNode base = AggregateInputSignature.base(aggB);
    final int groupCol = groupBaseColumn(aggB, payloadB);
    if (groupCol < 0) {
      return;
    }

    final List<RexNode> mergedPayload = new ArrayList<>();
    final Map<Integer, Integer> basePos = new HashMap<>();
    mergedPayload.add(rexBuilder.makeInputRef(base, groupCol));
    basePos.put(groupCol, 0);
    final Map<Integer, Integer> argMapB = new HashMap<>();
    final Map<Integer, Integer> argMapC = new HashMap<>();
    if (!registerArgs(aggB, payloadB, base, mergedPayload, basePos, argMapB,
        rexBuilder)
        || !registerArgs(aggC, payloadC, base, mergedPayload, basePos, argMapC,
        rexBuilder)) {
      return;
    }
    final int mergedSize = mergedPayload.size();
    final List<AggregateCall> mergedCalls = new ArrayList<>();
    transformCalls(aggB, payloadB, argMapB, mergedSize, mergedCalls);
    final int callsB = aggB.getAggCallList().size();
    transformCalls(aggC, payloadC, argMapC, mergedSize, mergedCalls);

    final RelNode mergedAggregate = relBuilder.push(base)
        .project(mergedPayload, ImmutableList.of(), true)
        .aggregate(relBuilder.groupKey(ImmutableBitSet.of(0)), mergedCalls)
        .build();

    final JoinRelType fusedType =
        topJoin.getJoinType() == JoinRelType.INNER
            || bottomJoin.getJoinType() == JoinRelType.INNER
            ? JoinRelType.INNER : JoinRelType.LEFT;
    relBuilder.push(driver).push(mergedAggregate);
    final RelNode newJoin =
        relBuilder.join(
            fusedType, relBuilder.equals(relBuilder.field(2, 0, driverKey),
            relBuilder.field(2, 1, 0))).build();

    // newJoin layout: [driver | group, callsB..., callsC...]
    // topJoin layout: [left columns | aggC columns]
    final int midWidth = topJoin.getLeft().getRowType().getFieldCount();
    final Map<Integer, Integer> outMap = new HashMap<>();
    for (int i = 0; i < midWidth; i++) {
      // A left column maps to the same leading position in newJoin (driver and
      // aggB's [group, calls] occupy the same slots).
      outMap.put(i, mid != null
          ? ((RexInputRef) mid.getProjects().get(i)).getIndex() : i);
    }
    outMap.put(midWidth, driverFieldCount(driver)); // aggC group column
    for (int j = 0; j < aggC.getAggCallList().size(); j++) {
      outMap.put(midWidth + 1 + j,
          driverFieldCount(driver) + 1 + callsB + j);
    }
    emit(call, relBuilder, newJoin, topJoin.getRowType(), outMap);
  }

  /** Swaps the two joins so {@code aggC} sits below {@code aggB}; sound because
   * both joins are one-to-one on the driver. */
  private static void transpose(RelOptRuleCall call, Join topJoin,
      @Nullable Project mid, Join bottomJoin, RelNode driver, int dkB, int dkC,
      Aggregate aggB, Aggregate aggC) {
    final RelBuilder relBuilder = call.builder();
    final int dc = driver.getRowType().getFieldCount();
    final int ccols = aggC.getRowType().getFieldCount();

    // Each aggregate keeps its own join type, so column nullability is
    // unchanged and the reproduction below is a pure permutation.
    relBuilder.push(driver).push(aggC);
    final RelNode newBottom =
        relBuilder.join(
            topJoin.getJoinType(), relBuilder.equals(relBuilder.field(2, 0, dkC),
            relBuilder.field(2, 1, 0))).build();
    relBuilder.push(newBottom).push(aggB);
    final RelNode newTop =
        relBuilder.join(
            bottomJoin.getJoinType(), relBuilder.equals(relBuilder.field(2, 0, dkB),
            relBuilder.field(2, 1, 0))).build();

    // newTop layout: [driver | aggC cols | aggB cols]
    // topJoin layout: [left (from driver + aggB) | aggC cols]
    final int midWidth = topJoin.getLeft().getRowType().getFieldCount();
    final Map<Integer, Integer> outMap = new HashMap<>();
    for (int i = 0; i < midWidth; i++) {
      final int x = mid != null
          ? ((RexInputRef) mid.getProjects().get(i)).getIndex() : i;
      outMap.put(i, x < dc ? x : dc + ccols + (x - dc)); // driver keeps; aggB shifts past aggC
    }
    for (int j = 0; j < ccols; j++) {
      outMap.put(midWidth + j, dc + j);
    }
    emit(call, relBuilder, newTop, topJoin.getRowType(), outMap);
  }

  /** Builds the reproduction projection from {@code outMap} (anchor column ->
   * rebuilt column) using {@link RelBuilder#fields}, casts each to the anchor's
   * declared type, and transforms if the row type matches. */
  private static void emit(RelOptRuleCall call, RelBuilder relBuilder,
      RelNode rebuilt, RelDataType anchorType, Map<Integer, Integer> outMap) {
    final RexBuilder rexBuilder = relBuilder.getRexBuilder();
    final Mappings.TargetMapping mapping =
        Mappings.target(outMap, anchorType.getFieldCount(),
            rebuilt.getRowType().getFieldCount());
    final List<RexNode> refs = relBuilder.push(rebuilt).fields(mapping);
    relBuilder.clear();
    final List<RexNode> outProjects = new ArrayList<>();
    for (int k = 0; k < refs.size(); k++) {
      outProjects.add(
          coerce(rexBuilder,
          anchorType.getFieldList().get(k).getType(), refs.get(k)));
    }
    final RelNode result =
        LogicalProject.create(rebuilt, ImmutableList.of(), outProjects,
            anchorType.getFieldNames(), ImmutableSet.of());
    if (RelOptUtil.areRowTypesEqual(result.getRowType(), anchorType, false)) {
      call.transformTo(result);
    }
  }

  private static void transformCalls(Aggregate aggregate,
      @Nullable Project payload, Map<Integer, Integer> argMap, int targetCount,
      List<AggregateCall> out) {
    final Mappings.TargetMapping mapping =
        Mappings.target(argMap, sourceFieldCount(aggregate, payload),
            targetCount);
    for (AggregateCall c : aggregate.getAggCallList()) {
      out.add(c.transform(mapping));
    }
  }

  private static int driverFieldCount(RelNode driver) {
    return driver.getRowType().getFieldCount();
  }

  private static boolean isInnerOrLeft(Join join) {
    return join.getJoinType() == JoinRelType.INNER
        || join.getJoinType() == JoinRelType.LEFT;
  }

  /** Returns whether the aggregate has a single, simple (non-rollup) group
   * column and no grouping sets. */
  private static boolean isSimpleSingleGroup(Aggregate aggregate) {
    return aggregate.getGroupType() == Aggregate.Group.SIMPLE
        && aggregate.getGroupCount() == 1;
  }

  /** Registers, for one aggregate, the base columns referenced by its calls
   * into the merged payload, and records the ordinal remapping. Returns false
   * (bailing) if a call cannot be handled. */
  private static boolean registerArgs(Aggregate aggregate,
      @Nullable Project payload, RelNode base, List<RexNode> mergedPayload,
      Map<Integer, Integer> basePos, Map<Integer, Integer> argMap,
      RexBuilder rexBuilder) {
    for (AggregateCall call : aggregate.getAggCallList()) {
      if (call.filterArg >= 0
          || !call.getCollation().getFieldCollations().isEmpty()
          || !call.rexList.isEmpty()) {
        return false;
      }
      for (int arg : call.getArgList()) {
        if (argMap.containsKey(arg)) {
          continue;
        }
        final int baseCol = payload != null
            ? refIndex(payload.getProjects().get(arg)) : arg;
        if (baseCol < 0) {
          return false;
        }
        Integer pos = basePos.get(baseCol);
        if (pos == null) {
          mergedPayload.add(rexBuilder.makeInputRef(base, baseCol));
          pos = mergedPayload.size() - 1;
          basePos.put(baseCol, pos);
        }
        argMap.put(arg, pos);
      }
    }
    return true;
  }

  /** Returns the single driver-side key of an equi-join whose right key is the
   * right input's first (group) column, or null if the join is not of that
   * shape. */
  private static @Nullable Integer singleDriverKey(Join join) {
    final JoinInfo joinInfo = join.analyzeCondition();
    if (!joinInfo.isEqui() || joinInfo.leftKeys.size() != 1
        || joinInfo.rightKeys.get(0) != 0) {
      return null;
    }
    return joinInfo.leftKeys.get(0);
  }

  /** Casts a reference to the exact target type (e.g. to widen a non-null
   * column to nullable) so it matches the reproduced output row type. */
  private static RexNode coerce(RexBuilder rexBuilder, RelDataType target,
      RexNode ref) {
    return ref.getType().equals(target) ? ref : rexBuilder.makeCast(target, ref);
  }

  /** Returns the index of a {@link RexInputRef}, or -1 if the node is not one. */
  private static int refIndex(RexNode node) {
    return node instanceof RexInputRef ? ((RexInputRef) node).getIndex() : -1;
  }

  /** Returns the base column the aggregate's single group key resolves to. */
  private static int groupBaseColumn(Aggregate aggregate,
      @Nullable Project payload) {
    final int g = aggregate.getGroupSet().nth(0);
    return payload != null ? refIndex(payload.getProjects().get(g)) : g;
  }

  /** Returns the field count of the relation an aggregate's calls index into. */
  private static int sourceFieldCount(Aggregate aggregate,
      @Nullable Project payload) {
    return payload != null
        ? payload.getRowType().getFieldCount()
        : aggregate.getInput().getRowType().getFieldCount();
  }

  /** Rule configuration. */
  @Value.Immutable
  public interface Config extends RelRule.Config {
    Config DEFAULT = ImmutableAggregateJoinFusionRule.Config.of()
        .withOperandSupplier(b0 ->
            b0.operand(LogicalJoin.class)
                .predicate(j -> j.getJoinType() == JoinRelType.INNER
                    || j.getJoinType() == JoinRelType.LEFT)
                .inputs(
                    b1 -> b1.operand(RelNode.class).anyInputs(),
                    b2 -> b2.operand(LogicalAggregate.class)
                        .oneInput(b3 -> b3.operand(LogicalProject.class)
                            .anyInputs())));

    @Override default AggregateJoinFusionRule toRule() {
      return new AggregateJoinFusionRule(this);
    }
  }
}
