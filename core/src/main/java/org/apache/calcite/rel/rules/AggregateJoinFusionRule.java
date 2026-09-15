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
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Planner rule that fuses sibling {@link Aggregate}s that appear as the right
 * inputs of a left-deep chain (a "spine") of joins to a common driver, when
 * they compute over the same base relation and group by the same key.
 * Aggregates sharing a {@link AggregateInputSignature signature} and driver key
 * are merged into a single aggregate carrying all their calls, so the spine
 * keeps one join per distinct computation.
 *
 * <p>This is the aggregate-fusion case of
 * <a href="https://issues.apache.org/jira/browse/CALCITE-5631">[CALCITE-5631]
 * Optimization to merge redundant joins</a>. It arises when several correlated
 * scalar sub-queries over the same table are decorrelated into separate grouped
 * aggregates joined to the driver, or when a query joins explicitly to several
 * grouped sub-queries of the same table.
 *
 * <p>For example
 *
 * <blockquote><pre>{@code
 * SELECT (SELECT sum(a) FROM t WHERE t.k = s.id),
 *        (SELECT sum(b) FROM t WHERE t.k = s.id)
 * FROM s
 * }</pre></blockquote>
 *
 * <p>becomes a single {@code s LEFT JOIN Agg(t GROUP BY k, sum(a), sum(b))}.
 * Because the rule scans the whole spine, fusable aggregates are merged even
 * when <em>interleaved</em> with joins to unrelated tables.
 *
 * <p>Both {@link JoinRelType#INNER INNER} and {@link JoinRelType#LEFT LEFT}
 * joins are handled in any mix. Because the aggregates in a group share a key
 * set, the fused join is {@code INNER} if any of the group's joins is
 * {@code INNER} (all drop exactly the same driver rows) and {@code LEFT}
 * otherwise. The join key is the unique group key, so every join is one-to-one
 * on the driver; the joins therefore commute and the merge changes neither
 * cardinality nor values.
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
    final Join anchor = call.rel(0);

    // 1. Walk the left spine from the anchor, collecting each join, its right
    //    aggregate rib, that aggregate's payload projection, and the (all-ref)
    //    projection on the join's left (null when absent). Stop at the driver.
    final List<Join> joins = new ArrayList<>();
    final List<Aggregate> aggs = new ArrayList<>();
    final List<@Nullable Project> payloads = new ArrayList<>();
    final List<@Nullable Project> mids = new ArrayList<>();
    @Nullable RelNode driver = null;
    Join cur = anchor;
    for (;;) {
      if (!isInnerOrLeft(cur)) {
        return;
      }
      final RelNode right = cur.getRight().stripped();
      if (!(right instanceof Aggregate)) {
        return;
      }
      final Aggregate agg = (Aggregate) right;
      if (!isSimpleSingleGroup(agg)) {
        return;
      }
      final RelNode payloadNode = agg.getInput().stripped();
      joins.add(cur);
      aggs.add(agg);
      payloads.add(payloadNode instanceof Project ? (Project) payloadNode : null);
      final RelNode left = cur.getLeft().stripped();
      if (left instanceof Project) {
        final Project p = (Project) left;
        for (RexNode e : p.getProjects()) {
          if (!(e instanceof RexInputRef)) {
            return;
          }
        }
        final RelNode below = p.getInput().stripped();
        if (!(below instanceof Join)) {
          return;
        }
        mids.add(p);
        cur = (Join) below;
      } else if (left instanceof Join) {
        mids.add(null);
        cur = (Join) left;
      } else {
        mids.add(null);
        driver = left;
        break;
      }
    }
    if (driver == null || joins.size() < 2) {
      return;
    }
    final int n = joins.size();
    // Reorder bottom-to-top: index 0 is the join whose left is the driver.
    Collections.reverse(joins);
    Collections.reverse(aggs);
    Collections.reverse(payloads);
    Collections.reverse(mids);

    final int driverFieldCount = driver.getRowType().getFieldCount();

    // 2. Simulate the spine bottom-up, tracking the origin of every output
    //    column (driver column, or (rib, column)); trace each join's driver key
    //    back to a driver column.
    List<int[]> sources = new ArrayList<>(); // {ribLevel or -1 for driver, col}
    for (int c = 0; c < driverFieldCount; c++) {
      sources.add(new int[] {-1, c});
    }
    final int[] driverKey = new int[n];
    final Integer key0 = singleDriverKey(joins.get(0));
    if (key0 == null) {
      return;
    }
    driverKey[0] = key0;
    addRibColumns(sources, 0, aggs.get(0).getRowType().getFieldCount());
    for (int i = 1; i < n; i++) {
      final Project mid = mids.get(i);
      List<int[]> acc = sources;
      if (mid != null) {
        final List<int[]> next = new ArrayList<>();
        for (RexNode e : mid.getProjects()) {
          next.add(acc.get(((RexInputRef) e).getIndex()));
        }
        acc = next;
      }
      final Integer ki = singleDriverKey(joins.get(i));
      if (ki == null) {
        return;
      }
      final int[] src = acc.get(ki);
      if (src[0] != -1) {
        return; // join is not on a driver column
      }
      driverKey[i] = src[1];
      addRibColumns(acc, i, aggs.get(i).getRowType().getFieldCount());
      sources = acc;
    }
    if (sources.size() != anchor.getRowType().getFieldCount()) {
      return;
    }

    // 3. Bucket ribs by (signature, driver key).
    final AggregateInputSignature[] signatures = new AggregateInputSignature[n];
    final Map<String, List<Integer>> buckets = new LinkedHashMap<>();
    for (int i = 0; i < n; i++) {
      signatures[i] = AggregateInputSignature.of(aggs.get(i));
      if (signatures[i] == null) {
        return;
      }
      buckets.computeIfAbsent(signatures[i] + "|dk=" + driverKey[i],
          k -> new ArrayList<>()).add(i);
    }
    if (buckets.values().stream().noneMatch(g -> g.size() >= 2)) {
      return; // nothing to fuse
    }

    final RelBuilder relBuilder = call.builder();
    final RexBuilder rexBuilder = relBuilder.getRexBuilder();

    // 4. Build one (merged) aggregate per bucket. Track, per rib level, its
    //    bucket's rebuilt column offset and the position of its calls.
    final int[] levelBucketStart = new int[n]; // rebuilt col of the bucket group
    final int[] levelCallStart = new int[n];   // rib's first call index in bucket
    final List<RelNode> bucketAggs = new ArrayList<>();
    final List<Integer> bucketDriverKey = new ArrayList<>();
    final List<JoinRelType> bucketJoinType = new ArrayList<>();
    final List<Integer> bucketWidth = new ArrayList<>();

    for (Map.Entry<String, List<Integer>> entry : buckets.entrySet()) {
      final List<Integer> members = entry.getValue();
      final int first = members.get(0);
      final RelNode bucketAgg;
      final int width;
      final JoinRelType joinType;
      if (members.size() == 1) {
        // Singleton: keep the original aggregate and its join type.
        bucketAgg = aggs.get(first);
        width = aggs.get(first).getRowType().getFieldCount();
        levelCallStart[first] = 0;
        joinType = joins.get(first).getJoinType() == JoinRelType.INNER
            ? JoinRelType.INNER : JoinRelType.LEFT;
      } else {
        final RelNode base = AggregateInputSignature.base(aggs.get(first));
        final int groupCol = groupBaseColumn(aggs.get(first), payloads.get(first));
        if (groupCol < 0) {
          return;
        }
        final List<RexNode> mergedPayload = new ArrayList<>();
        final Map<Integer, Integer> basePos = new HashMap<>();
        mergedPayload.add(rexBuilder.makeInputRef(base, groupCol));
        basePos.put(groupCol, 0);

        final List<Map<Integer, Integer>> argMaps = new ArrayList<>();
        int running = 0;
        JoinRelType jt = JoinRelType.LEFT;
        for (int m : members) {
          final Map<Integer, Integer> argMap = new HashMap<>();
          if (!registerArgs(aggs.get(m), payloads.get(m), base, mergedPayload,
              basePos, argMap, rexBuilder)) {
            return;
          }
          argMaps.add(argMap);
          levelCallStart[m] = running;
          running += aggs.get(m).getAggCallList().size();
          if (joins.get(m).getJoinType() == JoinRelType.INNER) {
            jt = JoinRelType.INNER;
          }
        }
        final int mergedSize = mergedPayload.size();
        final List<AggregateCall> mergedCalls = new ArrayList<>();
        for (int idx = 0; idx < members.size(); idx++) {
          final int m = members.get(idx);
          final int srcCount = sourceFieldCount(aggs.get(m), payloads.get(m));
          final Mappings.TargetMapping map =
              Mappings.target(argMaps.get(idx), srcCount, mergedSize);
          for (AggregateCall c : aggs.get(m).getAggCallList()) {
            mergedCalls.add(c.transform(map));
          }
        }
        bucketAgg = relBuilder.push(base)
            .project(mergedPayload, ImmutableList.of(), true)
            .aggregate(relBuilder.groupKey(ImmutableBitSet.of(0)), mergedCalls)
            .build();
        width = 1 + running;
        joinType = jt;
      }
      bucketAggs.add(bucketAgg);
      bucketDriverKey.add(driverKey[first]);
      bucketJoinType.add(joinType);
      bucketWidth.add(width);
    }

    // Compute each bucket's rebuilt column offset and record per-level starts.
    int offset = driverFieldCount;
    int b = 0;
    for (Map.Entry<String, List<Integer>> entry : buckets.entrySet()) {
      for (int m : entry.getValue()) {
        levelBucketStart[m] = offset;
      }
      offset += bucketWidth.get(b);
      b++;
    }

    // 5. Rebuild the spine: driver joined once per bucket.
    relBuilder.push(driver);
    for (int i = 0; i < bucketAggs.size(); i++) {
      relBuilder.push(bucketAggs.get(i));
      final RexNode condition =
          relBuilder.equals(relBuilder.field(2, 0, bucketDriverKey.get(i)),
              relBuilder.field(2, 1, 0));
      relBuilder.join(bucketJoinType.get(i), condition);
    }
    final RelNode rebuilt = relBuilder.build();

    // 6. Reproduce the anchor's output columns from the rebuilt spine. Each
    //    anchor column maps to a rebuilt column: a driver column keeps its
    //    index; a rib's group column lands at its bucket's start; a rib's
    //    measure lands after the bucket group and the calls of earlier members.
    //    The map is expressed as a Mappings.TargetMapping so the reference list
    //    is built with the standard RelBuilder.fields idiom.
    final RelDataType anchorType = anchor.getRowType();
    final Map<Integer, Integer> outMap = new HashMap<>();
    for (int k = 0; k < sources.size(); k++) {
      final int[] src = sources.get(k);
      outMap.put(k, src[0] == -1 ? src[1]
          : src[1] == 0 ? levelBucketStart[src[0]]
          : levelBucketStart[src[0]] + 1 + levelCallStart[src[0]] + (src[1] - 1));
    }
    final Mappings.TargetMapping outMapping =
        Mappings.target(outMap, sources.size(),
            rebuilt.getRowType().getFieldCount());
    final List<RexNode> refs = relBuilder.push(rebuilt).fields(outMapping);
    relBuilder.clear();

    // A per-column cast restores the anchor's declared types (e.g. widening a
    // now-non-null column back to nullable). The projection's row type is
    // derived from these expressions, so the check below genuinely validates
    // the reconstruction column-by-column instead of trivially holding.
    final List<RexNode> outProjects = new ArrayList<>();
    for (int k = 0; k < refs.size(); k++) {
      outProjects.add(
          coerce(rexBuilder,
          anchorType.getFieldList().get(k).getType(), refs.get(k)));
    }
    final RelNode result =
        LogicalProject.create(rebuilt, ImmutableList.of(), outProjects,
            anchorType.getFieldNames(), ImmutableSet.of());
    if (!RelOptUtil.areRowTypesEqual(result.getRowType(), anchorType, false)) {
      return;
    }
    call.transformTo(result);
  }

  private static void addRibColumns(List<int[]> sources, int level, int count) {
    for (int rc = 0; rc < count; rc++) {
      sources.add(new int[] {level, rc});
    }
  }

  /** Casts a reference to the exact target type (e.g. to widen a non-null
   * column to nullable) so it matches the reproduced output row type. */
  private static RexNode coerce(RexBuilder rexBuilder, RelDataType target,
      RexNode ref) {
    return ref.getType().equals(target) ? ref : rexBuilder.makeCast(target, ref);
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
        // With a payload projection, an argument is a projected column
        // reference; without one the aggregate is directly over the base.
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
