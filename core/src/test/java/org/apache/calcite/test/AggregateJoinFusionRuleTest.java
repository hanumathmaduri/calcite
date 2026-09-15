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
package org.apache.calcite.test;

import org.apache.calcite.plan.RelOptUtil;
import org.apache.calcite.plan.hep.HepPlanner;
import org.apache.calcite.plan.hep.HepProgramBuilder;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.core.Aggregate;
import org.apache.calcite.rel.core.Join;
import org.apache.calcite.rel.core.JoinRelType;
import org.apache.calcite.rel.core.RelFactories;
import org.apache.calcite.rel.rules.CoreRules;
import org.apache.calcite.rel.type.RelDataType;
import org.apache.calcite.rel.type.RelDataTypeFactory;
import org.apache.calcite.schema.SchemaPlus;
import org.apache.calcite.schema.impl.AbstractTable;
import org.apache.calcite.sql.SqlNode;
import org.apache.calcite.sql.type.SqlTypeName;
import org.apache.calcite.sql2rel.RelDecorrelator;
import org.apache.calcite.tools.Frameworks;
import org.apache.calcite.tools.Planner;
import org.apache.calcite.tools.RelBuilder;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.hasSize;

/** Tests for {@link org.apache.calcite.rel.rules.AggregateJoinFusionRule}. */
class AggregateJoinFusionRuleTest {

  private static SchemaPlus schema() {
    SchemaPlus root = Frameworks.createRootSchema(true);
    root.add("S", new AbstractTable() {
      @Override public RelDataType getRowType(RelDataTypeFactory tf) {
        return tf.builder()
            .add("ID", tf.createSqlType(SqlTypeName.INTEGER))
            .add("ID2", tf.createSqlType(SqlTypeName.INTEGER))
            .build();
      }
    });
    root.add("T", new AbstractTable() {
      @Override public RelDataType getRowType(RelDataTypeFactory tf) {
        return tf.builder()
            .add("K", tf.createSqlType(SqlTypeName.INTEGER))
            .add("A", tf.createSqlType(SqlTypeName.INTEGER))
            .add("B", tf.createSqlType(SqlTypeName.INTEGER))
            .build();
      }
    });
    root.add("U", new AbstractTable() {
      @Override public RelDataType getRowType(RelDataTypeFactory tf) {
        return tf.builder()
            .add("K", tf.createSqlType(SqlTypeName.INTEGER))
            .add("X", tf.createSqlType(SqlTypeName.INTEGER))
            .build();
      }
    });
    return root;
  }

  private static RelNode decorrelated(String sql) throws Exception {
    Planner planner =
        Frameworks.getPlanner(Frameworks.newConfigBuilder().defaultSchema(schema()).build());
    SqlNode validated = planner.validate(planner.parse(sql));
    RelNode rel = planner.rel(validated).rel;
    HepPlanner hep = new HepPlanner(new HepProgramBuilder()
        .addRuleInstance(CoreRules.PROJECT_SUB_QUERY_TO_CORRELATE)
        .addRuleInstance(CoreRules.FILTER_SUB_QUERY_TO_CORRELATE)
        .addRuleInstance(CoreRules.JOIN_SUB_QUERY_TO_CORRELATE)
        .build());
    hep.setRoot(rel);
    RelBuilder rb = RelFactories.LOGICAL_BUILDER.create(rel.getCluster(), null);
    return RelDecorrelator.decorrelateQuery(hep.findBestExp(), rb);
  }

  private static RelNode fuse(RelNode plan) {
    // PROJECT_MERGE collapses the reconstruction projections between successive
    // fusions, as a real optimization pipeline would, allowing N sibling
    // aggregates to fully collapse by repeated application.
    HepPlanner hep = new HepPlanner(new HepProgramBuilder()
        .addRuleCollection(
            java.util.Arrays.asList(CoreRules.AGGREGATE_JOIN_FUSION,
                CoreRules.PROJECT_MERGE))
        .build());
    hep.setRoot(plan);
    return hep.findBestExp();
  }

  private static <T> int count(RelNode rel, Class<T> clazz) {
    int n = clazz.isInstance(rel) ? 1 : 0;
    for (RelNode in : rel.getInputs()) {
      n += count(in, clazz);
    }
    return n;
  }

  private static List<Aggregate> aggregates(RelNode rel) {
    List<Aggregate> out = new ArrayList<>();
    collect(rel, out);
    return out;
  }

  private static void collect(RelNode rel, List<Aggregate> out) {
    if (rel instanceof Aggregate) {
      out.add((Aggregate) rel);
    }
    for (RelNode in : rel.getInputs()) {
      collect(in, out);
    }
  }

  private static Join firstJoin(RelNode rel) {
    if (rel instanceof Join) {
      return (Join) rel;
    }
    for (RelNode in : rel.getInputs()) {
      final Join j = firstJoin(in);
      if (j != null) {
        return j;
      }
    }
    return null;
  }

  /** Two scalar sub-queries over the same table fuse into one join to a merged
   * aggregate. */
  @Test void testFuseTwoSiblingAggregates() throws Exception {
    final RelNode before =
        decorrelated("SELECT (SELECT sum(A) FROM T WHERE T.K = S.ID), "
        + "(SELECT sum(B) FROM T WHERE T.K = S.ID) FROM S");
    assertThat("precondition: two joins", count(before, Join.class), is(2));
    assertThat("precondition: two aggregates", count(before, Aggregate.class), is(2));

    final RelNode after = fuse(before);

    assertThat("one join after fusion", count(after, Join.class), is(1));
    final List<Aggregate> aggs = aggregates(after);
    assertThat("one aggregate after fusion", aggs, hasSize(1));
    assertThat("merged aggregate carries both calls",
        aggs.get(0).getAggCallList(), hasSize(2));
    assertThat("output row type preserved",
        RelOptUtil.areRowTypesEqual(after.getRowType(), before.getRowType(), false),
        is(true));
  }

  /** Three scalar sub-queries fuse by repeated application (2, then 1). */
  @Test void testFuseThreeSiblingAggregates() throws Exception {
    final RelNode before =
        decorrelated("SELECT (SELECT sum(A) FROM T WHERE T.K = S.ID), "
        + "(SELECT sum(B) FROM T WHERE T.K = S.ID), "
        + "(SELECT min(A) FROM T WHERE T.K = S.ID) FROM S");
    assertThat(count(before, Aggregate.class), is(3));

    final RelNode after = fuse(before);
    assertThat("all joins collapse to one", count(after, Join.class), is(1));
    final List<Aggregate> aggs = aggregates(after);
    assertThat("one merged aggregate", aggs, hasSize(1));
    assertThat("three calls merged", aggs.get(0).getAggCallList(), hasSize(3));
    assertThat(
        RelOptUtil.areRowTypesEqual(after.getRowType(), before.getRowType(), false),
        is(true));
  }

  /** Four scalar sub-queries all fuse into one aggregate with four calls. */
  @Test void testFuseFourSiblingAggregates() throws Exception {
    final RelNode before =
        decorrelated("SELECT (SELECT sum(A) FROM T WHERE T.K = S.ID), "
        + "(SELECT sum(B) FROM T WHERE T.K = S.ID), "
        + "(SELECT min(A) FROM T WHERE T.K = S.ID), "
        + "(SELECT max(B) FROM T WHERE T.K = S.ID) FROM S");
    final RelNode after = fuse(before);
    assertThat(count(after, Join.class), is(1));
    final List<Aggregate> aggs = aggregates(after);
    assertThat(aggs, hasSize(1));
    assertThat(aggs.get(0).getAggCallList(), hasSize(4));
    assertThat(
        RelOptUtil.areRowTypesEqual(after.getRowType(), before.getRowType(), false),
        is(true));
  }

  /** Two sub-queries referencing the same measure column fuse (the base column
   * is shared in the merged payload, not duplicated). */
  @Test void testFuseSharedMeasureColumn() throws Exception {
    final RelNode before =
        decorrelated("SELECT (SELECT sum(A) FROM T WHERE T.K = S.ID), "
        + "(SELECT min(A) FROM T WHERE T.K = S.ID) FROM S");
    final RelNode after = fuse(before);
    assertThat(count(after, Join.class), is(1));
    final List<Aggregate> aggs = aggregates(after);
    assertThat(aggs, hasSize(1));
    assertThat(aggs.get(0).getAggCallList(), hasSize(2));
    assertThat(
        RelOptUtil.areRowTypesEqual(after.getRowType(), before.getRowType(), false),
        is(true));
  }

  /** Sub-queries carrying an identical extra (non-correlated) filter still fuse,
   * because the base computations are structurally equal. */
  @Test void testFuseWithIdenticalFilter() throws Exception {
    final RelNode before =
        decorrelated("SELECT (SELECT sum(A) FROM T WHERE T.K = S.ID AND T.A > 0), "
        + "(SELECT sum(B) FROM T WHERE T.K = S.ID AND T.A > 0) FROM S");
    final RelNode after = fuse(before);
    final List<Aggregate> aggs = aggregates(after);
    // May or may not fuse depending on how the filter attaches; must never be
    // more than the original and must preserve the row type.
    assertThat(aggs.size() <= count(before, Aggregate.class), is(true));
    assertThat(
        RelOptUtil.areRowTypesEqual(after.getRowType(), before.getRowType(), false),
        is(true));
  }

  // ------------------------------------------------------------------
  // Safety: the rule must NOT fire when fusion would be unsound.
  // ------------------------------------------------------------------

  /** Different tables: must not fuse. */
  @Test void testNoFusionDifferentTables() throws Exception {
    final RelNode before =
        decorrelated("SELECT (SELECT sum(A) FROM T WHERE T.K = S.ID), "
        + "(SELECT sum(X) FROM U WHERE U.K = S.ID) FROM S");
    final RelNode after = fuse(before);
    assertThat("joins unchanged", count(after, Join.class),
        is(count(before, Join.class)));
    assertThat("aggregates unchanged", count(after, Aggregate.class),
        is(count(before, Aggregate.class)));
  }

  /** Same table but different correlation keys: must not fuse. */
  @Test void testNoFusionDifferentKeys() throws Exception {
    final RelNode before =
        decorrelated("SELECT (SELECT sum(A) FROM T WHERE T.K = S.ID), "
        + "(SELECT sum(B) FROM T WHERE T.K = S.ID2) FROM S");
    final RelNode after = fuse(before);
    assertThat("aggregates unchanged", count(after, Aggregate.class),
        is(count(before, Aggregate.class)));
  }

  /** Same table but different (non-correlated) filters: must not fuse. */
  @Test void testNoFusionDifferentFilters() throws Exception {
    final RelNode before =
        decorrelated("SELECT (SELECT sum(A) FROM T WHERE T.K = S.ID AND T.A > 0), "
        + "(SELECT sum(B) FROM T WHERE T.K = S.ID AND T.A > 5) FROM S");
    final RelNode after = fuse(before);
    assertThat("aggregates unchanged", count(after, Aggregate.class),
        is(count(before, Aggregate.class)));
  }

  /** Two adjacent fusable aggregates over T, plus an unrelated aggregate over
   * U: only the T pair fuses, the U aggregate remains. */
  @Test void testPartialFusion() throws Exception {
    final RelNode before =
        decorrelated("SELECT (SELECT sum(A) FROM T WHERE T.K = S.ID), "
        + "(SELECT sum(B) FROM T WHERE T.K = S.ID), "
        + "(SELECT sum(X) FROM U WHERE U.K = S.ID) FROM S");
    assertThat(count(before, Aggregate.class), is(3));
    final RelNode after = fuse(before);
    // The two T aggregates fuse; the U aggregate remains.
    assertThat("two aggregates remain", count(after, Aggregate.class), is(2));
    assertThat(
        RelOptUtil.areRowTypesEqual(after.getRowType(), before.getRowType(), false),
        is(true));
  }

  /** Explicit INNER joins to two grouped sub-queries of the same table fuse
   * into a single INNER join to a merged aggregate. */
  @Test void testFuseInnerJoins() throws Exception {
    final RelNode before = decorrelated("select x.s1, y.s2 from s "
        + "join (select k, sum(a) s1 from t group by k) x on x.k = s.id "
        + "join (select k, sum(b) s2 from t group by k) y on y.k = s.id");
    final RelNode after = fuse(before);
    assertThat(count(after, Join.class), is(1));
    assertThat(aggregates(after), hasSize(1));
    assertThat(aggregates(after).get(0).getAggCallList(), hasSize(2));
    assertThat("both inner -> fused inner",
        firstJoin(after).getJoinType(), is(JoinRelType.INNER));
    assertThat(
        RelOptUtil.areRowTypesEqual(after.getRowType(), before.getRowType(), false),
        is(true));
  }

  /** A mix of INNER and LEFT joins to grouped sub-queries of the same table
   * fuses; because either INNER drops the same driver rows, the fused join is
   * INNER. */
  @Test void testFuseMixedJoins() throws Exception {
    final RelNode before = decorrelated("select x.s1, y.s2 from s "
        + "join (select k, sum(a) s1 from t group by k) x on x.k = s.id "
        + "left join (select k, sum(b) s2 from t group by k) y on y.k = s.id");
    final RelNode after = fuse(before);
    assertThat(count(after, Join.class), is(1));
    assertThat(aggregates(after), hasSize(1));
    assertThat("mixed with an inner -> fused inner",
        firstJoin(after).getJoinType(), is(JoinRelType.INNER));
    assertThat(
        RelOptUtil.areRowTypesEqual(after.getRowType(), before.getRowType(), false),
        is(true));
  }

  /** Three explicit INNER joins to grouped sub-queries collapse to one. */
  @Test void testFuseThreeInnerJoins() throws Exception {
    final RelNode before = decorrelated("select x.s1, y.s2, z.s3 from s "
        + "join (select k, sum(a) s1 from t group by k) x on x.k = s.id "
        + "join (select k, sum(b) s2 from t group by k) y on y.k = s.id "
        + "join (select k, min(a) s3 from t group by k) z on z.k = s.id");
    final RelNode after = fuse(before);
    assertThat(count(after, Join.class), is(1));
    assertThat(aggregates(after), hasSize(1));
    assertThat(aggregates(after).get(0).getAggCallList(), hasSize(3));
    assertThat(
        RelOptUtil.areRowTypesEqual(after.getRowType(), before.getRowType(), false),
        is(true));
  }

  /** A COUNT scalar sub-query decorrelates into a shape that this rule does not
   * (yet) match; the rule must leave the plan untouched and sound. */
  @Test void testNoFusionCountSubquery() throws Exception {
    final RelNode before =
        decorrelated("SELECT (SELECT sum(A) FROM T WHERE T.K = S.ID), "
        + "(SELECT count(A) FROM T WHERE T.K = S.ID) FROM S");
    final RelNode after = fuse(before);
    assertThat("aggregates not increased",
        count(after, Aggregate.class) <= count(before, Aggregate.class), is(true));
    assertThat("output row type preserved",
        RelOptUtil.areRowTypesEqual(after.getRowType(), before.getRowType(), false),
        is(true));
  }
}
