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

import org.apache.calcite.DataContext;
import org.apache.calcite.adapter.java.JavaTypeFactory;
import org.apache.calcite.adapter.java.ReflectiveSchema;
import org.apache.calcite.interpreter.Interpreter;
import org.apache.calcite.linq4j.QueryProvider;
import org.apache.calcite.plan.hep.HepPlanner;
import org.apache.calcite.plan.hep.HepProgramBuilder;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.core.Aggregate;
import org.apache.calcite.rel.core.RelFactories;
import org.apache.calcite.rel.rules.CoreRules;
import org.apache.calcite.schema.SchemaPlus;
import org.apache.calcite.sql.SqlNode;
import org.apache.calcite.sql2rel.RelDecorrelator;
import org.apache.calcite.tools.Frameworks;
import org.apache.calcite.tools.Planner;
import org.apache.calcite.tools.RelBuilder;

import org.checkerframework.checker.nullness.qual.Nullable;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.stream.Stream;

import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.equalTo;
import static org.hamcrest.Matchers.lessThan;
import static org.junit.jupiter.params.provider.Arguments.arguments;

/**
 * Execution-based equivalence tests for
 * {@link org.apache.calcite.rel.rules.AggregateJoinFusionRule}: each query is
 * planned with and without the fusion rule and executed over the same
 * in-memory data; the result multisets must be identical.
 */
class AggregateJoinFusionExecutionTest {

  /** Driver rows; id=3 has no matching row in {@link Trow}. */
  @SuppressWarnings("unused")
  public static class Srow {
    public final int id;
    public final int id2;
    Srow(int id, int id2) {
      this.id = id;
      this.id2 = id2;
    }
  }

  /** Grouped table; k=1 has two rows, k=2 one, k=3 none. */
  @SuppressWarnings("unused")
  public static class Trow {
    public final int k;
    public final int a;
    public final int b;
    Trow(int k, int a, int b) {
      this.k = k;
      this.a = a;
      this.b = b;
    }
  }

  /** Unrelated grouped table, for interleaving tests. */
  @SuppressWarnings("unused")
  public static class Urow {
    public final int k;
    public final int x;
    Urow(int k, int x) {
      this.k = k;
      this.x = x;
    }
  }

  /** Reflective schema exposing arrays {@code s}, {@code t} and {@code u}. */
  @SuppressWarnings("unused")
  public static class Db {
    public final Srow[] s = {new Srow(1, 10), new Srow(2, 20), new Srow(3, 30)};
    public final Trow[] t = {
        new Trow(1, 100, 1000), new Trow(1, 200, 2000), new Trow(2, 5, 50)};
    public final Urow[] u = {new Urow(1, 7), new Urow(3, 9)};
  }

  /** DataContext for the interpreter. */
  private static final class MyDataContext implements DataContext {
    private final SchemaPlus rootSchema;
    private final JavaTypeFactory typeFactory;
    MyDataContext(SchemaPlus rootSchema, RelNode rel) {
      this.rootSchema = rootSchema;
      this.typeFactory = (JavaTypeFactory) rel.getCluster().getTypeFactory();
    }
    @Override public SchemaPlus getRootSchema() {
      return rootSchema;
    }
    @Override public JavaTypeFactory getTypeFactory() {
      return typeFactory;
    }
    @Override public @Nullable QueryProvider getQueryProvider() {
      return null;
    }
    @Override public @Nullable Object get(String name) {
      return null;
    }
  }

  private SchemaPlus rootSchema;
  private SchemaPlus dbSchema;

  private void initSchema() {
    rootSchema = Frameworks.createRootSchema(true);
    dbSchema = rootSchema.add("DB", new ReflectiveSchema(new Db()));
  }

  private RelNode decorrelate(String sql) throws Exception {
    final Planner planner = Frameworks.getPlanner(Frameworks.newConfigBuilder()
        .defaultSchema(dbSchema)
        .parserConfig(org.apache.calcite.sql.parser.SqlParser.config()
            .withUnquotedCasing(org.apache.calcite.avatica.util.Casing.TO_LOWER))
        .build());
    final SqlNode validated = planner.validate(planner.parse(sql));
    final RelNode rel = planner.rel(validated).rel;
    final HepPlanner hep = new HepPlanner(new HepProgramBuilder()
        .addRuleInstance(CoreRules.PROJECT_SUB_QUERY_TO_CORRELATE)
        .addRuleInstance(CoreRules.FILTER_SUB_QUERY_TO_CORRELATE)
        .addRuleInstance(CoreRules.JOIN_SUB_QUERY_TO_CORRELATE)
        .build());
    hep.setRoot(rel);
    final RelBuilder rb = RelFactories.LOGICAL_BUILDER.create(rel.getCluster(), null);
    return RelDecorrelator.decorrelateQuery(hep.findBestExp(), rb);
  }

  private static RelNode fuse(RelNode plan) {
    final HepPlanner hep = new HepPlanner(new HepProgramBuilder()
        .addRuleCollection(
            Arrays.asList(CoreRules.AGGREGATE_JOIN_FUSION, CoreRules.PROJECT_MERGE))
        .build());
    hep.setRoot(plan);
    return hep.findBestExp();
  }

  private List<String> execute(RelNode plan) {
    final List<String> rows = new ArrayList<>();
    try (Interpreter interpreter = new Interpreter(new MyDataContext(rootSchema, plan), plan)) {
      for (Object[] row : interpreter) {
        rows.add(Arrays.toString(row));
      }
    }
    Collections.sort(rows);
    return rows;
  }

  private static int aggregateCount(RelNode rel) {
    int n = rel instanceof Aggregate ? 1 : 0;
    for (RelNode in : rel.getInputs()) {
      n += aggregateCount(in);
    }
    return n;
  }

  /** Asserts fusion fires (fewer aggregates) and results are unchanged. */
  private void assertFusedAndEquivalent(String sql) throws Exception {
    initSchema();
    final RelNode before = decorrelate(sql);
    final RelNode after = fuse(before);
    assertThat("fusion should reduce aggregate count for: " + sql,
        aggregateCount(after), lessThan(aggregateCount(before)));
    assertThat("results must match with vs without fusion for: " + sql,
        execute(after), equalTo(execute(before)));
  }

  /** Asserts results are unchanged (rule may or may not fire). */
  private void assertEquivalent(String sql) throws Exception {
    initSchema();
    final RelNode before = decorrelate(sql);
    final RelNode after = fuse(before);
    assertThat("results must match with vs without fusion for: " + sql,
        execute(after), equalTo(execute(before)));
  }

  // ---- LEFT-join (decorrelated scalar sub-query) shapes ----

  @Test void testTwoScalarSubqueries() throws Exception {
    assertFusedAndEquivalent("select "
        + "(select sum(A) from T where T.K = S.ID), "
        + "(select sum(B) from T where T.K = S.ID) from S");
  }

  @Test void testThreeScalarSubqueries() throws Exception {
    assertFusedAndEquivalent("select "
        + "(select sum(A) from T where T.K = S.ID), "
        + "(select sum(B) from T where T.K = S.ID), "
        + "(select min(A) from T where T.K = S.ID) from S");
  }

  @Test void testScalarSubqueriesWithOuterColumns() throws Exception {
    assertFusedAndEquivalent("select S.ID, S.ID2, "
        + "(select sum(A) from T where T.K = S.ID), "
        + "(select max(B) from T where T.K = S.ID) from S");
  }

  // ---- INNER / mixed explicit-join shapes ----

  @Test void testTwoInnerJoins() throws Exception {
    assertFusedAndEquivalent("select x.s1, y.s2 from S "
        + "join (select K, sum(A) s1 from T group by K) x on x.K = S.ID "
        + "join (select K, sum(B) s2 from T group by K) y on y.K = S.ID");
  }

  @Test void testMixedInnerLeftJoins() throws Exception {
    assertFusedAndEquivalent("select x.s1, y.s2 from S "
        + "join (select K, sum(A) s1 from T group by K) x on x.K = S.ID "
        + "left join (select K, sum(B) s2 from T group by K) y on y.K = S.ID");
  }

  @Test void testMixedLeftInnerJoins() throws Exception {
    assertFusedAndEquivalent("select x.s1, y.s2 from S "
        + "left join (select K, sum(A) s1 from T group by K) x on x.K = S.ID "
        + "join (select K, sum(B) s2 from T group by K) y on y.K = S.ID");
  }

  /** Two fusable aggregates over T with an unrelated U aggregate interleaved
   * between them: the T pair still fuses, and results are unchanged. */
  @Test void testInterleavedWithDifferentTable() throws Exception {
    assertFusedAndEquivalent("select "
        + "(select sum(A) from T where T.K = S.ID), "
        + "(select sum(X) from U where U.K = S.ID), "
        + "(select sum(B) from T where T.K = S.ID) from S");
  }

  @Test void testThreeInnerJoins() throws Exception {
    assertFusedAndEquivalent("select x.s1, y.s2, z.s3 from S "
        + "join (select K, sum(A) s1 from T group by K) x on x.K = S.ID "
        + "join (select K, sum(B) s2 from T group by K) y on y.K = S.ID "
        + "join (select K, min(A) s3 from T group by K) z on z.K = S.ID");
  }

  // ---- Must-not-change (safety) shapes; results equivalent regardless ----

  @Test void testDifferentKeysUnchangedResults() throws Exception {
    assertEquivalent("select "
        + "(select sum(A) from T where T.K = S.ID), "
        + "(select sum(B) from T where T.K = S.ID2) from S");
  }

  @Test void testCountSubqueryUnchangedResults() throws Exception {
    assertEquivalent("select "
        + "(select sum(A) from T where T.K = S.ID), "
        + "(select count(A) from T where T.K = S.ID) from S");
  }

  // ------------------------------------------------------------------
  // Combination matrix: every case runs with and without the rule and
  // asserts identical results; 'fuse' says whether the aggregate count
  // must strictly drop (true) or stay the same (false, safe no-op).
  // ------------------------------------------------------------------

  private static String lsub(String agg, String col, String key) {
    return "(select " + agg + "(" + col + ") from T where T.K = S." + key + ")";
  }

  private static String usub(String agg, String col) {
    return "(select " + agg + "(" + col + ") from U where U.K = S.ID)";
  }

  private static String ijoin(String alias, String tbl, String proj) {
    return " join (select K, " + proj + " from " + tbl + " group by K) " + alias
        + " on " + alias + ".K = S.ID";
  }

  private static String ljoin(String alias, String tbl, String proj) {
    return " left join (select K, " + proj + " from " + tbl + " group by K) "
        + alias + " on " + alias + ".K = S.ID";
  }

  static Stream<Arguments> combinations() {
    return Stream.of(
        // --- LEFT (decorrelated scalar sub-query) ---
        arguments("left-2-sum",
            "select " + lsub("sum", "A", "ID") + ", " + lsub("sum", "B", "ID")
                + " from S", true),
        arguments("left-3-mixed-aggs",
            "select " + lsub("sum", "A", "ID") + ", " + lsub("sum", "B", "ID")
                + ", " + lsub("min", "A", "ID") + " from S", true),
        arguments("left-4-aggs",
            "select " + lsub("sum", "A", "ID") + ", " + lsub("sum", "B", "ID")
                + ", " + lsub("min", "A", "ID") + ", " + lsub("max", "B", "ID")
                + " from S", true),
        arguments("left-same-measure-column",
            "select " + lsub("sum", "A", "ID") + ", " + lsub("min", "A", "ID")
                + " from S", true),
        arguments("left-with-outer-columns",
            "select S.ID, S.ID2, " + lsub("sum", "A", "ID") + ", "
                + lsub("max", "B", "ID") + " from S", true),
        arguments("left-interleaved-T-U-T",
            "select " + lsub("sum", "A", "ID") + ", " + usub("sum", "X") + ", "
                + lsub("sum", "B", "ID") + " from S", true),
        arguments("left-two-groups-TTUU",
            "select " + lsub("sum", "A", "ID") + ", " + lsub("sum", "B", "ID")
                + ", " + usub("sum", "X") + ", " + usub("min", "X")
                + " from S", true),
        arguments("left-two-groups-interleaved-TUTU",
            "select " + lsub("sum", "A", "ID") + ", " + usub("sum", "X") + ", "
                + lsub("sum", "B", "ID") + ", " + usub("min", "X")
                + " from S", true),
        arguments("left-different-keys-no-fuse",
            "select " + lsub("sum", "A", "ID") + ", " + lsub("sum", "B", "ID2")
                + " from S", false),
        arguments("left-different-tables-no-fuse",
            "select " + lsub("sum", "A", "ID") + ", " + usub("sum", "X")
                + " from S", false),
        arguments("left-count-bug-no-fuse",
            "select " + lsub("sum", "A", "ID") + ", " + lsub("count", "A", "ID")
                + " from S", false),
        // --- INNER / mixed explicit joins ---
        arguments("inner-2",
            "select x.s1, y.s2 from S" + ijoin("x", "T", "sum(A) s1")
                + ijoin("y", "T", "sum(B) s2"), true),
        arguments("inner-3",
            "select x.s1, y.s2, z.s3 from S" + ijoin("x", "T", "sum(A) s1")
                + ijoin("y", "T", "sum(B) s2") + ijoin("z", "T", "min(A) s3"),
            true),
        arguments("mixed-inner-left",
            "select x.s1, y.s2 from S" + ijoin("x", "T", "sum(A) s1")
                + ljoin("y", "T", "sum(B) s2"), true),
        arguments("mixed-left-inner",
            "select x.s1, y.s2 from S" + ljoin("x", "T", "sum(A) s1")
                + ijoin("y", "T", "sum(B) s2"), true),
        arguments("inner-interleaved-T-U-T",
            "select x.s1, u.s2, z.s3 from S" + ijoin("x", "T", "sum(A) s1")
                + ijoin("u", "U", "sum(X) s2") + ijoin("z", "T", "sum(B) s3"),
            true),
        arguments("inner-count-star",
            "select x.c, y.s from S" + ijoin("x", "T", "count(*) c")
                + ijoin("y", "T", "sum(B) s"), true),
        arguments("inner-count-col",
            "select x.c, y.s from S" + ijoin("x", "T", "count(A) c")
                + ijoin("y", "T", "sum(B) s"), true),
        arguments("inner-different-tables-no-fuse",
            "select x.s1, y.s2 from S" + ijoin("x", "T", "sum(A) s1")
                + ijoin("y", "U", "sum(X) s2"), false),
        arguments("inner-two-groups-TTU",
            "select x.s1, y.s2, u.s3 from S" + ijoin("x", "T", "sum(A) s1")
                + ijoin("y", "T", "sum(B) s2") + ijoin("u", "U", "sum(X) s3"),
            true));
  }

  @ParameterizedTest(name = "{0}")
  @MethodSource("combinations")
  void testCombination(String name, String sql, boolean fuse) throws Exception {
    initSchema();
    final RelNode before = decorrelate(sql);
    final RelNode after = fuse(before);
    assertThat(name + ": results must match with vs without fusion",
        execute(after), equalTo(execute(before)));
    if (fuse) {
      assertThat(name + ": expected fusion to reduce aggregate count",
          aggregateCount(after), lessThan(aggregateCount(before)));
    } else {
      assertThat(name + ": expected no fusion",
          aggregateCount(after), is(aggregateCount(before)));
    }
  }
}
