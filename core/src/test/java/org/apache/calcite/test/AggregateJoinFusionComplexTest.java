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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.equalTo;

/**
 * Equivalence tests for {@link org.apache.calcite.rel.rules.AggregateJoinFusionRule}
 * on complex correlated sub-query bodies (extra filters, joins inside the
 * sub-query, window functions, distinct aggregates). Verifies both that
 * results never change and that the rule fuses only when the sub-query
 * computations are genuinely the same.
 */
class AggregateJoinFusionComplexTest {

  /** Driver. */
  @SuppressWarnings("unused")
  public static class Srow {
    public final int id;
    Srow(int id) {
      this.id = id;
    }
  }

  /** Grouped table with a join key {@code j}. */
  @SuppressWarnings("unused")
  public static class Trow {
    public final int k;
    public final int a;
    public final int b;
    public final int j;
    Trow(int k, int a, int b, int j) {
      this.k = k;
      this.a = a;
      this.b = b;
      this.j = j;
    }
  }

  /** Table joined inside the sub-query. */
  @SuppressWarnings("unused")
  public static class Vrow {
    public final int j;
    public final int w;
    Vrow(int j, int w) {
      this.j = j;
      this.w = w;
    }
  }

  /** Reflective schema. */
  @SuppressWarnings("unused")
  public static class Db {
    public final Srow[] s = {new Srow(1), new Srow(2), new Srow(3)};
    public final Trow[] t = {
        new Trow(1, 100, 1000, 1), new Trow(1, 200, 2000, 2),
        new Trow(2, 5, 50, 1), new Trow(3, 7, 70, 3)};
    public final Vrow[] v = {new Vrow(1, 9), new Vrow(2, 8)};
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
    try (Interpreter interpreter =
             new Interpreter(new MyDataContext(rootSchema, plan), plan)) {
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

  /** Runs the query with and without the rule; returns whether fusion fired,
   * and always asserts identical results. */
  private boolean checkEquivalent(String sql) throws Exception {
    initSchema();
    final RelNode before = decorrelate(sql);
    final RelNode after = fuse(before);
    assertThat("results changed for: " + sql, execute(after), equalTo(execute(before)));
    return aggregateCount(after) < aggregateCount(before);
  }

  /** Identical extra filter in both sub-query bodies: same computation, fuses. */
  @Test void testSameFilterFuses() throws Exception {
    final boolean fused = checkEquivalent("select "
        + "(select sum(a) from t where t.k = s.id and t.a > 10), "
        + "(select sum(b) from t where t.k = s.id and t.a > 10) from s");
    assertThat("identical filtered bodies should fuse", fused, is(true));
  }

  /** Different filter in the two bodies: different computation, must not fuse. */
  @Test void testDifferentFilterDoesNotFuse() throws Exception {
    final boolean fused = checkEquivalent("select "
        + "(select sum(a) from t where t.k = s.id and t.a > 10), "
        + "(select sum(b) from t where t.k = s.id and t.a > 100) from s");
    assertThat("different filtered bodies must not fuse", fused, is(false));
  }

  /** Identical join inside both sub-query bodies: same computation, fuses. */
  @Test void testSameJoinBodyFuses() throws Exception {
    final boolean fused = checkEquivalent("select "
        + "(select sum(t.a) from t inner join v on t.j = v.j where t.k = s.id), "
        + "(select sum(t.b) from t inner join v on t.j = v.j where t.k = s.id) from s");
    assertThat("identical join bodies should fuse", fused, is(true));
  }

  /** Different join condition in the two bodies: must not fuse. */
  @Test void testDifferentJoinBodyDoesNotFuse() throws Exception {
    final boolean fused = checkEquivalent("select "
        + "(select sum(t.a) from t inner join v on t.j = v.j where t.k = s.id), "
        + "(select sum(t.b) from t inner join v on t.j = v.w where t.k = s.id) from s");
    assertThat("different join bodies must not fuse", fused, is(false));
  }

  /** Distinct aggregates over the same body: results must be preserved. */
  @Test void testDistinctAggregates() throws Exception {
    // Whether or not it fuses, the results must be identical.
    checkEquivalent("select "
        + "(select sum(distinct a) from t where t.k = s.id), "
        + "(select sum(distinct b) from t where t.k = s.id) from s");
  }

  /** A window function query is not the fusable shape; the rule must leave the
   * plan untouched. (Executed via plan comparison, since the interpreter does
   * not evaluate window functions.) */
  @Test void testWindowFunctionUntouched() throws Exception {
    initSchema();
    final RelNode before =
        decorrelate("select k, sum(a) over (partition by k), sum(b) over (partition by k) from t");
    final RelNode after = fuse(before);
    assertThat("window query plan must be unchanged",
        org.apache.calcite.plan.RelOptUtil.toString(after),
        equalTo(org.apache.calcite.plan.RelOptUtil.toString(before)));
  }
}
