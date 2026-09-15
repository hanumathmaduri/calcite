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
import java.util.Random;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.equalTo;
import static org.hamcrest.Matchers.greaterThan;

/**
 * Randomized, deterministic (fixed-seed) equivalence test for
 * {@link org.apache.calcite.rel.rules.AggregateJoinFusionRule}. Generates many
 * queries in the fusable pattern (correlated scalar sub-queries and explicit
 * joins to grouped sub-queries of the same table, mixing join types, aggregate
 * functions, measures, tables and keys) and asserts that running the rule never
 * changes results.
 */
class AggregateJoinFusionRandomTest {

  private static final int QUERY_COUNT = 400;
  private static final long SEED = 42L;

  /** Driver rows. */
  @SuppressWarnings("unused")
  public static class Srow {
    public final int id;
    public final int id2;
    Srow(int id, int id2) {
      this.id = id;
      this.id2 = id2;
    }
  }

  /** Grouped table T. */
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

  /** Grouped table U. */
  @SuppressWarnings("unused")
  public static class Urow {
    public final int k;
    public final int x;
    Urow(int k, int x) {
      this.k = k;
      this.x = x;
    }
  }

  /** Reflective schema. */
  @SuppressWarnings("unused")
  public static class Db {
    public final Srow[] s = {
        new Srow(1, 2), new Srow(2, 3), new Srow(3, 1), new Srow(4, 4)};
    public final Trow[] t = {
        new Trow(1, 100, 1000), new Trow(1, 200, 2000),
        new Trow(2, 5, 50), new Trow(3, 7, 70)};
    public final Urow[] u = {new Urow(1, 11), new Urow(2, 22), new Urow(4, 44)};
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

  private static String pick(Random r, String... opts) {
    return opts[r.nextInt(opts.length)];
  }

  /** Builds one random query in the fusable pattern. */
  private static String randomQuery(Random r) {
    final int count = 2 + r.nextInt(3); // 2..4 aggregates
    final boolean scalarForm = r.nextBoolean();
    if (scalarForm) {
      final List<String> parts = new ArrayList<>();
      for (int i = 0; i < count; i++) {
        final String tbl = pick(r, "t", "t", "u"); // bias toward t (fusable)
        final String agg = pick(r, "sum", "min", "max", "count");
        final String col = tbl.equals("t") ? pick(r, "a", "b") : "x";
        final String key = pick(r, "id", "id", "id2");
        parts.add("(select " + agg + "(" + col + ") from " + tbl
            + " where " + tbl + ".k = s." + key + ")");
      }
      return "select " + String.join(", ", parts) + " from s";
    } else {
      final List<String> joins = new ArrayList<>();
      final List<String> sel = new ArrayList<>();
      for (int i = 0; i < count; i++) {
        final String tbl = pick(r, "t", "t", "u");
        final String jt = pick(r, "join", "join", "left join");
        final String agg = pick(r, "sum", "min", "max", "count");
        final String col = tbl.equals("t") ? pick(r, "a", "b") : "x";
        final String key = pick(r, "id", "id", "id2");
        final String alias = "z" + i;
        final String expr = agg.equals("count") ? "count(*)" : agg + "(" + col + ")";
        joins.add(jt + " (select k, " + expr + " m from " + tbl
            + " group by k) " + alias + " on " + alias + ".k = s." + key);
        sel.add(alias + ".m");
      }
      return "select " + String.join(", ", sel) + " from s "
          + String.join(" ", joins);
    }
  }

  @Test void testRandomEquivalence() throws Exception {
    final Random r = new Random(SEED);
    int fused = 0;
    for (int q = 0; q < QUERY_COUNT; q++) {
      final String sql = randomQuery(r);
      initSchema();
      final RelNode before;
      final RelNode after;
      try {
        before = decorrelate(sql);
        after = fuse(before);
      } catch (RuntimeException e) {
        throw new AssertionError("planning failed for: " + sql, e);
      }
      final List<String> expected;
      final List<String> actual;
      try {
        expected = execute(before);
        actual = execute(after);
      } catch (RuntimeException e) {
        throw new AssertionError("execution failed for: " + sql, e);
      }
      assertThat("results changed for: " + sql, actual, equalTo(expected));
      if (aggregateCount(after) < aggregateCount(before)) {
        fused++;
      }
    }
    // Sanity: the generator must actually exercise fusion, not only no-ops.
    assertThat("generator should produce fusable queries", fused,
        greaterThan(0));
  }
}
