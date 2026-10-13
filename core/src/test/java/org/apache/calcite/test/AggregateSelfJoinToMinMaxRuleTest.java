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

import org.apache.calcite.adapter.java.ReflectiveSchema;
import org.apache.calcite.avatica.util.Casing;
import org.apache.calcite.plan.RelOptUtil;
import org.apache.calcite.plan.hep.HepPlanner;
import org.apache.calcite.plan.hep.HepProgram;
import org.apache.calcite.plan.hep.HepProgramBuilder;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.core.Join;
import org.apache.calcite.rel.core.RelFactories;
import org.apache.calcite.rel.rules.CoreRules;
import org.apache.calcite.schema.SchemaPlus;
import org.apache.calcite.sql.parser.SqlParser;
import org.apache.calcite.sql2rel.RelDecorrelator;
import org.apache.calcite.sql2rel.TopDownGeneralDecorrelator;
import org.apache.calcite.tools.Frameworks;
import org.apache.calcite.tools.Planner;
import org.apache.calcite.tools.RelBuilder;
import org.apache.calcite.tools.RelRunners;

import org.checkerframework.checker.nullness.qual.Nullable;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Random;
import java.util.stream.Stream;

import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.equalTo;
import static org.hamcrest.Matchers.greaterThan;
import static org.junit.jupiter.params.provider.Arguments.arguments;

/**
 * Execution-based equivalence tests for
 * {@link org.apache.calcite.rel.rules.AggregateSelfJoinToMinMaxRule}: each
 * query is planned with and without the rule and executed over the same
 * in-memory data, and the results must be identical.
 *
 * <p>The data covers the edge cases of the rewrite: null keys, null values,
 * single-row groups, groups whose values are all equal, and groups with
 * repeated values.
 */
class AggregateSelfJoinToMinMaxRuleTest {

  /** Row of table {@code t}; all columns are nullable. */
  @SuppressWarnings("unused")
  public static class Trow {
    public final @Nullable Integer k;
    public final @Nullable Integer k2;
    public final @Nullable Integer v;
    public final @Nullable String s;

    Trow(@Nullable Integer k, @Nullable Integer k2, @Nullable Integer v,
        @Nullable String s) {
      this.k = k;
      this.k2 = k2;
      this.v = v;
      this.s = s;
    }
  }

  /** Row of table {@code d}, the outer table of {@code IN} queries. */
  @SuppressWarnings("unused")
  public static class Drow {
    public final @Nullable Integer id;

    Drow(@Nullable Integer id) {
      this.id = id;
    }
  }

  /** Reflective schema. */
  @SuppressWarnings("unused")
  public static class Db {
    public final Trow[] t = {
        // k=1: two distinct values, repeated
        new Trow(1, 1, 10, "a"), new Trow(1, 1, 20, "b"),
        new Trow(1, 2, 10, "a"),
        // k=2: all values equal
        new Trow(2, 1, 5, "x"), new Trow(2, 1, 5, "x"),
        // k=3: single row
        new Trow(3, 1, 7, "y"),
        // k=4: one value plus nulls
        new Trow(4, 1, null, null), new Trow(4, 1, 8, "z"),
        new Trow(4, 2, null, null),
        // k=5: only nulls
        new Trow(5, 1, null, null), new Trow(5, 1, null, null),
        // k=6: distinct values but in different k2 groups
        new Trow(6, 1, 1, "p"), new Trow(6, 2, 2, "q"),
        // null keys with distinct values must never qualify
        new Trow(null, 1, 1, "m"), new Trow(null, 1, 2, "n"),
        new Trow(7, null, 3, "c"), new Trow(7, null, 4, "d"),
    };
    public final Trow[] e0 = {};
    public final Drow[] d = {
        new Drow(1), new Drow(2), new Drow(3), new Drow(4), new Drow(5),
        new Drow(6), new Drow(7), new Drow(null), new Drow(1)};
  }

  /** Normalizes the plan into the shape the rule expects, as a standard
   * program would: sub-queries expanded and join conditions pushed down. */
  private static final HepProgram PREPARE = new HepProgramBuilder()
      .addRuleCollection(
          Arrays.asList(CoreRules.FILTER_INTO_JOIN, CoreRules.PROJECT_MERGE,
              CoreRules.PROJECT_REMOVE, CoreRules.AGGREGATE_PROJECT_MERGE))
      .build();

  private static final HepProgram REWRITE = new HepProgramBuilder()
      .addRuleCollection(
          Arrays.asList(CoreRules.AGGREGATE_SELF_JOIN_TO_MIN_MAX,
              CoreRules.EXISTENCE_SELF_JOIN_TO_MIN_MAX,
              CoreRules.EXISTENCE_PROJECT_SELF_JOIN_TO_MIN_MAX,
              CoreRules.EXISTENCE_BELOW_JOIN_SELF_JOIN_TO_MIN_MAX))
      .build();

  private static final HepProgram REWRITE_WITH_TRANSPOSE =
      new HepProgramBuilder()
          .addRuleCollection(
              Arrays.asList(CoreRules.AGGREGATE_JOIN_TRANSPOSE_EXTENDED,
                  CoreRules.AGGREGATE_PROJECT_MERGE))
          .addRuleCollection(
              Arrays.asList(CoreRules.AGGREGATE_SELF_JOIN_TO_MIN_MAX,
                  CoreRules.EXISTENCE_SELF_JOIN_TO_MIN_MAX,
                  CoreRules.EXISTENCE_PROJECT_SELF_JOIN_TO_MIN_MAX,
                  CoreRules.EXISTENCE_BELOW_JOIN_SELF_JOIN_TO_MIN_MAX))
          .build();

  /** Plans {@code sql}, returning the plans before and after the rule.
   * {@code topDown} selects {@link TopDownGeneralDecorrelator}, which expands
   * {@code IN} and {@code EXISTS} to semi-, anti- and mark-joins, rather than
   * {@link RelDecorrelator}, which expands them to joins with aggregates. */
  private static RelNode[] plan(String sql, boolean topDown,
      HepProgram rewrite) throws Exception {
    final SchemaPlus rootSchema = Frameworks.createRootSchema(true);
    final SchemaPlus db = rootSchema.add("DB", new ReflectiveSchema(new Db()));
    final Planner planner = Frameworks.getPlanner(Frameworks.newConfigBuilder()
        .defaultSchema(db)
        .parserConfig(SqlParser.config().withUnquotedCasing(Casing.TO_LOWER))
        .build());
    RelNode rel = planner.rel(planner.validate(planner.parse(sql))).rel;
    rel = run(new HepProgramBuilder()
        .addRuleInstance(topDown
            ? CoreRules.FILTER_SUB_QUERY_TO_MARK_CORRELATE
            : CoreRules.FILTER_SUB_QUERY_TO_CORRELATE)
        .build(), rel);
    final RelBuilder relBuilder =
        RelFactories.LOGICAL_BUILDER.create(rel.getCluster(), null);
    rel = topDown
        ? TopDownGeneralDecorrelator.decorrelateQuery(rel, relBuilder)
        : RelDecorrelator.decorrelateQuery(rel, relBuilder);
    final RelNode before = run(PREPARE, rel);
    final RelNode after = run(rewrite, before);
    return new RelNode[] {before, after};
  }

  private static RelNode run(HepProgram program, RelNode rel) {
    final HepPlanner hep = new HepPlanner(program);
    hep.setRoot(rel);
    return hep.findBestExp();
  }

  /** Executes a plan using the Enumerable convention. */
  private static List<String> execute(RelNode plan) throws SQLException {
    final List<String> rows = new ArrayList<>();
    try (PreparedStatement statement = RelRunners.run(plan);
         ResultSet resultSet = statement.executeQuery()) {
      final int columnCount = resultSet.getMetaData().getColumnCount();
      while (resultSet.next()) {
        final List<@Nullable Object> row = new ArrayList<>();
        for (int i = 1; i <= columnCount; i++) {
          row.add(resultSet.getObject(i));
        }
        rows.add(row.toString());
      }
    }
    Collections.sort(rows);
    return rows;
  }

  private static int joinCount(RelNode rel) {
    int n = rel instanceof Join ? 1 : 0;
    for (RelNode input : rel.getInputs()) {
      n += joinCount(input);
    }
    return n;
  }

  /** Shape of the second {@code IN} of TPC-DS query 95: the self-join is joined
   * to another table below the duplicate-insensitive consumer.
   *
   * <p>With {@link RelDecorrelator} the consumer is a {@code DISTINCT}, which
   * {@link CoreRules#AGGREGATE_JOIN_TRANSPOSE_EXTENDED} pushes down to the
   * self-join, after which the rule fires. With
   * {@link TopDownGeneralDecorrelator} the consumer is a semi-join, which
   * {@link CoreRules#EXISTENCE_BELOW_JOIN_SELF_JOIN_TO_MIN_MAX} handles. */
  @Test void testBelowJoin() throws Exception {
    final String sql = "select id from d where id in (select x.id from d x,"
        + " (select t1.k from t t1, t t2"
        + " where t1.k = t2.k and t1.v <> t2.v) w where x.id = w.k)";
    check(sql, false, false, REWRITE);
    check(sql, false, true, REWRITE_WITH_TRANSPOSE);
    check(sql, true, true, REWRITE);
    check(sql, true, true, REWRITE_WITH_TRANSPOSE);
  }

  /** Asserts that results are unchanged by the rule, and that the rule fired
   * (removed a join) if and only if {@code fires}. Returns whether it fired. */
  private static boolean check(String sql, boolean topDown, boolean fires)
      throws Exception {
    return check(sql, topDown, fires, REWRITE);
  }

  private static boolean check(String sql, boolean topDown, boolean fires,
      HepProgram rewrite) throws Exception {
    final RelNode[] plans = plan(sql, topDown, rewrite);
    final RelNode before = plans[0];
    final RelNode after = plans[1];
    final String context =
        String.join(System.lineSeparator(), sql, "topDown: " + topDown,
            "before:",
            RelOptUtil.toString(before), "after:", RelOptUtil.toString(after));
    assertThat("row type changed: " + context,
        RelOptUtil.areRowTypesEqual(after.getRowType(), before.getRowType(),
            true), is(true));
    assertThat("results changed: " + context, execute(after),
        equalTo(execute(before)));
    final boolean fired = joinCount(after) < joinCount(before);
    assertThat("rule fired: " + context, fired, is(fires));
    return fired;
  }

  private static String selfJoin(String select, String condition) {
    return "select distinct " + select + " from t t1, t t2 where " + condition;
  }

  static Stream<Arguments> cases() {
    return Stream.of(
        // --- positive ---
        arguments("not-equals",
            selfJoin("t1.k", "t1.k = t2.k and t1.v <> t2.v"), true, true),
        arguments("less-than",
            selfJoin("t1.k", "t1.k = t2.k and t1.v < t2.v"), true, true),
        arguments("greater-than",
            selfJoin("t1.k", "t1.k = t2.k and t1.v > t2.v"), true, true),
        arguments("reversed-operands",
            selfJoin("t2.k", "t2.k = t1.k and t2.v <> t1.v"), true, true),
        arguments("string-value",
            selfJoin("t1.k", "t1.k = t2.k and t1.s <> t2.s"), true, true),
        arguments("same-expression-value",
            selfJoin("t1.k", "t1.k = t2.k and t1.v + 1 <> t2.v + 1"), true, true),
        arguments("boolean-value",
            selfJoin("t1.k", "t1.k = t2.k and (t1.v > 9) <> (t2.v > 9)"), true, true),
        arguments("empty-input",
            "select distinct e1.k from e0 e1, e0 e2"
                + " where e1.k = e2.k and e1.v <> e2.v", true, true),
        arguments("composite-key-all-projected",
            selfJoin("t1.k, t2.k2",
                "t1.k = t2.k and t1.k2 = t2.k2 and t1.v <> t2.v"), true, true),
        arguments("composite-key-subset-projected",
            selfJoin("t1.k", "t1.k = t2.k and t1.k2 = t2.k2 and t1.v <> t2.v"),
            true, true),
        arguments("key-projected-twice",
            selfJoin("t1.k, t2.k", "t1.k = t2.k and t1.v <> t2.v"), true, true),
        arguments("in-sub-query",
            "select id from d where id in (select t1.k from t t1, t t2"
                + " where t1.k = t2.k and t1.v <> t2.v)", true, true),
        arguments("in-sub-query-composite",
            "select id from d where id in (select t1.k from t t1, t t2"
                + " where t1.k = t2.k and t1.k2 = t2.k2 and t1.s <> t2.s)",
            true, true),
        arguments("same-filtered-inputs",
            "select distinct t1.k from (select * from t where k2 = 1) t1,"
                + " (select * from t where k2 = 1) t2"
                + " where t1.k = t2.k and t1.v <> t2.v", true, true),
        // --- negative ---
        arguments("count-not-duplicate-insensitive",
            "select t1.k, count(*) from t t1, t t2"
                + " where t1.k = t2.k and t1.v <> t2.v group by t1.k", false, false),
        arguments("different-inputs",
            "select distinct t1.k from t t1, (select * from t where k2 = 1) t2"
                + " where t1.k = t2.k and t1.v <> t2.v", false, false),
        arguments("two-inequalities",
            selfJoin("t1.k", "t1.k = t2.k and t1.v <> t2.v and t1.s <> t2.s"),
            false, false),
        arguments("different-columns",
            selfJoin("t1.k", "t1.k = t2.k and t1.v <> t2.k2"), false, false),
        arguments("non-key-group",
            selfJoin("t1.v", "t1.k = t2.k and t1.v <> t2.v"), false, false),
        // Without a strict inequality every row pairs with itself, so the
        // self-join reduces to a filter
        arguments("no-inequality",
            selfJoin("t1.k", "t1.k = t2.k and t1.v = t2.v"), true, true),
        arguments("less-than-or-equal",
            selfJoin("t1.k", "t1.k = t2.k and t1.v <= t2.v"), true, true),
        arguments("greater-than-or-equal-reversed",
            selfJoin("t2.k", "t2.k = t1.k and t2.s >= t1.s"), true, true),
        arguments("two-reflexive",
            selfJoin("t1.k, t1.k2",
                "t1.k = t2.k and t1.k2 = t2.k2 and t1.v <= t2.v"
                    + " and t1.s >= t2.s"), true, true),
        arguments("key-not-null-on-one-side",
            "select distinct t1.k from t t1,"
                + " (select * from t where k is not null) t2"
                + " where t1.k = t2.k and t1.v <> t2.v", true, true),
        arguments("expression-equality",
            selfJoin("t1.k", "t1.k = t2.k and t1.v + 1 = t2.v + 1"), true, true),
        arguments("strict-and-reflexive",
            selfJoin("t1.k", "t1.k = t2.k and t1.v <> t2.v and t1.s <= t2.s"),
            false, false),
        // "IS DISTINCT FROM" also holds between null and non-null (k = 4)
        arguments("is-distinct-from",
            selfJoin("t1.k", "t1.k = t2.k and t1.v is distinct from t2.v"),
            true, true),
        // "IS NOT DISTINCT FROM" keys match null keys, as GROUP BY does
        arguments("null-safe-key",
            selfJoin("t1.k",
                "t1.k is not distinct from t2.k and t1.v <> t2.v"), true, true),
        arguments("null-safe-key-is-distinct-from",
            selfJoin("t1.k", "t1.k is not distinct from t2.k"
                + " and t1.s is distinct from t2.s"), true, true),
        // "IS NOT DISTINCT FROM" of an expression holds for every row and
        // itself, even if null
        arguments("null-safe-expression",
            selfJoin("t1.k",
                "t1.k = t2.k and t1.v + 1 is not distinct from t2.v + 1"),
            true, true),
        arguments("approximate-key",
            "select distinct t1.k from (select cast(k as double) k, v from t) t1,"
                + " (select cast(k as double) k, v from t) t2"
                + " where t1.k = t2.k and t1.v <> t2.v", false, false),
        arguments("non-key-not-null-on-one-side",
            "select distinct t1.k from t t1,"
                + " (select * from t where v is not null) t2"
                + " where t1.k = t2.k and t1.v <> t2.v", false, false),
        arguments("no-key",
            selfJoin("t1.k", "t1.v <> t2.v"), false, false),
        arguments("not-a-comparison",
            selfJoin("t1.k", "t1.k = t2.k and t1.v + 1 <> t2.v"), false, false),
        arguments("key-expression",
            selfJoin("t1.k", "t1.k + 0 = t2.k + 0 and t1.v <> t2.v"), false, false),
        // NOT IN: RelDecorrelator expands to two aggregates over the
        // self-join; the rule replaces the one that groups by the key and
        // computes LITERAL_AGG, but not the one that computes COUNT;
        // TopDownGeneralDecorrelator expands to a mark-join
        arguments("not-in-sub-query",
            "select id from d where id not in (select t1.k from t t1, t t2"
                + " where t1.k = t2.k and t1.v <> t2.v)", true, true),
        arguments("not-exists-sub-query",
            "select id from d where not exists (select 1 from t t1, t t2"
                + " where t1.k = d.id and t1.k = t2.k and t1.v <> t2.v)",
            true, true),
        // The existence join tests a non-key column of the self-join
        arguments("in-sub-query-non-key",
            "select id from d where id in (select t1.v from t t1, t t2"
                + " where t1.k = t2.k and t1.v <> t2.v)", false, false),
        // Decorrelating EXISTS adds "k IS NOT NULL" to one join input only;
        // the rule ignores it, as the key equality rejects null keys anyway
        arguments("exists-sub-query",
            "select id from d where exists (select 1 from t t1, t t2"
                + " where t1.k = d.id and t1.k = t2.k and t1.v <> t2.v)", true, true),
        arguments("left-join",
            "select distinct t1.k from t t1 left join t t2"
                + " on t1.k = t2.k and t1.v <> t2.v", false, false),
        arguments("approximate-value",
            "select distinct t1.k from (select k, cast(v as double) v from t) t1,"
                + " (select k, cast(v as double) v from t) t2"
                + " where t1.k = t2.k and t1.v <> t2.v", false, false));
  }

  @ParameterizedTest(name = "{0}")
  @MethodSource("cases")
  void testCase(String name, String sql, boolean fires, boolean firesTopDown)
      throws Exception {
    check(sql, false, fires);
    check(sql, true, firesTopDown);
  }

  /** Generates random queries in and around the pattern; results must never
   * change, and the rule must fire exactly when the pattern conditions
   * hold. */
  @Test void testRandomEquivalence() throws Exception {
    final Random r = new Random(0);
    int fired = 0;
    for (int q = 0; q < 300; q++) {
      final boolean compositeKey = r.nextBoolean();
      final String value = pick(r, "v", "s");
      final String op =
          pick(r, "<>", "<", ">", "=", "<=", ">=", "is distinct from",
              "is not distinct from", "mismatch");
      final boolean swap = r.nextBoolean();
      final String a = swap ? "t2" : "t1";
      final String b = swap ? "t1" : "t2";
      final String condition = a + ".k = " + b + ".k"
          + (compositeKey ? " and " + b + ".k2 = " + a + ".k2" : "")
          + (op.equals("mismatch")
              ? " and " + a + ".v <> " + b + ".v + 1"
              : " and " + a + "." + value + " " + op + " " + b + "." + value);
      final String select = compositeKey
          ? pick(r, "t1.k", "t2.k", "t1.k, t1.k2", "t2.k2", "t1.k2, t2.k")
          : pick(r, "t1.k", "t2.k", "t1.k, t2.k");
      final String sql = r.nextBoolean()
          ? selfJoin(select, condition)
          : "select id from d where id in (select " + select.split(",")[0]
              + " from t t1, t t2 where " + condition + ")";
      final boolean topDown = r.nextBoolean();
      if (check(sql, topDown, !op.equals("mismatch"))) {
        fired++;
      }
    }
    assertThat(fired, greaterThan(0));
  }

  private static String pick(Random r, String... options) {
    return options[r.nextInt(options.length)];
  }
}
