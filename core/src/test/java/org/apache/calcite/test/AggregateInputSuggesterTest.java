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

import org.apache.calcite.plan.hep.HepPlanner;
import org.apache.calcite.plan.hep.HepProgramBuilder;
import org.apache.calcite.rel.AggregateInputSuggester;
import org.apache.calcite.rel.RelCommonExpressionBasicSuggester;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.core.Aggregate;
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

import static org.hamcrest.CoreMatchers.instanceOf;
import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.hasSize;

/**
 * Tests for {@link org.apache.calcite.rel.AggregateInputSuggester}: a
 * signature-based {@link org.apache.calcite.rel.RelCommonExpressionSuggester}
 * that discovers fusable grouped aggregates even when they differ in payload or
 * are interleaved with unrelated joins.
 */
class AggregateInputSuggesterTest {

  private static SchemaPlus schema() {
    SchemaPlus root = Frameworks.createRootSchema(true);
    root.add("S", new AbstractTable() {
      @Override public RelDataType getRowType(RelDataTypeFactory tf) {
        return tf.builder().add("ID", tf.createSqlType(SqlTypeName.INTEGER)).build();
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

  private static RelNode decorrelate(String sql) throws Exception {
    final Planner planner =
        Frameworks.getPlanner(Frameworks.newConfigBuilder().defaultSchema(schema()).build());
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

  /** Two aggregates over the same table that differ only in payload are
   * discovered as one common computation. */
  @Test void testDiscoversCommonComputation() throws Exception {
    final RelNode plan = decorrelate("select "
        + "(select sum(A) from T where T.K = S.ID), "
        + "(select sum(B) from T where T.K = S.ID) from S");
    assertThat(new AggregateInputSuggester().suggest(plan, null), hasSize(1));
  }

  /** The common computation is found even when the two fusable aggregates are
   * interleaved with an aggregate over a different table. */
  @Test void testDiscoversAcrossInterleavedJoins() throws Exception {
    final RelNode plan = decorrelate("select "
        + "(select sum(A) from T where T.K = S.ID), "
        + "(select sum(X) from U where U.K = S.ID), "
        + "(select sum(B) from T where T.K = S.ID) from S");
    final java.util.Collection<RelNode> suggestions =
        new AggregateInputSuggester().suggest(plan, null);
    // Only the T computation is common (shared by two aggregates); U is not.
    assertThat(suggestions, hasSize(1));
    assertThat(suggestions.iterator().next(), instanceOf(Aggregate.class));
  }

  /** Aggregates over different tables are not reported as common. */
  @Test void testNoCommonForDifferentTables() throws Exception {
    final RelNode plan = decorrelate("select "
        + "(select sum(A) from T where T.K = S.ID), "
        + "(select sum(X) from U where U.K = S.ID) from S");
    assertThat(new AggregateInputSuggester().suggest(plan, null), hasSize(0));
  }

  /** The exact-match basic suggester cannot see these payload-differing
   * aggregates as a common computation. */
  @Test void testBasicSuggesterMissesPayloadDiffering() throws Exception {
    final RelNode plan = decorrelate("select "
        + "(select sum(A) from T where T.K = S.ID), "
        + "(select sum(B) from T where T.K = S.ID) from S");
    final boolean anyAggregate =
        new RelCommonExpressionBasicSuggester().suggest(plan, null).stream()
            .anyMatch(r -> r instanceof Aggregate);
    assertThat("basic suggester should not report the aggregates as common",
        anyAggregate, is(false));
  }
}
