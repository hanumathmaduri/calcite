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
package org.apache.calcite.rel;

import org.apache.calcite.plan.RelOptUtil;
import org.apache.calcite.rel.core.Aggregate;
import org.apache.calcite.rel.core.Project;
import org.apache.calcite.rex.RexInputRef;
import org.apache.calcite.rex.RexNode;
import org.apache.calcite.util.ImmutableBitSet;

import org.checkerframework.checker.nullness.qual.Nullable;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * Identity of the <em>computation</em> underneath an {@link Aggregate}, used to
 * recognize aggregates that can be fused: its normalized input relation and the
 * columns it groups by. The aggregate calls (the "payload") are deliberately
 * excluded, so two aggregates that group the same input by the same key but
 * compute different measures share a signature.
 *
 * <p>This is the "parameterized common sub-expression" notion behind
 * <a href="https://issues.apache.org/jira/browse/CALCITE-5631">[CALCITE-5631]</a>:
 * unlike exact structural equality, it treats {@code Agg(t GROUP BY k, sum(a))}
 * and {@code Agg(t GROUP BY k, sum(b))} as the same computation with different
 * payloads.
 */
public final class AggregateInputSignature {
  private final String baseDigest;
  private final ImmutableBitSet groupSet;

  private AggregateInputSignature(String baseDigest, ImmutableBitSet groupSet) {
    this.baseDigest = baseDigest;
    this.groupSet = groupSet;
  }

  /**
   * Computes the signature of an aggregate, or returns null if the aggregate is
   * not in a normalizable form (non-simple grouping, or a grouping key that is
   * not a simple column reference of a projection over the base).
   */
  public static @Nullable AggregateInputSignature of(Aggregate aggregate) {
    if (aggregate.getGroupType() != Aggregate.Group.SIMPLE) {
      return null;
    }
    final List<Integer> baseCols = groupBaseColumns(aggregate);
    if (baseCols == null) {
      return null;
    }
    return new AggregateInputSignature(
        RelOptUtil.toString(base(aggregate)), ImmutableBitSet.of(baseCols));
  }

  /** Returns the base relation an aggregate computes over: the input, seeing
   * through a payload projection of simple column references. */
  public static RelNode base(Aggregate aggregate) {
    final RelNode input = aggregate.getInput().stripped();
    return input instanceof Project ? ((Project) input).getInput().stripped() : input;
  }

  /** Returns the group set expressed in terms of the {@link #base} columns. */
  public ImmutableBitSet groupSet() {
    return groupSet;
  }

  /** Maps the aggregate's group keys to columns of its base, or null if any key
   * is not a simple column reference. */
  private static @Nullable List<Integer> groupBaseColumns(Aggregate aggregate) {
    final RelNode input = aggregate.getInput().stripped();
    final List<Integer> cols = new ArrayList<>();
    if (input instanceof Project) {
      final Project project = (Project) input;
      for (int g : aggregate.getGroupSet()) {
        final RexNode e = project.getProjects().get(g);
        if (!(e instanceof RexInputRef)) {
          return null;
        }
        cols.add(((RexInputRef) e).getIndex());
      }
    } else {
      for (int g : aggregate.getGroupSet()) {
        cols.add(g);
      }
    }
    return cols;
  }


  @Override public boolean equals(@Nullable Object o) {
    if (this == o) {
      return true;
    }
    if (!(o instanceof AggregateInputSignature)) {
      return false;
    }
    final AggregateInputSignature other = (AggregateInputSignature) o;
    return baseDigest.equals(other.baseDigest) && groupSet.equals(other.groupSet);
  }

  @Override public int hashCode() {
    return Objects.hash(baseDigest, groupSet);
  }

  @Override public String toString() {
    return "AggregateInputSignature(group=" + groupSet + ", base=" + baseDigest + ")";
  }
}
