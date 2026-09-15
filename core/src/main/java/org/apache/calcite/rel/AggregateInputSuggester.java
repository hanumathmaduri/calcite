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

import org.apache.calcite.plan.Context;
import org.apache.calcite.rel.core.Aggregate;
import org.apache.calcite.rel.logical.LogicalAggregate;

import com.google.common.collect.ImmutableList;

import org.apiguardian.api.API;
import org.checkerframework.checker.nullness.qual.Nullable;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Suggester for common relational expressions based on the
 * {@link AggregateInputSignature computation underneath an aggregate} rather
 * than exact structural equality. It reports, once per group, the common
 * grouped computation shared by two or more {@link Aggregate}s that group the
 * same input by the same key but compute different aggregate calls.
 *
 * <p>Unlike {@link RelCommonExpressionBasicSuggester}, which only finds
 * identical trees, this suggester surfaces the "parameterized" common
 * sub-expressions behind
 * <a href="https://issues.apache.org/jira/browse/CALCITE-5631">[CALCITE-5631]</a>,
 * for example the common {@code t GROUP BY k} shared by {@code sum(a)} and
 * {@code sum(b)}. Because it scans the whole tree, it finds such groups even
 * when the aggregates are far apart or interleaved with unrelated joins.
 */
@API(since = "1.44.0", status = API.Status.EXPERIMENTAL)
public class AggregateInputSuggester implements RelCommonExpressionSuggester {

  @Override public Collection<RelNode> suggest(RelNode input,
      @Nullable Context context) {
    final Map<AggregateInputSignature, List<Aggregate>> groups = new LinkedHashMap<>();
    final Map<AggregateInputSignature, RelNode> baseOf = new LinkedHashMap<>();
    collect(input, groups, baseOf);

    final List<RelNode> result = new ArrayList<>();
    for (Map.Entry<AggregateInputSignature, List<Aggregate>> e : groups.entrySet()) {
      if (e.getValue().size() < 2) {
        continue;
      }
      final AggregateInputSignature signature = e.getKey();
      // The common computation is the shared base grouped by the shared key,
      // without any aggregate calls; consumers add the per-occurrence calls.
      result.add(
          LogicalAggregate.create(baseOf.get(signature), ImmutableList.of(),
              signature.groupSet(), null, ImmutableList.of()));
    }
    return result;
  }

  private static void collect(RelNode rel,
      Map<AggregateInputSignature, List<Aggregate>> groups,
      Map<AggregateInputSignature, RelNode> baseOf) {
    final RelNode node = rel.stripped();
    if (node instanceof Aggregate) {
      final Aggregate aggregate = (Aggregate) node;
      final AggregateInputSignature signature = AggregateInputSignature.of(aggregate);
      if (signature != null) {
        groups.computeIfAbsent(signature, k -> new ArrayList<>()).add(aggregate);
        baseOf.putIfAbsent(signature, AggregateInputSignature.base(aggregate));
      }
    }
    for (RelNode child : node.getInputs()) {
      collect(child, groups, baseOf);
    }
  }

}
