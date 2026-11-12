/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <optional>
#include <set>

#include "DexClass.h"
#include "PositionJoin.h"

using MethodOrderedSet = std::set<DexMethod*, dexmethods_comparator>;

namespace method_dedup {

/**
 * Group methods that are similar in that they share the same signature and of
 * the same size. It is useful for pre-sorting a method list before a custom
 * deduplication process.
 * Currently the only user of this function is in CleanupGQL. We can remove this
 * interface once that use is cleaned up.
 */
UnorderedBag<MethodOrderedSet> group_similar_methods(
    const std::vector<DexMethod*>&);

/**
 * Group methods that are identical in that they share the same signature and
 * identical code. We ignore non-opcodes like debug info.
 * Note that there's no side affects other than the grouping here.
 */
UnorderedBag<MethodOrderedSet> group_identical_methods(
    const std::vector<DexMethod*>&, bool dedup_fill_in_stack_trace);

/**
 * Check if the given list of methods share the same signature and identical
 * code.
 */
bool are_deduplicatable(const std::vector<DexMethod*>&,
                        bool dedup_fill_in_stack_trace);

/**
 * Identify identical methods and replace references to all duplicated methods
 * to their canonical replacemnt.
 * We do so by grouping identical methods, choosing the first one in each group
 * as its canonical replacement and update all call sites to point to their
 * canonical replacement.
 */
size_t dedup_methods(
    const Scope& scope,
    const std::vector<DexMethod*>& to_dedup,
    bool dedup_fill_in_stack_trace,
    std::vector<DexMethod*>& replacements,
    std::optional<UnorderedMap<DexMethod*, MethodOrderedSet>>& new_to_old,
    positions::JoinStats* join_stats);

} // namespace method_dedup
