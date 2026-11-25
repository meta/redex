/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <atomic>
#include <utility>
#include <vector>

#include "DexClass.h"

class PassManager;

namespace method_splitting_impl {

// Discriminates the two kinds of splits produced by this pass.
// Tests prefer this enum over name-substring matching to avoid the
// `$hot$` / `$hot_cold$` substring overlap trap.
enum class SplitKind {
  Suffix,
  Region,
};

// Plain-data snapshot of Stats. Returned by `Stats::snapshot()` so
// tests can read counter values by value without touching atomics.
struct StatsSnapshot {
  size_t split_count;
  size_t split_count_simple;
  size_t split_count_switches;
  size_t split_count_switch_cases;
  size_t hot_split_count;
  size_t hot_cold_split_count;
  size_t cold_split_count;
  size_t dex_limits_hit;
  size_t added_code_size;
  size_t split_code_size;
  size_t kept_large_packed_switches;
  size_t created_large_sparse_switches;
  size_t destroyed_large_packed_switches;
  size_t excluded_methods;
  size_t iterations;
};

struct Stats {
  std::atomic<size_t> split_count_simple{0};
  std::atomic<size_t> split_count_switches{0};
  std::atomic<size_t> split_count_switch_cases{0};
  std::atomic<size_t> hot_split_count{0};
  std::atomic<size_t> hot_cold_split_count{0};
  std::atomic<size_t> cold_split_count{0};
  std::atomic<size_t> dex_limits_hit{0};
  // Closures dropped because a synthesized argument type was not loadable:
  // external and above the min-sdk floor, or cross-store illegal.
  std::atomic<size_t> arg_type_illegal{0};
  std::atomic<size_t> added_code_size{0};
  std::atomic<size_t> split_code_size{0};
  std::atomic<size_t> kept_large_packed_switches{0};
  std::atomic<size_t> created_large_sparse_switches{0};
  std::atomic<size_t> destroyed_large_packed_switches{0};
  // Each newly-emitted split, tagged with its kind. Append-only;
  // deterministically ordered by `compare_dexmethods` when transferred
  // from the per-iteration concurrent collection.
  std::vector<std::pair<DexMethod*, SplitKind>> added_methods;
  std::atomic<size_t> excluded_methods{0};
  size_t iterations{0};

  // Every metric of the pass that the splitter counts.
  void export_metrics(PassManager& mgr) const;

  StatsSnapshot snapshot() const {
    return StatsSnapshot{
        .split_count = added_methods.size(),
        .split_count_simple = split_count_simple.load(),
        .split_count_switches = split_count_switches.load(),
        .split_count_switch_cases = split_count_switch_cases.load(),
        .hot_split_count = hot_split_count.load(),
        .hot_cold_split_count = hot_cold_split_count.load(),
        .cold_split_count = cold_split_count.load(),
        .dex_limits_hit = dex_limits_hit.load(),
        .added_code_size = added_code_size.load(),
        .split_code_size = split_code_size.load(),
        .kept_large_packed_switches = kept_large_packed_switches.load(),
        .created_large_sparse_switches = created_large_sparse_switches.load(),
        .destroyed_large_packed_switches =
            destroyed_large_packed_switches.load(),
        .excluded_methods = excluded_methods.load(),
        .iterations = iterations,
    };
  }
};

} // namespace method_splitting_impl
