/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <atomic>
#include <string>
#include <utility>
#include <vector>

#include "ConcurrentContainers.h"
#include "DeterministicContainers.h"
#include "DexClass.h"
#include "MethodSplittingConfig.h"
#include "SplittableClosures.h"

class DexStore;
using DexStoresVector = std::vector<DexStore>;

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

class SplitMethod {
 public:
  // Creates a new static method according to a splittable closure.
  static SplitMethod create(const SplittableClosure& splittable_closure,
                            DexType* target_type,
                            const DexString* split_name,
                            std::vector<const DexType*> arg_types);

  // Adds the new method to its parent class.
  void add_to_target();

  // Applies the code changes to the original method.
  void apply_code_changes();

  DexMethod* get_new_method() const { return m_new_method; }

 private:
  SplitMethod(const SplittableClosure& splittable_closure,
              DexMethod* new_method,
              cfg::Block* launchpad_template,
              std::unique_ptr<SourceBlock> launchpad_sb)
      : m_splittable_closure(splittable_closure),
        m_new_method(new_method),
        m_launchpad_template(launchpad_template),
        m_launchpad_sb(std::move(launchpad_sb)) {}

  const SplittableClosure& m_splittable_closure;
  DexMethod* m_new_method;
  cfg::Block* m_launchpad_template;
  std::unique_ptr<SourceBlock> m_launchpad_sb;
};

void split_methods_in_stores(
    DexStoresVector& stores,
    int32_t min_sdk,
    const Config& config,
    const StoreRefCheckers& store_ref_checkers,
    bool create_init_class_insns,
    size_t reserved_mrefs,
    size_t reserved_trefs,
    Stats* stats,
    const std::string& name_infix = "",
    InsertOnlyConcurrentSet<const DexMethod*>* concurrent_hot_methods = nullptr,
    InsertOnlyConcurrentMap<DexMethod*, DexMethod*>*
        concurrent_new_hot_split_methods = nullptr,
    InsertOnlyConcurrentMap<DexMethod*, size_t>*
        concurrent_splittable_no_optimizations_methods = nullptr);

} // namespace method_splitting_impl
