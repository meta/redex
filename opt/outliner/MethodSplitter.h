/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <atomic>
#include <string>
#include <vector>

#include "ConcurrentContainers.h"
#include "DeterministicContainers.h"
#include "DexClass.h"
#include "MethodSplittingConfig.h"
#include "SplittableClosures.h"

class DexStore;
using DexStoresVector = std::vector<DexStore>;

namespace method_splitting_impl {

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
  UnorderedSet<DexMethod*> added_methods;
  std::atomic<size_t> excluded_methods{0};
  size_t iterations{0};
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
