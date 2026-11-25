/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <string>
#include <utility>
#include <vector>

#include "ConcurrentContainers.h"
#include "DeterministicContainers.h"
#include "DexClass.h"
#include "MethodSplittingConfig.h"
#include "MethodSplittingStats.h"
#include "SplittableClosures.h"

struct ConfigFiles;
namespace method_profiles {
class MethodProfiles;
} // namespace method_profiles
class DexStore;
class PassManager;
using DexStoresVector = std::vector<DexStore>;

namespace method_splitting_impl {

class SplitMethod {
 public:
  // Creates a new static method according to a splittable closure.
  static SplitMethod create(const SplittableClosure& splittable_closure,
                            DexType* target_type,
                            const DexString* split_name,
                            const std::vector<const DexType*>& arg_types);

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

// What splitting needs from the pass that runs it: the min-sdk level, a
// reference checker per store, and the references InterDex reserved in every
// dex.
struct SplitEnvironment {
  int32_t min_sdk;
  StoreRefCheckers store_ref_checkers;
  bool create_init_class_insns;
  size_t reserved_mrefs;
  size_t reserved_trefs;
};

void split_methods_in_stores(
    DexStoresVector& stores,
    const SplitEnvironment& env,
    const Config& config,
    Stats* stats,
    const std::string& name_infix = "",
    InsertOnlyConcurrentSet<const DexMethod*>* concurrent_hot_methods = nullptr,
    InsertOnlyConcurrentMap<DexMethod*, DexMethod*>*
        concurrent_new_hot_split_methods = nullptr,
    InsertOnlyConcurrentMap<DexMethod*, size_t>*
        concurrent_splittable_no_optimizations_methods = nullptr);

// Builds the split environment of a pass run over `stores`. Counts
// `min_sdk_no_file` in the running pass's metrics when there is no api file
// for the min-sdk level.
SplitEnvironment make_split_environment(const DexStoresVector& stores,
                                        ConfigFiles& conf,
                                        PassManager& mgr);

struct SelectedSplits {
  // The methods with at least one split. A closure dropped because its dex ran
  // out of references is not applied.
  ConcurrentSet<DexMethod*> split_methods;
  // How many profile stats the splits of hot closures inherited.
  size_t derived_method_profile_stats;
};

// Splits closures a caller has already selected, keyed by the type of the class
// that holds their method, as one iteration of `split_methods_in_stores` does:
// with the same per-dex reference accounting, split names and stats. The code
// that a split leaves unreachable is removed, and the split of a hot closure
// inherits its method's profile, see `derive_hot_split_profiles`.
SelectedSplits split_selected_closures(
    DexStoresVector& stores,
    const SplitEnvironment& env,
    const ConcurrentMap<DexType*, std::vector<SplittableClosure>>&
        splittable_closures,
    const std::string& name_infix,
    method_profiles::MethodProfiles& method_profiles,
    Stats* stats);

// Gives every split of a hot closure, keyed to the method whose profile it
// inherits, that method's profile stats, so the baseline profile compiles the
// split as it compiles that method. Returns how many stats were derived.
size_t derive_hot_split_profiles(
    method_profiles::MethodProfiles& method_profiles,
    const InsertOnlyConcurrentMap<DexMethod*, DexMethod*>&
        concurrent_new_hot_split_methods);

} // namespace method_splitting_impl
