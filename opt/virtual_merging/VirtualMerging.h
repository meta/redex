/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "ConfigFiles.h"
#include "DeterministicContainers.h"
#include "DexStore.h"
#include "FrameworkApi.h"
#include "InitClassesWithSideEffects.h"
#include "InlinerConfig.h"
#include "Pass.h"
#include "Resolver.h"
#include "VirtualScopes.h"

class MultiMethodInliner;

// Orders scopes by their top def, mirroring legacy `virtualscopes_comparator`,
// so `MergeablePairsByVirtualScope` iterates deterministically.
struct virtual_scope_comparator {
  bool operator()(const virtual_scope::VirtualScope* a,
                  const virtual_scope::VirtualScope* b) const {
    return compare_dexmethods(a->top_def(), b->top_def());
  }
};

namespace method_profiles {
class MethodProfiles;
} // namespace method_profiles

struct VirtualMergingStats {
  size_t invoke_super_methods{0};
  size_t invoke_super_methods_refs{0};
  size_t invoke_super_unresolved_method_refs{0};
  size_t mergeable_virtual_methods{0};
  size_t annotated_methods{0};
  size_t cross_store_refs{0};
  size_t cross_dex_refs{0};
  size_t unavailable_overridden_methods{0};
  size_t inconcrete_overridden_methods{0};
  size_t abstract_overridden_methods{0};
  size_t mergeable_scope_methods{0};
  size_t mergeable_pairs{0};
  size_t virtual_scopes_with_mergeable_pairs{0};
  size_t unabstracted_methods{0};
  size_t uninlinable_methods{0};
  size_t huge_methods{0};
  size_t caller_size_removed_methods{0};
  size_t late_caller_too_large_methods{0};
  size_t removed_virtual_methods{0};
  size_t perf_skipped{0};

  VirtualMergingStats& operator+=(const VirtualMergingStats& rhs) {
    invoke_super_methods += rhs.invoke_super_methods;
    invoke_super_methods_refs += rhs.invoke_super_methods_refs;
    invoke_super_unresolved_method_refs +=
        rhs.invoke_super_unresolved_method_refs;
    mergeable_virtual_methods += rhs.mergeable_virtual_methods;
    annotated_methods += rhs.annotated_methods;
    cross_store_refs += rhs.cross_store_refs;
    cross_dex_refs += rhs.cross_dex_refs;
    unavailable_overridden_methods += rhs.unavailable_overridden_methods;
    inconcrete_overridden_methods += rhs.inconcrete_overridden_methods;
    abstract_overridden_methods += rhs.abstract_overridden_methods;
    perf_skipped += rhs.perf_skipped;
    mergeable_scope_methods += rhs.mergeable_scope_methods;
    mergeable_pairs += rhs.mergeable_pairs;
    virtual_scopes_with_mergeable_pairs +=
        rhs.virtual_scopes_with_mergeable_pairs;
    unabstracted_methods += rhs.unabstracted_methods;
    uninlinable_methods += rhs.uninlinable_methods;
    huge_methods += rhs.huge_methods;
    caller_size_removed_methods += rhs.caller_size_removed_methods;
    late_caller_too_large_methods += rhs.late_caller_too_large_methods;
    removed_virtual_methods += rhs.removed_virtual_methods;
    return *this;
  }

  bool operator==(const VirtualMergingStats& rhs) {
    return invoke_super_methods == rhs.invoke_super_methods &&
           invoke_super_methods_refs == rhs.invoke_super_methods_refs &&
           invoke_super_unresolved_method_refs ==
               rhs.invoke_super_unresolved_method_refs &&
           mergeable_virtual_methods == rhs.mergeable_virtual_methods &&
           annotated_methods == rhs.annotated_methods &&
           cross_store_refs == rhs.cross_store_refs &&
           cross_dex_refs == rhs.cross_dex_refs &&
           unavailable_overridden_methods ==
               rhs.unavailable_overridden_methods &&
           inconcrete_overridden_methods == rhs.inconcrete_overridden_methods &&
           abstract_overridden_methods == rhs.abstract_overridden_methods &&
           mergeable_scope_methods == rhs.mergeable_scope_methods &&
           mergeable_pairs == rhs.mergeable_pairs &&
           virtual_scopes_with_mergeable_pairs ==
               rhs.virtual_scopes_with_mergeable_pairs &&
           unabstracted_methods == rhs.unabstracted_methods &&
           uninlinable_methods == rhs.uninlinable_methods &&
           huge_methods == rhs.huge_methods &&
           caller_size_removed_methods == rhs.caller_size_removed_methods &&
           late_caller_too_large_methods == rhs.late_caller_too_large_methods &&
           removed_virtual_methods == rhs.removed_virtual_methods &&
           perf_skipped == rhs.perf_skipped;
  }
};

class VirtualMerging {
 public:
  enum class Strategy {
    kLexicographical,
    kProfileCallCount,
    kProfileAppearBucketsAndCallCount,
  };

  enum class InsertionStrategy {
    kJumpTo,
    kFallthrough,
  };

  struct PerfConfig {
    float appear100_threshold;
    float call_count_threshold;
    std::vector<std::string> interactions{"ColdStart"};

    PerfConfig()
        : appear100_threshold(101.0), call_count_threshold(0) {} // Default: off
    PerfConfig(float a, float c)
        : appear100_threshold(a), call_count_threshold(c) {}
  };

  VirtualMerging(DexStoresVector&,
                 const ConfigFiles& conf,
                 inliner::InlinerConfig,
                 size_t,
                 const api::AndroidSDK* min_sdk_api = nullptr,
                 PerfConfig perf_config = PerfConfig());
  ~VirtualMerging();
  void run(const method_profiles::MethodProfiles&,
           Strategy strategy,
           InsertionStrategy insertion_strategy);
  const VirtualMergingStats& get_stats() { return m_stats; }

 private:
  Scope m_scope;
  XStoreRefs m_xstores;
  XDexRefs m_xdexes;
  virtual_scope::VirtualScopes m_vscopes;
  size_t m_max_overriding_method_instructions;
  ConcurrentMethodResolverDeprecated m_concurrent_method_resolver;
  inliner::InlinerConfig m_inliner_config;
  init_classes::InitClassesWithSideEffects m_init_classes_with_side_effects;

  std::unique_ptr<MultiMethodInliner> m_inliner;
  VirtualMergingStats m_stats;

  void find_unsupported_virtual_scopes();
  UnorderedSet<const virtual_scope::VirtualScope*> m_unsupported_virtual_scopes;
  UnorderedMap<const DexString*, UnorderedSet<DexProto*>>
      m_unsupported_named_protos;
  UnorderedSet<const DexMethod*> m_method_handle_named_methods;

  void compute_mergeable_scope_methods();
  ConcurrentMap<const virtual_scope::VirtualScope*,
                UnorderedSet<const DexMethod*>>
      m_mergeable_scope_methods;

 public:
  using MergeablePairsByVirtualScope =
      std::map<const virtual_scope::VirtualScope*,
               std::vector<std::pair<const DexMethod*, const DexMethod*>>,
               virtual_scope_comparator>;

  void flush();

 private:
  MergeablePairsByVirtualScope compute_mergeable_pairs_by_virtual_scopes(
      const method_profiles::MethodProfiles&,
      Strategy strategy,
      VirtualMergingStats&) const;

  void merge_methods(const MergeablePairsByVirtualScope& mergeable_pairs,
                     InsertionStrategy insertion_strategy);
  UnorderedMap<DexClass*, std::vector<const DexMethod*>>
      m_virtual_methods_to_remove;
  UnorderedMap<DexMethod*, DexMethod*> m_virtual_methods_to_remap;
  PerfConfig m_perf_config;

  void remove_methods();

  void remap_invoke_virtuals();
};

class VirtualMergingPass : public Pass {
 public:
  VirtualMergingPass() : Pass("VirtualMergingPass") {}

  redex_properties::PropertyInteractions get_property_interactions()
      const override {
    using namespace redex_properties::interactions;
    using namespace redex_properties::names;
    return {
        {DexLimitsObeyed, Preserves},
        {HasSourceBlocks, RequiresAndEstablishes},
        {NoResolvablePureRefs, Preserves},
        {InitialRenameClass, Preserves},
    };
  }

  void bind_config() override;
  void run_pass(DexStoresVector&, ConfigFiles&, PassManager&) override;

 private:
  int64_t m_max_overriding_method_instructions;
  VirtualMerging::Strategy m_strategy{
      VirtualMerging::Strategy::kProfileCallCount};
  VirtualMerging::InsertionStrategy m_insertion_strategy{
      VirtualMerging::InsertionStrategy::kJumpTo};
  VirtualMerging::PerfConfig m_perf_config;
};
