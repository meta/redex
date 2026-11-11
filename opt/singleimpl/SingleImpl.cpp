/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "SingleImpl.h"

#include <memory>
#include <stdio.h>
#include <string>

#include "ClassHierarchy.h"
#include "Debug.h"
#include "DexUtil.h"
#include "PassManager.h"
#include "Resolver.h"
#include "SingleImplDefs.h"
#include "Trace.h"

size_t SingleImplPass::s_invoke_intf_count = 0;

namespace {

constexpr const char* METRIC_REMOVED_INTERFACES = "num_removed_interfaces";
constexpr const char* METRIC_INVOKE_INT_TO_VIRT = "num_invoke_intf_to_virt";
constexpr const char* METRIC_INSERTED_CHECK_CASTS = "num_inserted_check_casts";
constexpr const char* METRIC_RETAINED_CHECK_CASTS = "num_retained_check_casts";
constexpr const char* METRIC_POST_PROCESS_REMOVED_CASTS =
    "num_post_process_removed_casts";
constexpr const char* METRIC_POST_PROCESS_REPLACED_CASTS =
    "num_post_process_replaced_casts";
constexpr const char* METRIC_POST_PROCESS_WEAKENED_CASTS =
    "num_post_process_weakened_casts";
constexpr const char* METRIC_DELETED_REMOVED_INSTRUCTIONS =
    "num_deleted_removed_instructions";

/**
 * Build a map from interface to the type implementing that
 * interface. We also walk up the interface chain and for every interface
 * in scope (defined in the DEXes) we add an entry as well. So
 * interface B {}
 * interface A extends B {}
 * class C implements A {}
 * generates 2 entries in the map (assuming A, B and C are in the DEXes)
 * { A => C, B => C }
 * whereas if B was outside the DEXes (i.e. java or android interface)
 * we will only have one entry { A => C }
 * keep that in mind when using this map
 */
void map_interfaces(const DexTypeList* intf_list,
                    DexClass* cls,
                    TypeToTypes& intfs_to_classes) {
  for (const auto& intf : *intf_list) {
    auto* const intf_cls = type_class(intf);
    if (intf_cls == nullptr || intf_cls->is_external()) {
      continue;
    }
    if (std::find(intfs_to_classes[intf].begin(), intfs_to_classes[intf].end(),
                  cls->get_type()) == intfs_to_classes[intf].end()) {
      intfs_to_classes[intf].push_back(cls->get_type());
      auto* intfs = intf_cls->get_interfaces();
      map_interfaces(intfs, cls, intfs_to_classes);
    }
  }
}

/**
 * Collect all interfaces.
 */
void build_type_maps(const Scope& scope,
                     TypeToTypes& intfs_to_classes,
                     TypeSet& interfs) {
  for (const auto& cls : scope) {
    if (is_interface(cls)) {
      interfs.insert(cls->get_type());
      continue;
    }
    auto* intfs = cls->get_interfaces();
    map_interfaces(intfs, cls, intfs_to_classes);
  }
}

bool implements_all_intf_methods(const DexClass* impl_cls,
                                 const DexClass* intf_cls) {
  // Check if the class hierarchy implements all interface methods
  for (auto* intf_meth : intf_cls->get_vmethods()) {
    auto* resolved = resolve_virtual_deprecated(impl_cls, intf_meth->get_name(),
                                                intf_meth->get_proto());
    if (resolved == nullptr) {
      // method not found (probably optimized away)
      // => exclude pair from possible merging
      return false;
    }
  }
  return true;
}

void collect_single_impl(const TypeToTypes& intfs_to_classes,
                         TypeMap& single_impl) {
  for (const auto& intf_it : UnorderedIterable(intfs_to_classes)) {
    if (intf_it.second.size() != 1) {
      continue;
    }
    auto* intf = intf_it.first;
    auto* intf_cls = type_class(intf);
    always_assert(intf_cls && !intf_cls->is_external());
    if ((intf_cls->get_access() & DexAccessFlags::ACC_ANNOTATION) != 0u) {
      continue;
    }
    auto* impl = intf_it.second[0];
    auto* impl_cls = type_class(impl);
    always_assert(impl_cls && !impl_cls->is_external());
    // I don't know if it's possible but it's cheap enough to check
    if ((impl_cls->get_access() & DexAccessFlags::ACC_ANNOTATION) != 0u) {
      continue;
    }
    if (!is_abstract(impl_cls) &&
        !implements_all_intf_methods(impl_cls, intf_cls)) {
      continue;
    }
    single_impl[intf] = impl;
  }
}

} // namespace

const int MAX_PASSES = 8;

void SingleImplPass::run_pass(DexStoresVector& stores,
                              ConfigFiles& conf,
                              PassManager& mgr) {
  auto scope = build_class_scope(stores);
  ClassHierarchy ch = build_type_hierarchy(scope);
  int max_steps = 0;
  size_t previous_invoke_intf_count = s_invoke_intf_count;
  OptimizeStats stats;
  const auto& pg_map = conf.get_proguard_map();
  const auto& android_sdk =
      conf.get_android_sdk_api(mgr.get_redex_options().min_sdk);
  while (true) {
    Timer t{std::string("Iteration ").append(std::to_string(max_steps + 1))};
    TRACE(INTF, 9, "\tOPTIMIZE ROUND %d", max_steps);
    DEBUG_ONLY size_t scope_size = scope.size();
    TypeToTypes intfs_to_classes;
    TypeSet intfs;
    build_type_maps(scope, intfs_to_classes, intfs);
    TypeMap single_impl;
    collect_single_impl(intfs_to_classes, single_impl);

    std::unique_ptr<SingleImplAnalysis> single_impls =
        SingleImplAnalysis::analyze(scope, stores, single_impl, intfs, pg_map,
                                    m_pass_config, conf);

    auto optimized_stats =
        optimize(std::move(single_impls), ch, scope, m_pass_config, android_sdk,
                 conf.get_method_profiles());
    stats += optimized_stats;
    if (optimized_stats.removed_interfaces == 0 || ++max_steps >= MAX_PASSES) {
      break;
    }
    redex_assert(scope_size > scope.size());
  }

  TRACE(INTF, 2, "\ttotal steps %d", max_steps);
  TRACE(INTF, 1, "Removed interfaces %zu", removed_count);
  TRACE(INTF, 1, "Updated invoke-interface to invoke-virtual %zu",
        s_invoke_intf_count - previous_invoke_intf_count);

  mgr.incr_metric(METRIC_REMOVED_INTERFACES, stats.removed_interfaces);
  mgr.incr_metric(METRIC_INVOKE_INT_TO_VIRT,
                  s_invoke_intf_count - previous_invoke_intf_count);
  mgr.set_metric(METRIC_INSERTED_CHECK_CASTS, stats.inserted_check_casts);
  mgr.set_metric(METRIC_DELETED_REMOVED_INSTRUCTIONS,
                 stats.deleted_removed_instructions);
  mgr.set_metric(METRIC_RETAINED_CHECK_CASTS, stats.retained_check_casts);
  mgr.set_metric(METRIC_POST_PROCESS_REMOVED_CASTS,
                 stats.post_process.removed_casts);
  mgr.set_metric(METRIC_POST_PROCESS_REPLACED_CASTS,
                 stats.post_process.replaced_casts);
  mgr.set_metric(METRIC_POST_PROCESS_WEAKENED_CASTS,
                 stats.post_process.weakened_casts);

  post_dexen_changes(scope, stores);
}

static SingleImplPass s_pass;
