/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

/*
 * MethodSplittingPass splits large methods, relocating suffixes and cold
 * regions into separate helper methods. This entry point binds config and
 * emits metrics; the splitting machinery lives in MethodSplitter.
 */
#include "MethodSplittingPass.h"

#include "BaselineProfile.h"
#include "ConfigFiles.h"
#include "DexUtil.h"
#include "InterDexPassMetrics.h"
#include "MethodSplitter.h"
#include "PassManager.h"
#include "Show.h"
#include "Trace.h"

using namespace method_splitting_impl;

void MethodSplittingPass::bind_config() {
  bind("split_clinits", m_config.split_clinits, m_config.split_clinits,
       "Whether to consider splitting clinits");
  bind("split_block_size", m_config.split_block_size, m_config.split_block_size,
       "Splits blocks so that no block has more opcodes than this size");
  bind("min_original_size", m_config.min_original_size,
       m_config.min_original_size,
       "Minimum size of any method to consider splitting");
  bind("min_original_size_hot_method", m_config.min_original_size_hot_method,
       m_config.min_original_size_hot_method,
       "Minimum size of a hot method to consider splitting");
  bind("min_original_size_too_large_for_inlining",
       m_config.min_original_size_too_large_for_inlining,
       m_config.min_original_size_too_large_for_inlining,
       "Minimum size of method to consider splitting when too large for "
       "inlining");
  bind("min_hot_split_size", m_config.min_hot_split_size,
       m_config.min_hot_split_size, "Minimum size of split-out hot code");
  bind("min_hot_cold_split_size", m_config.min_hot_cold_split_size,
       m_config.min_hot_cold_split_size,
       "Minimum size of split-out code with transition from hot to cold");
  bind("min_cold_split_size", m_config.min_cold_split_size,
       m_config.min_cold_split_size, "Minimum size of split-out code code");
  bind("huge_threshold", m_config.huge_threshold, m_config.huge_threshold,
       "Threshold for a method to be considered huge to activate "
       "max_huge_overhead_ratio");
  bind("max_overhead_ratio", m_config.max_overhead_ratio,
       m_config.max_overhead_ratio,
       "Maximum ratio of combined split and remaining code size vs "
       "original code size");
  bind("max_hot_overhead_ratio", m_config.max_hot_overhead_ratio,
       m_config.max_hot_overhead_ratio,
       "Maximum ratio of combined split and remaining code size vs "
       "original code size for hot methods");
  bind("max_huge_overhead_ratio", m_config.max_huge_overhead_ratio,
       m_config.max_huge_overhead_ratio,
       "Maximum ratio of combined split and remaining code size vs "
       "original code size for huge methods");
  bind("max_live_in", m_config.max_live_in, m_config.max_live_in,
       "Maximum number of live-in registers");
  bind("max_iteration", m_config.max_iteration, m_config.max_iteration,
       "Maximum number of top-level iterations");
  bind("fix_new_hot_split_registration",
       m_config.fix_new_hot_split_registration,
       m_config.fix_new_hot_split_registration,
       "Register a newly created Hot split in the hot-method set, so later "
       "iterations treat it as the compiled host it actually is. Fixes a "
       "no-op insert of the root method. Off by default.");
  bind("excluded_prefices", m_config.excluded_prefices,
       m_config.excluded_prefices);
  bind("enable_region_splitting", m_config.enable_region_splitting,
       m_config.enable_region_splitting,
       "Master switch for cold-region outlining (off by default).");
}

void MethodSplittingPass::run_pass(DexStoresVector& stores,
                                   ConfigFiles& conf,
                                   PassManager& mgr) {
  const auto& interdex_metrics = mgr.get_interdex_metrics();
  auto it = interdex_metrics.find(interdex::METRIC_RESERVED_MREFS);
  size_t reserved_mrefs = it == interdex_metrics.end() ? 0 : it->second;
  it = interdex_metrics.find(interdex::METRIC_RESERVED_TREFS);
  size_t reserved_trefs = it == interdex_metrics.end() ? 0 : it->second;

  auto scope = build_class_scope(stores);
  auto baseline_profile = baseline_profiles::get_default_baseline_profile(
      scope, conf.get_baseline_profile_configs(), conf.get_method_profiles());
  InsertOnlyConcurrentSet<const DexMethod*> concurrent_hot_methods;
  for (auto&& [method, flags] : UnorderedIterable(baseline_profile.methods)) {
    if (flags.hot) {
      concurrent_hot_methods.insert_unsafe(method);
    }
  }

  auto name_infix = "$" + std::to_string(m_iteration) + "$";
  Stats stats;
  InsertOnlyConcurrentMap<DexMethod*, DexMethod*>
      concurrent_new_hot_split_methods;
  InsertOnlyConcurrentMap<DexMethod*, size_t>
      concurrent_splittable_no_optimizations_methods;
  int32_t min_sdk = mgr.get_redex_options().min_sdk;
  const api::AndroidSDK* min_sdk_api{nullptr};
  if (conf.get_android_sdk_api_file(min_sdk)) {
    min_sdk_api = &conf.get_android_sdk_api(min_sdk);
  } else {
    mgr.incr_metric("min_sdk_no_file", 1);
  }
  StoreRefCheckers store_ref_checkers(stores, conf.normal_primary_dex(),
                                      min_sdk_api);
  split_methods_in_stores(
      stores, min_sdk, m_config, store_ref_checkers,
      conf.create_init_class_insns(), reserved_mrefs, reserved_trefs, &stats,
      name_infix, &concurrent_hot_methods, &concurrent_new_hot_split_methods,
      &concurrent_splittable_no_optimizations_methods);

  auto& method_profiles = conf.get_method_profiles();
  size_t derived_method_profile_stats{0};
  for (auto [new_method, root_method] :
       UnorderedIterable(concurrent_new_hot_split_methods)) {
    derived_method_profile_stats +=
        method_profiles.derive_stats(new_method, {root_method});
  }

  mgr.set_metric("split_count", stats.added_methods.size());
  mgr.set_metric("split_count_simple", (size_t)stats.split_count_simple);
  mgr.set_metric("split_count_switches", (size_t)stats.split_count_switches);
  mgr.set_metric("split_count_switch_cases",
                 (size_t)stats.split_count_switch_cases);
  mgr.set_metric("hot_split_count", (size_t)stats.hot_split_count);
  mgr.set_metric("hot_cold_split_count", (size_t)stats.hot_cold_split_count);
  mgr.set_metric("cold_split_count", (size_t)stats.cold_split_count);
  mgr.set_metric("dex_limits_hit", (size_t)stats.dex_limits_hit);
  mgr.set_metric("added_code_size", (size_t)stats.added_code_size);
  mgr.set_metric("split_code_size", (size_t)stats.split_code_size);
  mgr.set_metric("kept_large_packed_switches",
                 (size_t)stats.kept_large_packed_switches);
  mgr.set_metric("destroyed_large_packed_switches",
                 (size_t)stats.destroyed_large_packed_switches);
  mgr.set_metric("created_large_sparse_switches",
                 (size_t)stats.created_large_sparse_switches);
  mgr.set_metric("new_hot_split_methods",
                 concurrent_new_hot_split_methods.size());
  mgr.set_metric("derived_method_profile_stats", derived_method_profile_stats);
  mgr.set_metric("excluded_methods", (size_t)stats.excluded_methods);
  // A nonzero value on a run that also reports `min_sdk_no_file` means the gate
  // rejected external types for want of an api model rather than on a real
  // min-sdk violation.
  mgr.set_metric("arg_type_illegal", (size_t)stats.arg_type_illegal);
  mgr.set_metric("iterations", stats.iterations);
  TRACE(MS, 1, "Split out %zu methods", stats.added_methods.size());

  for (auto [method, size] :
       UnorderedIterable(concurrent_splittable_no_optimizations_methods)) {
    mgr.set_metric("no_optimizations_" + show_deobfuscated(method), size);
  }
  m_iteration++;
}

static MethodSplittingPass s_pass;
