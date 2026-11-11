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

#include <string>

#include "BaselineProfile.h"
#include "ConfigFiles.h"
#include "DexUtil.h"
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
  // Net cost-model aggregates (see MethodSplittingConfig). The knobs exist so
  // the defaults can be swept without a recompile.
  auto bind_cu = [&](const char* name, size_t& field) {
    bind(name, field, field,
         "Net cost-model code-unit cost (see MethodSplittingConfig).");
  };
  bind_cu("net_cu_load_param", m_config.net_cu_load_param);
  bind_cu("net_cu_method_metadata", m_config.net_cu_method_metadata);
  bind_cu("net_cu_range_spill_per_reg", m_config.net_cu_range_spill_per_reg);
  bind("net_oat_weight", m_config.net_oat_weight, m_config.net_oat_weight,
       "Weight W in net saving = W * (compiled code moved out - compiled code "
       "the launchpad adds back) - DEX code added. W is the number of DEX code "
       "units a split may spend per compiled code unit it moves out. The "
       "default is about 5.5, because ART emits about 11 OAT bytes per "
       "compiled code unit and a DEX code unit is 2 bytes.");
  bind(
      "min_suffix_sub_floor_split_size",
      m_config.min_suffix_sub_floor_split_size,
      m_config.min_suffix_sub_floor_split_size,
      "Size floor for sub-floor suffix candidates: each suffix net gate lowers "
      "both size floors of its kind to this value where it is lower.");
  bind("suffix_net_gate", m_config.suffix_net_gate, m_config.suffix_net_gate,
       "On a compiled host, decide hot-cold suffix splits by their net saving "
       "and refuse those that do not pay; without the gate, size floors and an "
       "overhead ratio alone decide them. The gate also lowers both their size "
       "floors to min_suffix_sub_floor_split_size.");
  bind("suffix_net_gate_cold", m_config.suffix_net_gate_cold,
       m_config.suffix_net_gate_cold,
       "On a compiled host, lower both size floors of cold suffix splits to "
       "min_suffix_sub_floor_split_size. A cold tail that only these lower "
       "floors admit is kept only when the net cost model says it pays. Cold "
       "splits the legacy floors admit are untouched.");

  after_configuration([this] { m_config.validate(); });
}

namespace method_splitting_impl {

void FateCounters::export_metrics(PassManager& mgr) const {
  const std::string prefix = kind == SplitKind::Region ? "region_" : "suffix_";
  mgr.set_metric(prefix + "candidates", candidates.load());
  for (const auto& [fate, fate_name] : kCandidateFateNames) {
    if (!can_reach(kind, fate)) {
      continue;
    }
    const auto i = static_cast<size_t>(fate);
    const auto name = prefix + std::string(fate_name);
    mgr.set_metric(name, n[i].load());
    mgr.set_metric(name + "_code_units", code_units[i].load());
  }
}

void Stats::export_metrics(PassManager& mgr) const {
  mgr.set_metric("split_count", added_methods.size());
  mgr.set_metric("split_count_simple", split_count_simple.load());
  mgr.set_metric("split_count_switches", split_count_switches.load());
  mgr.set_metric("split_count_switch_cases", split_count_switch_cases.load());
  mgr.set_metric("hot_split_count", hot_split_count.load());
  mgr.set_metric("hot_cold_split_count", hot_cold_split_count.load());
  mgr.set_metric("cold_split_count", cold_split_count.load());
  mgr.set_metric("dex_limits_hit", dex_limits_hit.load());
  mgr.set_metric("added_code_size", added_code_size.load());
  mgr.set_metric("split_code_size", split_code_size.load());
  mgr.set_metric("kept_large_packed_switches",
                 kept_large_packed_switches.load());
  mgr.set_metric("destroyed_large_packed_switches",
                 destroyed_large_packed_switches.load());
  mgr.set_metric("created_large_sparse_switches",
                 created_large_sparse_switches.load());
  mgr.set_metric("excluded_methods", excluded_methods.load());
  mgr.set_metric("iterations", iterations);
  suffix_fates.export_metrics(mgr);
  mgr.set_metric("suffix_sub_floor_emitted", suffix_sub_floor_emitted.load());
}

} // namespace method_splitting_impl

namespace {

// The pass's metrics: the splitter's, and what the pass derived from its
// result.
void export_metrics(PassManager& mgr,
                    const Stats& stats,
                    size_t new_hot_split_methods,
                    size_t derived_method_profile_stats,
                    const InsertOnlyConcurrentMap<DexMethod*, size_t>&
                        splittable_no_optimizations_methods) {
  stats.export_metrics(mgr);
  mgr.set_metric("new_hot_split_methods", new_hot_split_methods);
  mgr.set_metric("derived_method_profile_stats", derived_method_profile_stats);
  for (auto [method, size] :
       UnorderedIterable(splittable_no_optimizations_methods)) {
    mgr.set_metric("no_optimizations_" + show_deobfuscated(method), size);
  }
}

} // namespace

void MethodSplittingPass::run_pass(DexStoresVector& stores,
                                   ConfigFiles& conf,
                                   PassManager& mgr) {
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
  auto env = make_split_environment(stores, conf, mgr);
  split_methods_in_stores(stores, env, m_config, &stats, name_infix,
                          &concurrent_hot_methods,
                          &concurrent_new_hot_split_methods,
                          &concurrent_splittable_no_optimizations_methods);

  auto derived_method_profile_stats = derive_hot_split_profiles(
      conf.get_method_profiles(), concurrent_new_hot_split_methods);

  export_metrics(mgr, stats, concurrent_new_hot_split_methods.size(),
                 derived_method_profile_stats,
                 concurrent_splittable_no_optimizations_methods);
  TRACE(MS, 1, "Split out %zu methods", stats.added_methods.size());
  m_iteration++;
}

static MethodSplittingPass s_pass;
