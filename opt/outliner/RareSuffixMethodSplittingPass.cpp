/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "RareSuffixMethodSplittingPass.h"

#include "AnnoUtils.h"
#include "BaselineProfile.h"
#include "ConcurrentContainers.h"
#include "ConfigFiles.h"
#include "DexUtil.h"
#include "MethodOverrideGraph.h"
#include "MethodSplitter.h"
#include "MethodUtil.h"
#include "NeverInlineEligibility.h"
#include "PassManager.h"
#include "SplittableClosures.h"
#include "TypeUtil.h"
#include "Walkers.h"

using namespace method_splitting_impl;

namespace {

// See `net_oat_weight`.
constexpr float kDefaultNetOatWeight = 1.0f;

} // namespace

void RareSuffixMethodSplittingPass::bind_config() {
  bind("enabled", false, m_enabled, "Whether the pass runs.");
  bind("art_inline_max_code_units",
       baseline_profiles::DEFAULT_ART_INLINE_MAX_CODE_UNITS,
       m_art_inline_max_code_units,
       "Largest method, in the code units dex2oat sees, that ART inlines and "
       "so the largest method split. The size is estimated before register "
       "allocation and can differ from the final size by a few code units.");
  bind("max_caller_instructions",
       never_inline_analysis::kDefaultMaxCallerInstructions,
       m_max_caller_instructions,
       "Callers with more estimated instructions (`IRCode::count_opcodes`) "
       "are not counted as inlining a method; see "
       "ArtProfileWriterPass's `never_inline_max_caller_instructions`.");
  bind("min_compiled_call_sites", size_t{2}, m_min_compiled_call_sites,
       "Fewest call sites in compiled callers for a method to be split.");
  bind("min_suffix_runtime_calls", size_t{2}, m_min_suffix_runtime_calls,
       "Fewest invokes or allocations the suffix must make. Each compiles to "
       "a call sequence with a stack map; a suffix with fewer is about as "
       "cheap as the call that replaces it.");
  bind("max_live_in", int64_t{3}, m_config.max_live_in,
       "Most registers the suffix may read from the rest of the method.");
  // A split is made when MethodSplittingPass's net cost model finds it pays,
  // with each call site in a compiled caller, a static estimate of the copies
  // ART inlines, counted as a compiled copy of the method.
  bind("net_oat_weight", kDefaultNetOatWeight, m_config.net_oat_weight,
       "OAT:dex weight W in net = W*(SAVED - ADDED_ccuc) - dex_added, as in "
       "MethodSplittingPass, where SAVED and ADDED_ccuc count every compiled "
       "copy of the method. A split is made when the net is positive.");
  bind("net_cu_method_metadata", m_config.net_cu_method_metadata,
       m_config.net_cu_method_metadata,
       "Net cost-model code-unit cost (see MethodSplittingConfig).");
  bind("net_cu_load_param", m_config.net_cu_load_param,
       m_config.net_cu_load_param,
       "Net cost-model code-unit cost (see MethodSplittingConfig).");
  bind("net_cu_range_spill_per_reg", m_config.net_cu_range_spill_per_reg,
       m_config.net_cu_range_spill_per_reg,
       "Net cost-model code-unit cost (see MethodSplittingConfig).");
  after_configuration([this] { m_config.validate(); });
}

void RareSuffixMethodSplittingPass::run_pass(DexStoresVector& stores,
                                             ConfigFiles& conf,
                                             PassManager& mgr) {
  if (!m_enabled) {
    return;
  }
  auto scope = build_class_scope(stores);
  auto baseline_profile = baseline_profiles::get_default_baseline_profile(
      scope, conf.get_baseline_profile_configs(), conf.get_method_profiles());

  auto exact_virtuals = never_inline_analysis::exact_virtuals(
      *method_override_graph::build_graph(scope), scope);
  std::atomic<size_t> callers_too_many_instructions{0};
  AtomicMap<DexMethod*, size_t> compiled_call_sites;
  walk::parallel::code(scope, [&](DexMethod* caller, IRCode& code) {
    if (!baseline_profiles::is_compiled(baseline_profile, caller)) {
      return;
    }
    // ART also skips callers over its register budget, but this pass runs
    // before register allocation, which decides how many registers a caller
    // ends up with.
    if (code.count_opcodes() > m_max_caller_instructions) {
      callers_too_many_instructions++;
      return;
    }
    never_inline_analysis::for_each_exact_call_site(
        caller, code.cfg(), exact_virtuals,
        [&](cfg::Block*, IRInstruction*, DexMethod* callee) {
          compiled_call_sites.fetch_add(callee, 1);
        });
  });

  std::atomic<size_t> too_few_call_sites{0};
  std::atomic<size_t> art_never_inlines{0};
  std::atomic<size_t> too_large{0};
  std::atomic<size_t> always_throws{0};
  std::atomic<size_t> simple{0};
  std::atomic<size_t> has_catch_handler{0};
  InsertOnlyConcurrentSet<DexMethod*> concurrent_candidates;
  walk::parallel::code(scope, [&](DexMethod* method, IRCode& code) {
    if (compiled_call_sites.load(method) < m_min_compiled_call_sites) {
      too_few_call_sites++;
      return;
    }
    // ART does not inline either kind.
    if (method::is_clinit(method) ||
        has_anno(method, type::dalvik_annotation_optimization_NeverInline())) {
      art_never_inlines++;
      return;
    }
    switch (never_inline_analysis::never_inline_shape(method)) {
    case never_inline_analysis::Shape::kAlwaysThrows:
      always_throws++;
      return;
    case never_inline_analysis::Shape::kSimple:
      simple++;
      return;
    case never_inline_analysis::Shape::kEligible:
      break;
    }
    if (baseline_profiles::dex2oat_code_units_before_unreachable_lowering(
            method) > m_art_inline_max_code_units) {
      too_large++;
      return;
    }
    if (code.has_try_blocks()) {
      has_catch_handler++;
      return;
    }
    concurrent_candidates.insert(method);
  });
  auto candidates =
      unordered_to_ordered(concurrent_candidates, compare_dexmethods);

  auto env = make_split_environment(stores, conf, mgr);
  RareSuffixSelectionStats selection_stats;
  Stats stats;
  RareSuffixSelection selection(
      candidates, m_config, m_min_suffix_runtime_calls,
      [&](const DexMethod* method) {
        return compiled_call_sites.load(const_cast<DexMethod*>(method));
      },
      env.store_ref_checkers, stats, selection_stats);
  auto selected_methods = selection.selected_method_count();
  auto [split_methods, derived_method_profile_stats] = split_selected_closures(
      stores, env, selection.splittable_closures(),
      /* name_infix */ "$rare_suffix$", conf.get_method_profiles(), &stats);
  std::move(selection).finish(split_methods);

  size_t split_call_sites = 0;
  for (auto* m : UnorderedIterable(split_methods)) {
    split_call_sites += compiled_call_sites.load(m);
  }

  mgr.set_metric("callers_too_many_instructions",
                 callers_too_many_instructions.load());
  mgr.set_metric("candidates", candidates.size());
  mgr.set_metric("rejected_too_few_call_sites", too_few_call_sites.load());
  mgr.set_metric("rejected_art_never_inlines", art_never_inlines.load());
  mgr.set_metric("rejected_unsplittable_method",
                 selection_stats.unsplittable.load());
  mgr.set_metric("rejected_too_large", too_large.load());
  mgr.set_metric("rejected_always_throws", always_throws.load());
  mgr.set_metric("rejected_simple", simple.load());
  mgr.set_metric("rejected_catch", has_catch_handler.load());
  mgr.set_metric("rejected_no_rare_suffix",
                 selection_stats.no_rare_suffix.load());
  mgr.set_metric("rejected_too_few_runtime_calls",
                 selection_stats.too_few_runtime_calls.load());
  mgr.set_metric("rejected_not_splittable",
                 selection_stats.not_splittable.load());
  mgr.set_metric("selected_methods", selected_methods);
  mgr.set_metric("split_count", stats.added_methods.size());
  mgr.set_metric("hot_split_count", stats.hot_split_count.load());
  mgr.set_metric("hot_cold_split_count", stats.hot_cold_split_count.load());
  mgr.set_metric("cold_split_count", stats.cold_split_count.load());
  mgr.set_metric("derived_method_profile_stats", derived_method_profile_stats);
  mgr.set_metric("split_compiled_call_sites", split_call_sites);
  mgr.set_metric("split_code_size", stats.split_code_size.load());
  mgr.set_metric("dex_limits_hit", stats.dex_limits_hit.load());
  stats.suffix_fates.export_metrics(mgr);
}

static RareSuffixMethodSplittingPass s_pass;
