/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "RareSuffixMethodSplittingPass.h"

#include <algorithm>
#include <functional>
#include <string>
#include <vector>

#include "AnnoUtils.h"
#include "BaselineProfile.h"
#include "ConcurrentContainers.h"
#include "ConfigFiles.h"
#include "DexUtil.h"
#include "MethodOverrideGraph.h"
#include "MethodProfiles.h"
#include "MethodSplitter.h"
#include "MethodUtil.h"
#include "NeverInlineEligibility.h"
#include "PassManager.h"
#include "Show.h"
#include "SplittableClosures.h"
#include "TypeUtil.h"
#include "Walkers.h"

using namespace method_splitting_impl;

namespace {

// See `net_oat_weight`.
constexpr float kDefaultNetOatWeight = 1.0f;

// How many split methods each top list reports.
constexpr size_t kTopSplitCount = 10;

// A method that got a split, for the top lists.
struct SplitReport {
  DexMethod* method;
  int64_t call_count;
  size_t compiled_call_sites;
  // The kind in the name of its first split, e.g. `hot_cold`.
  std::string kind;
  // The code units of its splits.
  size_t split_code_units;
};

// The kind part of a split's name, `<method>$split$<kind>$rare_suffix$<i>`.
std::string kind_of_split(const DexMethod* split) {
  std::string_view name = split->str();
  constexpr std::string_view kMarker = "$split$";
  auto begin = name.rfind(kMarker);
  if (begin == std::string_view::npos) {
    return "unknown";
  }
  begin += kMarker.size();
  auto end = name.find('$', begin);
  return std::string(name.substr(begin, end - begin));
}

// Reports the methods in `reports` with the highest `key`, as ArtProfileWriter
// reports its top never-compile methods: one metric per method, named after
// its rank, its split kind and the method, whose value is the key, and one
// with the code units of its splits.
void report_top_splits(PassManager& mgr,
                       const std::string& prefix,
                       std::vector<SplitReport> reports,
                       const std::function<int64_t(const SplitReport&)>& key) {
  std::sort(reports.begin(), reports.end(),
            [&](const SplitReport& a, const SplitReport& b) {
              if (key(a) != key(b)) {
                return key(a) > key(b);
              }
              return compare_dexmethods(a.method, b.method);
            });
  reports.resize(std::min(reports.size(), kTopSplitCount));
  for (size_t i = 0; i < reports.size(); ++i) {
    const auto& r = reports[i];
    const auto name = prefix + std::to_string(i) + "_" + r.kind + "_" +
                      show_deobfuscated(r.method);
    mgr.set_metric(name, key(r));
    mgr.set_metric(name + "_split_code_units",
                   static_cast<int64_t>(r.split_code_units));
  }
}

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

  // The top split methods, by how often the profile says they run and by how
  // many call sites in compiled callers inline them.
  UnorderedSet<const DexMethodRef*> splits;
  for (const auto& [split, kind] : stats.added_methods) {
    splits.insert(split);
  }
  std::vector<SplitReport> reports;
  for (auto* m : UnorderedIterable(split_methods)) {
    SplitReport r{.method = m,
                  .call_count = 0,
                  .compiled_call_sites = compiled_call_sites.load(m),
                  .kind = {},
                  .split_code_units = 0};
    auto stat = conf.get_method_profiles().get_method_stat(
        method_profiles::COLD_START, m);
    if (stat) {
      r.call_count = static_cast<int64_t>(stat->call_count);
    }
    // A method that got a split has code.
    always_assert_log(m->get_code() != nullptr, "%s", SHOW(m));
    for (const auto& mie : cfg::InstructionIterable(m->get_code()->cfg())) {
      if (!mie.insn->has_method() ||
          splits.count(mie.insn->get_method()) == 0) {
        continue;
      }
      auto* ref = mie.insn->get_method();
      auto* split = ref->as_def();
      // The ref names a split this pass just created, so it is a definition
      // with code.
      always_assert_log(split != nullptr && split->get_code() != nullptr, "%s",
                        SHOW(ref));
      if (r.kind.empty()) {
        r.kind = kind_of_split(split);
      }
      r.split_code_units += split->get_code()->estimate_code_units();
    }
    reports.push_back(std::move(r));
  }
  report_top_splits(mgr, "top_split_by_call_count_", reports,
                    [](const SplitReport& r) { return r.call_count; });
  report_top_splits(mgr, "top_split_by_compiled_call_sites_", reports,
                    [](const SplitReport& r) {
                      return static_cast<int64_t>(r.compiled_call_sites);
                    });

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
