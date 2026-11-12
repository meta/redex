/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "RareSuffixMethodSplittingPass.h"

#include <algorithm>
#include <functional>
#include <limits>
#include <optional>
#include <string>
#include <vector>

#include "AnnoUtils.h"
#include "BaselineProfile.h"
#include "ConcurrentContainers.h"
#include "ConfigFiles.h"
#include "DexUtil.h"
#include "HotCallsites.h"
#include "JsonWrapper.h"
#include "MethodProfiles.h"
#include "MethodSplitter.h"
#include "MethodUtil.h"
#include "NeverCompileSelection.h"
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

// See `max_returning_suffix_ratio`.
constexpr float kDefaultMaxReturningSuffixRatio = 0.01f;

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

// ArtProfileWriterPass's `@NeverInline` configuration, as this run's
// configuration gives it to that pass, at that pass's defaults where it says
// nothing.
struct WriterConfig {
  bool attach_annotations{false};
  float hot_block_appear_threshold{
      never_inline_analysis::kDefaultAppearThreshold};
  float hot_method_appear_threshold{
      never_inline_analysis::kDefaultAppearThreshold};
  size_t max_caller_instructions{
      never_inline_analysis::kDefaultMaxCallerInstructions};
  never_inline_analysis::NeverInlineCriteria criteria{
      .max_callee_code_units =
          never_inline_analysis::kDefaultMaxCalleeCodeUnits,
      .min_callee_instructions =
          never_inline_analysis::kDefaultMinCalleeInstructions,
      .min_hot_callsites = never_inline_analysis::kDefaultMinHotCallsites,
      .min_hot_callsites_min_code_units =
          never_inline_analysis::kDefaultMinHotCallsitesMinCodeUnits,
  };
};

WriterConfig read_writer_config(const ConfigFiles& conf) {
  WriterConfig writer;
  Json::Value json;
  conf.get_json_config().get("ArtProfileWriterPass", Json::nullValue, json);
  if (json.isNull()) {
    return writer;
  }
  const JsonWrapper jw(json);
  jw.get("never_inline_attach_annotations", writer.attach_annotations,
         writer.attach_annotations);
  // `JsonWrapper` reads no float.
  auto get_float = [&json](const char* name, float& dest) {
    if (json.isMember(name)) {
      dest = json[name].asFloat();
    }
  };
  get_float("never_inline_hot_block_appear_threshold",
            writer.hot_block_appear_threshold);
  get_float("never_inline_hot_method_appear_threshold",
            writer.hot_method_appear_threshold);
  jw.get("never_inline_max_caller_instructions", writer.max_caller_instructions,
         writer.max_caller_instructions);
  auto& criteria = writer.criteria;
  size_t max_callee_code_units = criteria.max_callee_code_units;
  jw.get("never_inline_max_callee_code_units", max_callee_code_units,
         max_callee_code_units);
  criteria.max_callee_code_units = static_cast<uint32_t>(max_callee_code_units);
  jw.get("never_inline_min_callee_instructions",
         criteria.min_callee_instructions, criteria.min_callee_instructions);
  jw.get("never_inline_min_hot_callsites", criteria.min_hot_callsites,
         criteria.min_hot_callsites);
  size_t min_hot_callsites_min_code_units =
      criteria.min_hot_callsites_min_code_units;
  jw.get("never_inline_min_hot_callsites_min_code_units",
         min_hot_callsites_min_code_units, min_hot_callsites_min_code_units);
  criteria.min_hot_callsites_min_code_units =
      static_cast<uint32_t>(min_hot_callsites_min_code_units);
  return writer;
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
  bind("min_compiled_call_sites", size_t{2}, m_min_compiled_call_sites,
       "Fewest call sites in compiled callers for a method to be split.");
  bind("min_suffix_runtime_calls", size_t{2}, m_min_suffix_runtime_calls,
       "Fewest invokes or allocations the suffix must make. Each compiles to "
       "a call sequence with a stack map; a suffix with fewer is about as "
       "cheap as the call that replaces it.");
  bind("max_returning_suffix_ratio", kDefaultMaxReturningSuffixRatio,
       m_max_returning_suffix_ratio,
       "Also split a suffix that returns when its entry's block count is at "
       "most this ratio of the method entry's, as for a lazily computed "
       "value. The counts come from the source blocks: a profile's, or "
       "SyntheticBlockCountsPass's estimate. A method without counts, or one "
       "that never ran, gets no such split. Negative turns this off.");
  bind("max_live_in", int64_t{3}, m_config.max_live_in,
       "Most registers the suffix may read from the rest of the method.");
  // A split is made when MethodSplittingPass's net cost model finds it pays,
  // with each compiled copy of the method counted: its own body when it is
  // compiled, and a copy per call site ART inlines it at.
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
  const auto& method_profiles = conf.get_method_profiles();
  // The profile that compiles the method itself.
  auto baseline_profile =
      baseline_profiles::get_default_baseline_profile(scope, conf);

  // ART inlines a method at each call site in a compiled caller within its
  // budgets, unless ArtProfileWriterPass, which runs later, annotates the
  // method `@NeverInline`. The call sites, and that pass's decision, come
  // from its own analysis, on the profile and configuration it reads. It also
  // skips callers over its register bound, but this pass runs before register
  // allocation, which decides how many registers a caller ends up with.
  const auto writer = read_writer_config(conf);
  auto [writer_profile, final_profiles] =
      baseline_profiles::get_baseline_profiles(
          scope, conf, /* method_refs_without_def */ nullptr,
          /* apply_forced_flags */ false);
  const never_inline_analysis::HotCallsiteThresholds thresholds{
      .hot_block_appear_threshold = writer.hot_block_appear_threshold,
      .hot_method_appear_threshold = writer.hot_method_appear_threshold,
      .max_caller_instructions = writer.max_caller_instructions,
      .max_caller_registers = std::numeric_limits<size_t>::max(),
  };
  const never_inline_analysis::HotCallsites callsites(
      scope, writer_profile, method_profiles, thresholds);

  // ArtProfileWriterPass's never-compile selection drops methods from the
  // default profile it writes, when that profile is the final one, and
  // dex2oat leaves them uncompiled: they hold no copy of their callees, nor
  // of their own body.
  InsertOnlyConcurrentSet<const DexMethod*> never_compiled;
  const auto& default_config = conf.get_default_baseline_profile_config();
  auto final_default = final_profiles.find(
      baseline_profiles::DEFAULT_BASELINE_PROFILE_CONFIG_NAME);
  if (default_config.harvest_config.enable_never_compile &&
      final_default != final_profiles.end()) {
    const auto excluded =
        never_compile_analysis::excluded_interaction_ids(default_config);
    walk::parallel::code(scope, [&](DexMethod* method, IRCode& code) {
      auto rules = never_compile_analysis::select_never_compile(
          method, code, final_default->second, default_config, excluded,
          method_profiles);
      if (rules && rules->any()) {
        never_compiled.insert(method);
      }
    });
  }
  // The call sites the analysis counts in callers dropped from compilation, a
  // subset of those it counts in all.
  AtomicMap<DexMethod*, size_t> never_compiled_call_sites;
  if (!never_compiled.empty()) {
    never_inline_analysis::walk_callsites(
        scope,
        never_inline_analysis::CallsiteWalk{
            .caller_compiled =
                [&](DexMethod* caller) {
                  return never_compiled.count(caller) != 0u &&
                         baseline_profiles::is_compiled(writer_profile, caller);
                },
            .max_caller_instructions = thresholds.max_caller_instructions,
            .max_caller_registers = thresholds.max_caller_registers,
            .visit_callers_over_register_bound = false,
            .follow_forwarder = [](const DexMethod*) { return true; },
        },
        [&](cfg::Block*, DexMethod* callee, bool) {
          never_compiled_call_sites.fetch_add(callee, 1);
        });
  }
  // The call sites in callers dex2oat compiles.
  const auto compiled_call_sites = [&](DexMethod* method) {
    const auto all = callsites.callsite_counts.load(method);
    const auto dropped = never_compiled_call_sites.load(method);
    // Both walks share the caller bounds and forwarder rule, and the second
    // visits only callers the first does.
    always_assert_log(dropped <= all, "%zu of %zu call sites dropped for %s",
                      dropped, all, SHOW(method));
    return all - dropped;
  };
  // The compiled copies of `method` with a body of `shape`: its own body if
  // it is compiled, and a copy per call site unless ArtProfileWriterPass
  // would annotate it. A method that already carries `@NeverInline` is not a
  // candidate.
  const auto compiled_copies =
      [&](const DexMethod* m,
          const never_inline_analysis::CalleeShape& shape) -> size_t {
    auto* method = const_cast<DexMethod*>(m);
    const size_t own =
        baseline_profiles::is_compiled(baseline_profile, method) &&
                never_compiled.count(method) == 0u
            ? 1
            : 0;
    if (writer.attach_annotations &&
        never_inline_analysis::decide_never_inline(
            shape, /* already_never_inline */ false,
            callsites.hot_cold_callees.count_unsafe(method) != 0u,
            callsites.hot_callsite_counts.load(method), writer.criteria)
                .decision ==
            never_inline_analysis::NeverInlineDecision::kAnnotate) {
      return own;
    }
    return own + compiled_call_sites(method);
  };

  std::atomic<size_t> too_few_call_sites{0};
  std::atomic<size_t> art_never_inlines{0};
  std::atomic<size_t> too_large{0};
  std::atomic<size_t> always_throws{0};
  std::atomic<size_t> simple{0};
  std::atomic<size_t> has_catch_handler{0};
  InsertOnlyConcurrentSet<DexMethod*> concurrent_candidates;
  walk::parallel::code(scope, [&](DexMethod* method, IRCode& code) {
    if (compiled_call_sites(method) < m_min_compiled_call_sites) {
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
      m_max_returning_suffix_ratio < 0
          ? std::nullopt
          : std::optional<float>(m_max_returning_suffix_ratio),
      compiled_copies, env.store_ref_checkers, stats, selection_stats);
  auto selected_methods = selection.selected_method_count();
  auto [split_methods, derived_method_profile_stats] = split_selected_closures(
      stores, env, selection.splittable_closures(),
      /* name_infix */ "$rare_suffix$", conf.get_method_profiles(), &stats);
  std::move(selection).finish(split_methods);

  size_t split_call_sites = 0;
  for (auto* m : UnorderedIterable(split_methods)) {
    split_call_sites += compiled_call_sites(m);
  }

  // The top split methods, by how often the profile says they run and by how
  // many call sites in compiled callers inline them.
  UnorderedSet<const DexMethodRef*> splits;
  for (const auto& [split, kind] : stats.added_methods) {
    splits.insert(split);
  }
  // A method is listed once per reason its splits were made for: a split that
  // never returns took a suffix that never returns, one that returns took a
  // rarely run suffix.
  std::vector<SplitReport> throw_reports;
  std::vector<SplitReport> rare_reports;
  for (auto* m : UnorderedIterable(split_methods)) {
    SplitReport base{.method = m,
                     .call_count = 0,
                     .compiled_call_sites = compiled_call_sites(m),
                     .kind = {},
                     .split_code_units = 0};
    auto stat = conf.get_method_profiles().get_method_stat(
        method_profiles::COLD_START, m);
    if (stat) {
      base.call_count = static_cast<int64_t>(stat->call_count);
    }
    std::optional<SplitReport> throw_report;
    std::optional<SplitReport> rare_report;
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
      // A split returns exactly when the suffix it took was selected as one
      // that returns: a suffix takes every block its head reaches.
      auto& r = split->get_code()->cfg().return_blocks().empty() ? throw_report
                                                                 : rare_report;
      if (!r) {
        r = base;
        r->kind = kind_of_split(split);
      }
      r->split_code_units += split->get_code()->estimate_code_units();
    }
    if (throw_report) {
      throw_reports.push_back(std::move(*throw_report));
    }
    if (rare_report) {
      rare_reports.push_back(std::move(*rare_report));
    }
  }
  const auto by_call_count = [](const SplitReport& r) { return r.call_count; };
  const auto by_compiled_call_sites = [](const SplitReport& r) {
    return static_cast<int64_t>(r.compiled_call_sites);
  };
  report_top_splits(mgr, "top_throw_split_by_call_count_", throw_reports,
                    by_call_count);
  report_top_splits(mgr, "top_throw_split_by_compiled_call_sites_",
                    throw_reports, by_compiled_call_sites);
  report_top_splits(mgr, "top_rare_split_by_call_count_", rare_reports,
                    by_call_count);
  report_top_splits(mgr, "top_rare_split_by_compiled_call_sites_", rare_reports,
                    by_compiled_call_sites);

  mgr.set_metric("callers_too_many_instructions",
                 callsites.callers_too_many_instructions);
  mgr.set_metric("never_compiled_methods", never_compiled.size());
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
  mgr.set_metric("rejected_no_block_counts",
                 selection_stats.no_block_counts.load());
  mgr.set_metric("rejected_method_never_ran",
                 selection_stats.method_never_ran.load());
  mgr.set_metric("returning_suffixes",
                 selection_stats.returning_suffixes.load());
  mgr.set_metric("methods_without_compiled_copies",
                 selection_stats.no_compiled_copies.load());
  mgr.set_metric("suffixes_changing_copies",
                 selection_stats.copies_changed.load());
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
