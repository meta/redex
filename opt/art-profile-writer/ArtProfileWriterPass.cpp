/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

/* This pass optionally creates a baseline profile file in a superset of the
 * human-readable ART profile format (HRF) according to
 * https://developer.android.com/topic/performance/baselineprofiles/manually-create-measure#define-rules-manually
 * .
 */

#include "ArtProfileWriterPass.h"

#include <boost/algorithm/string/replace.hpp>
#include <fstream>
#include <sstream>
#include <string>

#include "BaselineProfile.h"
#include "ConcurrentContainers.h"
#include "ConfigFiles.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexAssessments.h"
#include "DexStore.h"
#include "DexStructure.h"
#include "HotCallsites.h"
#include "IRCode.h"
#include "MethodProfiles.h"
#include "NeverCompileSelection.h"
#include "NeverInlineEligibility.h"
#include "PassManager.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "Trace.h"
#include "TypeUtil.h"
#include "Walkers.h"

namespace {
const std::string BASELINE_PROFILES_FILE = "additional-baseline-profiles.list";
const std::string STORE_FENCE_HELPER_NAME = "Lredex/$StoreFenceHelper;";

// An entry that trips any of these is pure profile weight: it costs bytes in
// the shipped app package and in the profile installed on every device, and
// produces nothing. The gates themselves live next to the profile model, in
// libredex/BaselineProfile.h.
using baseline_profiles::dex2oat_code_units;
using baseline_profiles::flags_request_compilation;
using baseline_profiles::uncompilable_reason;
using baseline_profiles::UncompilableReason;

// The HRF spelling the baseline-profile post-processor expects:
// `Lcls;->name(args)ret`, in pre-obfuscation names.
std::string hrf_descriptor(const DexMethod* method) {
  std::string descriptor = show_deobfuscated(method);
  boost::replace_all(descriptor, ".", "->");
  boost::replace_all(descriptor, ":(", "(");
  return descriptor;
}

// NOTE: `baseline_profiles::is_compiled` is a deliberate under-approximation,
// kept because the never_inline analysis has been tuned against it. It
// ignores the startup flag and the no-code / @NeverCompile gates. For
// profile-health reporting use `uncompilable_reason` and
// `flags_request_compilation` above, which model dex2oat exactly; the gap
// between the two is reported as
// `profile_<name>_compiled_legacy_overcount`.
using baseline_profiles::is_compiled;

// Eligibility bounds for the never-inline analysis. Each shadows a threshold
// inside ART's own inliner, and each default is a deliberate margin over ART's
// number -- see the doc strings in bind_config. Grouped in a struct rather than
// passed as four loose parameters because three of them are size_t and a
// positional transposition would compile silently.
struct NeverInlineThresholds {
  size_t max_caller_instructions;
  size_t max_caller_registers;
  uint32_t max_callee_code_units;
  size_t min_callee_instructions;
};

struct MinHotCallsitesThresholds {
  size_t min_hot_callsites;
  uint32_t min_code_units;
};

void never_inline(bool attach_annotations,
                  float hot_block_appear_threshold,
                  float hot_method_appear_threshold,
                  const NeverInlineThresholds& thresholds,
                  const MinHotCallsitesThresholds& min_hot_callsites_thresholds,
                  const Scope& scope,
                  const baseline_profiles::BaselineProfile& baseline_profile,
                  PassManager& mgr,
                  const method_profiles::MethodProfiles& method_profiles) {
  DexAnnotationSet anno_set;
  anno_set.add_annotation(std::make_unique<DexAnnotation>(
      type::dalvik_annotation_optimization_NeverInline(),
      DexAnnotationVisibility::DAV_BUILD));

  never_inline_analysis::HotCallsites hot_callsites(
      scope, baseline_profile, method_profiles,
      never_inline_analysis::HotCallsiteThresholds{
          .hot_block_appear_threshold = hot_block_appear_threshold,
          .hot_method_appear_threshold = hot_method_appear_threshold,
          .max_caller_instructions = thresholds.max_caller_instructions,
          .max_caller_registers = thresholds.max_caller_registers,
      });
  const auto& hot_cold_callees = hot_callsites.hot_cold_callees;
  const auto& hot_callsite_counts = hot_callsites.hot_callsite_counts;
  mgr.incr_metric("never_inline_callers_too_many_instructions",
                  hot_callsites.callers_too_many_instructions);
  mgr.incr_metric("never_inline_callers_too_many_registers",
                  hot_callsites.callers_too_many_registers);
  mgr.incr_metric("never_inline_hot_cold_callees", hot_cold_callees.size());
  mgr.incr_metric("never_inline_hot_hot_callees", hot_callsite_counts.size());

  // Attach annotation to callees where beneficial.
  std::atomic<size_t> callees_already_never_inline = 0;
  std::atomic<size_t> callees_too_hot = 0;
  std::atomic<size_t> callees_simple = 0;
  std::atomic<size_t> callees_too_small = 0;
  std::atomic<size_t> callees_too_large = 0;
  std::atomic<size_t> callees_always_throw = 0;
  std::atomic<size_t> callees_annotation_attached = 0;
  std::atomic<size_t> callees_annotated = 0;
  size_t callees_min_hot_callsites = 0;
  UnorderedMap<DexMethod*, size_t> min_hot_callsites_callees;
  const never_inline_analysis::NeverInlineCriteria criteria{
      .max_callee_code_units = thresholds.max_callee_code_units,
      .min_callee_instructions = thresholds.min_callee_instructions,
      .min_hot_callsites = min_hot_callsites_thresholds.min_hot_callsites,
      .min_hot_callsites_min_code_units =
          min_hot_callsites_thresholds.min_code_units,
  };
  walk::code(scope, [&](DexMethod* method, IRCode& code) {
    const auto verdict = never_inline_analysis::decide_never_inline(
        code,
        has_anno(method, type::dalvik_annotation_optimization_NeverInline()),
        hot_cold_callees.count_unsafe(method) != 0u,
        hot_callsite_counts.load(method), criteria);
    switch (verdict.decision) {
    case never_inline_analysis::NeverInlineDecision::kAlreadyNeverInline:
      callees_already_never_inline.fetch_add(1);
      return;
    case never_inline_analysis::NeverInlineDecision::kNoCandidate:
      return;
    case never_inline_analysis::NeverInlineDecision::kTooHot:
      callees_too_hot.fetch_add(1);
      return;
    case never_inline_analysis::NeverInlineDecision::kIneligible:
      switch (verdict.ineligibility) {
      case never_inline_analysis::Ineligibility::kAlwaysThrows:
        callees_always_throw.fetch_add(1);
        return;
      case never_inline_analysis::Ineligibility::kTooLarge:
        callees_too_large.fetch_add(1);
        return;
      case never_inline_analysis::Ineligibility::kTooSmall:
        callees_too_small.fetch_add(1);
        return;
      case never_inline_analysis::Ineligibility::kSimple:
        callees_simple.fetch_add(1);
        return;
      case never_inline_analysis::Ineligibility::kEligible:
        not_reached();
      }
      return;
    case never_inline_analysis::NeverInlineDecision::kAnnotate:
      break;
    }
    const bool min_hot_callsites_rule_met = verdict.min_hot_callsites_rule_met;

    // Counts callees that PASSED every gate, whether or not an annotation is
    // then attached -- deliberately, because it is what makes an estimate-mode
    // run
    // (`never_inline_estimate` without `attach_annotations`) report what the
    // pass would do without touching bytecode. The name predates that use and
    // reads as a count of attachments, so `never_inline_callees_annotated`
    // below is the one to read for those; this one is kept under its old name
    // because it is a published metric and renaming it would silently empty
    // whatever consumes it.
    callees_annotation_attached.fetch_add(1);
    if (min_hot_callsites_rule_met) {
      ++callees_min_hot_callsites;
      min_hot_callsites_callees.emplace(method,
                                        hot_callsite_counts.load(method));
    }
    if (!attach_annotations) {
      return;
    }
    callees_annotated.fetch_add(1);
    if (method->get_anno_set() != nullptr) {
      method->get_anno_set()->combine_with(anno_set);
      return;
    }
    auto access = method->get_access();
    // attach_annotation_set requires the method to be synthetic.
    // A bit bizarre, and suggests that Redex' code to mutate annotations is
    // ripe for an overhaul. But I won't fight that here.
    method->set_access(access | ACC_SYNTHETIC);
    auto res = method->attach_annotation_set(
        std::make_unique<DexAnnotationSet>(anno_set));
    always_assert(res);
    method->set_access(access);
  });
  mgr.incr_metric("never_inline_callees_already_never_inline",
                  callees_already_never_inline.load());
  mgr.incr_metric("never_inline_callees_too_hot", callees_too_hot.load());
  mgr.incr_metric("never_inline_callees_simple", callees_simple.load());
  mgr.incr_metric("never_inline_callees_too_small", callees_too_small.load());
  mgr.incr_metric("never_inline_callees_too_large", callees_too_large.load());
  mgr.incr_metric("never_inline_callees_always_throw",
                  callees_always_throw.load());
  mgr.incr_metric("never_inline_callees_annotation_attached",
                  callees_annotation_attached.load());
  mgr.incr_metric("never_inline_callees_annotated", callees_annotated.load());
  // Callees that pass the gates solely through `min_hot_callsites`.
  mgr.incr_metric("never_inline_callees_min_hot_callsites",
                  callees_min_hot_callsites);
  // For each such callee, there is one metric whose value is the number of its
  // call sites that count toward `min_hot_callsites`.
  for (const auto& [method, callsites] :
       UnorderedIterable(min_hot_callsites_callees)) {
    mgr.set_metric(
        "never_inline_min_hot_callsites_" + show_deobfuscated(method),
        static_cast<int64_t>(callsites));
  }
}

void never_compile_impl(
    const Scope& scope,
    const std::string& baseline_profile_name,
    const baseline_profiles::BaselineProfileConfig& baseline_profile_config,
    const method_profiles::MethodProfiles& method_profiles,
    PassManager& mgr,
    baseline_profiles::BaselineProfile* baseline_profile,
    UnorderedSet<const DexMethod*>* never_compiled) {
  const auto excluded_interaction_ids =
      never_compile_analysis::excluded_interaction_ids(baseline_profile_config);

  InsertOnlyConcurrentMap<DexMethod*, uint32_t> never_compile_methods;
  std::atomic<size_t> methods_already_never_compile = 0;
  std::atomic<size_t> methods_annotation_attached = 0;
  std::atomic<size_t> methods_annotation_not_attached = 0;
  std::atomic<size_t> never_compile_callcount_threshold_mets{0};
  std::atomic<size_t> never_compile_perf_threshold_mets{0};
  std::atomic<size_t> never_compile_called_coverage_threshold_mets{0};
  std::atomic<size_t> never_compile_strings_lookup_methods_matches{0};
  walk::parallel::code(scope, [&](DexMethod* method, IRCode& code) {
    auto rules = never_compile_analysis::select_never_compile(
        method, code, *baseline_profile, baseline_profile_config,
        excluded_interaction_ids, method_profiles);
    if (!rules) {
      return;
    }
    if (rules->callcount) {
      never_compile_callcount_threshold_mets.fetch_add(1);
    }
    if (rules->perf) {
      never_compile_perf_threshold_mets.fetch_add(1);
    }
    if (rules->called_coverage) {
      never_compile_called_coverage_threshold_mets.fetch_add(1);
    }
    if (rules->strings_lookup) {
      never_compile_strings_lookup_methods_matches.fetch_add(1);
    }
    if (!rules->any()) {
      return;
    }

    never_compile_methods.emplace(method,
                                  method->get_code()->estimate_code_units());

    if (has_anno(method, type::dalvik_annotation_optimization_NeverCompile())) {
      methods_already_never_compile.fetch_add(1);
      return;
    }

    methods_annotation_not_attached.fetch_add(1);
    return;
  });
  for (auto&& [method, _0] : UnorderedIterable(never_compile_methods)) {
    baseline_profile->methods.erase(method);
    // Dropping the entry is the whole decision -- nothing attaches
    // @NeverCompile here -- so the verdict is invisible to anything that later
    // looks at the method. Hand it to the caller so top-off does not pad the
    // method straight back in.
    if (never_compiled != nullptr) {
      never_compiled->insert(method);
    }
  }
  mgr.incr_metric(baseline_profile_name + "_never_compile_methods",
                  never_compile_methods.size());
  mgr.incr_metric(baseline_profile_name + "_methods_already_never_compile",
                  methods_already_never_compile.load());
  mgr.incr_metric(baseline_profile_name + "_methods_annotation_attached",
                  methods_annotation_attached.load());
  mgr.incr_metric(baseline_profile_name + "_methods_annotation_not_attached",
                  methods_annotation_not_attached.load());
  mgr.incr_metric(baseline_profile_name + "_never_compile_callcount",
                  never_compile_callcount_threshold_mets.load());
  mgr.incr_metric(baseline_profile_name + "_never_compile_perf",
                  never_compile_perf_threshold_mets.load());
  mgr.incr_metric(baseline_profile_name + "_never_compile_called_coverage",
                  never_compile_called_coverage_threshold_mets.load());
  mgr.incr_metric(
      baseline_profile_name + "_never_compile_strings_lookup_methods_matches",
      never_compile_strings_lookup_methods_matches.load());
  auto ordered_never_compile_methods = unordered_to_ordered(
      never_compile_methods, [](const auto& a, const auto& b) {
        if (a.second != b.second) {
          return a.second > b.second;
        }
        return compare_dexmethods(a.first, b.first);
      });
  ordered_never_compile_methods.resize(
      std::min(ordered_never_compile_methods.size(), size_t(10)));
  for (size_t i = 0; i < ordered_never_compile_methods.size(); ++i) {
    auto& [method, code_units] = ordered_never_compile_methods[i];
    mgr.incr_metric(baseline_profile_name + "_never_compile_methods_" +
                        std::to_string(i) + "_" + show_deobfuscated(method),
                    code_units);
  }
}

void never_compile(
    const Scope& scope,
    const baseline_profiles::BaselineProfileConfigMap& baseline_profile_configs,
    const method_profiles::MethodProfiles& method_profiles,
    PassManager& mgr,
    UnorderedMap<std::string, baseline_profiles::BaselineProfile>&
        baseline_profiles,
    UnorderedSet<const DexMethod*>* never_compiled) {
  for (auto& entry : UnorderedIterable(baseline_profiles)) {
    const auto& bp_name = entry.first;
    const auto& cur_bp_config = baseline_profile_configs.at(bp_name);
    if (!cur_bp_config.harvest_config.enable_never_compile) {
      continue;
    }
    auto& bp = entry.second;
    never_compile_impl(scope, bp_name, cur_bp_config, method_profiles, mgr, &bp,
                       never_compiled);
  }
}

// What write_methods() actually emitted, and why it dropped what it dropped.
// `dex2oat_compilable` is the headline health number: entries that survive
// every dex2oat gate AND whose flags ask for compilation. Everything else in a
// profile is weight without benefit.
struct MethodWriteStats {
  size_t in_scope{0}; // profile entries whose class is in scope
  size_t written{0}; // lines actually emitted
  size_t stripped{0};

  size_t dex2oat_compilable{0};
  size_t dex2oat_compilable_code_units{0};
  size_t compilable_but_not_requested{0};

  size_t uncompilable_clinit{0};
  size_t uncompilable_clinit_code_units{0};
  size_t uncompilable_no_code{0};
  size_t uncompilable_never_compile{0};
  size_t uncompilable_never_compile_code_units{0};
  size_t uncompilable_huge{0};
  size_t uncompilable_huge_code_units{0};
  size_t uncompilable_code_units{0};
  size_t uncompilable_but_requested{0};

  size_t classes_written_to{0};
  size_t classes_left_without_entry{0};

  size_t non_root_dropped{0};

  size_t topoff_target{0};
  size_t topoff_candidates{0};
  size_t topoff_candidates_return_void{0};
  size_t topoff_excluded_never_compile{0};
  size_t topoff_added{0};
  size_t topoff_added_return_void{0};
  size_t topoff_added_code_units{0};
  size_t topoff_shortfall{0};

  UnorderedMap<std::string, size_t> by_flags;

  size_t uncompilable() const {
    return uncompilable_clinit + uncompilable_no_code +
           uncompilable_never_compile + uncompilable_huge;
  }
};

// What write_methods() takes from the pass beyond the profile itself.
struct WriteMethodsConfig {
  uint32_t huge_method_max{baseline_profiles::DEFAULT_ART_HUGE_METHOD_MAX};
  // 0 disables top-off.
  size_t topoff_target_entries{0};
  // Every type in the root store. Required: used to report what the profile
  // carried that this pass will not write.
  const UnorderedSet<const DexType*>* root_types{nullptr};
  // Methods some config's never-compile analysis removed from its profile.
  // Padding with one of them would reinstate what that analysis just decided
  // against, so they are barred from the candidate pool.
  const UnorderedSet<const DexMethod*>* never_compiled{nullptr};
};

// What write_classes() actually emitted, so the caller can report it.
struct ClassWriteStats {
  size_t written{0};
  size_t external_skipped{0};
  size_t non_root_skipped{0};
  size_t deobfuscation_failures{0};
  size_t unmatched{0};
};

ClassWriteStats write_classes(const baseline_profiles::BaselineProfile& bp,
                              const UnorderedSet<const DexType*>& root_types,
                              std::ostream& os) {
  ClassWriteStats stats;
  std::vector<std::string_view> class_names;
  class_names.reserve(bp.classes.size());
  size_t deob_issues{0};
  unordered_for_each(bp.classes, [&](auto* cls) {
    if (cls->is_external()) {
      ++stats.external_skipped;
      return;
    }
    // Same reason as the method side: a module class in the profile is dropped
    // by the binary converter, so do not write it in the first place.
    if (root_types.count(cls->get_type()) == 0) {
      ++stats.non_root_skipped;
      TRACE(APW, 1, "Not writing non-root-store profile class %s", SHOW(cls));
      return;
    }
    auto* deobf_str = cls->get_deobfuscated_name_or_null();
    if (deobf_str == nullptr) {
      ++deob_issues;
      TRACE(APW, 1, "Failed to retrieve deobfuscated name for %s", SHOW(cls));
      deobf_str = cls->get_name();
    }
    redex_assert(deobf_str != nullptr);
    class_names.emplace_back(deobf_str->str());
  });
  if (deob_issues > 0) {
    TRACE(APW, 0,
          "Failed to retrieve deobfuscated name for %zu classes, run with "
          "TRACE=APW:1 to get details.",
          deob_issues);
  }

  os << "# " << class_names.size()
     << " classes from resolved and internal types\n";
  std::sort(class_names.begin(), class_names.end());
  for (auto& cls : class_names) {
    os << cls << "\n";
  }

  os << "# " << bp.unmatched_classes.size()
     << " classes from unresolved types\n";
  std::vector<std::string_view> unmatched;
  unmatched.reserve(bp.unmatched_classes.size());
  unordered_transform(bp.unmatched_classes, std::back_inserter(unmatched),
                      [](const auto& str) { return std::string_view(str); });
  std::sort(unmatched.begin(), unmatched.end());
  for (auto& cls : unmatched) {
    os << cls << "\n";
  }

  stats.written = class_names.size();
  stats.deobfuscation_failures = deob_issues;
  stats.unmatched = unmatched.size();
  return stats;
}

} // namespace

std::ostream& operator<<(std::ostream& os,
                         const baseline_profiles::MethodFlags& flags) {
  if (flags.hot) {
    os << "H";
  }
  if (flags.startup) {
    os << "S";
  }
  if (flags.post_startup) {
    os << "P";
  }
  return os;
}

void ArtProfileWriterPass::bind_config() {
  bind("never_inline_estimate", false, m_never_inline_estimate);
  bind("never_inline_attach_annotations", false,
       m_never_inline_attach_annotations);
  bind("never_inline_hot_block_appear_threshold",
       never_inline_analysis::kDefaultAppearThreshold,
       m_never_inline_hot_block_appear_threshold);
  bind("never_inline_hot_method_appear_threshold",
       never_inline_analysis::kDefaultAppearThreshold,
       m_never_inline_hot_method_appear_threshold);
  bind("never_inline_max_caller_instructions",
       never_inline_analysis::kDefaultMaxCallerInstructions,
       m_never_inline_max_caller_instructions,
       "Skip a caller with more estimated instructions "
       "(`IRCode::count_opcodes`) than this. Shadows ART's 1024-HIR caller "
       "budget, with a margin -- but in a DIFFERENT UNIT: HIR instructions are "
       "not IR opcodes (measured 1.83-1.99 HIR per distinct dex pc, up to 3.60 "
       "on tiny methods), so this value can land on either side of 1024 HIR "
       "depending on the method.");
  bind("never_inline_max_caller_registers",
       never_inline_analysis::kDefaultMaxCallerRegisters,
       m_never_inline_max_caller_registers,
       "Skip a caller needing more registers than this. Shadows ART's 32-slot "
       "inlining environment budget, with no margin.");
  bind(
      "never_inline_max_callee_code_units",
      never_inline_analysis::kDefaultMaxCalleeCodeUnits,
      m_never_inline_max_callee_code_units,
      "Do not annotate a callee larger than this many estimated code units "
      "(`IRCode::estimate_code_units`). Shadows ART's own callee size cliff, "
      "with a large margin: the cliff is cited as 14 code units in this file's "
      "history and as 32 (`NotInlinedCodeItem`) elsewhere, and neither number "
      "has been verified against a measurement.");
  bind("never_inline_min_callee_instructions",
       never_inline_analysis::kDefaultMinCalleeInstructions,
       m_never_inline_min_callee_instructions,
       "Do not annotate a callee with fewer estimated instructions than this: "
       "ART inlines trivial bodies whatever the annotation says, so the "
       "annotation would be dead DEX weight.");
  bind("never_inline_min_hot_callsites",
       never_inline_analysis::kDefaultMinHotCallsites,
       m_never_inline_min_hot_callsites,
       "Annotate a callee with `@NeverInline` if at least this many of its "
       "call sites are hot, with hotness defined by "
       "`never_inline_hot_block_appear_threshold` and "
       "`never_inline_hot_method_appear_threshold`. INT_MAX disables this. "
       "Inlining puts a compiled copy of the callee's body in every caller, so "
       "a callee with many hot call sites gets many copies, which increase the "
       "OAT size and the amount of code loaded at startup. Annotating it keeps "
       "one shared copy, at the cost of a call at each site.");
  bind("never_inline_min_hot_callsites_min_code_units",
       kDefaultNeverInlineMinHotCallsitesMinCodeUnits,
       m_never_inline_min_hot_callsites_min_code_units,
       "Apply `never_inline_min_hot_callsites` only to callees that have at "
       "least this many estimated code units (`IRCode::estimate_code_units`).");
  after_configuration([this] {
    always_assert_log(m_never_inline_min_hot_callsites >= 1,
                      "Set never_inline_min_hot_callsites to an integer >= 1, "
                      "or leave it unset to turn the rule off.");
  });

  bind("include_strings_lookup_class", false, m_include_strings_lookup_class);
  bind("override_strip_classes", std::nullopt, m_override_strip_classes,
       "Override the strip_classes flag to the one given.");

  bind("huge_method_max", baseline_profiles::DEFAULT_ART_HUGE_METHOD_MAX,
       m_huge_method_max,
       "Treat a profile entry larger than this many code units as "
       "uncompilable. Shadows ART's own `huge_method_threshold_`, whose "
       "default is 10000 and which dex2oat applies with a strict `>`. Raise it "
       "beyond any real method to disable the gate.");
  bind("topoff_target_entries", 0, m_topoff_target_entries,
       "Pad the default baseline profile with extra dex2oat-compilable methods "
       "until it holds this many entries. 0 disables. This is a measurement "
       "aid: pinning the entry count makes the amount of AOT-compiled code the "
       "same from one build to the next, so a size or startup comparison "
       "between two builds is not confounded by the profile itself having "
       "changed size. Pick a target at or above the largest profile the app "
       "produces. Never removes anything: a profile already at or over the "
       "target is left alone, which reads as `topoff_added` 0 and "
       "`topoff_shortfall` 0 against a non-zero `topoff_target`.");
}

void ArtProfileWriterPass::eval_pass(DexStoresVector& /*stores*/,
                                     ConfigFiles& /*conf*/,
                                     PassManager& mgr) {
  if (m_never_inline_attach_annotations) {
    m_reserved_refs_handle = mgr.reserve_refs(name(),
                                              ReserveRefsInfo(/* frefs */ 0,
                                                              /* trefs */ 1,
                                                              /* mrefs */ 0));
  }
}

MethodWriteStats write_methods(
    const Scope& root_scope,
    const baseline_profiles::BaselineProfile& baseline_profile,
    const WriteMethodsConfig& config,
    std::ofstream& ofs) {
  MethodWriteStats stats;
  always_assert(config.root_types != nullptr);
  const auto& root_types = *config.root_types;

  // Walking the root store rather than the whole scope is what keeps module
  // entries out of the file: the binary converter resolves the profile against
  // the base APK, so an entry naming a module class is dropped there anyway,
  // silently, and the written count stops matching what reaches the device.
  // Expected to be zero -- a non-zero value means some upstream source started
  // admitting module methods.
  for (auto&& entry : UnorderedIterable(baseline_profile.methods)) {
    const auto* method = entry.first;
    if (root_types.count(method->get_class()) != 0) {
      continue;
    }
    ++stats.non_root_dropped;
    TRACE(APW, 1, "Not writing non-root-store profile entry %s", SHOW(method));
  }

  // We order H before not-H. In each category, we order SP -> S -> P -> none.
  struct MethodFlagsLess {
    bool operator()(const baseline_profiles::MethodFlags& lhs,
                    const baseline_profiles::MethodFlags& rhs) const {
      if (lhs.hot != rhs.hot) {
        return lhs.hot;
      }
      auto idx = [](const baseline_profiles::MethodFlags& flags) {
        return (flags.startup ? 2 : 0) + (flags.post_startup ? 1 : 0);
      };
      return idx(lhs) > idx(rhs);
    }
  };
  std::map<baseline_profiles::MethodFlags, std::vector<std::string>,
           MethodFlagsLess>
      methods;

  UnorderedSet<const DexType*> classes_with_written_method;
  UnorderedSet<const DexType*> classes_only_uncompilable;

  walk::classes(root_scope, [&](DexClass* cls) {
    for (auto* method : cls->get_all_methods()) {
      auto it = baseline_profile.methods.find(method);
      if (it == baseline_profile.methods.end()) {
        continue;
      }
      const auto& flags = it->second;
      ++stats.in_scope;

      std::ostringstream flags_ss;
      flags_ss << flags;
      ++stats.by_flags[flags_ss.str()];

      size_t code_units = dex2oat_code_units(method);
      auto reason = uncompilable_reason(method, config.huge_method_max);
      bool wanted = flags_request_compilation(flags);

      switch (reason) {
      case UncompilableReason::kNoCode:
        ++stats.uncompilable_no_code;
        break;
      case UncompilableReason::kClinit:
        ++stats.uncompilable_clinit;
        stats.uncompilable_clinit_code_units += code_units;
        break;
      case UncompilableReason::kNeverCompile:
        ++stats.uncompilable_never_compile;
        stats.uncompilable_never_compile_code_units += code_units;
        break;
      case UncompilableReason::kHugeMethod:
        ++stats.uncompilable_huge;
        stats.uncompilable_huge_code_units += code_units;
        break;
      case UncompilableReason::kNone:
        if (wanted) {
          ++stats.dex2oat_compilable;
          stats.dex2oat_compilable_code_units += code_units;
        } else {
          // Compilable in principle, but the flags do not ask for it. Today
          // this only happens for post-startup-only entries.
          ++stats.compilable_but_not_requested;
        }
        break;
      }
      if (reason != UncompilableReason::kNone) {
        stats.uncompilable_code_units += code_units;
        if (wanted) {
          // The profile asked dex2oat to compile something it structurally
          // cannot. Counted before the entry is dropped, so this reports what
          // upstream produced rather than what ships.
          ++stats.uncompilable_but_requested;
        }
        // Dropped. Nothing here can ever become compiled code, so keeping it
        // only costs bytes in the shipped app package and in the profile
        // installed on every device. `classes_left_without_entry` below
        // reports the one exposure.
        classes_only_uncompilable.insert(cls->get_type());
        ++stats.stripped;
        continue;
      }

      classes_with_written_method.insert(cls->get_type());
      methods[flags].emplace_back(hrf_descriptor(method));
    }
  });

  // Top-off, to hold the entry count fixed across builds. See
  // `topoff_target_entries` in bind_config for why.
  //
  // Padding entries carry H and nothing else. H is the one flag dex2oat honours
  // unconditionally: S is compiled only on a device that is not in low-memory
  // mode, and P alone is never compiled anywhere, so neither reliably buys the
  // compiled code the padding is there to hold steady. Note that `by_flags`
  // below counts only what the profile itself supplied, so padding does not
  // appear in the flag census.
  stats.topoff_target = config.topoff_target_entries;
  size_t union_size = 0;
  for (const auto& p : methods) {
    union_size += p.second.size();
  }
  if (config.topoff_target_entries > union_size) {
    auto selection = baseline_profiles::select_smallest_topoff_methods(
        root_scope, baseline_profile, config.topoff_target_entries - union_size,
        config.huge_method_max, config.never_compiled);
    stats.topoff_candidates = selection.candidates;
    stats.topoff_candidates_return_void = selection.candidates_returning_void;
    stats.topoff_excluded_never_compile = selection.excluded_candidates;
    stats.topoff_added = selection.methods.size();
    stats.topoff_added_return_void = selection.methods_returning_void;
    baseline_profiles::MethodFlags hot_only;
    hot_only.hot = true;
    for (auto* method : selection.methods) {
      classes_with_written_method.insert(method->get_class());
      methods[hot_only].emplace_back(hrf_descriptor(method));
      auto code_units = dex2oat_code_units(method);
      stats.topoff_added_code_units += code_units;
      ++stats.dex2oat_compilable;
      stats.dex2oat_compilable_code_units += code_units;
    }
    stats.topoff_shortfall =
        config.topoff_target_entries - union_size - stats.topoff_added;
  }

  // Stripping is only free for a class that keeps at least one other entry.
  // Where it does not, the class disappears from whatever class set the
  // HRF-to-binary converter derives from the method lines, which can cost
  // app-image preloading. Report it rather than guessing.
  unordered_erase_if(classes_only_uncompilable, [&](const auto* type) {
    return classes_with_written_method.count(type) != 0;
  });
  stats.classes_left_without_entry = classes_only_uncompilable.size();

  for (auto& p : methods) {
    if (!p.second.empty()) {
      stats.written += p.second.size();
      ofs << "# " << p.second.size() << " " << p.first
          << " methods from write_methods().\n";
      std::sort(p.second.begin(), p.second.end());
      for (auto& str : p.second) {
        ofs << p.first << str << "\n";
      }
    }
  }
  stats.classes_written_to = classes_with_written_method.size();
  return stats;
}

void ArtProfileWriterPass::run_pass(DexStoresVector& stores,
                                    ConfigFiles& conf,
                                    PassManager& mgr) {
  if (m_never_inline_attach_annotations) {
    always_assert(m_reserved_refs_handle);
    mgr.release_reserved_refs(*m_reserved_refs_handle);
    m_reserved_refs_handle = std::nullopt;
  }

  UnorderedSet<const DexMethodRef*> method_refs_without_def;
  const auto& method_profiles = conf.get_method_profiles();

  auto scope = build_class_scope(stores);
  // Only the root store ships alongside the profile, so it bounds everything
  // this pass WRITES -- the entries emitted and the pool top-off pads from.
  // Profile construction upstream stays store-agnostic on purpose: InterDexPass
  // and ClinitOutlinePass consume the same profiles to drive optimizations,
  // where a hot module method is still real information. `stores[0]` is the
  // root store, as `get_root_store_types` relies on too.
  always_assert(!stores.empty());
  auto root_scope = build_class_scope(stores[0].get_dexen());
  auto root_types = get_root_store_types(stores);

  auto baseline_profiles_tuple = baseline_profiles::get_baseline_profiles(
      scope,
      conf.get_baseline_profile_configs(),
      method_profiles,
      &method_refs_without_def,
      false /* apply_forced_flags */);
  auto& baseline_profiles = std::get<1>(baseline_profiles_tuple);
  auto& manual_profile = std::get<0>(baseline_profiles_tuple);

  // Load classes from input.
  manual_profile.load_classes(scope, conf, "manual");
  manual_profile.mark = manual_profile.classes.size();
  // Only configs that get_baseline_profiles actually generated a profile for
  // are of interest here. It deliberately omits the default config when
  // use_final_redex_generated_profile is false, and looking that config up with
  // operator[] would resurrect it as an empty profile that then gets emitted
  // and shadows the preprocessed one.
  for (auto& [config_name, baseline_profile] :
       UnorderedIterable(baseline_profiles)) {
    baseline_profile.load_classes(scope, conf, config_name);
    baseline_profile.mark = baseline_profile.classes.size();
  }

  auto add_class = [&](DexClass* cls) {
    manual_profile.classes.insert(cls);
    for (const auto& [config_name, baseline_profile_config] :
         UnorderedIterable(conf.get_baseline_profile_configs())) {
      if (!baseline_profile_config.options.use_final_redex_generated_profile) {
        continue;
      }
      auto it = baseline_profiles.find(config_name);
      if (it != baseline_profiles.end()) {
        it->second.classes.insert(cls);
      }
    }
  };

  for (const auto& [config_name, baseline_profile_config] :
       UnorderedIterable(conf.get_baseline_profile_configs())) {

    auto baseline_profiles_it = baseline_profiles.find(config_name);
    if (baseline_profiles_it == baseline_profiles.end()) {
      continue;
    }
    if (baseline_profile_config.options.include_all_startup_classes) {
      const std::vector<std::string>& interdexorder =
          conf.get_coldstart_classes();
      std::vector<DexClass*> coldstart_classes;
      auto& baseline_profile = baseline_profiles_it->second;
      for (const auto& entry : interdexorder) {
        // Limit to just the 20% cold start set
        if (entry.find("ColdStart20PctEnd") != std::string::npos) {
          break;
        }

        DexType* type = DexType::get_type(entry);
        if (type != nullptr) {
          auto* coldstart_class = type_class(type);
          if (coldstart_class != nullptr) {
            coldstart_classes.push_back(coldstart_class);
            baseline_profile.classes.insert(coldstart_class);
          }
        }
      }

      baseline_profiles::MethodFlags flags;
      flags.hot = true;
      flags.startup = false;
      // walk::code, not walk::methods: the latter also visits abstract and
      // native methods, which have no code for dex2oat to compile. This is the
      // only insertion path that can put a code-less method into a
      // BaselineProfile. <clinit> and @NeverCompile still have code, so the
      // full predicate is applied rather than just a code check.
      size_t inserted = 0;
      walk::code(coldstart_classes,
                 [&baseline_profile, &inserted, flags, this](DexMethod* method,
                                                             IRCode&) {
                   if (uncompilable_reason(method, m_huge_method_max) !=
                       UncompilableReason::kNone) {
                     return;
                   }
                   if (baseline_profile.methods.emplace(method, flags).second) {
                     ++inserted;
                   }
                 });
      mgr.incr_metric(std::string("profile_") + config_name +
                          "_from_include_all_startup_classes",
                      inserted);
    }
  }

  UnorderedSet<const DexMethod*> never_compiled;
  never_compile(scope, conf.get_baseline_profile_configs(), method_profiles,
                mgr, baseline_profiles, &never_compiled);
  mgr.set_metric("never_compiled_methods", never_compiled.size());

  std::optional<baseline_profiles::BaselineProfile> never_inline_profile;
  if (m_never_inline_estimate || m_never_inline_attach_annotations) {
    never_inline_profile = manual_profile;
  }

  mgr.incr_metric(
      "profile_manual_forced_method_flags",
      baseline_profiles::apply_forced_method_flags(scope, &manual_profile));
  for (auto& [config_name, baseline_profile] :
       UnorderedIterable(baseline_profiles)) {
    mgr.incr_metric(
        std::string("profile_") + config_name + "_forced_method_flags",
        baseline_profiles::apply_forced_method_flags(scope, &baseline_profile));
  }

  auto* store_fence_helper_type = DexType::get_type(STORE_FENCE_HELPER_NAME);
  if (store_fence_helper_type != nullptr) {
    // helper class existing means we materialized IOPCODE_WRITE_BARRIER
    // Add it in for it to be compiled.
    auto* store_fence_helper_cls = type_class(store_fence_helper_type);
    always_assert(store_fence_helper_cls);
    add_class(store_fence_helper_cls);
  }
  if (m_include_strings_lookup_class) {
    walk::classes(scope, [&](DexClass* cls) {
      if (cls->rstate.is_generated() &&
          cls->get_perf_sensitive() == PerfSensitiveGroup::STRINGS_LOOKUP) {
        add_class(cls);
      }
    });
  }
  // Classes synthesized after profile collection that earlier passes spliced
  // into the coldstart list. MethodProfiles can never name them, so they
  // arrive through ConfigFiles instead.
  size_t extra_baseline_classes = 0;
  for (const auto& name : conf.get_extra_baseline_profile_classes()) {
    auto* type = DexType::get_type(name);
    if (type == nullptr) {
      continue;
    }
    auto* cls = type_class(type);
    if (cls == nullptr || cls->is_external()) {
      continue;
    }
    add_class(cls);
    extra_baseline_classes++;
  }
  mgr.incr_metric("baseline_profile_extra_classes", extra_baseline_classes);

  auto resolve_strip_classes = [&](const auto& bp) {
    return m_override_strip_classes ? *m_override_strip_classes
                                    : bp.options.strip_classes;
  };

  // Transitively close classes. We always do this for metrics.
  if (conf.get_default_baseline_profile_config()
          .options.transitively_close_classes) {
    manual_profile.transitively_close_classes(scope);
  }
  for (auto& entry : UnorderedIterable(baseline_profiles)) {
    const auto& bp_name = entry.first;
    auto& bp = entry.second;
    const auto transitively_close_classes =
        conf.get_baseline_profile_configs()
            .at(bp_name)
            .options.transitively_close_classes;
    if (transitively_close_classes) {
      bp.transitively_close_classes(scope);
    }
  }

  // Reported per profile below, in gather_metrics.
  UnorderedMap<std::string, MethodWriteStats> method_write_stats;
  UnorderedMap<std::string, ClassWriteStats> class_write_stats;

  WriteMethodsConfig write_config{.huge_method_max = m_huge_method_max,
                                  .root_types = &root_types,
                                  .never_compiled = &never_compiled};
  for (const auto& entry : UnorderedIterable(baseline_profiles)) {
    const auto& bp_name = entry.first;
    const auto& bp = entry.second;
    const auto strip_classes =
        resolve_strip_classes(conf.get_baseline_profile_configs().at(bp_name));
    auto output_name = conf.metafile(bp_name + "-baseline-profile.txt");
    std::ofstream ofs{output_name.c_str()};
    if (!strip_classes) {
      class_write_stats[bp_name] = write_classes(bp, root_types, ofs);
    }
    // Only the default config becomes the shipped baseline.prof. The others
    // exist to measure deltas against it, and the manual profile lands in a
    // file the post-processor does not pick up, so padding either would
    // perturb a comparison without reaching a device.
    auto bp_write_config = write_config;
    bp_write_config.topoff_target_entries =
        bp_name == baseline_profiles::DEFAULT_BASELINE_PROFILE_CONFIG_NAME
            ? m_topoff_target_entries
            : 0;
    method_write_stats[bp_name] =
        write_methods(root_scope, bp, bp_write_config, ofs);
    ofs.flush();
    always_assert_log(ofs.good(), "Could not write baseline profile %s",
                      output_name.c_str());
  }
  std::ofstream ofs{conf.metafile(BASELINE_PROFILES_FILE)};
  if (!resolve_strip_classes(conf.get_default_baseline_profile_config())) {
    class_write_stats["manual"] =
        write_classes(manual_profile, root_types, ofs);
  }
  method_write_stats["manual"] =
      write_methods(root_scope, manual_profile, write_config, ofs);
  ofs.flush();
  always_assert_log(ofs.good(), "Could not write additional baseline profiles");

  auto gather_metrics = [&](const auto& bp_name, const auto& bp_config_name,
                            const auto& profile) {
    static const size_t APPEAR100_BUCKETS = 10;
    std::atomic<size_t> code_units{0};
    std::atomic<size_t> compiled_methods{0};
    std::atomic<size_t> compiled_code_units_cold{0};
    std::array<std::atomic<size_t>, APPEAR100_BUCKETS + 1>
        compiled_code_units_hot_by_appear100{};
    std::atomic<size_t> compiled_code_units_hot_super{0};
    std::atomic<size_t> compiled_code_units_unknown{0};
    InsertOnlyConcurrentSet<DexType*> method_classes;
    walk::parallel::code(scope, [&](DexMethod* method, IRCode& code) {
      auto it = profile.methods.find(method);
      if (it == profile.methods.end()) {
        return;
      }
      method_classes.insert(method->get_class());
      auto ecu = code.estimate_code_units();
      code_units += ecu;
      if (is_compiled(method, it->second)) {
        compiled_methods++;
        size_t cold = 0;
        std::array<size_t, APPEAR100_BUCKETS + 1> hot_by_appear100{0};
        size_t hot_super = 0;
        size_t unknown = 0;
        for (auto* block : code.cfg().blocks()) {
          ecu = block->estimate_code_units();
          auto* sb = source_blocks::get_first_source_block(block);
          if (sb != nullptr && !sb->foreach_val_early([](const auto& v) {
                return !v || v->val > 0;
              })) {
            cold += ecu;
          } else if (sb != nullptr && sb->foreach_val_early([](const auto& v) {
                       return v && v->val > 0;
                     })) {
            float max_appear100 = 0;
            sb->foreach_val([&](const auto& v) {
              if (v) {
                max_appear100 = std::max(max_appear100, v->appear100);
              }
            });
            if (max_appear100 > 100) {
              hot_super += ecu;
            } else {
              size_t bucket = (size_t)(max_appear100 * APPEAR100_BUCKETS / 100);
              hot_by_appear100[bucket] += ecu;
            }
          } else {
            unknown += ecu;
          }
        }
        if (cold) {
          compiled_code_units_cold += cold;
        }
        for (size_t bucket = 0; bucket <= APPEAR100_BUCKETS; ++bucket) {
          if (hot_by_appear100[bucket]) {
            compiled_code_units_hot_by_appear100[bucket] +=
                hot_by_appear100[bucket];
          }
        }
        if (hot_super) {
          compiled_code_units_hot_super += hot_super;
        }
        if (unknown) {
          compiled_code_units_unknown += unknown;
        }
      }
    });

    size_t root_dexes_with_methods = [&]() {
      size_t cnt = 0;
      redex_assert(stores[0].is_root_store());
      for (const auto& dex : stores[0].get_dexen()) {
        for (auto* cls : dex) {
          if (method_classes.count_unsafe(cls->get_type())) {
            ++cnt;
            break;
          }
        }
      }
      return cnt;
    }();

    auto prefix = std::string("profile_") + bp_name + "_";
    mgr.incr_metric(prefix + "classes.in", profile.mark);
    mgr.incr_metric(prefix + "classes", profile.classes.size());
    mgr.incr_metric(prefix + "unmatched_classes",
                    profile.unmatched_classes.size());
    mgr.incr_metric(prefix + "methods", profile.methods.size());
    mgr.incr_metric(prefix + "code_units", (size_t)code_units);
    mgr.incr_metric(prefix + "compiled", (size_t)compiled_methods);
    size_t compiled_code_units_hot = compiled_code_units_hot_super;
    for (size_t bucket = 0; bucket <= APPEAR100_BUCKETS; ++bucket) {
      auto appear100 = (size_t)compiled_code_units_hot_by_appear100[bucket];
      compiled_code_units_hot += appear100;
      std::stringstream ss;
      ss << std::setw(3) << std::setfill('0')
         << (bucket * (100 / APPEAR100_BUCKETS));
      mgr.incr_metric(prefix + "compiled_code_units_hot_appear" + ss.str(),
                      appear100);
    }
    mgr.incr_metric(prefix + "compiled_code_units",
                    compiled_code_units_cold.load() + compiled_code_units_hot +
                        compiled_code_units_unknown.load());
    mgr.incr_metric(prefix + "compiled_code_units_cold",
                    compiled_code_units_cold);
    mgr.incr_metric(prefix + "compiled_code_units_hot",
                    compiled_code_units_hot);
    mgr.incr_metric(prefix + "compiled_code_units_hot_super",
                    compiled_code_units_hot_super);
    mgr.incr_metric(prefix + "compiled_code_units_unknown",
                    compiled_code_units_unknown);

    const auto& bp_config =
        conf.get_baseline_profile_configs().at(bp_config_name);
    for (auto&& [interaction_id, interaction_name] : bp_config.interactions) {
      mgr.incr_metric(prefix + "interaction_" + interaction_id, 1);
    }
    const auto& bp_options = bp_config.options;
    if (bp_options.oxygen_modules) {
      mgr.incr_metric(prefix + "oxygen_modules", 1);
    }
    if (bp_options.strip_classes &&
        (!m_override_strip_classes || *m_override_strip_classes)) {
      mgr.incr_metric(prefix + "strip_classes", 1);
    }
    if (bp_options.transitively_close_classes) {
      mgr.incr_metric(prefix + "transitively_close_classes", 1);
    }
    if (bp_options.use_redex_generated_profile) {
      mgr.incr_metric(prefix + "use_redex_generated_profile", 1);
    }
    if (bp_options.include_all_startup_classes) {
      mgr.incr_metric(prefix + "include_all_startup_classes", 1);
    }
    if (bp_options.use_final_redex_generated_profile) {
      mgr.incr_metric(prefix + "use_final_redex_generated_profile", 1);
    }

    mgr.incr_metric(prefix + "root_dexes_with_profile_methods",
                    root_dexes_with_methods);

    // --- Profile health -----------------------------------------------------
    // The question these answer: of everything we are about to ship, how much
    // can dex2oat actually turn into compiled code, and what is the rest?
    auto mws_it = method_write_stats.find(bp_name);
    if (mws_it != method_write_stats.end()) {
      const auto& s = mws_it->second;

      // Headline. Entries that clear every dex2oat gate AND whose flags ask
      // for compilation. This is the only number that buys anything.
      mgr.set_metric(prefix + "dex2oat_compilable", s.dex2oat_compilable);
      mgr.set_metric(prefix + "dex2oat_compilable_code_units",
                     s.dex2oat_compilable_code_units);

      // Everything the profile handed us that cannot become code. These are
      // no longer written, so this measures upstream quality: drive it to zero
      // by fixing what puts them in the profile, not by filtering harder.
      mgr.set_metric(prefix + "uncompilable", s.uncompilable());
      mgr.set_metric(prefix + "uncompilable_code_units",
                     s.uncompilable_code_units);
      mgr.set_metric(prefix + "uncompilable_clinit", s.uncompilable_clinit);
      mgr.set_metric(prefix + "uncompilable_clinit_code_units",
                     s.uncompilable_clinit_code_units);
      mgr.set_metric(prefix + "uncompilable_no_code", s.uncompilable_no_code);
      mgr.set_metric(prefix + "uncompilable_never_compile",
                     s.uncompilable_never_compile);
      mgr.set_metric(prefix + "uncompilable_never_compile_code_units",
                     s.uncompilable_never_compile_code_units);
      mgr.set_metric(prefix + "uncompilable_huge", s.uncompilable_huge);
      mgr.set_metric(prefix + "uncompilable_huge_code_units",
                     s.uncompilable_huge_code_units);
      // Entries the profile marks for compilation that dex2oat will refuse.
      // Drive this to zero.
      mgr.set_metric(prefix + "uncompilable_but_requested",
                     s.uncompilable_but_requested);
      // Compilable, but flagged post-startup only, so never compiled anywhere.
      mgr.set_metric(prefix + "compilable_but_not_requested",
                     s.compilable_but_not_requested);

      // Useful share of everything the profile asked us to consider, in basis
      // points so it survives the integer metric type. Denominator is the
      // pre-exclusion population, so this stays comparable across a change
      // that removes entries -- it measures upstream profile quality. Padding
      // is ours rather than the profile's, so it is out of the numerator too;
      // leaving it in would let the ratio exceed 10000.
      size_t upstream_compilable = s.dex2oat_compilable - s.topoff_added;
      mgr.set_metric(
          prefix + "dex2oat_compilable_bp",
          s.in_scope == 0 ? 0 : (10000 * upstream_compilable / s.in_scope));
      // Useful share of what actually ships. This one does move when entries
      // are excluded, and is the number that should approach 10000.
      mgr.set_metric(
          prefix + "dex2oat_compilable_shipped_bp",
          s.written == 0 ? 0 : (10000 * s.dex2oat_compilable / s.written));

      mgr.set_metric(prefix + "entries_in_scope", s.in_scope);
      mgr.set_metric(prefix + "entries_written", s.written);
      mgr.set_metric(prefix + "entries_stripped", s.stripped);
      // Entries in the profile whose class never showed up in scope, so no
      // line was written for them at all.
      mgr.set_metric(prefix + "entries_out_of_scope",
                     profile.methods.size() - s.in_scope);
      mgr.set_metric(prefix + "classes_with_written_method",
                     s.classes_written_to);
      // Only non-zero when stripping is on: classes that lost their last
      // entry. Check this before trusting a size win.
      mgr.set_metric(prefix + "classes_left_without_entry",
                     s.classes_left_without_entry);
      // Profile entries naming a class outside the root store. Drive this to
      // zero: it is the alarm for an upstream source admitting module methods,
      // which the binary converter would silently drop.
      mgr.set_metric(prefix + "non_root_dropped", s.non_root_dropped);

      // Top-off. `entries_written` should land on `topoff_target` exactly;
      // a non-zero `topoff_shortfall` means the eligible pool ran out, which
      // `topoff_candidates` distinguishes from a selection bug.
      mgr.set_metric(prefix + "topoff_target", s.topoff_target);
      mgr.set_metric(prefix + "topoff_candidates", s.topoff_candidates);
      // Padding that returns void folds into one compiled body, so it is the
      // cheapest kind. `topoff_added_return_void` below `topoff_added` means
      // the ranking fell back to value returns. `topoff_candidates_return_void`
      // counts candidates by return TYPE at any size, so it is an upper bound
      // on the pool, not the size of the one-code-unit pool padding comes from.
      mgr.set_metric(prefix + "topoff_candidates_return_void",
                     s.topoff_candidates_return_void);
      // Candidates barred because a never-compile analysis had already
      // rejected them. Non-zero means top-off would otherwise have reinstated
      // a method Redex decided not to compile.
      mgr.set_metric(prefix + "topoff_excluded_never_compile",
                     s.topoff_excluded_never_compile);
      mgr.set_metric(prefix + "topoff_added", s.topoff_added);
      mgr.set_metric(prefix + "topoff_added_return_void",
                     s.topoff_added_return_void);
      mgr.set_metric(prefix + "topoff_added_code_units",
                     s.topoff_added_code_units);
      mgr.set_metric(prefix + "topoff_shortfall", s.topoff_shortfall);

      // Flag census, so a regression can be attributed to the interaction
      // config that produced it. Emit every key, including the zeros: a metric
      // that only appears once it becomes non-zero shows up in a BSB report as
      // a new row rather than as a delta, which is easy to miss. Only P and
      // the empty set ask for no AOT compilation at all; S alone still
      // compiles, but only on a device that is not in low-memory mode.
      // {key as written by operator<<, metric suffix}
      static const std::array<std::pair<const char*, const char*>, 8>
          kFlagCombos = {{{"HSP", "HSP"},
                          {"HS", "HS"},
                          {"HP", "HP"},
                          {"H", "H"},
                          {"SP", "SP"},
                          {"S", "S"},
                          {"P", "P"},
                          {"", "none"}}};
      for (const auto& [key, suffix] : kFlagCombos) {
        auto it = s.by_flags.find(key);
        mgr.set_metric(prefix + "entries_flags_" + suffix,
                       it == s.by_flags.end() ? 0 : it->second);
      }

      // How far the legacy is_compiled() predicate is from modelling dex2oat.
      // Non-zero means the never_inline analysis is working off a wrong idea
      // of what gets compiled.
      int64_t legacy = static_cast<int64_t>(compiled_methods.load());
      mgr.set_metric(prefix + "compiled_legacy_overcount",
                     legacy - static_cast<int64_t>(upstream_compilable));
    }

    auto cws_it = class_write_stats.find(bp_name);
    if (cws_it != class_write_stats.end()) {
      const auto& c = cws_it->second;
      mgr.set_metric(prefix + "classes_written", c.written);
      mgr.set_metric(prefix + "classes_external_skipped", c.external_skipped);
      mgr.set_metric(prefix + "classes_non_root_skipped", c.non_root_skipped);
      mgr.set_metric(prefix + "classes_unmatched_written", c.unmatched);
      // Every one of these ships an obfuscated name that the converter cannot
      // resolve, i.e. a dead line.
      mgr.set_metric(prefix + "classes_deobfuscation_failures",
                     c.deobfuscation_failures);
    }
  };
  gather_metrics("manual",
                 baseline_profiles::DEFAULT_BASELINE_PROFILE_CONFIG_NAME,
                 manual_profile);
  for (auto&& [name, profile] : UnorderedIterable(baseline_profiles)) {
    always_assert(name != "manual");
    gather_metrics(name, name, profile);
  }
  // Absence of a metric is invisible in a base-vs-diff report: drop a config
  // and every profile_<thatname>_* row stops existing rather than going to
  // zero. Report how many profiles were actually accounted for.
  mgr.set_metric("baseline_profiles_reported", baseline_profiles.size() + 1);

  mgr.incr_metric("method_refs_without_def", method_refs_without_def.size());

  mgr.incr_metric(
      "used_bzl_baseline_profile_config",
      static_cast<int64_t>(conf.get_did_use_bzl_baseline_profile_config()));

  InsertOnlyConcurrentMap<DexMethod*, uint32_t> huge_methods;
  walk::parallel::code(scope, [&](DexMethod* method, IRCode& code) {
    auto code_units = code.estimate_code_units();
    code_units += code.cfg().get_size_adjustment();
    if (code_units > assessments::HUGE_METHOD_THRESHOLD) {
      huge_methods.emplace(method, code_units);
    }
  });
  for (auto [method, code_units] : UnorderedIterable(huge_methods)) {
    mgr.incr_metric("huge_methods_" + show_deobfuscated(method), code_units);
  }

  if (!never_inline_profile) {
    return;
  }

  never_inline(
      m_never_inline_attach_annotations,
      m_never_inline_hot_block_appear_threshold,
      m_never_inline_hot_method_appear_threshold,
      NeverInlineThresholds{
          .max_caller_instructions = m_never_inline_max_caller_instructions,
          .max_caller_registers = m_never_inline_max_caller_registers,
          .max_callee_code_units = m_never_inline_max_callee_code_units,
          .min_callee_instructions = m_never_inline_min_callee_instructions,
      },
      MinHotCallsitesThresholds{
          .min_hot_callsites = m_never_inline_min_hot_callsites,
          .min_code_units = m_never_inline_min_hot_callsites_min_code_units,
      },
      scope, *never_inline_profile, mgr, method_profiles);
}

static ArtProfileWriterPass s_pass;
