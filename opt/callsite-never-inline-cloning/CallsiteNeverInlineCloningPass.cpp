/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "CallsiteNeverInlineCloningPass.h"

#include <algorithm>
#include <sstream>

#include <boost/format.hpp> // NOLINT

#include "BaselineProfile.h"
#include "ConcurrentContainers.h"
#include "ConfigFiles.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexAccess.h"
#include "DexUtil.h"
#include "IRCode.h"
#include "MethodOverrideGraph.h"
#include "MethodProfiles.h"
#include "MethodUtil.h"
#include "NeverInlineEligibility.h"
#include "PassManager.h"
#include "RedexContext.h"
#include "Resolver.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "Trace.h"
#include "TypeUtil.h"
#include "Walkers.h"

using namespace baseline_profiles;

namespace {

// A single call instruction, inside `caller`, whose containing block is
// provably cold.
struct ColdCallsite {
  DexMethod* caller;
  IRInstruction* invoke_insn;
};

// Per-callee facts, computed once for every method in `scope`, before any
// call-site classification runs. Looked up by the parallel caller walk
// instead of dereferencing a callee's own CFG (or re-running a per-callee
// check) from there: `no_optimizations`/`no_outlining`/
// `already_never_inline`/`blocklisted` depend only on the callee itself, never
// on which call site is asking, so computing them once here instead of once
// per call site avoids repeating an annotation lookup, a no-outlining check,
// and a blocklist prefix scan for every invoke of a frequently-called callee.
struct CalleeFacts {
  uint32_t code_units;
  never_inline_analysis::Ineligibility eligibility;
  bool has_catch;
  bool no_optimizations;
  bool no_outlining;
  bool non_renamable_class;
  bool already_never_inline;
  bool blocklisted;
};

// A shape-eligible candidate, carrying the profitability-model inputs and
// outputs computed for it, plus the stable generated name its clone will use
// and whether that clone needs an extra access flag once it exists.
struct RankedCandidate {
  DexMethod* callee;
  const DexString* clone_name;
  bool needs_final_marking;
  uint32_t callee_code_units;
  size_t estimated_incremental_mrefs;
  int64_t estimated_oat_code_units_saved;
  int64_t estimated_dex_cost;
  int64_t estimated_net;
};

// Descending by estimated net; ties broken by a deterministic method
// ordering, never by container iteration order or address.
bool less_ranked_candidate_desc(const RankedCandidate& a,
                                const RankedCandidate& b) {
  if (a.estimated_net != b.estimated_net) {
    return a.estimated_net > b.estimated_net;
  }
  return compare_dexmethods(a.callee, b.callee);
}

// Deliberately identical to PartialApplicationPass's generated-name hash.
uint64_t get_stable_hash(const std::string& s) {
  uint64_t stable_hash{s.size()};
  for (auto c : s) {
    stable_hash = stable_hash * 7 + c;
  }
  return stable_hash;
}

bool method_profile_appears(const method_profiles::MethodProfiles& mp,
                            DexMethod* method,
                            float appear_threshold) {
  for (const auto& p : mp.all_interactions()) {
    auto it = p.second.find(method);
    if (it != p.second.end() && it->second.appear_percent >= appear_threshold) {
      return true;
    }
  }
  return false;
}

// The declaring class's own name for blocklist matching: its deobfuscated
// name once one has been set, else its raw class name. This pass runs ahead
// of any renaming pass, so a class has not necessarily been assigned a
// deobfuscated name yet (that generally happens no earlier than
// InitialRenameClassesPass/ObfuscatePass); falling back to the raw name
// keeps blocklist prefixes matchable before that point.
std::string_view blocklist_name_of(const DexClass* cls) {
  auto deobf = cls->get_deobfuscated_name_or_empty();
  return deobf.empty() ? cls->get_name()->str() : deobf;
}

using Config = CallsiteNeverInlineCloningPass::Config;
using Stats = CallsiteNeverInlineCloningPass::Stats;

// Everything computed about callees in one dedicated, read-only pass over
// `scope`, before any call-site classification runs.
struct CalleeContext {
  InsertOnlyConcurrentMap<DexMethod*, CalleeFacts> facts;
  // An invoke-virtual's resolved callee is an exact-dispatch target if it is
  // a "non-true-virtual" -- it neither overrides nor is overridden by any
  // other method in `scope` -- the same notion
  // MethodInliner/HotColdMethodSpecializingPass/CallGraph use for their own
  // exact-devirtualization decisions. This is strictly broader than "is
  // declared final", since a method can go unoverridden in practice without
  // being marked `final`.
  InsertOnlyConcurrentSet<DexMethod*> non_true_virtuals;
};

// Builds the method-override graph once for the whole run, and precomputes, in
// a dedicated read-only walk, the per-callee facts
// `collect_callsite_profiles`'s caller walk needs -- so that walk (which
// runs one thread per class, all concurrently) never has to dereference some
// OTHER method's CFG, or repeat a per-callee check, to get them.
//
// Every method with code in `scope` is required to have its CFG already
// built: `PassManager` establishes that invariant for every real pass run,
// and `clone_mixed_hotness_callees`'s own doc comment states the same
// requirement for direct (e.g. test) callers.
CalleeContext collect_callee_facts(const Scope& scope, const Config& config) {
  CalleeContext ctx;

  auto mog = method_override_graph::build_graph(scope);
  ctx.non_true_virtuals =
      method_override_graph::get_non_true_virtuals(*mog, scope);

  walk::parallel::code(scope, [&](DexMethod* method, IRCode& code) {
    redex_assert(code.cfg_built());
    bool has_catch = false;
    for (auto* block : code.cfg().blocks()) {
      if (block->is_catch()) {
        has_catch = true;
        break;
      }
    }
    bool blocklisted = false;
    auto blocklist_name = blocklist_name_of(type_class(method->get_class()));
    for (const auto& prefix : config.blocklist) {
      if (blocklist_name.starts_with(prefix)) {
        blocklisted = true;
        break;
      }
    }
    ctx.facts.emplace(
        method,
        CalleeFacts{
            code.estimate_code_units(),
            never_inline_analysis::never_inline_eligibility(
                method, config.max_callee_code_units,
                config.min_callee_instructions),
            has_catch, method->rstate.no_optimizations(),
            method->rstate.should_not_outline(),
            !can_rename(type_class(method->get_class())),
            has_anno(method,
                     type::dalvik_annotation_optimization_NeverInline()),
            blocklisted});
  });

  return ctx;
}

// The raw inputs to the profitability model: every eligible call site
// inside a profiled-compiled caller, classified hot or cold, plus every
// caller/call-site-level skip reason encountered along the way.
struct CallsiteProfile {
  ConcurrentMap<DexMethod*, std::vector<ColdCallsite>> cold_callsites;
  AtomicMap<DexMethod*, size_t> hot_callsite_counts;
  Stats stats;
};

// Classifies every eligible call site inside a profiled-compiled caller as
// hot or cold, and counts, per callee, how many landed in each bucket.
//
// This walk's per-caller/per-block classification (caller gates, catch
// check, throw-adjacent skip, hot/cold split) intentionally mirrors
// ArtProfileWriterPass::never_inline's own, for exactly the call sites this
// pass itself ever resolves (an exact invoke-static/invoke-direct, or an
// invoke-virtual to a non-true-virtual callee) -- not ArtProfileWriterPass's
// full analysis, which is broader: it also chases a receiver-type map to
// sometimes resolve an otherwise-ambiguous `invoke-virtual`, and follows a
// forwarder-method chain (`is_simple`) to its ultimate callee. This pass
// deliberately does neither, so the two passes classify identically only on
// the narrower set of call sites this pass considers at all.
// TODO(T226760922): consider factoring both into a common templated helper.
CallsiteProfile collect_callsite_profiles(
    const Scope& scope,
    const Config& config,
    const BaselineProfile& baseline_profile,
    const method_profiles::MethodProfiles& method_profiles,
    const CalleeContext& callee_context) {
  CallsiteProfile profile;

  auto is_sufficiently_hot = [&](cfg::Block* block, DexMethod* callee) {
    if (!is_compiled(baseline_profile, callee)) {
      return false;
    }
    if (config.hot_block_appear_threshold >= 0 &&
        !source_blocks::maybe_hot(block, config.hot_block_appear_threshold)) {
      return false;
    }
    if (config.hot_method_appear_threshold >= 0 &&
        !source_blocks::method_maybe_hot(callee,
                                         config.hot_method_appear_threshold) &&
        !method_profile_appears(method_profiles, callee,
                                config.hot_method_appear_threshold)) {
      return false;
    }
    return true;
  };

  // The unit of parallelization for `walk::parallel` is already one
  // DexClass per worker thread (every method in a class is visited
  // sequentially by the same thread that claimed the class), so each
  // worker's own `Stats` needs no locking at all while it accumulates --
  // only `profile.cold_callsites` (a `ConcurrentMap`, sharded per-key
  // locking) and `profile.hot_callsite_counts` (an `AtomicMap`) are ever
  // touched from more than one thread while the walk runs. Per-class
  // results are reduced into `profile.stats` via `Stats::operator+=` once
  // the whole walk completes.
  profile.stats =
      walk::parallel::classes<Stats>(scope, [&](DexClass* cls) -> Stats {
        Stats local_stats;
        walk::code(std::vector<DexClass*>{cls}, [&](DexMethod* caller,
                                                    IRCode& code) {
          redex_assert(code.cfg_built());
          // A pass must not rewrite bytecode belonging to a method whose
          // class is flagged `no_optimizations`.
          if (caller->rstate.no_optimizations()) {
            local_stats.callers_no_optimizations++;
            return;
          }
          if (!is_compiled(baseline_profile, caller)) {
            local_stats.callers_not_compiled++;
            return;
          }
          auto& cfg = code.cfg();
          switch (never_inline_analysis::caller_inline_budget(
              code.count_opcodes(), cfg.get_registers_size(),
              config.max_caller_instructions, config.max_caller_registers)) {
          case never_inline_analysis::CallerBudget::kTooManyInstructions:
            local_stats.callers_too_many_instructions++;
            return;
          case never_inline_analysis::CallerBudget::kTooManyRegisters:
            local_stats.callers_too_many_registers++;
            return;
          case never_inline_analysis::CallerBudget::kWithin:
            break;
          }
          auto skips = never_inline_analysis::for_each_exact_call_site(
              caller, cfg, callee_context.non_true_virtuals,
              [&](cfg::Block* block, IRInstruction* insn, DexMethod* callee) {
                bool callsite_has_catch =
                    cfg.get_succ_edge_of_type(block, cfg::EDGE_THROW) !=
                    nullptr;
                // A clone replaces the callee this invoke names, so the
                // invoke must name the definition itself.
                if (callee != insn->get_method()) {
                  local_stats.invokes_unresolved++;
                  return;
                }
                // Only present for callees in `scope`; see
                // `CalleeContext::facts`'s own comment above.
                const auto* facts = callee_context.facts.get(callee);
                if (facts == nullptr) {
                  local_stats.invokes_external_or_no_code_callee++;
                  return;
                }
                // <init>/<clinit> cannot be cloned under a different name:
                // the JVM and ART both require the literal names
                // "<init>"/"<clinit>" for these methods, so renaming would
                // break object-construction verification entirely.
                // (ArtProfileWriterPass has no equivalent exclusion: it
                // only ever attaches an annotation, never renames.)
                if (method::is_any_init(callee)) {
                  local_stats.invokes_init_callee++;
                  return;
                }
                if (facts->no_optimizations) {
                  local_stats.invokes_no_optimizations_callee++;
                  return;
                }
                // `no_outlining` protects methods whose body or identity must
                // not be copied into a new method. ReachableNativesPass uses it
                // for load-library entry points: cloning one would create an
                // unpinned copy whose forwarding body supplies a non-constant
                // library-name parameter, violating that pass's final analysis.
                // This is the same gate used by HotColdMethodSpecializingPass
                // and the other body-extracting/outlining transforms. A plain
                // `dont_inline` bit is intentionally not enough: it constrains
                // Redex inlining, not body cloning.
                if (facts->no_outlining) {
                  local_stats.invokes_no_outlining_callee++;
                  return;
                }
                // Adding even an otherwise unreachable helper changes the
                // declared-method set that reflection can observe. Follow
                // PartialApplication's same-class helper rule and only add a
                // clone to a class whose name is not kept for reflective use.
                if (facts->non_renamable_class) {
                  local_stats.invokes_non_renamable_callee_class++;
                  return;
                }
                if (facts->already_never_inline) {
                  local_stats.invokes_already_never_inline_callee++;
                  return;
                }
                if (facts->blocklisted) {
                  local_stats.invokes_blocklisted_callee++;
                  return;
                }
                if (callsite_has_catch && facts->has_catch) {
                  local_stats.invokes_callsite_and_callee_both_have_catch++;
                  return;
                }
                if (is_sufficiently_hot(block, callee)) {
                  profile.hot_callsite_counts.fetch_add(callee, 1);
                } else {
                  profile.cold_callsites.update(
                      callee,
                      [&](DexMethod*, std::vector<ColdCallsite>& v, bool) {
                        v.push_back(ColdCallsite{caller, insn});
                      });
                }
              });
          local_stats.invokes_throw_adjacent += skips.throw_adjacent;
          local_stats.invokes_super_opcode += skips.super_invoke;
          local_stats.invokes_interface_opcode += skips.interface_invoke;
          local_stats.invokes_unresolved += skips.unresolved;
          local_stats.invokes_external_or_no_code_callee +=
              skips.external_or_no_code;
          local_stats.invokes_ambiguous_virtual_callee +=
              skips.ambiguous_virtual;
        });
        return local_stats;
      });

  return profile;
}

// The profitability-model output: every candidate that survived every
// threshold and every cap, in deterministic net-descending order, plus the
// classification/rejection counters accumulated along the way.
struct RankedCandidates {
  std::vector<RankedCandidate> accepted;
  Stats stats;
};

// Determines the mixed-hotness population (a callee with at least one cold
// call site and at least one it could not prove cold -- a callee with only
// cold call sites needs no clone, since a plain `@NeverInline` already
// covers it), applies the profitability/volume model documented on
// `Config`'s own fields, and ranks + caps the survivors. Stable clone names are
// assigned here, before ranking, from the callee identity and deterministic
// iteration order; `create_clones` later interns only accepted methods.
RankedCandidates rank_and_cap_candidates(
    const Config& config,
    size_t iteration,
    const CalleeContext& callee_context,
    const CallsiteProfile& callsite_profile) {
  RankedCandidates result;

  auto hot_count_of = [&](DexMethod* callee) -> size_t {
    return callsite_profile.hot_callsite_counts.load(callee, 0);
  };

  // A candidate is a callee with at least one cold call site and at least
  // one it could not prove cold -- ArtProfileWriterPass's own "too hot to
  // ever-inline" rejection, the reason this pass exists. Shape-eligibility
  // below reuses the facts precomputed by `collect_callee_facts`, which
  // called the exact same `never_inline_analysis::never_inline_eligibility`
  // ArtProfileWriterPass calls for its own annotation decision, so a clone
  // this pass creates is always one that later run is willing to annotate.
  auto candidate_callees = unordered_to_ordered_keys(
      callsite_profile.cold_callsites, compare_dexmethods);
  std::vector<DexMethod*> mixed_hotness_callees;
  mixed_hotness_callees.reserve(candidate_callees.size());
  for (auto* callee : candidate_callees) {
    if (hot_count_of(callee) == 0) {
      result.stats.callees_all_cold_no_clone_needed++;
      continue;
    }
    switch (callee_context.facts.at(callee).eligibility) {
    case never_inline_analysis::Ineligibility::kAlwaysThrows:
      result.stats.callees_always_throw++;
      continue;
    case never_inline_analysis::Ineligibility::kTooLarge:
      result.stats.callees_too_large++;
      continue;
    case never_inline_analysis::Ineligibility::kTooSmall:
      result.stats.callees_too_small++;
      continue;
    case never_inline_analysis::Ineligibility::kSimple:
      result.stats.callees_simple++;
      continue;
    case never_inline_analysis::Ineligibility::kEligible:
      break;
    }
    mixed_hotness_callees.push_back(callee);
  }
  result.stats.mixed_hotness_callees = mixed_hotness_callees.size();

  // Candidates that clear every per-candidate threshold are ranked by
  // estimated net descending (ties broken by `compare_dexmethods`) before
  // the global caps are applied, so a lower-ranked candidate that still
  // fits is accepted even when a higher-ranked one did not.
  std::vector<RankedCandidate> ranked;
  ranked.reserve(mixed_hotness_callees.size());
  UnorderedMap<uint64_t, uint32_t> stable_hash_indices;
  for (auto* callee : mixed_hotness_callees) {
    size_t hot_count = hot_count_of(callee);
    if (hot_count < config.min_hot_callsites) {
      result.stats.rejected_insufficient_hot_callsites++;
      continue;
    }
    const auto& cold_callsites_for_callee =
        callsite_profile.cold_callsites.at_unsafe(callee);
    size_t cold_count = cold_callsites_for_callee.size();
    if (cold_count < config.min_cold_callsites) {
      result.stats.rejected_insufficient_cold_callsites++;
      continue;
    }
    auto* callee_cls = type_class(callee->get_class());
    // Match PartialApplicationPass's generated-name convention: a stable hash
    // of the full callee identity keeps helpers from different classes apart,
    // and a deterministic index disambiguates the vanishingly unlikely hash
    // collision. `$cnic$` is a reserved generated namespace, like `$spa$` and
    // `$ipa$`; no scan for hand-written methods using that namespace is needed.
    auto callee_stable_hash = get_stable_hash(show(callee));
    auto stable_hash_index = stable_hash_indices[callee_stable_hash]++;
    std::ostringstream oss;
    oss << callee->get_name()->str() << "$cnic$" << iteration << "$"
        << ((boost::format("%08x") % callee_stable_hash).str()) << "$"
        << stable_hash_index;
    const auto* clone_name = DexString::make_string(oss.str());
    // A non-final virtual method whose clone would otherwise stay virtual
    // and non-final (`make_method_from` copies access flags verbatim) is
    // invisible to ArtProfileWriterPass's own, narrower
    // `is_final(method) || is_final(cls)` virtual-eligibility check. Match
    // PartialApplicationPass and mark the generated helper `final` so the
    // later pass can annotate it. The stable generated name keeps independent
    // helpers from accidentally overriding one another.
    bool needs_final_marking =
        callee->is_virtual() && !is_final(callee) && !is_final(callee_cls);
    UnorderedSet<DexType*> distinct_cold_caller_classes;
    for (const auto& cs : cold_callsites_for_callee) {
      distinct_cold_caller_classes.insert(cs.caller->get_class());
    }
    // +1 for the clone's own definition; see `method_ref_cost`'s doc string
    // for why one ref per distinct calling class is the proxy used here.
    size_t estimated_incremental_mrefs =
        1 + distinct_cold_caller_classes.size();
    auto ecu = callee_context.facts.at(callee).code_units;
    int64_t saved =
        static_cast<int64_t>(cold_count) * static_cast<int64_t>(ecu);
    if (saved < config.min_estimated_oat_code_units_saved) {
      result.stats.rejected_insufficient_estimated_savings++;
      continue;
    }
    int64_t cost = static_cast<int64_t>(ecu) +
                   static_cast<int64_t>(config.method_ref_cost) *
                       static_cast<int64_t>(estimated_incremental_mrefs);
    int64_t net = saved - cost;
    if (net <= 0) {
      result.stats.rejected_non_positive_net++;
      continue;
    }
    ranked.push_back(RankedCandidate{callee, clone_name, needs_final_marking,
                                     ecu, estimated_incremental_mrefs, saved,
                                     cost, net});
  }
  std::sort(ranked.begin(), ranked.end(), less_ranked_candidate_desc);

  result.accepted.reserve(ranked.size());
  size_t total_clones = 0;
  uint64_t total_cloned_code_units = 0;
  for (auto& rc : ranked) {
    if (total_clones + 1 > config.max_total_clones) {
      result.stats.rejected_cap_max_total_clones++;
      continue;
    }
    if (total_cloned_code_units + rc.callee_code_units >
        config.max_total_cloned_code_units) {
      result.stats.rejected_cap_max_total_cloned_code_units++;
      continue;
    }
    total_clones++;
    total_cloned_code_units += rc.callee_code_units;
    result.stats.total_estimated_oat_code_units_saved +=
        rc.estimated_oat_code_units_saved;
    result.stats.total_estimated_method_refs += rc.estimated_incremental_mrefs;
    result.stats.total_estimated_dex_cost += rc.estimated_dex_cost;
    result.stats.total_estimated_net += rc.estimated_net;
    result.accepted.push_back(rc);
  }
  result.stats.total_cloned_code_units = total_cloned_code_units;
  result.stats.selected_candidates = result.accepted.size();

  return result;
}

// Creates every accepted clone from the program as it stood before ANY of
// this pass's rewrites -- clone creation and call-site redirection
// (`redirect_cold_callsites`) are fully separated so that a candidate's own
// clone never depends on whether some OTHER candidate happened to be
// processed earlier. (If callee A's body itself contains a cold call to
// candidate B, redirecting that call before A gets cloned would make A's
// clone reflect B's clone instead of the original B; which of A/B is
// net-ranked first must never change that outcome.) Every `DexMethodRef`
// created here is for a candidate that survived every check in
// `rank_and_cap_candidates`, so this is never reached under `estimate_only`.
std::vector<std::pair<DexMethod*, DexMethod*>> create_clones(
    const std::vector<RankedCandidate>& accepted) {
  std::vector<std::pair<DexMethod*, DexMethod*>> originals_and_clones;
  originals_and_clones.reserve(accepted.size());
  for (const auto& rc : accepted) {
    auto* original = rc.callee;
    // `make_method_from` copies access flags, the annotation set, and the
    // method's own `IRCode` (built CFG and `DexDebugItem` included) via
    // `IRCode`'s copy constructor. Every redirected call site was already
    // proven, above, to reach the original through an opcode matching its
    // access flags exactly; since the clone shares those flags, that same
    // opcode stays valid unchanged -- no opcode rewrite is ever needed, and
    // the only access-flag change ever made is the `ACC_FINAL` addition
    // below, which changes neither the clone's virtual-ness nor its
    // visibility nor which existing callers can reach it.
    auto* clone = DexMethod::make_method_from(original, original->get_class(),
                                              rc.clone_name);

    if (rc.needs_final_marking) {
      clone->set_access(clone->get_access() | ACC_FINAL);
    }

    clone->rstate.set_generated();
    clone->rstate.set_dont_inline();
    clone->rstate.set_force_hot_in_baseline_profile();
    // Creating the clone is a single whole-program structural decision,
    // analogous to profile-guided inlining or outlining. Force-H therefore
    // applies to every materialized profile rather than re-deciding the
    // transformation per profile.
    // Match the cold-only call sites this clone will serve.
    source_blocks::fill_source_block_entry_values(clone->get_code()->cfg(),
                                                  SourceBlock::Val(0, 0));
    // Run before any renaming pass (this pass's own canonical placement is
    // ahead of InitialRenameClassesPass), so `show(clone)` still reflects the
    // true, pre-obfuscation class and method names.
    clone->set_deobfuscated_name(show(clone));
    type_class(original->get_class())->add_method(clone);
    originals_and_clones.emplace_back(original, clone);
  }
  return originals_and_clones;
}

// Redirects every collected cold call site to its callee's clone. Each
// `invoke_insn` was captured by `collect_callsite_profiles`, before any
// clone existed, so this is the first and only time any of them is mutated.
// Each redirect only changes that one instruction's own method operand,
// independent of every other, so the order they're applied in is not
// observable in the output; no sort is needed here. Returns the total
// number of call sites redirected.
size_t redirect_cold_callsites(
    const std::vector<std::pair<DexMethod*, DexMethod*>>& originals_and_clones,
    const ConcurrentMap<DexMethod*, std::vector<ColdCallsite>>&
        cold_callsites) {
  size_t redirected = 0;
  for (const auto& [original, clone] : originals_and_clones) {
    const auto& sites = cold_callsites.at_unsafe(original);
    for (const auto& cs : sites) {
      cs.invoke_insn->set_method(clone);
      redirected++;
    }
    TRACE(CNIC, 3, "%s (%zu cold call site(s)) -> %s", SHOW(original),
          sites.size(), SHOW(clone));
  }
  return redirected;
}

} // namespace

void CallsiteNeverInlineCloningPass::bind_config() {
  bind("hot_block_appear_threshold", m_config.hot_block_appear_threshold,
       m_config.hot_block_appear_threshold,
       "A call site's containing block counts as possibly-hot only if its "
       "SourceBlock reports at least this appear100 (percentage of "
       "measured runs reaching the block). Defaults to -1, disabling this "
       "check (any executed block counts), matching ArtProfileWriterPass's "
       "own global default -- an app enabling this pass should set the same "
       "value it gives ArtProfileWriterPass's own "
       "`never_inline_hot_block_appear_threshold`.");
  bind("hot_method_appear_threshold", m_config.hot_method_appear_threshold,
       m_config.hot_method_appear_threshold,
       "A callee counts as possibly-hot on its own only if its entry block's "
       "SourceBlock, or its method-profiles appear_percent, reports at least "
       "this threshold. Defaults to -1, disabling this check, matching "
       "ArtProfileWriterPass's own global default -- see "
       "`hot_block_appear_threshold`'s doc string.");
  bind("max_caller_instructions", m_config.max_caller_instructions,
       m_config.max_caller_instructions,
       "Skip every call site inside a caller with more estimated "
       "instructions (`IRCode::count_opcodes`) than this. Shadows "
       "ArtProfileWriterPass's own `never_inline_max_caller_instructions`.");
  bind("max_caller_registers", m_config.max_caller_registers,
       m_config.max_caller_registers,
       "Skip every call site inside a caller needing more registers than "
       "this. Shadows ArtProfileWriterPass's own "
       "`never_inline_max_caller_registers`.");
  bind("max_callee_code_units", m_config.max_callee_code_units,
       m_config.max_callee_code_units,
       "Do not clone a callee larger than this many estimated code units "
       "(`IRCode::estimate_code_units`). Shadows ArtProfileWriterPass's own "
       "`never_inline_max_callee_code_units` -- a clone larger than this "
       "would never be annotated `@NeverInline` by a later "
       "ArtProfileWriterPass run anyway.");
  bind("min_callee_instructions", m_config.min_callee_instructions,
       m_config.min_callee_instructions,
       "Do not clone a callee with fewer estimated instructions than this. "
       "Shadows ArtProfileWriterPass's own "
       "`never_inline_min_callee_instructions`.");
  bind("min_hot_callsites", m_config.min_hot_callsites,
       m_config.min_hot_callsites,
       "Do not clone a callee reached from fewer than this many call sites "
       "this pass could not prove cold.");
  bind("min_cold_callsites", m_config.min_cold_callsites,
       m_config.min_cold_callsites,
       "Do not clone a callee reached from fewer than this many call sites "
       "this pass proved cold. A single cold call site's estimated saving "
       "rarely clears the fixed cost of a whole extra clone; raise this to "
       "require more volume before paying that cost.");
  bind("min_estimated_oat_code_units_saved",
       m_config.min_estimated_oat_code_units_saved,
       m_config.min_estimated_oat_code_units_saved,
       "Do not clone a callee whose estimated OAT/code-size win "
       "(`cold_callsite_count * callee_code_units`) is under this many "
       "estimated code units.");
  bind("max_total_clones", m_config.max_total_clones, m_config.max_total_clones,
       "Global cap on the number of clones this pass creates in one run. "
       "Candidates are ranked by estimated net benefit descending before "
       "this cap is applied, so the highest-value candidates win.");
  bind("max_total_cloned_code_units", m_config.max_total_cloned_code_units,
       m_config.max_total_cloned_code_units,
       "Global cap on the total estimated code units of every clone this "
       "pass creates in one run, applied in the same net-ranked order as "
       "`max_total_clones`.");
  bind("method_ref_cost", m_config.method_ref_cost, m_config.method_ref_cost,
       "Estimated fixed DEX cost, in code units, of one incremental method "
       "ref to the clone -- charged once per distinct class among the cold "
       "call sites being redirected, plus one for the clone's own "
       "definition (a conservative dex-placement-agnostic proxy, since "
       "InterDex has not run yet). Part of the estimated cost side of the "
       "profitability model.");
  bind("estimate_only", m_config.estimate_only, m_config.estimate_only,
       "Dry-run mode: compute every `Stats` field as a real run would, but "
       "create no clone and rewrite no call site.");
  bind("blocklist", m_config.blocklist, m_config.blocklist,
       "Skip candidate callees whose declaring class's deobfuscated name "
       "(or, if none has been set yet, its own raw class name) starts with "
       "any of these prefixes.");
}

CallsiteNeverInlineCloningPass::Stats
CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
    const Scope& scope,
    const Config& config,
    size_t iteration,
    const BaselineProfile& baseline_profile,
    const method_profiles::MethodProfiles& method_profiles) {
  auto callee_context = collect_callee_facts(scope, config);
  auto callsite_profile = collect_callsite_profiles(
      scope, config, baseline_profile, method_profiles, callee_context);
  auto ranked_candidates = rank_and_cap_candidates(
      config, iteration, callee_context, callsite_profile);

  Stats stats = callsite_profile.stats;
  stats += ranked_candidates.stats;

  if (config.estimate_only) {
    return stats;
  }

  auto originals_and_clones = create_clones(ranked_candidates.accepted);
  stats.clones_created = originals_and_clones.size();
  stats.cold_callsites_redirected = redirect_cold_callsites(
      originals_and_clones, callsite_profile.cold_callsites);

  return stats;
}

void CallsiteNeverInlineCloningPass::run_pass(DexStoresVector& stores,
                                              ConfigFiles& conf,
                                              PassManager& mgr) {
  if (g_redex->instrument_mode) {
    return;
  }

  auto scope = build_class_scope(stores);
  auto baseline_profile = baseline_profiles::get_default_baseline_profile(
      scope, conf.get_baseline_profile_configs(), conf.get_method_profiles());
  auto stats =
      clone_mixed_hotness_callees(scope, m_config, m_iteration,
                                  baseline_profile, conf.get_method_profiles());
  m_iteration++;

  TRACE(CNIC, 1, "Population (mixed-hotness, shape-eligible): %zu",
        stats.mixed_hotness_callees);
  TRACE(CNIC, 1, "Selected candidates (net-ranked, capped): %zu",
        stats.selected_candidates);
  TRACE(CNIC, 1, "Clones created: %zu", stats.clones_created);
  TRACE(CNIC, 1, "Cold call sites redirected: %zu",
        stats.cold_callsites_redirected);
  TRACE(CNIC, 1, "Total cloned code units: %zu",
        (size_t)stats.total_cloned_code_units);
  TRACE(CNIC, 1, "Total estimated OAT code units saved: %zd",
        (ssize_t)stats.total_estimated_oat_code_units_saved);
  TRACE(CNIC, 1, "Total estimated DEX cost: %zd",
        (ssize_t)stats.total_estimated_dex_cost);
  TRACE(CNIC, 1, "Total estimated net: %zd",
        (ssize_t)stats.total_estimated_net);

  mgr.incr_metric("mixed_hotness_callees", stats.mixed_hotness_callees);
  mgr.incr_metric("rejected_insufficient_hot_callsites",
                  stats.rejected_insufficient_hot_callsites);
  mgr.incr_metric("rejected_insufficient_cold_callsites",
                  stats.rejected_insufficient_cold_callsites);
  mgr.incr_metric("rejected_insufficient_estimated_savings",
                  stats.rejected_insufficient_estimated_savings);
  mgr.incr_metric("rejected_non_positive_net", stats.rejected_non_positive_net);
  mgr.incr_metric("rejected_cap_max_total_clones",
                  stats.rejected_cap_max_total_clones);
  mgr.incr_metric("rejected_cap_max_total_cloned_code_units",
                  stats.rejected_cap_max_total_cloned_code_units);
  mgr.incr_metric("estimate_only", m_config.estimate_only ? 1 : 0);
  mgr.incr_metric("selected_candidates", stats.selected_candidates);
  mgr.incr_metric("total_cloned_code_units", stats.total_cloned_code_units);
  mgr.incr_metric("total_estimated_oat_code_units_saved",
                  stats.total_estimated_oat_code_units_saved);
  mgr.incr_metric("total_estimated_method_refs",
                  stats.total_estimated_method_refs);
  mgr.incr_metric("total_estimated_dex_cost", stats.total_estimated_dex_cost);
  mgr.incr_metric("total_estimated_net", stats.total_estimated_net);
  mgr.incr_metric("clones_created", stats.clones_created);
  mgr.incr_metric("cold_callsites_redirected", stats.cold_callsites_redirected);
  mgr.incr_metric("callees_all_cold_no_clone_needed",
                  stats.callees_all_cold_no_clone_needed);
  mgr.incr_metric("callees_always_throw", stats.callees_always_throw);
  mgr.incr_metric("callees_too_large", stats.callees_too_large);
  mgr.incr_metric("callees_too_small", stats.callees_too_small);
  mgr.incr_metric("callees_simple", stats.callees_simple);
  mgr.incr_metric("callers_no_optimizations", stats.callers_no_optimizations);
  mgr.incr_metric("callers_not_compiled", stats.callers_not_compiled);
  mgr.incr_metric("callers_too_many_instructions",
                  stats.callers_too_many_instructions);
  mgr.incr_metric("callers_too_many_registers",
                  stats.callers_too_many_registers);
  mgr.incr_metric("invokes_super_opcode", stats.invokes_super_opcode);
  mgr.incr_metric("invokes_interface_opcode", stats.invokes_interface_opcode);
  mgr.incr_metric("invokes_unresolved", stats.invokes_unresolved);
  mgr.incr_metric("invokes_external_or_no_code_callee",
                  stats.invokes_external_or_no_code_callee);
  mgr.incr_metric("invokes_ambiguous_virtual_callee",
                  stats.invokes_ambiguous_virtual_callee);
  mgr.incr_metric("invokes_init_callee", stats.invokes_init_callee);
  mgr.incr_metric("invokes_no_optimizations_callee",
                  stats.invokes_no_optimizations_callee);
  mgr.incr_metric("invokes_no_outlining_callee",
                  stats.invokes_no_outlining_callee);
  mgr.incr_metric("invokes_non_renamable_callee_class",
                  stats.invokes_non_renamable_callee_class);
  mgr.incr_metric("invokes_already_never_inline_callee",
                  stats.invokes_already_never_inline_callee);
  mgr.incr_metric("invokes_blocklisted_callee",
                  stats.invokes_blocklisted_callee);
  mgr.incr_metric("invokes_callsite_and_callee_both_have_catch",
                  stats.invokes_callsite_and_callee_both_have_catch);
  mgr.incr_metric("invokes_throw_adjacent", stats.invokes_throw_adjacent);
}

static CallsiteNeverInlineCloningPass s_pass;
