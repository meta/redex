/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <climits>
#include <cstddef>
#include <cstdint>
#include <functional>

#include "ConcurrentContainers.h"
#include "ControlFlow.h"
#include "DexClass.h"
#include "IRInstruction.h"
#include "IROpcode.h"
#include "MethodUtil.h"
#include "NeverInlineEligibility.h"

namespace baseline_profiles {
struct BaselineProfile;
struct Dex2oatFacts;
} // namespace baseline_profiles

namespace method_profiles {
class MethodProfiles;
} // namespace method_profiles

namespace never_inline_analysis {

// The bounds of the call-site classification below. The caller bounds each
// shadow a threshold inside ART's own inliner; the appear thresholds say which
// call sites count as hot, a negative one leaving its check out.
struct HotCallsiteThresholds {
  float hot_block_appear_threshold;
  float hot_method_appear_threshold;
  size_t max_caller_instructions;
  size_t max_caller_registers;
};

// `ArtProfileWriterPass`'s defaults for these bounds, which its doc strings
// explain, for a pass that reads the configuration that pass runs with. The
// caller bounds default to `kDefaultMaxCallerInstructions` and
// `kDefaultMaxCallerRegisters`.
inline constexpr float kDefaultAppearThreshold = -1.0f;

// `ArtProfileWriterPass`'s defaults for its `min_hot_callsites` rule: off, and
// applied to callees of at least this many code units once on.
//
// Inlining replaces a call
//
//   invoke-static {...}, callee   // 3 code units
//   move-result vX                // 1 code unit
//
// with a copy of the callee, so it adds code only when the callee is longer
// than 4 code units. Therefore, 5 is the minimum callee size that can benefit
// from not inlining.
inline constexpr size_t kDefaultMinHotCallsites = INT_MAX;
inline constexpr uint32_t kDefaultMinHotCallsitesMinCodeUnits = 5;

// Whether the call sites of a caller are read, and if not, which bound it
// exceeds.
enum class CallerVerdict : uint8_t {
  kNotCompiled,
  kTooManyInstructions,
  kTooManyRegisters,
  kRead,
};

// The verdict on a caller that is `compiled` or not, with `instructions`
// (`IRCode::count_opcodes`) and `registers`
// (`ControlFlowGraph::get_registers_size`).
CallerVerdict classify_caller(bool compiled,
                              size_t instructions,
                              size_t registers,
                              size_t max_caller_instructions,
                              size_t max_caller_registers);

// Calls `f(insn)` on each invoke of `block` that is a call site, last first:
// every invoke except those constructing an exception the block then throws,
// up to and including the first of them that is not a constructor call.
template <typename F>
void for_each_block_callsite(cfg::Block* block, F&& f) {
  auto throw_invokes = throw_constructing_invokes(block);
  for (auto& mie : InstructionIterable(block).reversed()) {
    auto* insn = mie.insn;
    if (!opcode::is_an_invoke(insn->opcode()) ||
        throw_invokes.count(insn) != 0u) {
      continue;
    }
    f(insn);
  }
}

// Whether a call site in `block` is left out because the site is in a `try`
// and its callee has one too.
inline bool is_try_excluded(cfg::ControlFlowGraph& cfg,
                            cfg::Block* block,
                            bool callee_has_catch) {
  return callee_has_catch &&
         cfg.get_succ_edge_of_type(block, cfg::EDGE_THROW) != nullptr;
}

// A walk over the call sites of compiled callers. A call site counts when its
// caller is compiled and within the caller bounds, its callee resolves (an
// `invoke-virtual` through the receiver type the caller proves, and through
// the trivial forwarders `follow_forwarder` admits, see `is_simple`) to a
// method with code in a non-external class that is not a true virtual, it is
// not excluded by `is_try_excluded`, and `for_each_block_callsite` yields it.
struct CallsiteWalk {
  std::function<bool(DexMethod*)> caller_compiled;
  size_t max_caller_instructions;
  size_t max_caller_registers;
  // Whether the call sites of a caller over `max_caller_registers` are still
  // visited, marked as such.
  bool visit_callers_over_register_bound;
  // Whether a call into the trivial forwarder `forwarder` counts as a call of
  // the forwarder's callee rather than of the forwarder.
  std::function<bool(const DexMethod*)> follow_forwarder;
};

// Compiled callers the walk skipped, or marked, for exceeding a caller bound.
struct CallsiteWalkCounts {
  size_t callers_too_many_instructions{0};
  size_t callers_too_many_registers{0};
};

// Called from several threads at once, for each call site with the block it
// sits in, its callee, and whether its caller is within the register bound.
using CallsiteVisitor = std::function<void(
    cfg::Block* block, DexMethod* callee, bool within_register_bound)>;

// Every method in `scope` with code must have its CFG built.
CallsiteWalkCounts walk_callsites(const Scope& scope,
                                  const CallsiteWalk& walk,
                                  const CallsiteVisitor& visit);

// The call sites at which a baseline-compiled caller may inline its callee,
// each classified as hot or not, per callee: the walk above over callers
// dex2oat compiles (`baseline_profiles::dex2oat_compiles` with the entry's
// flags and the method's `dex2oat_facts`), following every forwarder. A site
// is hot when its callee is compiled and both appear thresholds hold.
// `dex2oat_facts` must hold every method of `baseline_profile`; it is computed
// up front because computing a method's size may simplify its CFG, which must
// not happen while the walk reads that CFG from another thread.
//
// The analysis behind `ArtProfileWriterPass`'s `@NeverInline` annotations,
// shared so that a pass predicting those annotations cannot drift from it.
// That pass reads the default baseline profile without forced method flags.
struct HotCallsites {
  HotCallsites(const Scope& scope,
               const baseline_profiles::BaselineProfile& baseline_profile,
               const InsertOnlyConcurrentMap<DexMethod*,
                                             baseline_profiles::Dex2oatFacts>&
                   dex2oat_facts,
               const method_profiles::MethodProfiles& method_profiles,
               const HotCallsiteThresholds& thresholds);

  // Compiled callers skipped for exceeding a caller bound.
  size_t callers_too_many_instructions{0};
  size_t callers_too_many_registers{0};
  // Callees with at least one call site that is not hot.
  InsertOnlyConcurrentSet<DexMethod*> hot_cold_callees;
  // Per callee with at least one hot call site, how many it has.
  AtomicMap<DexMethod*, size_t> hot_callsite_counts;
  // Per callee, how many call sites it has, hot or not.
  AtomicMap<DexMethod*, size_t> callsite_counts;
};

// `ArtProfileWriterPass`'s criteria for annotating a callee `@NeverInline`.
struct NeverInlineCriteria {
  uint32_t max_callee_code_units;
  size_t min_callee_instructions;
  size_t min_hot_callsites;
  uint32_t min_hot_callsites_min_code_units;
};

enum class NeverInlineDecision : uint8_t {
  kAlreadyNeverInline,
  // No call site that is not hot, and the `min_hot_callsites` rule unmet.
  kNoCandidate,
  // A hot call site, and the `min_hot_callsites` rule unmet.
  kTooHot,
  // Ruled out by `never_inline_eligibility`, which `ineligibility` names.
  kIneligible,
  kAnnotate,
};

struct NeverInlineVerdict {
  NeverInlineDecision decision;
  Ineligibility ineligibility{Ineligibility::kEligible};
  bool min_hot_callsites_rule_met{false};
};

// `ArtProfileWriterPass`'s `@NeverInline` decision on a callee with body
// `code`, already annotated or not, with or without a call site that is not
// hot, and with `hot_callsites` hot ones, as `HotCallsites` classifies them.
// The pass attaches the annotation on `kAnnotate` when it attaches any.
NeverInlineVerdict decide_never_inline(IRCode& code,
                                       bool already_never_inline,
                                       bool has_cold_callsite,
                                       size_t hot_callsites,
                                       const NeverInlineCriteria& criteria);

// The same decision on a callee whose body has `shape`, which lets a pass ask
// about a body it has yet to build.
NeverInlineVerdict decide_never_inline(const CalleeShape& shape,
                                       bool already_never_inline,
                                       bool has_cold_callsite,
                                       size_t hot_callsites,
                                       const NeverInlineCriteria& criteria);

} // namespace never_inline_analysis
