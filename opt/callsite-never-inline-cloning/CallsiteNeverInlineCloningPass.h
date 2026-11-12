/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <cstdint>
#include <string>
#include <vector>

#include "BaselineProfile.h"
#include "DexClass.h"
#include "MethodProfiles.h"
#include "NeverInlineEligibility.h"
#include "Pass.h"

class CallsiteNeverInlineCloningPass : public Pass {
 public:
  struct Stats {
    // Whole callers skipped (every call site inside is ignored).
    size_t callers_no_optimizations{0};
    size_t callers_not_compiled{0};
    size_t callers_too_many_instructions{0};
    // Individual call sites skipped.
    size_t invokes_super_opcode{0};
    size_t invokes_interface_opcode{0};
    size_t invokes_unresolved{0};
    size_t invokes_external_or_no_code_callee{0};
    size_t invokes_ambiguous_virtual_callee{0};
    size_t invokes_init_callee{0};
    size_t invokes_no_optimizations_callee{0};
    // Body-copying transforms must honor `no_outlining`: ReachableNativesPass
    // uses it to pin load-library entry points whose copies would invalidate
    // its final constant-name analysis.
    size_t invokes_no_outlining_callee{0};
    size_t invokes_non_renamable_callee_class{0};
    size_t invokes_already_never_inline_callee{0};
    size_t invokes_blocklisted_callee{0};
    size_t invokes_callsite_and_callee_both_have_catch{0};
    // Mirrors ArtProfileWriterPass's own reverse throw-adjacent skip: an
    // invoke immediately preceding an explicit `throw` at the end of its
    // block, up to and including the first non-`<init>` one, is typically
    // just constructing the thrown exception, not a normal call site.
    size_t invokes_throw_adjacent{0};
    // Candidate callees (>=1 cold call site, >=1 not-proven-cold call site)
    // rejected on ArtProfileWriterPass-parity shape grounds, before the
    // profitability model runs at all.
    size_t callees_all_cold_no_clone_needed{0};
    size_t callees_always_throw{0};
    size_t callees_too_large{0};
    size_t callees_too_small{0};
    size_t callees_simple{0};
    // The eligible population: callees that passed every shape/eligibility
    // gate above.
    size_t mixed_hotness_callees{0};
    // Profitability-model rejections, applied to the population above, in
    // the order they are checked (see `clone_mixed_hotness_callees`).
    size_t rejected_insufficient_hot_callsites{0};
    size_t rejected_insufficient_cold_callsites{0};
    size_t rejected_insufficient_estimated_savings{0};
    size_t rejected_non_positive_net{0};
    size_t rejected_cap_max_total_clones{0};
    size_t rejected_cap_max_total_cloned_code_units{0};
    // Outcomes: actual mutation counts (both stay 0 under `estimate_only`).
    size_t clones_created{0};
    size_t cold_callsites_redirected{0};
    // What the profitability model decided -- populated identically whether
    // or not `estimate_only` suppressed the actual mutation: the number of
    // candidates that survived every threshold and every cap, in
    // deterministic net-descending order.
    size_t selected_candidates{0};
    uint64_t total_cloned_code_units{0};
    int64_t total_estimated_oat_code_units_saved{0};
    // Sum, over every selected candidate, of its own estimated incremental
    // method-ref count (see `method_ref_cost`'s doc string) -- not a count of
    // clones.
    size_t total_estimated_method_refs{0};
    int64_t total_estimated_dex_cost{0};
    int64_t total_estimated_net{0};
    Stats& operator+=(const Stats& other) {
      callers_no_optimizations += other.callers_no_optimizations;
      callers_not_compiled += other.callers_not_compiled;
      callers_too_many_instructions += other.callers_too_many_instructions;
      invokes_super_opcode += other.invokes_super_opcode;
      invokes_interface_opcode += other.invokes_interface_opcode;
      invokes_unresolved += other.invokes_unresolved;
      invokes_external_or_no_code_callee +=
          other.invokes_external_or_no_code_callee;
      invokes_ambiguous_virtual_callee +=
          other.invokes_ambiguous_virtual_callee;
      invokes_init_callee += other.invokes_init_callee;
      invokes_no_optimizations_callee += other.invokes_no_optimizations_callee;
      invokes_no_outlining_callee += other.invokes_no_outlining_callee;
      invokes_non_renamable_callee_class +=
          other.invokes_non_renamable_callee_class;
      invokes_already_never_inline_callee +=
          other.invokes_already_never_inline_callee;
      invokes_blocklisted_callee += other.invokes_blocklisted_callee;
      invokes_callsite_and_callee_both_have_catch +=
          other.invokes_callsite_and_callee_both_have_catch;
      invokes_throw_adjacent += other.invokes_throw_adjacent;
      callees_all_cold_no_clone_needed +=
          other.callees_all_cold_no_clone_needed;
      callees_always_throw += other.callees_always_throw;
      callees_too_large += other.callees_too_large;
      callees_too_small += other.callees_too_small;
      callees_simple += other.callees_simple;
      mixed_hotness_callees += other.mixed_hotness_callees;
      rejected_insufficient_hot_callsites +=
          other.rejected_insufficient_hot_callsites;
      rejected_insufficient_cold_callsites +=
          other.rejected_insufficient_cold_callsites;
      rejected_insufficient_estimated_savings +=
          other.rejected_insufficient_estimated_savings;
      rejected_non_positive_net += other.rejected_non_positive_net;
      rejected_cap_max_total_clones += other.rejected_cap_max_total_clones;
      rejected_cap_max_total_cloned_code_units +=
          other.rejected_cap_max_total_cloned_code_units;
      clones_created += other.clones_created;
      cold_callsites_redirected += other.cold_callsites_redirected;
      selected_candidates += other.selected_candidates;
      total_cloned_code_units += other.total_cloned_code_units;
      total_estimated_oat_code_units_saved +=
          other.total_estimated_oat_code_units_saved;
      total_estimated_method_refs += other.total_estimated_method_refs;
      total_estimated_dex_cost += other.total_estimated_dex_cost;
      total_estimated_net += other.total_estimated_net;
      return *this;
    }
  };

  struct Config {
    // Shares the callee shape and instruction thresholds with
    // ArtProfileWriterPass. The writer checks allocated caller registers;
    // this pass runs before allocation and cannot apply that bound yet.
    //
    // `hot_block_appear_threshold`/`hot_method_appear_threshold` default to
    // -1 (disabled), matching ArtProfileWriterPass's own global default: with
    // no explicit override, this pass classifies a call site as hot whenever
    // its callee is baseline-profile-compiled at all, so it finds no
    // "mixed-hotness" callee to clone and is a safe no-op. An app enabling
    // this pass is expected to set these to the same values it already gives
    // ArtProfileWriterPass (as instagram.refig.inc/fb4a.refig.inc do, 80/20),
    // so both passes agree on what "hot" means at a given call site.
    float hot_block_appear_threshold{-1.0f};
    float hot_method_appear_threshold{-1.0f};
    size_t max_caller_instructions{
        never_inline_analysis::kDefaultMaxCallerInstructions};
    uint32_t max_callee_code_units{40};
    size_t min_callee_instructions{4};

    // Profitability / volume model. A mixed-hotness callee (one that already
    // passed every shape-eligibility gate above) is only actually cloned if
    // it clears ALL of the following, in the order checked:
    //   - at least `min_hot_callsites` call sites this pass could not prove
    //     cold (the population that benefits from leaving the original
    //     inlinable);
    //   - at least `min_cold_callsites` call sites this pass proved cold
    //     (the population that benefits from the clone's `@NeverInline`);
    //   - `estimated_oat_code_units_saved = cold_callsite_count *
    //     callee_code_units` (the OAT/code-size win of never-inlining every
    //     cold call site, once a later ArtProfileWriterPass annotates the
    //     clone) is at least `min_estimated_oat_code_units_saved`;
    //   - `estimated_net = estimated_oat_code_units_saved -
    //     (callee_code_units + method_ref_cost *
    //     estimated_incremental_mrefs)` is strictly positive, where
    //     `estimated_incremental_mrefs = 1 (the clone's own definition) +
    //     the number of distinct classes the cold call sites being
    //     redirected live in`: this pass runs pre-InterDex, so which dex
    //     each caller and the clone eventually land in is not yet known;
    //     one incremental method ref per distinct calling class is a
    //     conservative upper-bound proxy for how many dexes may end up
    //     needing their own ref to the clone (a caller class split across
    //     dexes from the callee could need more than one, but never fewer
    //     than one per distinct class).
    // Every number above is an ESTIMATE computed ahead of InterDex, dex
    // splitting, and any later shrinking pass -- a signal for ranking
    // potential copies, not a promised or measured byte count. Callers may
    // remain over ART's register budget after allocation, leaving a clone
    // without a NeverInline annotation.
    // Surviving candidates are then ranked by `estimated_net` descending
    // (ties broken by a stable, deterministic method ordering) and accepted
    // in that order until `max_total_clones` or `max_total_cloned_code_units`
    // would be exceeded -- a lower-ranked candidate that would fit under the
    // caps is still accepted even if a higher-ranked one did not fit.
    size_t min_hot_callsites{1};
    size_t min_cold_callsites{2};
    int64_t min_estimated_oat_code_units_saved{1};
    size_t max_total_clones{10000};
    uint64_t max_total_cloned_code_units{1000000};
    uint32_t method_ref_cost{16};

    // Dry-run mode: run the full analysis, including the profitability
    // model, ranking, and cap application, and populate every `Stats` field
    // exactly as a real run would -- but never call `DexMethod::make_method`,
    // never rewrite a call site. `clones_created`/`cold_callsites_redirected`
    // read 0; `selected_candidates` (and the `total_*` fields) report what a
    // real run would have done.
    bool estimate_only{false};

    // Skip candidate callees whose declaring class's deobfuscated name (or,
    // before any renaming pass has run and none has been set, its own raw
    // class name) starts with any of these prefixes.
    std::vector<std::string> blocklist;
  };

  CallsiteNeverInlineCloningPass() : Pass("CallsiteNeverInlineCloningPass") {}

  redex_properties::PropertyInteractions get_property_interactions()
      const override {
    using namespace redex_properties::interactions;
    using namespace redex_properties::names;
    return {
        {HasSourceBlocks, RequiresAndEstablishes},
        {NoResolvablePureRefs, Preserves},
        {SpuriousGetClassCallsInterned, Preserves},
        {InitialRenameClass, Preserves},
        {UltralightCodePatterns, Preserves},
    };
  }

  std::string get_config_doc() override {
    return trim(R"(
A method that is called from both a profiled-hot call site and a
profiled-cold call site cannot be marked `@NeverInline` by
`ArtProfileWriterPass`: doing so would also block ART's AOT inliner at the hot
call site, where inlining is wanted. This pass resolves that conflict ahead of
`InitialRenameClassesPass` and `InterDexPass`, so a later `ArtProfileWriterPass`
sees the result: for such a "mixed-hotness" callee, it clones the method (a
plain, same-class, full copy, via `DexMethod::make_method_from`, so debug info
and the built CFG carry over unchanged) and rewrites only the call sites in a
profiled-cold block to invoke the clone; call sites in a not-proven-cold block
keep calling the original, unchanged -- and so does the call instruction's own
opcode, since the clone keeps the original's exact access flags (virtual or
not, visibility, `final`-ness). The clone is marked `dont_inline` (Redex's own
inliner will not touch it), force-H in every materialized baseline profile so
whichever profile is used asks dex2oat to compile the one shared body, and has
its own primary `SourceBlock` values zeroed. This is a single whole-program
structural decision, analogous to profile-guided inlining or outlining: once the
pass creates the clone, every materialized profile describes that transformed
program instead of independently deciding whether the clone exists.
`ArtProfileWriterPass` evaluates `@NeverInline` against the pre-overlay profile,
so forced H does not masquerade as observed hot execution. The original, now
free of any observed-cold caller, is left for normal treatment. The profile
policy uses the explicit `ReferencedState` hot bit, not the generated `$cnic$`
name.

Only an exact call site is ever redirected: `invoke-static`, `invoke-direct`,
or an `invoke-virtual` resolving to a non-true-virtual method (per Redex's
method-override graph: one that neither overrides nor is overridden by any
other method in the current scope, so its dispatch is exact even though it is
not declared `final`). `invoke-super` and `invoke-interface` call sites are
always left alone; no receiver-type inference is attempted for an otherwise
true-virtual `invoke-virtual`.

The pass also honors Redex's shared transformation constraints. A callee marked
`no_optimizations` or `no_outlining` is never cloned; the latter is the
body-copying gate also used by HotColdMethodSpecializingPass and the outlining
passes. The target class must be renamable, following PartialApplicationPass's
same-class-helper rule: adding a generated method to a kept class can change the
declared-method set visible through reflection. A plain `dont_inline` marker is
not a cloning prohibition -- it only constrains Redex's own inliner. The
configured class-prefix `blocklist` remains available for app-specific cases
that are not represented by these shared semantic flags.

The hot/cold classification of a call site, and the shape-eligibility of a
callee to be cloned away from (does it have a return block, is it within the
configured code-unit/instruction bounds -- `max_callee_code_units` (default
40) sized to the callees ART could plausibly inline anyway, bounding the
clone's own DEX cost, and `min_callee_instructions` (default 4) filtering out
a body too small for cloning to matter -- is it not a trivial forwarder, which
`ArtProfileWriterPass` would otherwise still see straight through to the
original body it wraps), mirror `ArtProfileWriterPass`'s own `never_inline`
analysis for exactly the call sites this pass itself ever resolves (the
`invoke-static`/`invoke-direct`/non-true-virtual set above) -- not that
analysis's full breadth, which also chases a receiver-type map to sometimes
resolve an otherwise-ambiguous `invoke-virtual`, and follows a forwarder
chain to its ultimate callee; this pass deliberately does neither. Within
that narrower set: only call sites inside a
profiled-compiled caller are inspected at all; a caller over
`max_caller_instructions` is skipped entirely. Registers here are virtual;
`ArtProfileWriterPass` checks the allocated caller frame later. A call
site whose containing block can throw into a callee that itself has a catch
handler is skipped; an invoke immediately preceding an explicit `throw` at the
end of its block, up to and including the first non-`<init>` one, is treated
as exception-construction noise, not a call site, and is skipped the same way
`ArtProfileWriterPass` skips it. The callee shape-eligibility check itself
(`never_inline_analysis::never_inline_eligibility`, in `libredex/`) is the
exact same function `ArtProfileWriterPass` calls for its own annotation
decision. Passing these body-shape requirements does not guarantee an
annotation: the writer still checks the allocated caller frames. Its
virtual-callee eligibility check is
narrower than this pass's own (`is_final(method) || is_final(class)`, not the
broader non-true-virtual notion above), so a clone of a non-final,
non-true-virtual callee is additionally marked `final`, matching
`PartialApplicationPass`, purely so that later pass is willing to annotate it
too. Clone names follow the same generated-name convention: a reserved `$cnic$`
tag, pass iteration, stable hash of the full callee identity, and deterministic
hash-collision index keep independently generated helpers distinct. This never
changes the clone's virtual-ness, visibility, or which existing callers can
reach it.

A shape-eligible mixed-hotness callee is cloned only if it also clears the
profitability model's thresholds (`min_hot_callsites`, `min_cold_callsites`,
`min_estimated_oat_code_units_saved`, a positive estimated net after a
`method_ref_cost` charge scaled by the number of distinct classes the
redirected cold call sites live in) -- see the `Config` fields' own doc
strings for the exact formula -- and fits within the deterministic, net-ranked
`max_total_clones`/`max_total_cloned_code_units` caps. The model ranks
potential inline copies before allocation; callers may remain over the
register budget, leaving a clone without an annotation. Its numbers are not
promised or measured byte counts.

This pass produces no clone and rewrites no call site for a callee with only
cold call sites (nothing to split away from), or for any program with no
baseline-profile/`SourceBlock` profiling data at all -- so on a build with no
such instrumentation, this pass is a no-op. With its own bare defaults
(`hot_block_appear_threshold`/`hot_method_appear_threshold` both -1, matching
`ArtProfileWriterPass`'s own global default), it is a no-op for any app that
has not explicitly configured those two thresholds, since it then cannot
distinguish a hot call site from a cold one. Like every Redex pass, it can
also be turned off entirely for an app via `<PassName>.disabled(True)` in that
app's config; it is unconditionally disabled by default in `module_core.refig`.
    )");
  }

  void bind_config() override;
  void run_pass(DexStoresVector& stores,
                ConfigFiles& conf,
                PassManager& mgr) override;

  // Exposed for unit testing: applies the whole pass to a given scope with an
  // explicit baseline profile and method profiles, independent of
  // PassManager/ConfigFiles plumbing. Every method in `scope` with code must
  // already have its CFG built (`IRCode::build_cfg`) -- the same invariant
  // `PassManager` establishes before every real pass run -- since this is
  // asserted, not defensively checked.
  static Stats clone_mixed_hotness_callees(
      const Scope& scope,
      const Config& config,
      size_t iteration,
      const baseline_profiles::BaselineProfile& baseline_profile,
      uint32_t huge_method_max,
      const method_profiles::MethodProfiles& method_profiles);

 private:
  Config m_config;
  size_t m_iteration{0};
};
