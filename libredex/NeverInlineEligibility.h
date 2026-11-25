/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <cstddef>
#include <cstdint>

class DexMethod;
class IRInstruction;

// The shape-only part of "is this method a sensible `@NeverInline` target":
// the checks that depend on the method's own body and not on any caller
// context. An existing `@NeverInline` annotation, and hot/cold call-site
// classification, remain each caller's own concern. Shared so that a pass
// deciding to annotate a method and a pass deciding to clone one for
// annotation cannot drift apart on what is eligible.
namespace never_inline_analysis {

// True for a single-block method whose body is a trivial forwarder: nothing
// but its own parameters, at most one constant/field-read/invoke, and a
// return. ART's own inliner absorbs a body this shape regardless of any
// `@NeverInline` annotation, so annotating it -- or cloning it away for that
// purpose -- would be dead weight.
//
// If the body's one interior instruction is an invoke and `invoke_insn` is
// non-null, `*invoke_insn` is set to it -- used by a caller chasing a
// forwarder chain to its real target (a devirtualizing callee resolver).
// `never_inline_eligibility` below does not need this output; it calls with
// the default `nullptr`.
bool is_simple(DexMethod* method, IRInstruction** invoke_insn = nullptr);

enum class Ineligibility {
  kEligible,
  kAlwaysThrows, // No return block: every path through the method throws.
  kTooLarge, // Estimated code units over the configured ceiling.
  kTooSmall, // Estimated instruction count under the configured floor.
  kSimple, // A trivial forwarder per `is_simple`.
};

// `ArtProfileWriterPass`'s defaults for the bounds below, which its doc
// strings explain.
inline constexpr uint32_t kDefaultMaxCalleeCodeUnits = 40;
inline constexpr size_t kDefaultMinCalleeInstructions = 4;

// `method`'s code must already have its CFG built (the Redex pass-entry
// invariant). Recomputes `estimate_code_units()`/`count_opcodes()` internally
// rather than taking precomputed values, since this is only ever called for
// a small, already-filtered candidate set in either caller.
Ineligibility never_inline_eligibility(DexMethod* method,
                                       uint32_t max_callee_code_units,
                                       size_t min_callee_instructions);

} // namespace never_inline_analysis
