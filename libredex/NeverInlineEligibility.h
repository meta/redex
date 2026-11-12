/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <cstddef>
#include <cstdint>
#include <functional>
#include <vector>

#include "ConcurrentContainers.h"
#include "DeterministicContainers.h"

class DexClass;
class DexMethod;
class IRCode;
class IRInstruction;

namespace cfg {
class Block;
class ControlFlowGraph;
} // namespace cfg

namespace method_override_graph {
class Graph;
} // namespace method_override_graph

// Shared analysis for passes that reason about what ART inlines: the
// shape-only part of "is this method a sensible `@NeverInline` target" (the
// checks that depend on the method's own body and not on any caller context),
// and the walk over the call sites whose callee is known exactly. An existing
// `@NeverInline` annotation, and hot/cold call-site classification, remain
// each caller's own concern. Shared so that passes deciding to annotate,
// clone or split a method cannot drift apart on what is eligible.
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

// `is_simple` of a body, which need not belong to a method: one a pass builds
// to ask about a method it has yet to create.
bool is_simple(IRCode& code, IRInstruction** invoke_insn = nullptr);

enum class Ineligibility {
  kEligible,
  kAlwaysThrows, // No return block: every path through the method throws.
  kTooLarge, // Estimated code units over the configured ceiling.
  kTooSmall, // Estimated instruction count under the configured floor.
  kSimple, // A trivial forwarder per `is_simple`.
};

enum class Shape {
  kEligible,
  kAlwaysThrows, // No return block: every path through the method throws.
  kSimple, // A trivial forwarder per `is_simple`.
};

// The checks of `never_inline_eligibility` that take no threshold. `method`'s
// code must already have its CFG built.
Shape never_inline_shape(DexMethod* method);

// `ArtProfileWriterPass`'s defaults for the bounds below, which its doc
// strings explain.
inline constexpr uint32_t kDefaultMaxCalleeCodeUnits = 40;
inline constexpr size_t kDefaultMinCalleeInstructions = 4;

// What `never_inline_eligibility` reads of a method's body: whether a path
// returns, its estimated code units (`IRCode::estimate_code_units`) and
// instructions (`IRCode::count_opcodes`), and whether it is a trivial
// forwarder (`is_simple`). Lets a pass ask about a method it has yet to
// create.
struct CalleeShape {
  bool returns;
  uint32_t code_units;
  size_t instructions;
  bool simple;
};

Ineligibility never_inline_eligibility(const CalleeShape& shape,
                                       uint32_t max_callee_code_units,
                                       size_t min_callee_instructions);

// `method`'s code must already have its CFG built (the Redex pass-entry
// invariant). Recomputes `estimate_code_units()`/`count_opcodes()` internally
// rather than taking precomputed values, since this is only ever called for
// a small, already-filtered candidate set in either caller.
Ineligibility never_inline_eligibility(DexMethod* method,
                                       uint32_t max_callee_code_units,
                                       size_t min_callee_instructions);

// `never_inline_eligibility` of a body, which need not belong to a method.
Ineligibility never_inline_eligibility(IRCode& code,
                                       uint32_t max_callee_code_units,
                                       size_t min_callee_instructions);

// ART inlines into a caller only within these budgets. The instruction budget
// shadows ART's 1024-HIR caller budget, with a margin, but in a different
// unit: HIR instructions are not IR opcodes (measured 1.83-1.99 HIR per
// distinct dex pc, up to 3.60 on tiny methods), so it can land on either side
// of 1024 HIR depending on the method. The register budget shadows ART's
// 32-slot inlining environment budget, with no margin.
inline constexpr size_t kDefaultMaxCallerInstructions = 1100;
inline constexpr size_t kDefaultMaxCallerRegisters = 32;

enum class CallerBudget {
  kWithin,
  kTooManyInstructions, // More IR instructions (`IRCode::count_opcodes`).
  kTooManyRegisters,
};

// Instruction-only screening for passes that run before register allocation.
// This is not a prediction of the caller's final allocated register frame.
CallerBudget caller_inline_instruction_budget(size_t instructions,
                                              size_t max_instructions);

// Whether a caller with `instructions` IR instructions and `registers`
// registers is within the budgets ART inlines into.
CallerBudget caller_inline_budget(size_t instructions,
                                  size_t registers,
                                  size_t max_instructions,
                                  size_t max_registers);

// The virtual methods of `scope` that an invoke-virtual reaches exactly: those
// no method overrides. CallsiteNeverInlineCloningPass keeps the narrower set
// of non-true virtuals (methods that neither override nor are overridden):
// widening it would change which call sites it clones. ArtProfileWriterPass
// resolves invoke-virtuals through receiver types instead.
InsertOnlyConcurrentSet<DexMethod*> exact_virtuals(
    const method_override_graph::Graph& graph,
    const std::vector<DexClass*>& scope);

// The invokes that construct the exception `block` throws: an invoke
// immediately preceding an explicit `throw` at the end of the block, up to and
// including the first one that is not an `<init>` call, is typically just
// constructing the thrown exception rather than a normal call site.
UnorderedSet<IRInstruction*> throw_constructing_invokes(cfg::Block* block);

// Why `for_each_exact_call_site` passed over an invoke.
struct ExactCallSiteSkips {
  // Constructs the exception a block throws; see `throw_constructing_invokes`.
  size_t throw_adjacent{0};
  size_t super_invoke{0};
  size_t interface_invoke{0};
  // Does not resolve to a method.
  size_t unresolved{0};
  // The callee has no code or is in an external class.
  size_t external_or_no_code{0};
  // An invoke-virtual whose callee may be overridden.
  size_t ambiguous_virtual{0};
};

// Calls `visit(block, invoke, callee)` for every call site in `caller`'s CFG
// whose callee is known exactly: an invoke-static, an invoke-direct, or an
// invoke-virtual of a method in `exact_virtuals`, that resolves to a
// method with code in an internal class. The invoke may name the method
// through a subclass, e.g. `MyFragment.requireContext()` for
// `Fragment.requireContext()`. `exact_virtuals` holds the virtual methods the
// caller treats as reached exactly by an invoke-virtual, e.g. those no other
// method overrides.
//
// Skips the invokes that construct the exception a block throws; see
// `throw_constructing_invokes`.
ExactCallSiteSkips for_each_exact_call_site(
    DexMethod* caller,
    cfg::ControlFlowGraph& cfg,
    const InsertOnlyConcurrentSet<DexMethod*>& exact_virtuals,
    const std::function<void(cfg::Block*, IRInstruction*, DexMethod*)>& visit);

} // namespace never_inline_analysis
