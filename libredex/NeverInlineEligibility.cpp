/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "NeverInlineEligibility.h"

#include "ControlFlow.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexClass.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "IROpcode.h"
#include "MethodOverrideGraph.h"
#include "MethodUtil.h"
#include "Resolver.h"
#include "Walkers.h"

namespace never_inline_analysis {

bool is_simple(DexMethod* method, IRInstruction** invoke_insn) {
  return is_simple(*method->get_code(), invoke_insn);
}

bool is_simple(IRCode& code, IRInstruction** invoke_insn) {
  always_assert(code.cfg_built());
  auto& cfg = code.cfg();
  if (cfg.blocks().size() != 1) {
    return false;
  }
  auto* b = cfg.entry_block();
  auto last_it = b->get_last_insn();
  if (last_it == b->end() || !opcode::is_a_return(last_it->insn->opcode())) {
    return false;
  }
  auto ii = InstructionIterable(b);
  auto it = ii.begin();
  always_assert(it != ii.end());
  while (opcode::is_a_load_param(it->insn->opcode())) {
    ++it;
    always_assert(it != ii.end());
  }
  if (opcode::is_a_const(it->insn->opcode())) {
    ++it;
    always_assert(it != ii.end());
  } else if (opcode::is_an_iget(it->insn->opcode()) ||
             opcode::is_an_sget(it->insn->opcode())) {
    ++it;
    always_assert(it != ii.end());
  } else if (opcode::is_an_invoke(it->insn->opcode())) {
    if (invoke_insn != nullptr) {
      *invoke_insn = it->insn;
    }
    ++it;
    always_assert(it != ii.end());
  }
  if (opcode::is_move_result_any(it->insn->opcode())) {
    ++it;
    always_assert(it != ii.end());
  }
  always_assert(it != ii.end());
  return it->insn == last_it->insn;
}

Ineligibility never_inline_eligibility(DexMethod* method,
                                       uint32_t max_callee_code_units,
                                       size_t min_callee_instructions) {
  return never_inline_eligibility(*method->get_code(), max_callee_code_units,
                                  min_callee_instructions);
}

namespace {

// The checks of `never_inline_eligibility`, in order, each reading only what
// it needs of the body: `returns`, `code_units`, `instructions` and `simple`
// give a `CalleeShape`'s fields.
template <typename Returns,
          typename CodeUnits,
          typename Instructions,
          typename Simple>
Ineligibility eligibility(uint32_t max_callee_code_units,
                          size_t min_callee_instructions,
                          const Returns& returns,
                          const CodeUnits& code_units,
                          const Instructions& instructions,
                          const Simple& simple) {
  if (!returns()) {
    return Ineligibility::kAlwaysThrows;
  }
  if (code_units() > max_callee_code_units) {
    return Ineligibility::kTooLarge;
  }
  if (instructions() < min_callee_instructions) {
    return Ineligibility::kTooSmall;
  }
  if (simple()) {
    return Ineligibility::kSimple;
  }
  return Ineligibility::kEligible;
}

} // namespace

Ineligibility never_inline_eligibility(IRCode& code,
                                       uint32_t max_callee_code_units,
                                       size_t min_callee_instructions) {
  always_assert(code.cfg_built());
  return eligibility(
      max_callee_code_units, min_callee_instructions,
      [&] { return !code.cfg().return_blocks().empty(); },
      [&] { return code.estimate_code_units(); },
      [&] { return code.count_opcodes(); }, [&] { return is_simple(code); });
}

Ineligibility never_inline_eligibility(const CalleeShape& shape,
                                       uint32_t max_callee_code_units,
                                       size_t min_callee_instructions) {
  return eligibility(
      max_callee_code_units, min_callee_instructions,
      [&] { return shape.returns; }, [&] { return shape.code_units; },
      [&] { return shape.instructions; }, [&] { return shape.simple; });
}

Shape never_inline_shape(DexMethod* method) {
  auto* code = method->get_code();
  always_assert(code->cfg_built());
  if (code->cfg().return_blocks().empty()) {
    return Shape::kAlwaysThrows;
  }
  if (is_simple(method)) {
    return Shape::kSimple;
  }
  return Shape::kEligible;
}

CallerBudget caller_inline_budget(size_t instructions,
                                  size_t registers,
                                  size_t max_instructions,
                                  size_t max_registers) {
  if (instructions > max_instructions) {
    return CallerBudget::kTooManyInstructions;
  }
  if (registers > max_registers) {
    return CallerBudget::kTooManyRegisters;
  }
  return CallerBudget::kWithin;
}

InsertOnlyConcurrentSet<DexMethod*> exact_virtuals(
    const method_override_graph::Graph& graph,
    const std::vector<DexClass*>& scope) {
  InsertOnlyConcurrentSet<DexMethod*> result;
  walk::parallel::classes(scope, [&](DexClass* cls) {
    for (auto* method : cls->get_vmethods()) {
      if (!method_override_graph::any_overriding_methods(graph, method)) {
        result.insert(method);
      }
    }
  });
  return result;
}

UnorderedSet<IRInstruction*> throw_constructing_invokes(cfg::Block* block) {
  UnorderedSet<IRInstruction*> result;
  bool has_throw = false;
  bool has_non_init_invoke = false;
  for (auto& mie : InstructionIterable(block).reversed()) {
    auto* insn = mie.insn;
    if (!opcode::is_an_invoke(insn->opcode())) {
      if (opcode::is_throw(insn->opcode())) {
        has_throw = true;
      }
      continue;
    }
    if (has_throw && !has_non_init_invoke) {
      if (!method::is_init(insn->get_method())) {
        has_non_init_invoke = true;
      }
      result.insert(insn);
    }
  }
  return result;
}

ExactCallSiteSkips for_each_exact_call_site(
    DexMethod* caller,
    cfg::ControlFlowGraph& cfg,
    const InsertOnlyConcurrentSet<DexMethod*>& exact_virtuals,
    const std::function<void(cfg::Block*, IRInstruction*, DexMethod*)>& visit) {
  ExactCallSiteSkips skips;
  for (auto* block : cfg.blocks()) {
    auto throw_adjacent_invokes = throw_constructing_invokes(block);

    for (auto& mie : InstructionIterable(block)) {
      auto* insn = mie.insn;
      auto op = insn->opcode();
      if (!opcode::is_an_invoke(op)) {
        continue;
      }
      if (throw_adjacent_invokes.count(insn) != 0u) {
        skips.throw_adjacent++;
        continue;
      }
      if (op == OPCODE_INVOKE_SUPER) {
        skips.super_invoke++;
        continue;
      }
      if (op == OPCODE_INVOKE_INTERFACE) {
        skips.interface_invoke++;
        continue;
      }
      if (op != OPCODE_INVOKE_STATIC && op != OPCODE_INVOKE_DIRECT &&
          op != OPCODE_INVOKE_VIRTUAL) {
        // Not reachable given is_an_invoke(), kept as a defensive default.
        continue;
      }
      auto* callee = resolve_invoke_method_deprecated(insn, caller);
      if (callee == nullptr) {
        skips.unresolved++;
        continue;
      }
      auto* callee_cls = type_class(callee->get_class());
      if (callee->get_code() == nullptr || callee_cls == nullptr ||
          callee_cls->is_external()) {
        skips.external_or_no_code++;
        continue;
      }
      // Exact dispatch only: an invoke-virtual is accepted only when the
      // resolved callee cannot be overridden at this call site. No
      // receiver-type inference is attempted for an otherwise true-virtual
      // target.
      if (callee->is_virtual() && exact_virtuals.count(callee) == 0) {
        skips.ambiguous_virtual++;
        continue;
      }
      visit(block, insn, callee);
    }
  }
  return skips;
}

} // namespace never_inline_analysis
