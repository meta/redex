/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "NeverInlineEligibility.h"

#include "ControlFlow.h"
#include "Debug.h"
#include "DexClass.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "IROpcode.h"

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

Ineligibility never_inline_eligibility(IRCode& code,
                                       uint32_t max_callee_code_units,
                                       size_t min_callee_instructions) {
  always_assert(code.cfg_built());
  if (code.cfg().return_blocks().empty()) {
    return Ineligibility::kAlwaysThrows;
  }
  if (code.estimate_code_units() > max_callee_code_units) {
    return Ineligibility::kTooLarge;
  }
  if (code.count_opcodes() < min_callee_instructions) {
    return Ineligibility::kTooSmall;
  }
  if (is_simple(code)) {
    return Ineligibility::kSimple;
  }
  return Ineligibility::kEligible;
}

} // namespace never_inline_analysis
