/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "UninitializedObjects.h"

#include "BaseIRAnalyzer.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "MethodUtil.h"

namespace {

using namespace uninitialized_objects;
using namespace ir_analyzer;

const IRInstruction* get_first_load_param(const cfg::ControlFlowGraph& cfg) {
  const auto param_insns = InstructionIterable(cfg.get_param_instructions());
  const auto& mie = *param_insns.begin();
  auto* const insn = mie.insn;
  always_assert(insn->opcode() == IOPCODE_LOAD_PARAM_OBJECT);
  return insn;
}

// A throwing instruction has no effect on the paths where it throws: a handler
// sees the registers as they were before it. So every effect is applied on the
// paths where the instruction does not throw (`analyze_no_throw`); a `<init>`
// that throws leaves its object uninitialized in the handler, as ART's verifier
// does.
class Analyzer final
    : public BaseEdgeAwareIRAnalyzer<UninitializedObjectEnvironment> {
 public:
  explicit Analyzer(DexMethod* method)
      : BaseEdgeAwareIRAnalyzer(method->get_code()->cfg()),
        m_init_first_load_param(
            method::is_init(method)
                ? get_first_load_param(method->get_code()->cfg())
                : nullptr) {}

 protected:
  void analyze_instruction_normal(
      const IRInstruction* /* insn */,
      UninitializedObjectEnvironment* /* current_state */) const override {}

  void analyze_no_throw(
      const IRInstruction* insn,
      UninitializedObjectEnvironment* current_state) const override {
    if (opcode::is_a_move(insn->opcode())) {
      current_state->set(insn->dest(), current_state->get(insn->src(0)));
    } else if (opcode::is_move_result_any(insn->opcode())) {
      current_state->set(insn->dest(), current_state->get(RESULT_REGISTER));
    } else if (insn == m_init_first_load_param) {
      current_state->set(insn->dest(), UninitializedObjectDomain(true));
    } else if (insn->has_dest()) {
      current_state->set(insn->dest(), UninitializedObjectDomain(false));
    } else if (opcode::is_new_instance(insn->opcode())) {
      current_state->set(RESULT_REGISTER, UninitializedObjectDomain(true));
    } else if (opcode::is_invoke_direct(insn->opcode()) &&
               method::is_init(insn->get_method())) {
      current_state->set(insn->src(0), UninitializedObjectDomain(false));
    } else if (insn->has_move_result_any()) {
      current_state->set(RESULT_REGISTER, UninitializedObjectDomain(false));
    }
  }

 private:
  const IRInstruction* m_init_first_load_param;
};
} // namespace

namespace uninitialized_objects {

UninitializedObjectEnvironments get_uninitialized_object_environments(
    DexMethod* method) {
  Analyzer fp_iter(method);
  fp_iter.run({});
  UninitializedObjectEnvironments res;
  for (cfg::Block* block : method->get_code()->cfg().blocks()) {
    auto env = fp_iter.get_entry_state_at(block);
    for (const auto& mie : InstructionIterable(block)) {
      res.emplace(mie.insn, env);
      fp_iter.analyze_instruction(mie.insn, &env, /* is_last */ false);
    }
  }
  return res;
}

} // namespace uninitialized_objects
