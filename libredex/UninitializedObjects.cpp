/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "UninitializedObjects.h"

#include <vector>

#include <sparta/DirectProductAbstractDomain.h>

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

// The allocation an uninitialized object came from: its `new-instance`, or
// the `load-param-object` of a constructor's receiver. Several registers can
// hold one allocation, as after `move-object v2, v1`, and its `<init>`
// initializes it in all of them, as in ART's verifier. Only registers that hold
// a known allocation are bound; a register held different allocations on two
// incoming paths, or none, is unbound (Top).
using AllocationDomain = sparta::ConstantAbstractDomain<const IRInstruction*>;
using AllocationEnvironment =
    sparta::PatriciaTreeMapAbstractEnvironment<reg_t, AllocationDomain>;

class State final
    : public sparta::DirectProductAbstractDomain<State,
                                                 UninitializedObjectEnvironment,
                                                 AllocationEnvironment> {
 public:
  using DirectProductAbstractDomain::DirectProductAbstractDomain;

  const UninitializedObjectEnvironment& uninitialized() const {
    return get<0>();
  }

  const AllocationEnvironment& allocations() const { return get<1>(); }

  // Binds `reg` to what `src` holds.
  void copy(reg_t reg, reg_t src) {
    auto uninitialized = get<0>().get(src);
    auto allocation = get<1>().get(src);
    set(reg, uninitialized, allocation);
  }

  void set(reg_t reg,
           const UninitializedObjectDomain& uninitialized,
           const AllocationDomain& allocation) {
    apply<0>([&](auto* env) { env->set(reg, uninitialized); });
    apply<1>([&](auto* env) { env->set(reg, allocation); });
  }

  // The registers bound to `allocation`.
  std::vector<reg_t> holders(const IRInstruction* allocation) const {
    std::vector<reg_t> regs;
    get<1>().visit([&](const auto& binding) {
      if (binding.second.get_constant() == allocation) {
        regs.push_back(binding.first);
      }
    });
    return regs;
  }
};

// A throwing instruction has no effect on the paths where it throws: a handler
// sees the registers as they were before it. So every effect is applied on the
// paths where the instruction does not throw (`analyze_no_throw`); a `<init>`
// that throws leaves its object uninitialized in the handler, as ART's verifier
// does.
class Analyzer final : public BaseEdgeAwareIRAnalyzer<State> {
 public:
  explicit Analyzer(DexMethod* method)
      : BaseEdgeAwareIRAnalyzer(method->get_code()->cfg()),
        m_init_first_load_param(
            method::is_init(method)
                ? get_first_load_param(method->get_code()->cfg())
                : nullptr) {}

 protected:
  void analyze_instruction_normal(const IRInstruction* /* insn */,
                                  State* /* current_state */) const override {}

  void analyze_no_throw(const IRInstruction* insn,
                        State* current_state) const override {
    const UninitializedObjectDomain initialized(false);
    if (opcode::is_a_move(insn->opcode())) {
      current_state->copy(insn->dest(), insn->src(0));
    } else if (opcode::is_move_result_any(insn->opcode())) {
      current_state->copy(insn->dest(), RESULT_REGISTER);
    } else if (insn == m_init_first_load_param) {
      current_state->set(insn->dest(), UninitializedObjectDomain(true),
                         AllocationDomain(insn));
    } else if (insn->has_dest()) {
      current_state->set(insn->dest(), initialized, AllocationDomain::top());
    } else if (opcode::is_new_instance(insn->opcode())) {
      // No register is bound to an object from an earlier run of this
      // `new-instance`, as in a loop: a register stays bound after a merge
      // only if every incoming path binds it (otherwise it is Top), and the
      // first path to reach this instruction had not run it yet.
      redex_assert(current_state->holders(insn).empty());
      current_state->set(RESULT_REGISTER, UninitializedObjectDomain(true),
                         AllocationDomain(insn));
    } else if (opcode::is_invoke_direct(insn->opcode()) &&
               method::is_init(insn->get_method())) {
      auto allocation =
          current_state->allocations().get(insn->src(0)).get_constant();
      if (allocation) {
        for (auto reg : current_state->holders(*allocation)) {
          current_state->set(reg, initialized, AllocationDomain::top());
        }
      }
      current_state->set(insn->src(0), initialized, AllocationDomain::top());
    } else if (insn->has_move_result_any()) {
      current_state->set(RESULT_REGISTER, initialized, AllocationDomain::top());
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
    auto state = fp_iter.get_entry_state_at(block);
    for (const auto& mie : InstructionIterable(block)) {
      res.emplace(mie.insn, state.uninitialized());
      fp_iter.analyze_instruction(mie.insn, &state, /* is_last */ false);
    }
  }
  return res;
}

} // namespace uninitialized_objects
