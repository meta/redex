/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <utility>

#include <sparta/ConstantAbstractDomain.h>
#include <sparta/MonotonicFixpointIterator.h>

#include "BaseIRAnalyzer.h"
#include "DexUtil.h"
#include "InitClassesWithSideEffects.h"

namespace init_classes {

using LastInitClassDomain = sparta::ConstantAbstractDomain<const DexType*>;

class InitClassBackwardFixpointIterator final
    : public ir_analyzer::BaseBackwardsIRAnalyzer<LastInitClassDomain> {
 private:
  const InitClassesWithSideEffects& m_init_classes_with_side_effects;

 public:
  explicit InitClassBackwardFixpointIterator(
      const InitClassesWithSideEffects& init_classes_with_side_effects,
      const cfg::ControlFlowGraph& cfg)
      : ir_analyzer::BaseBackwardsIRAnalyzer<LastInitClassDomain>(cfg),
        m_init_classes_with_side_effects(init_classes_with_side_effects) {}

  void analyze_instruction(IRInstruction* insn,
                           LastInitClassDomain* current_state) const override {
    const auto* init_class = m_init_classes_with_side_effects.refine(
        get_init_class_type_demand(insn));
    // When an instruction...
    // 1) has an init-class type demand, or
    // 2) is an invoke that can run arbitrary code that can trigger other static
    //    initializers,
    // then we need to overwrite the current state with the
    // current init class type demand.
    if ((init_class != nullptr) || opcode::is_an_invoke(insn->opcode())) {
      *current_state = init_class != nullptr ? LastInitClassDomain(init_class)
                                             : LastInitClassDomain::top();
    }
  }

  LastInitClassDomain analyze_edge(
      const EdgeId& edge,
      const LastInitClassDomain& exit_state_at_source) const override {
    auto env = exit_state_at_source;
    if (edge->type() != cfg::EDGE_THROW) {
      return env;
    }

    auto last_insn_it = edge->src()->get_last_insn();
    always_assert(last_insn_it != edge->src()->end());

    auto* insn = last_insn_it->insn;
    if (opcode::is_init_class(insn->opcode())) {
      // We have a throw-edge from an init-class instruction. We'll pretend that
      // this didn't happen, as when joining with normal control-flow it would
      // destroy the knowledge about the actually following init-class domain.
      return LastInitClassDomain::bottom();
    }

    return env;
  }
};

} // namespace init_classes
