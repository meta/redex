/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "InitClassPruner.h"

#include "CFGMutation.h"
#include "InitClassBackwardAnalysis.h"
#include "InitClassForwardAnalysis.h"
#include "Show.h"

namespace init_classes {

Stats& Stats::operator+=(const Stats& that) {
  init_class_instructions += that.init_class_instructions;
  init_class_instructions_removed += that.init_class_instructions_removed;
  init_class_instructions_refined += that.init_class_instructions_refined;
  return *this;
}

InitClassPruner::InitClassPruner(
    const InitClassesWithSideEffects& init_classes_with_side_effects,
    const DexType* declaring_type,
    cfg::ControlFlowGraph& cfg)
    : m_init_classes_with_side_effects(init_classes_with_side_effects),
      m_declaring_type(declaring_type),
      m_cfg(cfg) {}

void InitClassPruner::apply() {
  apply_forward();
  if (m_stats.init_class_instructions >
      m_stats.init_class_instructions_removed) {
    apply_backward();
  }
}

void InitClassPruner::apply_forward() {
  InitClassForwardFixpointIterator fp_iter(m_init_classes_with_side_effects,
                                           m_cfg);
  auto initial_env = fp_iter.initial_env(m_declaring_type);
  fp_iter.run(initial_env);
  cfg::CFGMutation mutation(m_cfg);
  for (cfg::Block* block : m_cfg.blocks()) {
    auto env = fp_iter.get_entry_state_at(block);
    auto ii = InstructionIterable(block);
    for (auto it = ii.begin(); it != ii.end();
         fp_iter.analyze_instruction(it->insn, &env,
                                     it->insn == ii.end()->insn),
              it++) {
      auto* insn = it->insn;
      if (!opcode::is_init_class(insn->opcode())) {
        continue;
      }
      m_stats.init_class_instructions++;
      const auto* refined_type =
          m_init_classes_with_side_effects.refine(insn->get_type());
      if (refined_type == nullptr ||
          env.unwrap().contains(type_class(refined_type))) {
        mutation.remove(block->to_cfg_instruction_iterator(it));
        m_stats.init_class_instructions_removed++;
      } else if (refined_type != insn->get_type()) {
        insn->set_type(const_cast<DexType*>(refined_type));
        m_stats.init_class_instructions_refined++;
      }
    }
  }
  mutation.flush();
}

void InitClassPruner::apply_backward() {
  m_cfg.calculate_exit_block();
  InitClassBackwardFixpointIterator fp_iter(m_init_classes_with_side_effects,
                                            m_cfg);
  fp_iter.run({});
  cfg::CFGMutation mutation(m_cfg);
  for (cfg::Block* block : m_cfg.blocks()) {
    auto env = fp_iter.get_entry_state_at(block);
    for (auto& mie : InstructionIterable(block).reversed()) {
      auto* insn = mie.insn;
      if (opcode::is_init_class(insn->opcode())) {
        const auto& c = env.get_constant();
        if (c && insn->get_type() == *c) {
          mutation.remove(block->to_cfg_instruction_iterator(mie));
          m_stats.init_class_instructions_removed++;
        }
      }
      fp_iter.analyze_instruction(mie.insn, &env);
    }
  }
  mutation.flush();
  m_cfg.reset_exit_block();
}

} // namespace init_classes
