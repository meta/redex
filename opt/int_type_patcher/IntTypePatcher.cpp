/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "IntTypePatcher.h"
#include "Debug.h"
#include "DexUtil.h"
#include "IROpcode.h"
#include "MethodUtil.h"
#include "PassManager.h"
#include "Show.h"
#include "Trace.h"
#include "TypeUtil.h"
#include "Walkers.h"

void IntTypePatcherPass::run_pass(DexStoresVector& stores,
                                  ConfigFiles& /* unused */,
                                  PassManager& mgr) {
  auto scope = build_class_scope(stores);
  walk::parallel::methods(scope, [&](DexMethod* m) { run(m); });

  std::string printable_methods;
  for (DexMethod* m : UnorderedIterable(changed_methods)) {
    printable_methods += m->get_deobfuscated_name_or_empty_copy() + " ";
  }

  TRACE(ITP,
        1,
        "IntTypePatcher: number of added instructions: %zu",
        added_insns.load());
  TRACE(ITP,
        1,
        "IntTypePatcher: altered DexMethods: %s",
        printable_methods.c_str());

  mgr.set_metric("added_insns", added_insns.load());
  mgr.set_metric("mismatched_bool", mismatched_bool.load());
  mgr.set_metric("mismatched_byte", mismatched_byte.load());
  mgr.set_metric("mismatched_char", mismatched_char.load());
  mgr.set_metric("mismatched_short", mismatched_short.load());
}

void IntTypePatcherPass::run(DexMethod* m) {
  DexType* desired_type = m->get_proto()->get_rtype();
  if (!type::is_integral(desired_type)) {
    return;
  }

  IRCode* code = m->get_code();
  if (!method::is_optimizable(m)) {
    return;
  }
  always_assert(code->cfg_built());
  auto& cfg = code->cfg();
  type_inference::TypeInference inference(cfg);
  inference.run(m);

  type_inference::IntTypeDomain return_type;
  const std::vector<cfg::Block*> exits = cfg.real_exit_blocks();
  for (auto* block : exits) {
    if (block->get_last_insn() == block->end()) {
      continue;
    }
    IRInstruction* insn = block->get_last_insn()->insn;
    if (insn->opcode() != OPCODE_RETURN) {
      continue;
    }
    const auto& exit_env = inference.get_exit_state_at(block);
    if (exit_env.get_type(insn->src(0)) !=
        type_inference::TypeDomain(IRType::INT)) {
      continue;
    }
    return_type = exit_env.get_int_type(insn->src(0));
    if (type::is_boolean(desired_type) &&
        return_type_mismatch(type_inference::IntTypeDomain(IntType::BOOLEAN),
                             return_type)) {
      convert_to_boolean(cfg, block, insn);
      changed_methods.insert(m);
      added_insns += 5;
      mismatched_bool += 1;
    } else if (type::is_byte(desired_type) &&
               return_type_mismatch(
                   type_inference::IntTypeDomain(IntType::BYTE), return_type)) {
      convert_int_to(OPCODE_INT_TO_BYTE, cfg, block, insn);
      changed_methods.insert(m);
      mismatched_byte += 1;
    } else if (type::is_char(desired_type) &&
               return_type_mismatch(
                   type_inference::IntTypeDomain(IntType::CHAR), return_type)) {
      convert_int_to(OPCODE_INT_TO_CHAR, cfg, block, insn);
      changed_methods.insert(m);
      mismatched_char += 1;
    } else if (type::is_short(desired_type) &&
               return_type_mismatch(
                   type_inference::IntTypeDomain(IntType::SHORT),
                   return_type)) {
      convert_int_to(OPCODE_INT_TO_SHORT, cfg, block, insn);
      changed_methods.insert(m);
      mismatched_short += 1;
    }
  }
}

bool IntTypePatcherPass::return_type_mismatch(
    const type_inference::IntTypeDomain& int_type,
    const type_inference::IntTypeDomain& return_type) {
  return int_type.join(return_type) != int_type;
}

void IntTypePatcherPass::convert_int_to(IROpcode opcode,
                                        cfg::ControlFlowGraph& cfg,
                                        cfg::Block* exit_block,
                                        IRInstruction* insn) {
  IRInstruction* convert_insn = new IRInstruction(opcode);
  convert_insn->set_src(0, insn->src(0))->set_dest(insn->src(0));
  cfg.insert_before(cfg.find_insn(insn, exit_block), convert_insn);
  added_insns += 1;
}

void IntTypePatcherPass::convert_to_boolean(cfg::ControlFlowGraph& cfg,
                                            cfg::Block* exit_block,
                                            IRInstruction* insn) {
  IRInstruction* if_insn = new IRInstruction(OPCODE_IF_EQZ);
  reg_t reg = insn->src(0);
  if_insn->set_src(0, reg);

  cfg::Block* pred = cfg.split_block_before(cfg.find_insn(insn));
  if (cfg.entry_block() == exit_block) {
    cfg.set_entry_block(pred);
  }
  cfg.remove_block(exit_block);

  auto* true_block = cfg.create_block();
  auto* false_block = cfg.create_block();
  cfg.create_branch(pred, if_insn, false_block, true_block);

  false_block->push_back(
      (new IRInstruction(OPCODE_CONST))->set_literal(1)->set_dest(reg));
  false_block->push_back((new IRInstruction(OPCODE_RETURN))->set_src(0, reg));

  true_block->push_back(
      (new IRInstruction(OPCODE_CONST))->set_literal(0)->set_dest(reg));
  true_block->push_back((new IRInstruction(OPCODE_RETURN))->set_src(0, reg));
}

static IntTypePatcherPass s_pass;
