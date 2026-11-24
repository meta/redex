/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "TypeAnalysisRuntimeAssert.h"

#include "ControlFlow.h"
#include "Debug.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "MethodUtil.h"
#include "ProguardMap.h"
#include "Resolver.h"
#include "TypeUtil.h"

namespace type_analyzer {

namespace {

template <typename DexMember>
const DexString* get_deobfuscated_name_dex_string(const DexMember* member) {
  return member->get_deobfuscated_name_or_null();
}

template <>
const DexString* get_deobfuscated_name_dex_string(const DexField* member) {
  const auto& str = member->get_deobfuscated_name();
  if (str.empty()) {
    return nullptr;
  }
  return DexString::make_string(str);
}
} // namespace

RuntimeAssertTransform::Config::Config(const ProguardMap& pg_map) {
  param_assert_fail_handler = DexMethod::get_method(pg_map.translate_method(
      "Lcom/facebook/redex/"
      "ConstantPropagationAssertHandler;.paramValueError:(I)V"));
  field_assert_fail_handler = DexMethod::get_method(
      pg_map.translate_method("Lcom/facebook/redex/"
                              "ConstantPropagationAssertHandler;."
                              "fieldValueError:(Ljava/lang/String;)V"));
  return_value_assert_fail_handler = DexMethod::get_method(
      pg_map.translate_method("Lcom/facebook/redex/"
                              "ConstantPropagationAssertHandler;."
                              "returnValueError:(Ljava/lang/String;)V"));
}

/* Given an iterator \p it, whose block is B, split block B into B1->B2. Then
 * insert a if-stmt at the end of Block B1, and create another block throw_block
 * with assertion call. After this change, the blocks look like: B1 (if_isns is
 * false) -> throw_block -> B2, B1 (if_insn is true)-> B2 */
template <typename DexMember>
static void insert_null_check_with_throw(cfg::ControlFlowGraph& cfg,
                                         cfg::InstructionIterator& it,
                                         reg_t reg_to_check,
                                         const DexMember* member,
                                         DexMethodRef* handler,
                                         bool branch_on_null = true) {
  // 1. Split it into B1->B2, and current 'it' is the last insn of B1.
  cfg::Block* B1 = it.block();
  cfg::Block* B2 = cfg.split_block(it);
  cfg.delete_edges_between(B1, B2);
  // 2. Create a new block throw_block for throwing error.
  cfg::Block* throw_block = cfg.create_block();
  auto member_name_reg = cfg.allocate_temp();
  IRInstruction* const_insn =
      (new IRInstruction(OPCODE_CONST_STRING))
          ->set_string(get_deobfuscated_name_dex_string(member));
  IRInstruction* move_insn =
      (new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT))
          ->set_dest(member_name_reg);
  IRInstruction* invoke_insn = (new IRInstruction(OPCODE_INVOKE_STATIC))
                                   ->set_method(handler)
                                   ->set_srcs_size(1)
                                   ->set_src(0, member_name_reg);
  throw_block->push_back({const_insn, move_insn, invoke_insn});
  // 3. Insert a null-check at the end of B1, and create edges between B1, B2,
  // and throw_block.
  auto opcode = branch_on_null ? OPCODE_IF_EQZ : OPCODE_IF_NEZ;
  IRInstruction* if_insn = new IRInstruction(opcode);
  if_insn->set_src(0, reg_to_check);
  cfg.create_branch(B1, if_insn, throw_block, B2);
  cfg.add_edge(throw_block, B2, cfg::EDGE_GOTO);
}

/* Given an iterator \p it, whose block is B, split block B into B1->B2. Then
 * create one type_check_block(for type checking) and one block throw_block with
 * assertion call. After this insertion, the blocks look like:
 B1 -> type_check_block -> (T) B2
                        |-> (F) throw_block -> B2
*/
template <typename DexMember>
static void insert_type_check_with_throw(cfg::ControlFlowGraph& cfg,
                                         cfg::InstructionIterator& it,
                                         reg_t reg_to_check,
                                         const DexMember* member,
                                         DexMethodRef* handler,
                                         const DexType* dex_type,
                                         bool need_null_check,
                                         bool branch_on_null = true) {
  always_assert(dex_type);
  // 1. Split it into B1->B2, and current 'it' is the last insn of B1.
  cfg::Block* B1 = it.block();
  cfg::Block* B2 = cfg.split_block(it);
  cfg.delete_edges_between(B1, B2);
  // 2. Create a new block throw_block for throwing error.
  cfg::Block* throw_block = cfg.create_block();
  auto member_name_reg = cfg.allocate_temp();
  IRInstruction* const_insn =
      (new IRInstruction(OPCODE_CONST_STRING))
          ->set_string(get_deobfuscated_name_dex_string(member));
  IRInstruction* move_obj_insn =
      (new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT))
          ->set_dest(member_name_reg);
  IRInstruction* invoke_insn = (new IRInstruction(OPCODE_INVOKE_STATIC))
                                   ->set_method(handler)
                                   ->set_srcs_size(1)
                                   ->set_src(0, member_name_reg);
  throw_block->push_back({const_insn, move_obj_insn, invoke_insn});
  // 3. Create a new block type_check_block for type check.
  cfg::Block* type_check_block = cfg.create_block();
  auto res_reg = cfg.allocate_temp();
  IRInstruction* inst_insn = (new IRInstruction(OPCODE_INSTANCE_OF))
                                 ->set_type(const_cast<DexType*>(dex_type))
                                 ->set_src(0, reg_to_check);
  IRInstruction* move_insn =
      (new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO))->set_dest(res_reg);
  IRInstruction* if_insn =
      (new IRInstruction(OPCODE_IF_NEZ))->set_src(0, res_reg);
  type_check_block->push_back({inst_insn, move_insn});
  cfg.create_branch(type_check_block, if_insn, throw_block, B2);
  // 3. If possible, insert a null-check at the end of B1, and update edges
  // between B1, B2, type_check_block, and throw_block.
  if (need_null_check) {
    auto opcode = branch_on_null ? OPCODE_IF_EQZ : OPCODE_IF_NEZ;
    IRInstruction* if_null_insn = new IRInstruction(opcode);
    if_null_insn->set_src(0, reg_to_check);
    cfg.create_branch(B1, if_null_insn, type_check_block, B2);
  } else {
    // Add goto edge between B1 and type_check_block.
    cfg.add_edge(B1, type_check_block, cfg::EDGE_GOTO);
  }
  cfg.add_edge(throw_block, B2, cfg::EDGE_GOTO);
}

RuntimeAssertTransform::Stats RuntimeAssertTransform::apply(
    const local::LocalTypeAnalyzer& /* lta */,
    const WholeProgramState& wps,
    DexMethod* method) {
  auto* code = method->get_code();
  always_assert(code != nullptr);
  RuntimeAssertTransform::Stats stats{};
  bool in_clinit_or_init = method::is_clinit(method) && method::is_init(method);
  bool in_try = false;
  auto& cfg = code->cfg();
  auto ii = cfg::InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    // Avoid emitting checks in a try section.
    // The inserted checks could introduce a throw edge from a block in the try
    // section to the catch section. This could change the CFG and the data
    // flow, which could introduce a type violation.
    if (it->type == MFLOW_TRY) {
      if (it->tentry->type == TRY_START) {
        in_try = true;
      } else if (it->tentry->type == TRY_END) {
        in_try = false;
      }
      continue;
    } else if (it->type != MFLOW_OPCODE) {
      continue;
    }
    if (!in_try) {
      always_assert(it->insn);
      auto next_it = std::next(it);
      bool changed;
      changed =
          insert_field_assert(wps, method, cfg, in_clinit_or_init, it, stats);
      if (changed) {
        // Some code has been inserted. Skip the those code.
        it = next_it;
      }
      changed = insert_return_value_assert(wps, method, cfg, it, stats);
      if (changed) {
        // Some code has been inserted. Skip the those code.
        it = next_it;
      }
    }
  }
  return stats;
}

bool RuntimeAssertTransform::insert_field_assert(const WholeProgramState& wps,
                                                 const DexMethod* method,
                                                 cfg::ControlFlowGraph& cfg,
                                                 bool in_clinit_or_init,
                                                 cfg::InstructionIterator& it,
                                                 Stats& stats) {
  auto* insn = it->insn;
  auto op = insn->opcode();
  if (!opcode::is_an_sget(op) && !opcode::is_an_iget(op)) {
    return false;
  }
  auto* field = resolve_field(insn->get_field());
  if (field == nullptr) {
    return false;
  }
  if (!type::is_object(field->get_type())) {
    return false;
  }
  auto domain = wps.get_field_type(field);
  if (domain.is_top()) {
    return false;
  }
  if (!insn->has_move_result_pseudo()) {
    return false;
  }
  auto mov_res_it = cfg.move_result_of(it);
  if (mov_res_it.is_end()) {
    return false;
  }

  // Nullness check
  // We do not emit null checks for fields in clinits or ctors. Because the
  // field might not be initialized yet.
  bool skip_null_check = domain.is_not_null() || in_clinit_or_init;
  auto reg_to_check = mov_res_it->insn->dest();

  if (!skip_null_check) {
    if (domain.is_null()) {
      insert_null_check_with_throw(cfg, mov_res_it, reg_to_check, field,
                                   m_config.field_assert_fail_handler);
      stats.field_nullness_check_inserted++;
      return true;
    } else if (domain.is_not_null()) {
      insert_null_check_with_throw(cfg, mov_res_it, reg_to_check, field,
                                   m_config.field_assert_fail_handler, false);
      stats.field_nullness_check_inserted++;
    }
  }

  // Singleton type check
  auto dex_type = domain.get_dex_type();
  if (!dex_type) {
    return true;
  }
  if (!type::can_name_type(method, *dex_type,
                           /* app_classes_made_public_later */ false)) {
    return true;
  }

  insert_type_check_with_throw(cfg, mov_res_it, reg_to_check, field,
                               m_config.field_assert_fail_handler, *dex_type,
                               !skip_null_check);
  stats.field_type_check_inserted++;
  return true;
}

bool RuntimeAssertTransform::insert_return_value_assert(
    const WholeProgramState& wps,
    const DexMethod* method,
    cfg::ControlFlowGraph& cfg,
    cfg::InstructionIterator& it,
    Stats& stats) {
  auto* insn = it->insn;
  if (!opcode::is_a_method_invoke(insn->opcode())) {
    return false;
  }

  DexMethod* callee = nullptr;
  DexTypeDomain domain = DexTypeDomain::top();
  if (wps.has_call_graph()) {
    if (wps.invoke_is_dynamic(insn)) {
      return false;
    }
    callee = resolve_invoke_method_deprecated(insn);
    domain = wps.get_return_type_from_cg(insn);
  } else {
    callee =
        resolve_method_deprecated(insn->get_method(), opcode_to_search(insn));
    if (callee == nullptr) {
      return false;
    }
    auto* ret_type = callee->get_proto()->get_rtype();
    if (!type::is_object(ret_type)) {
      return false;
    }
    domain = wps.get_return_type(callee);
  }

  if (domain.is_top()) {
    return false;
  }
  if (it.is_end_in_block()) {
    return false;
  }
  always_assert(callee);

  auto mov_res_it = cfg.move_result_of(it);
  if (mov_res_it.is_end()) {
    return false;
  }

  // Nullness check
  auto reg_to_check = mov_res_it->insn->dest();
  if (domain.is_null()) {
    insert_null_check_with_throw(cfg, mov_res_it, reg_to_check, callee,
                                 m_config.return_value_assert_fail_handler);
    stats.return_nullness_check_inserted++;
    // No need to emit type check anymore.
    return true;
  } else if (domain.is_not_null()) {
    insert_null_check_with_throw(cfg, mov_res_it, reg_to_check, callee,
                                 m_config.return_value_assert_fail_handler,
                                 false);
    stats.return_nullness_check_inserted++;
  }

  // Singleton type check
  auto dex_type = domain.get_dex_type();
  if (!dex_type) {
    return true;
  }
  if (!type::can_name_type(method, *dex_type,
                           /* app_classes_made_public_later */ false)) {
    return true;
  }

  bool skip_null_check = domain.is_not_null();
  insert_type_check_with_throw(cfg, mov_res_it, reg_to_check, callee,
                               m_config.return_value_assert_fail_handler,
                               *dex_type, !skip_null_check);
  stats.return_type_check_inserted++;
  return true;
}

} // namespace type_analyzer
