/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "DedupBlockValueNumbering.h"

#include <map>

#include "Debug.h"
#include "RedexContext.h"

using namespace DedupBlkValueNumbering;

// Make sure there is no padding in IROperationSourceBlock.
static_assert(sizeof(IROperationSourceBlock) ==
                  sizeof(uint32_t) + sizeof(DexString*),
              "IROperationSourceBlock has padding!");

// Make sure that looking at IROperationSourceBlock is OK.
static_assert(sizeof(IROperationSourceBlock) >= sizeof(uint64_t),
              "IROperationSourceBlock is not largest member!");

// Make sure IROperation is small without too much padding.
static_assert(sizeof(size_t) != 8 || sizeof(IROperation) == 40,
              "IROperationSourceBlock has unexpected size");

void next_opcode_or_srcblk(IRList::iterator& block_it, cfg::Block* block) {
  if (g_redex->instrument_mode) {
    while (block_it != block->end() && block_it->type != MFLOW_OPCODE &&
           block_it->type != MFLOW_SOURCE_BLOCK) {
      ++block_it;
    }
  } else {
    while (block_it != block->end() && block_it->type != MFLOW_OPCODE) {
      ++block_it;
    }
  }
}

// Return BlockValue hash for the given block.
const BlockValue* BlockValues::get_block_value(cfg::Block* block) const {
  // Check if we have already computed.
  auto it = m_block_values.find(block);
  if (it != m_block_values.end()) {
    return it->second.get();
  }

  std::unique_ptr<BlockValue> block_value = std::make_unique<BlockValue>();
  auto& regs = block_value->out_regs;
  auto& ordered_operations = block_value->ordered_operations;
  auto block_it = block->begin();
  while (block_it != block->end()) {
    next_opcode_or_srcblk(block_it, block);
    if (block_it != block->end()) {
      if (block_it->type == MFLOW_OPCODE) {
        auto operation = get_operation(regs, block_it->insn);
        bool is_ordered = is_ordered_operation(operation);
        if (is_ordered) {
          ordered_operations.push_back(operation);
        } else {
          always_assert(operation.opcode == OPCODE_NOP ||
                        block_it->insn->has_dest());
        }
        if (block_it->insn->has_dest()) {
          if (is_ordered) {
            operation.opcode = IOPCODE_OPERATION_RESULT;
            operation.srcs.clear();
            operation.op_data.operation_index = ordered_operations.size() - 1;
          }
          auto value = opcode::is_a_move(operation.opcode)
                           ? operation.srcs.at(0)
                           : get_value_id(operation);
          regs[block_it->insn->dest()] = value;
          if (block_it->insn->dest_is_wide()) {
            regs.erase(block_it->insn->dest() + 1);
          }
        }
      } else if (block_it->type == MFLOW_SOURCE_BLOCK) {
        SourceBlock* cur_src_blk = block_it->src_block.get();
        while (cur_src_blk != nullptr) {
          IROperation operation;
          operation.op_data.src_blk = {cur_src_blk->src, cur_src_blk->id};
          ordered_operations.push_back(operation);
          cur_src_blk = cur_src_blk->next.get();
        }
      }
      block_it++;
    }
  }
  const auto& live_out_vars =
      m_liveness_fixpoint_iter.get_live_out_vars_at(block);
  always_assert(!live_out_vars.is_top());
  always_assert(!live_out_vars.is_bottom());
  std::erase_if(regs, [&live_out_vars](auto& p) {
    return !live_out_vars.elements().contains(p.first);
  });
  for (auto reg : live_out_vars.elements()) {
    prepare_and_get_reg(regs, reg);
  }
  auto* ptr = block_value.get();
  m_block_values.emplace(block, std::move(block_value));
  return ptr;
};

value_id_t BlockValues::prepare_and_get_reg(std::map<reg_t, value_id_t>& regs,
                                            reg_t reg) const {
  auto it = regs.find(reg);
  if (it != regs.end()) {
    return it->second;
  }
  IROperation operation;
  operation.opcode = IOPCODE_LOAD_REG;
  operation.op_data.in_reg = reg;
  auto value = get_value_id(operation);
  regs.emplace(reg, value);
  return value;
}

IROperation BlockValues::get_operation(std::map<reg_t, value_id_t>& regs,
                                       const IRInstruction* insn) const {
  IROperation operation;
  auto opcode = insn->opcode();
  operation.opcode = opcode;
  for (auto reg : insn->srcs()) {
    operation.srcs.push_back(prepare_and_get_reg(regs, reg));
  }
  if (opcode::is_commutative(opcode)) {
    std::sort(operation.srcs.begin(), operation.srcs.end());
  }
  if (insn->has_literal()) {
    operation.op_data.literal = insn->get_literal();
  } else if (insn->has_type()) {
    operation.op_data.type = insn->get_type();
  } else if (insn->has_field()) {
    operation.op_data.field = insn->get_field();
  } else if (insn->has_signature_polymorphic()) {
    // The call-site prototype is part of the call: `invokeExact` typed `()V`
    // and typed `()I` are different calls.
    operation.op_data.literal =
        reinterpret_cast<uintptr_t>(insn->get_signature_polymorphic());
  } else if (insn->has_method()) {
    operation.op_data.method = insn->get_method();
  } else if (insn->has_string()) {
    operation.op_data.string = insn->get_string();
  } else if (insn->has_data()) {
    operation.op_data.data = insn->get_data();
  } else if (insn->has_callsite()) {
    // op_data is hashed and compared as raw bytes, so storing the ref's
    // identity in any pointer-sized member is enough to tell refs apart.
    operation.op_data.literal =
        reinterpret_cast<uintptr_t>(insn->get_callsite());
  } else if (insn->has_methodhandle()) {
    operation.op_data.literal =
        reinterpret_cast<uintptr_t>(insn->get_methodhandle());
  } else if (insn->has_proto()) {
    operation.op_data.literal = reinterpret_cast<uintptr_t>(insn->get_proto());
  }
  return operation;
}

bool BlockValues::is_ordered_operation(const IROperation& operation) const {
  always_assert(operation.opcode != IOPCODE_LOAD_REG &&
                operation.opcode != IOPCODE_OPERATION_RESULT);
  return operation.opcode == OPCODE_MOVE_EXCEPTION ||
         opcode::has_side_effects(operation.opcode) ||
         opcode::is_a_load_param(operation.opcode) ||
         opcode::is_move_result_any(operation.opcode) ||
         opcode::may_throw(operation.opcode);
}

value_id_t BlockValues::get_value_id(const IROperation& operation) const {
  always_assert(!opcode::is_a_move(operation.opcode));
  auto it = m_value_ids.find(operation);
  if (it != m_value_ids.end()) {
    return it->second;
  }
  value_id_t id = m_value_ids.size();
  m_value_ids.emplace(operation, id);
  return id;
}
