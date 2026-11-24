/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "PartialInliner.h"

#include "CFGInliner.h"
#include "Debug.h"
#include "Inliner.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "Trace.h"

namespace inliner {

IROpcode get_fallback_invoke_opcode(const DexMethod* method) {
  if (is_static(method)) {
    return OPCODE_INVOKE_STATIC;
  }
  if (!method->is_virtual()) {
    return OPCODE_INVOKE_DIRECT;
  }
  auto* cls = type_class(method->get_class());
  // Callers reach this only for an inliner candidate, which is concrete and
  // defined by a class in scope. A null here means a non-scope or external
  // method got through, and guessing invoke-virtual for it would emit a wrong
  // opcode rather than surface the bug -- `is_interface` would also just
  // dereference the null.
  always_assert_log(cls != nullptr, "%s has no DexClass\n", SHOW(method));
  return is_interface(cls) ? OPCODE_INVOKE_INTERFACE : OPCODE_INVOKE_VIRTUAL;
}

PartialCode get_partially_inlined_code(const DexMethod* method,
                                       const cfg::ControlFlowGraph& cfg,
                                       uint32_t max_code_units) {
  if (!source_blocks::is_hot(cfg.entry_block())) {
    // No hot entry block? That suggests that something went wrong with our
    // source-blocks. Anyway, we are not going to fight that here.
    TRACE(INLINE, 4,
          "Mismatch between initial and eventual assessment of entry point "
          "hotness in %s. This should not happen, and suggests some problem "
          "with how source blocks are handled by some inlining and local "
          "transformations.",
          SHOW(method));
    return PartialCode();
  }

  auto normal_blocks = cfg.blocks_reaching_return();
  if (normal_blocks.count(cfg.entry_block()) == 0u) {
    // We are not interested in methods that always throw. Those certainly
    // exist.
    return PartialCode();
  }
  auto can_inline_block = [&](cfg::Block* block) {
    for (auto& mie : InstructionIterable(block)) {
      auto* insn = mie.insn;
      auto op = insn->opcode();
      if (opcode::is_an_aput(op) || opcode::is_an_sput(op) ||
          opcode::is_an_iput(op) || opcode::is_fill_array_data(op) ||
          opcode::is_an_invoke(op)) {
        // TODO: It's okay to mutate newly created objects, and to invoke
        // pure methods. (Then again, we don't want the code to grow too large.)
        return false;
      }
      if (opcode::is_a_monitor(op) || opcode::is_throw(op)) {
        // No inherent problem with monitor or throw, we just don't think they
        // are good candidates to improve performance with partial inlining.
        return false;
      }
      if (opcode::is_switch(op)) {
        // No inherent problem with switches, we just want to dodge the
        // cost-accounting, and code with switches is probably getting too big
        // anyway.
        return false;
      }
      always_assert(!opcode::has_side_effects(op) || opcode::is_a_return(op) ||
                    opcode::is_branch(op) || opcode::is_an_internal(op));
      // Some of the allowed opcodes have indirect side effects, e.g.
      // new-instance and init-class instructions can trigger static
      // initializers to run, and/or throw exceptions. That is okay, as they are
      // idempotent, and/or might get cleaned up by Local-DCE.
    }
    return true;
  };

  std::queue<cfg::Block*> work_queue;
  work_queue.push(cfg.entry_block());
  UnorderedSet<cfg::Block*> inline_blocks;
  uint32_t code_units{0};
  UnorderedSet<cfg::Block*> visited;
  while (!work_queue.empty()) {
    auto* block = work_queue.front();
    work_queue.pop();
    if (!visited.emplace(block).second) {
      continue;
    }
    if ((normal_blocks.count(block) == 0u) ||
        !source_blocks::maybe_hot(block)) {
      // We ignore blocks that are cold or will eventually throw exception.
      continue;
    }
    if (!can_inline_block(block)) {
      // We have not-cold block that we can't deal with. Give up.
      return PartialCode();
    }
    inline_blocks.insert(block);
    code_units += block->estimate_code_units();
    if (code_units > max_code_units) {
      // Too large
      return PartialCode();
    }
    for (auto* edge : block->succs()) {
      if (edge->type() == cfg::EDGE_THROW) {
        // Let's not inline blocks with exception handlers. Give up.
        return PartialCode();
      }
      work_queue.push(edge->target());
    }
  }
  always_assert(!inline_blocks.empty());
  if (!unordered_any_of(inline_blocks, [&](cfg::Block* block) {
        auto b = block->branchingness();
        return b == opcode::BRANCH_RETURN;
      })) {
    // We didn't find any normal-return path. Partial inlining is unlikely to be
    // beneficial.
    return PartialCode();
  }

  // Any non-inlinable blocks?
  auto blocks = cfg.blocks();
  if (std::none_of(blocks.begin(), blocks.end(), [&](cfg::Block* block) {
        return (inline_blocks.count(block) == 0u) && !can_inline_block(block);
      })) {
    // We didn't find any non-inlinable blocks that we wouldn't inline. So
    // "partial" inlining here would amount to either fully inlining the callee,
    // or inlining the callee fully except for some rather trivial code. There
    // is nothing technically wrong with that, but it goes beyond the idea of
    // partially inlining for performance: "partial" inlining here would
    // degenerate into simply inlining small callees.
    // TODO: Experiment with inlining small callees for performance even if that
    // leads to increased code size.
    return PartialCode();
  }

  // Clone cfg
  auto partial_code = std::make_shared<ReducedCode>();
  auto& partial_cfg = partial_code->cfg();
  cfg.deep_copy(&partial_cfg);

  std::vector<IRInstruction*> arg_copy_insns;
  std::vector<reg_t> arg_copies;
  for (const auto& mie :
       InstructionIterable(partial_cfg.get_param_instructions())) {
    auto* insn = mie.insn;
    auto op = insn->opcode();
    switch (op) {
    case IOPCODE_LOAD_PARAM:
      op = OPCODE_MOVE;
      break;
    case IOPCODE_LOAD_PARAM_OBJECT:
      op = OPCODE_MOVE_OBJECT;
      break;
    case IOPCODE_LOAD_PARAM_WIDE:
      op = OPCODE_MOVE_WIDE;
      break;
    default:
      not_reached();
    }
    auto tmp_reg = insn->dest_is_wide() ? partial_cfg.allocate_wide_temp()
                                        : partial_cfg.allocate_temp();
    arg_copy_insns.push_back(
        (new IRInstruction(op))->set_src(0, insn->dest())->set_dest(tmp_reg));
    arg_copies.push_back(tmp_reg);
  }
  auto* entry_block = partial_cfg.entry_block();
  auto insert_it = entry_block->get_first_non_param_loading_insn();
  partial_cfg.insert_before(entry_block->to_cfg_instruction_iterator(insert_it),
                            arg_copy_insns);

  auto* invoke_insn = (new IRInstruction(get_fallback_invoke_opcode(method)))
                          ->set_method(const_cast<DexMethod*>(method))
                          ->set_srcs_size(arg_copy_insns.size());
  for (src_index_t i = 0; i < arg_copies.size(); i++) {
    invoke_insn->set_src(i, arg_copies[i]);
  }
  std::vector<IRInstruction*> fallback_insns{invoke_insn};
  auto* proto = method->get_proto();
  if (proto->is_void()) {
    fallback_insns.push_back(new IRInstruction(OPCODE_RETURN_VOID));
  } else {
    auto* rtype = proto->get_rtype();
    auto tmp_reg = type::is_wide_type(rtype) ? partial_cfg.allocate_wide_temp()
                                             : partial_cfg.allocate_temp();
    auto move_result_op = type::is_object(rtype) ? OPCODE_MOVE_RESULT_OBJECT
                          : type::is_wide_type(rtype) ? OPCODE_MOVE_RESULT_WIDE
                                                      : OPCODE_MOVE_RESULT;
    fallback_insns.push_back(
        (new IRInstruction(move_result_op))->set_dest(tmp_reg));
    auto return_op = type::is_object(rtype)      ? OPCODE_RETURN_OBJECT
                     : type::is_wide_type(rtype) ? OPCODE_RETURN_WIDE
                                                 : OPCODE_RETURN;
    fallback_insns.push_back(
        (new IRInstruction(return_op))->set_src(0, tmp_reg));
  }
  auto* fallback_block = partial_cfg.create_block();
  // Insert magic position that the cfg-inliner recognizes
  const auto* method_str = DexString::make_string(show_deobfuscated(method));
  auto new_pos = std::make_unique<DexPosition>(
      method_str, cfg::get_partial_inline_source(), 0);
  partial_cfg.insert_before(fallback_block, fallback_block->begin(),
                            std::move(new_pos));
  // Insert cold source-block
  auto* template_sb = source_blocks::get_first_source_block(cfg.entry_block());
  fallback_block->push_back(fallback_insns);
  always_assert(template_sb);
  auto new_sb = source_blocks::clone_as_synthetic(template_sb, method,
                                                  SourceBlock::Val(0, 0));
  fallback_block->insert_before(fallback_block->begin(), std::move(new_sb));

  UnorderedSet<size_t> retained_block_ids{fallback_block->id()};
  retained_block_ids.reserve(inline_blocks.size());
  for (auto* block : UnorderedIterable(inline_blocks)) {
    retained_block_ids.insert(block->id());
  }
  for (auto* block : partial_cfg.blocks()) {
    if (retained_block_ids.count(block->id()) != 0u) {
      continue;
    }
    auto first_insn_it = block->get_first_insn();
    if (first_insn_it == block->end()) {
      // Don't bother with empty blocks.
      continue;
    }
    if (opcode::is_move_result_any(first_insn_it->insn->opcode())) {
      if (first_insn_it == block->get_last_insn()) {
        // A block with only a move-result(-pseudo) doesn't have useful
        // source-block data.
        continue;
      }
      first_insn_it++;
    }

    block = partial_cfg.split_block_before(block, first_insn_it);
    partial_cfg.delete_succ_edges(block);
    partial_cfg.add_edge(block, fallback_block, cfg::EDGE_GOTO);
  }

  // Re-build cfg once more to get linearized representation, good for
  // chaining fallthrough branches
  partial_code->code().build_cfg();

  TRACE(INLINE, 5,
        "Derived partial code (%u code units) for %s:\nbefore:\n%s\nafter:\n%s",
        code_units, SHOW(method), SHOW(cfg), SHOW(partial_cfg));

  auto insn_size = partial_code->cfg().estimate_code_units();
  return PartialCode{std::move(partial_code), insn_size};
}

} // namespace inliner
