/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "StringBuilderAppendChain.h"

#include <algorithm>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "CFGMutation.h"
#include "ConstantEnvironment.h"
#include "ConstantPropagationAnalysis.h"
#include "ConstantPropagationTransform.h"
#include "ControlFlow.h"
#include "DeterministicContainers.h"
#include "DexClass.h"
#include "IRInstruction.h"
#include "IROpcode.h"
#include "MethodUtil.h"
#include "StringBuilderAnalysis.h"

namespace constant_propagation::stringbuilder_append_chain {

namespace {

// The concat reads its operands at the toString(), by which point the register
// an append read may hold something else:
//
//   append(v0, v1)          ; the builder gets v1's value
//   const-string "x" -> v1
//   toString(v0)            ; a concat reading v1 would see "x"
//
// Inserting `move-object vFresh, v1` right before the append copies the value
// into a register no other instruction writes to, so it still reads back at
// the toString(); the concat takes vFresh as its operand. A builder reached by
// more than one toString() reuses the temp already allocated for that append,
// so `capture_moves` records the move made for each append.
reg_t capture_append_value(
    cfg::ControlFlowGraph& cfg,
    UnorderedMap<const IRInstruction*, IRInstruction*>& capture_moves,
    const IRInstruction* append_insn) {
  if (auto move_it = capture_moves.find(append_insn);
      move_it != capture_moves.end()) {
    return move_it->second->dest();
  }
  reg_t reg = cfg.allocate_temp();
  auto* move = (new IRInstruction(OPCODE_MOVE_OBJECT))
                   ->set_src(0, append_insn->src(1))
                   ->set_dest(reg);
  capture_moves.emplace(append_insn, move);
  return reg;
}

// Whether `insn` invokes the String overload of StringBuilder.append. The other
// overloads take a value whose text is a conversion, so they are not
// interchangeable with it.
bool is_string_append(const IRInstruction* insn) {
  return insn->has_method() &&
         insn->get_method() == method::java_lang_StringBuilder_append_String();
}

} // namespace

size_t reduce_two_append_concats(
    const intraprocedural::FixpointIterator& fp_iter,
    cfg::ControlFlowGraph& cfg) {
  // Scanning for toString() first keeps the more expensive fixpoint off methods
  // that have no builder to reduce.
  auto tostring_instructions =
      stringbuilder_analysis::find_tostring_instructions(
          cfg, method::java_lang_StringBuilder_toString());
  if (tostring_instructions.empty()) {
    return 0;
  }
  auto tostring_to_state =
      stringbuilder_analysis::gather_builder_states(cfg, tostring_instructions);

  struct TwoAppendInsns {
    const IRInstruction* tostring;
    const IRInstruction* append_a;
    const IRInstruction* append_b;
  };
  std::vector<TwoAppendInsns> candidates;
  for (const auto& [tostring_insn, state] : tostring_to_state) {
    // String.concat takes a String receiver and argument, so appends of the
    // other modeled types are not candidates.
    if (state.size() == 2 && is_string_append(state[0]) &&
        is_string_append(state[1])) {
      candidates.push_back({tostring_insn, state[0], state[1]});
    }
  }
  if (candidates.empty()) {
    return 0;
  }

  // Read each append operand's non-nullness from the solved fixpoint by
  // replaying it per block to recover the state before each append.
  UnorderedSet<const IRInstruction*> non_null_ops;
  for (auto* block : cfg.blocks()) {
    auto env = fp_iter.get_entry_state_at(block);
    if (env.is_bottom()) {
      continue;
    }
    auto last_insn = block->get_last_insn();
    for (auto& mie : InstructionIterable(block)) {
      auto* insn = mie.insn;
      if (is_string_append(insn) && is_known_non_null(env.get(insn->src(1)))) {
        non_null_ops.insert(insn);
      }
      fp_iter.analyze_instruction(insn, &env, insn == last_insn->insn);
    }
  }

  UnorderedMap<const IRInstruction*, IRInstruction*> capture_moves_to_insert;
  UnorderedMap<const IRInstruction*, std::pair<reg_t, reg_t>>
      tostring_to_concat_srcs;
  auto* concat_ref = DexMethod::make_method(
      "Ljava/lang/String;.concat:(Ljava/lang/String;)Ljava/lang/String;");

  size_t reduced = 0;
  for (const auto& cand : candidates) {
    if (!non_null_ops.contains(cand.append_a) ||
        !non_null_ops.contains(cand.append_b)) {
      continue;
    }
    reg_t reg_a =
        capture_append_value(cfg, capture_moves_to_insert, cand.append_a);
    reg_t reg_b =
        capture_append_value(cfg, capture_moves_to_insert, cand.append_b);
    tostring_to_concat_srcs.emplace(cand.tostring, std::pair(reg_a, reg_b));
    reduced++;
  }

  if (tostring_to_concat_srcs.empty()) {
    return 0;
  }

  // Insert each capture move before its append, and turn each toString() into
  // String.concat.
  cfg::CFGMutation mutation(cfg);
  for (auto* block : cfg.blocks()) {
    for (auto& mie : InstructionIterable(block)) {
      auto* insn = mie.insn;
      // insert moves
      if (auto move_it = capture_moves_to_insert.find(insn);
          move_it != capture_moves_to_insert.end()) {
        mutation.insert_before(block->to_cfg_instruction_iterator(mie),
                               {move_it->second});
      }
      // replace toString with concat
      if (auto srcs_it = tostring_to_concat_srcs.find(insn);
          srcs_it != tostring_to_concat_srcs.end()) {
        insn->set_method(concat_ref)->set_srcs_size(2);
        insn->set_src(0, srcs_it->second.first);
        insn->set_src(1, srcs_it->second.second);
      }
    }
  }
  mutation.flush();

  return reduced;
}

size_t merge_adjacent_constant_appends(
    const intraprocedural::FixpointIterator& fp_iter,
    cfg::ControlFlowGraph& cfg) {
  // Counting String appends first keeps the fixpoint replay below off methods
  // with no two appends to merge.
  auto ii = cfg::InstructionIterable(cfg);
  if (std::count_if(ii.begin(), ii.end(), [](const auto& mie) {
        return is_string_append(mie.insn);
      }) < 2) {
    return 0;
  }

  UnorderedMap<const IRInstruction*, const DexString*>
      first_append_invocation_to_concatenated_string;
  UnorderedSet<const IRInstruction*> append_invocations_to_drop;
  std::vector<std::pair<const IRInstruction*, const DexString*>> group;
  auto flush_group = [&]() {
    if (group.size() >= 2) {
      std::string concatenated_string;
      for (const auto& [append_insn, constant] : group) {
        concatenated_string += constant->str_copy();
        if (append_insn != group.front().first) {
          append_invocations_to_drop.insert(append_insn);
        }
      }
      first_append_invocation_to_concatenated_string.emplace(
          group.front().first, DexString::make_string(concatenated_string));
    }
    group.clear();
  };
  // Whether `insn` can appear between two appends in `group`: it either writes
  // the previous append's result back to the builder register, or loads a
  // string constant into another register.
  auto is_allowed_between_appends = [&group](const IRInstruction* insn) {
    reg_t builder_reg = group.front().first->src(0);
    switch (insn->opcode()) {
    case OPCODE_CONST_STRING:
      return true;
    case IOPCODE_MOVE_RESULT_PSEUDO_OBJECT:
      return insn->dest() != builder_reg;
    case OPCODE_MOVE_RESULT_OBJECT:
      return insn->dest() == builder_reg;
    default:
      return false;
    }
  };
  for (auto* block : cfg.blocks()) {
    auto env = fp_iter.get_entry_state_at(block);
    if (env.is_bottom()) {
      continue;
    }
    auto last_insn = block->get_last_insn();
    for (auto& mie : InstructionIterable(block)) {
      auto* insn = mie.insn;
      if (is_string_append(insn)) {
        // Only an append that writes its result back to its receiver register,
        // or discards it, can be deleted: the receiver register already holds
        // the builder, so deleting the append changes nothing that later code
        // reads.
        auto result_it =
            cfg.move_result_of(block->to_cfg_instruction_iterator(mie));
        bool is_self_loop =
            result_it.is_end() || result_it->insn->dest() == insn->src(0);
        const DexString* constant = nullptr;
        auto value = env.get(insn->src(1));
        if (const auto& sd = value.maybe_get<StringDomain>()) {
          if (auto c = sd->get_constant()) {
            constant = *c;
          }
        }
        if (!group.empty() && (constant == nullptr || !is_self_loop ||
                               insn->src(0) != group.front().first->src(0))) {
          flush_group();
        }
        if (constant != nullptr && is_self_loop) {
          group.emplace_back(insn, constant);
        }
      } else if (!group.empty() && !is_allowed_between_appends(insn)) {
        flush_group();
      }
      fp_iter.analyze_instruction(insn, &env, insn == last_insn->insn);
    }
    flush_group();
  }
  if (first_append_invocation_to_concatenated_string.empty()) {
    return 0;
  }

  // `mutation.remove` takes each dropped append's move-result-object with it.
  // The operand loads the merge orphans are left for a later LocalDce run.
  cfg::CFGMutation mutation(cfg);
  for (auto* block : cfg.blocks()) {
    for (auto& mie : InstructionIterable(block)) {
      auto* insn = mie.insn;
      auto it = block->to_cfg_instruction_iterator(mie);
      if (auto concatenated_string_it =
              first_append_invocation_to_concatenated_string.find(insn);
          concatenated_string_it !=
          first_append_invocation_to_concatenated_string.end()) {
        reg_t reg = cfg.allocate_temp();
        auto* const_insn = (new IRInstruction(OPCODE_CONST_STRING))
                               ->set_string(concatenated_string_it->second);
        auto* move_insn = (new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT))
                              ->set_dest(reg);
        mutation.insert_before(it, {const_insn, move_insn});
        insn->set_src(1, reg);
      }
      if (append_invocations_to_drop.contains(insn)) {
        mutation.remove(it);
      }
    }
  }
  mutation.flush();

  return append_invocations_to_drop.size();
}

size_t replace_constant_tostring_with_const_string(
    const intraprocedural::FixpointIterator& fp_iter,
    cfg::ControlFlowGraph& cfg) {
  auto tostring_instructions =
      stringbuilder_analysis::find_tostring_instructions(
          cfg, method::java_lang_StringBuilder_toString());
  if (tostring_instructions.empty()) {
    return 0;
  }
  auto tostring_to_state =
      stringbuilder_analysis::gather_builder_states(cfg, tostring_instructions);

  UnorderedMap<const IRInstruction*, const IRInstruction*> tostring_to_append;
  for (const auto& [tostring_insn, state] : tostring_to_state) {
    // We only need to handle chains with single append because
    // merge_adjacent_constant_appends should have merged consecutive appends on
    // constants.
    if (state.size() == 1u && is_string_append(state[0])) {
      tostring_to_append.emplace(tostring_insn, state[0]);
    }
  }

  if (tostring_to_append.empty()) {
    return 0;
  }

  UnorderedMap<const IRInstruction*, const DexString*>
      append_invocation_to_constant;
  for (auto* block : cfg.blocks()) {
    auto env = fp_iter.get_entry_state_at(block);
    if (env.is_bottom()) {
      continue;
    }
    auto last_insn = block->get_last_insn();
    for (auto& mie : InstructionIterable(block)) {
      auto* insn = mie.insn;
      if (is_string_append(insn)) {
        auto value = env.get(insn->src(1));
        if (const auto& sd = value.maybe_get<StringDomain>()) {
          if (auto c = sd->get_constant()) {
            append_invocation_to_constant.emplace(insn, *c);
          }
        }
      }
      fp_iter.analyze_instruction(insn, &env, insn == last_insn->insn);
    }
  }

  size_t replaced = 0;
  cfg::CFGMutation mutation(cfg);
  for (auto* block : cfg.blocks()) {
    for (auto& mie : InstructionIterable(block)) {
      auto* insn = mie.insn;
      const auto append_it = tostring_to_append.find(insn);
      if (append_it == tostring_to_append.end()) {
        continue;
      }
      auto constant_string_it =
          append_invocation_to_constant.find(append_it->second);
      if (constant_string_it == append_invocation_to_constant.end()) {
        continue;
      }
      auto result_it =
          cfg.move_result_of(block->to_cfg_instruction_iterator(mie));
      // No need to handle a toString() whose result is discarded. A dead code
      // elimination pass will delete it.
      if (result_it.is_end()) {
        continue;
      }
      auto* const_insn = (new IRInstruction(OPCODE_CONST_STRING))
                             ->set_string(constant_string_it->second);
      // Replacing the toString() removes its move-result-object too, so this
      // must write the same register.
      auto* move_insn = (new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT))
                            ->set_dest(result_it->insn->dest());
      mutation.replace(block->to_cfg_instruction_iterator(mie),
                       {const_insn, move_insn});
      replaced++;
    }
  }
  mutation.flush();

  return replaced;
}

} // namespace constant_propagation::stringbuilder_append_chain
