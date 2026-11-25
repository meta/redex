/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "UsedVarsAnalysis.h"

#include <utility>

#include "ReachableClasses.h"
#include "Show.h"
#include "Trace.h"

namespace ptrs = local_pointers;

namespace {

/*
 * Record the environment before the execution of every instruction. We need
 * this data during the backwards used vars analysis.
 */
UnorderedMap<const IRInstruction*, ptrs::Environment>
gen_instruction_environment_map(const cfg::ControlFlowGraph& cfg,
                                const ptrs::FixpointIterator& fp_iter) {
  UnorderedMap<const IRInstruction*, ptrs::Environment> result;
  for (auto* block : cfg.blocks()) {
    auto env = fp_iter.get_entry_state_at(block);
    for (auto& mie : InstructionIterable(block)) {
      auto* insn = mie.insn;
      result.emplace(insn, env);
      fp_iter.analyze_instruction(insn, &env);
    }
  }
  return result;
}

} // namespace

namespace used_vars {

using namespace ir_analyzer;

FixpointIterator::FixpointIterator(
    const local_pointers::FixpointIterator& pointers_fp_iter,
    side_effects::InvokeToSummaryMap invoke_to_summary_map,
    const cfg::ControlFlowGraph& cfg,
    const DexMethod* method)
    : BaseBackwardsIRAnalyzer<UsedVarsSet>(cfg),
      m_method(method),
      m_insn_env_map(gen_instruction_environment_map(cfg, pointers_fp_iter)),
      m_invoke_to_summary_map(std::move(invoke_to_summary_map)) {}

void FixpointIterator::analyze_instruction(IRInstruction* insn,
                                           UsedVarsSet* used_vars) const {
  TRACE(OSDCE, 5, "Before %s : %s", SHOW(insn), SHOW(*used_vars));
  bool required = is_required(insn, *used_vars);
  auto op = insn->opcode();
  if (ptrs::may_alloc(op)) {
    used_vars->remove(insn);
  }
  if (insn->has_dest()) {
    used_vars->remove(insn->dest());
  } else if (insn->has_move_result_any()) {
    used_vars->remove(RESULT_REGISTER);
  }
  if (required) {
    const auto& env = m_insn_env_map.at(insn);
    if (env.is_bottom()) {
      return;
    }
    // We mark all src registers -- and any pointers they contain -- as used,
    // even if we don't read from the pointee objects. This is done in order to
    // correctly handle the verifier's requirement that all objects are
    // initialized before being used (even if only to make unused writes to them
    // or to check whether the pointer is non-null.) Marking modified objects as
    // used ensures that we don't delete the <init>() calls on them. See the
    // UsedVarsTest_noDeleteInit unit test for a concrete example.
    for (size_t i = 0; i < insn->srcs_size(); ++i) {
      auto reg = insn->src(i);
      used_vars->add(reg);
      const auto& pointers = env.get_pointers(reg);
      if (!pointers.is_value()) {
        continue;
      }
      for (const auto* pointer : pointers.elements()) {
        if (ptrs::may_alloc(pointer->opcode())) {
          used_vars->add(pointer);
        }
      }
    }
    if (opcode::is_move_result_any(op)) {
      used_vars->add(RESULT_REGISTER);
    }
  }
  TRACE(OSDCE, 5, "After: %s", SHOW(*used_vars));
}

bool FixpointIterator::is_used_or_escaping_write(const ptrs::Environment& env,
                                                 const UsedVarsSet& used_vars,
                                                 reg_t obj_reg) const {
  const auto& pointers = env.get_pointers(obj_reg);
  if (!pointers.is_value()) {
    return true;
  }
  for (const auto* pointer : pointers.elements()) {
    if (pointer->opcode() == IOPCODE_LOAD_PARAM_OBJECT ||
        used_vars.contains(pointer) || env.may_have_escaped(pointer)) {
      return true;
    }
  }
  return false;
}

bool FixpointIterator::is_required(const IRInstruction* insn,
                                   const UsedVarsSet& used_vars) const {
  auto op = insn->opcode();
  switch (op) {
  case IOPCODE_LOAD_PARAM:
  case IOPCODE_LOAD_PARAM_OBJECT:
  case IOPCODE_LOAD_PARAM_WIDE:
  // Control-flow opcodes are always required.
  case OPCODE_RETURN_VOID:
  case OPCODE_RETURN:
  case OPCODE_RETURN_WIDE:
  case OPCODE_RETURN_OBJECT:
  case OPCODE_MONITOR_ENTER:
  case OPCODE_MONITOR_EXIT:
  case OPCODE_THROW:
  case OPCODE_GOTO:
  case OPCODE_SWITCH:
  case OPCODE_IF_EQ:
  case OPCODE_IF_NE:
  case OPCODE_IF_LT:
  case OPCODE_IF_GE:
  case OPCODE_IF_GT:
  case OPCODE_IF_LE:
  case OPCODE_IF_EQZ:
  case OPCODE_IF_NEZ:
  case OPCODE_IF_LTZ:
  case OPCODE_IF_GEZ:
  case OPCODE_IF_GTZ:
  case OPCODE_IF_LEZ: {
    return true;
  }
  case OPCODE_APUT:
  case OPCODE_APUT_WIDE:
  case OPCODE_APUT_OBJECT:
  case OPCODE_APUT_BOOLEAN:
  case OPCODE_APUT_BYTE:
  case OPCODE_APUT_CHAR:
  case OPCODE_APUT_SHORT:
  case OPCODE_IPUT:
  case OPCODE_IPUT_WIDE:
  case OPCODE_IPUT_OBJECT:
  case OPCODE_IPUT_BOOLEAN:
  case OPCODE_IPUT_BYTE:
  case OPCODE_IPUT_CHAR:
  case OPCODE_IPUT_SHORT: {
    const auto& env = m_insn_env_map.at(insn);
    return is_used_or_escaping_write(env, used_vars, insn->src(1));
  }
  case OPCODE_FILL_ARRAY_DATA: {
    const auto& env = m_insn_env_map.at(insn);
    return is_used_or_escaping_write(env, used_vars, insn->src(0));
  }
  case OPCODE_SPUT:
  case OPCODE_SPUT_WIDE:
  case OPCODE_SPUT_OBJECT:
  case OPCODE_SPUT_BOOLEAN:
  case OPCODE_SPUT_BYTE:
  case OPCODE_SPUT_CHAR:
  case OPCODE_SPUT_SHORT: {
    return true;
  }
  case OPCODE_INVOKE_SUPER:
  case OPCODE_INVOKE_INTERFACE:
  case OPCODE_INVOKE_DIRECT:
  case OPCODE_INVOKE_STATIC:
  case OPCODE_INVOKE_VIRTUAL: {
    auto* method = resolve_invoke_method_deprecated(insn, m_method);
    const auto& env = m_insn_env_map.at(insn);
    if (method != nullptr) {
      if (method::is_init(method)) {
        if (used_vars.contains(insn->src(0)) ||
            is_used_or_escaping_write(env, used_vars, insn->src(0))) {
          return true;
        }
      } else if (assumenosideeffects(method)) {
        return used_vars.contains(RESULT_REGISTER);
      }
    }
    if (m_invoke_to_summary_map.count(insn) == 0u) {
      return true;
    }
    // A call is required if it has a side-effect, if its return value is used,
    // or if it mutates an argument that may later be read somewhere up the
    // callstack.
    const auto& summary = m_invoke_to_summary_map.at(insn);
    if (summary.effects != side_effects::EFF_NONE ||
        used_vars.contains(RESULT_REGISTER)) {
      return true;
    }
    const auto& mod_params = summary.modified_params;
    return unordered_any_of(mod_params, [&](param_idx_t idx) {
      return is_used_or_escaping_write(env, used_vars, insn->src(idx));
    });
  }
  default: {
    if (insn->has_dest()) {
      return used_vars.contains(insn->dest());
    } else if (insn->has_move_result_any()) {
      return used_vars.contains(RESULT_REGISTER);
    }
    return true;
  }
  }
}

std::vector<cfg::InstructionIterator> get_dead_instructions(
    const cfg::ControlFlowGraph& cfg, const FixpointIterator& fp_iter) {
  std::vector<cfg::InstructionIterator> dead_instructions;
  for (auto* block : cfg.blocks()) {
    auto used_vars = fp_iter.get_used_vars_at_exit(block);
    TRACE(OSDCE, 5, "B%zu exit : %s", block->id(), SHOW(used_vars));
    for (auto& mie : InstructionIterable(block).reversed()) {
      auto* insn = mie.insn;
      if (!fp_iter.is_required(insn, used_vars)) {
        // move-result-pseudo instructions will be automatically removed
        // when their primary instruction is deleted.
        if (!opcode::is_a_move_result_pseudo(insn->opcode())) {
          dead_instructions.emplace_back(
              block->to_cfg_instruction_iterator(mie));
        }
      }
      fp_iter.analyze_instruction(insn, &used_vars);
    }
    TRACE(OSDCE, 5, "B%zu entry : %s", block->id(),
          SHOW(fp_iter.get_used_vars_at_entry(block)));
  }
  return dead_instructions;
}
} // namespace used_vars
