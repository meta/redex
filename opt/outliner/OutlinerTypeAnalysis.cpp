/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "OutlinerTypeAnalysis.h"

#include "Debug.h"
#include "DexClass.h"
#include "DexTypeEnvironment.h"
#include "Lazy.h"
#include "Show.h"

namespace outliner_impl {

OutlinerTypeAnalysis::OutlinerTypeAnalysis(DexMethod* method)
    : m_method(method),
      m_reaching_defs_environments([method]() {
        auto& cfg = method->get_code()->cfg();
        reaching_defs::MoveAwareFixpointIterator reaching_defs_fp_iter(cfg);
        reaching_defs_fp_iter.run({});
        ReachingDefsEnvironments res;
        for (auto* block : cfg.blocks()) {
          auto env = reaching_defs_fp_iter.get_entry_state_at(block);
          for (auto& mie : InstructionIterable(block)) {
            res[mie.insn] = env;
            reaching_defs_fp_iter.analyze_instruction(mie.insn, &env);
          }
        }
        return res;
      }),
      m_immediate_chains([method]() {
        auto& cfg = method->get_code()->cfg();
        return std::make_unique<live_range::Chains>(cfg);
      }),
      m_immediate_reaching_defs_environments([this, method]() {
        auto& cfg = method->get_code()->cfg();
        const auto& reaching_defs_fp_iter = m_immediate_chains->get_fp_iter();
        ReachingDefsEnvironments res;
        for (auto* block : cfg.blocks()) {
          auto env = reaching_defs_fp_iter.get_entry_state_at(block);
          for (auto& mie : InstructionIterable(block)) {
            res[mie.insn] = env;
            reaching_defs_fp_iter.analyze_instruction(mie.insn, &env);
          }
        }
        return res;
      }),
      m_immediate_def_uses([this]() {
        return std::make_unique<live_range::DefUseChains>(
            m_immediate_chains->get_def_use_chains());
      }),
      m_type_environments([method]() {
        auto& cfg = method->get_code()->cfg();
        type_inference::TypeInference type_inference(cfg);
        type_inference.run(method);
        // Move, not copy: `type_inference` is a local that dies with this
        // lambda, and the map holds one environment per instruction.
        return std::move(type_inference.get_type_environments());
      }),
      m_constant_uses([method]() {
        auto& cfg = method->get_code()->cfg();
        return std::make_unique<constant_uses::ConstantUses>(cfg, method);
      }) {}

const DexType* OutlinerTypeAnalysis::get_result_type(
    const CandidateAdapter* ca,
    const UnorderedSet<const IRInstruction*>& insns,
    const DexType* optional_extra_type) {
  auto defs = get_defs(insns);
  return defs ? get_type_of_defs(ca, *defs, optional_extra_type)
              : optional_extra_type;
}

const DexType* OutlinerTypeAnalysis::get_type_demand(const CandidateAdapter& ca,
                                                     reg_t reg) {
  UnorderedSet<reg_t> regs_to_track{reg};
  UnorderedSet<const DexType*> type_demands;
  get_type_demand_helper(ca, std::move(regs_to_track), &type_demands);
  const auto* type_demand = narrow_type_demands(std::move(type_demands));
  if (type_demand == nullptr) {
    type_demand = get_inferred_type(ca, reg);
  }
  return type_demand;
}

const DexType* OutlinerTypeAnalysis::get_inferred_type(
    const CandidateAdapter& ca, reg_t reg) {
  const auto& env = ca.get_type_env();
  switch (env.get_type(reg).element()) {
  case IRType::BOTTOM:
  case IRType::ZERO:
  case IRType::CONST:
  case IRType::CONST1:
  case IRType::SCALAR:
  case IRType::SCALAR1:
    // Can't figure out exact type via type inference; let's try reaching-defs
    return get_type_of_reaching_defs(ca, reg);
  case IRType::REFERENCE: {
    auto dex_type = env.get_dex_type(reg);
    return dex_type ? *dex_type : nullptr;
  }
  case IRType::INT:
    // Could actually be boolean, byte, short; let's try reaching-defs
    return get_type_of_reaching_defs(ca, reg);
  case IRType::FLOAT:
    return type::_float();
  case IRType::LONG1:
    return type::_long();
  case IRType::DOUBLE1:
    return type::_double();
  case IRType::CONST2:
  case IRType::DOUBLE2:
  case IRType::LONG2:
  case IRType::SCALAR2:
  case IRType::TOP:
  default:
    // shouldn't happen for any input, but we don't need to fight that here
    return nullptr;
  }
}

const DexType* OutlinerTypeAnalysis::narrow_type_demands(
    UnorderedSet<const DexType*> type_demands) {
  if (type_demands.empty() || (type_demands.count(nullptr) != 0u)) {
    return nullptr;
  }

  if (type_demands.size() > 1) {
    // Less strict primitive type demands can be removed
    if (type_demands.count(type::_boolean()) != 0u) {
      type_demands.erase(type::_byte());
      type_demands.erase(type::_short());
      type_demands.erase(type::_char());
      type_demands.erase(type::_int());
    } else if (type_demands.count(type::_byte()) != 0u) {
      if (type_demands.count(type::_char()) != 0u) {
        type_demands = {type::_int()};
      } else {
        type_demands.erase(type::_short());
        type_demands.erase(type::_int());
      }
    } else if (type_demands.count(type::_short()) != 0u) {
      if (type_demands.count(type::_char()) != 0u) {
        type_demands = {type::_int()};
      } else {
        type_demands.erase(type::_int());
      }
    } else if (type_demands.count(type::_char()) != 0u) {
      type_demands.erase(type::_int());
    }

    // remove less specific object types
    unordered_erase_if(type_demands, [&type_demands](auto* u) {
      return type::is_object(u) &&
             unordered_any_of(type_demands, [u](const DexType* t) {
               return t != u && type::is_object(t) && type::check_cast(t, u);
             });
    });

    // TODO: I saw that most often, when multiple object type demands
    // remain, they are often even contradictory, and that's because in fact
    // the value that flows in is a null constant, which is the only
    // feasible value in those cases. Still, a relatively uncommon
    // occurrence overall.
  }

  return type_demands.size() == 1 ? *unordered_any(type_demands) : nullptr;
}

static bool any_outside_range(const UnorderedSet<const IRInstruction*>& insns,
                              int64_t min,
                              int64_t max) {
  return unordered_any_of(insns, [min, max](const IRInstruction* insn) {
    const auto literal = insn->get_literal();
    return literal < min || literal > max;
  });
}

template <class T>
static bool any_outside(const UnorderedSet<const IRInstruction*>& insns) {
  return any_outside_range(insns, std::numeric_limits<T>::min(),
                           std::numeric_limits<T>::max());
}

size_t OutlinerTypeAnalysis::get_load_param_index(
    const IRInstruction* load_param_insn) {
  always_assert(opcode::is_a_load_param(load_param_insn->opcode()));
  auto& cfg = m_method->get_code()->cfg();
  auto param_insns = cfg.get_param_instructions();
  auto it = std::find_if(param_insns.begin(), param_insns.end(),
                         [load_param_insn](MethodItemEntry& mie) {
                           return mie.insn == load_param_insn;
                         });
  always_assert(it != param_insns.end());
  return std::distance(param_insns.begin(), it);
}

const DexType* OutlinerTypeAnalysis::get_result_type_helper(
    const IRInstruction* insn) {
  switch (insn->opcode()) {
  case OPCODE_CONST:
  case OPCODE_CONST_WIDE:
  case OPCODE_AND_INT:
  case OPCODE_OR_INT:
  case OPCODE_XOR_INT:
  case OPCODE_AND_INT_LIT:
  case OPCODE_OR_INT_LIT:
  case OPCODE_XOR_INT_LIT:
  case IOPCODE_UNREACHABLE:
    // These (must) get a special handling by caller
    not_reached();

  case IOPCODE_MOVE_RESULT_PSEUDO:
  case OPCODE_MOVE_RESULT:
  case IOPCODE_MOVE_RESULT_PSEUDO_OBJECT:
  case OPCODE_MOVE_RESULT_OBJECT:
  case IOPCODE_MOVE_RESULT_PSEUDO_WIDE:
  case OPCODE_MOVE_RESULT_WIDE:
  case OPCODE_MOVE:
  case OPCODE_MOVE_WIDE:
  case OPCODE_MOVE_OBJECT:
    // Not supported here
    not_reached();

  case IOPCODE_LOAD_PARAM:
  case IOPCODE_LOAD_PARAM_OBJECT:
  case IOPCODE_LOAD_PARAM_WIDE: {
    auto arg_idx = get_load_param_index(insn);
    if (!is_static(m_method) && arg_idx-- == 0) {
      return m_method->get_class();
    }
    const auto* arg_types = m_method->get_proto()->get_args();
    return arg_types->at(arg_idx);
  }

  case OPCODE_FILL_ARRAY_DATA:
  case OPCODE_GOTO:
  case OPCODE_NOP:
  case OPCODE_RETURN_VOID:
  case OPCODE_RETURN:
  case OPCODE_RETURN_WIDE:
  case OPCODE_RETURN_OBJECT:
  case OPCODE_MONITOR_ENTER:
  case OPCODE_MONITOR_EXIT:
  case OPCODE_IF_EQ:
  case OPCODE_IF_NE:
  case OPCODE_IF_EQZ:
  case OPCODE_IF_NEZ:
  case OPCODE_IF_LTZ:
  case OPCODE_IF_GEZ:
  case OPCODE_IF_GTZ:
  case OPCODE_IF_LEZ:
  case OPCODE_IF_LT:
  case OPCODE_IF_GE:
  case OPCODE_IF_GT:
  case OPCODE_IF_LE:
  case OPCODE_SWITCH:
  case OPCODE_APUT:
  case OPCODE_APUT_BOOLEAN:
  case OPCODE_APUT_BYTE:
  case OPCODE_APUT_CHAR:
  case OPCODE_APUT_SHORT:
  case OPCODE_APUT_WIDE:
  case OPCODE_APUT_OBJECT:
  case OPCODE_IPUT:
  case OPCODE_IPUT_BOOLEAN:
  case OPCODE_IPUT_BYTE:
  case OPCODE_IPUT_CHAR:
  case OPCODE_IPUT_SHORT:
  case OPCODE_IPUT_WIDE:
  case OPCODE_IPUT_OBJECT:
  case OPCODE_SPUT:
  case OPCODE_SPUT_BOOLEAN:
  case OPCODE_SPUT_BYTE:
  case OPCODE_SPUT_CHAR:
  case OPCODE_SPUT_SHORT:
  case OPCODE_SPUT_WIDE:
  case OPCODE_SPUT_OBJECT:
  case OPCODE_THROW:
  case IOPCODE_INIT_CLASS:
  case IOPCODE_INJECTION_ID:
  case IOPCODE_WRITE_BARRIER:
    not_reached();

  case OPCODE_MOVE_EXCEPTION:
    return type::java_lang_Throwable();

  case OPCODE_NEG_INT:
  case OPCODE_NOT_INT:
  case OPCODE_ADD_INT:
  case OPCODE_SUB_INT:
  case OPCODE_MUL_INT:
  case OPCODE_SHL_INT:
  case OPCODE_SHR_INT:
  case OPCODE_USHR_INT:
  case OPCODE_ADD_INT_LIT:
  case OPCODE_RSUB_INT_LIT:
  case OPCODE_MUL_INT_LIT:
  case OPCODE_SHL_INT_LIT:
  case OPCODE_SHR_INT_LIT:
  case OPCODE_USHR_INT_LIT:
  case OPCODE_FLOAT_TO_INT:
  case OPCODE_DOUBLE_TO_INT:
  case OPCODE_LONG_TO_INT:
  case IOPCODE_R_CONST:
    return type::_int();

  case OPCODE_INT_TO_BYTE:
    return type::_byte();
  case OPCODE_INT_TO_CHAR:
    return type::_char();
  case OPCODE_INT_TO_SHORT:
    return type::_short();
  case OPCODE_INT_TO_LONG:
  case OPCODE_FLOAT_TO_LONG:
  case OPCODE_DOUBLE_TO_LONG:
  case OPCODE_NEG_LONG:
  case OPCODE_NOT_LONG:
  case OPCODE_ADD_LONG:
  case OPCODE_SUB_LONG:
  case OPCODE_MUL_LONG:
  case OPCODE_AND_LONG:
  case OPCODE_OR_LONG:
  case OPCODE_XOR_LONG:
  case OPCODE_SHL_LONG:
  case OPCODE_SHR_LONG:
  case OPCODE_USHR_LONG:
    return type::_long();
  case OPCODE_INT_TO_FLOAT:
  case OPCODE_NEG_FLOAT:
  case OPCODE_ADD_FLOAT:
  case OPCODE_SUB_FLOAT:
  case OPCODE_MUL_FLOAT:
  case OPCODE_DIV_FLOAT:
  case OPCODE_REM_FLOAT:
  case OPCODE_DOUBLE_TO_FLOAT:
  case OPCODE_LONG_TO_FLOAT:
    return type::_float();
  case OPCODE_INT_TO_DOUBLE:
  case OPCODE_FLOAT_TO_DOUBLE:
  case OPCODE_NEG_DOUBLE:
  case OPCODE_ADD_DOUBLE:
  case OPCODE_SUB_DOUBLE:
  case OPCODE_MUL_DOUBLE:
  case OPCODE_DIV_DOUBLE:
  case OPCODE_REM_DOUBLE:
  case OPCODE_LONG_TO_DOUBLE:
    return type::_double();

  case OPCODE_CMPL_FLOAT:
  case OPCODE_CMPG_FLOAT:
  case OPCODE_CMPL_DOUBLE:
  case OPCODE_CMPG_DOUBLE:
  case OPCODE_CMP_LONG:
    return type::_int();

  case OPCODE_CONST_STRING:
    return type::java_lang_String();
  case OPCODE_CONST_CLASS:
    return type::java_lang_Class();
  case OPCODE_NEW_INSTANCE:
  case OPCODE_NEW_ARRAY:
  case OPCODE_FILLED_NEW_ARRAY:
  case OPCODE_CHECK_CAST:
    return insn->get_type();
  case OPCODE_SGET:
  case OPCODE_SGET_BOOLEAN:
  case OPCODE_SGET_BYTE:
  case OPCODE_SGET_CHAR:
  case OPCODE_SGET_SHORT:
  case OPCODE_SGET_WIDE:
  case OPCODE_SGET_OBJECT:
  case OPCODE_IGET:
  case OPCODE_IGET_BOOLEAN:
  case OPCODE_IGET_BYTE:
  case OPCODE_IGET_CHAR:
  case OPCODE_IGET_SHORT:
  case OPCODE_IGET_WIDE:
  case OPCODE_IGET_OBJECT:
    return insn->get_field()->get_type();
  case OPCODE_ARRAY_LENGTH:
    return type::_int();
  case OPCODE_INSTANCE_OF:
  case OPCODE_AGET_BOOLEAN:
    return type::_boolean();
  case OPCODE_AGET_BYTE:
    return type::_byte();
  case OPCODE_AGET_CHAR:
    return type::_char();
  case OPCODE_AGET_SHORT:
    return type::_short();
  case OPCODE_AGET:
  case OPCODE_AGET_WIDE:
  case OPCODE_AGET_OBJECT: {
    auto& env = m_type_environments->at(insn);
    auto dex_type = env.get_dex_type(insn->src(0));
    return (dex_type && type::is_array(*dex_type))
               ? type::get_array_component_type(*dex_type)
               : nullptr;
  }
  case OPCODE_INVOKE_VIRTUAL:
  case OPCODE_INVOKE_SUPER:
  case OPCODE_INVOKE_DIRECT:
  case OPCODE_INVOKE_STATIC:
  case OPCODE_INVOKE_INTERFACE:
    return insn->get_method()->get_proto()->get_rtype();

  case OPCODE_INVOKE_CUSTOM:
  case OPCODE_INVOKE_POLYMORPHIC:
  case OPCODE_CONST_METHOD_HANDLE:
  case OPCODE_CONST_METHOD_TYPE:
    not_reached_log(
        "Unsupported instruction {%s} in "
        "get_result_type_helper\n",
        SHOW(insn));

  case OPCODE_DIV_INT:
  case OPCODE_REM_INT:
  case OPCODE_DIV_INT_LIT:
  case OPCODE_REM_INT_LIT:
    return type::_int();
  case OPCODE_DIV_LONG:
  case OPCODE_REM_LONG:
    return type::_long();
  }
}

const DexType* OutlinerTypeAnalysis::get_type_of_reaching_defs(
    const CandidateAdapter& ca, reg_t reg) {
  auto defs = ca.get_rdef_env().get(reg);
  if (defs.is_bottom() || defs.is_top()) {
    return nullptr;
  }
  return get_type_of_defs(nullptr,
                          UnorderedSet<const IRInstruction*>(
                              defs.elements().begin(), defs.elements().end()),
                          /* optional_extra_type */ nullptr);
}

const DexType* OutlinerTypeAnalysis::get_if_insn_type_demand(
    IRInstruction* insn) {
  always_assert(opcode::is_a_conditional_branch(insn->opcode()));
  auto& env = m_type_environments->at(insn);
  for (size_t src_index = 0; src_index < insn->srcs_size(); src_index++) {
    auto t = env.get_type(insn->src(src_index));
    if (t.element() == IRType::REFERENCE) {
      return type::java_lang_Object();
    } else if (t.element() == IRType::FLOAT) {
      return type::_float();
    } else if (t.element() == IRType::INT) {
      return type::_int();
    }
  }
  return nullptr;
}

const DexType* OutlinerTypeAnalysis::get_type_demand(IRInstruction* insn,
                                                     size_t src_index) {
  always_assert(src_index < insn->srcs_size());
  switch (insn->opcode()) {
  case OPCODE_GOTO:
  case IOPCODE_LOAD_PARAM:
  case IOPCODE_LOAD_PARAM_OBJECT:
  case IOPCODE_LOAD_PARAM_WIDE:
  case OPCODE_NOP:
  case IOPCODE_MOVE_RESULT_PSEUDO:
  case OPCODE_MOVE_RESULT:
  case IOPCODE_MOVE_RESULT_PSEUDO_OBJECT:
  case OPCODE_MOVE_RESULT_OBJECT:
  case IOPCODE_MOVE_RESULT_PSEUDO_WIDE:
  case OPCODE_MOVE_RESULT_WIDE:
  case OPCODE_MOVE_EXCEPTION:
  case OPCODE_RETURN_VOID:
  case OPCODE_CONST:
  case OPCODE_CONST_WIDE:
  case OPCODE_CONST_STRING:
  case OPCODE_CONST_CLASS:
  case OPCODE_NEW_INSTANCE:
  case OPCODE_SGET:
  case OPCODE_SGET_BOOLEAN:
  case OPCODE_SGET_BYTE:
  case OPCODE_SGET_CHAR:
  case OPCODE_SGET_SHORT:
  case OPCODE_SGET_WIDE:
  case OPCODE_SGET_OBJECT:
  case IOPCODE_INIT_CLASS:
  case IOPCODE_INJECTION_ID:
  case IOPCODE_UNREACHABLE:
  case IOPCODE_WRITE_BARRIER:
    not_reached();

  case OPCODE_RETURN:
  case OPCODE_RETURN_WIDE:
  case OPCODE_RETURN_OBJECT:
    always_assert(src_index == 0);
    return m_method->get_proto()->get_rtype();

  case OPCODE_MOVE:
  case OPCODE_MOVE_WIDE:
  case OPCODE_MOVE_OBJECT:
    // Handled by caller
    not_reached();

  case OPCODE_MONITOR_ENTER:
  case OPCODE_MONITOR_EXIT:
  case OPCODE_CHECK_CAST:
  case OPCODE_INSTANCE_OF:
    always_assert(src_index == 0);
    return type::java_lang_Object();

  case OPCODE_ARRAY_LENGTH:
  case OPCODE_FILL_ARRAY_DATA: {
    always_assert(src_index == 0);
    auto& env = m_type_environments->at(insn);
    auto dex_type = env.get_dex_type(insn->src(0));
    return dex_type ? *dex_type : nullptr;
  }

  case OPCODE_THROW:
    always_assert(src_index == 0);
    return type::java_lang_Throwable();

  case OPCODE_IGET:
  case OPCODE_IGET_BOOLEAN:
  case OPCODE_IGET_BYTE:
  case OPCODE_IGET_CHAR:
  case OPCODE_IGET_SHORT:
  case OPCODE_IGET_WIDE:
  case OPCODE_IGET_OBJECT:
    always_assert(src_index == 0);
    return insn->get_field()->get_class();

  case OPCODE_IF_EQ:
  case OPCODE_IF_NE:
    always_assert(src_index < 2);
    // Could be int or object
    return get_if_insn_type_demand(insn);

  case OPCODE_IF_EQZ:
  case OPCODE_IF_NEZ:
  case OPCODE_IF_LTZ:
  case OPCODE_IF_GEZ:
  case OPCODE_IF_GTZ:
  case OPCODE_IF_LEZ:
    always_assert(src_index == 0);
    // Could be int or object
    return get_if_insn_type_demand(insn);

  case OPCODE_IF_LT:
  case OPCODE_IF_GE:
  case OPCODE_IF_GT:
  case OPCODE_IF_LE:
  case OPCODE_NEW_ARRAY:
  case OPCODE_SWITCH:
  case OPCODE_NEG_INT:
  case OPCODE_NOT_INT:
  case OPCODE_INT_TO_BYTE:
  case OPCODE_INT_TO_CHAR:
  case OPCODE_INT_TO_SHORT:
  case OPCODE_INT_TO_LONG:
  case OPCODE_INT_TO_FLOAT:
  case OPCODE_INT_TO_DOUBLE:
  case OPCODE_ADD_INT:
  case OPCODE_SUB_INT:
  case OPCODE_MUL_INT:
  case OPCODE_SHL_INT:
  case OPCODE_SHR_INT:
  case OPCODE_USHR_INT:
  case OPCODE_DIV_INT:
  case OPCODE_REM_INT:
  case OPCODE_ADD_INT_LIT:
  case OPCODE_RSUB_INT_LIT:
  case OPCODE_MUL_INT_LIT:
  case OPCODE_SHL_INT_LIT:
  case OPCODE_SHR_INT_LIT:
  case OPCODE_USHR_INT_LIT:
  case OPCODE_DIV_INT_LIT:
  case OPCODE_REM_INT_LIT:
    always_assert(src_index < 2);
    return type::_int();

  case OPCODE_AND_INT:
  case OPCODE_OR_INT:
  case OPCODE_XOR_INT:
  case OPCODE_AND_INT_LIT:
  case OPCODE_OR_INT_LIT:
  case OPCODE_XOR_INT_LIT:
    always_assert(src_index < 2);
    // Note: These opcodes can preserve boolean-ness. The caller of this
    // method needs to track that.
    return type::_int();

  case OPCODE_FILLED_NEW_ARRAY:
    return type::get_array_component_type(insn->get_type());

  case OPCODE_CMPL_FLOAT:
  case OPCODE_CMPG_FLOAT:
  case OPCODE_NEG_FLOAT:
  case OPCODE_FLOAT_TO_INT:
  case OPCODE_FLOAT_TO_LONG:
  case OPCODE_FLOAT_TO_DOUBLE:
  case OPCODE_ADD_FLOAT:
  case OPCODE_SUB_FLOAT:
  case OPCODE_MUL_FLOAT:
  case OPCODE_DIV_FLOAT:
  case OPCODE_REM_FLOAT:
    always_assert(src_index < 2);
    return type::_float();

  case OPCODE_CMPL_DOUBLE:
  case OPCODE_CMPG_DOUBLE:
  case OPCODE_NEG_DOUBLE:
  case OPCODE_DOUBLE_TO_INT:
  case OPCODE_DOUBLE_TO_LONG:
  case OPCODE_DOUBLE_TO_FLOAT:
  case OPCODE_ADD_DOUBLE:
  case OPCODE_SUB_DOUBLE:
  case OPCODE_MUL_DOUBLE:
  case OPCODE_DIV_DOUBLE:
  case OPCODE_REM_DOUBLE:
    always_assert(src_index < 2);
    return type::_double();

  case OPCODE_CMP_LONG:
  case OPCODE_NEG_LONG:
  case OPCODE_NOT_LONG:
  case OPCODE_LONG_TO_INT:
  case OPCODE_LONG_TO_FLOAT:
  case OPCODE_LONG_TO_DOUBLE:
  case OPCODE_ADD_LONG:
  case OPCODE_SUB_LONG:
  case OPCODE_MUL_LONG:
  case OPCODE_AND_LONG:
  case OPCODE_OR_LONG:
  case OPCODE_XOR_LONG:
  case OPCODE_DIV_LONG:
  case OPCODE_REM_LONG:
    always_assert(src_index < 2);
    return type::_long();

  case OPCODE_SHL_LONG:
  case OPCODE_SHR_LONG:
  case OPCODE_USHR_LONG:
    if (src_index == 0) {
      return type::_long();
    }
    always_assert(src_index == 1);
    return type::_int();

  case IOPCODE_R_CONST:
    return type::_int();

  case OPCODE_AGET:
  case OPCODE_AGET_BOOLEAN:
  case OPCODE_AGET_BYTE:
  case OPCODE_AGET_CHAR:
  case OPCODE_AGET_SHORT:
  case OPCODE_AGET_WIDE:
  case OPCODE_AGET_OBJECT:
    if (src_index == 0) {
      auto& env = m_type_environments->at(insn);
      auto dex_type = env.get_dex_type(insn->src(0));
      return dex_type ? *dex_type : nullptr;
    }
    always_assert(src_index == 1);
    return type::_int();

  case OPCODE_APUT:
  case OPCODE_APUT_BOOLEAN:
  case OPCODE_APUT_BYTE:
  case OPCODE_APUT_CHAR:
  case OPCODE_APUT_SHORT:
  case OPCODE_APUT_WIDE:
  case OPCODE_APUT_OBJECT:
    if (src_index == 1) {
      if (insn->opcode() == OPCODE_APUT_OBJECT) {
        return DexType::make_type("[Ljava/lang/Object;");
      }
      auto& env = m_type_environments->at(insn);
      auto dex_type = env.get_dex_type(insn->src(1));
      return dex_type ? *dex_type : nullptr;
    }
    if (src_index == 2) {
      return type::_int();
    }
    always_assert(src_index == 0);
    switch (insn->opcode()) {
    case OPCODE_APUT:
    case OPCODE_APUT_WIDE: {
      auto& env = m_type_environments->at(insn);
      auto dex_type = env.get_dex_type(insn->src(1));
      return (dex_type && type::is_array(*dex_type))
                 ? type::get_array_component_type(*dex_type)
                 : nullptr;
    }
    case OPCODE_APUT_BOOLEAN:
      return type::_boolean();
    case OPCODE_APUT_BYTE:
      return type::_byte();
    case OPCODE_APUT_CHAR:
      return type::_char();
    case OPCODE_APUT_SHORT:
      return type::_short();
    case OPCODE_APUT_OBJECT:
      // There seems to be very little static verification for this
      // instruction, as most is deferred to runtime.
      // https://android.googlesource.com/platform/dalvik/+/android-cts-4.4_r4/vm/analysis/CodeVerify.cpp#186
      // So, we can just get away with the following:
      return type::java_lang_Object();
    default:
      not_reached();
    }

  case OPCODE_IPUT:
  case OPCODE_IPUT_BOOLEAN:
  case OPCODE_IPUT_BYTE:
  case OPCODE_IPUT_CHAR:
  case OPCODE_IPUT_SHORT:
  case OPCODE_IPUT_WIDE:
  case OPCODE_IPUT_OBJECT:
    if (src_index == 1) {
      return insn->get_field()->get_class();
    }
    always_assert(src_index == 0);
    return insn->get_field()->get_type();

  case OPCODE_SPUT:
  case OPCODE_SPUT_BOOLEAN:
  case OPCODE_SPUT_BYTE:
  case OPCODE_SPUT_CHAR:
  case OPCODE_SPUT_SHORT:
  case OPCODE_SPUT_WIDE:
  case OPCODE_SPUT_OBJECT:
    always_assert(src_index == 0);
    return insn->get_field()->get_type();

  case OPCODE_INVOKE_VIRTUAL:
  case OPCODE_INVOKE_SUPER:
  case OPCODE_INVOKE_DIRECT:
  case OPCODE_INVOKE_STATIC:
  case OPCODE_INVOKE_INTERFACE: {
    DexMethodRef* dex_method = insn->get_method();
    const auto* arg_types = dex_method->get_proto()->get_args();
    size_t expected_args =
        (insn->opcode() != OPCODE_INVOKE_STATIC ? 1 : 0) + arg_types->size();
    always_assert(insn->srcs_size() == expected_args);

    if (insn->opcode() != OPCODE_INVOKE_STATIC) {
      // The first argument is a reference to the object instance on which the
      // method is invoked.
      if (src_index-- == 0) {
        return dex_method->get_class();
      }
    }
    return arg_types->at(src_index);
  }
  case OPCODE_INVOKE_CUSTOM:
  case OPCODE_INVOKE_POLYMORPHIC:
  case OPCODE_CONST_METHOD_HANDLE:
  case OPCODE_CONST_METHOD_TYPE:
    not_reached_log(
        "Unsupported instruction {%s} in "
        "get_type_demand\n",
        SHOW(insn));
  }
}

std::optional<UnorderedSet<const IRInstruction*>>
OutlinerTypeAnalysis::get_defs(
    const UnorderedSet<const IRInstruction*>& insns) {
  UnorderedSet<const IRInstruction*> res;
  for (const auto* insn : UnorderedIterable(insns)) {
    always_assert(insn->has_dest());
    if (opcode::is_a_move(insn->opcode()) ||
        opcode::is_move_result_any(insn->opcode())) {
      auto reg = insn->srcs_size() != 0u ? insn->src(0) : RESULT_REGISTER;
      auto defs = m_reaching_defs_environments->at(insn).get(reg);
      if (defs.is_bottom() || defs.is_top()) {
        return std::nullopt;
      }
      res.insert(defs.elements().begin(), defs.elements().end());
      continue;
    }
    res.insert(insn);
  }
  return res;
}

// Infer type demand imposed on an incoming register across all instructions
// in the given instruction sequence.
// The return value nullptr indicates that the demand could not be determined.
void OutlinerTypeAnalysis::get_type_demand_helper(
    const CandidateAdapter& ca,
    UnorderedSet<reg_t> regs_to_track,
    UnorderedSet<const DexType*>* type_demands) {
  auto follow = [](IRInstruction* insn, src_index_t) {
    switch (insn->opcode()) {
    case OPCODE_AND_INT:
    case OPCODE_OR_INT:
    case OPCODE_XOR_INT:
    case OPCODE_AND_INT_LIT:
    case OPCODE_OR_INT_LIT:
    case OPCODE_XOR_INT_LIT:
      return !insn->has_literal() || insn->get_literal() == 0 ||
             insn->get_literal() == 1;
    default:
      return false;
    }
  };
  ca.gather_type_demands(std::move(regs_to_track), follow, type_demands);
}

const DexType* OutlinerTypeAnalysis::get_const_insns_type_demand(
    const CandidateAdapter* ca,
    const UnorderedSet<const IRInstruction*>& const_insns) {
  always_assert(!const_insns.empty());
  // `get_type_of_defs` classifies `IOPCODE_UNREACHABLE` (a synthetic undefined
  // value) separately and never routes it here: it carries no literal, so both
  // the constant-uses analysis and the literal-range checks below would assert
  // on it. Only real `const`/`const-wide` defs reach this point.
  // 1. Let's see if we can get something out of the constant-uses analysis.
  constant_uses::TypeDemand type_demand{constant_uses::TypeDemand::None};
  for (const auto* insn : UnorderedIterable(const_insns)) {
    type_demand =
        (constant_uses::TypeDemand)(type_demand &
                                    m_constant_uses->get_constant_type_demand(
                                        const_cast<IRInstruction*>(insn)));
    if (type_demand == constant_uses::TypeDemand::Error) {
      return nullptr;
    }
  }
  if ((type_demand & constant_uses::TypeDemand::Object) != 0) {
    always_assert(unordered_none_of(const_insns, [](const IRInstruction* insn) {
      return insn->get_literal() != 0;
    }));
  } else if ((type_demand & constant_uses::TypeDemand::Long) != 0) {
    return type::_long();
  } else if ((type_demand & constant_uses::TypeDemand::Float) != 0) {
    return type::_float();
  } else if ((type_demand & constant_uses::TypeDemand::Double) != 0) {
    return type::_double();
  } else {
    always_assert(type_demand == constant_uses::TypeDemand::Int);
    if (!any_outside_range(const_insns, 0, 1)) {
      return type::_boolean();
    } else {
      auto not_short = any_outside<int16_t>(const_insns);
      auto not_char = any_outside<uint16_t>(const_insns);
      if (not_short && not_char) {
        return type::_int();
      } else if (not_short && !not_char) {
        return type::_char();
      } else if (!not_short && not_char) {
        return type::_short();
      }
    }
  }

  // No, so...
  // 2. Let's go over all constant-uses, and use our own judgement.
  UnorderedSet<const DexType*> type_demands;
  bool not_object{false};
  // Both scan all of `const_insns`, which does not change in the loop below, so
  // each is worth computing at most once. Lazily, because most opcodes reach
  // neither: an eager pair of scans would charge every caller for work the
  // switch below usually never asks for.
  Lazy<bool> any_outside_bit(
      [&const_insns] { return any_outside_range(const_insns, 0, 1); });
  Lazy<bool> any_outside_zero(
      [&const_insns] { return any_outside_range(const_insns, 0, 0); });
  for (const auto* insn : UnorderedIterable(const_insns)) {
    for (const auto& p :
         m_constant_uses->get_constant_uses(const_cast<IRInstruction*>(insn))) {
      if ((ca != nullptr) && ca->contains(p.first)) {
        continue;
      }
      switch (p.first->opcode()) {
      case OPCODE_AND_INT:
      case OPCODE_OR_INT:
      case OPCODE_XOR_INT:
      case OPCODE_AND_INT_LIT:
      case OPCODE_OR_INT_LIT:
      case OPCODE_XOR_INT_LIT:
        if (*any_outside_bit) {
          type_demands.insert(type::_int());
        } else {
          type_demands.insert(type::_boolean());
        }
        break;
      case OPCODE_MOVE:
        not_object = true;
        break;
      case OPCODE_MOVE_WIDE:
        break;
      case OPCODE_MOVE_OBJECT:
        type_demands.insert(type::java_lang_Object());
        break;
      case OPCODE_IF_EQ:
      case OPCODE_IF_NE:
      case OPCODE_IF_EQZ:
      case OPCODE_IF_NEZ:
      case OPCODE_IF_LTZ:
      case OPCODE_IF_GEZ:
      case OPCODE_IF_GTZ:
      case OPCODE_IF_LEZ:
        // Could be int or object
        if (*any_outside_zero) {
          type_demands.insert(type::_int());
          break;
        }
        [[fallthrough]];
      default:
        type_demands.insert(get_type_demand(p.first, p.second));
        break;
      }
    }
  }
  if (type_demands.empty()) {
    // A constant without (meaningful) use? Oh well. Dead code!
    return (*unordered_any(const_insns))->dest_is_wide() ? type::_long()
                                                         : type::_int();
  }
  const auto* narrowed_type_demand = narrow_type_demands(type_demands);
  if ((narrowed_type_demand != nullptr) &&
      type::is_object(narrowed_type_demand) && not_object) {
    return nullptr;
  }
  return narrowed_type_demand;
}

static const DexType* compute_joined_type(
    const UnorderedSet<const DexType*>& types) {
  std::optional<dtv_impl::DexTypeValue> joined_type_value;
  // `join_with` is neither associative nor commutative. When the common super
  // class walk reaches Object, `find_common_type` resolves through the
  // interfaces the operands share: sharing several incomparable ones is an
  // intersection type no DexType can hold, so it gives up to Top, and the
  // shared set is collected from the left operand only. Either one makes the
  // fold depend on the visit order. Fold in a stable type order.
  for (const auto* t : unordered_to_ordered(types, compare_dextypes)) {
    if (!type::is_object(t)) {
      return nullptr;
    }
    auto type_value = dtv_impl::DexTypeValue(t);
    if (joined_type_value) {
      if (joined_type_value->join_with(type_value) ==
          sparta::AbstractValueKind::Top) {
        return nullptr;
      }
      always_assert(joined_type_value->get_dex_type());
    } else {
      joined_type_value = type_value;
    }
  }
  return joined_type_value ? joined_type_value->get_dex_type() : nullptr;
}

// Compute the (widened) type of all given definitions.
const DexType* OutlinerTypeAnalysis::get_type_of_defs(
    const CandidateAdapter* ca,
    const UnorderedSet<const IRInstruction*>& defs,
    const DexType* optional_extra_type) {
  UnorderedSet<const DexType*> types;
  if (optional_extra_type != nullptr) {
    types.insert(optional_extra_type);
  }
  UnorderedSet<const IRInstruction*> const_insns;
  bool any_unreachable = false;
  for (const auto* def : UnorderedIterable(defs)) {
    always_assert(!opcode::is_a_move(def->opcode()) &&
                  !opcode::is_move_result_any(def->opcode()));
    UnorderedSet<const IRInstruction*> expanded_defs;
    UnorderedSet<const IRInstruction*> visited;
    // Helper function that expands bitwise operations that can preserve
    // booleanness. Returns true when we know result is type::_int()
    std::function<bool(const IRInstruction*)> expand;
    expand = [&](const IRInstruction* def) {
      if (!visited.insert(def).second) {
        return false;
      }
      switch (def->opcode()) {
      case OPCODE_AND_INT:
      case OPCODE_OR_INT:
      case OPCODE_XOR_INT:
      case OPCODE_AND_INT_LIT:
      case OPCODE_OR_INT_LIT:
      case OPCODE_XOR_INT_LIT:
        if (def->has_literal() && def->get_literal() != 0 &&
            def->get_literal() != 1) {
          // Overall result cannot be a boolean (as far as the Android type
          // checker is concerned), so it must be an int.
          return true;
        }
        for (auto src : def->srcs()) {
          auto inner_defs = m_reaching_defs_environments->at(def).get(src);
          for (auto* inner_def : inner_defs.elements()) {
            if (expand(inner_def)) {
              return true;
            }
          }
        }
        return false;
      case IOPCODE_UNREACHABLE:
        // A synthetic undefined value carries no literal and no type demand.
        // Keep it out of `const_insns`: the constant-uses analysis and the
        // literal-range checks (`any_outside*`) below both call
        // `get_literal()`, which asserts on it. Its only effect is that, if
        // nothing else contributes a type, the result is undeterminable
        // (handled below where `types` is empty).
        any_unreachable = true;
        return false;
      case OPCODE_CONST:
      case OPCODE_CONST_WIDE:
        const_insns.insert(def);
        return false;
      default:
        expanded_defs.insert(def);
        return false;
      }
    };
    if (expand(def)) {
      return type::_int();
    }
    for (const auto* inner_def : UnorderedIterable(expanded_defs)) {
      const DexType* t = get_result_type_helper(inner_def);
      types.insert(t);
    }
  }
  // TODO: Figure out a most general way of doing this.
  // In practice, the following special cases seem to most of what matters.

  if (types.count(nullptr) != 0u) {
    return nullptr;
  }

  if (types.empty()) {
    if (const_insns.empty()) {
      // Only undefined (unreachable) defs contributed; with no real const or
      // typed producer, the type is undeterminable.
      always_assert(any_unreachable);
      return nullptr;
    }
    return get_const_insns_type_demand(ca, const_insns);
  }

  // Stricter primitive types can be removed
  if (types.count(type::_int()) != 0u) {
    types.erase(type::_boolean());
    types.erase(type::_byte());
    types.erase(type::_short());
    types.erase(type::_char());
  } else {
    if (types.count(type::_short()) != 0u) {
      types.erase(type::_boolean());
      types.erase(type::_byte());
    }
    if ((types.count(type::_byte()) != 0u) ||
        (types.count(type::_char()) != 0u)) {
      types.erase(type::_boolean());
    }
    // Widen primitive types
    if ((types.count(type::_char()) != 0u) &&
        ((types.count(type::_byte()) != 0u) ||
         (types.count(type::_short()) != 0u))) {
      types.erase(type::_byte());
      types.erase(type::_short());
      types.erase(type::_char());
      types.insert(type::_int());
    }
  }

  // remove more specific object types
  unordered_erase_if(types, [&types](auto* u) {
    return type::is_object(u) && unordered_any_of(types, [u](const DexType* t) {
             return t != u && type::is_object(t) && type::check_cast(u, t);
           });
  });

  if (types.size() > 1) {
    // TODO: Consider folding the above attempts to reduce the types set
    // into DexTypeValue.
    return compute_joined_type(types);
  }
  if (types.empty()) {
    return nullptr;
  }
  always_assert(types.size() == 1);

  // Give up when we have an incompatible constant.
  // TODO: Do some careful widening.
  const auto* defs_type = *unordered_any(types);
  if ((defs_type == type::_short() && any_outside<int16_t>(const_insns)) ||
      (defs_type == type::_byte() && any_outside<int8_t>(const_insns)) ||
      (defs_type == type::_char() && any_outside<uint16_t>(const_insns)) ||
      (defs_type == type::_boolean() && any_outside_range(const_insns, 0, 1))) {
    return nullptr;
  }
  return defs_type;
}

} // namespace outliner_impl
