/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "EnumAnalyzeGeneratedMethods.h"

#include <array>

#include "Debug.h"
#include "Resolver.h"
#include "Show.h"
#include "Trace.h"

using namespace optimize_enums;

size_t EnumAnalyzeGeneratedMethods::transform_code(const Scope& scope) {

  walk::parallel::code(scope, [this](DexMethod* method, IRCode& code) {
    // Do not analyze the generated methods we are trying to remove.
    if (is_enum_valueof(method) || is_enum_values(method)) {
      return;
    }

    auto env = EnumFixpointIterator::gen_env(method);
    EnumFixpointIterator engine(code.cfg(), m_config);
    engine.run(env);

    process_method(engine, code.cfg(), method);
  });

  size_t num_removed_methods = 0;
  for (const auto* candidate_method : UnorderedIterable(m_candidate_methods)) {
    const DexType* candidate_type = candidate_method->get_class();
    if (m_candidate_types.count_unsafe(candidate_type) != 0u) {
      DexClass* candidate_class = type_class(candidate_type);
      always_assert(candidate_class);
      TRACE(ENUM, 4, "safe to remove method %s from %s", SHOW(candidate_method),
            SHOW(candidate_class));
      candidate_class->remove_method(candidate_method);
      num_removed_methods++;
    }
  }

  return num_removed_methods;
}

void EnumAnalyzeGeneratedMethods::process_method(
    const EnumFixpointIterator& engine,
    const cfg::ControlFlowGraph& cfg,
    const DexMethod* method) {
  for (const auto& block : cfg.blocks()) {
    EnumTypeEnvironment env = engine.get_entry_state_at(block);
    if (env.is_bottom()) {
      continue;
    }
    for (const auto& mie : InstructionIterable(block)) {
      engine.analyze_instruction(mie.insn, &env);
      process_instruction(mie.insn, &env, method);
    }
  }
}

/**
 * Rejects all enums that try to use its class type and all enums that are
 * upcasted and escape a method. This can happen by returning an upcasted enum
 * or by assigning it to some field or array.
 */
void EnumAnalyzeGeneratedMethods::process_instruction(
    const IRInstruction* insn,
    const EnumTypeEnvironment* env,
    const DexMethod* method) {
  switch (insn->opcode()) {
  case OPCODE_INVOKE_VIRTUAL:
  case OPCODE_INVOKE_SUPER:
  case OPCODE_INVOKE_DIRECT:
  case OPCODE_INVOKE_STATIC:
  case OPCODE_INVOKE_INTERFACE:
    process_invocation(insn, env);
    break;
  case OPCODE_CHECK_CAST:
  case OPCODE_CONST_CLASS: {
    const auto* type = type::make_element_type_if_array(insn->get_type());
    if (m_candidate_types.count(type) != 0u) {
      TRACE(ENUM, 4, "reject enum %s for using class type", SHOW(type));
      m_candidate_types.erase(type);
    }
  } break;
  case OPCODE_FILLED_NEW_ARRAY: {
    auto* base_type = type::make_array_element_type(insn->get_type());
    always_assert(base_type);
    for (size_t src_id = 1; src_id < insn->srcs_size(); src_id++) {
      const EnumTypes elem_types = env->get(insn->src(src_id));
      reject_if_unsafe(base_type, elem_types, insn);
    }
  } break;
  case OPCODE_APUT_OBJECT: {
    const EnumTypes elem_types = env->get(insn->src(0));
    const EnumTypes array_types = env->get(insn->src(1));
    for (const DexType* escaping_type : array_types.elements()) {
      const auto* base_escaping_type =
          type::make_element_type_if_array(escaping_type);
      reject_if_unsafe(base_escaping_type, elem_types, insn);
    }
  } break;
  case OPCODE_IPUT_OBJECT:
  case OPCODE_SPUT_OBJECT: {
    const auto* type =
        type::make_element_type_if_array(insn->get_field()->get_type());
    reject_if_unsafe(type, env->get(insn->src(0)), insn);
  } break;
  case OPCODE_RETURN_OBJECT: {
    const auto* return_type =
        type::make_element_type_if_array(method->get_proto()->get_rtype());
    reject_if_unsafe(return_type, env->get(insn->src(0)), insn);
  } break;
  default:
    break;
  }
}

/**
 * We reject an enum method if it is invoked. We also reject enums if invokes
 * the method `Enum.getDeclaringClass()` or a method whose arguments would
 * upcast that enum.
 */
void EnumAnalyzeGeneratedMethods::process_invocation(
    const IRInstruction* insn, const EnumTypeEnvironment* env) {
  auto* callee_ref = insn->get_method();
  auto* callee_class = callee_ref->get_class();
  auto* proto = callee_ref->get_proto();

  /**
   * A list of common enum methods that may upcast arguments, but cannot lead
   * to a call to `Enum.valueOf()` or `Enum.values()` directly or reflectively
   * because they are safe and final.
   */
  static const std::array allowlisted_methods{
      DexMethod::get_method("Ljava/lang/Enum;.<init>:(Ljava/lang/String;I)V"),
      DexMethod::get_method("Ljava/lang/Enum;.compareTo:(Ljava/lang/Enum;)I"),
      DexMethod::get_method("Ljava/lang/Enum;.equals:(Ljava/lang/Object;)Z"),
      DexMethod::get_method("Ljava/lang/Enum;.hashCode:()I"),
      DexMethod::get_method("Ljava/lang/Enum;.name:()Ljava/lang/String;"),
      DexMethod::get_method("Ljava/lang/Enum;.ordinal:()I"),
      DexMethod::get_method("Ljava/lang/Enum;.toString:()Ljava/lang/String;"),
  };

  if ((m_candidate_types.count(callee_class) != 0u) ||
      type::java_lang_Enum() == callee_class ||
      type::java_lang_Object() == callee_class) {
    for (const auto* allowlisted_method : allowlisted_methods) {
      if (method::signatures_match(callee_ref, allowlisted_method)) {
        TRACE(ENUM, 9, "Skipping allowed invocation %s", SHOW(insn));
        return;
      }
    }
  }

  // `param_id` is the id of the parameter in the callee prototype
  size_t param_id = 0;
  // `arg_id` is the id of the argument in the invocation
  size_t arg_id = 0;
  if (insn->opcode() != OPCODE_INVOKE_STATIC) {
    // The first argument is the `this` pointer.
    reject_if_unsafe(callee_ref->get_class(), env->get(insn->src(arg_id)),
                     insn);
    arg_id++;
  }
  const DexTypeList* parameters = proto->get_args();
  while (param_id < parameters->size()) {
    const EnumTypes possible_types = env->get(insn->src(arg_id));
    reject_if_unsafe(type::make_element_type_if_array(parameters->at(param_id)),
                     possible_types, insn);
    param_id++;
    arg_id++;
  }

  switch (insn->opcode()) {
  case OPCODE_INVOKE_VIRTUAL: {
    const DexMethodRef* get_declaring_class_method = DexMethod::get_method(
        "Ljava/lang/Enum;.getDeclaringClass:()Ljava/lang/Class;");
    const DexMethodRef* get_class_method = DexMethod::get_method(
        "Ljava/lang/Object;.getClass:()Ljava/lang/Class;");
    if (method::signatures_match(callee_ref, get_declaring_class_method) ||
        method::signatures_match(callee_ref, get_class_method)) {
      const EnumTypes possible_types = env->get(insn->src(0));
      for (const DexType* type : possible_types.elements()) {
        if (m_candidate_types.count(type) != 0u) {
          TRACE(ENUM, 4, "reject enum %s for using class type", SHOW(type));
          m_candidate_types.erase(type);
        }
      }
    }
  } break;
  case OPCODE_INVOKE_STATIC: {
    auto* callee = resolve_method_deprecated(callee_ref, MethodSearch::Static);
    if (m_candidate_methods.count(callee) != 0u) {
      if (is_enum_valueof(callee)) {
        // Enum.valueOf() calls Enum.values() and so we reject the whole type
        DexType* callee_type = callee->get_class();
        TRACE(ENUM, 4, "reject enum %s for calling valueOf", SHOW(callee_type));
        m_candidate_types.erase(callee_type);
      } else { // `SubEnum.values()`
        TRACE(ENUM, 4, "reject generated enum method %s", SHOW(callee));
        m_candidate_methods.erase(callee);
      }
    }
  } break;
  default:
    break;
  }
}

void EnumAnalyzeGeneratedMethods::reject_if_unsafe(
    const DexType* expected_type,
    const EnumTypes& possible_types,
    const IRInstruction* insn) {
  for (const DexType* possible_type : possible_types.elements()) {
    const auto* type = type::make_element_type_if_array(possible_type);
    if (expected_type != type && (m_candidate_types.count(type) != 0u)) {
      TRACE(ENUM, 4, "reject enum %s for upcasting to %s in %s", SHOW(type),
            SHOW(expected_type), SHOW(insn));
      m_candidate_types.erase(type);
    }
  }
}
