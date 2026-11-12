/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

/**
 * Background:
 *
 * Code contains many seemingly redundant const-instructions.
 * However, the Android verifier checks how const
 * values are used, and it will reject code that uses the same register
 * inconsistently along any execution path, where inconsistently means that the
 * register is used with conflicting type categories, e.g. once as an int, and
 * then again as a float. At a high level, the Android verifier considers three
 * type categories for <=32-bit values: int, float, object. All smaller integer
 * types are "implicitly" widened to int. And for 64-bit values, there is long,
 * double. Some instruction impose exact type demands, e.g. ADD_INT demands an
 * int, not a float, and not an object. But IF_EQZ can be given an int or an
 * object.
 *
 * In the actual Android verifier implementation, the exact tracked types are
 * much more involved, considering all relevant smaller integer types and their
 * relationships. See here:
 * https://android.googlesource.com/platform/dalvik/+/android-cts-4.4_r4/vm/analysis/CodeVerify.cpp#186
 * However, all that complexity in the Verifier exists to ensure that a value is
 * never used in a context where certain bits should be 0 or 1. We can ignore
 * these details for constants, as a constant is a constant is a constant.
 *
 * Our approach:
 *
 * If we have two const instructions loading the same bit patterns, we can drop
 * one if they don't have mismatching type demands along all execution paths. To
 * avoid doing a potentially expensive path-sensitive analysis for each pair of
 * const instructions, this diff applies one major simplification to the
 * problem: For each const instruction, we look at all type demands across all
 * execution paths, and compute the intersection of all these demands. In this
 * way, if two const instructions have the same combined type demands, then it
 * is safe to eliminate one of them. This is quite conservative, but safe.
 *
 * Note that the combined type demands might be contradictory (represented as
 * TypeDemand::Error). Consider the following instructions: const r0, 1234
 *   if-eqz r1, L1
 *   add-int r0, r0, r0
 *   goto L2
 *   :L1
 *   add-float r0, r0, r0
 *   :L2
 *
 * My understanding is that this is verifiable, as there is no inconsistent
 * feasible execution path. However, the path-insensitive combined type demand
 * for r0 is inconsistent, and thus r0 will not be considered for elimination.
 * This is the most extreme aspect of how this approach to the problem is safe.
 *
 * A few details on how type demands are computed:
 * - For return and return-wide instructions, we look at the method result type.
 * - For the the value passed in to an aput or aput-wide we try to determine the
 *   incoming array type using TypeInference. (I am not sure if TypeInference
 *   can always decide the array type, due to some simplifications that might
 *   exist in our type inference implementation. The Android verifier certainly
 *   is able to always figure out the exact array type if the code verifies.
 *   Anyway, if in doubt, we can always safely bail out with TypeDemand::Error)
 */

#include "ConstantUses.h"
#include "Debug.h"
#include "OptionalIO.h"
#include "ReachingDefinitions.h"
#include "Show.h"
#include "Trace.h"

namespace constant_uses {

ConstantUses::ConstantUses(const cfg::ControlFlowGraph& cfg,
                           DexMethod* method,
                           bool force_type_inference)
    : ConstantUses(
          cfg,
          method != nullptr ? is_static(method) : true,
          method != nullptr ? method->get_class() : nullptr,
          method != nullptr ? method->get_proto()->get_rtype() : nullptr,
          method != nullptr ? method->get_proto()->get_args() : nullptr,
          [method]() { return show(method); },
          force_type_inference) {}

ConstantUses::ConstantUses(const cfg::ControlFlowGraph& cfg,
                           bool is_static,
                           DexType* declaring_type,
                           DexType* rtype,
                           DexTypeList* args,
                           const std::function<std::string()>& method_describer,
                           bool force_type_inference)
    : m_rtype(rtype) {
  static AccumulatingTimer s_timer("ConstantUses::ConstantUses");
  auto t = s_timer.scope();

  always_assert(!force_type_inference || args);
  auto is_const = [](auto* insn) {
    return insn->opcode() == OPCODE_CONST ||
           insn->opcode() == OPCODE_CONST_WIDE;
  };
  reaching_defs::MoveAwareFixpointIterator reaching_definitions(cfg, is_const);
  reaching_definitions.run(reaching_defs::Environment());

  bool need_type_inference = false;
  for (cfg::Block* block : cfg.blocks()) {
    auto env = reaching_definitions.get_entry_state_at(block);
    for (auto& mie : InstructionIterable(block)) {
      IRInstruction* insn = mie.insn;
      for (size_t src_index = 0; src_index < insn->srcs_size(); src_index++) {
        auto src = insn->src(src_index);
        const auto& defs = env.get(src);
        if (!defs.is_top() && !defs.is_bottom()) {
          for (auto* def : defs.elements()) {
            always_assert(is_const(def));
            m_constant_uses[def].emplace_back(insn, src_index);
            // So there's an instruction that uses a const value.
            // For some uses, get_type_demand(IRInstruction*, size_t) will
            // need to know type inference information on operands.
            // The following switch logic needs to be kept in sync with that
            // actual usage of type inference information.
            auto opcode = insn->opcode();
            switch (opcode) {
            case OPCODE_APUT:
            case OPCODE_APUT_WIDE:
              if (src_index == 0) {
                need_type_inference = true;
              }
              break;
            case OPCODE_IF_EQ:
            case OPCODE_IF_NE:
            case OPCODE_IF_EQZ:
            case OPCODE_IF_NEZ:
              need_type_inference = true;
              break;
            default:
              break;
            }
          }
        }
      }
      reaching_definitions.analyze_instruction(insn, &env);
    }
  }

  TRACE(CU, 2, "[CU] ConstantUses(%s) need_type_inference:%d",
        method_describer().c_str(), need_type_inference);
  if ((need_type_inference && (args != nullptr)) || force_type_inference) {
    m_type_inference.reset(new type_inference::TypeInference(cfg));
    m_type_inference->run(is_static, declaring_type, args);
  }
}

const std::vector<std::pair<IRInstruction*, size_t>>&
ConstantUses::get_constant_uses(IRInstruction* insn) const {
  always_assert(insn->opcode() == OPCODE_CONST ||
                insn->opcode() == OPCODE_CONST_WIDE);
  auto it = m_constant_uses.find(insn);
  return it != m_constant_uses.end() ? it->second : m_no_uses;
}

TypeDemand ConstantUses::get_constant_type_demand(IRInstruction* insn) const {
  always_assert(insn->opcode() == OPCODE_CONST ||
                insn->opcode() == OPCODE_CONST_WIDE);
  TypeDemand type_demand = TypeDemand::None;
  for (const auto& p : get_constant_uses(insn)) {
    type_demand =
        (TypeDemand)(type_demand & get_type_demand(p.first, p.second));
    if (type_demand == TypeDemand::Error) {
      break;
    }
  }
  TRACE(CU, 4, "[CU] type demand of {%s}: %u (%s %s %s %s %s)", SHOW(insn),
        type_demand, type_demand & Int ? "Int" : "",
        type_demand & Float ? "Float" : "",
        type_demand & Object ? "Object" : "", type_demand & Long ? "Long" : "",
        type_demand & Double ? "Double" : "");
  if (insn->get_literal() != 0) {
    type_demand = (TypeDemand)(type_demand & ~TypeDemand::Object);
  }
  return type_demand;
}

TypeDemand ConstantUses::get_type_demand(const DexType* type) {
  switch (type->c_str()[0]) {
  case 'V':
    not_reached();

  case 'B':
  case 'C':
  case 'S':
  case 'I':
  case 'Z':
    return TypeDemand::Int;

  case 'J':
    return TypeDemand::Long;

  case 'F':
    return TypeDemand::Float;

  case 'D':
    return TypeDemand::Double;

  default:
    return TypeDemand::Object;
  }
}

static bool is_non_zero_int(IRType type) {
  return type == IRType::SCALAR || type == IRType::INT || type == IRType::CONST;
}

TypeDemand ConstantUses::get_type_demand(IRInstruction* insn,
                                         size_t src_index) const {
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
  case IOPCODE_R_CONST:
  case IOPCODE_INIT_CLASS:
  case IOPCODE_INJECTION_ID:
  case IOPCODE_UNREACHABLE:
  case IOPCODE_WRITE_BARRIER:
    not_reached();

  case OPCODE_RETURN:
  case OPCODE_RETURN_WIDE:
    return m_rtype != nullptr ? get_type_demand(m_rtype) : TypeDemand::Error;

  case OPCODE_MOVE:
    return TypeDemand::IntOrFloat;

  case OPCODE_MOVE_WIDE:
    return TypeDemand::LongOrDouble;

  case OPCODE_MOVE_OBJECT:
  case OPCODE_RETURN_OBJECT:
  case OPCODE_MONITOR_ENTER:
  case OPCODE_MONITOR_EXIT:
  case OPCODE_ARRAY_LENGTH:
  case OPCODE_FILL_ARRAY_DATA:
  case OPCODE_THROW:
  case OPCODE_IGET:
  case OPCODE_IGET_BOOLEAN:
  case OPCODE_IGET_BYTE:
  case OPCODE_IGET_CHAR:
  case OPCODE_IGET_SHORT:
  case OPCODE_IGET_WIDE:
  case OPCODE_IGET_OBJECT:
    return TypeDemand::Object;

  case OPCODE_CHECK_CAST:
    // In the Android verifier, the check-cast instruction updates the assumed
    // exact type on the incoming register, even in the case of a zero constant.
    // We don't track exact types here, and just bail out.
  case OPCODE_INSTANCE_OF:
    // The Android verifier in some ART versions match a pattern of
    // instance-of + ifXXX, and then may strengthen assumptions on the incoming
    // register, even in the case of a zero constant.
    // https://android.googlesource.com/platform/art/+/refs/tags/android-10.0.0_r5/runtime/verifier/method_verifier.cc#2683
    // We don't track exact types here, and certainly don't want to deal with
    // somewhat fragile pattern matching, and so just bail out.
    return TypeDemand::Error;

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
  case OPCODE_AND_INT:
  case OPCODE_OR_INT:
  case OPCODE_XOR_INT:
  case OPCODE_SHL_INT:
  case OPCODE_SHR_INT:
  case OPCODE_USHR_INT:
  case OPCODE_DIV_INT:
  case OPCODE_REM_INT:
  case OPCODE_ADD_INT_LIT:
  case OPCODE_RSUB_INT_LIT:
  case OPCODE_MUL_INT_LIT:
  case OPCODE_AND_INT_LIT:
  case OPCODE_OR_INT_LIT:
  case OPCODE_XOR_INT_LIT:
  case OPCODE_SHL_INT_LIT:
  case OPCODE_SHR_INT_LIT:
  case OPCODE_USHR_INT_LIT:
  case OPCODE_DIV_INT_LIT:
  case OPCODE_REM_INT_LIT:
    return TypeDemand::Int;

  case OPCODE_FILLED_NEW_ARRAY: {
    DexType* component_type = type::make_array_component_type(insn->get_type());
    return get_type_demand(component_type);
  }
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
    return TypeDemand::Float;

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
    return TypeDemand::Double;

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
    return TypeDemand::Long;

  case OPCODE_SHL_LONG:
  case OPCODE_SHR_LONG:
  case OPCODE_USHR_LONG:
    if (src_index == 0) {
      return TypeDemand::Long;
    }
    always_assert(src_index == 1);
    return TypeDemand::Int;

  case OPCODE_IF_EQ:
  case OPCODE_IF_NE:
    if (m_type_inference) {
      auto& type_environments = m_type_inference->get_type_environments();
      auto& type_environment = type_environments.at(insn);
      auto t1 = type_environment.get_type(insn->src(0));
      auto t2 = type_environment.get_type(insn->src(1));
      if (!t1.is_top() && !t1.is_bottom() && !t2.is_top() && !t2.is_bottom()) {
        if (t1.element() == IRType::REFERENCE ||
            t2.element() == IRType::REFERENCE) {
          return TypeDemand::Object;
        }
        if (is_non_zero_int(t1.element()) || is_non_zero_int(t2.element())) {
          return TypeDemand::Int;
        }
        return TypeDemand::IntOrObject;
      }
    } else {
      TRACE(CU, 3,
            "[CU] if-eq or if-ne instruction encountered {%s}, but type "
            "inference is unavailable",
            SHOW(insn));
    }
    return TypeDemand::Error;

  case OPCODE_IF_EQZ:
  case OPCODE_IF_NEZ:
    if (m_type_inference) {
      auto& type_environments = m_type_inference->get_type_environments();
      auto& type_environment = type_environments.at(insn);
      auto t = type_environment.get_type(insn->src(0));
      if (!t.is_top() && !t.is_bottom()) {
        if (t.element() == IRType::REFERENCE) {
          return TypeDemand::Object;
        }
        if (is_non_zero_int(t.element())) {
          return TypeDemand::Int;
        }
        return TypeDemand::IntOrObject;
      }
    } else {
      TRACE(CU, 3,
            "[CU] if-eqz or if-nez instruction encountered {%s}, but type "
            "inference is unavailable",
            SHOW(insn));
    }
    return TypeDemand::Error;

  case OPCODE_IF_LTZ:
  case OPCODE_IF_GEZ:
  case OPCODE_IF_GTZ:
  case OPCODE_IF_LEZ:
    return TypeDemand::IntOrObject;

  case OPCODE_IF_LT:
  case OPCODE_IF_GE:
  case OPCODE_IF_GT:
  case OPCODE_IF_LE:
    return TypeDemand::Int;

  case OPCODE_AGET:
  case OPCODE_AGET_BOOLEAN:
  case OPCODE_AGET_BYTE:
  case OPCODE_AGET_CHAR:
  case OPCODE_AGET_SHORT:
  case OPCODE_AGET_WIDE:
  case OPCODE_AGET_OBJECT:
    if (src_index == 0) {
      return TypeDemand::Object;
    }
    always_assert(src_index == 1);
    return TypeDemand::Int;

  case OPCODE_APUT:
  case OPCODE_APUT_BOOLEAN:
  case OPCODE_APUT_BYTE:
  case OPCODE_APUT_CHAR:
  case OPCODE_APUT_SHORT:
  case OPCODE_APUT_WIDE:
  case OPCODE_APUT_OBJECT:
    if (src_index == 1) {
      return TypeDemand::Object;
    }
    if (src_index == 2) {
      return TypeDemand::Int;
    }
    always_assert(src_index == 0);
    switch (insn->opcode()) {
    case OPCODE_APUT:
    case OPCODE_APUT_WIDE: {
      if (m_type_inference) {
        auto& type_environments = m_type_inference->get_type_environments();
        auto& type_environment = type_environments.at(insn);
        auto dex_type = type_environment.get_dex_type(insn->src(1));
        TRACE(CU, 3, "[CU] aput(-wide) instruction array type: %s",
              dex_type ? SHOW(dex_type) : "(unknown dex type)");
        if (dex_type && type::is_array(*dex_type)) {
          auto type_demand =
              get_type_demand(type::make_array_component_type(*dex_type));
          always_assert(insn->opcode() != OPCODE_APUT ||
                        (type_demand == TypeDemand::Error ||
                         type_demand == TypeDemand::Int ||
                         type_demand == TypeDemand::Float));
          always_assert(insn->opcode() != OPCODE_APUT_WIDE ||
                        (type_demand == TypeDemand::Error ||
                         type_demand == TypeDemand::Long ||
                         type_demand == TypeDemand::Double));
          return type_demand;
        }
      } else {
        TRACE(CU, 3,
              "[CU] aput(-wide) instruction encountered {%s}, but type "
              "inference is unavailable",
              SHOW(insn));
      }
      return TypeDemand::Error;
    }
    case OPCODE_APUT_BOOLEAN:
    case OPCODE_APUT_BYTE:
    case OPCODE_APUT_CHAR:
    case OPCODE_APUT_SHORT:
      return TypeDemand::Int;
    case OPCODE_APUT_OBJECT:
      return TypeDemand::Object;
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
      return TypeDemand::Object;
    }
    always_assert(src_index == 0);
    return get_type_demand(insn->get_field()->get_type());

  case OPCODE_SPUT:
  case OPCODE_SPUT_BOOLEAN:
  case OPCODE_SPUT_BYTE:
  case OPCODE_SPUT_CHAR:
  case OPCODE_SPUT_SHORT:
  case OPCODE_SPUT_WIDE:
  case OPCODE_SPUT_OBJECT:
    return get_type_demand(insn->get_field()->get_type());

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
        return TypeDemand::Object;
      }
    }
    return get_type_demand(arg_types->at(src_index));
  }
  case OPCODE_INVOKE_CUSTOM:
  case OPCODE_INVOKE_POLYMORPHIC:
  case OPCODE_CONST_METHOD_HANDLE:
  case OPCODE_CONST_METHOD_TYPE:
    not_reached_log(
        "Unsupported instruction {%s} in ConstantUses::get_type_demand\n",
        SHOW(insn));
  }
}

bool ConstantUses::has_type_inference() const { return !!m_type_inference; }

} // namespace constant_uses
