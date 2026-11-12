/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "RegisterType.h"

#include "Debug.h"
#include "Show.h"
#include "TypeUtil.h"

namespace regalloc {

namespace register_type_impl {

/*
 *             UNKNOWN
 *              /    \
 *            ZERO   WIDE
 *           /    \     |
 *       OBJECT NORMAL  |
 *          \     |    /
 *           \    |   /
 *            CONFLICT
 */
Lattice lattice({RegisterType::CONFLICT, RegisterType::ZERO,
                 RegisterType::NORMAL, RegisterType::WIDE, RegisterType::OBJECT,
                 RegisterType::UNKNOWN},
                {{RegisterType::CONFLICT, RegisterType::OBJECT},
                 {RegisterType::CONFLICT, RegisterType::NORMAL},
                 {RegisterType::CONFLICT, RegisterType::WIDE},
                 {RegisterType::OBJECT, RegisterType::ZERO},
                 {RegisterType::NORMAL, RegisterType::ZERO},
                 {RegisterType::ZERO, RegisterType::UNKNOWN},
                 {RegisterType::WIDE, RegisterType::UNKNOWN}});

} // namespace register_type_impl

static IROpcode move_op_for_type(RegisterType type) {
  switch (type) {
  case RegisterType::ZERO:
  case RegisterType::NORMAL:
    return OPCODE_MOVE;
  case RegisterType::OBJECT:
    return OPCODE_MOVE_OBJECT;
  case RegisterType::WIDE:
    return OPCODE_MOVE_WIDE;
  case RegisterType::UNKNOWN:
  case RegisterType::CONFLICT:
    not_reached_log("Cannot generate move for register type %s", SHOW(type));
  case RegisterType::SIZE:
    not_reached();
  }
  not_reached();
}

IRInstruction* gen_move(RegisterType type, vreg_t dest, vreg_t src) {
  auto* insn = new IRInstruction(move_op_for_type(type));
  insn->set_dest(dest);
  insn->set_src(0, src);
  return insn;
}

static RegisterType const_dest_type(const IRInstruction* insn) {
  if (insn->get_literal() == 0) {
    return RegisterType::ZERO;
  } else {
    return RegisterType::NORMAL;
  }
}

RegisterType dest_reg_type(const IRInstruction* insn) {
  auto op = insn->opcode();
  switch (op) {
  case OPCODE_NOP:
    not_reached_log("No dest");
  case OPCODE_MOVE:
    return RegisterType::NORMAL;
  case OPCODE_MOVE_WIDE:
    return RegisterType::WIDE;
  case OPCODE_MOVE_OBJECT:
    return RegisterType::OBJECT;
  case OPCODE_MOVE_RESULT:
    return RegisterType::NORMAL;
  case OPCODE_MOVE_RESULT_WIDE:
    return RegisterType::WIDE;
  case OPCODE_MOVE_RESULT_OBJECT:
  case OPCODE_MOVE_EXCEPTION:
    return RegisterType::OBJECT;
  case OPCODE_RETURN_VOID:
  case OPCODE_RETURN:
  case OPCODE_RETURN_WIDE:
  case OPCODE_RETURN_OBJECT:
    not_reached_log("No dest");
  case OPCODE_MONITOR_ENTER:
  case OPCODE_MONITOR_EXIT:
  case OPCODE_THROW:
  case OPCODE_GOTO:
    not_reached_log("No dest");
  case OPCODE_NEG_INT:
  case OPCODE_NOT_INT:
    return RegisterType::NORMAL;
  case OPCODE_NEG_LONG:
  case OPCODE_NOT_LONG:
    return RegisterType::WIDE;
  case OPCODE_NEG_FLOAT:
    return RegisterType::NORMAL;
  case OPCODE_NEG_DOUBLE:
  case OPCODE_INT_TO_LONG:
    return RegisterType::WIDE;
  case OPCODE_INT_TO_FLOAT:
    return RegisterType::NORMAL;
  case OPCODE_INT_TO_DOUBLE:
    return RegisterType::WIDE;
  case OPCODE_LONG_TO_INT:
  case OPCODE_LONG_TO_FLOAT:
    return RegisterType::NORMAL;
  case OPCODE_LONG_TO_DOUBLE:
    return RegisterType::WIDE;
  case OPCODE_FLOAT_TO_INT:
    return RegisterType::NORMAL;
  case OPCODE_FLOAT_TO_LONG:
  case OPCODE_FLOAT_TO_DOUBLE:
    return RegisterType::WIDE;
  case OPCODE_DOUBLE_TO_INT:
    return RegisterType::NORMAL;
  case OPCODE_DOUBLE_TO_LONG:
    return RegisterType::WIDE;
  case OPCODE_DOUBLE_TO_FLOAT:
  case OPCODE_INT_TO_BYTE:
  case OPCODE_INT_TO_CHAR:
  case OPCODE_INT_TO_SHORT:
  case OPCODE_ARRAY_LENGTH:
  case OPCODE_CMPL_FLOAT:
  case OPCODE_CMPG_FLOAT:
  case OPCODE_CMPL_DOUBLE:
  case OPCODE_CMPG_DOUBLE:
  case OPCODE_CMP_LONG:
    return RegisterType::NORMAL;
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
  case OPCODE_IF_LEZ:
    not_reached_log("No dest");
  case OPCODE_AGET:
    return RegisterType::NORMAL;
  case OPCODE_AGET_WIDE:
    return RegisterType::WIDE;
  case OPCODE_AGET_OBJECT:
    return RegisterType::OBJECT;
  case OPCODE_AGET_BOOLEAN:
  case OPCODE_AGET_BYTE:
  case OPCODE_AGET_CHAR:
  case OPCODE_AGET_SHORT:
    return RegisterType::NORMAL;
  case OPCODE_APUT:
  case OPCODE_APUT_WIDE:
  case OPCODE_APUT_OBJECT:
  case OPCODE_APUT_BOOLEAN:
  case OPCODE_APUT_BYTE:
  case OPCODE_APUT_CHAR:
  case OPCODE_APUT_SHORT:
    not_reached_log("No dest");
  case OPCODE_ADD_INT:
  case OPCODE_SUB_INT:
  case OPCODE_MUL_INT:
  case OPCODE_DIV_INT:
  case OPCODE_REM_INT:
  case OPCODE_AND_INT:
  case OPCODE_OR_INT:
  case OPCODE_XOR_INT:
  case OPCODE_SHL_INT:
  case OPCODE_SHR_INT:
  case OPCODE_USHR_INT:
    return RegisterType::NORMAL;
  case OPCODE_ADD_LONG:
  case OPCODE_SUB_LONG:
  case OPCODE_MUL_LONG:
  case OPCODE_DIV_LONG:
  case OPCODE_REM_LONG:
  case OPCODE_AND_LONG:
  case OPCODE_OR_LONG:
  case OPCODE_XOR_LONG:
  case OPCODE_SHL_LONG:
  case OPCODE_SHR_LONG:
  case OPCODE_USHR_LONG:
    return RegisterType::WIDE;
  case OPCODE_ADD_FLOAT:
  case OPCODE_SUB_FLOAT:
  case OPCODE_MUL_FLOAT:
  case OPCODE_DIV_FLOAT:
  case OPCODE_REM_FLOAT:
    return RegisterType::NORMAL;
  case OPCODE_ADD_DOUBLE:
  case OPCODE_SUB_DOUBLE:
  case OPCODE_MUL_DOUBLE:
  case OPCODE_DIV_DOUBLE:
  case OPCODE_REM_DOUBLE:
    return RegisterType::WIDE;
  case OPCODE_ADD_INT_LIT:
  case OPCODE_RSUB_INT_LIT:
  case OPCODE_MUL_INT_LIT:
  case OPCODE_DIV_INT_LIT:
  case OPCODE_REM_INT_LIT:
  case OPCODE_AND_INT_LIT:
  case OPCODE_OR_INT_LIT:
  case OPCODE_XOR_INT_LIT:
  case OPCODE_SHL_INT_LIT:
  case OPCODE_SHR_INT_LIT:
  case OPCODE_USHR_INT_LIT:
    return RegisterType::NORMAL;
  case IOPCODE_R_CONST:
  case OPCODE_CONST:
    return const_dest_type(insn);
  case OPCODE_FILL_ARRAY_DATA:
  case OPCODE_SWITCH:
    not_reached_log("No dest");
  case OPCODE_CONST_WIDE:
    return RegisterType::WIDE;
  case OPCODE_IGET:
    return RegisterType::NORMAL;
  case OPCODE_IGET_WIDE:
    return RegisterType::WIDE;
  case OPCODE_IGET_OBJECT:
    return RegisterType::OBJECT;
  case OPCODE_IGET_BOOLEAN:
  case OPCODE_IGET_BYTE:
  case OPCODE_IGET_CHAR:
  case OPCODE_IGET_SHORT:
    return RegisterType::NORMAL;
  case OPCODE_IPUT:
  case OPCODE_IPUT_WIDE:
  case OPCODE_IPUT_OBJECT:
  case OPCODE_IPUT_BOOLEAN:
  case OPCODE_IPUT_BYTE:
  case OPCODE_IPUT_CHAR:
  case OPCODE_IPUT_SHORT:
    not_reached_log("No dest");
  case OPCODE_SGET:
    return RegisterType::NORMAL;
  case OPCODE_SGET_WIDE:
    return RegisterType::WIDE;
  case OPCODE_SGET_OBJECT:
    return RegisterType::OBJECT;
  case OPCODE_SGET_BOOLEAN:
  case OPCODE_SGET_BYTE:
  case OPCODE_SGET_CHAR:
  case OPCODE_SGET_SHORT:
    return RegisterType::NORMAL;
  case OPCODE_SPUT:
  case OPCODE_SPUT_WIDE:
  case OPCODE_SPUT_OBJECT:
  case OPCODE_SPUT_BOOLEAN:
  case OPCODE_SPUT_BYTE:
  case OPCODE_SPUT_CHAR:
  case OPCODE_SPUT_SHORT:
    not_reached_log("No dest");
  case OPCODE_INVOKE_VIRTUAL:
  case OPCODE_INVOKE_SUPER:
  case OPCODE_INVOKE_DIRECT:
  case OPCODE_INVOKE_STATIC:
  case OPCODE_INVOKE_INTERFACE:
  case OPCODE_INVOKE_CUSTOM:
  case OPCODE_INVOKE_POLYMORPHIC:
    not_reached_log("No dest");
  case OPCODE_CONST_STRING:
  case OPCODE_CONST_CLASS:
  case OPCODE_CHECK_CAST:
    return RegisterType::OBJECT;
  case OPCODE_INSTANCE_OF:
    return RegisterType::NORMAL;
  case OPCODE_NEW_INSTANCE:
  case OPCODE_NEW_ARRAY:
  case OPCODE_FILLED_NEW_ARRAY:
  case OPCODE_CONST_METHOD_HANDLE:
  case OPCODE_CONST_METHOD_TYPE:
    return RegisterType::OBJECT;
  case IOPCODE_LOAD_PARAM:
    return RegisterType::NORMAL;
  case IOPCODE_LOAD_PARAM_OBJECT:
    return RegisterType::OBJECT;
  case IOPCODE_LOAD_PARAM_WIDE:
    return RegisterType::WIDE;
  case IOPCODE_MOVE_RESULT_PSEUDO:
    return RegisterType::NORMAL;
  case IOPCODE_MOVE_RESULT_PSEUDO_OBJECT:
    return RegisterType::OBJECT;
  case IOPCODE_MOVE_RESULT_PSEUDO_WIDE:
    return RegisterType::WIDE;
  case IOPCODE_UNREACHABLE:
    return RegisterType::ZERO;
  case IOPCODE_INJECTION_ID:
    return RegisterType::NORMAL;
  default:
    not_reached_log("Unknown opcode %02x\n", op);
  }
}

static RegisterType invoke_src_type(const IRInstruction* insn, vreg_t i) {
  auto* method = insn->get_method();
  // non-static invokes have an implicit `this` arg that is not reflected in
  // the method proto.
  //
  // TODO(T59333250): WHAT ABOUT invoke-custom and invoke-polymorphic
  if (insn->opcode() != OPCODE_INVOKE_CUSTOM &&
      insn->opcode() != OPCODE_INVOKE_POLYMORPHIC &&
      insn->opcode() != OPCODE_INVOKE_STATIC) {
    if (i == 0) {
      return RegisterType::OBJECT;
    } else {
      // decrement `i` by one so that we can use it as an index into the
      // argument type list.
      --i;
    }
  }
  const auto* types = method->get_proto()->get_args();
  always_assert_log(types->size() > i, "Invalid invoke insn %s\n", SHOW(insn));
  auto* type = types->at(i);
  if (type::is_wide_type(type)) {
    return RegisterType::WIDE;
  } else if (type::is_primitive(type)) {
    return RegisterType::NORMAL;
  } else {
    return RegisterType::OBJECT;
  }
}

RegisterType src_reg_type(const IRInstruction* insn, vreg_t i) {
  auto op = insn->opcode();
  switch (op) {
  case OPCODE_NOP:
    not_reached_log("No src");
  case OPCODE_MOVE:
    return RegisterType::NORMAL;
  case OPCODE_MOVE_WIDE:
    return RegisterType::WIDE;
  case OPCODE_MOVE_OBJECT:
    return RegisterType::OBJECT;
  case OPCODE_MOVE_RESULT:
  case OPCODE_MOVE_RESULT_WIDE:
  case OPCODE_MOVE_RESULT_OBJECT:
  case OPCODE_MOVE_EXCEPTION:
  case OPCODE_RETURN_VOID:
    not_reached_log("No src");
  case OPCODE_RETURN:
    return RegisterType::NORMAL;
  case OPCODE_RETURN_WIDE:
    return RegisterType::WIDE;
  case OPCODE_RETURN_OBJECT:
  case OPCODE_MONITOR_ENTER:
  case OPCODE_MONITOR_EXIT:
  case OPCODE_THROW:
    return RegisterType::OBJECT;
  case OPCODE_GOTO:
    not_reached_log("No src");
  case OPCODE_NEG_INT:
  case OPCODE_NOT_INT:
    return RegisterType::NORMAL;
  case OPCODE_NEG_LONG:
  case OPCODE_NOT_LONG:
    return RegisterType::WIDE;
  case OPCODE_NEG_FLOAT:
    return RegisterType::NORMAL;
  case OPCODE_NEG_DOUBLE:
    return RegisterType::WIDE;
  case OPCODE_INT_TO_LONG:
  case OPCODE_INT_TO_FLOAT:
  case OPCODE_INT_TO_DOUBLE:
    return RegisterType::NORMAL;
  case OPCODE_LONG_TO_INT:
  case OPCODE_LONG_TO_FLOAT:
  case OPCODE_LONG_TO_DOUBLE:
    return RegisterType::WIDE;
  case OPCODE_FLOAT_TO_INT:
  case OPCODE_FLOAT_TO_LONG:
  case OPCODE_FLOAT_TO_DOUBLE:
    return RegisterType::NORMAL;
  case OPCODE_DOUBLE_TO_INT:
  case OPCODE_DOUBLE_TO_LONG:
  case OPCODE_DOUBLE_TO_FLOAT:
    return RegisterType::WIDE;
  case OPCODE_INT_TO_BYTE:
  case OPCODE_INT_TO_CHAR:
  case OPCODE_INT_TO_SHORT:
    return RegisterType::NORMAL;
  case OPCODE_ARRAY_LENGTH:
    return RegisterType::OBJECT;
  case OPCODE_CMPL_FLOAT:
  case OPCODE_CMPG_FLOAT:
    return RegisterType::NORMAL;
  case OPCODE_CMPL_DOUBLE:
  case OPCODE_CMPG_DOUBLE:
  case OPCODE_CMP_LONG:
    return RegisterType::WIDE;
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
  case OPCODE_IF_LEZ:
    // can either be primitive or ref
    return RegisterType::UNKNOWN;
  case OPCODE_AGET:
  case OPCODE_AGET_WIDE:
  case OPCODE_AGET_OBJECT:
  case OPCODE_AGET_BOOLEAN:
  case OPCODE_AGET_BYTE:
  case OPCODE_AGET_CHAR:
  case OPCODE_AGET_SHORT:
    return i == 0 ? RegisterType::OBJECT : RegisterType::NORMAL;
  case OPCODE_APUT:
    return i == 1 ? RegisterType::OBJECT : RegisterType::NORMAL;
  case OPCODE_APUT_WIDE:
    return i == 1   ? RegisterType::OBJECT
           : i == 2 ? RegisterType::NORMAL
                    : RegisterType::WIDE;
  case OPCODE_APUT_OBJECT:
    return i <= 1 ? RegisterType::OBJECT : RegisterType::NORMAL;
  case OPCODE_APUT_BOOLEAN:
  case OPCODE_APUT_BYTE:
  case OPCODE_APUT_CHAR:
  case OPCODE_APUT_SHORT:
    return i == 1 ? RegisterType::OBJECT : RegisterType::NORMAL;
  case OPCODE_ADD_INT:
  case OPCODE_SUB_INT:
  case OPCODE_MUL_INT:
  case OPCODE_DIV_INT:
  case OPCODE_REM_INT:
  case OPCODE_AND_INT:
  case OPCODE_OR_INT:
  case OPCODE_XOR_INT:
  case OPCODE_SHL_INT:
  case OPCODE_SHR_INT:
  case OPCODE_USHR_INT:
    return RegisterType::NORMAL;
  case OPCODE_ADD_LONG:
  case OPCODE_SUB_LONG:
  case OPCODE_MUL_LONG:
  case OPCODE_DIV_LONG:
  case OPCODE_REM_LONG:
  case OPCODE_AND_LONG:
  case OPCODE_OR_LONG:
  case OPCODE_XOR_LONG:
    return RegisterType::WIDE;
  case OPCODE_SHL_LONG:
  case OPCODE_SHR_LONG:
  case OPCODE_USHR_LONG:
    return i == 0 ? RegisterType::WIDE : RegisterType::NORMAL;
  case OPCODE_ADD_FLOAT:
  case OPCODE_SUB_FLOAT:
  case OPCODE_MUL_FLOAT:
  case OPCODE_DIV_FLOAT:
  case OPCODE_REM_FLOAT:
    return RegisterType::NORMAL;
  case OPCODE_ADD_DOUBLE:
  case OPCODE_SUB_DOUBLE:
  case OPCODE_MUL_DOUBLE:
  case OPCODE_DIV_DOUBLE:
  case OPCODE_REM_DOUBLE:
    return RegisterType::WIDE;
  case OPCODE_ADD_INT_LIT:
  case OPCODE_RSUB_INT_LIT:
  case OPCODE_MUL_INT_LIT:
  case OPCODE_DIV_INT_LIT:
  case OPCODE_REM_INT_LIT:
  case OPCODE_AND_INT_LIT:
  case OPCODE_OR_INT_LIT:
  case OPCODE_XOR_INT_LIT:
  case OPCODE_SHL_INT_LIT:
  case OPCODE_SHR_INT_LIT:
  case OPCODE_USHR_INT_LIT:
    return RegisterType::NORMAL;
  case OPCODE_CONST:
    not_reached_log("No src");
  case OPCODE_FILL_ARRAY_DATA:
    return RegisterType::OBJECT;
  case OPCODE_SWITCH:
    return RegisterType::UNKNOWN;
  case OPCODE_CONST_WIDE:
    not_reached_log("No src");
  case OPCODE_IGET:
  case OPCODE_IGET_WIDE:
  case OPCODE_IGET_OBJECT:
  case OPCODE_IGET_BOOLEAN:
  case OPCODE_IGET_BYTE:
  case OPCODE_IGET_CHAR:
  case OPCODE_IGET_SHORT:
    always_assert(i == 0);
    return RegisterType::OBJECT;
  case OPCODE_IPUT:
    return i == 1 ? RegisterType::OBJECT : RegisterType::NORMAL;
  case OPCODE_IPUT_WIDE:
    return i == 1 ? RegisterType::OBJECT : RegisterType::WIDE;
  case OPCODE_IPUT_OBJECT:
    return RegisterType::OBJECT;
  case OPCODE_IPUT_BOOLEAN:
  case OPCODE_IPUT_BYTE:
  case OPCODE_IPUT_CHAR:
  case OPCODE_IPUT_SHORT:
    return i == 1 ? RegisterType::OBJECT : RegisterType::NORMAL;
  case OPCODE_SGET:
  case OPCODE_SGET_WIDE:
  case OPCODE_SGET_OBJECT:
  case OPCODE_SGET_BOOLEAN:
  case OPCODE_SGET_BYTE:
  case OPCODE_SGET_CHAR:
  case OPCODE_SGET_SHORT:
    not_reached_log("No src");
  case OPCODE_SPUT:
    return RegisterType::NORMAL;
  case OPCODE_SPUT_WIDE:
    return RegisterType::WIDE;
  case OPCODE_SPUT_OBJECT:
    return RegisterType::OBJECT;
  case OPCODE_SPUT_BOOLEAN:
  case OPCODE_SPUT_BYTE:
  case OPCODE_SPUT_CHAR:
  case OPCODE_SPUT_SHORT:
    return RegisterType::NORMAL;
  case OPCODE_INVOKE_VIRTUAL:
  case OPCODE_INVOKE_SUPER:
  case OPCODE_INVOKE_DIRECT:
  case OPCODE_INVOKE_STATIC:
  case OPCODE_INVOKE_INTERFACE:
  case OPCODE_INVOKE_CUSTOM:
  case OPCODE_INVOKE_POLYMORPHIC:
    return invoke_src_type(insn, i);
  case OPCODE_CONST_STRING:
  case OPCODE_CONST_CLASS:
    not_reached_log("No src");
  case OPCODE_CHECK_CAST:
  case OPCODE_INSTANCE_OF:
    return RegisterType::OBJECT;
  case OPCODE_NEW_INSTANCE:
    not_reached_log("No src");
  case OPCODE_NEW_ARRAY:
    return RegisterType::NORMAL;
  case OPCODE_FILLED_NEW_ARRAY:
    return type::is_primitive(type::make_array_component_type(insn->get_type()))
               ? RegisterType::NORMAL
               : RegisterType::OBJECT;
  case IOPCODE_LOAD_PARAM:
  case IOPCODE_LOAD_PARAM_OBJECT:
  case IOPCODE_LOAD_PARAM_WIDE:
    not_reached_log("No src");
  case IOPCODE_MOVE_RESULT_PSEUDO:
  case IOPCODE_MOVE_RESULT_PSEUDO_WIDE:
    not_reached_log("No src");
  default:
    not_reached_log("Unknown opcode %02x\n", op);
  }
}

} // namespace regalloc

using namespace regalloc;

std::string show(RegisterType type) {
  switch (type) {
  case RegisterType::NORMAL:
    return "NORMAL";
  case RegisterType::OBJECT:
    return "OBJECT";
  case RegisterType::WIDE:
    return "WIDE";
  case RegisterType::ZERO:
    return "ZERO";
  case RegisterType::UNKNOWN:
    return "UNKNOWN";
  case RegisterType::CONFLICT:
    return "CONFLICT";
  case RegisterType::SIZE:
    not_reached();
  }
  not_reached();
}
