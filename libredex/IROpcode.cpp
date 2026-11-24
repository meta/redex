/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "IROpcode.h"

#include "Debug.h"
#include "DexClass.h"
#include "DexOpcode.h"
#include "Show.h"
#include "TypeUtil.h"

std::ostream& operator<<(std::ostream& os, const IROpcode& op) {
  os << show(op);
  return os;
}

namespace opcode {

std::optional<IROpcode> from_dex_opcode(DexOpcode op) {
  switch (op) {
  case DOPCODE_NOP:
    return OPCODE_NOP;
  case DOPCODE_MOVE:
    return OPCODE_MOVE;
  case DOPCODE_MOVE_WIDE:
    return OPCODE_MOVE_WIDE;
  case DOPCODE_MOVE_OBJECT:
    return OPCODE_MOVE_OBJECT;
  case DOPCODE_MOVE_RESULT:
    return OPCODE_MOVE_RESULT;
  case DOPCODE_MOVE_RESULT_WIDE:
    return OPCODE_MOVE_RESULT_WIDE;
  case DOPCODE_MOVE_RESULT_OBJECT:
    return OPCODE_MOVE_RESULT_OBJECT;
  case DOPCODE_MOVE_EXCEPTION:
    return OPCODE_MOVE_EXCEPTION;
  case DOPCODE_RETURN_VOID:
    return OPCODE_RETURN_VOID;
  case DOPCODE_RETURN:
    return OPCODE_RETURN;
  case DOPCODE_RETURN_WIDE:
    return OPCODE_RETURN_WIDE;
  case DOPCODE_RETURN_OBJECT:
    return OPCODE_RETURN_OBJECT;
  case DOPCODE_CONST_4:
    return OPCODE_CONST;
  case DOPCODE_MONITOR_ENTER:
    return OPCODE_MONITOR_ENTER;
  case DOPCODE_MONITOR_EXIT:
    return OPCODE_MONITOR_EXIT;
  case DOPCODE_THROW:
    return OPCODE_THROW;
  case DOPCODE_GOTO:
    return OPCODE_GOTO;
  case DOPCODE_NEG_INT:
    return OPCODE_NEG_INT;
  case DOPCODE_NOT_INT:
    return OPCODE_NOT_INT;
  case DOPCODE_NEG_LONG:
    return OPCODE_NEG_LONG;
  case DOPCODE_NOT_LONG:
    return OPCODE_NOT_LONG;
  case DOPCODE_NEG_FLOAT:
    return OPCODE_NEG_FLOAT;
  case DOPCODE_NEG_DOUBLE:
    return OPCODE_NEG_DOUBLE;
  case DOPCODE_INT_TO_LONG:
    return OPCODE_INT_TO_LONG;
  case DOPCODE_INT_TO_FLOAT:
    return OPCODE_INT_TO_FLOAT;
  case DOPCODE_INT_TO_DOUBLE:
    return OPCODE_INT_TO_DOUBLE;
  case DOPCODE_LONG_TO_INT:
    return OPCODE_LONG_TO_INT;
  case DOPCODE_LONG_TO_FLOAT:
    return OPCODE_LONG_TO_FLOAT;
  case DOPCODE_LONG_TO_DOUBLE:
    return OPCODE_LONG_TO_DOUBLE;
  case DOPCODE_FLOAT_TO_INT:
    return OPCODE_FLOAT_TO_INT;
  case DOPCODE_FLOAT_TO_LONG:
    return OPCODE_FLOAT_TO_LONG;
  case DOPCODE_FLOAT_TO_DOUBLE:
    return OPCODE_FLOAT_TO_DOUBLE;
  case DOPCODE_DOUBLE_TO_INT:
    return OPCODE_DOUBLE_TO_INT;
  case DOPCODE_DOUBLE_TO_LONG:
    return OPCODE_DOUBLE_TO_LONG;
  case DOPCODE_DOUBLE_TO_FLOAT:
    return OPCODE_DOUBLE_TO_FLOAT;
  case DOPCODE_INT_TO_BYTE:
    return OPCODE_INT_TO_BYTE;
  case DOPCODE_INT_TO_CHAR:
    return OPCODE_INT_TO_CHAR;
  case DOPCODE_INT_TO_SHORT:
    return OPCODE_INT_TO_SHORT;
  case DOPCODE_ADD_INT_2ADDR:
    return OPCODE_ADD_INT;
  case DOPCODE_SUB_INT_2ADDR:
    return OPCODE_SUB_INT;
  case DOPCODE_MUL_INT_2ADDR:
    return OPCODE_MUL_INT;
  case DOPCODE_DIV_INT_2ADDR:
    return OPCODE_DIV_INT;
  case DOPCODE_REM_INT_2ADDR:
    return OPCODE_REM_INT;
  case DOPCODE_AND_INT_2ADDR:
    return OPCODE_AND_INT;
  case DOPCODE_OR_INT_2ADDR:
    return OPCODE_OR_INT;
  case DOPCODE_XOR_INT_2ADDR:
    return OPCODE_XOR_INT;
  case DOPCODE_SHL_INT_2ADDR:
    return OPCODE_SHL_INT;
  case DOPCODE_SHR_INT_2ADDR:
    return OPCODE_SHR_INT;
  case DOPCODE_USHR_INT_2ADDR:
    return OPCODE_USHR_INT;
  case DOPCODE_ADD_LONG_2ADDR:
    return OPCODE_ADD_LONG;
  case DOPCODE_SUB_LONG_2ADDR:
    return OPCODE_SUB_LONG;
  case DOPCODE_MUL_LONG_2ADDR:
    return OPCODE_MUL_LONG;
  case DOPCODE_DIV_LONG_2ADDR:
    return OPCODE_DIV_LONG;
  case DOPCODE_REM_LONG_2ADDR:
    return OPCODE_REM_LONG;
  case DOPCODE_AND_LONG_2ADDR:
    return OPCODE_AND_LONG;
  case DOPCODE_OR_LONG_2ADDR:
    return OPCODE_OR_LONG;
  case DOPCODE_XOR_LONG_2ADDR:
    return OPCODE_XOR_LONG;
  case DOPCODE_SHL_LONG_2ADDR:
    return OPCODE_SHL_LONG;
  case DOPCODE_SHR_LONG_2ADDR:
    return OPCODE_SHR_LONG;
  case DOPCODE_USHR_LONG_2ADDR:
    return OPCODE_USHR_LONG;
  case DOPCODE_ADD_FLOAT_2ADDR:
    return OPCODE_ADD_FLOAT;
  case DOPCODE_SUB_FLOAT_2ADDR:
    return OPCODE_SUB_FLOAT;
  case DOPCODE_MUL_FLOAT_2ADDR:
    return OPCODE_MUL_FLOAT;
  case DOPCODE_DIV_FLOAT_2ADDR:
    return OPCODE_DIV_FLOAT;
  case DOPCODE_REM_FLOAT_2ADDR:
    return OPCODE_REM_FLOAT;
  case DOPCODE_ADD_DOUBLE_2ADDR:
    return OPCODE_ADD_DOUBLE;
  case DOPCODE_SUB_DOUBLE_2ADDR:
    return OPCODE_SUB_DOUBLE;
  case DOPCODE_MUL_DOUBLE_2ADDR:
    return OPCODE_MUL_DOUBLE;
  case DOPCODE_DIV_DOUBLE_2ADDR:
    return OPCODE_DIV_DOUBLE;
  case DOPCODE_REM_DOUBLE_2ADDR:
    return OPCODE_REM_DOUBLE;
  case DOPCODE_ARRAY_LENGTH:
    return OPCODE_ARRAY_LENGTH;
  case DOPCODE_MOVE_FROM16:
    return OPCODE_MOVE;
  case DOPCODE_MOVE_WIDE_FROM16:
    return OPCODE_MOVE_WIDE;
  case DOPCODE_MOVE_OBJECT_FROM16:
    return OPCODE_MOVE_OBJECT;
  case DOPCODE_CONST_16:
    return OPCODE_CONST;
  case DOPCODE_CONST_HIGH16:
    return OPCODE_CONST;
  case DOPCODE_CONST_WIDE_16:
    return OPCODE_CONST_WIDE;
  case DOPCODE_CONST_WIDE_HIGH16:
    return OPCODE_CONST_WIDE;
  case DOPCODE_GOTO_16:
    return OPCODE_GOTO;
  case DOPCODE_CMPL_FLOAT:
    return OPCODE_CMPL_FLOAT;
  case DOPCODE_CMPG_FLOAT:
    return OPCODE_CMPG_FLOAT;
  case DOPCODE_CMPL_DOUBLE:
    return OPCODE_CMPL_DOUBLE;
  case DOPCODE_CMPG_DOUBLE:
    return OPCODE_CMPG_DOUBLE;
  case DOPCODE_CMP_LONG:
    return OPCODE_CMP_LONG;
  case DOPCODE_IF_EQ:
    return OPCODE_IF_EQ;
  case DOPCODE_IF_NE:
    return OPCODE_IF_NE;
  case DOPCODE_IF_LT:
    return OPCODE_IF_LT;
  case DOPCODE_IF_GE:
    return OPCODE_IF_GE;
  case DOPCODE_IF_GT:
    return OPCODE_IF_GT;
  case DOPCODE_IF_LE:
    return OPCODE_IF_LE;
  case DOPCODE_IF_EQZ:
    return OPCODE_IF_EQZ;
  case DOPCODE_IF_NEZ:
    return OPCODE_IF_NEZ;
  case DOPCODE_IF_LTZ:
    return OPCODE_IF_LTZ;
  case DOPCODE_IF_GEZ:
    return OPCODE_IF_GEZ;
  case DOPCODE_IF_GTZ:
    return OPCODE_IF_GTZ;
  case DOPCODE_IF_LEZ:
    return OPCODE_IF_LEZ;
  case DOPCODE_AGET:
    return OPCODE_AGET;
  case DOPCODE_AGET_WIDE:
    return OPCODE_AGET_WIDE;
  case DOPCODE_AGET_OBJECT:
    return OPCODE_AGET_OBJECT;
  case DOPCODE_AGET_BOOLEAN:
    return OPCODE_AGET_BOOLEAN;
  case DOPCODE_AGET_BYTE:
    return OPCODE_AGET_BYTE;
  case DOPCODE_AGET_CHAR:
    return OPCODE_AGET_CHAR;
  case DOPCODE_AGET_SHORT:
    return OPCODE_AGET_SHORT;
  case DOPCODE_APUT:
    return OPCODE_APUT;
  case DOPCODE_APUT_WIDE:
    return OPCODE_APUT_WIDE;
  case DOPCODE_APUT_OBJECT:
    return OPCODE_APUT_OBJECT;
  case DOPCODE_APUT_BOOLEAN:
    return OPCODE_APUT_BOOLEAN;
  case DOPCODE_APUT_BYTE:
    return OPCODE_APUT_BYTE;
  case DOPCODE_APUT_CHAR:
    return OPCODE_APUT_CHAR;
  case DOPCODE_APUT_SHORT:
    return OPCODE_APUT_SHORT;
  case DOPCODE_ADD_INT:
    return OPCODE_ADD_INT;
  case DOPCODE_SUB_INT:
    return OPCODE_SUB_INT;
  case DOPCODE_MUL_INT:
    return OPCODE_MUL_INT;
  case DOPCODE_DIV_INT:
    return OPCODE_DIV_INT;
  case DOPCODE_REM_INT:
    return OPCODE_REM_INT;
  case DOPCODE_AND_INT:
    return OPCODE_AND_INT;
  case DOPCODE_OR_INT:
    return OPCODE_OR_INT;
  case DOPCODE_XOR_INT:
    return OPCODE_XOR_INT;
  case DOPCODE_SHL_INT:
    return OPCODE_SHL_INT;
  case DOPCODE_SHR_INT:
    return OPCODE_SHR_INT;
  case DOPCODE_USHR_INT:
    return OPCODE_USHR_INT;
  case DOPCODE_ADD_LONG:
    return OPCODE_ADD_LONG;
  case DOPCODE_SUB_LONG:
    return OPCODE_SUB_LONG;
  case DOPCODE_MUL_LONG:
    return OPCODE_MUL_LONG;
  case DOPCODE_DIV_LONG:
    return OPCODE_DIV_LONG;
  case DOPCODE_REM_LONG:
    return OPCODE_REM_LONG;
  case DOPCODE_AND_LONG:
    return OPCODE_AND_LONG;
  case DOPCODE_OR_LONG:
    return OPCODE_OR_LONG;
  case DOPCODE_XOR_LONG:
    return OPCODE_XOR_LONG;
  case DOPCODE_SHL_LONG:
    return OPCODE_SHL_LONG;
  case DOPCODE_SHR_LONG:
    return OPCODE_SHR_LONG;
  case DOPCODE_USHR_LONG:
    return OPCODE_USHR_LONG;
  case DOPCODE_ADD_FLOAT:
    return OPCODE_ADD_FLOAT;
  case DOPCODE_SUB_FLOAT:
    return OPCODE_SUB_FLOAT;
  case DOPCODE_MUL_FLOAT:
    return OPCODE_MUL_FLOAT;
  case DOPCODE_DIV_FLOAT:
    return OPCODE_DIV_FLOAT;
  case DOPCODE_REM_FLOAT:
    return OPCODE_REM_FLOAT;
  case DOPCODE_ADD_DOUBLE:
    return OPCODE_ADD_DOUBLE;
  case DOPCODE_SUB_DOUBLE:
    return OPCODE_SUB_DOUBLE;
  case DOPCODE_MUL_DOUBLE:
    return OPCODE_MUL_DOUBLE;
  case DOPCODE_DIV_DOUBLE:
    return OPCODE_DIV_DOUBLE;
  case DOPCODE_REM_DOUBLE:
    return OPCODE_REM_DOUBLE;
  case DOPCODE_ADD_INT_LIT16:
    return OPCODE_ADD_INT_LIT;
  case DOPCODE_RSUB_INT:
    return OPCODE_RSUB_INT_LIT;
  case DOPCODE_MUL_INT_LIT16:
    return OPCODE_MUL_INT_LIT;
  case DOPCODE_DIV_INT_LIT16:
    return OPCODE_DIV_INT_LIT;
  case DOPCODE_REM_INT_LIT16:
    return OPCODE_REM_INT_LIT;
  case DOPCODE_AND_INT_LIT16:
    return OPCODE_AND_INT_LIT;
  case DOPCODE_OR_INT_LIT16:
    return OPCODE_OR_INT_LIT;
  case DOPCODE_XOR_INT_LIT16:
    return OPCODE_XOR_INT_LIT;
  case DOPCODE_ADD_INT_LIT8:
    return OPCODE_ADD_INT_LIT;
  case DOPCODE_RSUB_INT_LIT8:
    return OPCODE_RSUB_INT_LIT;
  case DOPCODE_MUL_INT_LIT8:
    return OPCODE_MUL_INT_LIT;
  case DOPCODE_DIV_INT_LIT8:
    return OPCODE_DIV_INT_LIT;
  case DOPCODE_REM_INT_LIT8:
    return OPCODE_REM_INT_LIT;
  case DOPCODE_AND_INT_LIT8:
    return OPCODE_AND_INT_LIT;
  case DOPCODE_OR_INT_LIT8:
    return OPCODE_OR_INT_LIT;
  case DOPCODE_XOR_INT_LIT8:
    return OPCODE_XOR_INT_LIT;
  case DOPCODE_SHL_INT_LIT8:
    return OPCODE_SHL_INT_LIT;
  case DOPCODE_SHR_INT_LIT8:
    return OPCODE_SHR_INT_LIT;
  case DOPCODE_USHR_INT_LIT8:
    return OPCODE_USHR_INT_LIT;
  case DOPCODE_MOVE_16:
    return OPCODE_MOVE;
  case DOPCODE_MOVE_WIDE_16:
    return OPCODE_MOVE_WIDE;
  case DOPCODE_MOVE_OBJECT_16:
    return OPCODE_MOVE_OBJECT;
  case DOPCODE_CONST:
    return OPCODE_CONST;
  case DOPCODE_CONST_WIDE_32:
    return OPCODE_CONST_WIDE;
  case DOPCODE_FILL_ARRAY_DATA:
    return OPCODE_FILL_ARRAY_DATA;
  case DOPCODE_GOTO_32:
    return OPCODE_GOTO;
  case DOPCODE_PACKED_SWITCH:
  case DOPCODE_SPARSE_SWITCH:
    return OPCODE_SWITCH;
  case DOPCODE_CONST_WIDE:
    return OPCODE_CONST_WIDE;
  case DOPCODE_IGET:
    return OPCODE_IGET;
  case DOPCODE_IGET_WIDE:
    return OPCODE_IGET_WIDE;
  case DOPCODE_IGET_OBJECT:
    return OPCODE_IGET_OBJECT;
  case DOPCODE_IGET_BOOLEAN:
    return OPCODE_IGET_BOOLEAN;
  case DOPCODE_IGET_BYTE:
    return OPCODE_IGET_BYTE;
  case DOPCODE_IGET_CHAR:
    return OPCODE_IGET_CHAR;
  case DOPCODE_IGET_SHORT:
    return OPCODE_IGET_SHORT;
  case DOPCODE_IPUT:
    return OPCODE_IPUT;
  case DOPCODE_IPUT_WIDE:
    return OPCODE_IPUT_WIDE;
  case DOPCODE_IPUT_OBJECT:
    return OPCODE_IPUT_OBJECT;
  case DOPCODE_IPUT_BOOLEAN:
    return OPCODE_IPUT_BOOLEAN;
  case DOPCODE_IPUT_BYTE:
    return OPCODE_IPUT_BYTE;
  case DOPCODE_IPUT_CHAR:
    return OPCODE_IPUT_CHAR;
  case DOPCODE_IPUT_SHORT:
    return OPCODE_IPUT_SHORT;
  case DOPCODE_SGET:
    return OPCODE_SGET;
  case DOPCODE_SGET_WIDE:
    return OPCODE_SGET_WIDE;
  case DOPCODE_SGET_OBJECT:
    return OPCODE_SGET_OBJECT;
  case DOPCODE_SGET_BOOLEAN:
    return OPCODE_SGET_BOOLEAN;
  case DOPCODE_SGET_BYTE:
    return OPCODE_SGET_BYTE;
  case DOPCODE_SGET_CHAR:
    return OPCODE_SGET_CHAR;
  case DOPCODE_SGET_SHORT:
    return OPCODE_SGET_SHORT;
  case DOPCODE_SPUT:
    return OPCODE_SPUT;
  case DOPCODE_SPUT_WIDE:
    return OPCODE_SPUT_WIDE;
  case DOPCODE_SPUT_OBJECT:
    return OPCODE_SPUT_OBJECT;
  case DOPCODE_SPUT_BOOLEAN:
    return OPCODE_SPUT_BOOLEAN;
  case DOPCODE_SPUT_BYTE:
    return OPCODE_SPUT_BYTE;
  case DOPCODE_SPUT_CHAR:
    return OPCODE_SPUT_CHAR;
  case DOPCODE_SPUT_SHORT:
    return OPCODE_SPUT_SHORT;
  case DOPCODE_INVOKE_VIRTUAL:
    return OPCODE_INVOKE_VIRTUAL;
  case DOPCODE_INVOKE_SUPER:
    return OPCODE_INVOKE_SUPER;
  case DOPCODE_INVOKE_DIRECT:
    return OPCODE_INVOKE_DIRECT;
  case DOPCODE_INVOKE_STATIC:
    return OPCODE_INVOKE_STATIC;
  case DOPCODE_INVOKE_INTERFACE:
    return OPCODE_INVOKE_INTERFACE;
  case DOPCODE_INVOKE_POLYMORPHIC:
    return OPCODE_INVOKE_POLYMORPHIC;
  case DOPCODE_INVOKE_CUSTOM:
    return OPCODE_INVOKE_CUSTOM;
  case DOPCODE_INVOKE_VIRTUAL_RANGE:
    return OPCODE_INVOKE_VIRTUAL;
  case DOPCODE_INVOKE_SUPER_RANGE:
    return OPCODE_INVOKE_SUPER;
  case DOPCODE_INVOKE_DIRECT_RANGE:
    return OPCODE_INVOKE_DIRECT;
  case DOPCODE_INVOKE_STATIC_RANGE:
    return OPCODE_INVOKE_STATIC;
  case DOPCODE_INVOKE_INTERFACE_RANGE:
    return OPCODE_INVOKE_INTERFACE;
  case DOPCODE_INVOKE_CUSTOM_RANGE:
    return OPCODE_INVOKE_CUSTOM;
  case DOPCODE_INVOKE_POLYMORPHIC_RANGE:
    return OPCODE_INVOKE_POLYMORPHIC;
  case DOPCODE_CONST_STRING:
  case DOPCODE_CONST_STRING_JUMBO:
    return OPCODE_CONST_STRING;
  case DOPCODE_CONST_CLASS:
    return OPCODE_CONST_CLASS;
  case DOPCODE_CHECK_CAST:
    return OPCODE_CHECK_CAST;
  case DOPCODE_INSTANCE_OF:
    return OPCODE_INSTANCE_OF;
  case DOPCODE_NEW_INSTANCE:
    return OPCODE_NEW_INSTANCE;
  case DOPCODE_NEW_ARRAY:
    return OPCODE_NEW_ARRAY;
  case DOPCODE_FILLED_NEW_ARRAY:
    return OPCODE_FILLED_NEW_ARRAY;
  case DOPCODE_FILLED_NEW_ARRAY_RANGE:
    return OPCODE_FILLED_NEW_ARRAY;
  case DOPCODE_CONST_METHOD_HANDLE:
    return OPCODE_CONST_METHOD_HANDLE;
  case DOPCODE_CONST_METHOD_TYPE:
    return OPCODE_CONST_METHOD_TYPE;
  case FOPCODE_PACKED_SWITCH:
  case FOPCODE_SPARSE_SWITCH:
  case FOPCODE_FILLED_ARRAY:
    return std::nullopt;
    // clang-format off
  SWITCH_FORMAT_QUICK_FIELD_REF {
    return std::nullopt;
  }
  SWITCH_FORMAT_QUICK_METHOD_REF {
    return std::nullopt;
  }
  SWITCH_FORMAT_RETURN_VOID_NO_BARRIER {
    return std::nullopt;
  }
    // clang-format on
  }
  return std::nullopt;
}

DexOpcode to_dex_opcode(IROpcode op) {
  switch (op) {
  case OPCODE_NOP:
    return DOPCODE_NOP;
  case OPCODE_MOVE:
    return DOPCODE_MOVE;
  case OPCODE_MOVE_WIDE:
    return DOPCODE_MOVE_WIDE;
  case OPCODE_MOVE_OBJECT:
    return DOPCODE_MOVE_OBJECT;
  case OPCODE_MOVE_RESULT:
    return DOPCODE_MOVE_RESULT;
  case OPCODE_MOVE_RESULT_WIDE:
    return DOPCODE_MOVE_RESULT_WIDE;
  case OPCODE_MOVE_RESULT_OBJECT:
    return DOPCODE_MOVE_RESULT_OBJECT;
  case OPCODE_MOVE_EXCEPTION:
    return DOPCODE_MOVE_EXCEPTION;
  case OPCODE_RETURN_VOID:
    return DOPCODE_RETURN_VOID;
  case OPCODE_RETURN:
    return DOPCODE_RETURN;
  case OPCODE_RETURN_WIDE:
    return DOPCODE_RETURN_WIDE;
  case OPCODE_RETURN_OBJECT:
    return DOPCODE_RETURN_OBJECT;
  case OPCODE_MONITOR_ENTER:
    return DOPCODE_MONITOR_ENTER;
  case OPCODE_MONITOR_EXIT:
    return DOPCODE_MONITOR_EXIT;
  case OPCODE_THROW:
    return DOPCODE_THROW;
  case OPCODE_GOTO:
    return DOPCODE_GOTO;
  case OPCODE_NEG_INT:
    return DOPCODE_NEG_INT;
  case OPCODE_NOT_INT:
    return DOPCODE_NOT_INT;
  case OPCODE_NEG_LONG:
    return DOPCODE_NEG_LONG;
  case OPCODE_NOT_LONG:
    return DOPCODE_NOT_LONG;
  case OPCODE_NEG_FLOAT:
    return DOPCODE_NEG_FLOAT;
  case OPCODE_NEG_DOUBLE:
    return DOPCODE_NEG_DOUBLE;
  case OPCODE_INT_TO_LONG:
    return DOPCODE_INT_TO_LONG;
  case OPCODE_INT_TO_FLOAT:
    return DOPCODE_INT_TO_FLOAT;
  case OPCODE_INT_TO_DOUBLE:
    return DOPCODE_INT_TO_DOUBLE;
  case OPCODE_LONG_TO_INT:
    return DOPCODE_LONG_TO_INT;
  case OPCODE_LONG_TO_FLOAT:
    return DOPCODE_LONG_TO_FLOAT;
  case OPCODE_LONG_TO_DOUBLE:
    return DOPCODE_LONG_TO_DOUBLE;
  case OPCODE_FLOAT_TO_INT:
    return DOPCODE_FLOAT_TO_INT;
  case OPCODE_FLOAT_TO_LONG:
    return DOPCODE_FLOAT_TO_LONG;
  case OPCODE_FLOAT_TO_DOUBLE:
    return DOPCODE_FLOAT_TO_DOUBLE;
  case OPCODE_DOUBLE_TO_INT:
    return DOPCODE_DOUBLE_TO_INT;
  case OPCODE_DOUBLE_TO_LONG:
    return DOPCODE_DOUBLE_TO_LONG;
  case OPCODE_DOUBLE_TO_FLOAT:
    return DOPCODE_DOUBLE_TO_FLOAT;
  case OPCODE_INT_TO_BYTE:
    return DOPCODE_INT_TO_BYTE;
  case OPCODE_INT_TO_CHAR:
    return DOPCODE_INT_TO_CHAR;
  case OPCODE_INT_TO_SHORT:
    return DOPCODE_INT_TO_SHORT;
  case OPCODE_ARRAY_LENGTH:
    return DOPCODE_ARRAY_LENGTH;
  case OPCODE_CMPL_FLOAT:
    return DOPCODE_CMPL_FLOAT;
  case OPCODE_CMPG_FLOAT:
    return DOPCODE_CMPG_FLOAT;
  case OPCODE_CMPL_DOUBLE:
    return DOPCODE_CMPL_DOUBLE;
  case OPCODE_CMPG_DOUBLE:
    return DOPCODE_CMPG_DOUBLE;
  case OPCODE_CMP_LONG:
    return DOPCODE_CMP_LONG;
  case OPCODE_IF_EQ:
    return DOPCODE_IF_EQ;
  case OPCODE_IF_NE:
    return DOPCODE_IF_NE;
  case OPCODE_IF_LT:
    return DOPCODE_IF_LT;
  case OPCODE_IF_GE:
    return DOPCODE_IF_GE;
  case OPCODE_IF_GT:
    return DOPCODE_IF_GT;
  case OPCODE_IF_LE:
    return DOPCODE_IF_LE;
  case OPCODE_IF_EQZ:
    return DOPCODE_IF_EQZ;
  case OPCODE_IF_NEZ:
    return DOPCODE_IF_NEZ;
  case OPCODE_IF_LTZ:
    return DOPCODE_IF_LTZ;
  case OPCODE_IF_GEZ:
    return DOPCODE_IF_GEZ;
  case OPCODE_IF_GTZ:
    return DOPCODE_IF_GTZ;
  case OPCODE_IF_LEZ:
    return DOPCODE_IF_LEZ;
  case OPCODE_AGET:
    return DOPCODE_AGET;
  case OPCODE_AGET_WIDE:
    return DOPCODE_AGET_WIDE;
  case OPCODE_AGET_OBJECT:
    return DOPCODE_AGET_OBJECT;
  case OPCODE_AGET_BOOLEAN:
    return DOPCODE_AGET_BOOLEAN;
  case OPCODE_AGET_BYTE:
    return DOPCODE_AGET_BYTE;
  case OPCODE_AGET_CHAR:
    return DOPCODE_AGET_CHAR;
  case OPCODE_AGET_SHORT:
    return DOPCODE_AGET_SHORT;
  case OPCODE_APUT:
    return DOPCODE_APUT;
  case OPCODE_APUT_WIDE:
    return DOPCODE_APUT_WIDE;
  case OPCODE_APUT_OBJECT:
    return DOPCODE_APUT_OBJECT;
  case OPCODE_APUT_BOOLEAN:
    return DOPCODE_APUT_BOOLEAN;
  case OPCODE_APUT_BYTE:
    return DOPCODE_APUT_BYTE;
  case OPCODE_APUT_CHAR:
    return DOPCODE_APUT_CHAR;
  case OPCODE_APUT_SHORT:
    return DOPCODE_APUT_SHORT;
  case OPCODE_ADD_INT:
    return DOPCODE_ADD_INT;
  case OPCODE_SUB_INT:
    return DOPCODE_SUB_INT;
  case OPCODE_MUL_INT:
    return DOPCODE_MUL_INT;
  case OPCODE_DIV_INT:
    return DOPCODE_DIV_INT;
  case OPCODE_REM_INT:
    return DOPCODE_REM_INT;
  case OPCODE_AND_INT:
    return DOPCODE_AND_INT;
  case OPCODE_OR_INT:
    return DOPCODE_OR_INT;
  case OPCODE_XOR_INT:
    return DOPCODE_XOR_INT;
  case OPCODE_SHL_INT:
    return DOPCODE_SHL_INT;
  case OPCODE_SHR_INT:
    return DOPCODE_SHR_INT;
  case OPCODE_USHR_INT:
    return DOPCODE_USHR_INT;
  case OPCODE_ADD_LONG:
    return DOPCODE_ADD_LONG;
  case OPCODE_SUB_LONG:
    return DOPCODE_SUB_LONG;
  case OPCODE_MUL_LONG:
    return DOPCODE_MUL_LONG;
  case OPCODE_DIV_LONG:
    return DOPCODE_DIV_LONG;
  case OPCODE_REM_LONG:
    return DOPCODE_REM_LONG;
  case OPCODE_AND_LONG:
    return DOPCODE_AND_LONG;
  case OPCODE_OR_LONG:
    return DOPCODE_OR_LONG;
  case OPCODE_XOR_LONG:
    return DOPCODE_XOR_LONG;
  case OPCODE_SHL_LONG:
    return DOPCODE_SHL_LONG;
  case OPCODE_SHR_LONG:
    return DOPCODE_SHR_LONG;
  case OPCODE_USHR_LONG:
    return DOPCODE_USHR_LONG;
  case OPCODE_ADD_FLOAT:
    return DOPCODE_ADD_FLOAT;
  case OPCODE_SUB_FLOAT:
    return DOPCODE_SUB_FLOAT;
  case OPCODE_MUL_FLOAT:
    return DOPCODE_MUL_FLOAT;
  case OPCODE_DIV_FLOAT:
    return DOPCODE_DIV_FLOAT;
  case OPCODE_REM_FLOAT:
    return DOPCODE_REM_FLOAT;
  case OPCODE_ADD_DOUBLE:
    return DOPCODE_ADD_DOUBLE;
  case OPCODE_SUB_DOUBLE:
    return DOPCODE_SUB_DOUBLE;
  case OPCODE_MUL_DOUBLE:
    return DOPCODE_MUL_DOUBLE;
  case OPCODE_DIV_DOUBLE:
    return DOPCODE_DIV_DOUBLE;
  case OPCODE_REM_DOUBLE:
    return DOPCODE_REM_DOUBLE;
  case OPCODE_ADD_INT_LIT:
    return DOPCODE_ADD_INT_LIT16;
  case OPCODE_RSUB_INT_LIT:
    return DOPCODE_RSUB_INT;
  case OPCODE_MUL_INT_LIT:
    return DOPCODE_MUL_INT_LIT16;
  case OPCODE_DIV_INT_LIT:
    return DOPCODE_DIV_INT_LIT16;
  case OPCODE_REM_INT_LIT:
    return DOPCODE_REM_INT_LIT16;
  case OPCODE_AND_INT_LIT:
    return DOPCODE_AND_INT_LIT16;
  case OPCODE_OR_INT_LIT:
    return DOPCODE_OR_INT_LIT16;
  case OPCODE_XOR_INT_LIT:
    return DOPCODE_XOR_INT_LIT16;
  case OPCODE_SHL_INT_LIT:
    return DOPCODE_SHL_INT_LIT8;
  case OPCODE_SHR_INT_LIT:
    return DOPCODE_SHR_INT_LIT8;
  case OPCODE_USHR_INT_LIT:
    return DOPCODE_USHR_INT_LIT8;
  case OPCODE_CONST:
    return DOPCODE_CONST;
  case OPCODE_FILL_ARRAY_DATA:
    return DOPCODE_FILL_ARRAY_DATA;
  case OPCODE_SWITCH:
    return DOPCODE_SPARSE_SWITCH;
  case OPCODE_CONST_WIDE:
    return DOPCODE_CONST_WIDE;
  case OPCODE_IGET:
    return DOPCODE_IGET;
  case OPCODE_IGET_WIDE:
    return DOPCODE_IGET_WIDE;
  case OPCODE_IGET_OBJECT:
    return DOPCODE_IGET_OBJECT;
  case OPCODE_IGET_BOOLEAN:
    return DOPCODE_IGET_BOOLEAN;
  case OPCODE_IGET_BYTE:
    return DOPCODE_IGET_BYTE;
  case OPCODE_IGET_CHAR:
    return DOPCODE_IGET_CHAR;
  case OPCODE_IGET_SHORT:
    return DOPCODE_IGET_SHORT;
  case OPCODE_IPUT:
    return DOPCODE_IPUT;
  case OPCODE_IPUT_WIDE:
    return DOPCODE_IPUT_WIDE;
  case OPCODE_IPUT_OBJECT:
    return DOPCODE_IPUT_OBJECT;
  case OPCODE_IPUT_BOOLEAN:
    return DOPCODE_IPUT_BOOLEAN;
  case OPCODE_IPUT_BYTE:
    return DOPCODE_IPUT_BYTE;
  case OPCODE_IPUT_CHAR:
    return DOPCODE_IPUT_CHAR;
  case OPCODE_IPUT_SHORT:
    return DOPCODE_IPUT_SHORT;
  case OPCODE_SGET:
    return DOPCODE_SGET;
  case OPCODE_SGET_WIDE:
    return DOPCODE_SGET_WIDE;
  case OPCODE_SGET_OBJECT:
    return DOPCODE_SGET_OBJECT;
  case OPCODE_SGET_BOOLEAN:
    return DOPCODE_SGET_BOOLEAN;
  case OPCODE_SGET_BYTE:
    return DOPCODE_SGET_BYTE;
  case OPCODE_SGET_CHAR:
    return DOPCODE_SGET_CHAR;
  case OPCODE_SGET_SHORT:
    return DOPCODE_SGET_SHORT;
  case OPCODE_SPUT:
    return DOPCODE_SPUT;
  case OPCODE_SPUT_WIDE:
    return DOPCODE_SPUT_WIDE;
  case OPCODE_SPUT_OBJECT:
    return DOPCODE_SPUT_OBJECT;
  case OPCODE_SPUT_BOOLEAN:
    return DOPCODE_SPUT_BOOLEAN;
  case OPCODE_SPUT_BYTE:
    return DOPCODE_SPUT_BYTE;
  case OPCODE_SPUT_CHAR:
    return DOPCODE_SPUT_CHAR;
  case OPCODE_SPUT_SHORT:
    return DOPCODE_SPUT_SHORT;
  case OPCODE_INVOKE_VIRTUAL:
    return DOPCODE_INVOKE_VIRTUAL;
  case OPCODE_INVOKE_SUPER:
    return DOPCODE_INVOKE_SUPER;
  case OPCODE_INVOKE_DIRECT:
    return DOPCODE_INVOKE_DIRECT;
  case OPCODE_INVOKE_STATIC:
    return DOPCODE_INVOKE_STATIC;
  case OPCODE_INVOKE_INTERFACE:
    return DOPCODE_INVOKE_INTERFACE;
  case OPCODE_INVOKE_CUSTOM:
    return DOPCODE_INVOKE_CUSTOM;
  case OPCODE_INVOKE_POLYMORPHIC:
    return DOPCODE_INVOKE_POLYMORPHIC;
  case OPCODE_CONST_STRING:
    return DOPCODE_CONST_STRING;
  case OPCODE_CONST_CLASS:
    return DOPCODE_CONST_CLASS;
  case OPCODE_CHECK_CAST:
    return DOPCODE_CHECK_CAST;
  case OPCODE_INSTANCE_OF:
    return DOPCODE_INSTANCE_OF;
  case OPCODE_NEW_INSTANCE:
    return DOPCODE_NEW_INSTANCE;
  case OPCODE_NEW_ARRAY:
    return DOPCODE_NEW_ARRAY;
  case OPCODE_FILLED_NEW_ARRAY:
    return DOPCODE_FILLED_NEW_ARRAY;
  case OPCODE_CONST_METHOD_HANDLE:
    return DOPCODE_CONST_METHOD_HANDLE;
  case OPCODE_CONST_METHOD_TYPE:
    return DOPCODE_CONST_METHOD_TYPE;
  default:
    not_reached_log("Cannot create DexOpcode from %s", SHOW(op));
  }
}

DexOpcode range_version(IROpcode op) {
  switch (op) {
  case OPCODE_INVOKE_DIRECT:
    return DOPCODE_INVOKE_DIRECT_RANGE;
  case OPCODE_INVOKE_STATIC:
    return DOPCODE_INVOKE_STATIC_RANGE;
  case OPCODE_INVOKE_SUPER:
    return DOPCODE_INVOKE_SUPER_RANGE;
  case OPCODE_INVOKE_VIRTUAL:
    return DOPCODE_INVOKE_VIRTUAL_RANGE;
  case OPCODE_INVOKE_INTERFACE:
    return DOPCODE_INVOKE_INTERFACE_RANGE;
  case OPCODE_INVOKE_CUSTOM:
    return DOPCODE_INVOKE_CUSTOM_RANGE;
  case OPCODE_INVOKE_POLYMORPHIC:
    return DOPCODE_INVOKE_POLYMORPHIC_RANGE;
  case OPCODE_FILLED_NEW_ARRAY:
    return DOPCODE_FILLED_NEW_ARRAY_RANGE;
  default:
    not_reached();
  }
}

bool has_variable_srcs_size(IROpcode op) {
  switch (op) {
  case OPCODE_INVOKE_VIRTUAL:
  case OPCODE_INVOKE_DIRECT:
  case OPCODE_INVOKE_SUPER:
  case OPCODE_INVOKE_STATIC:
  case OPCODE_INVOKE_INTERFACE:
  case OPCODE_INVOKE_CUSTOM:
  case OPCODE_INVOKE_POLYMORPHIC:
  case OPCODE_FILLED_NEW_ARRAY:
    return true;
  default:
    return false;
  }
}

bool may_throw(IROpcode op) {
  switch (op) {
  case OPCODE_CONST_STRING:
  case OPCODE_CONST_CLASS:
  case IOPCODE_INIT_CLASS:
  case IOPCODE_WRITE_BARRIER:
  case OPCODE_MONITOR_ENTER:
  case OPCODE_MONITOR_EXIT:
  case OPCODE_CHECK_CAST:
  case OPCODE_INSTANCE_OF:
  case OPCODE_ARRAY_LENGTH:
  case OPCODE_NEW_INSTANCE:
  case OPCODE_NEW_ARRAY:
  case OPCODE_FILLED_NEW_ARRAY:
  case OPCODE_FILL_ARRAY_DATA:
  case OPCODE_AGET:
  case OPCODE_AGET_WIDE:
  case OPCODE_AGET_OBJECT:
  case OPCODE_AGET_BOOLEAN:
  case OPCODE_AGET_BYTE:
  case OPCODE_AGET_CHAR:
  case OPCODE_AGET_SHORT:
  case OPCODE_APUT:
  case OPCODE_APUT_WIDE:
  case OPCODE_APUT_OBJECT:
  case OPCODE_APUT_BOOLEAN:
  case OPCODE_APUT_BYTE:
  case OPCODE_APUT_CHAR:
  case OPCODE_APUT_SHORT:
  case OPCODE_IGET:
  case OPCODE_IGET_WIDE:
  case OPCODE_IGET_OBJECT:
  case OPCODE_IGET_BOOLEAN:
  case OPCODE_IGET_BYTE:
  case OPCODE_IGET_CHAR:
  case OPCODE_IGET_SHORT:
  case OPCODE_IPUT:
  case OPCODE_IPUT_WIDE:
  case OPCODE_IPUT_OBJECT:
  case OPCODE_IPUT_BOOLEAN:
  case OPCODE_IPUT_BYTE:
  case OPCODE_IPUT_CHAR:
  case OPCODE_IPUT_SHORT:
  case OPCODE_SGET:
  case OPCODE_SGET_WIDE:
  case OPCODE_SGET_OBJECT:
  case OPCODE_SGET_BOOLEAN:
  case OPCODE_SGET_BYTE:
  case OPCODE_SGET_CHAR:
  case OPCODE_SGET_SHORT:
  case OPCODE_SPUT:
  case OPCODE_SPUT_WIDE:
  case OPCODE_SPUT_OBJECT:
  case OPCODE_SPUT_BOOLEAN:
  case OPCODE_SPUT_BYTE:
  case OPCODE_SPUT_CHAR:
  case OPCODE_SPUT_SHORT:
  case OPCODE_INVOKE_VIRTUAL:
  case OPCODE_INVOKE_SUPER:
  case OPCODE_INVOKE_DIRECT:
  case OPCODE_INVOKE_STATIC:
  case OPCODE_INVOKE_INTERFACE:
  case OPCODE_INVOKE_CUSTOM:
  case OPCODE_INVOKE_POLYMORPHIC:
  case OPCODE_DIV_INT:
  case OPCODE_REM_INT:
  case OPCODE_DIV_LONG:
  case OPCODE_REM_LONG:
  case OPCODE_DIV_INT_LIT:
  case OPCODE_REM_INT_LIT:
  case OPCODE_CONST_METHOD_HANDLE:
  case OPCODE_CONST_METHOD_TYPE:
    return true;
  default:
    return false;
  }
}

Branchingness branchingness(IROpcode op) {
  if (may_throw(op)) {
    return BRANCH_THROW;
  }

  switch (op) {
  case OPCODE_RETURN_VOID:
  case OPCODE_RETURN:
  case OPCODE_RETURN_WIDE:
  case OPCODE_RETURN_OBJECT:
    return BRANCH_RETURN;
  case OPCODE_THROW:
    return BRANCH_THROW;
  case OPCODE_GOTO:
    return BRANCH_GOTO;
  case OPCODE_SWITCH:
    return BRANCH_SWITCH;
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
    return BRANCH_IF;
  default:
    return BRANCH_NONE;
  }
}

bool has_range_form(IROpcode op) {
  switch (op) {
  case OPCODE_INVOKE_DIRECT:
  case OPCODE_INVOKE_STATIC:
  case OPCODE_INVOKE_SUPER:
  case OPCODE_INVOKE_VIRTUAL:
  case OPCODE_INVOKE_INTERFACE:
  case OPCODE_INVOKE_CUSTOM:
  case OPCODE_INVOKE_POLYMORPHIC:
  case OPCODE_FILLED_NEW_ARRAY:
    return true;
  default:
    return false;
  }
}

bool is_move_result_any(IROpcode op) {
  return is_a_move_result(op) || is_a_move_result_pseudo(op);
}

bool is_commutative(IROpcode opcode) {
  switch (opcode) {
  case OPCODE_AND_INT:
  case OPCODE_AND_LONG:
  case OPCODE_OR_INT:
  case OPCODE_OR_LONG:
  case OPCODE_XOR_INT:
  case OPCODE_XOR_LONG:
  case OPCODE_ADD_INT:
  case OPCODE_ADD_LONG:
  case OPCODE_ADD_FLOAT:
  case OPCODE_ADD_DOUBLE:
  case OPCODE_MUL_INT:
  case OPCODE_MUL_LONG:
  case OPCODE_MUL_FLOAT:
  case OPCODE_MUL_DOUBLE:
  case OPCODE_IF_EQ:
  case OPCODE_IF_NE:
    return true;
  default:
    return false;
  }
}

bool is_binop64(IROpcode op) {
  switch (op) {
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
  case OPCODE_ADD_FLOAT:
  case OPCODE_SUB_FLOAT:
  case OPCODE_MUL_FLOAT:
  case OPCODE_DIV_FLOAT:
  case OPCODE_REM_FLOAT: {
    return false;
  }
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
  case OPCODE_ADD_DOUBLE:
  case OPCODE_SUB_DOUBLE:
  case OPCODE_MUL_DOUBLE:
  case OPCODE_DIV_DOUBLE:
  case OPCODE_REM_DOUBLE: {
    return true;
  }
  default: {
    not_reached_log("Unexpected opcode: %s\n", SHOW(op));
  }
  }
}

IROpcode load_param_to_move(IROpcode op) {
  switch (op) {
  case IOPCODE_LOAD_PARAM:
    return OPCODE_MOVE;
  case IOPCODE_LOAD_PARAM_OBJECT:
    return OPCODE_MOVE_OBJECT;
  case IOPCODE_LOAD_PARAM_WIDE:
    return OPCODE_MOVE_WIDE;
  default:
    not_reached_log("Expected param op, got %s", SHOW(op));
  }
}

IROpcode iput_to_move(IROpcode op) {
  switch (op) {
  case OPCODE_IPUT:
  case OPCODE_IPUT_BOOLEAN:
  case OPCODE_IPUT_BYTE:
  case OPCODE_IPUT_CHAR:
  case OPCODE_IPUT_SHORT:
    return OPCODE_MOVE;
  case OPCODE_IPUT_OBJECT:
    return OPCODE_MOVE_OBJECT;
  case OPCODE_IPUT_WIDE:
    return OPCODE_MOVE_WIDE;
  default:
    not_reached_log("Expected iput, got %s", SHOW(op));
  }
}

IROpcode iget_to_move(IROpcode op) {
  switch (op) {
  case OPCODE_IGET:
  case OPCODE_IGET_BOOLEAN:
  case OPCODE_IGET_BYTE:
  case OPCODE_IGET_CHAR:
  case OPCODE_IGET_SHORT:
    return OPCODE_MOVE;
  case OPCODE_IGET_OBJECT:
    return OPCODE_MOVE_OBJECT;
  case OPCODE_IGET_WIDE:
    return OPCODE_MOVE_WIDE;
  default:
    not_reached_log("Expected iget, got %s", SHOW(op));
  }
}

IROpcode move_result_pseudo_for_iget(IROpcode op) {
  always_assert_log(opcode::is_an_iget(op), "Unexpected opcode %s", SHOW(op));
  return move_result_pseudo_for(op);
}

IROpcode move_result_pseudo_for_sget(IROpcode op) {
  always_assert_log(opcode::is_an_sget(op), "Unexpected opcode %s", SHOW(op));
  return move_result_pseudo_for(op);
}

IROpcode move_result_for_invoke(const DexMethodRef* method) {
  auto* rtype = method->get_proto()->get_rtype();
  return type::is_wide_type(rtype) ? OPCODE_MOVE_RESULT_WIDE
         : type::is_object(rtype)  ? OPCODE_MOVE_RESULT_OBJECT
                                   : OPCODE_MOVE_RESULT;
}

IROpcode invoke_for_method(const DexMethod* method) {
  always_assert(method->is_def());

  if (is_static(method)) {
    return OPCODE_INVOKE_STATIC;
  } else if (is_private(method) || is_constructor(method)) {
    return OPCODE_INVOKE_DIRECT;
  } else {
    always_assert(method->is_virtual());
    return is_interface(type_class(method->get_class()))
               ? OPCODE_INVOKE_INTERFACE
               : OPCODE_INVOKE_VIRTUAL;
  }
}

IROpcode return_opcode(const DexType* type) {
  return type::is_wide_type(type) ? OPCODE_RETURN_WIDE
         : type::is_object(type)  ? OPCODE_RETURN_OBJECT
                                  : OPCODE_RETURN;
}

IROpcode load_opcode(const DexType* type) {
  return type::is_wide_type(type) ? IOPCODE_LOAD_PARAM_WIDE
         : type::is_object(type)  ? IOPCODE_LOAD_PARAM_OBJECT
                                  : IOPCODE_LOAD_PARAM;
}

IROpcode move_opcode(const DexType* type) {
  return type::is_wide_type(type) ? OPCODE_MOVE_WIDE
         : type::is_object(type)  ? OPCODE_MOVE_OBJECT
                                  : OPCODE_MOVE;
}

IROpcode move_result_to_move(IROpcode op) {
  switch (op) {
  case OPCODE_MOVE_RESULT:
    return OPCODE_MOVE;
  case OPCODE_MOVE_RESULT_OBJECT:
    return OPCODE_MOVE_OBJECT;
  case OPCODE_MOVE_RESULT_WIDE:
    return OPCODE_MOVE_WIDE;
  default:
    not_reached();
  }
}

IROpcode return_to_move(IROpcode op) {
  switch (op) {
  case OPCODE_RETURN:
    return OPCODE_MOVE;
  case OPCODE_RETURN_WIDE:
    return OPCODE_MOVE_WIDE;
  case OPCODE_RETURN_OBJECT:
    return OPCODE_MOVE_OBJECT;
  default:
    not_reached();
  }
}

IROpcode move_result_to_pseudo(IROpcode op) {
  switch (op) {
  case OPCODE_MOVE_RESULT:
    return IOPCODE_MOVE_RESULT_PSEUDO;
  case OPCODE_MOVE_RESULT_OBJECT:
    return IOPCODE_MOVE_RESULT_PSEUDO_OBJECT;
  case OPCODE_MOVE_RESULT_WIDE:
    return IOPCODE_MOVE_RESULT_PSEUDO_WIDE;
  default:
    not_reached();
  }
}

IROpcode pseudo_to_move_result(IROpcode op) {
  switch (op) {
  case IOPCODE_MOVE_RESULT_PSEUDO:
    return OPCODE_MOVE_RESULT;
  case IOPCODE_MOVE_RESULT_PSEUDO_OBJECT:
    return OPCODE_MOVE_RESULT_OBJECT;
  case IOPCODE_MOVE_RESULT_PSEUDO_WIDE:
    return OPCODE_MOVE_RESULT_WIDE;
  default:
    not_reached();
  }
}

IROpcode iget_opcode_for_field(const DexField* field) {
  switch (type::to_datatype(field->get_type())) {
  case DataType::Array:
  case DataType::Object:
    return OPCODE_IGET_OBJECT;
  case DataType::Boolean:
    return OPCODE_IGET_BOOLEAN;
  case DataType::Byte:
    return OPCODE_IGET_BYTE;
  case DataType::Char:
    return OPCODE_IGET_CHAR;
  case DataType::Short:
    return OPCODE_IGET_SHORT;
  case DataType::Int:
  case DataType::Float:
    return OPCODE_IGET;
  case DataType::Long:
  case DataType::Double:
    return OPCODE_IGET_WIDE;
  case DataType::Void:
  default:
    not_reached();
  }
}

IROpcode sget_opcode_for_field(const DexField* field) {
  switch (type::to_datatype(field->get_type())) {
  case DataType::Array:
  case DataType::Object:
    return OPCODE_SGET_OBJECT;
  case DataType::Boolean:
    return OPCODE_SGET_BOOLEAN;
  case DataType::Byte:
    return OPCODE_SGET_BYTE;
  case DataType::Char:
    return OPCODE_SGET_CHAR;
  case DataType::Short:
    return OPCODE_SGET_SHORT;
  case DataType::Int:
  case DataType::Float:
    return OPCODE_SGET;
  case DataType::Long:
  case DataType::Double:
    return OPCODE_SGET_WIDE;
  case DataType::Void:
    break;
  }
  not_reached();
}

IROpcode aget_opcode_for_type(const DexType* component) {
  switch (type::to_datatype(component)) {
  case DataType::Array:
  case DataType::Object:
    return OPCODE_AGET_OBJECT;
  case DataType::Boolean:
    return OPCODE_AGET_BOOLEAN;
  case DataType::Byte:
    return OPCODE_AGET_BYTE;
  case DataType::Char:
    return OPCODE_AGET_CHAR;
  case DataType::Short:
    return OPCODE_AGET_SHORT;
  case DataType::Int:
  case DataType::Float:
    return OPCODE_AGET;
  case DataType::Long:
  case DataType::Double:
    return OPCODE_AGET_WIDE;
  case DataType::Void:
    break;
  }
  // Callers pass the component type of an array, which is never void.
  not_reached_log("No array of %s", SHOW(component));
}

IROpcode aput_opcode_for_type(const DexType* component) {
  switch (type::to_datatype(component)) {
  case DataType::Array:
  case DataType::Object:
    return OPCODE_APUT_OBJECT;
  case DataType::Boolean:
    return OPCODE_APUT_BOOLEAN;
  case DataType::Byte:
    return OPCODE_APUT_BYTE;
  case DataType::Char:
    return OPCODE_APUT_CHAR;
  case DataType::Short:
    return OPCODE_APUT_SHORT;
  case DataType::Int:
  case DataType::Float:
    return OPCODE_APUT;
  case DataType::Long:
  case DataType::Double:
    return OPCODE_APUT_WIDE;
  case DataType::Void:
    break;
  }
  // Callers pass the component type of an array, which is never void.
  not_reached_log("No array of %s", SHOW(component));
}

IROpcode move_result_pseudo_for(IROpcode op) {
  always_assert_log(opcode_impl::has_move_result_pseudo(op),
                    "%s has no move-result-pseudo", SHOW(op));
  return opcode_impl::dest_is_wide(op)     ? IOPCODE_MOVE_RESULT_PSEUDO_WIDE
         : opcode_impl::dest_is_object(op) ? IOPCODE_MOVE_RESULT_PSEUDO_OBJECT
                                           : IOPCODE_MOVE_RESULT_PSEUDO;
}

IROpcode invert_conditional_branch(IROpcode op) {
  switch (op) {
  case OPCODE_IF_EQ:
    return OPCODE_IF_NE;
  case OPCODE_IF_NE:
    return OPCODE_IF_EQ;
  case OPCODE_IF_LT:
    return OPCODE_IF_GE;
  case OPCODE_IF_GE:
    return OPCODE_IF_LT;
  case OPCODE_IF_GT:
    return OPCODE_IF_LE;
  case OPCODE_IF_LE:
    return OPCODE_IF_GT;
  case OPCODE_IF_EQZ:
    return OPCODE_IF_NEZ;
  case OPCODE_IF_NEZ:
    return OPCODE_IF_EQZ;
  case OPCODE_IF_LTZ:
    return OPCODE_IF_GEZ;
  case OPCODE_IF_GEZ:
    return OPCODE_IF_LTZ;
  case OPCODE_IF_GTZ:
    return OPCODE_IF_LEZ;
  case OPCODE_IF_LEZ:
    return OPCODE_IF_GTZ;
  default:
    not_reached_log("Invalid conditional opcode %s", SHOW(op));
  }
}

bool has_side_effects(IROpcode opc) {
  switch (opc) {
  case OPCODE_RETURN_VOID:
  case OPCODE_RETURN:
  case OPCODE_RETURN_WIDE:
  case OPCODE_RETURN_OBJECT:
  case OPCODE_MONITOR_ENTER:
  case OPCODE_MONITOR_EXIT:
  case OPCODE_FILL_ARRAY_DATA:
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
  case OPCODE_IF_LEZ:
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
  case OPCODE_IPUT_SHORT:
  case OPCODE_SPUT:
  case OPCODE_SPUT_WIDE:
  case OPCODE_SPUT_OBJECT:
  case OPCODE_SPUT_BOOLEAN:
  case OPCODE_SPUT_BYTE:
  case OPCODE_SPUT_CHAR:
  case OPCODE_SPUT_SHORT:
  case OPCODE_INVOKE_VIRTUAL:
  case OPCODE_INVOKE_SUPER:
  case OPCODE_INVOKE_DIRECT:
  case OPCODE_INVOKE_STATIC:
  case OPCODE_INVOKE_INTERFACE:
  case OPCODE_INVOKE_POLYMORPHIC:
  case OPCODE_INVOKE_CUSTOM:
  case IOPCODE_LOAD_PARAM:
  case IOPCODE_LOAD_PARAM_OBJECT:
  case IOPCODE_LOAD_PARAM_WIDE:
  case IOPCODE_INIT_CLASS:
  case IOPCODE_WRITE_BARRIER:
    return true;
  default:
    return false;
  }
  not_reached();
}

} // namespace opcode

namespace opcode_impl {

bool has_dest(IROpcode op) {
  if (opcode::is_an_internal(op)) {
    return op != IOPCODE_INIT_CLASS && op != IOPCODE_WRITE_BARRIER;
  } else {
    auto dex_op = opcode::to_dex_opcode(op);
    return !opcode::may_throw(op) && dex_opcode::has_dest(dex_op);
  }
}

bool has_move_result_pseudo(IROpcode op) {
  if (opcode::is_an_internal(op)) {
    return false;
  } else if (op == OPCODE_CHECK_CAST) {
    return true;
  } else {
    auto dex_op = opcode::to_dex_opcode(op);
    return dex_opcode::has_dest(dex_op) && opcode::may_throw(op);
  }
}

unsigned min_srcs_size(IROpcode op) {
  if (opcode::is_an_internal(op)) {
    return 0;
  } else {
    auto dex_op = opcode::to_dex_opcode(op);
    return dex_opcode::min_srcs_size(dex_op);
  }
}

bool dest_is_wide(IROpcode op) {
  switch (op) {
  case OPCODE_MOVE_WIDE:
  case OPCODE_MOVE_RESULT_WIDE:

  case OPCODE_CONST_WIDE:

  case OPCODE_AGET_WIDE:
  case OPCODE_IGET_WIDE:
  case OPCODE_SGET_WIDE:

  case OPCODE_NEG_LONG:
  case OPCODE_NOT_LONG:
  case OPCODE_NEG_DOUBLE:
  case OPCODE_INT_TO_LONG:
  case OPCODE_INT_TO_DOUBLE:
  case OPCODE_LONG_TO_DOUBLE:
  case OPCODE_FLOAT_TO_LONG:
  case OPCODE_FLOAT_TO_DOUBLE:
  case OPCODE_DOUBLE_TO_LONG:

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
  case OPCODE_ADD_DOUBLE:
  case OPCODE_SUB_DOUBLE:
  case OPCODE_MUL_DOUBLE:
  case OPCODE_DIV_DOUBLE:
  case OPCODE_REM_DOUBLE:
    return true;

  case IOPCODE_LOAD_PARAM:
  case IOPCODE_LOAD_PARAM_OBJECT:
    return false;
  case IOPCODE_LOAD_PARAM_WIDE:
    return true;

  case IOPCODE_MOVE_RESULT_PSEUDO:
  case IOPCODE_MOVE_RESULT_PSEUDO_OBJECT:
    return false;
  case IOPCODE_MOVE_RESULT_PSEUDO_WIDE:
    return true;

  default:
    return false;
  }
}

bool dest_is_object(IROpcode op) {
  switch (op) {
  case OPCODE_NOP:
    not_reached_log("No dest");
  case OPCODE_MOVE:
  case OPCODE_MOVE_WIDE:
    return false;
  case OPCODE_MOVE_OBJECT:
    return true;
  case OPCODE_MOVE_RESULT:
  case OPCODE_MOVE_RESULT_WIDE:
    return false;
  case OPCODE_MOVE_RESULT_OBJECT:
  case OPCODE_MOVE_EXCEPTION:
    return true;
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
  case OPCODE_NEG_LONG:
  case OPCODE_NOT_LONG:
  case OPCODE_NEG_FLOAT:
  case OPCODE_NEG_DOUBLE:
  case OPCODE_INT_TO_LONG:
  case OPCODE_INT_TO_FLOAT:
  case OPCODE_INT_TO_DOUBLE:
  case OPCODE_LONG_TO_INT:
  case OPCODE_LONG_TO_FLOAT:
  case OPCODE_LONG_TO_DOUBLE:
  case OPCODE_FLOAT_TO_INT:
  case OPCODE_FLOAT_TO_LONG:
  case OPCODE_FLOAT_TO_DOUBLE:
  case OPCODE_DOUBLE_TO_INT:
  case OPCODE_DOUBLE_TO_LONG:
  case OPCODE_DOUBLE_TO_FLOAT:
  case OPCODE_INT_TO_BYTE:
  case OPCODE_INT_TO_CHAR:
  case OPCODE_INT_TO_SHORT:
  case OPCODE_ARRAY_LENGTH:
    return false;
  case OPCODE_CMPL_FLOAT:
  case OPCODE_CMPG_FLOAT:
  case OPCODE_CMPL_DOUBLE:
  case OPCODE_CMPG_DOUBLE:
  case OPCODE_CMP_LONG:
    return false;
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
  case OPCODE_AGET_WIDE:
    return false;
  case OPCODE_AGET_OBJECT:
    return true;
  case OPCODE_AGET_BOOLEAN:
  case OPCODE_AGET_BYTE:
  case OPCODE_AGET_CHAR:
  case OPCODE_AGET_SHORT:
    return false;
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
  case OPCODE_ADD_FLOAT:
  case OPCODE_SUB_FLOAT:
  case OPCODE_MUL_FLOAT:
  case OPCODE_DIV_FLOAT:
  case OPCODE_REM_FLOAT:
  case OPCODE_ADD_DOUBLE:
  case OPCODE_SUB_DOUBLE:
  case OPCODE_MUL_DOUBLE:
  case OPCODE_DIV_DOUBLE:
  case OPCODE_REM_DOUBLE:
    return false;
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
    return false;
  case IOPCODE_R_CONST:
  case OPCODE_CONST:
    return false;
  case OPCODE_FILL_ARRAY_DATA:
  case OPCODE_SWITCH:
    not_reached_log("No dest");
  case OPCODE_CONST_WIDE:
  case OPCODE_IGET:
  case OPCODE_IGET_WIDE:
    return false;
  case OPCODE_IGET_OBJECT:
    return true;
  case OPCODE_IGET_BOOLEAN:
  case OPCODE_IGET_BYTE:
  case OPCODE_IGET_CHAR:
  case OPCODE_IGET_SHORT:
    return false;
  case OPCODE_IPUT:
  case OPCODE_IPUT_WIDE:
  case OPCODE_IPUT_OBJECT:
  case OPCODE_IPUT_BOOLEAN:
  case OPCODE_IPUT_BYTE:
  case OPCODE_IPUT_CHAR:
  case OPCODE_IPUT_SHORT:
    not_reached_log("No dest");
  case OPCODE_SGET:
  case OPCODE_SGET_WIDE:
    return false;
  case OPCODE_SGET_OBJECT:
    return true;
  case OPCODE_SGET_BOOLEAN:
  case OPCODE_SGET_BYTE:
  case OPCODE_SGET_CHAR:
  case OPCODE_SGET_SHORT:
    return false;
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
    return true;
  case OPCODE_INSTANCE_OF:
    return false;
  case OPCODE_NEW_INSTANCE:
  case OPCODE_NEW_ARRAY:
  case OPCODE_FILLED_NEW_ARRAY:
    return true;

  case OPCODE_CONST_METHOD_HANDLE:
  case OPCODE_CONST_METHOD_TYPE:
    return true;

  case IOPCODE_LOAD_PARAM:
    return false;
  case IOPCODE_LOAD_PARAM_OBJECT:
    return true;
  case IOPCODE_LOAD_PARAM_WIDE:
    return false;
  case IOPCODE_MOVE_RESULT_PSEUDO:
    return false;
  case IOPCODE_MOVE_RESULT_PSEUDO_OBJECT:
    return true;
  case IOPCODE_MOVE_RESULT_PSEUDO_WIDE:
    return false;
  case IOPCODE_INJECTION_ID:
  case IOPCODE_UNREACHABLE:
    return false;

  case IOPCODE_INIT_CLASS:
  case IOPCODE_WRITE_BARRIER:
    not_reached_log("No dest");
  }
  not_reached_log("Unknown opcode %02x\n", op);
}

} // namespace opcode_impl
