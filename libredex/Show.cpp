/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "Show.h"

#include <iomanip>

#include <boost/locale/encoding_utf.hpp>
#include <boost/version.hpp>
// Quoted was accepted into public components as of 1.73. The `detail`
// header was removed in 1.74.
#if BOOST_VERSION < 107400
#include <boost/io/detail/quoted_manip.hpp>
#else
#include <boost/io/quoted.hpp>
#endif

#include "ControlFlow.h"
#include "CppUtil.h"
#include "Creators.h"
#include "Debug.h"
#include "DexAnnotation.h"
#include "DexCallSite.h"
#include "DexClass.h"
#include "DexDebugInstruction.h"
#include "DexEncoding.h"
#include "DexIdx.h"
#include "DexInstruction.h"
#include "DexMethodHandle.h"
#include "DexPosition.h"
#include "DexUtil.h"
#include "IRCode.h"
#include "IROpcode.h"
#include "ShowCFG.h"
#include "StringBuilder.h"
#include "TypeUtil.h"

namespace {

std::string humanize(std::string const& type) {
  if (type.compare("B") == 0) {
    return "byte";
  } else if (type.compare("C") == 0) {
    return "char";
  } else if (type.compare("D") == 0) {
    return "double";
  } else if (type.compare("F") == 0) {
    return "float";
  } else if (type.compare("I") == 0) {
    return "int";
  } else if (type.compare("J") == 0) {
    return "long";
  } else if (type.compare("S") == 0) {
    return "short";
  } else if (type.compare("V") == 0) {
    return "void";
  } else if (type.compare("Z") == 0) {
    return "boolean";
  } else if (type[0] == '[') {
    std::ostringstream ss;
    ss << humanize(type.substr(1)) << "[]";
    return ss.str();
  } else if (type[0] == 'L') {
    return java_names::internal_to_external(type);
  }
  return "unknown";
}

// TODO: make sure names reported handles collisions correctly.
//       i.e. ACC_VOLATILE and ACC_BRIDGE etc.
std::string accessibility(uint32_t acc, bool method = false) {
  std::ostringstream ss;
  if ((acc & DexAccessFlags::ACC_PUBLIC) != 0u) {
    ss << "public ";
  }
  if ((acc & DexAccessFlags::ACC_PRIVATE) != 0u) {
    ss << "private ";
  }
  if ((acc & DexAccessFlags::ACC_PROTECTED) != 0u) {
    ss << "protected ";
  }
  if ((acc & DexAccessFlags::ACC_STATIC) != 0u) {
    ss << "static ";
  }
  if ((acc & DexAccessFlags::ACC_FINAL) != 0u) {
    ss << "final ";
  }
  if ((acc & DexAccessFlags::ACC_INTERFACE) != 0u) {
    ss << "interface ";
  } else if ((acc & DexAccessFlags::ACC_ABSTRACT) != 0u) {
    ss << "abstract ";
  }
  if ((acc & DexAccessFlags::ACC_ENUM) != 0u) {
    ss << "enum ";
  }
  if ((acc & DexAccessFlags::ACC_SYNCHRONIZED) != 0u) {
    ss << "synchronized ";
  }
  if ((acc & DexAccessFlags::ACC_VOLATILE) != 0u) {
    if (method) {
      ss << "bridge ";
    } else {
      ss << "volatile ";
    }
  }
  if ((acc & DexAccessFlags::ACC_NATIVE) != 0u) {
    ss << "native ";
  }
  if ((acc & DexAccessFlags::ACC_TRANSIENT) != 0u) {
    if (method) {
      ss << "vararg ";
    } else {
      ss << "transient ";
    }
  }
  return ss.str();
}

std::string show(DexAnnotationVisibility vis) {
  switch (vis) {
  case DAV_BUILD:
    return "build";
  case DAV_RUNTIME:
    return "runtime";
  case DAV_SYSTEM:
    return "system";
  }
}

std::string show_type(const DexType* t, bool deobfuscated) {
  return self_recursive_fn(
      [&](auto self, const DexType* t) -> std::string {
        if (t == nullptr) {
          return std::string("");
        }
        auto name = t->get_name()->str();
        if (!deobfuscated || name.empty()) {
          return str_copy(name);
        }
        if (name[0] == 'L') {
          auto* cls = type_class(t);
          if (cls != nullptr &&
              !cls->get_deobfuscated_name_or_empty().empty()) {
            return cls->get_deobfuscated_name_or_empty_copy();
          }
          return str_copy(name);
        } else if (name[0] == '[') {
          std::ostringstream ss;
          ss << '[' << self(self, type::get_array_component_type(t));
          return ss.str();
        }
        return str_copy(name);
      },
      t);
}

std::string show_field(const DexFieldRef* ref, bool deobfuscated) {
  if (ref == nullptr) {
    return "";
  }

  if (deobfuscated && ref->is_def()) {
    const auto name = ref->as_def()->get_deobfuscated_name_or_empty();
    if (!name.empty()) {
      return str_copy(name);
    }
  }
  string_builders::StaticStringBuilder<5> b;
  b << show_type(ref->get_class(), deobfuscated) << "." << show(ref->get_name())
    << ":" << show_type(ref->get_type(), deobfuscated);
  return b.str();
}

std::string show_type_list(const DexTypeList* l, bool deobfuscated) {
  if (l == nullptr) {
    return "";
  }

  string_builders::DynamicStringBuilder b(static_cast<uint32_t>(l->size()));
  for (const auto& type : *l) {
    b << show_type(type, deobfuscated);
  }
  return b.str();
}

std::string show_proto(const DexProto* p, bool deobfuscated) {
  if (p == nullptr) {
    return "";
  }
  string_builders::StaticStringBuilder<4> b;
  b << "(" << show_type_list(p->get_args(), deobfuscated) << ")"
    << show_type(p->get_rtype(), deobfuscated);
  return b.str();
}

std::string show_method(const DexMethodRef* ref, bool deobfuscated) {
  if (ref == nullptr) {
    return "";
  }

  if (deobfuscated && ref->is_def()) {
    const auto name = ref->as_def()->get_deobfuscated_name_or_empty();
    if (!name.empty()) {
      return str_copy(name);
    }
  }

  string_builders::StaticStringBuilder<5> b;
  b << show_type(ref->get_class(), deobfuscated) << "." << show(ref->get_name())
    << ":" << show_proto(ref->get_proto(), deobfuscated);
  return b.str();
}

std::string show_methodhandle(const DexMethodHandle* ref, bool deobfuscated) {
  if (ref == nullptr) {
    return "";
  }
  return show_method(ref->methodref(), deobfuscated);
}

std::string show_opcode(const DexInstruction* insn, bool deobfuscated = false) {
  if (insn == nullptr) {
    return "";
  }
  std::ostringstream ss;
  auto opcode = insn->opcode();
  switch (opcode) {
  case DOPCODE_NOP:
    return "nop";
  case DOPCODE_MOVE:
    return "move";
  case DOPCODE_MOVE_WIDE:
    return "move-wide";
  case DOPCODE_MOVE_OBJECT:
    return "move-object";
  case DOPCODE_MOVE_RESULT:
    return "move-result";
  case DOPCODE_MOVE_RESULT_WIDE:
    return "move-result-wide";
  case DOPCODE_MOVE_RESULT_OBJECT:
    return "move-result-object";
  case DOPCODE_MOVE_EXCEPTION:
    return "move-exception";
  case DOPCODE_RETURN_VOID:
    return "return-void";
  case DOPCODE_RETURN:
    return "return";
  case DOPCODE_RETURN_WIDE:
    return "return-wide";
  case DOPCODE_RETURN_OBJECT:
    return "return-object";
  case DOPCODE_CONST_4:
    return "const/4";
  case DOPCODE_MONITOR_ENTER:
    return "monitor-enter";
  case DOPCODE_MONITOR_EXIT:
    return "monitor-exit";
  case DOPCODE_THROW:
    return "throw";
  case DOPCODE_GOTO:
    return "goto";
  case DOPCODE_NEG_INT:
    return "neg-int";
  case DOPCODE_NOT_INT:
    return "not-int";
  case DOPCODE_NEG_LONG:
    return "neg-long";
  case DOPCODE_NOT_LONG:
    return "not-long";
  case DOPCODE_NEG_FLOAT:
    return "neg-float";
  case DOPCODE_NEG_DOUBLE:
    return "neg-double";
  case DOPCODE_INT_TO_LONG:
    return "int-to-long";
  case DOPCODE_INT_TO_FLOAT:
    return "int-to-float";
  case DOPCODE_INT_TO_DOUBLE:
    return "int-to-double";
  case DOPCODE_LONG_TO_INT:
    return "long-to-int";
  case DOPCODE_LONG_TO_FLOAT:
    return "long-to-float";
  case DOPCODE_LONG_TO_DOUBLE:
    return "long-to-double";
  case DOPCODE_FLOAT_TO_INT:
    return "float-to-int";
  case DOPCODE_FLOAT_TO_LONG:
    return "float-to-long";
  case DOPCODE_FLOAT_TO_DOUBLE:
    return "float-to-double";
  case DOPCODE_DOUBLE_TO_INT:
    return "double-to-int";
  case DOPCODE_DOUBLE_TO_LONG:
    return "double-to-long";
  case DOPCODE_DOUBLE_TO_FLOAT:
    return "double-to-float";
  case DOPCODE_INT_TO_BYTE:
    return "int-to-byte";
  case DOPCODE_INT_TO_CHAR:
    return "int-to-char";
  case DOPCODE_INT_TO_SHORT:
    return "int-to-short";
  case DOPCODE_ARRAY_LENGTH:
    return "array-length";
  case DOPCODE_MOVE_FROM16:
    return "move/from16";
  case DOPCODE_MOVE_WIDE_FROM16:
    return "move-wide/from16";
  case DOPCODE_MOVE_OBJECT_FROM16:
    return "move-object/from16";
  case DOPCODE_CONST_16:
    return "const/16";
  case DOPCODE_CONST_HIGH16:
    return "const/high16";
  case DOPCODE_CONST_WIDE_16:
    return "const-wide/16";
  case DOPCODE_CONST_WIDE_HIGH16:
    return "const-wide/high16";
  case DOPCODE_GOTO_16:
    return "goto/16";
  case DOPCODE_CMPL_FLOAT:
    return "cmpl-float";
  case DOPCODE_CMPG_FLOAT:
    return "cmpg-float";
  case DOPCODE_CMPL_DOUBLE:
    return "cmpl-double";
  case DOPCODE_CMPG_DOUBLE:
    return "cmpg-double";
  case DOPCODE_CMP_LONG:
    return "cmp-long";
  case DOPCODE_IF_EQ:
    return "if-eq";
  case DOPCODE_IF_NE:
    return "if-ne";
  case DOPCODE_IF_LT:
    return "if-lt";
  case DOPCODE_IF_GE:
    return "if-ge";
  case DOPCODE_IF_GT:
    return "if-gt";
  case DOPCODE_IF_LE:
    return "if-le";
  case DOPCODE_IF_EQZ:
    return "if-eqz";
  case DOPCODE_IF_NEZ:
    return "if-nez";
  case DOPCODE_IF_LTZ:
    return "if-ltz";
  case DOPCODE_IF_GEZ:
    return "if-gez";
  case DOPCODE_IF_GTZ:
    return "if-gtz";
  case DOPCODE_IF_LEZ:
    return "if-lez";
  case DOPCODE_AGET:
    return "aget";
  case DOPCODE_AGET_WIDE:
    return "aget-wide";
  case DOPCODE_AGET_OBJECT:
    return "aget-object";
  case DOPCODE_AGET_BOOLEAN:
    return "aget-boolean";
  case DOPCODE_AGET_BYTE:
    return "aget-byte";
  case DOPCODE_AGET_CHAR:
    return "aget-char";
  case DOPCODE_AGET_SHORT:
    return "aget-short";
  case DOPCODE_APUT:
    return "aput";
  case DOPCODE_APUT_WIDE:
    return "aput-wide";
  case DOPCODE_APUT_OBJECT:
    return "aput-object";
  case DOPCODE_APUT_BOOLEAN:
    return "aput-boolean";
  case DOPCODE_APUT_BYTE:
    return "aput-byte";
  case DOPCODE_APUT_CHAR:
    return "aput-char";
  case DOPCODE_APUT_SHORT:
    return "aput-short";
  case DOPCODE_ADD_INT:
    return "add-int";
  case DOPCODE_SUB_INT:
    return "sub-int";
  case DOPCODE_MUL_INT:
    return "mul-int";
  case DOPCODE_DIV_INT:
    return "div-int";
  case DOPCODE_REM_INT:
    return "rem-int";
  case DOPCODE_AND_INT:
    return "and-int";
  case DOPCODE_OR_INT:
    return "or-int";
  case DOPCODE_XOR_INT:
    return "xor-int";
  case DOPCODE_SHL_INT:
    return "shl-int";
  case DOPCODE_SHR_INT:
    return "shr-int";
  case DOPCODE_USHR_INT:
    return "ushr-int";
  case DOPCODE_ADD_LONG:
    return "add-long";
  case DOPCODE_SUB_LONG:
    return "sub-long";
  case DOPCODE_MUL_LONG:
    return "mul-long";
  case DOPCODE_DIV_LONG:
    return "div-long";
  case DOPCODE_REM_LONG:
    return "rem-long";
  case DOPCODE_AND_LONG:
    return "and-long";
  case DOPCODE_OR_LONG:
    return "or-long";
  case DOPCODE_XOR_LONG:
    return "xor-long";
  case DOPCODE_SHL_LONG:
    return "shl-long";
  case DOPCODE_SHR_LONG:
    return "shr-long";
  case DOPCODE_USHR_LONG:
    return "ushr-long";
  case DOPCODE_ADD_FLOAT:
    return "add-float";
  case DOPCODE_SUB_FLOAT:
    return "sub-float";
  case DOPCODE_MUL_FLOAT:
    return "mul-float";
  case DOPCODE_DIV_FLOAT:
    return "div-float";
  case DOPCODE_REM_FLOAT:
    return "rem-float";
  case DOPCODE_ADD_DOUBLE:
    return "add-double";
  case DOPCODE_SUB_DOUBLE:
    return "sub-double";
  case DOPCODE_MUL_DOUBLE:
    return "mul-double";
  case DOPCODE_DIV_DOUBLE:
    return "div-double";
  case DOPCODE_REM_DOUBLE:
    return "rem-double";
  case DOPCODE_ADD_INT_LIT16:
    return "add-int/lit16";
  case DOPCODE_RSUB_INT:
    return "rsub-int";
  case DOPCODE_MUL_INT_LIT16:
    return "mul-int/lit16";
  case DOPCODE_DIV_INT_LIT16:
    return "div-int/lit16";
  case DOPCODE_REM_INT_LIT16:
    return "rem-int/lit16";
  case DOPCODE_AND_INT_LIT16:
    return "and-int/lit16";
  case DOPCODE_OR_INT_LIT16:
    return "or-int/lit16";
  case DOPCODE_XOR_INT_LIT16:
    return "xor-int/lit16";
  case DOPCODE_ADD_INT_LIT8:
    return "add-int/lit8";
  case DOPCODE_RSUB_INT_LIT8:
    return "rsub-int/lit8";
  case DOPCODE_MUL_INT_LIT8:
    return "mul-int/lit8";
  case DOPCODE_DIV_INT_LIT8:
    return "div-int/lit8";
  case DOPCODE_REM_INT_LIT8:
    return "rem-int/lit8";
  case DOPCODE_AND_INT_LIT8:
    return "and-int/lit8";
  case DOPCODE_OR_INT_LIT8:
    return "or-int/lit8";
  case DOPCODE_XOR_INT_LIT8:
    return "xor-int/lit8";
  case DOPCODE_SHL_INT_LIT8:
    return "shl-int/lit8";
  case DOPCODE_SHR_INT_LIT8:
    return "shr-int/lit8";
  case DOPCODE_USHR_INT_LIT8:
    return "ushr-int/lit8";
  case DOPCODE_MOVE_16:
    return "move/16";
  case DOPCODE_MOVE_WIDE_16:
    return "move-wide/16";
  case DOPCODE_MOVE_OBJECT_16:
    return "move-object/16";
  case DOPCODE_CONST:
    return "const";
  case DOPCODE_CONST_WIDE_32:
    return "const-wide/32";
  case DOPCODE_FILL_ARRAY_DATA:
    return "fill-array-data";
  case DOPCODE_GOTO_32:
    return "goto/32";
  case DOPCODE_PACKED_SWITCH:
    return "packed-switch";
  case DOPCODE_SPARSE_SWITCH:
    return "sparse-switch";
  case DOPCODE_CONST_WIDE:
    return "const-wide";
  // field opcode
  case DOPCODE_IGET:
    ss << "iget ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_IGET_WIDE:
    ss << "iget-wide ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_IGET_OBJECT:
    ss << "iget-object ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_IGET_BOOLEAN:
    ss << "iget-boolean ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_IGET_BYTE:
    ss << "iget-byte ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_IGET_CHAR:
    ss << "iget-char ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_IGET_SHORT:
    ss << "iget-short ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_IPUT:
    ss << "iput ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_IPUT_WIDE:
    ss << "iput-wide ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_IPUT_OBJECT:
    ss << "iput-object ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_IPUT_BOOLEAN:
    ss << "iput-boolean ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_IPUT_BYTE:
    ss << "iput-byte ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_IPUT_CHAR:
    ss << "iput-char ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_IPUT_SHORT:
    ss << "iput-short ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_SGET:
    ss << "sget ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_SGET_WIDE:
    ss << "sget-wide ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_SGET_OBJECT:
    ss << "sget-object ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_SGET_BOOLEAN:
    ss << "sget-boolean ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_SGET_BYTE:
    ss << "sget-byte ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_SGET_CHAR:
    ss << "sget-char ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_SGET_SHORT:
    ss << "sget-short ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_SPUT:
    ss << "sput ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_SPUT_WIDE:
    ss << "sput-wide ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_SPUT_OBJECT:
    ss << "sput-object ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_SPUT_BOOLEAN:
    ss << "sput-boolean ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_SPUT_BYTE:
    ss << "sput-byte ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_SPUT_CHAR:
    ss << "sput-char ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_SPUT_SHORT:
    ss << "sput-short ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_INVOKE_VIRTUAL:
    ss << "invoke-virtual ";
    ss << show_method(dynamic_cast<const DexOpcodeMethod*>(insn)->get_method(),
                      deobfuscated);
    return ss.str();
  case DOPCODE_INVOKE_SUPER:
    ss << "invoke-super ";
    ss << show_method(dynamic_cast<const DexOpcodeMethod*>(insn)->get_method(),
                      deobfuscated);
    return ss.str();
  case DOPCODE_INVOKE_DIRECT:
    ss << "invoke-direct ";
    ss << show_method(dynamic_cast<const DexOpcodeMethod*>(insn)->get_method(),
                      deobfuscated);
    return ss.str();
  case DOPCODE_INVOKE_STATIC:
    ss << "invoke-static ";
    ss << show_method(dynamic_cast<const DexOpcodeMethod*>(insn)->get_method(),
                      deobfuscated);
    return ss.str();
  case DOPCODE_INVOKE_INTERFACE:
    ss << "invoke-interface ";
    ss << show_method(dynamic_cast<const DexOpcodeMethod*>(insn)->get_method(),
                      deobfuscated);
    return ss.str();
  case DOPCODE_INVOKE_VIRTUAL_RANGE:
    ss << "invoke-virtual/range ";
    ss << show_method(dynamic_cast<const DexOpcodeMethod*>(insn)->get_method(),
                      deobfuscated);
    return ss.str();
  case DOPCODE_INVOKE_SUPER_RANGE:
    ss << "invoke-super/range ";
    ss << show_method(dynamic_cast<const DexOpcodeMethod*>(insn)->get_method(),
                      deobfuscated);
    return ss.str();
  case DOPCODE_INVOKE_DIRECT_RANGE:
    ss << "invoke-direct/range ";
    ss << show_method(dynamic_cast<const DexOpcodeMethod*>(insn)->get_method(),
                      deobfuscated);
    return ss.str();
  case DOPCODE_INVOKE_STATIC_RANGE:
    ss << "invoke-static/range ";
    ss << show_method(dynamic_cast<const DexOpcodeMethod*>(insn)->get_method(),
                      deobfuscated);
    return ss.str();
  case DOPCODE_INVOKE_INTERFACE_RANGE:
    ss << "invoke-interface/range ";
    ss << show_method(dynamic_cast<const DexOpcodeMethod*>(insn)->get_method(),
                      deobfuscated);
    return ss.str();
  case DOPCODE_CONST_STRING:
    ss << "const-string "
       << show(dynamic_cast<const DexOpcodeString*>(insn)->get_string());
    return ss.str();
  case DOPCODE_CONST_STRING_JUMBO:
    ss << "const-string/jumbo "
       << show(dynamic_cast<const DexOpcodeString*>(insn)->get_string());
    return ss.str();
  case DOPCODE_CONST_CLASS:
    ss << "const-class ";
    ss << show_type(dynamic_cast<const DexOpcodeType*>(insn)->get_type(),
                    deobfuscated);
    return ss.str();
  case DOPCODE_CHECK_CAST:
    ss << "check-cast ";
    ss << show_type(dynamic_cast<const DexOpcodeType*>(insn)->get_type(),
                    deobfuscated);
    return ss.str();
  case DOPCODE_INSTANCE_OF:
    ss << "instance-of ";
    ss << show_type(dynamic_cast<const DexOpcodeType*>(insn)->get_type(),
                    deobfuscated);
    return ss.str();
  case DOPCODE_NEW_INSTANCE:
    ss << "new-instance ";
    ss << show_type(dynamic_cast<const DexOpcodeType*>(insn)->get_type(),
                    deobfuscated);
    return ss.str();
  case DOPCODE_NEW_ARRAY:
    ss << "new-array ";
    ss << show_type(dynamic_cast<const DexOpcodeType*>(insn)->get_type(),
                    deobfuscated);
    return ss.str();
  case DOPCODE_FILLED_NEW_ARRAY:
    ss << "filled-new-array ";
    ss << show_type(dynamic_cast<const DexOpcodeType*>(insn)->get_type(),
                    deobfuscated);
    return ss.str();
  case FOPCODE_PACKED_SWITCH:
    return "packed-switch-payload";
  case FOPCODE_SPARSE_SWITCH:
    return "sparse-switch-payload";
  case FOPCODE_FILLED_ARRAY:
    return "fill-array-data-payload";
  case DOPCODE_FILLED_NEW_ARRAY_RANGE:
    return "filled-new-array/range";
  case DOPCODE_RETURN_VOID_NO_BARRIER:
    return "return-void-no-barrier";
  case DOPCODE_ADD_INT_2ADDR:
    return "add-int/2addr";
  case DOPCODE_SUB_INT_2ADDR:
    return "sub-int/2addr";
  case DOPCODE_MUL_INT_2ADDR:
    return "mult-int/2addr";
  case DOPCODE_DIV_INT_2ADDR:
    return "div-int/2addr";
  case DOPCODE_REM_INT_2ADDR:
    return "rem-int/2addr";
  case DOPCODE_AND_INT_2ADDR:
    return "and-int/2addr";
  case DOPCODE_OR_INT_2ADDR:
    return "or-int/2addr";
  case DOPCODE_XOR_INT_2ADDR:
    return "xor-int/2addr";
  case DOPCODE_SHL_INT_2ADDR:
    return "shl-int/2addr";
  case DOPCODE_SHR_INT_2ADDR:
    return "shr-int/2addr";
  case DOPCODE_USHR_INT_2ADDR:
    return "ushr-int/2addr";
  case DOPCODE_ADD_LONG_2ADDR:
    return "add-long/2addr";
  case DOPCODE_SUB_LONG_2ADDR:
    return "sub-long/2addr";
  case DOPCODE_MUL_LONG_2ADDR:
    return "mul-long/2addr";
  case DOPCODE_DIV_LONG_2ADDR:
    return "div-long/2addr";
  case DOPCODE_REM_LONG_2ADDR:
    return "rem-long/2addr";
  case DOPCODE_AND_LONG_2ADDR:
    return "and-long/2addr";
  case DOPCODE_OR_LONG_2ADDR:
    return "or-long/2addr";
  case DOPCODE_XOR_LONG_2ADDR:
    return "xor-long/2addr";
  case DOPCODE_SHL_LONG_2ADDR:
    return "shl-long/2addr";
  case DOPCODE_SHR_LONG_2ADDR:
    return "shr-long/2addr";
  case DOPCODE_USHR_LONG_2ADDR:
    return "ushr-long/2addr";
  case DOPCODE_ADD_FLOAT_2ADDR:
    return "add-float/2addr";
  case DOPCODE_SUB_FLOAT_2ADDR:
    return "sub-float/2addr";
  case DOPCODE_MUL_FLOAT_2ADDR:
    return "mul-float/2addr";
  case DOPCODE_DIV_FLOAT_2ADDR:
    return "div-float/2addr";
  case DOPCODE_REM_FLOAT_2ADDR:
    return "rem-float/2addr";
  case DOPCODE_ADD_DOUBLE_2ADDR:
    return "add-double/2addr";
  case DOPCODE_SUB_DOUBLE_2ADDR:
    return "sub-double/2addr";
  case DOPCODE_MUL_DOUBLE_2ADDR:
    return "mul-double/2addr";
  case DOPCODE_DIV_DOUBLE_2ADDR:
    return "div-double/2addr";
  case DOPCODE_REM_DOUBLE_2ADDR:
    return "rem-double/2addr";
  case DOPCODE_IGET_QUICK:
    ss << "iget-quick ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_IGET_WIDE_QUICK:
    ss << "iget-wide-quick ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_IGET_OBJECT_QUICK:
    ss << "iget-object-quick ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_IPUT_QUICK:
    ss << "iput-quick ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_IPUT_WIDE_QUICK:
    ss << "iput-wide-quick ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_IPUT_OBJECT_QUICK:
    ss << "iput-object-quick ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_INVOKE_VIRTUAL_QUICK:
    ss << "invoke-virtual-quick ";
    ss << show_method(dynamic_cast<const DexOpcodeMethod*>(insn)->get_method(),
                      deobfuscated);
    return ss.str();
  case DOPCODE_INVOKE_VIRTUAL_RANGE_QUICK:
    ss << "invoke-virtual/range-quick ";
    ss << show_method(dynamic_cast<const DexOpcodeMethod*>(insn)->get_method(),
                      deobfuscated);
    return ss.str();
  case DOPCODE_IPUT_BOOLEAN_QUICK:
    ss << "iput-boolean-quick ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_IPUT_BYTE_QUICK:
    ss << "iput-byte-quick ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_IPUT_CHAR_QUICK:
    ss << "iput-char-quick ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_IPUT_SHORT_QUICK:
    ss << "iput-short-quick ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_IGET_BOOLEAN_QUICK:
    ss << "iget-boolean-quick ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_IGET_BYTE_QUICK:
    ss << "iget-byte-quick ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_IGET_CHAR_QUICK:
    ss << "iget-char-quick ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_IGET_SHORT_QUICK:
    ss << "iget-short-quick ";
    ss << show_field(dynamic_cast<const DexOpcodeField*>(insn)->get_field(),
                     deobfuscated);
    return ss.str();
  case DOPCODE_INVOKE_POLYMORPHIC:
    ss << "invoke-polymorphic ";
    ss << show_method(dynamic_cast<const DexOpcodeMethod*>(insn)->get_method(),
                      deobfuscated);
    return ss.str();
  case DOPCODE_INVOKE_POLYMORPHIC_RANGE:
    ss << "invoke-polymorphic/range ";
    ss << show_method(dynamic_cast<const DexOpcodeMethod*>(insn)->get_method(),
                      deobfuscated);
    return ss.str();
  case DOPCODE_INVOKE_CUSTOM:
    ss << "invoke-custom ";
    ss << show_method(dynamic_cast<const DexOpcodeMethod*>(insn)->get_method(),
                      deobfuscated);
    return ss.str();
  case DOPCODE_INVOKE_CUSTOM_RANGE:
    ss << "invoke-custom/range ";
    ss << show_method(dynamic_cast<const DexOpcodeMethod*>(insn)->get_method(),
                      deobfuscated);
    return ss.str();
  case DOPCODE_CONST_METHOD_HANDLE:
    ss << "const-method-handle ";
    ss << show_methodhandle(
        dynamic_cast<const DexOpcodeMethodHandle*>(insn)->get_methodhandle(),
        deobfuscated);
    return ss.str();
  case DOPCODE_CONST_METHOD_TYPE:
    ss << "const-method-type ";
    ss << show_proto(dynamic_cast<const DexOpcodeProto*>(insn)->get_proto(),
                     deobfuscated);
    return ss.str();
  }
}

std::string show_insn(const IRInstruction* insn, bool deobfuscated) {
  if (insn == nullptr) {
    return "";
  }
  std::ostringstream ss;
  ss << show(insn->opcode()) << " ";
  bool first = true;
  if (insn->has_dest()) {
    ss << "v" << insn->dest();
    first = false;
  }
  for (unsigned i = 0; i < insn->srcs_size(); ++i) {
    if (!first) {
      ss << ", ";
    }
    ss << "v";
    ss << std::to_string(static_cast<unsigned int>(insn->src(i)));
    first = false;
  }
  if (opcode::ref(insn->opcode()) != opcode::Ref::None && !first) {
    ss << ", ";
  }
  switch (opcode::ref(insn->opcode())) {
  case opcode::Ref::None:
    break;
  case opcode::Ref::String:
    ss << boost::io::quoted(show(insn->get_string()));
    break;
  case opcode::Ref::Type:
    ss << (deobfuscated ? show_deobfuscated(insn->get_type())
                        : show(insn->get_type()));
    break;
  case opcode::Ref::Field:
    if (deobfuscated) {
      ss << show_deobfuscated(insn->get_field());
    } else {
      ss << show(insn->get_field());
    }
    break;
  case opcode::Ref::Method:
    if (deobfuscated) {
      ss << show_deobfuscated(insn->get_method());
    } else {
      ss << show(insn->get_method());
    }
    break;
  case opcode::Ref::Literal:
    ss << insn->get_literal();
    break;
  case opcode::Ref::Data:
    ss << "<data>"; // TODO: print something more informative
    break;
  case opcode::Ref::CallSite:
    if (deobfuscated) {
      ss << show_deobfuscated(insn->get_callsite());
    } else {
      ss << show(insn->get_callsite());
    }
    break;
  case opcode::Ref::MethodHandle:
    if (deobfuscated) {
      ss << show_deobfuscated(insn->get_methodhandle());
    } else {
      ss << show(insn->get_methodhandle());
    }
    break;
  case opcode::Ref::Proto:
    ss << show_proto(insn->get_proto(), deobfuscated);
    break;
  }
  return ss.str();
}

std::string show_helper(const DexAnnotation* anno, bool deobfuscated) {
  if (anno == nullptr) {
    return "";
  }
  std::ostringstream ss;
  ss << "type:" << show(anno->type()) << " visibility:" << show(anno->viz())
     << " annotations:";
  if (deobfuscated) {
    ss << show_deobfuscated(&anno->anno_elems());
  } else {
    ss << show(&anno->anno_elems());
  }
  return ss.str();
}

} // namespace

std::ostream& operator<<(std::ostream& o, const DexString& str) {
  o << str.c_str();
  return o;
}

// This format must match the proguard map format because it's used to look up
// in the proguard map
std::ostream& operator<<(std::ostream& o, const DexType& type) {
  o << *type.get_name();
  return o;
}

inline std::string show(const DexString* p) {
  if (p == nullptr) {
    return "";
  }
  return p->str_copy();
}

inline std::string show(const DexType* t) { return show_type(t, false); }

// This format must match the proguard map format because it's used to look up
// in the proguard map
std::string show(const DexFieldRef* ref) { return show_field(ref, false); }

std::ostream& operator<<(std::ostream& o, const DexFieldRef& p) {
  o << show(&p);
  return o;
}

std::string vshow(const DexField* p) {
  if (p == nullptr) {
    return "";
  }
  std::ostringstream ss;
  ss << accessibility(p->get_access()) << humanize(show(p->get_type())) << " "
     << humanize(show(p->get_class())) << "." << show(p->get_name());
  if (p->get_anno_set() != nullptr) {
    ss << "\n  annotations:" << show(p->get_anno_set());
  }
  return ss.str();
}

std::string vshow(const DexTypeList* p) {
  if (p == nullptr) {
    return "";
  }
  std::ostringstream ss;
  bool first = true;
  for (auto const& type : *p) {
    if (!first) {
      ss << ", ";
    } else {
      first = false;
    }
    ss << humanize(show(type));
  }
  return ss.str();
}

std::string vshow(const DexProto* p, bool include_ret_type = true) {
  if (p == nullptr) {
    return "";
  }
  std::ostringstream ss;
  ss << "(" << vshow(p->get_args()) << ")";
  if (include_ret_type) {
    ss << humanize(show(p->get_rtype()));
  }
  return ss.str();
}

// This format must match the proguard map format because it's used to look up
// in the proguard map
std::string show(const DexTypeList* l) { return show_type_list(l, false); }

// This format must match the proguard map format because it's used to look up
// in the proguard map
std::string show(const DexProto* p) { return show_proto(p, false); }

std::string show(const DexCode* code) {
  if (code == nullptr) {
    return "";
  }
  std::ostringstream ss;
  ss << "regs: " << code->get_registers_size()
     << ", ins: " << code->get_ins_size() << ", outs: " << code->get_outs_size()
     << "\n";
  if (code->m_insns) {
    for (auto const& insn : code->get_instructions()) {
      ss << show(insn) << "\n";
    }
  }
  return ss.str();
}

// This format must match the proguard map format because it's used to look up
// in the proguard map
std::string show(const DexMethodRef* ref) { return show_method(ref, false); }

std::string vshow(uint32_t acc, bool is_method) {
  return accessibility(acc, is_method);
}

std::string vshow(const DexType* t) { return humanize(show(t)); }

std::string vshow(const DexMethod* p, bool include_annotations /*=true*/) {
  if (p == nullptr) {
    return "";
  }
  std::ostringstream ss;
  ss << (p->is_def() ? accessibility(p->get_access(), true)
                     : std::string("(?)"))
     << vshow(p->get_proto()->get_rtype()) << " "
     << humanize(show(p->get_class())) << "." << show(p->get_name())
     << vshow(p->get_proto(), false);
  if (include_annotations) {
    if (p->get_anno_set() != nullptr) {
      ss << "\n  annotations:" << show(p->get_anno_set());
    }
    bool first = true;
    if (p->get_param_anno() != nullptr) {
      for (auto const& pair : *p->get_param_anno()) {
        if (first) {
          ss << "\n  param annotations:" << "\n";
          first = false;
        }
        ss << "    " << pair.first << ": " << show(pair.second) << "\n";
      }
    }
  }
  return ss.str();
}

// This format must match the proguard map format because it's used to look up
// in the proguard map
std::ostream& operator<<(std::ostream& o, const DexClass& cls) {
  o << *cls.get_type();
  return o;
}

std::string vshow(const DexClass* p) {
  if (p == nullptr) {
    return "";
  }
  std::ostringstream ss;
  ss << accessibility(p->get_access()) << humanize(show(p->get_type()))
     << " extends " << humanize(show(p->get_super_class()));
  if ((p->get_interfaces() != nullptr) && !p->get_interfaces()->empty()) {
    ss << " implements ";
    bool first = true;
    for (auto* const type : *p->get_interfaces()) {
      if (first) {
        first = false;
      } else {
        ss << ", ";
      }
      ss << humanize(show(type));
    }
  }
  if (p->get_anno_set() != nullptr) {
    ss << "\n  annotations:" << show(p->get_anno_set());
  }
  return ss.str();
}

std::string show(const DexEncodedValue* value) {
  if (value == nullptr) {
    return "";
  }
  return value->show();
}

std::string show(const DexAnnotation* anno) { return show_helper(anno, false); }

std::string show_deobfuscated(const DexAnnotation* anno) {
  return show_helper(anno, true);
}

std::string show(const DexAnnotationSet* p) {
  if (p == nullptr) {
    return "";
  }
  std::ostringstream ss;
  bool first = true;
  for (auto const& anno : p->get_annotations()) {
    if (!first) {
      ss << ", ";
    }
    ss << show(anno.get());
    first = false;
  }
  return ss.str();
}

std::string show(const DexAnnotationDirectory* p) {
  if (p == nullptr) {
    return "";
  }
  std::ostringstream ss;
  if (p->m_class != nullptr) {
    ss << "class annotations:\n" << show(p->m_class) << "\n";
  }
  if (p->m_field) {
    ss << "field annotations:\n";
    for (auto const& pair : *p->m_field) {
      ss << show(pair.first->get_name()) << ": " << show(pair.second) << "\n";
    }
  }
  if (p->m_method) {
    ss << "method annotations:\n";
    for (auto const& pair : *p->m_method) {
      ss << show(pair.first->get_name()) << ": " << show(pair.second) << "\n";
    }
  }
  if (p->m_method_param) {
    ss << "method parameter annotations:\n";
    for (auto const& pair : *p->m_method_param) {
      ss << show(pair.first->get_name());
      for (auto const& parampair : *pair.second) {
        ss << "  " << parampair.first << ": " << show(parampair.second) << "\n";
      }
    }
  }
  return ss.str();
}

std::string show(IROpcode opcode) {
  switch (opcode) {
#define OP(op, ...) \
  case OPCODE_##op: \
    return #op;
#define IOP(op, ...) \
  case IOPCODE_##op: \
    return "IOPCODE_" #op;
#define OPRANGE(...)
#include "IROpcodes.def"
  }
  not_reached_log("Unknown opcode 0x%x", opcode);
}

std::string show(DexOpcode opcode) {
  switch (opcode) {
#define OP(op, ...)  \
  case DOPCODE_##op: \
    return #op;
  DOPS
#undef OP
      case FOPCODE_PACKED_SWITCH:
    return "PACKED_SWITCH_DATA";
  case FOPCODE_SPARSE_SWITCH:
    return "SPARSE_SWITCH_DATA";
  case FOPCODE_FILLED_ARRAY:
    return "FILLED_ARRAY_DATA";
    SWITCH_FORMAT_QUICK_FIELD_REF
    SWITCH_FORMAT_QUICK_METHOD_REF
    SWITCH_FORMAT_RETURN_VOID_NO_BARRIER { not_reached(); }
  }
}

// Read n_bytes bytes from data into an integral value of type
// IntType while also incrementing the data pointer by n_bytes bytes.
// n_bytes should be less than sizeof(IntType)
template <typename IntType>
static IntType read(const uint8_t*& data, uint16_t n_bytes) {
  static_assert(std::is_integral<IntType>::value,
                "Only read into integral values.");
  always_assert_log(sizeof(IntType) >= n_bytes,
                    "Should not read more bytes than sizeof(IntType)");
  IntType result = 0;
  memcpy(&result, data, n_bytes);
  data += n_bytes;
  return result;
}

std::string show(const DexOpcodeData* insn) {
  if (insn == nullptr) {
    return "";
  }
  std::ostringstream ss;
  ss << "{ ";
  const auto* data = insn->data();
  switch (insn->opcode()) {
  case FOPCODE_SPARSE_SWITCH: {
    // See format at
    // https://source.android.com/devices/tech/dalvik/dalvik-bytecode#sparse-switch
    const uint16_t entries = *data++;
    const uint16_t* tdata = data + static_cast<ptrdiff_t>(2 * entries);

    const uint8_t* data_ptr = reinterpret_cast<const uint8_t*>(data);
    const uint8_t* tdata_ptr = reinterpret_cast<const uint8_t*>(tdata);
    for (size_t i = 0; i < entries; i++) {
      if (i != 0) {
        ss << ", ";
      }
      int32_t case_key = read<int32_t>(data_ptr, sizeof(int32_t));
      uint32_t target_offset = read<uint32_t>(tdata_ptr, sizeof(uint32_t));
      ss << case_key << "->" << target_offset;
    }
    break;
  }
  case FOPCODE_PACKED_SWITCH: {
    // See format at
    // https://source.android.com/devices/tech/dalvik/dalvik-bytecode#packed-switch
    const uint16_t entries = *data++;
    const uint8_t* data_ptr = reinterpret_cast<const uint8_t*>(data);
    int32_t case_key = read<int32_t>(data_ptr, sizeof(int32_t));
    for (size_t i = 0; i < entries; i++) {
      if (i != 0) {
        ss << ", ";
      }
      uint32_t target_offset = read<uint32_t>(data_ptr, sizeof(uint32_t));
      ss << case_key++ << "->" << target_offset;
    }
    break;
  }
  case FOPCODE_FILLED_ARRAY: {
    // See format at
    // https://source.android.com/devices/tech/dalvik/dalvik-bytecode#fill-array
    const uint16_t ewidth = *data++;
    const uint32_t element_count = *reinterpret_cast<const uint32_t*>(data);
    ss << "[" << element_count << " x " << ewidth << "] {";
    auto vec = pretty_array_data_payload(ewidth, element_count, insn->data());
    bool first{true};
    for (const auto& s : vec) {
      if (!first) {
        ss << ",";
      }
      ss << " " << s;
      first = false;
    }
    ss << " }";
    break;
  }
  default:
    // should not get here
    ss << "unknown_payload";
    break;
  }
  ss << " }";
  return ss.str();
}

std::string show_insn(const DexInstruction* insn, bool deobfuscated) {
  if (insn == nullptr) {
    return "";
  }
  std::ostringstream ss;
  ss << show_opcode(insn, deobfuscated);
  if (dex_opcode::is_fopcode(insn->opcode())) {
    ss << " " << show(dynamic_cast<const DexOpcodeData*>(insn));
    return ss.str();
  }

  bool first = true;
  if (insn->has_dest()) {
    ss << " v" << insn->dest();
    first = false;
  }
  for (unsigned i = 0; i < insn->srcs_size(); ++i) {
    if (!first) {
      ss << ",";
    }
    const uint32_t src_value = static_cast<uint32_t>(insn->src(i));
    ss << " v" << src_value;
    first = false;
  }
  if (dex_opcode::has_literal(insn->opcode())) {
    if (!first) {
      ss << ",";
    }
    ss << " " << insn->get_literal();
    first = false;
  }
  return ss.str();
}

std::string show(const IRInstruction* insn) { return show_insn(insn, false); }

std::string show(const DexInstruction* insn) { return show_insn(insn, false); }

std::ostream& operator<<(std::ostream& o, const IRInstruction& insn) {
  o << show(&insn);
  return o;
}

std::string show(const DexDebugInstruction* insn) {
  if (insn == nullptr) {
    return "";
  }
  std::ostringstream ss;
  switch (insn->opcode()) {
  case DBG_END_SEQUENCE:
    ss << "DBG_END_SEQUENCE";
    break;
  case DBG_ADVANCE_PC:
    ss << "DBG_ADVANCE_PC " << insn->uvalue();
    break;
  case DBG_ADVANCE_LINE:
    ss << "DBG_ADVANCE_LINE " << insn->value();
    break;
  case DBG_START_LOCAL: {
    const auto* sl = dynamic_cast<const DexDebugOpcodeStartLocal*>(insn);
    ss << "DBG_START_LOCAL v" << sl->uvalue() << " " << show(sl->name()) << ":"
       << show(sl->type());
    break;
  }
  case DBG_START_LOCAL_EXTENDED: {
    const auto* sl = dynamic_cast<const DexDebugOpcodeStartLocal*>(insn);
    ss << "DBG_START_LOCAL v" << sl->uvalue() << " " << show(sl->name()) << ":"
       << show(sl->type()) << ";" << show(sl->sig());
    break;
  }
  case DBG_END_LOCAL:
    ss << "DBG_END_LOCAL v" << insn->uvalue();
    break;
  case DBG_RESTART_LOCAL:
    ss << "DBG_RESTART_LOCAL v" << insn->uvalue();
    break;
  case DBG_SET_PROLOGUE_END:
    ss << "DBG_SET_PROLOGUE_END";
    break;
  case DBG_SET_EPILOGUE_BEGIN:
    ss << "DBG_SET_EPILOGUE_BEGIN";
    break;
  case DBG_SET_FILE: {
    const auto* sf = dynamic_cast<const DexDebugOpcodeSetFile*>(insn);
    ss << "DBG_SET_FILE " << show(sf->file());
    break;
  }
  default: {
    auto adjusted_opcode = insn->opcode() - DBG_FIRST_SPECIAL;
    auto line = DBG_LINE_BASE + (adjusted_opcode % DBG_LINE_RANGE);
    auto address = (adjusted_opcode / DBG_LINE_RANGE);
    ss << "DBG_SPECIAL line+=" << line << " addr+=" << address;
  }
  }
  return ss.str();
}

std::ostream& operator<<(std::ostream& o, const DexPosition& pos) {
  if (pos.method != nullptr) {
    o << *pos.method;
  } else {
    o << "Unknown method";
  }
  o << "(";
  if (pos.file == nullptr) {
    o << "Unknown source";
  } else {
    o << *pos.file;
  }
  o << ":" << pos.line << ")";
  if (pos.parent != nullptr) {
    o << " [parent: " << pos.parent << "]";
  }
  return o;
}

std::string show(const DexDebugEntry* entry) {
  std::ostringstream ss;
  ss << std::hex;
  switch (entry->type) {
  case DexDebugEntryType::Instruction:
    ss << "INSTRUCTION: [0x" << entry->addr << "] " << show(entry->insn);
    break;
  case DexDebugEntryType::Position:
    ss << "POSITION: [0x" << entry->addr << "] " << show(entry->pos);
    break;
  }
  return ss.str();
}

std::string show(TryEntryType t) {
  switch (t) {
  case TRY_START:
    return "TRY_START";
  case TRY_END:
    return "TRY_END";
  }
}

std::string show(const SwitchIndices& si) {
  std::ostringstream ss;
  for (auto index : si) {
    ss << index << " ";
  }
  return ss.str();
}

std::string show_mie_plain(const MethodItemEntry& mie) {
  std::ostringstream o;
  switch (mie.type) {
  case MFLOW_OPCODE:
    o << "OPCODE: " << show(mie.insn);
    break;
  case MFLOW_DEX_OPCODE:
    o << "DEX_OPCODE: " << show(mie.dex_insn);
    break;
  case MFLOW_TARGET:
    if (mie.target->type == BRANCH_MULTI) {
      o << "TARGET: MULTI " << mie.target->case_key << " ";
    } else {
      o << "TARGET: SIMPLE ";
    }
    o << mie.target->src;
    break;
  case MFLOW_TRY:
    o << "TRY: " << show(mie.tentry->type) << " " << mie.tentry->catch_start;
    break;
  case MFLOW_CATCH:
    o << "CATCH: " << show(mie.centry->catch_type);
    if (mie.centry->next != nullptr) {
      o << " (next " << mie.centry->next << ")";
    }
    break;
  case MFLOW_DEBUG:
    o << "DEBUG: " << show(mie.dbgop);
    break;
  case MFLOW_POSITION:
    o << "POSITION: " << *mie.pos;
    break;
  case MFLOW_SOURCE_BLOCK:
    o << "SOURCE-BLOCKS: " << mie.src_block->show();
    break;
  case MFLOW_REMARK:
    o << "REMARK: " << show(mie.remark->producer) << " "
      << show(mie.remark->val_str) << " " << mie.remark->val_int;
    break;
  case MFLOW_FALLTHROUGH:
    o << "FALLTHROUGH";
    break;
  }
  return o.str();
}

std::ostream& operator<<(std::ostream& o, const MethodItemEntry& mie) {
  o << "[" << &mie << "] " << show_mie_plain(mie);
  return o;
}

std::ostream& operator<<(std::ostream& o, const DexMethodHandle& mh) {
  o << "[" << &mh << "] ";
  o << "METHODHANDLE: TYPE=" << show(mh.type());
  o << " FIELD_OR_METHOD_ID=";
  if (DexMethodHandle::isInvokeType(mh.type())) {
    o << show(mh.methodref());
  } else {
    o << show(mh.fieldref());
  }
  return o;
}

std::ostream& operator<<(std::ostream& o, const DexCallSite& cs) {
  o << "[" << &cs << "] ";
  o << "CALLSITE: METHODHANDLE=" << show(cs.method_handle());
  o << " METHODNAME=" << show(cs.method_name());
  o << " METHODTYPE=" << show(cs.method_type());
  return o;
}

std::string show(const IRList* ir, bool code_only) {
  std::string ret;
  for (auto const& mie : *ir) {
    if (!code_only || shown_in_code_only(mie.type)) {
      ret += show(mie);
      ret += "\n";
    }
  }
  return ret;
}

namespace {

struct NoneSpecial {
  std::string show_mie(const MethodItemEntry& mie) const { return show(mie); }

  void mie_before(std::ostream&, const MethodItemEntry&) {}
  void mie_after(std::ostream&, const MethodItemEntry&) {}
  void start_block(std::ostream&, const cfg::Block*) {}
  void end_block(std::ostream&, const cfg::Block*) {}
};

} // namespace

std::string show(const cfg::Block* block, bool code_only) {
  NoneSpecial nothing{};
  return show(block, nothing, code_only);
}

std::string show(const cfg::ControlFlowGraph& cfg, bool code_only) {
  NoneSpecial nothing{};
  return show(cfg, nothing, code_only);
}

std::string show(const MethodCreator* mc) {
  if (mc == nullptr) {
    return "";
  }
  std::ostringstream ss;
  ss << "MethodCode for " << SHOW(mc->method) << "\n";
  ss << "locals: ";
  for (const auto& loc : mc->locals) {
    ss << "[" << loc.get_reg() << "] " << SHOW(loc.get_type());
  }
  ss << "\ninstructions:\n";
  ss << show(mc->main_block);
  return ss.str();
}

std::string show(const MethodBlock* block) {
  if (block == nullptr) {
    return "";
  }
  std::ostringstream ss;
  return ss.str();
}

std::string show(DexIdx* p) {
  std::ostringstream ss;
  ss << "----------------------------------------\n"
     << "strings\n"
     << "----------------------------------------\n";
  for (uint32_t i = 0; i < p->m_string_ids_size; i++) {
    always_assert(i < p->m_string_cache.size());
    // NOLINTNEXTLINE(facebook-hte-ParameterUncheckedArrayBounds)
    ss << show(p->m_string_cache[i]) << "\n";
  }
  ss << "----------------------------------------\n"
     << "types\n"
     << "----------------------------------------\n";
  for (uint32_t i = 0; i < p->m_type_ids_size; i++) {
    always_assert(i < p->m_type_cache.size());
    // NOLINTNEXTLINE(facebook-hte-ParameterUncheckedArrayBounds)
    ss << show(p->m_type_cache[i]) << "\n";
  }
  ss << "----------------------------------------\n"
     << "fields\n"
     << "----------------------------------------\n";
  for (uint32_t i = 0; i < p->m_field_ids_size; i++) {
    always_assert(i < p->m_field_cache.size());
    // NOLINTNEXTLINE(facebook-hte-ParameterUncheckedArrayBounds)
    ss << show(p->m_field_cache[i]) << "\n";
  }
  ss << "----------------------------------------\n"
     << "methods\n"
     << "----------------------------------------\n";
  for (uint32_t i = 0; i < p->m_method_ids_size; i++) {
    always_assert(i < p->m_method_cache.size());
    // NOLINTNEXTLINE(facebook-hte-ParameterUncheckedArrayBounds)
    ss << show(p->m_method_cache[i]) << "\n";
  }
  return ss.str();
}

std::string show(const IRCode* mt, bool code_only) {
  return mt->cfg_built() ? show(mt->cfg(), code_only)
                         : show(mt->m_ir_list.get(), code_only);
}

std::string show(const ir_list::InstructionIterable& it) {
  std::ostringstream ss;
  for (auto& mei : it) {
    ss << show(mei.insn) << "\n";
  }
  return ss.str();
}

std::string show_context(IRCode const* code, IRInstruction const* insn) {
  std::ostringstream ss;
  auto iter = code->begin();
  while ((*iter).insn != insn) {
    always_assert(iter != code->end());
    iter++;
  }
  for (int i = 0; i < 6 && iter != code->begin(); i++) {
    iter--;
  }
  for (int i = 0; i < 11 && iter != code->end(); i++) {
    ss << SHOW(*iter++) << '\n';
  }
  return ss.str();
}

std::string show_deobfuscated(const DexClass* cls) {
  if (cls == nullptr) {
    return "";
  }
  const auto& deob = cls->get_deobfuscated_name_or_empty();
  if (!deob.empty()) {
    return str_copy(deob);
  }
  return cls->get_name() != nullptr ? cls->get_name()->str_copy() : show(cls);
}

std::string show_deobfuscated(const DexFieldRef* ref) {
  return show_field(ref, true);
}

std::string show_deobfuscated(const DexMethodRef* ref) {
  return show_method(ref, true);
}

std::string show_deobfuscated(const IRInstruction* insn) {
  return show_insn(insn, true);
}

std::string show_deobfuscated(const DexInstruction* insn) {
  return show_insn(insn, true);
}

std::string show_deobfuscated(const DexEncodedValue* ev) {
  if (ev == nullptr) {
    return "";
  }
  return ev->show_deobfuscated();
}

std::string show_deobfuscated(const DexType* t) { return show_type(t, true); }

std::string show_deobfuscated(const DexTypeList* l) {
  return show_type_list(l, true);
}

std::string show_deobfuscated(const DexProto* p) { return show_proto(p, true); }

std::string show_deobfuscated(const DexCallSite* callsite) {
  if (callsite == nullptr) {
    return "";
  }
  // TODO(T58570881) - actually deobfuscate
  return SHOW(callsite);
}

std::string show_deobfuscated(const DexMethodHandle* methodhandle) {
  if (methodhandle == nullptr) {
    return "";
  }
  // TODO(T58570881) - actually deobfuscate
  return SHOW(methodhandle);
}

std::string pretty_bytes(uint64_t val) {
  size_t divisions = 0;
  double d_val = static_cast<double>(val);
  while (d_val > 1024 && divisions < 3) {
    d_val /= 1024;
    ++divisions;
  }

  const char* modifier;
  switch (divisions) {
  case 0:
    modifier = "";
    break;
  case 1:
    modifier = "k";
    break;
  case 2:
    modifier = "M";
    break;
  case 3:
    modifier = "G";
    break;
  default:
    modifier = "Error";
    break;
  }

  std::ostringstream oss;
  oss << std::setiosflags(std::ios::fixed) << std::setprecision(2) << d_val
      << " " << modifier << "B";
  return oss.str();
}

namespace {
static bool is_control_character(const uint32_t c) {
  return c <= 0x1F || c == 0x7F || (c >= 0x80 && c <= 0x9F);
}

std::string escape_string(const char* ptr) {
  std::ostringstream oss;
  while (*ptr != '\0') {
    uint32_t unit = mutf8_next_code_point(ptr);
    if (is_control_character(unit)) {
      oss << "\\u" << std::setfill('0') << std::setw(4) << std::hex << unit;
    } else {
      char32_t code_point = unit;
      // Despite the name "mutf8_next_code_point" does not return code points,
      // it returns code units. Munge together surrogate pairs if need be.
      if (unit >= 0xD800 && unit <= 0xDFFF) {
        code_point = (unit - 0xD800) * 0x400;
        uint32_t low_unit = mutf8_next_code_point(ptr);
        always_assert_log(low_unit != '\0', "Unpaired surrogate");
        code_point += low_unit - 0xDC00;
        code_point += 0x10000;
      }
      std::string result =
          boost::locale::conv::utf_to_utf<char>(&code_point, &code_point + 1);
      oss << result;
    }
  }
  return oss.str();
}
} // namespace

std::string show_escaped(const DexString* s) {
  if (s == nullptr) {
    return "";
  }
  return escape_string(s->c_str());
}

std::vector<std::string> pretty_array_data_payload(const uint16_t ewidth,
                                                   const uint32_t element_count,
                                                   const uint16_t* data) {
  std::vector<std::string> result;
  result.reserve(element_count);
  const uint8_t* data_ptr = reinterpret_cast<const uint8_t*>(data + 3);
  for (size_t i = 0; i < element_count; i++) {
    auto xx = read<uint64_t>(data_ptr, ewidth);
    std::ostringstream oss;
    oss << std::hex << xx;
    result.emplace_back(oss.str());
  }
  return result;
}
