/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "RedexTestUtils.h"

#include "Debug.h"
#include "DexCallSite.h"
#include "DexClass.h"
#include "DexMethodHandle.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "RedexContext.h"
#include "Show.h"

#include <iostream>

namespace redex {
bool are_files_equal(const std::string& p1, const std::string& p2) {
  std::ifstream f1(p1, std::ifstream::binary | std::ifstream::ate);
  std::ifstream f2(p2, std::ifstream::binary | std::ifstream::ate);
  always_assert_log(!f1.fail(), "Failed to read path %s", p1.c_str());
  always_assert_log(!f2.fail(), "Failed to read path %s", p2.c_str());
  if (f1.tellg() != f2.tellg()) {
    std::cerr << "File length mismatch. " << f1.tellg() << " != " << f2.tellg()
              << "\n";
    return false;
  }
  f1.seekg(0, std::ifstream::beg);
  f2.seekg(0, std::ifstream::beg);
  return std::equal(std::istreambuf_iterator<char>(f1.rdbuf()),
                    std::istreambuf_iterator<char>(),
                    std::istreambuf_iterator<char>(f2.rdbuf()));
}

std::map<std::string, std::vector<std::string>> show_instructions_by_method(
    const std::vector<DexClass*>& classes) {
  std::map<std::string, std::vector<std::string>> result;
  for (const auto* cls : classes) {
    for (const auto* method : cls->get_all_methods()) {
      const auto* code = method->get_code();
      if (code == nullptr) {
        continue;
      }
      always_assert(!code->cfg_built());
      auto& instructions = result[show(method)];
      for (const auto& mie : InstructionIterable(code)) {
        instructions.push_back(show(mie.insn));
      }
    }
  }
  return result;
}

DexMethodHandle* make_method_handle(MethodHandleType type,
                                    std::string_view ref) {
  return DexMethodHandle::isInvokeType(type)
             ? DexMethodHandle::make_method_handle(type,
                                                   DexMethod::make_method(ref))
             : DexMethodHandle::make_method_handle(type,
                                                   DexField::make_field(ref));
}

namespace {

// The descriptor of the bootstrap method parameter that receives `arg`.
std::string_view bootstrap_parameter_descriptor(const DexEncodedValue& arg) {
  switch (arg.evtype()) {
  case DEVT_INT:
    return "I";
  case DEVT_LONG:
    return "J";
  case DEVT_FLOAT:
    return "F";
  case DEVT_DOUBLE:
    return "D";
  case DEVT_STRING:
    return "Ljava/lang/String;";
  case DEVT_TYPE:
    return "Ljava/lang/Class;";
  case DEVT_METHOD_TYPE:
    return "Ljava/lang/invoke/MethodType;";
  case DEVT_METHOD_HANDLE:
    return "Ljava/lang/invoke/MethodHandle;";
  case DEVT_BYTE:
  case DEVT_SHORT:
  case DEVT_CHAR:
  case DEVT_FIELD:
  case DEVT_METHOD:
  case DEVT_ENUM:
  case DEVT_ARRAY:
  case DEVT_ANNOTATION:
  case DEVT_NULL:
  case DEVT_BOOLEAN:
    break;
  }
  not_reached_log("%s cannot be a bootstrap argument", arg.show().c_str());
}

} // namespace

DexCallSite* make_callsite(std::string_view method_name,
                           std::string_view method_type,
                           std::vector<std::unique_ptr<DexEncodedValue>> args) {
  std::string bootstrap =
      "LBoot;.bootstrap:(Ljava/lang/invoke/MethodHandles$Lookup;"
      "Ljava/lang/String;Ljava/lang/invoke/MethodType;";
  for (const auto& arg : args) {
    bootstrap += bootstrap_parameter_descriptor(*arg);
  }
  bootstrap += ")Ljava/lang/invoke/CallSite;";
  auto* callsite = new DexCallSite(
      make_method_handle(METHOD_HANDLE_TYPE_INVOKE_STATIC, bootstrap),
      DexString::make_string(method_name), DexProto::make_proto(method_type),
      std::move(args));
  g_redex->publish_callsite(callsite);
  return callsite;
}

DexCallSite* make_invoke_custom(
    IRCode* code,
    std::string_view method_name,
    std::string_view method_type,
    std::vector<std::unique_ptr<DexEncodedValue>> args) {
  always_assert(!code->cfg_built());
  auto* callsite = make_callsite(method_name, method_type, std::move(args));
  size_t converted{0};
  for (auto& mie : InstructionIterable(code)) {
    if (mie.insn->opcode() != OPCODE_INVOKE_STATIC) {
      continue;
    }
    // The registers were laid out for the placeholder's arguments.
    always_assert_log(mie.insn->get_method()->get_proto()->get_args() ==
                          callsite->method_type()->get_args(),
                      "%s does not take the arguments of %s", SHOW(mie.insn),
                      SHOW(callsite->method_type()));
    mie.insn->set_opcode(OPCODE_INVOKE_CUSTOM)->set_callsite(callsite);
    ++converted;
  }
  always_assert_log(converted > 0,
                    "no invoke-static to turn into invoke-custom");
  return callsite;
}
} // namespace redex
