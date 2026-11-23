/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "Creators.h"
#include "DelSuper.h"
#include "DexClass.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "PassManager.h"
#include "RedexTest.h"
#include "Show.h"
#include "TypeUtil.h"

namespace {

DexMethod* make_vmethod(const char* signature, const char* body) {
  auto* method =
      DexMethod::make_method(signature)->make_concrete(ACC_PUBLIC, true);
  method->set_code(assembler::ircode_from_string(body));
  return method;
}

DexClass* make_class(const char* name,
                     DexType* super,
                     const std::vector<DexType*>& interfaces,
                     const std::vector<DexMethod*>& methods,
                     DexAccessFlags access = ACC_PUBLIC) {
  ClassCreator creator(DexType::make_type(name));
  creator.set_access(access);
  creator.set_super(super);
  for (auto* intf : interfaces) {
    creator.add_interface(intf);
  }
  for (auto* method : methods) {
    creator.add_method(method);
  }
  return creator.create();
}

class DelSuperTest : public RedexTest {
 protected:
  void run_pass(const std::vector<DexClass*>& classes) {
    DelSuperPass pass;
    PassManager manager({&pass});
    // Apps that keep default methods (min SDK 24 and up) turn this check off,
    // since their input contains invoke-super of program default methods.
    Json::Value json;
    json["ir_type_checker"]["validate_invoke_super"] = false;
    ConfigFiles config(json);
    config.parse_global_config();
    DexStore store("classes");
    store.add_classes(classes);
    std::vector<DexStore> stores;
    stores.emplace_back(std::move(store));
    manager.run_passes(stores, config);
  }

  static bool declares(const DexClass* cls, const DexMethod* method) {
    const auto& vmethods = cls->get_vmethods();
    return std::find(vmethods.begin(), vmethods.end(), method) !=
           vmethods.end();
  }

  static std::string callee(DexMethod* caller) {
    for (const auto& mie : InstructionIterable(caller->get_code())) {
      if (opcode::is_a_method_invoke(mie.insn->opcode())) {
        return show(mie.insn->get_method());
      }
    }
    return "";
  }
};

// class A { int m() { return 2; } }
// class B extends A { int m() { return super.m(); } }
//
// B inherits A.m once B.m is gone, so B.m can go and calls of B.m become
// calls of A.m.
TEST_F(DelSuperTest, classSuperForwarderIsDeleted) {
  create_object_class();
  auto* a_m = make_vmethod("LA;.m:()I", R"(
    ((load-param-object v0) (const v1 2) (return v1))
  )");
  auto* b_m = make_vmethod("LB;.m:()I", R"(
    (
      (load-param-object v0)
      (invoke-super (v0) "LA;.m:()I")
      (move-result v1)
      (return v1)
    )
  )");
  auto* call = DexMethod::make_method("LCaller;.call:(LB;)I")
                   ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  call->set_code(assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (invoke-virtual (v0) "LB;.m:()I")
      (move-result v1)
      (return v1)
    )
  )"));
  auto* a = make_class("LA;", type::java_lang_Object(), {}, {a_m});
  auto* b = make_class("LB;", a->get_type(), {}, {b_m});
  auto* caller = make_class("LCaller;", type::java_lang_Object(), {}, {call});

  run_pass({a, b, caller});

  EXPECT_FALSE(declares(b, b_m));
  EXPECT_EQ(callee(call), "LA;.m:()I");
}

// interface I { default int m() { return 1; } }
// class A { int m() { return 2; } }
// class B extends A implements I { int m() { return I.super.m(); } }
//
// Without B.m, B inherits A.m, not I.m: a call on a B would return 2 instead
// of 1. Rewriting `invoke-virtual B.m` to `invoke-virtual I.m` would also
// fail at runtime with IncompatibleClassChangeError.
TEST_F(DelSuperTest, interfaceSuperForwarderIsKept) {
  create_object_class();
  auto* i_m = make_vmethod("LI;.m:()I", R"(
    ((load-param-object v0) (const v1 1) (return v1))
  )");
  auto* a_m = make_vmethod("LA;.m:()I", R"(
    ((load-param-object v0) (const v1 2) (return v1))
  )");
  auto* b_m = make_vmethod("LB;.m:()I", R"(
    (
      (load-param-object v0)
      (invoke-super (v0) "LI;.m:()I")
      (move-result v1)
      (return v1)
    )
  )");
  auto* call = DexMethod::make_method("LCaller;.call:(LB;)I")
                   ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  call->set_code(assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (invoke-virtual (v0) "LB;.m:()I")
      (move-result v1)
      (return v1)
    )
  )"));
  auto* i = make_class("LI;", type::java_lang_Object(), {}, {i_m},
                       ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  auto* a = make_class("LA;", type::java_lang_Object(), {}, {a_m});
  auto* b = make_class("LB;", a->get_type(), {i->get_type()}, {b_m});
  auto* caller = make_class("LCaller;", type::java_lang_Object(), {}, {call});

  run_pass({i, a, b, caller});

  EXPECT_TRUE(declares(b, b_m));
  EXPECT_EQ(callee(call), "LB;.m:()I");
}

} // namespace
