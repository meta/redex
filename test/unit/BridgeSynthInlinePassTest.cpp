/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "BridgeSynthInlinePass.h"
#include "BridgeSynthInlineInternal.h"

#include <gtest/gtest.h>

#include "ConfigFiles.h"
#include "ControlFlow.h"
#include "Creators.h"
#include "DexClass.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "PassManager.h"
#include "RedexTest.h"
#include "Show.h"
#include "TypeUtil.h"

class BridgeSynthInlinePassTest : public RedexTest {
 protected:
  // Returns a synthetic bridge whose body is `invoke-super Parent.foo()`;
  // parent + abstract method are registered as a side effect.
  DexMethod* make_synthetic_bridge_with_invoke_super_to_abstract(
      const std::string& parent_type_name, const std::string& child_type_name) {
    auto* foo_proto =
        DexProto::make_proto(type::_void(), DexTypeList::make_type_list({}));

    auto* parent_ty = DexType::make_type(parent_type_name);
    ClassCreator parent_cc(parent_ty);
    parent_cc.set_super(type::java_lang_Object());
    parent_cc.set_access(ACC_PUBLIC | ACC_ABSTRACT);
    auto* parent_foo = DexMethod::make_method(
                           parent_ty, DexString::make_string("foo"), foo_proto)
                           ->make_concrete(ACC_PUBLIC | ACC_ABSTRACT,
                                           /* is_virtual */ true);
    parent_cc.add_method(parent_foo);
    parent_cc.create();

    auto* child_ty = DexType::make_type(child_type_name);
    ClassCreator child_cc(child_ty);
    child_cc.set_super(parent_ty);
    auto* child_foo =
        DexMethod::make_method(
            child_ty, DexString::make_string("foo"), foo_proto)
            ->make_concrete(ACC_PUBLIC | ACC_BRIDGE | ACC_SYNTHETIC,
                            /* is_virtual */ true);
    child_foo->set_code(assembler::ircode_from_string(R"(
      (
        (load-param-object v0)
        (invoke-super (v0) ")" + parent_type_name + R"(.foo:()V")
        (return-void)
      )
    )"));
    child_cc.add_method(child_foo);
    child_cc.create();

    // Mirror the cfg-friendly pass contract that PassManager would set up.
    child_foo->get_code()->build_cfg();
    return child_foo;
  }

  static bool body_contains_opcode(IRCode* code, IROpcode op) {
    for (const auto& mie : cfg::InstructionIterable(code->cfg())) {
      if (mie.insn->opcode() == op) {
        return true;
      }
    }
    return false;
  }

  static bool body_throws_abstract_method_error(IRCode* code) {
    auto* ame = DexType::get_type("Ljava/lang/AbstractMethodError;");
    bool has_new_ame = false;
    bool has_throw = false;
    for (const auto& mie : cfg::InstructionIterable(code->cfg())) {
      auto* insn = mie.insn;
      if (insn->opcode() == OPCODE_NEW_INSTANCE && insn->get_type() == ame) {
        has_new_ame = true;
      }
      if (insn->opcode() == OPCODE_THROW) {
        has_throw = true;
      }
    }
    return has_new_ame && has_throw;
  }
};

TEST_F(BridgeSynthInlinePassTest,
       rewrites_synthetic_bridge_invoke_super_to_abstract) {
  auto* bridge = make_synthetic_bridge_with_invoke_super_to_abstract(
      "LBaselineParent;", "LBaselineChild;");

  ASSERT_TRUE(is_bridge(bridge));
  ASSERT_TRUE(body_contains_opcode(bridge->get_code(), OPCODE_INVOKE_SUPER));

  EXPECT_TRUE(
      bridge_synth_inline_internal::rewrite_bridge_with_abstract_super_target(
          bridge));

  EXPECT_TRUE(body_throws_abstract_method_error(bridge->get_code()));
  EXPECT_FALSE(body_contains_opcode(bridge->get_code(), OPCODE_INVOKE_SUPER));
}

TEST_F(BridgeSynthInlinePassTest, honors_no_optimizations_flag) {
  auto* bridge = make_synthetic_bridge_with_invoke_super_to_abstract(
      "LNoOptParent;", "LNoOptChild;");

  bridge->rstate.set_no_optimizations();

  EXPECT_FALSE(
      bridge_synth_inline_internal::rewrite_bridge_with_abstract_super_target(
          bridge));

  EXPECT_TRUE(body_contains_opcode(bridge->get_code(), OPCODE_INVOKE_SUPER));
  EXPECT_FALSE(body_throws_abstract_method_error(bridge->get_code()));
}

// A synthetic constructor that only calls a super constructor is
// relaxed-inlined: its caller then initializes the object with the super
// constructor, and the synthetic constructor is deleted.
TEST_F(BridgeSynthInlinePassTest, relaxed_inlines_synthetic_ctor) {
  auto* base_cls = assembler::class_from_string(R"(
    (class (public) "LBase;"
      (method (public constructor) "LBase;.<init>:()V"
        (
          (load-param-object v0)
          (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
          (return-void)
        )
      )
    )
  )");
  auto* foo_cls = assembler::class_from_string(R"(
    (class (public) "LFoo;" extends "LBase;"
      (method (public constructor synthetic) "LFoo;.<init>:(I)V"
        (
          (load-param-object v0)
          (load-param v1)
          (invoke-direct (v0) "LBase;.<init>:()V")
          (return-void)
        )
      )
    )
  )");
  auto* bar_cls = assembler::class_from_string(R"(
    (class (public) "LBar;"
      (method (public static) "LBar;.make:()Ljava/lang/Object;"
        (
          (const v0 0)
          (new-instance "LFoo;")
          (move-result-pseudo-object v1)
          (invoke-direct (v1 v0) "LFoo;.<init>:(I)V")
          (return-object v1)
        )
      )
    )
  )");
  DexStoresVector stores;
  DexStore store("root");
  store.add_classes({base_cls, foo_cls, bar_cls});
  stores.push_back(std::move(store));
  Json::Value config;
  config["inliner"]["relaxed_init_inline"] = true;
  ConfigFiles conf(config);
  conf.parse_global_config();
  RedexOptions options;
  options.min_sdk = 21;
  BridgeSynthInlinePass pass;
  PassManager manager({&pass}, conf, options);
  manager.run_passes(stores, conf);

  EXPECT_TRUE(foo_cls->get_ctors().empty());
  auto* make = bar_cls->get_dmethods().front();
  make->get_code()->build_cfg();
  std::vector<std::string> invoked;
  for (const auto& mie : cfg::InstructionIterable(make->get_code()->cfg())) {
    if (mie.insn->has_method()) {
      invoked.push_back(show(mie.insn->get_method()));
    }
  }
  EXPECT_EQ(invoked, std::vector<std::string>{"LBase;.<init>:()V"});
}
