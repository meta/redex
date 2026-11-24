/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "MethodUtil.h"

#include "Creators.h"
#include "IRAssembler.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"
#include "TypeUtil.h"

class MethodUtilTest : public RedexTest {};

TEST_F(MethodUtilTest, test_count_opcodes) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v1 1)
      (const v2 2)
      (const v3 3)
      (const v4 4)
      (const v5 5)
      (const v6 6)
    )
  )");

  EXPECT_EQ(6, method::count_opcode_of_types(code.get(), {OPCODE_CONST}));
  code->build_cfg();
  EXPECT_EQ(6, method::count_opcode_of_types(code->cfg(), {OPCODE_CONST}));
  EXPECT_EQ(
      6,
      method::count_opcode_of_types(code->cfg().entry_block(), {OPCODE_CONST}));
  code->clear_cfg();
}

TEST_F(MethodUtilTest, can_change_signature) {
  auto make = [](const char* signature, DexAccessFlags access) {
    return DexMethod::make_method(signature)->make_concrete(access, false);
  };
  auto* plain = make("LA;.plain:()V", ACC_PUBLIC | ACC_STATIC);
  EXPECT_TRUE(method::can_change_signature(plain));

  auto* kept = make("LA;.kept:()V", ACC_PUBLIC | ACC_STATIC);
  kept->rstate.set_root();
  EXPECT_FALSE(method::can_change_signature(kept));

  auto* native = make("LA;.jni:()V", ACC_PUBLIC | ACC_STATIC | ACC_NATIVE);
  EXPECT_FALSE(method::can_change_signature(native));

  auto* no_optimizations = make("LA;.noOpt:()V", ACC_PUBLIC | ACC_STATIC);
  no_optimizations->rstate.set_no_optimizations();
  EXPECT_FALSE(method::can_change_signature(no_optimizations));
}

// A static initializer that makes a method handle call or a call through a call
// site may run any code, so it may have side effects.
TEST_F(MethodUtilTest, clinitWithDynamicInvokeMayHaveSideEffects) {
  auto make_class = [](const char* name, const std::string& body) {
    auto* clinit = assembler::method_from_string(
        std::string(R"((method (public static constructor) ")") + name +
        R"(.<clinit>:()V" )" + body + ")");
    ClassCreator creator(DexType::make_type(name));
    creator.set_super(type::java_lang_Object());
    creator.add_method(clinit);
    return creator.create();
  };
  auto* polymorphic = make_class("LPolymorphic;", R"(
    (
      (const-method-handle invoke-static "LBar;.run:()V")
      (move-result-pseudo-object v0)
      (invoke-polymorphic (v0) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "()V")
      (return-void)
    )
  )");
  EXPECT_NE(method::clinit_may_have_side_effects(
                polymorphic, /* allow_benign_method_invocations */ false),
            nullptr);

  // The `invoke-static` becomes an `invoke-custom`.
  auto* custom = make_class("LCustom;", R"(
    (
      (invoke-static () "LCustom;.placeholder:()V")
      (return-void)
    )
  )");
  redex::make_invoke_custom(custom->get_clinit()->get_code(), "run", "()V");
  EXPECT_NE(method::clinit_may_have_side_effects(
                custom, /* allow_benign_method_invocations */ false),
            nullptr);
}
