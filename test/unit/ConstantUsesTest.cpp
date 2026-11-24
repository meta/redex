/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "ConstantUses.h"
#include "IRAssembler.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"

class ConstantUsesTest : public RedexTest {};

// A constant passed to a method handle call must have the type that the call
// site's prototype gives its argument, here a float.
TEST_F(ConstantUsesTest, methodHandleCallArgument) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:(Ljava/lang/invoke/MethodHandle;)V"
     (
      (load-param-object v0)
      (const v1 0)
      (invoke-polymorphic (v0 v1) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "(F)V")
      (return-void)
     )
    )
  )");
  auto* code = method->get_code();
  code->build_cfg();
  constant_uses::ConstantUses constant_uses(code->cfg(), method);
  for (auto& mie : cfg::InstructionIterable(code->cfg())) {
    if (mie.insn->opcode() == OPCODE_CONST) {
      EXPECT_EQ(constant_uses.get_constant_type_demand(mie.insn),
                constant_uses::TypeDemand::Float);
    }
  }
}

// A constant passed through a call site must have the type that the call
// site's method type gives its argument, here a float. Such a call has no
// receiver, so the constant is its first source.
TEST_F(ConstantUsesTest, callSiteArgument) {
  // The `invoke-static` becomes an `invoke-custom`.
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:()V"
     (
      (const v1 0)
      (invoke-static (v1) "LFoo;.placeholder:(F)V")
      (return-void)
     )
    )
  )");
  auto* code = method->get_code();
  redex::make_invoke_custom(code, "run", "(F)V");
  code->build_cfg();
  constant_uses::ConstantUses constant_uses(code->cfg(), method);
  for (auto& mie : cfg::InstructionIterable(code->cfg())) {
    if (mie.insn->opcode() == OPCODE_CONST) {
      EXPECT_EQ(constant_uses.get_constant_type_demand(mie.insn),
                constant_uses::TypeDemand::Float);
    }
  }
}
