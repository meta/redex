/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "IRAssembler.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"
#include "TypeInference.h"
#include "TypeUtil.h"

using namespace testing;

class TypeInferenceTest : public RedexTest {};

TEST_F(TypeInferenceTest, const0) {
  auto* method = assembler::method_from_string(R"(
    (method (private) "LFoo;.bar:()V"
     (
      (load-param-object v1) ; 'this' argument
      (iget-object v1 "LFoo;.a:LBar;")
      (move-result-pseudo-object v0)
      (const v0 0)
      (invoke-interface (v0) "LBaz;.heh:()V")  ; v0 should not be LBar type
      (return-void)
     )
    )
  )");
  auto* code = method->get_code();
  code->build_cfg();
  auto& cfg = code->cfg();
  type_inference::TypeInference inference(cfg);
  inference.run(method);
  auto& envs = inference.get_type_environments();
  for (auto& mie : InstructionIterable(cfg)) {
    auto* insn = mie.insn;
    if (opcode::is_a_method_invoke(insn->opcode())) {
      auto& env = envs.at(insn);
      auto dex_type = env.get_dex_type(insn->src(0));
      if (dex_type && *dex_type != type::java_lang_Object()) {
        EXPECT_TRUE(DexType::get_type("LBar;") != *dex_type);
      }
    }
  }
}

/*
 * const-string and const-class either produce a reference or throw, so their
 * results are never null, and both java.lang.String and java.lang.Class are
 * final, so the inferred type is exact. That exactness is what puts them in
 * the small set domain: it is only populated for types we know precisely.
 */
TEST_F(TypeInferenceTest, constStringAndConstClassAreNotNullAndExact) {
  auto* method = assembler::method_from_string(R"(
    (method (private) "LFoo;.bar:()V"
     (
      (load-param-object v2) ; 'this' argument
      (const-string "s")
      (move-result-pseudo-object v0)
      (const-class "LBar;")
      (move-result-pseudo-object v1)
      (invoke-static (v0 v1) "LBaz;.heh:(Ljava/lang/String;Ljava/lang/Class;)V")
      (return-void)
     )
    )
  )");
  auto* code = method->get_code();
  code->build_cfg();
  auto& cfg = code->cfg();
  type_inference::TypeInference inference(cfg);
  inference.run(method);
  auto& envs = inference.get_type_environments();

  bool checked = false;
  for (auto& mie : InstructionIterable(cfg)) {
    auto* insn = mie.insn;
    if (!opcode::is_a_method_invoke(insn->opcode())) {
      continue;
    }
    auto& env = envs.at(insn);
    for (auto [reg, expected] :
         {std::make_pair(insn->src(0), type::java_lang_String()),
          std::make_pair(insn->src(1), type::java_lang_Class())}) {
      auto domain = env.get_type_domain(reg);
      EXPECT_TRUE(domain.is_not_null());
      EXPECT_EQ(expected, *domain.get_dex_type());
      // Exact type, so it is tracked in the small set domain as well.
      ASSERT_FALSE(domain.get_set_domain().is_top());
      EXPECT_EQ(1, domain.get_type_set().size());
      EXPECT_TRUE(domain.get_type_set().contains(expected));
    }
    checked = true;
  }
  EXPECT_TRUE(checked);
}

// `invoke-polymorphic` passes and returns the types of its call-site
// prototype, here an int and a long.
TEST_F(TypeInferenceTest, invokePolymorphicUsesCallSiteProto) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:(Ljava/lang/invoke/MethodHandle;)V"
     (
      (load-param-object v0)
      (const v1 7)
      (invoke-polymorphic (v0 v1) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "(I)J")
      (move-result-wide v2)
      (return-void)
     )
    )
  )");
  auto* code = method->get_code();
  code->build_cfg();
  type_inference::TypeInference inference(code->cfg());
  inference.run(method);
  bool checked = false;
  for (auto& mie : InstructionIterable(code->cfg())) {
    if (mie.insn->opcode() == OPCODE_RETURN_VOID) {
      checked = true;
      const auto& env = inference.get_type_environments().at(mie.insn);
      EXPECT_EQ(env.get_type(2), type_inference::TypeDomain(IRType::LONG1));
      EXPECT_EQ(env.get_type(3), type_inference::TypeDomain(IRType::LONG2));
    }
  }
  EXPECT_TRUE(checked);
}

// `invoke-custom` passes and returns the types of its call site's method
// type, and has no receiver.
TEST_F(TypeInferenceTest, invokeCustomUsesCallSiteMethodType) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:(J)V"
     (
      (load-param-wide v0)
      (invoke-static (v0) "LFoo;.placeholder:(J)V")
      (move-result-object v2)
      (return-void)
     )
    )
  )");
  auto* code = method->get_code();
  redex::make_invoke_custom(code, "get", "(J)Ljava/util/function/Supplier;");
  code->build_cfg();
  type_inference::TypeInference inference(code->cfg());
  inference.run(method);
  bool checked = false;
  for (auto& mie : InstructionIterable(code->cfg())) {
    if (mie.insn->opcode() == OPCODE_RETURN_VOID) {
      checked = true;
      const auto& env = inference.get_type_environments().at(mie.insn);
      EXPECT_EQ(env.get_type(0), type_inference::TypeDomain(IRType::LONG1));
      EXPECT_EQ(env.get_type(2), type_inference::TypeDomain(IRType::REFERENCE));
      ASSERT_TRUE(env.get_dex_type(2));
      EXPECT_EQ(*env.get_dex_type(2),
                DexType::get_type("Ljava/util/function/Supplier;"));
    }
  }
  EXPECT_TRUE(checked);
}

// `const-method-handle` loads some subclass of MethodHandle, and
// `const-method-type` loads a MethodType, which is final, so it is that exact
// class and never null.
TEST_F(TypeInferenceTest, constMethodHandleAndType) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:()V"
     (
      (const-method-handle invoke-instance "Ljava/lang/Object;.hashCode:()I")
      (move-result-pseudo-object v0)
      (const-method-type "(CSJ)Z")
      (move-result-pseudo-object v1)
      (return-void)
     )
    )
  )");
  auto* code = method->get_code();
  code->build_cfg();
  type_inference::TypeInference inference(code->cfg());
  inference.run(method);
  bool checked = false;
  for (auto& mie : InstructionIterable(code->cfg())) {
    if (mie.insn->opcode() == OPCODE_RETURN_VOID) {
      checked = true;
      const auto& env = inference.get_type_environments().at(mie.insn);
      ASSERT_TRUE(env.get_dex_type(0));
      ASSERT_TRUE(env.get_dex_type(1));
      EXPECT_EQ(*env.get_dex_type(0),
                DexType::get_type("Ljava/lang/invoke/MethodHandle;"));
      // Not the exact class.
      EXPECT_TRUE(env.get_type_domain(0).get_set_domain().is_top());
      const auto* method_type =
          DexType::get_type("Ljava/lang/invoke/MethodType;");
      EXPECT_EQ(*env.get_dex_type(1), method_type);
      EXPECT_TRUE(env.get_type_domain(1).is_not_null());
      EXPECT_TRUE(env.get_type_domain(1).get_type_set().contains(method_type));
    }
  }
  EXPECT_TRUE(checked);
}
