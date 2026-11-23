/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "IRAssembler.h"
#include "RedexTest.h"
#include "TypeInference.h"

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
