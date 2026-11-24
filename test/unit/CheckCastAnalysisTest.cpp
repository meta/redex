/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "CheckCastAnalysis.h"
#include "Creators.h"
#include "DexUtil.h"
#include "FrameworkApi.h"
#include "IRAssembler.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"

struct CheckCastAnalysisTest : public RedexTest {
  CheckCastAnalysisTest() {
    // The tests need java.lang.Object to resolve to a DexClass to build a
    // proper scope.
    create_object_class();
    type_class(type::java_lang_Object())->set_external();
    if (type_class(type::java_lang_String()) == nullptr) {
      ClassCreator cc(type::java_lang_String());
      cc.set_super(type::java_lang_Object());
      cc.set_access(ACC_PUBLIC);
      cc.create();
    }
    type_class(type::java_lang_String())->set_external();
    auto* foo_cls = DexType::make_type("LFoo;");
    if (type_class(foo_cls) == nullptr) {
      ClassCreator cc(foo_cls);
      cc.set_super(type::java_lang_Object());
      cc.add_interface(DexType::make_type("LUnknownExternalInterface;"));
      cc.set_access(ACC_PUBLIC);
      cc.create();
    }
    auto* bar_cls = DexType::make_type("LBar;");
    if (type_class(bar_cls) == nullptr) {
      ClassCreator cc(bar_cls);
      cc.set_super(type::java_lang_Object());
      cc.set_access(ACC_PUBLIC);
      cc.create();
    }
  }
  static api::AndroidSDK create_empty_sdk() {
    return api::AndroidSDK(std::nullopt);
  }
};

TEST_F(CheckCastAnalysisTest, simple_string) {
  auto* method = assembler::method_from_string(R"(
    (method (public) "LFoo;.bar:()Ljava/lang/String;"
      (
        (const-string "S1")
        (move-result-pseudo-object v1)
        (check-cast v1 "Ljava/lang/String;")
        (move-result-pseudo-object v1)
        (return-object v1)
      )
    )
  )");
  method->get_code()->build_cfg();
  check_casts::CheckCastConfig config;
  auto api = api::AndroidSDK::from_string(R"(
    Ljava/lang/String; 1 Ljava/lang/Object; 0 0
  )");
  auto analysis =
      check_casts::impl::CheckCastAnalysis::forMethod(config, method, api);
  auto replacements = analysis.collect_redundant_checks_replacement();

  EXPECT_EQ(replacements.size(), 1);
  auto it = replacements.begin();
  auto* insn = it->insn;
  EXPECT_EQ(insn->opcode(), OPCODE_CHECK_CAST);
  EXPECT_EQ(insn->get_type()->get_name()->str(), "Ljava/lang/String;");
  EXPECT_EQ(it->replacement_insn, std::nullopt);
  EXPECT_EQ(it->replacement_type, std::nullopt);
  method->get_code()->clear_cfg();
}

TEST_F(CheckCastAnalysisTest, new_instance) {
  auto* method = assembler::method_from_string(R"(
    (method (public) "LFoo;.bar:()LFoo;"
      (
        (new-instance "LFoo;")
        (move-result-pseudo-object v1)
        (check-cast v1 "LFoo;")
        (move-result-pseudo-object v1)
        (return-object v1)
      )
    )
  )");
  method->get_code()->build_cfg();
  check_casts::CheckCastConfig config;
  auto api = create_empty_sdk();
  auto analysis =
      check_casts::impl::CheckCastAnalysis::forMethod(config, method, api);
  auto replacements = analysis.collect_redundant_checks_replacement();

  EXPECT_EQ(replacements.size(), 1);
  auto it = replacements.begin();
  auto* insn = it->insn;
  EXPECT_EQ(insn->opcode(), OPCODE_CHECK_CAST);
  EXPECT_EQ(insn->get_type()->get_name()->str(), "LFoo;");
  EXPECT_EQ(it->replacement_insn, std::nullopt);
  EXPECT_EQ(it->replacement_type, std::nullopt);
  method->get_code()->clear_cfg();
}

TEST_F(CheckCastAnalysisTest, parameter) {
  auto* method = assembler::method_from_string(R"(
    (method (public) "LFoo;.bar:(LBar;)LBar;"
      (
        (load-param-object v0)
        (load-param-object v1)
        (check-cast v1 "LBar;")
        (move-result-pseudo-object v0)
        (return-object v0)
      )
    )
  )");
  method->get_code()->build_cfg();
  check_casts::CheckCastConfig config;
  auto api = create_empty_sdk();
  auto analysis =
      check_casts::impl::CheckCastAnalysis::forMethod(config, method, api);
  auto replacements = analysis.collect_redundant_checks_replacement();

  EXPECT_EQ(replacements.size(), 1);
  auto it = replacements.begin();
  auto* insn = it->insn;
  EXPECT_EQ(insn->opcode(), OPCODE_CHECK_CAST);
  EXPECT_EQ(insn->get_type()->get_name()->str(), "LBar;");
  EXPECT_NE(it->replacement_insn, std::nullopt);
  EXPECT_EQ(it->replacement_type, std::nullopt);
  method->get_code()->clear_cfg();
}

TEST_F(CheckCastAnalysisTest, array_parameter) {
  auto* method = assembler::method_from_string(R"(
    (method (public) "LFoo;.bar:([LBar;)V"
      (
        (load-param-object v0)
        (load-param-object v1)
        (check-cast v1 "Ljava/lang/Object;")
        (move-result-pseudo-object v0)
      )
    )
  )");
  method->get_code()->build_cfg();
  check_casts::CheckCastConfig config;
  auto api = create_empty_sdk();
  auto analysis =
      check_casts::impl::CheckCastAnalysis::forMethod(config, method, api);
  auto replacements = analysis.collect_redundant_checks_replacement();

  EXPECT_EQ(replacements.size(), 1);
  auto it = replacements.begin();
  auto* insn = it->insn;
  EXPECT_EQ(insn->opcode(), OPCODE_CHECK_CAST);
  EXPECT_EQ(insn->get_type()->get_name()->str(), "Ljava/lang/Object;");
  EXPECT_NE(it->replacement_insn, std::nullopt);
  EXPECT_EQ(it->replacement_type, std::nullopt);
  method->get_code()->clear_cfg();
}

TEST_F(CheckCastAnalysisTest, this_parameter) {
  auto* method = assembler::method_from_string(R"(
    (method (public) "LFoo;.bar:(LBar;)LFoo;"
      (
        (load-param-object v0)
        (load-param-object v1)
        (check-cast v0 "LFoo;")
        (move-result-pseudo-object v0)
        (return-object v0)
      )
    )
  )");
  method->get_code()->build_cfg();
  check_casts::CheckCastConfig config;
  auto api = create_empty_sdk();
  auto analysis =
      check_casts::impl::CheckCastAnalysis::forMethod(config, method, api);
  auto replacements = analysis.collect_redundant_checks_replacement();

  EXPECT_EQ(replacements.size(), 1);
  auto it = replacements.begin();
  auto* insn = it->insn;
  EXPECT_EQ(insn->opcode(), OPCODE_CHECK_CAST);
  EXPECT_EQ(insn->get_type()->get_name()->str(), "LFoo;");
  EXPECT_EQ(it->replacement_insn, std::nullopt);
  EXPECT_EQ(it->replacement_type, std::nullopt);
  method->get_code()->clear_cfg();
}

TEST_F(CheckCastAnalysisTest, get_field) {

  auto* method = assembler::method_from_string(R"(
    (method (public) "LFoo;.bar:()LBar;"
      (
        (iget-object v0 "LFoo;.b:LBar;")
        (move-result-pseudo-object v1)
        (check-cast v1 "LBar;")
        (move-result-pseudo-object v2)
        (return-object v2)
      )
    )
  )");
  method->get_code()->build_cfg();
  check_casts::CheckCastConfig config{.weaken = false};
  auto api = create_empty_sdk();
  auto analysis =
      check_casts::impl::CheckCastAnalysis::forMethod(config, method, api);
  auto replacements = analysis.collect_redundant_checks_replacement();

  EXPECT_EQ(replacements.size(), 1);
  auto it = replacements.begin();
  auto* insn = it->insn;
  EXPECT_EQ(insn->opcode(), OPCODE_CHECK_CAST);
  EXPECT_EQ(insn->get_type()->get_name()->str(), "LBar;");
  EXPECT_NE(it->replacement_insn, std::nullopt);
  EXPECT_EQ(it->replacement_type, std::nullopt);

  method->get_code()->clear_cfg();
}

TEST_F(CheckCastAnalysisTest, weaken_disabled) {
  auto* method = assembler::method_from_string(R"(
    (method (public) "LFoo;.bar:(Ljava/lang/Object;)Ljava/lang/Object;"
      (
        (load-param-object v0)
        (load-param-object v1)
        (check-cast v1 "LBar;")
        (move-result-pseudo-object v0)
        (return-object v0)
      )
    )
  )");
  method->get_code()->build_cfg();
  check_casts::CheckCastConfig config{.weaken = false};
  auto api = create_empty_sdk();
  auto analysis =
      check_casts::impl::CheckCastAnalysis::forMethod(config, method, api);
  auto replacements = analysis.collect_redundant_checks_replacement();

  EXPECT_EQ(replacements.size(), 0);
  method->get_code()->clear_cfg();
}

TEST_F(CheckCastAnalysisTest, weaken_replace) {
  auto* method = assembler::method_from_string(R"(
    (method (public) "LFoo;.bar:(Ljava/lang/Object;)Ljava/lang/Object;"
      (
        (load-param-object v0)
        (load-param-object v1)
        (check-cast v1 "LBar;")
        (move-result-pseudo-object v0)
        (return-object v0)
      )
    )
  )");
  method->get_code()->build_cfg();
  check_casts::CheckCastConfig config;
  auto api = create_empty_sdk();
  auto analysis =
      check_casts::impl::CheckCastAnalysis::forMethod(config, method, api);
  auto replacements = analysis.collect_redundant_checks_replacement();

  EXPECT_EQ(replacements.size(), 1);
  auto it = replacements.begin();
  auto* insn = it->insn;
  EXPECT_EQ(insn->opcode(), OPCODE_CHECK_CAST);
  EXPECT_EQ(insn->get_type()->get_name()->str(), "LBar;");
  EXPECT_NE(it->replacement_insn, std::nullopt);
  EXPECT_EQ(it->replacement_type, std::nullopt);
  method->get_code()->clear_cfg();
}

TEST_F(CheckCastAnalysisTest, weaken) {
  auto* a_type = DexType::make_type("LA;");
  auto* b_type = DexType::make_type("LB;");
  auto* c_type = DexType::make_type("LC;");
  ClassCreator a_creator(a_type);
  a_creator.set_super(type::java_lang_Object());
  ClassCreator b_creator(b_type);
  b_creator.set_super(a_type);
  ClassCreator c_creator(c_type);
  c_creator.set_super(b_type);
  a_creator.create();
  b_creator.create();
  c_creator.create();

  auto* method = assembler::method_from_string(R"(
    (method (public) "LFoo;.bar:(LA;)LB;"
      (
        (load-param-object v0)
        (load-param-object v1)
        (check-cast v1 "LC;")
        (move-result-pseudo-object v0)
        (return-object v0)
      )
    )
  )");
  method->get_code()->build_cfg();
  check_casts::CheckCastConfig config;
  auto api = create_empty_sdk();
  auto analysis =
      check_casts::impl::CheckCastAnalysis::forMethod(config, method, api);
  auto replacements = analysis.collect_redundant_checks_replacement();

  EXPECT_EQ(replacements.size(), 1);
  auto it = replacements.begin();
  auto* insn = it->insn;
  EXPECT_EQ(insn->opcode(), OPCODE_CHECK_CAST);
  EXPECT_EQ(insn->get_type()->get_name()->str(), "LC;");
  EXPECT_EQ(it->replacement_insn, std::nullopt);
  EXPECT_NE(it->replacement_type, std::nullopt);
  EXPECT_EQ(*it->replacement_type, b_type);
  method->get_code()->clear_cfg();
}

TEST_F(CheckCastAnalysisTest, weaken_interface_to_interface) {
  auto* i_type = DexType::make_type("LI;");
  ClassCreator i_creator(i_type);
  i_creator.set_access(ACC_INTERFACE | ACC_ABSTRACT);
  i_creator.set_super(type::java_lang_Object());
  auto* j_type = DexType::make_type("LJ;");
  ClassCreator j_creator(j_type);
  j_creator.set_access(ACC_INTERFACE | ACC_ABSTRACT);
  j_creator.set_super(type::java_lang_Object());
  j_creator.add_interface(i_type);
  auto* k_type = DexType::make_type("LK;");
  ClassCreator k_creator(k_type);
  k_creator.set_access(ACC_INTERFACE | ACC_ABSTRACT);
  k_creator.set_super(type::java_lang_Object());
  k_creator.add_interface(i_type);
  i_creator.create();
  j_creator.create();
  k_creator.create();

  auto* method = assembler::method_from_string(R"(
    (method (public) "LFoo;.bar:(LI;)LJ;"
      (
        (load-param-object v0)
        (load-param-object v1)
        (check-cast v1 "LK;")
        (move-result-pseudo-object v0)
        (return-object v0)
      )
    )
  )");
  method->get_code()->build_cfg();
  check_casts::CheckCastConfig config;
  auto api = create_empty_sdk();
  auto analysis =
      check_casts::impl::CheckCastAnalysis::forMethod(config, method, api);
  auto replacements = analysis.collect_redundant_checks_replacement();

  EXPECT_EQ(replacements.size(), 1);
  auto it = replacements.begin();
  auto* insn = it->insn;
  EXPECT_EQ(insn->opcode(), OPCODE_CHECK_CAST);
  EXPECT_EQ(insn->get_type()->get_name()->str(), "LK;");
  EXPECT_EQ(it->replacement_insn, std::nullopt);
  EXPECT_NE(it->replacement_type, std::nullopt);
  EXPECT_EQ(*it->replacement_type, j_type);
  method->get_code()->clear_cfg();
}

TEST_F(CheckCastAnalysisTest, weaken_replace_class_to_interface) {
  auto* i_type = DexType::make_type("LI;");
  ClassCreator i_creator(i_type);
  i_creator.set_access(ACC_INTERFACE | ACC_ABSTRACT);
  i_creator.set_super(type::java_lang_Object());

  auto* a_type = DexType::make_type("LA;");
  auto* b_type = DexType::make_type("LB;");
  ClassCreator a_creator(a_type);
  a_creator.set_super(type::java_lang_Object());
  a_creator.add_interface(i_type);
  ClassCreator b_creator(b_type);
  b_creator.set_super(a_type);
  b_creator.add_interface(i_type);
  i_creator.create();
  a_creator.create();
  b_creator.create();

  auto* method = assembler::method_from_string(R"(
    (method (public) "LFoo;.bar:(LA;)LI;"
      (
        (load-param-object v0)
        (load-param-object v1)
        (check-cast v1 "LB;")
        (move-result-pseudo-object v0)
        (return-object v0)
      )
    )
  )");
  method->get_code()->build_cfg();
  check_casts::CheckCastConfig config;
  auto api = create_empty_sdk();
  auto analysis =
      check_casts::impl::CheckCastAnalysis::forMethod(config, method, api);
  auto replacements = analysis.collect_redundant_checks_replacement();

  EXPECT_EQ(replacements.size(), 1);
  auto it = replacements.begin();
  auto* insn = it->insn;
  EXPECT_EQ(insn->opcode(), OPCODE_CHECK_CAST);
  EXPECT_EQ(insn->get_type()->get_name()->str(), "LB;");
  EXPECT_NE(it->replacement_insn, std::nullopt);
  EXPECT_EQ(it->replacement_type, std::nullopt);
  method->get_code()->clear_cfg();
}

TEST_F(CheckCastAnalysisTest, do_not_weaken_class_to_interface) {
  auto* i_type = DexType::make_type("LI;");
  ClassCreator i_creator(i_type);
  i_creator.set_access(ACC_INTERFACE | ACC_ABSTRACT);
  i_creator.set_super(type::java_lang_Object());

  auto* a_type = DexType::make_type("LA;");
  auto* b_type = DexType::make_type("LB;");
  ClassCreator a_creator(a_type);
  a_creator.set_super(type::java_lang_Object());
  ClassCreator b_creator(b_type);
  b_creator.set_super(a_type);
  b_creator.add_interface(i_type);
  i_creator.create();
  a_creator.create();
  b_creator.create();

  auto* method = assembler::method_from_string(R"(
    (method (public) "LFoo;.bar:(LA;)LI;"
      (
        (load-param-object v0)
        (load-param-object v1)
        (check-cast v1 "LB;")
        (move-result-pseudo-object v0)
        (return-object v0)
      )
    )
  )");
  method->get_code()->build_cfg();
  check_casts::CheckCastConfig config;
  auto api = create_empty_sdk();
  auto analysis =
      check_casts::impl::CheckCastAnalysis::forMethod(config, method, api);
  auto replacements = analysis.collect_redundant_checks_replacement();

  EXPECT_EQ(replacements.size(), 0);
}

TEST_F(CheckCastAnalysisTest, external) {
  auto* method = assembler::method_from_string(R"(
    (method (public) "LFoo;.bar:()LUnknownExternalInterface;"
      (
        (new-instance "LFoo;")
        (move-result-pseudo-object v1)
        (check-cast v1 "LUnknownExternalInterface;")
        (move-result-pseudo-object v1)
        (return-object v1)
      )
    )
  )");
  method->get_code()->build_cfg();
  check_casts::CheckCastConfig config;
  auto api = create_empty_sdk();
  auto analysis =
      check_casts::impl::CheckCastAnalysis::forMethod(config, method, api);
  auto replacements = analysis.collect_redundant_checks_replacement();

  EXPECT_EQ(replacements.size(), 0);
}

namespace {

std::tuple<DexType*, DexType*, DexType*, DexType*> create_chain_of_four() {
  auto create_class = [](const char* t_name, DexType* super_type,
                         bool external) {
    auto* t_type = DexType::make_type(t_name);
    ClassCreator t_creator(t_type);
    t_creator.set_super(super_type);
    if (external) {
      t_creator.set_external();
    }
    t_creator.create();
    return t_type;
  };

  auto* t1_type = create_class("LT1;", type::java_lang_Object(), true);
  auto* t2_type = create_class("LT2;", t1_type, true);
  auto* t3_type = create_class("LT3;", t2_type, true);
  auto* t4_type = create_class("LT4;", t3_type, false);

  return std::make_tuple(t1_type, t2_type, t3_type, t4_type);
}

} // namespace

class CheckCastAnalysisSDKTest
    : public RedexTest,
      public testing::WithParamInterface<
          std::tuple<const char*, const char*, bool>> {};

TEST_P(CheckCastAnalysisSDKTest, parameter) {
  [[maybe_unused]] auto [t1_type, t2_type, t3_type, t4_type] =
      create_chain_of_four();

  auto api = api::AndroidSDK::from_string(std::get<1>(GetParam()));

  auto* method = assembler::method_from_string(R"(
    (method (public) "LFoo;.bar:(LT3;)LT1;"
      (
        (load-param-object v0)
        (load-param-object v1)
        (check-cast v1 "LT1;")
        (move-result-pseudo-object v0)
        (return-object v0)
      )
    )
  )");
  method->get_code()->build_cfg();
  check_casts::CheckCastConfig config;
  auto analysis =
      check_casts::impl::CheckCastAnalysis::forMethod(config, method, api);
  auto replacements = analysis.collect_redundant_checks_replacement();

  if (std::get<2>(GetParam())) {
    ASSERT_EQ(replacements.size(), 1);
    auto& rep = replacements[0];
    EXPECT_EQ(rep.insn->opcode(), OPCODE_CHECK_CAST);
    ASSERT_TRUE(rep.replacement_insn);
    EXPECT_EQ((*rep.replacement_insn)->opcode(), OPCODE_MOVE_OBJECT);
    EXPECT_EQ(rep.replacement_type, std::nullopt);
  } else {
    EXPECT_EQ(replacements.size(), 0);
  }
  method->get_code()->clear_cfg();
}

INSTANTIATE_TEST_SUITE_P(SDKCombinations,
                         CheckCastAnalysisSDKTest,
                         testing::Values(std::make_tuple("Full_Chain",
                                                         R"(
    LT1; 1 Ljava/lang/Object; 0 0
    LT2; 1 LT1; 0 0
    LT3; 1 LT2; 0 0
  )",
                                                         true),
                                         std::make_tuple("Hierarchy_Bypass",
                                                         R"(
    LT1; 1 Ljava/lang/Object; 0 0
    LT2; 1 LT1; 0 0
    LT3; 1 LT1; 0 0
  )",
                                                         true),
                                         std::make_tuple("Source_Not_In_SDK",
                                                         R"(
    LT1; 1 Ljava/lang/Object; 0 0
    LT2; 1 LT1; 0 0
  )",
                                                         false),
                                         std::make_tuple("SDK_Not_Related",
                                                         R"(
    LT1; 1 Ljava/lang/Object; 0 0
    LT2; 1 Ljava/lang/Object; 0 0
    LT3; 1 LT2; 0 0
  )",
                                                         false)),
                         [](const auto& info) {
                           return std::get<0>(info.param);
                         });

// A method handle call needs its argument to have the type that the call
// site's prototype gives it, so the cast stays.
TEST_F(CheckCastAnalysisTest, method_handle_call_argument) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:(Ljava/lang/invoke/MethodHandle;Ljava/lang/Object;)V"
      (
        (load-param-object v0)
        (load-param-object v1)
        (check-cast v1 "LBar;")
        (move-result-pseudo-object v2)
        (invoke-polymorphic (v0 v2) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "(LBar;)V")
        (return-void)
      )
    )
  )");
  method->get_code()->build_cfg();
  check_casts::CheckCastConfig config;
  auto api = create_empty_sdk();
  auto analysis =
      check_casts::impl::CheckCastAnalysis::forMethod(config, method, api);
  EXPECT_TRUE(analysis.collect_redundant_checks_replacement().empty());
  method->get_code()->clear_cfg();
}

// A method handle call needs its receiver to be a `MethodHandle`, so the cast
// stays.
TEST_F(CheckCastAnalysisTest, method_handle_call_receiver) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:(Ljava/lang/Object;)V"
      (
        (load-param-object v0)
        (check-cast v0 "Ljava/lang/invoke/MethodHandle;")
        (move-result-pseudo-object v1)
        (invoke-polymorphic (v1) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "()V")
        (return-void)
      )
    )
  )");
  method->get_code()->build_cfg();
  check_casts::CheckCastConfig config;
  auto api = create_empty_sdk();
  auto analysis =
      check_casts::impl::CheckCastAnalysis::forMethod(config, method, api);
  EXPECT_TRUE(analysis.collect_redundant_checks_replacement().empty());
  method->get_code()->clear_cfg();
}

// A call through a call site needs its argument to have the type that the call
// site's method type gives it, so the cast stays.
TEST_F(CheckCastAnalysisTest, call_site_argument) {
  // The `invoke-static` becomes an `invoke-custom`.
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:(Ljava/lang/Object;)V"
      (
        (load-param-object v1)
        (check-cast v1 "LBar;")
        (move-result-pseudo-object v2)
        (invoke-static (v2) "LFoo;.placeholder:(LBar;)V")
        (return-void)
      )
    )
  )");
  redex::make_invoke_custom(method->get_code(), "run", "(LBar;)V");
  method->get_code()->build_cfg();
  check_casts::CheckCastConfig config;
  auto api = create_empty_sdk();
  auto analysis =
      check_casts::impl::CheckCastAnalysis::forMethod(config, method, api);
  EXPECT_TRUE(analysis.collect_redundant_checks_replacement().empty());
  method->get_code()->clear_cfg();
}
