/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "KotlinLambdaDeduplicationPass.h"

#include <algorithm>
#include <array>
#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include "ConfigFiles.h"
#include "Creators.h"
#include "DexStore.h"
#include "DexUtil.h"
#include "IRAssembler.h"
#include "IROpcode.h"
#include "PassManager.h"
#include "RedexTest.h"

namespace {

using ::testing::Contains;
using ::testing::NotNull;

// Create a non-capturing Kotlin lambda class.
// @param name Type descriptor, e.g. "LNonSingletonLambda$0;".
// @param singleton If true, adds a static INSTANCE field.
DexClass* create_lambda(std::string_view name, bool singleton) {
  // All lambdas in a dedup group share these bodies so they hash identically
  // in UniqueMethodTracker.
  const std::string invoke_body = R"((
    (load-param-object v0)
    (const v1 0)
    (return-object v1)
  ))";
  const std::string ctor_body = R"((
    (load-param-object v0)
    (return-void)
  ))";

  auto* type = DexType::make_type(name);
  ClassCreator cc(type);
  cc.set_super(type::kotlin_jvm_internal_Lambda());
  cc.add_interface(DexType::make_type("Lkotlin/jvm/functions/Function0;"));

  auto* invoke_proto = DexProto::make_proto(type::java_lang_Object(),
                                            DexTypeList::make_type_list({}));
  auto* invoke = DexMethod::make_method(type, DexString::make_string("invoke"),
                                        invoke_proto)
                     ->make_concrete(ACC_PUBLIC, true);
  invoke->set_code(assembler::ircode_from_string(invoke_body));
  cc.add_method(invoke);

  auto* init_proto =
      DexProto::make_proto(type::_void(), DexTypeList::make_type_list({}));
  auto* init =
      DexMethod::make_method(type, DexString::make_string("<init>"), init_proto)
          ->make_concrete(ACC_PUBLIC, false);
  init->set_code(assembler::ircode_from_string(ctor_body));
  cc.add_method(init);

  if (singleton) {
    auto* instance_field =
        DexField::make_field(type, DexString::make_string("INSTANCE"), type)
            ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL);
    cc.add_field(instance_field);
  }

  return cc.create();
}

// Run the dedup pass with classes split across multiple dex files.
// Classes in dex 0 have a lower index, so the canonical lambda is chosen
// from dex 0.
void run_dedup_pass(std::vector<std::vector<DexClass*>> dexes) {
  Json::Value json_config(Json::objectValue);
  json_config["redex"] = Json::objectValue;
  json_config["redex"]["passes"] = Json::arrayValue;
  json_config["redex"]["passes"].append("KotlinLambdaDeduplicationPass");
  json_config["KotlinLambdaDeduplicationPass"] = Json::objectValue;
  json_config["KotlinLambdaDeduplicationPass"]["min_duplicate_group_size"] = 2;

  KotlinLambdaDeduplicationPass pass;
  std::vector<Pass*> passes{&pass};
  ConfigFiles config(json_config);
  config.parse_global_config();
  PassManager manager(passes, config);
  DexStore store("classes");
  for (auto& classes : dexes) {
    store.add_classes(std::move(classes));
  }
  std::vector<DexStore> stores;
  stores.emplace_back(std::move(store));
  manager.run_passes(stores, config);
}

const DexType* get_referenced_type(const IRInstruction* insn) {
  if (insn->has_type()) {
    return insn->get_type();
  }
  if (insn->has_method()) {
    return insn->get_method()->get_class();
  }
  if (insn->has_field()) {
    return insn->get_field()->get_class();
  }
  return nullptr;
}

} // namespace

class KotlinLambdaDeduplicationPassTest : public RedexTest {};

struct CanonicalDexCase {
  std::string name;
  // lambda_dex_layout[i] = lambda indices for dex i.
  // Lambda 0 is the target (referenced by the caller); caller is placed in the
  // same dex as lambda 0.
  std::vector<std::vector<int>> lambda_dex_layout;
};

using CanonicalDexParam = std::tuple<bool, CanonicalDexCase>;

class CanonicalDexSelectionTest
    : public KotlinLambdaDeduplicationPassTest,
      public ::testing::WithParamInterface<CanonicalDexParam> {};

TEST_P(CanonicalDexSelectionTest, SelectsCanonicalFromLowestIndexedDex) {
  const auto& [singleton, dex_case] = GetParam();

  // 5 identical lambdas. The caller references lambda 0 (the "target"), which
  // may or may not end up canonical depending on dex layout.
  std::array<DexClass*, 5> lambdas;
  lambdas[0] = create_lambda("LTarget$0;", singleton);
  for (int i = 1; i < 5; ++i) {
    std::string name = "LLambda$" + std::to_string(i) + ";";
    lambdas[i] = create_lambda(name, singleton);
  }

  // Caller references the target lambda.
  ClassCreator cc(DexType::make_type("LCaller;"));
  cc.set_super(type::java_lang_Object());
  auto* caller_method =
      DexMethod::make_method("LCaller;.call:()Ljava/lang/Object;")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  if (singleton) {
    caller_method->set_code(assembler::ircode_from_string(R"((
      (sget-object "LTarget$0;.INSTANCE:LTarget$0;")
      (move-result-pseudo-object v0)
      (return-object v0)
    ))"));
  } else {
    caller_method->set_code(assembler::ircode_from_string(R"((
      (new-instance "LTarget$0;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LTarget$0;.<init>:()V")
      (return-object v0)
    ))"));
  }
  cc.add_method(caller_method);
  auto* caller_cls = cc.create();

  // Build dex groups from lambda_dex_layout; place caller with the target.
  std::vector<std::vector<DexClass*>> dexes(dex_case.lambda_dex_layout.size());
  for (size_t dex_idx = 0; dex_idx < dex_case.lambda_dex_layout.size();
       ++dex_idx) {
    for (int lambda_idx : dex_case.lambda_dex_layout[dex_idx]) {
      dexes[dex_idx].push_back(lambdas[lambda_idx]);
      if (lambda_idx == 0) {
        dexes[dex_idx].push_back(caller_cls);
      }
    }
  }

  run_dedup_pass(std::move(dexes));

  // Expected canonical types = types of lambdas in the lowest-indexed dex that
  // contains at least one lambda.
  const auto canonical_dex = *std::ranges::find_if_not(
      dex_case.lambda_dex_layout, &std::vector<int>::empty);
  std::unordered_set<const DexType*> expected_canonical_types;
  for (int idx : canonical_dex) {
    expected_canonical_types.insert(lambdas[idx]->get_type());
  }

  ASSERT_THAT(caller_method->get_code(), NotNull());
  bool found = false;
  for (const auto& mie : *caller_method->get_code()) {
    if (mie.type != MFLOW_OPCODE) {
      continue;
    }
    const auto* ref_type = get_referenced_type(mie.insn);
    if (ref_type == nullptr) {
      continue;
    }
    found = true;
    EXPECT_THAT(expected_canonical_types, Contains(ref_type))
        << "instruction must reference a canonical type from the "
           "lowest-indexed dex";
    if (singleton && opcode::is_an_sget(mie.insn->opcode())) {
      EXPECT_EQ(mie.insn->get_field()->get_name()->str(),
                KotlinLambdaDeduplicationPass::kDedupedInstanceName);
    }
  }
  EXPECT_TRUE(found) << "expected at least one instruction referencing a "
                        "lambda type";
}

INSTANTIATE_TEST_SUITE_P(
    CanonicalDexSelectionTests,
    CanonicalDexSelectionTest,
    ::testing::Combine(
        ::testing::Bool(), // singleton
        // 0 is the target lambda
        ::testing::Values(
            CanonicalDexCase{"TargetInDex0", {{0}, {1, 2, 3, 4}}},
            CanonicalDexCase{"TargetInDex1With2Dexes", {{1, 2, 3, 4}, {0}}},
            CanonicalDexCase{"TargetInDex1With3Dexes", {{1, 2}, {0, 3}, {4}}},
            CanonicalDexCase{"TargetInDex2With3DexesAndEmptyDex0",
                             {{}, {1, 2, 3}, {0, 4}}},
            CanonicalDexCase{"TargetInDex2With3Dexes", {{1, 2}, {3, 4}, {0}}})),
    [](const ::testing::TestParamInfo<CanonicalDexParam>& info) {
      return std::string(std::get<0>(info.param) ? "Singleton_"
                                                 : "NonSingleton_") +
             std::get<1>(info.param).name;
    });

struct OpcodeRedirectParam {
  std::string name;
  IROpcode opcode;
  std::string caller_ir;
};

class NonSingleton_InstructionRedirectTest
    : public KotlinLambdaDeduplicationPassTest,
      public ::testing::WithParamInterface<OpcodeRedirectParam> {};

TEST_P(NonSingleton_InstructionRedirectTest, RedirectsToCanonical) {
  const auto& param = GetParam();

  // Canonical lambda in dex 0, target lambda + caller in dex 1.
  auto* canonical = create_lambda("LNonSingletonLambda$0;", false);
  auto* target_lambda = create_lambda("LNonSingletonTarget$0;", false);
  const auto* target_type = target_lambda->get_type();
  const auto* canonical_type = canonical->get_type();

  ClassCreator cc(DexType::make_type("LNonSingletonCaller;"));
  cc.set_super(type::java_lang_Object());
  auto* caller_method =
      DexMethod::make_method("LNonSingletonCaller;.call:()Ljava/lang/Object;")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  caller_method->set_code(assembler::ircode_from_string(param.caller_ir));
  cc.add_method(caller_method);
  auto* caller_cls = cc.create();

  run_dedup_pass({{canonical}, {target_lambda, caller_cls}});

  bool found = false;
  for (const auto& mie : *caller_method->get_code()) {
    if (mie.type != MFLOW_OPCODE || mie.insn->opcode() != param.opcode) {
      continue;
    }
    found = true;
    const auto* ref_type = get_referenced_type(mie.insn);
    ASSERT_NE(ref_type, nullptr);
    EXPECT_NE(ref_type, target_type)
        << "instruction must be redirected from non-canonical type";
    EXPECT_EQ(ref_type, canonical_type)
        << "instruction must reference the canonical type from dex 0";
  }
  EXPECT_TRUE(found) << "expected at least one " << param.name
                     << " instruction";
}

INSTANTIATE_TEST_SUITE_P(
    NonSingleton_InstructionRedirectTests,
    NonSingleton_InstructionRedirectTest,
    ::testing::Values(OpcodeRedirectParam{"NewInstance", OPCODE_NEW_INSTANCE,
                                          R"((
          (new-instance "LNonSingletonTarget$0;")
          (move-result-pseudo-object v0)
          (invoke-direct (v0) "LNonSingletonTarget$0;.<init>:()V")
          (return-object v0)
        ))"},
                      OpcodeRedirectParam{"InvokeDirect", OPCODE_INVOKE_DIRECT,
                                          R"((
          (new-instance "LNonSingletonTarget$0;")
          (move-result-pseudo-object v0)
          (invoke-direct (v0) "LNonSingletonTarget$0;.<init>:()V")
          (return-object v0)
        ))"},
                      OpcodeRedirectParam{"InvokeVirtual",
                                          OPCODE_INVOKE_VIRTUAL,
                                          R"((
          (const v0 0)
          (invoke-virtual (v0) "LNonSingletonTarget$0;.invoke:()Ljava/lang/Object;")
          (move-result-object v1)
          (return-object v1)
        ))"},
                      OpcodeRedirectParam{"CheckCast", OPCODE_CHECK_CAST,
                                          R"((
          (const v0 0)
          (check-cast v0 "LNonSingletonTarget$0;")
          (move-result-pseudo-object v0)
          (return-object v0)
        ))"}),
    [](const ::testing::TestParamInfo<OpcodeRedirectParam>& info) {
      return info.param.name;
    });

class Singleton_InstructionRedirectTest
    : public KotlinLambdaDeduplicationPassTest,
      public ::testing::WithParamInterface<OpcodeRedirectParam> {};

TEST_P(Singleton_InstructionRedirectTest, RedirectsToCanonical) {
  const auto& param = GetParam();

  // Canonical lambda in dex 0, target lambda + caller in dex 1.
  auto* canonical = create_lambda("LSingletonLambda$0;", true);
  auto* target_lambda = create_lambda("LSingletonTarget$0;", true);
  const auto* target_type = target_lambda->get_type();
  const auto* canonical_type = canonical->get_type();

  ClassCreator cc(DexType::make_type("LSingletonCaller;"));
  cc.set_super(type::java_lang_Object());
  auto* caller_method =
      DexMethod::make_method("LSingletonCaller;.call:()Ljava/lang/Object;")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  caller_method->set_code(assembler::ircode_from_string(param.caller_ir));
  cc.add_method(caller_method);
  auto* caller_cls = cc.create();

  run_dedup_pass({{canonical}, {target_lambda, caller_cls}});

  bool found = false;
  for (const auto& mie : *caller_method->get_code()) {
    if (mie.type != MFLOW_OPCODE || mie.insn->opcode() != param.opcode) {
      continue;
    }
    found = true;
    const auto* ref_type = get_referenced_type(mie.insn);
    ASSERT_NE(ref_type, nullptr);
    EXPECT_NE(ref_type, target_type)
        << "instruction must be redirected from non-canonical type";
    EXPECT_EQ(ref_type, canonical_type)
        << "instruction must reference the canonical type from dex 0";
  }
  EXPECT_TRUE(found) << "expected at least one " << param.name
                     << " instruction";
}

INSTANTIATE_TEST_SUITE_P(
    Singleton_InstructionRedirectTests,
    Singleton_InstructionRedirectTest,
    ::testing::Values(OpcodeRedirectParam{"SgetObject", OPCODE_SGET_OBJECT,
                                          R"((
          (sget-object "LSingletonTarget$0;.INSTANCE:LSingletonTarget$0;")
          (move-result-pseudo-object v0)
          (return-object v0)
        ))"},
                      OpcodeRedirectParam{"InvokeDirect", OPCODE_INVOKE_DIRECT,
                                          R"((
          (const v0 0)
          (invoke-direct (v0) "LSingletonTarget$0;.<init>:()V")
          (const v1 0)
          (return-object v1)
        ))"},
                      OpcodeRedirectParam{"InvokeVirtual",
                                          OPCODE_INVOKE_VIRTUAL,
                                          R"((
          (const v0 0)
          (invoke-virtual (v0) "LSingletonTarget$0;.invoke:()Ljava/lang/Object;")
          (move-result-object v1)
          (return-object v1)
        ))"}),
    [](const ::testing::TestParamInfo<OpcodeRedirectParam>& info) {
      return info.param.name;
    });

// A lambda that a method handle or method type names stays out of
// deduplication: redirecting the sget alone would hand code that expects the
// named lambda an instance of the canonical one. The method handles and method
// types are tool-generated bytecode.
class Singleton_NamedByMethodConstantTest
    : public KotlinLambdaDeduplicationPassTest,
      public ::testing::WithParamInterface<OpcodeRedirectParam> {};

TEST_P(Singleton_NamedByMethodConstantTest, KeepsLambda) {
  const auto& param = GetParam();

  // Canonical lambda in dex 0, target lambda + caller in dex 1.
  auto* canonical = create_lambda("LSingletonLambda$0;", true);
  auto* target_lambda = create_lambda("LSingletonTarget$0;", true);
  const auto* target_type = target_lambda->get_type();

  ClassCreator cc(DexType::make_type("LSingletonCaller;"));
  cc.set_super(type::java_lang_Object());
  auto* caller_method =
      DexMethod::make_method("LSingletonCaller;.call:()Ljava/lang/Object;")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  caller_method->set_code(assembler::ircode_from_string(std::string(R"((
    (sget-object "LSingletonTarget$0;.INSTANCE:LSingletonTarget$0;")
    (move-result-pseudo-object v0)
  )") + param.caller_ir + R"(
    (return-object v0)
  ))"));
  cc.add_method(caller_method);
  auto* caller_cls = cc.create();

  run_dedup_pass({{canonical}, {target_lambda, caller_cls}});

  bool found = false;
  for (const auto& mie : *caller_method->get_code()) {
    if (mie.type != MFLOW_OPCODE || mie.insn->opcode() != OPCODE_SGET_OBJECT) {
      continue;
    }
    found = true;
    EXPECT_EQ(get_referenced_type(mie.insn), target_type);
  }
  EXPECT_TRUE(found);
}

INSTANTIATE_TEST_SUITE_P(
    Singleton_NamedByMethodConstantTests,
    Singleton_NamedByMethodConstantTest,
    ::testing::Values(
        OpcodeRedirectParam{"InvokeInstanceHandle", OPCODE_CONST_METHOD_HANDLE,
                            R"(
    (const-method-handle invoke-instance "LSingletonTarget$0;.invoke:()Ljava/lang/Object;")
    (move-result-pseudo-object v1)
  )"},
        OpcodeRedirectParam{"StaticGetHandle", OPCODE_CONST_METHOD_HANDLE,
                            R"(
    (const-method-handle static-get "LSingletonTarget$0;.INSTANCE:LSingletonTarget$0;")
    (move-result-pseudo-object v1)
  )"},
        OpcodeRedirectParam{"MethodType", OPCODE_CONST_METHOD_TYPE,
                            R"(
    (const-method-type "(LSingletonTarget$0;)V")
    (move-result-pseudo-object v1)
  )"}),
    [](const ::testing::TestParamInfo<OpcodeRedirectParam>& info) {
      return info.param.name;
    });
