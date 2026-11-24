/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>
#include <string>
#include <utility>
#include <vector>

#include "ClassReorderingPass.h"
#include "ConfigFiles.h"
#include "Creators.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "PassManager.h"
#include "RedexTest.h"
#include "TypeUtil.h"

namespace {

class FeatureCheckPass : public Pass {
 public:
  explicit FeatureCheckPass(const std::string& name) : Pass(name) {}
  void run_pass(DexStoresVector&, ConfigFiles&, PassManager&) override {
    ++runs;
  }
  size_t runs{0};
};

struct PassManagerFeatureTest : public RedexTest {
  static std::vector<DexStore> stores(DexMethod* method,
                                      bool is_interface = false) {
    ClassCreator creator(method->get_class());
    creator.set_super(type::java_lang_Object());
    creator.set_access(is_interface ? ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT
                                    : ACC_PUBLIC);
    creator.add_method(method);
    DexStore store("classes");
    store.add_classes({creator.create()});
    std::vector<DexStore> result;
    result.push_back(std::move(store));
    return result;
  }

  static void run_rejecting(DexMethod* method,
                            int version,
                            const std::string& expected,
                            bool is_interface = false) {
    auto input = stores(method, is_interface);
    FeatureCheckPass pass("FeatureCheckPass");
    ClassReorderingPass reorder;
    ConfigFiles config(Json::nullValue);
    config.parse_global_config();
    RedexOptions options;
    options.input_dex_version = version;
    PassManager manager({&pass, &reorder}, config, options);
    try {
      manager.run_passes(input, config);
      FAIL() << "Unsupported feature was accepted";
    } catch (const RedexException& error) {
      EXPECT_NE(std::string::npos, std::string(error.what()).find(expected))
          << error.what();
    }
    EXPECT_EQ(0, pass.runs);
  }
};

TEST_F(PassManagerFeatureTest, featureless_versions_pass_cached_checks) {
  for (int version : {35, 37, 38, 39}) {
    auto* method = assembler::method_from_string(
        "(method (public static) \"LFeatureFree" + std::to_string(version) +
        ";.empty:()V\" ((return-void)))");
    auto input = stores(method);
    FeatureCheckPass first("FirstFeatureCheck");
    FeatureCheckPass second("SecondFeatureCheck");
    ClassReorderingPass reorder;
    ConfigFiles config(Json::nullValue);
    config.parse_global_config();
    RedexOptions options;
    options.input_dex_version = version;
    PassManager manager({&first, &second, &reorder}, config, options);
    EXPECT_NO_THROW(manager.run_passes(input, config));
    EXPECT_EQ(1, first.runs);
    EXPECT_EQ(1, second.runs);
    EXPECT_NO_THROW(manager.run_passes(input, config));
    EXPECT_EQ(2, first.runs);
    EXPECT_EQ(2, second.runs);
  }
}

TEST_F(PassManagerFeatureTest, default_interface_methods_still_reject) {
  auto* method = assembler::method_from_string(R"(
    (method (public) "LFeatureInterface;.body:()V"
      ((load-param-object v0)(return-void))))");
  run_rejecting(method, 37,
                "Input APK has dex37 features that this pass FeatureCheckPass "
                "doesn't support",
                true);
}

TEST_F(PassManagerFeatureTest,
       earlier_features_in_newer_versions_still_reject) {
  for (int version : {38, 39}) {
    auto* method = assembler::method_from_string(
        "(method (public) \"LFeatureInterface" + std::to_string(version) +
        ";.body:()V\" ((load-param-object v0)(return-void)))");
    run_rejecting(
        method, version,
        "Input APK has dex37 features that this pass FeatureCheckPass "
        "doesn't support",
        true);
  }
}

TEST_F(PassManagerFeatureTest, method_type_constants_still_reject) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFeatureMethodType;.constant:()V"
      ((return-void))))");
  method->get_code()->set_registers_size(1);
  method->get_code()->insert_after(
      nullptr,
      {(new IRInstruction(OPCODE_CONST_METHOD_TYPE))
           ->set_proto(DexProto::make_proto(type::_void(),
                                            DexTypeList::make_type_list({}))),
       (new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT))->set_dest(0)});
  run_rejecting(method, 39,
                "Input APK has dex39 features that this pass FeatureCheckPass "
                "doesn't support");
}

} // namespace
