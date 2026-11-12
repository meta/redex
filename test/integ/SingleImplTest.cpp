/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "BaselineProfile.h"
#include "ConfigFiles.h"
#include "Creators.h"
#include "DexClass.h"
#include "DexUtil.h"
#include "IRAssembler.h"
#include "MethodProfiles.h"
#include "PassManager.h"
#include "RedexTest.h"
#include "SingleImpl.h"
#include "TypeUtil.h"

class SingleImplTest : public RedexIntegrationTest {
 public:
  void SetUp() override {
    // As in an app, `java.lang.Object` resolves to an external class.
    create_object_class();
    type_class(type::java_lang_Object())->set_external();

    DexType* m_helper = DexType::get_type("Lcom/facebook/redextest/Helper;");

    auto* create_intf = assembler::method_from_string(R"(
      (method (public static) "Lcom/facebook/redextest/Helper;.createIntf:()Ljava/lang/Object;"
       (
        (new-instance "Lcom/facebook/redextest/Impl;")
        (move-result-pseudo-object v0)
        (invoke-direct (v0) "Lcom/facebook/redextest/Impl;.<init>:()V")
        (return-object v0)
       )
      )
    )");

    auto* ret_intf = assembler::method_from_string(R"(
      (method (public static) "Lcom/facebook/redextest/Helper;.retIntf:()Lcom/facebook/redextest/Intf;"
       (
        (invoke-static () "Lcom/facebook/redextest/Helper;.createIntf:()Ljava/lang/Object;")
        (move-result-object v0)
        (return-object v0)
       )
      )
    )");

    type_class(m_helper)->add_method(create_intf);
    type_class(m_helper)->add_method(ret_intf);
  }
};

/**
 * If we replace an interface declared as the return type of a method with a
 * class, we want to make sure the return-object does not introduce a type
 * error. If the return-object relies on the more relaxed to-interface type
 * checking, we make sure a desired check-cast is inserted as needed.
 */
TEST_F(SingleImplTest, RemoveReturnTypeInterfaceTest) {
  auto scope = build_class_scope(stores);

  auto si = std::make_unique<SingleImplPass>();
  std::vector<Pass*> passes{si.get()};
  run_passes(passes);

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (invoke-static () "Lcom/facebook/redextest/Helper;.createIntf:()Ljava/lang/Object;")
     (move-result-object v0)
     (check-cast v0 "Lcom/facebook/redextest/Impl;")
     (move-result-pseudo-object v1)
     (return-object v1)
    )
  )");

  auto* ret_impl = DexMethod::get_method(
      "Lcom/facebook/redextest/Helper;.retIntf:()Lcom/"
      "facebook/redextest/Impl;");
  EXPECT_CODE_EQ(ret_impl->as_def()->get_code(), expected_code.get());
}

TEST_F(SingleImplTest, MovedDefaultMethodKeepsProfile) {
  auto* intf = type_class(DexType::get_type("Lcom/facebook/redextest/Intf;"));
  auto* impl = type_class(DexType::get_type("Lcom/facebook/redextest/Impl;"));
  ASSERT_NE(intf, nullptr);
  ASSERT_NE(impl, nullptr);
  impl->set_access(impl->get_access() | ACC_ABSTRACT);
  auto* old_override =
      DexMethod::get_method("Lcom/facebook/redextest/Impl;.get:()I")->as_def();
  auto stale_profiles = method_profiles::MethodProfiles::initialize(
      method_profiles::COLD_START, {{old_override, {0, 0, 100, 0}}});
  impl->remove_method(old_override);
  old_override->make_non_concrete();
  auto* source =
      DexMethod::get_method("Lcom/facebook/redextest/Intf;.get:()I")->as_def();
  ASSERT_NE(source, nullptr);
  source->set_access(ACC_PUBLIC);
  source->set_code(assembler::ircode_from_string(
      "((load-param-object v0) (const v1 42) (return v1))"));
  auto* create_intf =
      DexMethod::get_method(
          "Lcom/facebook/redextest/Helper;.createIntf:()Ljava/lang/Object;")
          ->as_def();
  create_intf->set_code(
      assembler::ircode_from_string("((const v0 0) (return-object v0))"));
  ClassCreator child(DexType::make_type("Lcom/facebook/redextest/ChildImpl;"));
  child.set_super(impl->get_type());
  child.set_access(ACC_PUBLIC);
  stores.front().get_dexen().front().push_back(child.create());
  auto* caller = assembler::method_from_string(R"(
    (method (public static) "Lcom/facebook/redextest/Helper;.call:(Lcom/facebook/redextest/Intf;)I"
      ((load-param-object v0)
       (invoke-interface (v0) "Lcom/facebook/redextest/Intf;.get:()I")
       (move-result v1)
       (return v1))))");
  type_class(caller->get_class())->add_method(caller);
  Json::Value config_json;
  config_json["redex"]["passes"].append("SingleImplPass");
  ConfigFiles config(config_json);
  config.parse_global_config();
  config.get_method_profiles() = std::move(stale_profiles);
  config.get_method_profiles().set_method_stats(method_profiles::COLD_START,
                                                source, {100, 20, 50, 0});
  baseline_profiles::BaselineProfileConfig profile_config;
  profile_config.interaction_configs[method_profiles::COLD_START] = {};
  baseline_profiles::BaselineProfileConfigMap profile_configs{
      {"default", profile_config}};
  auto before = baseline_profiles::get_default_baseline_profile(
      build_class_scope(stores), profile_configs, config.get_method_profiles(),
      /* coldstart_classes */ {},
      baseline_profiles::get_huge_method_max(config));
  ASSERT_TRUE(baseline_profiles::dex2oat_compiles(
      before, source, baseline_profiles::get_huge_method_max(config)));
  SingleImplPass pass;
  PassManager manager({&pass}, config);
  manager.run_passes(stores, config);
  auto* target_ref =
      DexMethod::get_method("Lcom/facebook/redextest/Impl;.get:()I");
  ASSERT_NE(target_ref, nullptr);
  ASSERT_TRUE(target_ref->is_def());
  auto* target = target_ref->as_def();
  ASSERT_NE(target, source);
  ASSERT_EQ(target, old_override);
  auto after = baseline_profiles::get_default_baseline_profile(
      build_class_scope(stores), profile_configs, config.get_method_profiles(),
      /* coldstart_classes */ {},
      baseline_profiles::get_huge_method_max(config));
  EXPECT_TRUE(baseline_profiles::dex2oat_compiles(
      after, target, baseline_profiles::get_huge_method_max(config)));
}

TEST_F(SingleImplTest, KeepsOverloadsOfDefaultMethods) {
  for (const auto* signature :
       {"Lcom/facebook/redextest/Printer;.print:(Lcom/facebook/redextest/"
        "GreetingImpl;)Ljava/lang/String;",
        "Lcom/facebook/redextest/Sender;.send:(Lcom/facebook/redextest/"
        "Message;)Ljava/lang/String;"}) {
    auto* default_method = assembler::method_from_string(
        std::string("(method (public) \"") + signature + R"(" (
          (load-param-object v1)
          (load-param-object v2)
          (const-string "default")
          (move-result-pseudo-object v0)
          (return-object v0)
        )))");
    type_class(default_method->get_class())->add_method(default_method);
  }

  auto si = std::make_unique<SingleImplPass>();
  std::vector<Pass*> passes{si.get()};
  run_passes(passes);

  auto is_def = [](const char* signature) {
    auto* method = DexMethod::get_method(signature);
    return method != nullptr && method->is_def();
  };
  // `ConsolePrinter.print(GreetingImpl)` would override the default method
  // `Printer.print(GreetingImpl)`.
  EXPECT_TRUE(
      is_def("Lcom/facebook/redextest/ConsolePrinter;.print:(Lcom/facebook/"
             "redextest/Greeting;)Ljava/lang/String;"));
  // `EmailSender.send(MessageImpl)` would override the default method
  // `Sender.send(MessageImpl)`.
  EXPECT_TRUE(
      is_def("Lcom/facebook/redextest/Sender;.send:(Lcom/facebook/redextest/"
             "Message;)Ljava/lang/String;"));
}
