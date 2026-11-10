/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "Creators.h"
#include "DexUtil.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "MaterializeNullChecksPass.h"
#include "RedexTest.h"
#include "TypeUtil.h"

class MaterializeNullChecksTest : public RedexTest {
 public:
  ::sparta::s_expr run_pass(const std::string& code) {
    create_object_class();
    DexMethod::make_method("Ljava/lang/Object;.getClass:()Ljava/lang/Class;");

    ClassCreator null_check(DexType::make_type("Lredex/$NullCheck;"));
    null_check.set_super(type::java_lang_Object());
    for (const auto& [signature, body] :
         std::initializer_list<std::pair<const char*, const char*>>{
             {"Lredex/$NullCheck;.null_check:(Ljava/lang/Object;)V",
              "((load-param-object v0) (return-void))"},
             {"Lredex/$NullCheck;.other:()V", "((return-void))"}}) {
      auto* method = DexMethod::make_method(signature)->make_concrete(
          ACC_PUBLIC | ACC_STATIC, false);
      method->set_code(assembler::ircode_from_string(body));
      null_check.add_method(method);
    }

    ClassCreator creator(DexType::make_type("LTest;"));
    creator.set_super(type::java_lang_Object());
    auto* method = DexMethod::make_method("LTest;.foo:(Ljava/lang/Object;)V")
                       ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
    method->set_code(assembler::ircode_from_string(code));
    creator.add_method(method);

    MaterializeNullChecksPass pass;
    PassManager manager({&pass});
    ConfigFiles config(Json::nullValue);
    config.parse_global_config();
    DexStore store("classes");
    store.add_classes({null_check.create(), creator.create()});
    std::vector<DexStore> stores;
    stores.emplace_back(std::move(store));
    manager.run_passes(stores, config);

    return assembler::to_s_expr(method->get_code());
  }
};

TEST_F(MaterializeNullChecksTest, rewritesOnlyTheIntrinsic) {
  auto actual = run_pass(R"(
    (
      (load-param-object v0)
      (invoke-static (v0) "Lredex/$NullCheck;.null_check:(Ljava/lang/Object;)V")
      (invoke-static () "Lredex/$NullCheck;.other:()V")
      (return-void)
    )
  )");
  auto expected = assembler::to_s_expr(assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (invoke-virtual (v0) "Ljava/lang/Object;.getClass:()Ljava/lang/Class;")
      (invoke-static () "Lredex/$NullCheck;.other:()V")
      (return-void)
    )
  )")
                                           .get());
  EXPECT_EQ(actual, expected) << actual.str();
}
