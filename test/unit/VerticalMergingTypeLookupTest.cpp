/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "ConfigFiles.h"
#include "Creators.h"
#include "DexClass.h"
#include "IRAssembler.h"
#include "PassManager.h"
#include "RedexTest.h"
#include "TypeUtil.h"
#include "VerticalMerging.h"

class VerticalMergingTypeLookupTest : public RedexTest {};

// Only the array type `[Lmissing/T;` exists. Recording merge blockers must not
// create its element type `Lmissing/T;`: whether that type exists decides
// whether a type-like string "missing.T" counts as a type reference.
TEST_F(VerticalMergingTypeLookupTest, doesNotCreateArrayElementTypes) {
  create_object_class();

  ClassCreator user_creator(DexType::make_type("Lcom/redextest/User;"));
  user_creator.set_super(type::java_lang_Object());
  auto* check =
      DexMethod::make_method("Lcom/redextest/User;.check:(Ljava/lang/Object;)Z")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  check->set_code(assembler::ircode_from_string(R"(
    (
      (load-param-object v1)
      (instance-of v1 "[Lmissing/T;")
      (move-result-pseudo v0)
      (return v0)
    )
  )"));
  user_creator.add_method(check);
  auto* user_cls = user_creator.create();

  ASSERT_NE(DexType::get_type("[Lmissing/T;"), nullptr);
  ASSERT_EQ(DexType::get_type("Lmissing/T;"), nullptr);

  DexStore store("classes");
  store.add_classes({user_cls});
  std::vector<DexStore> stores;
  stores.emplace_back(std::move(store));

  VerticalMergingPass pass;
  PassManager manager({&pass});
  ConfigFiles config(Json::nullValue);
  config.parse_global_config();
  manager.run_passes(stores, config);

  EXPECT_EQ(DexType::get_type("Lmissing/T;"), nullptr);
}
