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
#include "RClass.h"
#include "RedexTest.h"
#include "TypeUtil.h"
#include "VerticalMerging.h"

namespace {

DexClass* create_r_inner_class(const char* name,
                               DexType* super,
                               const char* super_init) {
  auto* type = DexType::make_type(name);
  ClassCreator creator(type);
  creator.set_access(ACC_PUBLIC);
  creator.set_super(super);
  auto* init = DexMethod::make_method(std::string(name) + ".<init>:()V")
                   ->make_concrete(ACC_PUBLIC | ACC_CONSTRUCTOR, false);
  init->set_code(assembler::ircode_from_string(
      std::string("((load-param-object v0) (invoke-direct (v0) \"") +
      super_init + "\") (return-void))"));
  creator.add_method(init);
  return creator.create();
}

} // namespace

class VerticalMergingRClassTest : public RedexTest {};

// A generated "union" R inner class holds every resource field, and a
// per-package R inner class is an empty subclass of it. Once all other
// subclasses are gone, the union has a single child, but merging the two would
// leave an R class with a constructor the resources code does not accept.
TEST_F(VerticalMergingRClassTest, doesNotMergeRClasses) {
  create_object_class();

  auto* union_cls = create_r_inner_class("Lcom/redextest/union/R$attr;",
                                         type::java_lang_Object(),
                                         "Ljava/lang/Object;.<init>:()V");
  auto* field =
      DexField::make_field("Lcom/redextest/union/R$attr;.foo:I")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL,
                          DexEncodedValue::zero_for_type(type::_int()));
  union_cls->add_field(field);

  auto* proxy_cls =
      create_r_inner_class("Lcom/redextest/proxy/R$attr;",
                           union_cls->get_type(),
                           "Lcom/redextest/union/R$attr;.<init>:()V");

  ClassCreator user_creator(DexType::make_type("Lcom/redextest/User;"));
  user_creator.set_super(type::java_lang_Object());
  auto* use = DexMethod::make_method("Lcom/redextest/User;.use:()I")
                  ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  use->set_code(assembler::ircode_from_string(R"(
    (
      (sget "Lcom/redextest/union/R$attr;.foo:I")
      (move-result-pseudo v0)
      (return v0)
    )
  )"));
  user_creator.add_method(use);
  auto* user_cls = user_creator.create();

  DexStore store("classes");
  store.add_classes({union_cls, proxy_cls, user_cls});
  std::vector<DexStore> stores;
  stores.emplace_back(std::move(store));

  VerticalMergingPass pass;
  PassManager manager({&pass});
  ConfigFiles config(Json::nullValue);
  config.parse_global_config();
  manager.run_passes(stores, config);

  EXPECT_EQ(proxy_cls->get_super_class(), union_cls->get_type());
  resources::RClassReader r_class_reader(config.get_global_config());
  EXPECT_TRUE(r_class_reader.is_r_class(union_cls));
  EXPECT_TRUE(r_class_reader.is_r_class(proxy_cls));
}
