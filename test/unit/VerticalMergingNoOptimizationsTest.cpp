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

namespace {

DexMethod* add_init(ClassCreator& creator,
                    const std::string& cls,
                    const std::string& super_init) {
  auto* init = DexMethod::make_method(cls + ".<init>:()V")
                   ->make_concrete(ACC_PUBLIC | ACC_CONSTRUCTOR, false);
  init->set_code(assembler::ircode_from_string(
      "((load-param-object v0) (invoke-direct (v0) \"" + super_init +
      "\") (return-void))"));
  creator.add_method(init);
  return init;
}

DexClass* create_user(const std::string& code) {
  ClassCreator creator(DexType::make_type("Lcom/redextest/User;"));
  creator.set_super(type::java_lang_Object());
  auto* method =
      DexMethod::make_method("Lcom/redextest/User;.use:()Ljava/lang/Object;")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  method->set_code(assembler::ircode_from_string(code));
  creator.add_method(method);
  return creator.create();
}

constexpr const char* kNewImpl = R"(
  (
    (new-instance "Lcom/redextest/Impl;")
    (move-result-pseudo-object v0)
    (invoke-direct (v0) "Lcom/redextest/Impl;.<init>:()V")
    (return-object v0)
  )
)";

class VerticalMergingNoOptimizationsTest : public RedexTest {
 protected:
  void SetUp() override {
    create_object_class();
    ClassCreator base_creator(DexType::make_type("Lcom/redextest/Base;"));
    base_creator.set_access(ACC_PUBLIC | ACC_ABSTRACT);
    base_creator.set_super(type::java_lang_Object());
    base_init = add_init(base_creator, "Lcom/redextest/Base;",
                         "Ljava/lang/Object;.<init>:()V");
    base = base_creator.create();

    ClassCreator impl_creator(DexType::make_type("Lcom/redextest/Impl;"));
    impl_creator.set_access(ACC_PUBLIC | ACC_FINAL);
    impl_creator.set_super(base->get_type());
    add_init(impl_creator, "Lcom/redextest/Impl;",
             "Lcom/redextest/Base;.<init>:()V");
    impl = impl_creator.create();
  }

  size_t run_pass(DexClass* user) {
    DexStore store("classes");
    store.add_classes({base, impl, user});
    std::vector<DexStore> stores;
    stores.emplace_back(std::move(store));
    VerticalMergingPass pass;
    PassManager manager({&pass});
    ConfigFiles config(Json::nullValue);
    config.parse_global_config();
    manager.run_passes(stores, config);
    return stores[0].get_dexen()[0].size();
  }

  DexClass* base{nullptr};
  DexMethod* base_init{nullptr};
  DexClass* impl{nullptr};
};

} // namespace

// Without the protected constructor, `Base` merges with its only subclass.
TEST_F(VerticalMergingNoOptimizationsTest, mergesWithoutProtectedMethods) {
  EXPECT_EQ(run_pass(create_user(kNewImpl)), 2);
}

// Merging `Base` with `Impl` would move or rewrite `Base`'s constructor, which
// is excluded from optimization.
TEST_F(VerticalMergingNoOptimizationsTest, keepsClassOfProtectedMethod) {
  base_init->rstate.set_no_optimizations();
  auto* user = create_user(kNewImpl);

  EXPECT_EQ(run_pass(user), 3);
  EXPECT_EQ(impl->get_super_class(), base->get_type());
  EXPECT_EQ(base_init->get_proto()->get_args()->size(), 0);
}

// Merging `Impl` away would rewrite the protected method that creates it.
TEST_F(VerticalMergingNoOptimizationsTest,
       keepsTypesReferencedByProtectedCode) {
  auto* user = create_user(kNewImpl);
  auto* use = user->get_dmethods().front();
  use->rstate.set_no_optimizations();

  EXPECT_EQ(run_pass(user), 3);
  EXPECT_EQ(impl->get_super_class(), base->get_type());
}
