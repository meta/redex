/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <algorithm>
#include <string>
#include <vector>

#include <gtest/gtest.h>

#include "ConfigFiles.h"
#include "Creators.h"
#include "DexClass.h"
#include "DexStore.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "PassManager.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"
#include "SingleImpl.h"

namespace {

// The interface `LI;` with the method `m` has the only implementation
// `LImpl;`. `LUser;.use` holds what each test names `LI;` in.
class SingleImplMethodHandleTest : public RedexTest {
 protected:
  void SetUp() override {
    // As in an app, `java.lang.Object` resolves to an external class.
    create_object_class();
    type_class(type::java_lang_Object())->set_external();
    ClassCreator intf(DexType::make_type("LI;"));
    intf.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
    intf.set_super(type::java_lang_Object());
    intf.add_method(DexMethod::make_method("LI;.m:()V")
                        ->make_concrete(ACC_PUBLIC | ACC_ABSTRACT,
                                        /* is_virtual */ true));
    m_intf = intf.create();

    ClassCreator impl(DexType::make_type("LImpl;"));
    impl.set_access(ACC_PUBLIC);
    impl.set_super(type::java_lang_Object());
    impl.add_interface(m_intf->get_type());
    impl.add_method(assembler::method_from_string(R"(
      (method (public constructor) "LImpl;.<init>:()V"
        ((load-param-object v0)
         (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
         (return-void))))"));
    impl.add_method(assembler::method_from_string(R"(
      (method (public) "LImpl;.m:()V"
        ((load-param-object v0) (return-void))))"));
    m_impl = impl.create();
  }

  IRCode* make_user(const std::string& code) {
    ClassCreator user(DexType::make_type("LUser;"));
    user.set_access(ACC_PUBLIC);
    user.set_super(type::java_lang_Object());
    user.add_method(assembler::method_from_string(R"(
      (method (public static) "LUser;.take:(LI;)V"
        ((load-param-object v0) (return-void))))"));
    auto* use = assembler::method_from_string(
        "(method (public static) \"LUser;.use:()V\" " + code + ")");
    user.add_method(use);
    m_user = user.create();
    return use->get_code();
  }

  // Runs the pass and returns whether `LI;` remains.
  bool run_pass_and_find_interface() {
    DexStore store("classes");
    store.add_classes({m_intf, m_impl, m_user});
    std::vector<DexStore> stores;
    stores.emplace_back(std::move(store));
    SingleImplPass pass;
    PassManager manager({&pass});
    ConfigFiles config(Json::nullValue);
    config.parse_global_config();
    manager.run_passes(stores, config);
    const auto& classes = stores[0].get_dexen()[0];
    return std::find(classes.begin(), classes.end(), m_intf) != classes.end();
  }

  DexClass* m_intf{nullptr};
  DexClass* m_impl{nullptr};
  DexClass* m_user{nullptr};
};

} // namespace

// Without anything that the pass cannot rewrite, it removes `LI;`.
TEST_F(SingleImplMethodHandleTest, removesInterfaceThatOnlyCodeNames) {
  make_user(R"((
    (new-instance "LImpl;")
    (move-result-pseudo-object v0)
    (invoke-direct (v0) "LImpl;.<init>:()V")
    (invoke-interface (v0) "LI;.m:()V")
    (invoke-static (v0) "LUser;.take:(LI;)V")
    (return-void)
  ))");
  EXPECT_FALSE(run_pass_and_find_interface());
}

// The handle would name the method of a removed interface.
TEST_F(SingleImplMethodHandleTest, keepsInterfaceWhoseMethodHandleCalls) {
  make_user(R"((
    (const-method-handle invoke-interface "LI;.m:()V")
    (move-result-pseudo-object v0)
    (return-void)
  ))");
  EXPECT_TRUE(run_pass_and_find_interface());
}

// The pass changes `take` to take `LImpl;`, so the method type of the handle,
// on which `invokeExact` callers depend, would change.
TEST_F(SingleImplMethodHandleTest, keepsInterfaceInPrototypeOfHandledMethod) {
  make_user(R"((
    (const-method-handle invoke-static "LUser;.take:(LI;)V")
    (move-result-pseudo-object v0)
    (return-void)
  ))");
  EXPECT_TRUE(run_pass_and_find_interface());
}

// The call-site prototype would name a removed interface.
TEST_F(SingleImplMethodHandleTest, keepsInterfaceInCallSitePrototype) {
  make_user(R"((
    (const v0 0)
    (new-instance "LImpl;")
    (move-result-pseudo-object v1)
    (invoke-direct (v1) "LImpl;.<init>:()V")
    (invoke-polymorphic (v0 v1) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "(LI;)V")
    (return-void)
  ))");
  EXPECT_TRUE(run_pass_and_find_interface());
}

// The method type of the call site would name a removed interface.
TEST_F(SingleImplMethodHandleTest, keepsInterfaceInCallSiteMethodType) {
  auto* code = make_user(R"((
    (invoke-static () "LUser;.placeholder:()LI;")
    (move-result-object v0)
    (return-void)
  ))");
  redex::make_invoke_custom(code, "make", "()LI;");
  EXPECT_TRUE(run_pass_and_find_interface());
}
