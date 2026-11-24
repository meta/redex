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
#include "KotlinCompanionOptimizationPass.h"
#include "PassManager.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"

namespace {

// `LFoo;` holds its companion `LFoo$Companion;` in the static field
// `Companion`; the companion's method `bar` does not use `this`.
// `LUser;.use` holds what each test names the companion in.
class KotlinCompanionMethodHandleTest : public RedexTest {
 protected:
  void SetUp() override {
    // As in an app, `java.lang.Object` resolves to an external class.
    create_object_class();
    type_class(type::java_lang_Object())->set_external();

    ClassCreator companion(DexType::make_type("LFoo$Companion;"));
    companion.set_access(ACC_PUBLIC | ACC_FINAL);
    companion.set_super(type::java_lang_Object());
    companion.add_method(assembler::method_from_string(R"(
      (method (public constructor) "LFoo$Companion;.<init>:()V"
        ((load-param-object v0)
         (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
         (return-void))))"));
    m_bar = assembler::method_from_string(R"(
      (method (public final) "LFoo$Companion;.bar:()V"
        ((load-param-object v0) (return-void))))");
    companion.add_method(m_bar);
    m_companion = companion.create();

    ClassCreator outer(DexType::make_type("LFoo;"));
    outer.set_access(ACC_PUBLIC);
    outer.set_super(type::java_lang_Object());
    auto* field = DexField::make_field("LFoo;.Companion:LFoo$Companion;")
                      ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL);
    outer.add_field(field);
    m_outer = outer.create();
  }

  void make_user(const std::string& code) {
    ClassCreator user(DexType::make_type("LUser;"));
    user.set_access(ACC_PUBLIC);
    user.set_super(type::java_lang_Object());
    user.add_method(assembler::method_from_string(
        "(method (public static) \"LUser;.use:()V\" " + code + ")"));
    m_user = user.create();
  }

  // Runs the pass and returns whether it moved `bar` into `LFoo;`.
  bool run_pass_and_check_relocated() {
    DexStore store("classes");
    store.add_classes({m_companion, m_outer, m_user});
    std::vector<DexStore> stores;
    stores.emplace_back(std::move(store));
    KotlinCompanionOptimizationPass pass;
    PassManager manager({&pass});
    ConfigFiles config(Json::nullValue);
    config.parse_global_config();
    manager.run_passes(stores, config);
    return m_bar->get_class() == m_outer->get_type();
  }

  DexMethod* m_bar{nullptr};
  DexClass* m_companion{nullptr};
  DexClass* m_outer{nullptr};
  DexClass* m_user{nullptr};
};

} // namespace

// Without anything that the pass cannot rewrite, it moves `bar`.
TEST_F(KotlinCompanionMethodHandleTest, relocatesCompanionThatOnlyCodeNames) {
  make_user(R"((
    (sget-object "LFoo;.Companion:LFoo$Companion;")
    (move-result-pseudo-object v0)
    (invoke-virtual (v0) "LFoo$Companion;.bar:()V")
    (return-void)
  ))");
  EXPECT_TRUE(run_pass_and_check_relocated());
}

// Moving `bar` would leave the handle passing a companion instance, as an
// invoke-instance handle, to a static method that takes none.
TEST_F(KotlinCompanionMethodHandleTest, keepsCompanionWhoseMethodHandleCalls) {
  make_user(R"((
    (const-method-handle invoke-instance "LFoo$Companion;.bar:()V")
    (move-result-pseudo-object v0)
    (return-void)
  ))");
  EXPECT_FALSE(run_pass_and_check_relocated());
  EXPECT_FALSE(is_static(m_bar));
}

// The pass removes `LFoo;.Companion`, which the handle reads.
TEST_F(KotlinCompanionMethodHandleTest, keepsCompanionWhoseFieldHandleGets) {
  make_user(R"((
    (const-method-handle static-get "LFoo;.Companion:LFoo$Companion;")
    (move-result-pseudo-object v0)
    (return-void)
  ))");
  EXPECT_FALSE(run_pass_and_check_relocated());
  auto* field = DexField::get_field("LFoo;.Companion:LFoo$Companion;");
  ASSERT_NE(field, nullptr);
  const auto& sfields = m_outer->get_sfields();
  EXPECT_NE(std::find(sfields.begin(), sfields.end(), field), sfields.end());
}

// A method type that names the companion keeps it too: like a call-site
// prototype, it can describe a call that passes the companion instance, which
// the pass does not track.
TEST_F(KotlinCompanionMethodHandleTest, keepsCompanionThatAMethodTypeNames) {
  make_user(R"((
    (const-method-type "(LFoo$Companion;)V")
    (move-result-pseudo-object v0)
    (return-void)
  ))");
  EXPECT_FALSE(run_pass_and_check_relocated());
}

// What an invoke-direct handle of `Object.hashCode` in `bar` runs depends on
// the class of the code that holds it: from the companion, which inherits
// `Object.hashCode`, every ART version runs `Object.hashCode`, but from
// `LFoo;`, which overrides it, Android 9 would run `LFoo;.hashCode`. So `bar`
// stays.
TEST_F(KotlinCompanionMethodHandleTest,
       keepsMethodWhoseHandleDependsOnItsClass) {
  m_bar->set_code(assembler::ircode_from_string(R"((
    (load-param-object v0)
    (const-method-handle invoke-direct "Ljava/lang/Object;.hashCode:()I")
    (move-result-pseudo-object v1)
    (return-void)
  ))"));
  m_outer->add_method(assembler::method_from_string(R"(
    (method (public) "LFoo;.hashCode:()I"
      ((load-param-object v0) (const v1 0) (return v1))))"));
  make_user(R"((
    (sget-object "LFoo;.Companion:LFoo$Companion;")
    (move-result-pseudo-object v0)
    (invoke-virtual (v0) "LFoo$Companion;.bar:()V")
    (return-void)
  ))");
  EXPECT_FALSE(run_pass_and_check_relocated());
}

// The bootstrap method of an invoke-custom receives a lookup in the class of
// the code that holds it, so `bar` stays.
TEST_F(KotlinCompanionMethodHandleTest, keepsMethodWithInvokeCustom) {
  auto code = assembler::ircode_from_string(R"((
    (load-param-object v0)
    (invoke-static () "LFoo$Companion;.placeholder:()V")
    (return-void)
  ))");
  redex::make_invoke_custom(code.get(), "run", "()V");
  m_bar->set_code(std::move(code));
  make_user(R"((
    (sget-object "LFoo;.Companion:LFoo$Companion;")
    (move-result-pseudo-object v0)
    (invoke-virtual (v0) "LFoo$Companion;.bar:()V")
    (return-void)
  ))");
  EXPECT_FALSE(run_pass_and_check_relocated());
}
