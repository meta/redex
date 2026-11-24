/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <string>
#include <vector>

#include <gtest/gtest.h>

#include "ClassMergingTestFixture.h"
#include "DexClass.h"
#include "DexMethodHandle.h"
#include "Resolver.h"
#include "ScopeHelper.h"
#include "Show.h"
#include "TypeUtil.h"
#include "Walkers.h"

using namespace class_merging_test;

namespace {

// `Lcom/redextest/Base;` has the mergeable subclasses `Lcom/redextest/A;` and
// `Lcom/redextest/B;`.
class ClassMergingMethodHandleTest : public ClassMergingTest {
 protected:
  void SetUp() override {
    m_scope = create_empty_scope();
    m_base = make_class("Lcom/redextest/Base;", type::java_lang_Object());
    add_ctor(m_base);
    add_virtual(m_base, "run");
    m_a = make_mergeable("Lcom/redextest/A;");
    m_b = make_mergeable("Lcom/redextest/B;");
  }

  // Runs one model for the subclasses of `Base` and returns whether `A` was
  // merged away.
  bool run_merging() {
    Json::Value model;
    model["name"] = "Handles";
    model["class_name_prefix"] = "Handles";
    model["roots"].append("Lcom/redextest/Base;");
    model["include_primary_dex"] = true;
    ClassMergingTest::run_merging({model});
    return std::none_of(m_scope.begin(), m_scope.end(), [](DexClass* cls) {
      return cls->get_type() == DexType::get_type("Lcom/redextest/A;");
    });
  }

  // The method handles that the code in the scope holds.
  std::vector<DexMethodHandle*> held_method_handles() {
    std::vector<DexMethodHandle*> method_handles;
    walk::opcodes(m_scope, [&](DexMethod*, IRInstruction* insn) {
      for_each_method_handle(insn, [&](const DexMethodHandle* handle) {
        method_handles.push_back(const_cast<DexMethodHandle*>(handle));
      });
    });
    return method_handles;
  }

  DexClass* m_a{nullptr};
  DexClass* m_b{nullptr};
};

} // namespace

// Merging would make the private method `A.p` public and virtual, and move the
// code that holds its invoke-direct handle, so `A` stays apart.
TEST_F(ClassMergingMethodHandleTest,
       invokeDirectHandleOfPrivateMethodKeepsClass) {
  add_method(m_a, R"(
    (method (private) "Lcom/redextest/A;.p:()V"
     (
      (load-param-object v0)
      (return-void)
     )
    )
  )");
  add_method(m_a, R"(
    (method (public) "Lcom/redextest/A;.use:()V"
     (
      (load-param-object v0)
      (const-method-handle invoke-direct "Lcom/redextest/A;.p:()V")
      (move-result-pseudo-object v1)
      (return-void)
     )
    )
  )");

  EXPECT_FALSE(run_merging());
}

// A handle in another class that names `A.run` keeps `A`, whose `run` merging
// would replace with a dispatch in the merger.
TEST_F(ClassMergingMethodHandleTest, handleOfMethodKeepsItsClass) {
  auto* user = make_class("Lcom/redextest/User;", type::java_lang_Object());
  add_method(user, R"(
    (method (public static) "Lcom/redextest/User;.use:()V"
     (
      (const-method-handle invoke-instance "Lcom/redextest/A;.run:()V")
      (move-result-pseudo-object v0)
      (return-void)
     )
    )
  )");

  EXPECT_FALSE(run_merging());
}

// A handle that names `Base.other` through `A` names `A`, which must go on
// existing for the handle to resolve.
TEST_F(ClassMergingMethodHandleTest, handleOfInheritedMethodKeepsNamedClass) {
  add_virtual(m_base, "other");
  auto* user = make_class("Lcom/redextest/User;", type::java_lang_Object());
  add_method(user, R"(
    (method (public static) "Lcom/redextest/User;.use:()V"
     (
      (const-method-handle invoke-instance "Lcom/redextest/A;.other:()V")
      (move-result-pseudo-object v0)
      (return-void)
     )
    )
  )");

  EXPECT_FALSE(run_merging());
}

// What an invoke-direct handle of a method that is not private runs depends on
// the class of the code that holds it: from `A`, which inherits `Base.other`,
// every ART version runs `Base.other`, but from the merger, which overrides
// `other` for `B`, Android 9 would run that override. So `A` stays apart.
TEST_F(ClassMergingMethodHandleTest,
       invokeDirectHandleOfInheritedMethodKeepsHolder) {
  add_virtual(m_base, "other");
  add_virtual(m_b, "other");
  add_method(m_a, R"(
    (method (public) "Lcom/redextest/A;.use:()V"
     (
      (load-param-object v0)
      (const-method-handle invoke-direct "Lcom/redextest/Base;.other:()V")
      (move-result-pseudo-object v1)
      (return-void)
     )
    )
  )");

  EXPECT_FALSE(run_merging());
}

// Without method handles, `A` and `B` merge.
TEST_F(ClassMergingMethodHandleTest, classesWithoutHandlesMerge) {
  add_method(m_a, R"(
    (method (public) "Lcom/redextest/A;.use:()V"
     (
      (load-param-object v0)
      (return-void)
     )
    )
  )");

  EXPECT_TRUE(run_merging());
}

// The merger has the superclass of `A` and `B`, so an invoke-super in their
// code calls the same method from the merger, and they merge.
TEST_F(ClassMergingMethodHandleTest, invokeSuperWithoutHandlesMerges) {
  add_method(m_a, R"(
    (method (public) "Lcom/redextest/A;.use:()V"
     (
      (load-param-object v0)
      (invoke-super (v0) "Lcom/redextest/Base;.run:()V")
      (return-void)
     )
    )
  )");

  EXPECT_TRUE(run_merging());
}

// Merging `A` and `B` makes the constructors `User(A)` and `User(B)` collide,
// which a type reference update resolves by adding a parameter to one of
// them. A method handle cannot pass it.
TEST_F(ClassMergingMethodHandleTest,
       constructorHandleKeepsTheTypesOfItsParameters) {
  auto* user = make_class("Lcom/redextest/User;", type::java_lang_Object());
  for (const auto* param : {"Lcom/redextest/A;", "Lcom/redextest/B;"}) {
    add_method(user, std::string(R"(
      (method (public constructor) "Lcom/redextest/User;.<init>:()") +
                         param + R"()V"
       (
        (load-param-object v0)
        (load-param-object v1)
        (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
        (return-void)
       )
      )
    )");
  }
  add_method(user, R"(
    (method (public static) "Lcom/redextest/User;.use:()V"
     (
      (const-method-handle invoke-constructor "Lcom/redextest/User;.<init>:(Lcom/redextest/A;)V")
      (move-result-pseudo-object v0)
      (return-void)
     )
    )
  )");

  EXPECT_FALSE(run_merging());
  auto method_handles = held_method_handles();
  ASSERT_EQ(method_handles.size(), 1);
  EXPECT_EQ(show(method_handles[0]->methodref()),
            "Lcom/redextest/User;.<init>:(Lcom/redextest/A;)V");
}
