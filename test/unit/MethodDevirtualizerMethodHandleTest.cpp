/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <string>
#include <string_view>
#include <vector>

#include <gtest/gtest.h>

#include "Creators.h"
#include "DexClass.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "MethodDevirtualizer.h"
#include "RedexTest.h"
#include "Walkers.h"

namespace {

DexClass* make_class(const std::string& name,
                     DexType* super,
                     const std::vector<std::string>& methods) {
  ClassCreator creator(DexType::make_type(name));
  creator.set_access(ACC_PUBLIC);
  creator.set_super(super);
  for (const auto& method : methods) {
    creator.add_method(assembler::method_from_string(method));
  }
  return creator.create();
}

// `LFoo;` has the final methods `m` and `n` and the private method `p`, which
// do not use `this`, and the final method `self`, which returns it. Only the
// handles in each test call them.
class MethodDevirtualizerMethodHandleTest : public RedexTest {
 protected:
  void SetUp() override {
    create_object_class();
    m_foo = make_class("LFoo;", type::java_lang_Object(),
                       {R"((method (public final) "LFoo;.m:()V"
              ((load-param-object v0) (return-void))))",
                        R"((method (public final) "LFoo;.n:()V"
              ((load-param-object v0) (return-void))))",
                        R"((method (private) "LFoo;.p:()V"
              ((load-param-object v0) (return-void))))",
                        R"((method (public final) "LFoo;.self:()LFoo;"
              ((load-param-object v0) (return-object v0))))"});
    m_sub = make_class("LSub;", m_foo->get_type(), {});
  }

  void make_user(const std::string& code) {
    m_user = make_class(
        "LUser;", type::java_lang_Object(),
        {"(method (public static) \"LUser;.use:()V\" " + code + ")"});
  }

  // Runs the devirtualizer with every kind of staticization enabled.
  void devirtualize() {
    Scope scope{m_foo, m_sub, m_user};
    walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });
    UnorderedSet<DexType*> do_not_devirt_anno;
    MethodDevirtualizer devirtualizer(
        /* vmethods_not_using_this */ true, /* vmethods_using_this */ true,
        /* dmethods_not_using_this */ true, /* dmethods_using_this */ true,
        /* ignore_keep */ false, do_not_devirt_anno);
    devirtualizer.devirtualize_methods(scope);
  }

  // Whether `LFoo;`'s method `name` is static; staticization changes its
  // prototype, so it is found by name.
  bool is_static_method(std::string_view name) const {
    for (auto* method : m_foo->get_all_methods()) {
      if (method->get_name()->str() == name) {
        return is_static(method);
      }
    }
    ADD_FAILURE() << "no method " << name;
    return false;
  }

  DexClass* m_foo{nullptr};
  DexClass* m_sub{nullptr};
  DexClass* m_user{nullptr};
};

} // namespace

// Making `m` static without `this` would leave the handle passing a receiver
// to a method that takes none.
TEST_F(MethodDevirtualizerMethodHandleTest, keepsVirtualMethodThatHandleCalls) {
  make_user(R"((
    (const-method-handle invoke-instance "LFoo;.m:()V")
    (move-result-pseudo-object v0)
    (return-void)
  ))");
  devirtualize();
  EXPECT_FALSE(is_static_method("m"));
  EXPECT_TRUE(is_static_method("n"));
}

// Making `self` static with `this` as its first parameter would give an
// invoke-static handle of it the method type (LFoo;)LFoo;, but the handle,
// which names it through the subclass, has the method type (LSub;)LFoo;.
TEST_F(MethodDevirtualizerMethodHandleTest,
       keepsMethodUsingThisThatHandleCallsOnSubclass) {
  make_user(R"((
    (const-method-handle invoke-instance "LSub;.self:()LFoo;")
    (move-result-pseudo-object v0)
    (return-void)
  ))");
  devirtualize();
  EXPECT_FALSE(is_static_method("self"));
  EXPECT_TRUE(is_static_method("n"));
}

// The private method `p` is called through an invoke-direct handle in its own
// class.
TEST_F(MethodDevirtualizerMethodHandleTest, keepsPrivateMethodThatHandleCalls) {
  m_foo->add_method(assembler::method_from_string(R"(
    (method (public static) "LFoo;.use:()V"
      ((const-method-handle invoke-direct "LFoo;.p:()V")
       (move-result-pseudo-object v0)
       (return-void))))"));
  make_user("((return-void))");
  devirtualize();
  EXPECT_FALSE(is_static_method("p"));
  EXPECT_TRUE(is_static_method("n"));
}
