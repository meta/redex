/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <utility>

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

// `Parent` and its only subclass `Child`, which is abstract and has no methods.
std::pair<DexClass*, DexClass*> create_parent_and_abstract_child() {
  ClassCreator parent_creator(DexType::make_type("Lcom/redextest/Parent;"));
  parent_creator.set_access(ACC_PUBLIC);
  parent_creator.set_super(type::java_lang_Object());
  add_init(parent_creator, "Lcom/redextest/Parent;",
           "Ljava/lang/Object;.<init>:()V");
  auto* parent = parent_creator.create();

  ClassCreator child_creator(DexType::make_type("Lcom/redextest/Child;"));
  child_creator.set_access(ACC_PUBLIC | ACC_ABSTRACT);
  child_creator.set_super(parent->get_type());
  return {parent, child_creator.create()};
}

size_t run_pass_on(const std::vector<DexClass*>& classes) {
  DexStore store("classes");
  store.add_classes(classes);
  std::vector<DexStore> stores;
  stores.emplace_back(std::move(store));
  VerticalMergingPass pass;
  PassManager manager({&pass});
  ConfigFiles config(Json::nullValue);
  config.parse_global_config();
  manager.run_passes(stores, config);
  return stores[0].get_dexen()[0].size();
}

constexpr const char* kNewImpl = R"(
  (
    (new-instance "Lcom/redextest/Impl;")
    (move-result-pseudo-object v0)
    (invoke-direct (v0) "Lcom/redextest/Impl;.<init>:()V")
    (return-object v0)
  )
)";

class VerticalMergingTest : public RedexTest {
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

  size_t run_pass(DexClass* user) { return run_pass_on({base, impl, user}); }

  DexClass* base{nullptr};
  DexMethod* base_init{nullptr};
  DexClass* impl{nullptr};
};

} // namespace

// Without the protected constructor, `Base` merges with its only subclass.
TEST_F(VerticalMergingTest, mergesWithoutProtectedMethods) {
  EXPECT_EQ(run_pass(create_user(kNewImpl)), 2);
}

// Merging `Base` with `Impl` would move or rewrite `Base`'s constructor, which
// is excluded from optimization.
TEST_F(VerticalMergingTest, keepsClassOfProtectedMethod) {
  base_init->rstate.set_no_optimizations();
  auto* user = create_user(kNewImpl);

  EXPECT_EQ(run_pass(user), 3);
  EXPECT_EQ(impl->get_super_class(), base->get_type());
  EXPECT_EQ(base_init->get_proto()->get_args()->size(), 0);
}

// Merging `Impl` away would rewrite the protected method that creates it.
TEST_F(VerticalMergingTest, keepsTypesReferencedByProtectedCode) {
  auto* user = create_user(kNewImpl);
  auto* use = user->get_dmethods().front();
  use->rstate.set_no_optimizations();

  EXPECT_EQ(run_pass(user), 3);
  EXPECT_EQ(impl->get_super_class(), base->get_type());
}

// Java: `map.put(Base.class, a); map.put(Impl.class, b);`. Merging the abstract
// `Base` into its only subclass would make both literals the same class.
TEST_F(VerticalMergingTest, keepsAbstractClassWithClassLiteral) {
  auto* user = create_user(R"(
    (
      (const-class "Lcom/redextest/Base;")
      (move-result-pseudo-object v0)
      (const-class "Lcom/redextest/Impl;")
      (move-result-pseudo-object v1)
      (new-instance "Lcom/redextest/Impl;")
      (move-result-pseudo-object v2)
      (invoke-direct (v2) "Lcom/redextest/Impl;.<init>:()V")
      (return-object v0)
    )
  )");

  EXPECT_EQ(run_pass(user), 3);
  EXPECT_EQ(impl->get_super_class(), base->get_type());
}

// An array class literal names its element type's identity too.
TEST_F(VerticalMergingTest, keepsAbstractClassWithArrayClassLiteral) {
  auto* user = create_user(R"(
    (
      (const-class "[Lcom/redextest/Base;")
      (move-result-pseudo-object v0)
      (new-instance "Lcom/redextest/Impl;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1) "Lcom/redextest/Impl;.<init>:()V")
      (return-object v0)
    )
  )");

  EXPECT_EQ(run_pass(user), 3);
  EXPECT_EQ(impl->get_super_class(), base->get_type());
}

// A cast to the abstract `Base` does not observe its identity, so `Base` still
// merges into its only subclass.
TEST_F(VerticalMergingTest, mergesAbstractClassUsedInCast) {
  auto* user = create_user(R"(
    (
      (new-instance "Lcom/redextest/Impl;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "Lcom/redextest/Impl;.<init>:()V")
      (check-cast v0 "Lcom/redextest/Base;")
      (move-result-pseudo-object v1)
      (return-object v1)
    )
  )");

  EXPECT_EQ(run_pass(user), 2);
}

// `Child` is abstract, has no methods and is never instantiated, so it could
// merge into `Parent`, but `Child.class` would then be `Parent.class`.
TEST_F(VerticalMergingTest, keepsAbstractSubclassWithClassLiteral) {
  auto [parent, child] = create_parent_and_abstract_child();
  auto* user = create_user(R"(
    (
      (new-instance "Lcom/redextest/Parent;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "Lcom/redextest/Parent;.<init>:()V")
      (const-class "Lcom/redextest/Child;")
      (move-result-pseudo-object v1)
      (return-object v1)
    )
  )");

  EXPECT_EQ(run_pass_on({parent, child, user}), 3);
  EXPECT_EQ(child->get_super_class(), parent->get_type());
}

constexpr const char* kSynchronizedOnImplCallsS = R"(
  (
    (const-class "Lcom/redextest/Impl;")
    (move-result-pseudo-object v0)
    (monitor-enter v0)
    (invoke-static () "Lcom/redextest/Base;.s:()V")
    (monitor-exit v0)
    (new-instance "Lcom/redextest/Impl;")
    (move-result-pseudo-object v1)
    (invoke-direct (v1) "Lcom/redextest/Impl;.<init>:()V")
    (return-object v1)
  )
)";

// Java: `abstract class Base { static synchronized native void s(); }` and
// `synchronized (Impl.class) { Base.s(); }`. The runtime binds `s` to `Base`
// by name and locks `Base.class` around it; moving `s` to `Impl` would break
// the binding and make both locks `Impl.class`.
TEST_F(VerticalMergingTest, keepsClassWithStaticSynchronizedNativeMethod) {
  auto* s =
      DexMethod::make_method("Lcom/redextest/Base;.s:()V")
          ->make_concrete(
              ACC_PUBLIC | ACC_STATIC | ACC_SYNCHRONIZED | ACC_NATIVE, false);
  base->add_method(s);

  EXPECT_EQ(run_pass(create_user(kSynchronizedOnImplCallsS)), 3);
  EXPECT_EQ(s->get_class(), base->get_type());
}

// Java: `abstract class Base { native int n(); }`.
TEST_F(VerticalMergingTest, keepsClassWithNativeMethod) {
  auto* n = DexMethod::make_method("Lcom/redextest/Base;.n:()I")
                ->make_concrete(ACC_PUBLIC | ACC_NATIVE, true);
  base->add_method(n);

  EXPECT_EQ(run_pass(create_user(kNewImpl)), 3);
  EXPECT_EQ(n->get_class(), base->get_type());
}

// The merger keeps its methods and its name, so its native methods stay bound.
TEST_F(VerticalMergingTest, mergesIntoClassWithNativeMethod) {
  auto* n = DexMethod::make_method("Lcom/redextest/Impl;.n:()I")
                ->make_concrete(ACC_PUBLIC | ACC_NATIVE, true);
  impl->add_method(n);

  EXPECT_EQ(run_pass(create_user(kNewImpl)), 2);
  EXPECT_EQ(n->get_class(), impl->get_type());
}

// d8 compiles `static synchronized void s() {}` to a method that locks
// `Base.class` with `const-class` and `monitor-enter`, and keeps only
// `ACC_DECLARED_SYNCHRONIZED`, which has no effect at run time. The class
// literal keeps `Base` from being merged away.
TEST_F(VerticalMergingTest, keepsClassWithStaticSynchronizedMethod) {
  auto* s = DexMethod::make_method("Lcom/redextest/Base;.s:()V")
                ->make_concrete(
                    ACC_PUBLIC | ACC_STATIC | ACC_DECLARED_SYNCHRONIZED, false);
  s->set_code(assembler::ircode_from_string(R"(
    (
      (const-class "Lcom/redextest/Base;")
      (move-result-pseudo-object v0)
      (monitor-enter v0)
      (monitor-exit v0)
      (return-void)
    )
  )"));
  base->add_method(s);

  EXPECT_EQ(run_pass(create_user(kSynchronizedOnImplCallsS)), 3);
  EXPECT_EQ(s->get_class(), base->get_type());
}

// Java: `abstract class Child extends Parent { static native void m(); }`.
// `Child` has no code, so it could merge into `Parent`, which would move `m`.
TEST_F(VerticalMergingTest, keepsAbstractSubclassWithNativeMethod) {
  auto [parent, child] = create_parent_and_abstract_child();
  auto* m = DexMethod::make_method("Lcom/redextest/Child;.m:()V")
                ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_NATIVE, false);
  child->add_method(m);
  auto* user = create_user(R"(
    (
      (new-instance "Lcom/redextest/Parent;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "Lcom/redextest/Parent;.<init>:()V")
      (return-object v0)
    )
  )");

  EXPECT_EQ(run_pass_on({parent, child, user}), 3);
  EXPECT_EQ(m->get_class(), child->get_type());
}

namespace {

// Every place a class literal can name a class `X`.
enum class Site {
  kConstClass, // `const-class` in code
  kClassFieldValue, // `static final Class<?> TAG = X.class;`
  kObjectFieldValue, // `static final Object TAG = X.class;`
};

// Adds a class literal naming `type` to `user`, at `site`.
void add_class_literal(DexClass* user, Site site, DexType* type) {
  auto add_field = [&](DexType* field_type) {
    auto* field =
        DexField::make_field(user->get_type(), DexString::make_string("TAG"),
                             field_type)
            ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL,
                            std::make_unique<DexEncodedValueType>(type));
    user->add_field(field);
  };
  switch (site) {
  case Site::kConstClass: {
    auto* method = DexMethod::make_method(
                       "Lcom/redextest/User;.literal:()Ljava/lang/Object;")
                       ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
    method->set_code(assembler::ircode_from_string(
        "((const-class \"" + type->str_copy() +
        "\") (move-result-pseudo-object v0) (return-object v0))"));
    user->add_method(method);
    break;
  }
  case Site::kClassFieldValue:
    add_field(type::java_lang_Class());
    break;
  case Site::kObjectFieldValue:
    add_field(type::java_lang_Object());
    break;
  }
}

class VerticalMergingLiteralTest : public VerticalMergingTest,
                                   public ::testing::WithParamInterface<Site> {
};

constexpr const char* kNewParent = R"(
  (
    (new-instance "Lcom/redextest/Parent;")
    (move-result-pseudo-object v0)
    (invoke-direct (v0) "Lcom/redextest/Parent;.<init>:()V")
    (return-object v0)
  )
)";

} // namespace

// The class a literal names keeps its identity when it absorbs its parent.
TEST_P(VerticalMergingLiteralTest, mergesIntoClassNamedByLiteral) {
  auto* user = create_user(kNewImpl);
  add_class_literal(user, GetParam(), impl->get_type());

  EXPECT_EQ(run_pass(user), 2);
  EXPECT_EQ(impl->get_super_class(), type::java_lang_Object());
}

// Merging the named parent away would make the literal name its subclass.
TEST_P(VerticalMergingLiteralTest, keepsParentNamedByLiteral) {
  auto* user = create_user(kNewImpl);
  add_class_literal(user, GetParam(), base->get_type());

  EXPECT_EQ(run_pass(user), 3);
  EXPECT_EQ(impl->get_super_class(), base->get_type());
}

// Merging the named subclass away would make the literal name its parent.
TEST_P(VerticalMergingLiteralTest, keepsSubclassNamedByLiteral) {
  auto [parent, child] = create_parent_and_abstract_child();
  auto* user = create_user(kNewParent);
  add_class_literal(user, GetParam(), child->get_type());

  EXPECT_EQ(run_pass_on({parent, child, user}), 3);
  EXPECT_EQ(child->get_super_class(), parent->get_type());
}

INSTANTIATE_TEST_SUITE_P(CodeAndStaticValues,
                         VerticalMergingLiteralTest,
                         ::testing::Values(Site::kConstClass,
                                           Site::kClassFieldValue,
                                           Site::kObjectFieldValue));
