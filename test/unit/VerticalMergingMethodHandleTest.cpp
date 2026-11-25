/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <string>
#include <vector>

#include <gtest/gtest.h>

#include "ConfigFiles.h"
#include "Creators.h"
#include "DexAnnotation.h"
#include "DexCallSite.h"
#include "DexClass.h"
#include "DexMethodHandle.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "PassManager.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"
#include "Resolver.h"
#include "TypeUtil.h"
#include "VerticalMerging.h"

namespace {

void add_method(ClassCreator& creator, const std::string& method) {
  creator.add_method(assembler::method_from_string(method));
}

void add_init(ClassCreator& creator,
              const std::string& cls,
              const std::string& super_init) {
  add_method(creator, "(method (public constructor) \"" + cls +
                          ".<init>:()V\" ((load-param-object v0) "
                          "(invoke-direct (v0) \"" +
                          super_init + "\") (return-void)))");
}

void add_run(ClassCreator& creator, const std::string& cls) {
  add_method(creator, "(method (public) \"" + cls +
                          ".run:()V\" ((load-param-object v0) (return-void)))");
}

// The method handles that the code of `method` holds.
std::vector<DexMethodHandle*> held_method_handles(const std::string& method) {
  std::vector<DexMethodHandle*> method_handles;
  auto* code = DexMethod::get_method(method)->as_def()->get_code();
  for (const auto& mie : InstructionIterable(code)) {
    for_each_method_handle(mie.insn, [&](const DexMethodHandle* handle) {
      method_handles.push_back(const_cast<DexMethodHandle*>(handle));
    });
  }
  return method_handles;
}

// `LBase;` has the only subclass `LImpl;`, and both have the method `run`.
// `LUser;` has the static method `use`.
class VerticalMergingMethodHandleTest : public RedexTest {
 protected:
  void SetUp() override { create_object_class(); }

  DexClass* make_base(DexAccessFlags access,
                      const std::vector<std::string>& extra_methods = {}) {
    ClassCreator creator(DexType::make_type("LBase;"));
    creator.set_access(access);
    creator.set_super(type::java_lang_Object());
    add_init(creator, "LBase;", "Ljava/lang/Object;.<init>:()V");
    add_run(creator, "LBase;");
    for (const auto& method : extra_methods) {
      add_method(creator, method);
    }
    return creator.create();
  }

  DexClass* make_impl(const std::vector<std::string>& extra_methods = {}) {
    ClassCreator creator(DexType::make_type("LImpl;"));
    creator.set_access(ACC_PUBLIC | ACC_FINAL);
    creator.set_super(DexType::make_type("LBase;"));
    add_init(creator, "LImpl;", "LBase;.<init>:()V");
    add_run(creator, "LImpl;");
    for (const auto& method : extra_methods) {
      add_method(creator, method);
    }
    return creator.create();
  }

  void make_user(const std::string& code) {
    ClassCreator creator(DexType::make_type("LUser;"));
    creator.set_super(type::java_lang_Object());
    add_method(creator,
               "(method (public static) \"LUser;.use:()V\" " + code + ")");
    m_user = creator.create();
  }

  // Runs the pass and returns how many classes remain.
  size_t run_pass(DexClass* base, DexClass* impl) {
    DexStore store("classes");
    store.add_classes({base, impl, m_user});
    std::vector<DexStore> stores;
    stores.emplace_back(std::move(store));
    VerticalMergingPass pass;
    PassManager manager({&pass});
    ConfigFiles config(Json::nullValue);
    config.parse_global_config();
    manager.run_passes(stores, config);
    return stores[0].get_dexen()[0].size();
  }

  DexClass* m_user{nullptr};
};

constexpr const char* kNewImpl = R"((
  (new-instance "LImpl;")
  (move-result-pseudo-object v0)
  (invoke-direct (v0) "LImpl;.<init>:()V")
  (return-void)
))";

} // namespace

// Vertical merging does not rewrite method handles, so the class of the method
// that a handle names stays: merging `LBase;` into its subclass would drop
// `LBase;.run`.
TEST_F(VerticalMergingMethodHandleTest,
       handleOfMethodOfSuperKeepsClassesApart) {
  auto* base = make_base(ACC_PUBLIC | ACC_ABSTRACT);
  auto* impl = make_impl();
  make_user(R"((
    (new-instance "LImpl;")
    (move-result-pseudo-object v0)
    (invoke-direct (v0) "LImpl;.<init>:()V")
    (const-method-handle invoke-instance "LBase;.run:()V")
    (move-result-pseudo-object v1)
    (return-void)
  ))");

  EXPECT_EQ(run_pass(base, impl), 3);
  EXPECT_EQ(impl->get_super_class(), base->get_type());
}

// Merging `LImpl;` into its superclass would drop `LImpl;.run`, which a handle
// names.
TEST_F(VerticalMergingMethodHandleTest,
       handleOfMethodOfSubclassKeepsClassesApart) {
  auto* base = make_base(ACC_PUBLIC);
  auto* impl = make_impl();
  make_user(R"((
    (new-instance "LBase;")
    (move-result-pseudo-object v0)
    (invoke-direct (v0) "LBase;.<init>:()V")
    (const-method-handle invoke-instance "LImpl;.run:()V")
    (move-result-pseudo-object v1)
    (return-void)
  ))");

  EXPECT_EQ(run_pass(base, impl), 3);
  EXPECT_EQ(impl->get_super_class(), base->get_type());
}

// An invoke-direct handle of `LBase;.run` held by `LImpl;`, which overrides
// it, runs `LImpl;.run` on Android 9 and, on Android 10 and later, what
// `Ljava/lang/Object;` has at the vtable index of `run` (see
// `resolve_method_handle`). Merging could change either, so the classes stay
// apart.
TEST_F(VerticalMergingMethodHandleTest,
       handleOfOverriddenMethodKeepsClassesApart) {
  auto* base = make_base(ACC_PUBLIC | ACC_ABSTRACT);
  auto* base_run = DexMethod::get_method("LBase;.run:()V");
  auto* impl = make_impl({R"(
    (method (public) "LImpl;.callSuper:()V"
     (
      (load-param-object v0)
      (const-method-handle invoke-direct "LBase;.run:()V")
      (move-result-pseudo-object v1)
      (return-void)
     )
    )
  )"});
  make_user(kNewImpl);

  EXPECT_EQ(run_pass(base, impl), 3);
  EXPECT_EQ(impl->get_super_class(), base->get_type());
  auto method_handles = held_method_handles("LImpl;.callSuper:()V");
  ASSERT_EQ(method_handles.size(), 1);
  EXPECT_EQ(method_handles[0]->type(), METHOD_HANDLE_TYPE_INVOKE_DIRECT);
  EXPECT_EQ(method_handles[0]->methodref(), base_run);
}

// The bootstrap method of an invoke-custom receives a lookup in the class of
// the code that holds it, which merging would move to another class.
TEST_F(VerticalMergingMethodHandleTest, invokeCustomKeepsClassesApart) {
  auto* base = make_base(ACC_PUBLIC | ACC_ABSTRACT, {R"(
    (method (public) "LBase;.link:()V"
     (
      (load-param-object v0)
      (invoke-static () "LBase;.placeholder:()V")
      (return-void)
     )
    )
  )"});
  auto* impl = make_impl();
  redex::make_invoke_custom(
      DexMethod::get_method("LBase;.link:()V")->as_def()->get_code(), "run",
      "()V");
  make_user(kNewImpl);

  EXPECT_EQ(run_pass(base, impl), 3);
  EXPECT_EQ(impl->get_super_class(), base->get_type());
}

// An invoke-direct handle of `LBase;.run` in `LBase;` itself calls
// `LBase;.run`, which `LBase;` declares, without virtual dispatch; merging
// `LBase;` into `LImpl;` would make it call `LImpl;.run`.
TEST_F(VerticalMergingMethodHandleTest,
       handleOfOwnMethodInSuperKeepsClassesApart) {
  auto* base = make_base(ACC_PUBLIC | ACC_ABSTRACT, {R"(
    (method (public) "LBase;.callOwn:()V"
     (
      (load-param-object v0)
      (const-method-handle invoke-direct "LBase;.run:()V")
      (move-result-pseudo-object v1)
      (return-void)
     )
    )
  )"});
  auto* impl = make_impl();
  make_user(kNewImpl);

  EXPECT_EQ(run_pass(base, impl), 3);
  EXPECT_EQ(impl->get_super_class(), base->get_type());
}

// A handle that names `LBase;.toString`, which `LBase;` inherits, names
// `LBase;`, which must go on existing.
TEST_F(VerticalMergingMethodHandleTest,
       handleOfInheritedMethodKeepsNamedClass) {
  auto* base = make_base(ACC_PUBLIC | ACC_ABSTRACT);
  auto* impl = make_impl({R"(
    (method (public) "LImpl;.callSuper:()V"
     (
      (load-param-object v0)
      (const-method-handle invoke-direct "LBase;.toString:()Ljava/lang/String;")
      (move-result-pseudo-object v1)
      (return-void)
     )
    )
  )"});
  make_user(kNewImpl);

  EXPECT_EQ(run_pass(base, impl), 3);
  EXPECT_EQ(impl->get_super_class(), base->get_type());
}

// An invoke-direct handle of `LBase;.toString` held by `LBase;` runs
// `Ljava/lang/Object;.toString`, which `LBase;` inherits. Merging `LBase;` into
// `LImpl;`, which overrides `toString`, would make the handle's holder
// `LImpl;`, whose implementation the handle would then run, so the classes
// stay apart.
TEST_F(VerticalMergingMethodHandleTest,
       handleOfInheritedMethodKeepsSuperWhenSubclassOverridesIt) {
  auto* base = make_base(ACC_PUBLIC | ACC_ABSTRACT, {R"(
    (method (public) "LBase;.callInherited:()V"
     (
      (load-param-object v0)
      (const-method-handle invoke-direct "LBase;.toString:()Ljava/lang/String;")
      (move-result-pseudo-object v1)
      (return-void)
     )
    )
  )"});
  auto* impl = make_impl({R"(
    (method (public) "LImpl;.toString:()Ljava/lang/String;"
     (
      (load-param-object v0)
      (const v1 0)
      (return-object v1)
     )
    )
  )"});
  make_user(kNewImpl);

  EXPECT_EQ(run_pass(base, impl), 3);
  EXPECT_EQ(impl->get_super_class(), base->get_type());
}

// Like an invoke, a handle of a method that `LImpl;` does not define keeps
// both classes apart.
TEST_F(VerticalMergingMethodHandleTest, handleOfMethodWithoutDefinition) {
  auto* base = make_base(ACC_PUBLIC | ACC_ABSTRACT);
  auto* impl = make_impl();
  make_user(R"((
    (new-instance "LImpl;")
    (move-result-pseudo-object v0)
    (invoke-direct (v0) "LImpl;.<init>:()V")
    (const-method-handle invoke-instance "LImpl;.hashCode:()I")
    (move-result-pseudo-object v1)
    (return-void)
  ))");

  EXPECT_EQ(run_pass(base, impl), 3);
  EXPECT_EQ(impl->get_super_class(), base->get_type());
}

// Merging `LBase;` into `LImpl;` makes the constructor `LUser;.<init>(LBase;)`
// collide with `LUser;.<init>(LImpl;)`, which a type reference update resolves
// by adding a parameter to one of them. A method handle cannot pass it.
TEST_F(VerticalMergingMethodHandleTest,
       constructorHandleKeepsTheTypesOfItsParameters) {
  auto* base = make_base(ACC_PUBLIC | ACC_ABSTRACT);
  auto* impl = make_impl();
  ClassCreator creator(DexType::make_type("LUser;"));
  creator.set_super(type::java_lang_Object());
  for (const auto* param : {"LBase;", "LImpl;"}) {
    add_method(creator, std::string(R"(
      (method (public constructor) "LUser;.<init>:()") +
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
  add_method(creator, R"(
    (method (public static) "LUser;.use:()V"
     (
      (new-instance "LImpl;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LImpl;.<init>:()V")
      (const-method-handle invoke-constructor "LUser;.<init>:(LBase;)V")
      (move-result-pseudo-object v1)
      (return-void)
     )
    )
  )");
  m_user = creator.create();

  EXPECT_EQ(run_pass(base, impl), 3);
  auto method_handles = held_method_handles("LUser;.use:()V");
  ASSERT_EQ(method_handles.size(), 1);
  EXPECT_EQ(method_handles[0]->methodref(),
            DexMethod::get_method("LUser;.<init>:(LBase;)V"));
}

// A const-class keeps its class, even an abstract one, from being merged away:
// code can compare the Class or key a map on it. A Class among the bootstrap
// arguments of a call site, which ART loads like a const-class, must too.
TEST_F(VerticalMergingMethodHandleTest, classArgumentKeepsItsClass) {
  auto* base = make_base(ACC_PUBLIC | ACC_ABSTRACT);
  auto* impl = make_impl();
  make_user(R"((
    (new-instance "LImpl;")
    (move-result-pseudo-object v0)
    (invoke-direct (v0) "LImpl;.<init>:()V")
    (invoke-static () "LUser;.placeholder:()V")
    (return-void)
  ))");
  auto* use = DexMethod::get_method("LUser;.use:()V")->as_def();
  std::vector<std::unique_ptr<DexEncodedValue>> args;
  args.push_back(
      std::make_unique<DexEncodedValueType>(DexType::make_type("[LBase;")));
  auto* callsite =
      redex::make_invoke_custom(use->get_code(), "run", "()V", std::move(args));

  EXPECT_EQ(run_pass(base, impl), 3);
  EXPECT_EQ(impl->get_super_class(), base->get_type());
  EXPECT_EQ(callsite->args().at(0)->show(), "[LBase;");
}

// A const-string that names a class keeps it from being merged away: code can
// load the class by that name. A string among the bootstrap arguments of a call
// site can name a class too.
TEST_F(VerticalMergingMethodHandleTest, stringArgumentKeepsTheClassItNames) {
  auto* base = make_base(ACC_PUBLIC | ACC_ABSTRACT);
  auto* impl = make_impl();
  make_user(R"((
    (new-instance "LImpl;")
    (move-result-pseudo-object v0)
    (invoke-direct (v0) "LImpl;.<init>:()V")
    (invoke-static () "LUser;.placeholder:()V")
    (return-void)
  ))");
  auto* use = DexMethod::get_method("LUser;.use:()V")->as_def();
  std::vector<std::unique_ptr<DexEncodedValue>> args;
  args.push_back(
      std::make_unique<DexEncodedValueString>(DexString::make_string("Base")));
  redex::make_invoke_custom(use->get_code(), "run", "()V", std::move(args));

  EXPECT_EQ(run_pass(base, impl), 3);
  EXPECT_EQ(impl->get_super_class(), base->get_type());
}

namespace {

// `LUser;.use` creates a `LBase;` and calls `LImpl;.make`, so `LImpl;` has no
// instances and merging it into `LBase;` drops its instance methods.
constexpr const char* kNewBaseAndMakeImpl = R"((
  (new-instance "LBase;")
  (move-result-pseudo-object v0)
  (invoke-direct (v0) "LBase;.<init>:()V")
  (invoke-static () "LImpl;.make:()V")
  (return-void)
))";

} // namespace

// An invoke-direct handle of `LImpl;.run` in `LImpl;` calls `LImpl;.run`, which
// `LImpl;` declares, without virtual dispatch. Merging `LImpl;` into its
// superclass would drop that method and move the static method that holds the
// handle into `LBase;`, so the classes stay apart.
TEST_F(VerticalMergingMethodHandleTest, handleOfOwnMethodKeepsMergedSubclass) {
  auto* base = make_base(ACC_PUBLIC);
  auto* impl = make_impl({R"(
    (method (public static) "LImpl;.make:()V"
     (
      (const-method-handle invoke-direct "LImpl;.run:()V")
      (move-result-pseudo-object v0)
      (return-void)
     )
    )
  )"});
  make_user(kNewBaseAndMakeImpl);

  EXPECT_EQ(run_pass(base, impl), 3);
  EXPECT_EQ(impl->get_super_class(), base->get_type());
  auto method_handles = held_method_handles("LImpl;.make:()V");
  ASSERT_EQ(method_handles.size(), 1);
  EXPECT_EQ(method_handles[0]->type(), METHOD_HANDLE_TYPE_INVOKE_DIRECT);
  EXPECT_EQ(method_handles[0]->methodref(),
            DexMethod::get_method("LImpl;.run:()V"));
}

// The same holds for a handle of a private method of `LImpl;`.
TEST_F(VerticalMergingMethodHandleTest,
       handleOfOwnPrivateMethodKeepsMergedSubclass) {
  auto* base = make_base(ACC_PUBLIC);
  auto* impl = make_impl({R"(
    (method (private) "LImpl;.p:()V"
     (
      (load-param-object v0)
      (return-void)
     )
    )
  )",
                          R"(
    (method (public static) "LImpl;.make:()V"
     (
      (const-method-handle invoke-direct "LImpl;.p:()V")
      (move-result-pseudo-object v0)
      (return-void)
     )
    )
  )"});
  make_user(kNewBaseAndMakeImpl);

  EXPECT_EQ(run_pass(base, impl), 3);
  EXPECT_EQ(impl->get_super_class(), base->get_type());
}

// An invoke-direct handle of `LImpl;.toString`, which `LImpl;` inherits, held
// by `LImpl;` runs the implementation that `LImpl;` inherits. Merging `LImpl;`
// into its superclass would leave the handle naming a class that no longer
// exists, so the classes stay apart.
TEST_F(VerticalMergingMethodHandleTest,
       inheritedMethodHandleNamingMergedSubclassKeepsIt) {
  auto* base = make_base(ACC_PUBLIC);
  auto* impl = make_impl({R"(
    (method (public static) "LImpl;.make:()V"
     (
      (const-method-handle invoke-direct "LImpl;.toString:()Ljava/lang/String;")
      (move-result-pseudo-object v0)
      (return-void)
     )
    )
  )"});
  make_user(kNewBaseAndMakeImpl);

  EXPECT_EQ(run_pass(base, impl), 3);
  EXPECT_EQ(impl->get_super_class(), base->get_type());
}

// Without method handles, `LBase;` merges into `LImpl;`.
TEST_F(VerticalMergingMethodHandleTest, classesWithoutHandlesMerge) {
  auto* base = make_base(ACC_PUBLIC | ACC_ABSTRACT);
  auto* impl = make_impl();
  make_user(kNewImpl);

  EXPECT_EQ(run_pass(base, impl), 2);
}

namespace {

std::unique_ptr<DexAnnotationSet> make_annotation_set(
    std::unique_ptr<DexEncodedValue> value) {
  auto annotation = std::make_unique<DexAnnotation>(
      DexType::make_type("LAnno;"), DAV_RUNTIME);
  annotation->add_element("value", std::move(value));
  auto annotation_set = std::make_unique<DexAnnotationSet>();
  annotation_set->add_annotation(std::move(annotation));
  return annotation_set;
}

} // namespace

// Like the types that the values of static fields and annotations name, the
// classes that their method handles name stay.
TEST_F(VerticalMergingMethodHandleTest,
       staticFieldValueHandleKeepsMergedSuper) {
  auto* base = make_base(ACC_PUBLIC | ACC_ABSTRACT);
  auto* impl = make_impl();
  make_user(kNewImpl);
  auto* field =
      DexField::make_field("LUser;.HANDLE:Ljava/lang/invoke/MethodHandle;")
          ->make_concrete(
              ACC_PUBLIC | ACC_STATIC | ACC_FINAL,
              std::make_unique<DexEncodedValueMethodHandle>(
                  redex::make_method_handle(METHOD_HANDLE_TYPE_INVOKE_INSTANCE,
                                            "LBase;.run:()V")));
  m_user->add_field(field);

  EXPECT_EQ(run_pass(base, impl), 3);
  EXPECT_EQ(redex::encoded_value_as<DexEncodedValueMethodHandle>(
                field->get_static_value())
                ->methodhandle()
                ->methodref(),
            DexMethod::get_method("LBase;.run:()V"));
}

TEST_F(VerticalMergingMethodHandleTest, annotationHandleKeepsMergedSubclass) {
  auto* base = make_base(ACC_PUBLIC);
  auto* impl = make_impl();
  make_user(R"((
    (new-instance "LBase;")
    (move-result-pseudo-object v0)
    (invoke-direct (v0) "LBase;.<init>:()V")
    (return-void)
  ))");
  ASSERT_TRUE(m_user->attach_annotation_set(make_annotation_set(
      std::make_unique<DexEncodedValueMethodHandle>(redex::make_method_handle(
          METHOD_HANDLE_TYPE_INVOKE_INSTANCE, "LImpl;.run:()V")))));

  EXPECT_EQ(run_pass(base, impl), 3);
  EXPECT_NE(DexMethod::get_method("LImpl;.run:()V"), nullptr);
}
