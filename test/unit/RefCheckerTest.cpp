/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include <algorithm>

#include "Creators.h"
#include "DexStore.h"
#include "IRAssembler.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"
#include "RefChecker.h"
#include "Show.h"
#include "TypeUtil.h"

class RefCheckerTest : public RedexTest {};

namespace {

DexMethod* make_method(const std::string& code) {
  return assembler::method_from_string(
      R"((method (public static) "LFoo;.bar:(Ljava/lang/Object;)V" )" + code +
      ")");
}

CodeRefs code_refs(DexMethod* method) {
  method->get_code()->build_cfg();
  return CodeRefs(method);
}

bool contains(const std::vector<const DexType*>& types, const char* name) {
  return std::find(types.begin(), types.end(), DexType::get_type(name)) !=
         types.end();
}

// Defines `method` in a new class of its own.
DexMethod* define_in_own_class(const char* method) {
  auto* def = DexMethod::make_method(method)->make_concrete(
      ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);
  ClassCreator creator(def->get_class());
  creator.set_super(type::java_lang_Object());
  creator.add_method(def);
  creator.create();
  return def;
}

} // namespace

// A hierarchy may end in a `java.lang.Object` that the input defines, as in
// tests, rather than in the external one of the SDK.
TEST_F(RefCheckerTest, typeWhoseHierarchyEndsInDefinedObject) {
  ClassCreator object_creator(type::java_lang_Object());
  object_creator.set_access(ACC_PUBLIC);
  auto* object = object_creator.create();
  ClassCreator foo_creator(DexType::make_type("LFoo;"));
  foo_creator.set_super(type::java_lang_Object());
  foo_creator.set_access(ACC_PUBLIC);
  auto* foo = foo_creator.create();
  DexStore store("classes");
  store.add_classes({object, foo});
  DexStoresVector stores({store});
  XStoreRefs xstores(stores, /* normal_primary_dex */ false);
  RefChecker checker(&xstores, xstores.get_store_idx(foo->get_type()),
                     /* min_sdk_api */ nullptr);

  EXPECT_TRUE(checker.check_type(foo->get_type()));
  EXPECT_TRUE(checker.check_type(DexType::make_type("[LFoo;")));
}

// Code in a package may name a public class, or a package-private class of
// the same package, and arrays of either.
TEST_F(RefCheckerTest, typeFromPackage) {
  ClassCreator object_creator(type::java_lang_Object());
  object_creator.set_access(ACC_PUBLIC);
  auto* object = object_creator.create();
  std::vector<DexClass*> classes{object};
  for (const auto& [name, access] :
       std::vector<std::pair<const char*, DexAccessFlags>>{
           {"Lcom/a/Public;", ACC_PUBLIC}, {"Lcom/a/Hidden;", ACC_FINAL}}) {
    ClassCreator creator(DexType::make_type(name));
    creator.set_super(type::java_lang_Object());
    creator.set_access(access);
    classes.push_back(creator.create());
  }
  DexStore store("classes");
  store.add_classes(classes);
  DexStoresVector stores({store});
  XStoreRefs xstores(stores, /* normal_primary_dex */ false);
  RefChecker checker(&xstores, 0, /* min_sdk_api */ nullptr);

  EXPECT_TRUE(checker.check_type_from_package(
      DexType::get_type("Lcom/a/Public;"), "Lcom/b/"));
  EXPECT_TRUE(checker.check_type_from_package(
      DexType::make_type("[Lcom/a/Hidden;"), "Lcom/a/"));
  EXPECT_FALSE(checker.check_type_from_package(
      DexType::get_type("Lcom/a/Hidden;"), "Lcom/b/"));
  EXPECT_TRUE(checker.check_type_from_package(type::_int(), "Lcom/b/"));
  EXPECT_FALSE(checker.check_type_from_package(
      DexType::make_type("Lcom/a/Unknown;"), "Lcom/a/"));
}

// A method handle constant references the method or field it names.
TEST_F(RefCheckerTest, methodHandleConstantReferencesItsMember) {
  auto make_handle_user = [] {
    return make_method(R"(
      (
        (load-param-object v0)
        (const-method-handle invoke-static "LTarget;.run:()V")
        (move-result-pseudo-object v1)
        (return-void)
      )
    )");
  };
  // Without a definition of the method, the reference cannot be checked.
  EXPECT_TRUE(code_refs(make_handle_user()).invalid_refs);

  auto* target = define_in_own_class("LTarget;.run:()V");
  auto refs = code_refs(make_handle_user());
  EXPECT_FALSE(refs.invalid_refs);
  EXPECT_EQ(refs.methods, std::vector<const DexMethod*>{target});
  EXPECT_TRUE(contains(refs.types, "LTarget;"));
}

// A static-get handle of `LChild;.x` gets the static `LBase;.x`, as ART
// resolves it, not the instance field of that name that `LChild;` declares.
TEST_F(RefCheckerTest, fieldHandleReferencesFieldOfItsKind) {
  ClassCreator base(DexType::make_type("LBase;"));
  base.set_super(type::java_lang_Object());
  auto* base_x = DexField::make_field("LBase;.x:I")
                     ->make_concrete(ACC_PUBLIC | ACC_STATIC);
  base.add_field(base_x);
  base.create();
  ClassCreator child(DexType::make_type("LChild;"));
  child.set_super(DexType::get_type("LBase;"));
  child.add_field(
      DexField::make_field("LChild;.x:I")->make_concrete(ACC_PUBLIC));
  child.create();
  auto refs = code_refs(make_method(R"(
    (
      (load-param-object v0)
      (const-method-handle static-get "LChild;.x:I")
      (move-result-pseudo-object v1)
      (return-void)
    )
  )"));
  EXPECT_FALSE(refs.invalid_refs);
  EXPECT_EQ(refs.fields, std::vector<const DexField*>{base_x});
}

// A call site references its bootstrap method and the types of its method
// type.
TEST_F(RefCheckerTest, callSiteReferencesItsBootstrapMethodAndTypes) {
  auto make_custom = [] {
    // The `invoke-static` becomes an `invoke-custom`.
    auto* method = make_method(R"(
      (
        (load-param-object v0)
        (invoke-static () "LFoo;.placeholder:()V")
        (return-void)
      )
    )");
    redex::make_invoke_custom(method->get_code(), "run",
                              "()Ljava/lang/Runnable;");
    return method;
  };
  // Without a definition of the bootstrap method, the reference cannot be
  // checked.
  EXPECT_TRUE(code_refs(make_custom()).invalid_refs);

  auto* bootstrap = define_in_own_class(
      "LBoot;.bootstrap:(Ljava/lang/invoke/MethodHandles$Lookup;"
      "Ljava/lang/String;Ljava/lang/invoke/MethodType;)"
      "Ljava/lang/invoke/CallSite;");
  auto refs = code_refs(make_custom());
  EXPECT_FALSE(refs.invalid_refs);
  EXPECT_EQ(refs.methods, std::vector<const DexMethod*>{bootstrap});
  EXPECT_TRUE(contains(refs.types, "Ljava/lang/Runnable;"));
}

// A method handle call references the signature-polymorphic method it names
// and the types of its call-site prototype.
TEST_F(RefCheckerTest, methodHandleCallReferencesItsMethodAndTypes) {
  const auto* invoke_exact =
      "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/"
      "lang/Object;";
  auto make_call = [] {
    return make_method(R"(
      (
        (load-param-object v0)
        (invoke-polymorphic (v0) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "(LBar;)LBaz;")
        (return-void)
      )
    )");
  };
  // Without a definition of the method, the reference cannot be checked.
  EXPECT_TRUE(code_refs(make_call()).invalid_refs);

  ClassCreator creator(DexType::make_type("Ljava/lang/invoke/MethodHandle;"));
  creator.set_super(type::java_lang_Object());
  creator.set_access(ACC_PUBLIC | ACC_ABSTRACT);
  creator.set_external();
  auto* definition = DexMethod::make_method(invoke_exact)
                         ->make_concrete(ACC_PUBLIC | ACC_NATIVE | ACC_VARARGS,
                                         /* is_virtual */ true);
  creator.add_method(definition);
  creator.create();

  auto refs = code_refs(make_call());
  EXPECT_FALSE(refs.invalid_refs);
  EXPECT_EQ(refs.methods, std::vector<const DexMethod*>{definition});
  EXPECT_TRUE(contains(refs.types, "LBar;"));
  EXPECT_TRUE(contains(refs.types, "LBaz;"));
}

// A method type constant references the types of its prototype.
TEST_F(RefCheckerTest, methodTypeConstantReferencesItsTypes) {
  auto* constant = make_method(R"(
    (
      (load-param-object v0)
      (const-method-type "(LBar;)LBaz;")
      (move-result-pseudo-object v1)
      (return-void)
    )
  )");
  auto refs = code_refs(constant);
  EXPECT_FALSE(refs.invalid_refs);
  EXPECT_TRUE(contains(refs.types, "LBar;"));
  EXPECT_TRUE(contains(refs.types, "LBaz;"));
}

namespace {

DexClass* make_class(const char* name,
                     const DexType* super,
                     DexAccessFlags access = ACC_PUBLIC,
                     const std::vector<DexType*>& interfaces = {}) {
  ClassCreator creator(DexType::make_type(name));
  creator.set_super(const_cast<DexType*>(super));
  creator.set_access(access);
  for (auto* interface : interfaces) {
    creator.add_interface(interface);
  }
  return creator.create();
}

DexMethod* add_virtual(DexClass* cls,
                       const std::string& name,
                       DexAccessFlags access = ACC_PUBLIC) {
  auto* method =
      DexMethod::make_method(show(cls->get_type()) + "." + name + ":()V")
          ->make_concrete(access, /* is_virtual */ true);
  cls->add_method(method);
  return method;
}

} // namespace

// A method handle references the method that calling it runs, found like the
// invoke the handle acts like: an invoke-interface handle finds a method of a
// superinterface.
TEST_F(RefCheckerTest, interfaceMethodHandleReferencesInheritedMethod) {
  auto* j = make_class("LJ;", type::java_lang_Object(),
                       ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  auto* m = add_virtual(j, "m", ACC_PUBLIC | ACC_ABSTRACT);
  make_class("LI;", type::java_lang_Object(),
             ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT, {j->get_type()});

  auto refs = code_refs(make_method(R"(
    (
      (load-param-object v0)
      (const-method-handle invoke-interface "LI;.m:()V")
      (move-result-pseudo-object v1)
      (return-void)
    )
  )"));

  EXPECT_FALSE(refs.invalid_refs);
  EXPECT_EQ(refs.methods, std::vector<const DexMethod*>{m});
}

// Resolving an invoke-interface handle of a class method fails in ART with
// IncompatibleClassChangeError, so the handle references no method.
TEST_F(RefCheckerTest, interfaceMethodHandleOfClassMethodIsInvalid) {
  auto* c = make_class("LC;", type::java_lang_Object());
  add_virtual(c, "m");

  auto refs = code_refs(make_method(R"(
    (
      (const-method-handle invoke-interface "LC;.m:()V")
      (move-result-pseudo-object v0)
      (return-void)
    )
  )"));

  EXPECT_TRUE(refs.invalid_refs);
}

// An invoke-direct handle of a method that is not private runs the holder's
// implementation without virtual dispatch when the named class inherits it, so
// it references that implementation.
TEST_F(RefCheckerTest, directMethodHandleReferencesInheritedImplementation) {
  auto* a = make_class("LA;", type::java_lang_Object());
  auto* a_m = add_virtual(a, "m");
  auto* b = make_class("LB;", a->get_type());
  auto* c = make_class("LC;", b->get_type());
  auto* holder = assembler::method_from_string(R"(
    (method (public static) "LC;.run:()V"
      (
        (const-method-handle invoke-direct "LB;.m:()V")
        (move-result-pseudo-object v0)
        (return-void)
      )
    )
  )");
  c->add_method(holder);

  auto refs = code_refs(holder);

  EXPECT_FALSE(refs.invalid_refs);
  EXPECT_EQ(refs.methods, std::vector<const DexMethod*>{a_m});
}

// When `LB;` overrides `LA;.m`, ART versions disagree on what an invoke-direct
// handle of `LA;.m` held by `LC;` runs (see `resolve_method_handle`), so the
// handle references no known method.
TEST_F(RefCheckerTest, directMethodHandleOfOverriddenMethodIsInvalid) {
  auto* a = make_class("LA;", type::java_lang_Object());
  add_virtual(a, "m");
  auto* b = make_class("LB;", a->get_type());
  add_virtual(b, "m");
  auto* c = make_class("LC;", b->get_type());
  auto* holder = assembler::method_from_string(R"(
    (method (public static) "LC;.run:()V"
      (
        (const-method-handle invoke-direct "LA;.m:()V")
        (move-result-pseudo-object v0)
        (return-void)
      )
    )
  )");
  c->add_method(holder);

  auto refs = code_refs(holder);

  EXPECT_TRUE(refs.invalid_refs);
}
