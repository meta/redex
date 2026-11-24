/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ClassChecker.h"
#include "Debug.h"
#include "DexClass.h"
#include "RedexTest.h"
#include "ScopeHelper.h"
#include "TypeUtil.h"

class ClassVCheckerTest : public RedexTest {};

TEST_F(ClassVCheckerTest, testNonAbstractClassWithAbstractMethods) {
  Scope scope = create_empty_scope();
  auto* void_t = type::_void();
  auto* void_void =
      DexProto::make_proto(void_t, DexTypeList::make_type_list({}));

  DexType* a_type = DexType::make_type("LA;");
  DexClass* a_cls =
      create_internal_class(a_type, type::java_lang_Object(), {}, ACC_PUBLIC);
  create_abstract_method(a_cls, "m", void_void);

  scope.push_back(a_cls);

  ClassChecker checker;
  checker.run(scope);
  EXPECT_TRUE(checker.fail());
}

TEST_F(ClassVCheckerTest, testNonAbstractClassWithNonAbstractMethods) {
  Scope scope = create_empty_scope();
  auto* void_t = type::_void();
  auto* void_void =
      DexProto::make_proto(void_t, DexTypeList::make_type_list({}));

  DexType* a_type = DexType::make_type("LA;");
  DexClass* a_cls =
      create_internal_class(a_type, type::java_lang_Object(), {}, ACC_PUBLIC);
  create_empty_method(a_cls, "m", void_void, ACC_PUBLIC);

  scope.push_back(a_cls);

  ClassChecker checker;
  checker.run(scope);
  EXPECT_FALSE(checker.fail());
}

TEST_F(ClassVCheckerTest, testAbstractClassWithAbstractMethods) {
  Scope scope = create_empty_scope();
  auto* void_t = type::_void();
  auto* void_void =
      DexProto::make_proto(void_t, DexTypeList::make_type_list({}));

  DexType* a_type = DexType::make_type("LA;");
  DexClass* a_cls = create_internal_class(a_type, type::java_lang_Object(), {},
                                          ACC_PUBLIC | ACC_ABSTRACT);
  create_abstract_method(a_cls, "m", void_void);

  scope.push_back(a_cls);

  ClassChecker checker;
  checker.run(scope);
  EXPECT_FALSE(checker.fail());
}

TEST_F(ClassVCheckerTest, testInterfaceClassWithAbstractMethods) {
  Scope scope = create_empty_scope();
  auto* void_t = type::_void();
  auto* void_void =
      DexProto::make_proto(void_t, DexTypeList::make_type_list({}));

  DexType* a_type = DexType::make_type("LA;");
  DexClass* a_cls = create_internal_class(a_type, type::java_lang_Object(), {},
                                          ACC_INTERFACE);
  create_abstract_method(a_cls, "m", void_void);

  scope.push_back(a_cls);

  ClassChecker checker;
  checker.run(scope);
  EXPECT_FALSE(checker.fail());
}

TEST_F(ClassVCheckerTest, testAbstractClassWithNonAbstractMethods) {
  Scope scope = create_empty_scope();
  auto* void_t = type::_void();
  auto* void_void =
      DexProto::make_proto(void_t, DexTypeList::make_type_list({}));

  DexType* a_type = DexType::make_type("LA;");
  DexClass* a_cls =
      create_internal_class(a_type, type::java_lang_Object(), {}, ACC_ABSTRACT);
  create_empty_method(a_cls, "m", void_void);

  scope.push_back(a_cls);

  ClassChecker checker;
  checker.run(scope);
  EXPECT_FALSE(checker.fail());
}

TEST_F(ClassVCheckerTest, testInterfaceClassWithNonAbstractMethods) {
  Scope scope = create_empty_scope();
  auto* void_t = type::_void();
  auto* void_void =
      DexProto::make_proto(void_t, DexTypeList::make_type_list({}));

  DexType* a_type = DexType::make_type("LA;");
  DexClass* a_cls = create_internal_class(a_type, type::java_lang_Object(), {},
                                          ACC_INTERFACE);
  create_empty_method(a_cls, "m", void_void);

  scope.push_back(a_cls);

  ClassChecker checker;
  checker.run(scope);
  EXPECT_FALSE(checker.fail());
}

namespace {
// Make a super class A with a method called foo, of given proto and access, and
// a subclass B also with a method called foo of given proto and access.
Scope make_scope_with_a_foo_b_foo(const std::string& a_package,
                                  DexProto* a_foo_proto,
                                  DexAccessFlags a_foo_access,
                                  const std::string& b_package,
                                  DexProto* b_foo_proto,
                                  DexAccessFlags b_foo_access) {
  Scope scope = create_empty_scope();

  DexType* a_type = DexType::make_type(a_package + "A;");
  DexClass* a_cls =
      create_internal_class(a_type, type::java_lang_Object(), {}, ACC_PUBLIC);

  auto* a_foo = create_empty_method(a_cls, "foo", a_foo_proto, a_foo_access);
  always_assert(a_foo->is_virtual());

  DexType* b_type = DexType::make_type(b_package + "B;");
  DexClass* b_cls = create_internal_class(b_type, a_type, {}, ACC_PUBLIC);
  auto* b_foo = create_empty_method(b_cls, "foo", b_foo_proto, b_foo_access);
  always_assert(b_foo->is_virtual());

  scope.push_back(a_cls);
  scope.push_back(b_cls);
  return scope;
}

Scope make_scope_with_a_foo_b_foo(DexProto* a_foo_proto,
                                  DexAccessFlags a_foo_access,
                                  DexProto* b_foo_proto,
                                  DexAccessFlags b_foo_access) {
  return make_scope_with_a_foo_b_foo("Lredex/", a_foo_proto, a_foo_access,
                                     "Lredex/", b_foo_proto, b_foo_access);
}
} // namespace

TEST_F(ClassVCheckerTest, testFinalMethodNotInSubclassPasses) {
  auto* int_return_void = DexProto::make_proto(
      type::_void(), DexTypeList::make_type_list({type::_int()}));
  auto* int_return_int = DexProto::make_proto(
      type::_int(), DexTypeList::make_type_list({type::_int()}));
  // A and B are in the same package, both defining foo() with different return
  // value. No problem.
  auto scope = make_scope_with_a_foo_b_foo(
      int_return_void, ACC_PUBLIC | ACC_FINAL, int_return_int, ACC_PUBLIC);

  ClassChecker checker;
  checker.run(scope);
  EXPECT_FALSE(checker.fail());
}

TEST_F(ClassVCheckerTest, testFinalMethodInSubclassFails) {
  auto* int_return_void = DexProto::make_proto(
      type::_void(), DexTypeList::make_type_list({type::_int()}));
  // A and B are in the same package, both defining foo() with same proto.
  // A.foo() is final, which should be disallowed.
  auto scope = make_scope_with_a_foo_b_foo(
      int_return_void, ACC_PUBLIC | ACC_FINAL, int_return_void, ACC_PUBLIC);

  ClassChecker checker;
  checker.run(scope);
  EXPECT_TRUE(checker.fail());
  std::cerr << checker.print_failed_classes().str() << "\n";
}

TEST_F(ClassVCheckerTest, testProtectedFinalMethodInSubclassFails) {
  auto* int_return_void = DexProto::make_proto(
      type::_void(), DexTypeList::make_type_list({type::_int()}));
  // Same as above, but A.foo() is protected, still should be disallowed.
  auto scope = make_scope_with_a_foo_b_foo(
      int_return_void, ACC_PROTECTED | ACC_FINAL, int_return_void, ACC_PUBLIC);

  ClassChecker checker;
  checker.run(scope);
  EXPECT_TRUE(checker.fail());
  std::cerr << checker.print_failed_classes().str() << "\n";
}

TEST_F(ClassVCheckerTest, testDefaultAccessFinalMethodInSubclassSamePkgFails) {
  auto* int_return_void = DexProto::make_proto(
      type::_void(), DexTypeList::make_type_list({type::_int()}));
  // Same as above, but A.foo() is default access, still should be disallowed.
  auto scope = make_scope_with_a_foo_b_foo(int_return_void, ACC_FINAL,
                                           int_return_void, ACC_PUBLIC);

  ClassChecker checker;
  checker.run(scope);
  EXPECT_TRUE(checker.fail());
  std::cerr << checker.print_failed_classes().str() << "\n";
}

TEST_F(ClassVCheckerTest, testDefaultAccessFinalMethodInSubclassOtherPkgPass) {
  auto* int_return_void = DexProto::make_proto(
      type::_void(), DexTypeList::make_type_list({type::_int()}));
  // A.foo() is final, package-private, and B.foo() has same signature but in a
  // different package, should be fine.
  auto scope =
      make_scope_with_a_foo_b_foo("Lredex/", int_return_void, ACC_FINAL,
                                  "Lother/", int_return_void, ACC_PUBLIC);

  ClassChecker checker;
  checker.run(scope);
  EXPECT_FALSE(checker.fail());
}

TEST_F(ClassVCheckerTest, testNonFinalOverrideInSubclassPasses) {
  auto* int_return_void = DexProto::make_proto(
      type::_void(), DexTypeList::make_type_list({type::_int()}));
  // A and B are in the same package, both defining foo() with same proto.
  // A.foo() is not final, no problem.
  auto scope = make_scope_with_a_foo_b_foo(int_return_void, ACC_PUBLIC,
                                           int_return_void, ACC_PUBLIC);

  ClassChecker checker;
  checker.run(scope);
  EXPECT_FALSE(checker.fail());
}

// This following example would not compile if written as source code
// (P1203397896) but is represented in a test case for thoroughness.
TEST_F(ClassVCheckerTest, testVeryFunnyBusiness) {
  Scope scope = create_empty_scope();

  auto* int_return_void = DexProto::make_proto(
      type::_void(), DexTypeList::make_type_list({type::_int()}));
  DexAccessFlags def_access{};

  DexType* a_type = DexType::make_type("Lredex/A;");
  DexClass* a_cls =
      create_internal_class(a_type, type::java_lang_Object(), {}, ACC_PUBLIC);

  auto* a_foo = create_empty_method(a_cls, "foo", int_return_void, ACC_FINAL);
  always_assert(a_foo->is_virtual());

  DexType* b_type = DexType::make_type("Lother/B;");
  DexClass* b_cls = create_internal_class(b_type, a_type, {}, ACC_PUBLIC);
  auto* b_foo = create_empty_method(b_cls, "foo", int_return_void, def_access);
  always_assert(b_foo->is_virtual());

  DexType* c_type = DexType::make_type("Lredex/C;");
  DexClass* c_cls = create_internal_class(c_type, b_type, {}, ACC_PUBLIC);
  auto* c_foo = create_empty_method(c_cls, "foo", int_return_void, def_access);
  always_assert(c_foo->is_virtual());

  scope.push_back(a_cls);
  scope.push_back(b_cls);
  scope.push_back(c_cls);

  ClassChecker checker;
  checker.run(scope);
  EXPECT_TRUE(checker.fail());
}

namespace {

DexClass* make_class(const char* name,
                     const char* super,
                     const std::vector<const char*>& interfaces = {},
                     DexAccessFlags access = ACC_PUBLIC,
                     bool external = false) {
  std::vector<DexType*> intfs;
  intfs.reserve(interfaces.size());
  for (const auto* intf : interfaces) {
    intfs.push_back(DexType::make_type(intf));
  }
  return create_class(DexType::make_type(name),
                      super == nullptr ? type::java_lang_Object()
                                       : DexType::make_type(super),
                      intfs, access, external);
}

const DexAccessFlags kInterface = ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT;

std::string hierarchy_errors(const Scope& scope) {
  auto errors = check_class_hierarchy(scope);
  return errors ? *errors : "";
}

} // namespace

// class C implements I {}
// class D extends C {}
TEST_F(ClassVCheckerTest, testClassHierarchyWithKindsAsDefined) {
  Scope scope = create_empty_scope();
  scope.push_back(make_class("LI;", nullptr, {}, kInterface));
  scope.push_back(make_class("LC;", nullptr, {"LI;"}));
  scope.push_back(make_class("LD;", "LC;"));

  EXPECT_EQ(hierarchy_errors(scope), "");
}

// interface I {}  // external
// class C extends I {}
TEST_F(ClassVCheckerTest, testSuperclassDefinedAsInterfaceFails) {
  Scope scope = create_empty_scope();
  make_class("LI;", nullptr, {}, kInterface, /* external */ true);
  scope.push_back(make_class("LC;", "LI;"));

  EXPECT_NE(
      hierarchy_errors(scope).find("Superclass LI; of LC; is an interface"),
      std::string::npos);
}

// abstract class S {}  // external, from a library jar older than the app
// class Lite implements S {}
TEST_F(ClassVCheckerTest, testInterfaceDefinedAsClassFails) {
  Scope scope = create_empty_scope();
  make_class("LS;", nullptr, {}, ACC_PUBLIC | ACC_ABSTRACT,
             /* external */ true);
  scope.push_back(make_class("LLite;", nullptr, {"LS;"}));

  EXPECT_NE(hierarchy_errors(scope).find(
                "Class LLite; implements non-interface class LS;"),
            std::string::npos);
}

// class S {}
// interface J extends S {}
TEST_F(ClassVCheckerTest, testSuperinterfaceDefinedAsClassFails) {
  Scope scope = create_empty_scope();
  scope.push_back(make_class("LS;", nullptr));
  scope.push_back(make_class("LJ;", nullptr, {"LS;"}, kInterface));

  EXPECT_NE(hierarchy_errors(scope).find(
                "Class LJ; implements non-interface class LS;"),
            std::string::npos);
}

// interface J extends I {}, with java.lang.Object as superclass
TEST_F(ClassVCheckerTest, testInterfaceExtendingObjectPasses) {
  Scope scope = create_empty_scope();
  scope.push_back(make_class("LI;", nullptr, {}, kInterface));
  scope.push_back(make_class("LJ;", nullptr, {"LI;"}, kInterface));

  EXPECT_EQ(hierarchy_errors(scope), "");
}

// An interface whose superclass is the class C.
TEST_F(ClassVCheckerTest, testInterfaceWithOtherSuperclassFails) {
  Scope scope = create_empty_scope();
  scope.push_back(make_class("LC;", nullptr));
  scope.push_back(make_class("LI;", "LC;", {}, kInterface));

  EXPECT_NE(hierarchy_errors(scope).find(
                "Interface LI; has superclass LC;, but interfaces must have "
                "java.lang.Object as superclass"),
            std::string::npos);
}

// interface I {}  interface J extends I {}  interface K extends I {}
// class C implements J, K {}  class D extends C implements I {}
TEST_F(ClassVCheckerTest, testDiamondHierarchyPasses) {
  Scope scope = create_empty_scope();
  scope.push_back(make_class("LI;", nullptr, {}, kInterface));
  scope.push_back(make_class("LJ;", nullptr, {"LI;"}, kInterface));
  scope.push_back(make_class("LK;", nullptr, {"LI;"}, kInterface));
  scope.push_back(make_class("LC;", nullptr, {"LJ;", "LK;"}));
  scope.push_back(make_class("LD;", "LC;", {"LI;"}));

  EXPECT_EQ(hierarchy_errors(scope), "");
}

// class A extends B {}  class B extends A {}  class C extends C {}
TEST_F(ClassVCheckerTest, testCyclicSuperclassesFail) {
  Scope scope = create_empty_scope();
  scope.push_back(make_class("LA;", "LB;"));
  scope.push_back(make_class("LB;", "LA;"));
  scope.push_back(make_class("LC;", "LC;"));

  auto errors = hierarchy_errors(scope);
  EXPECT_NE(errors.find("Class LA; is its own supertype: LA; -> LB; -> LA;"),
            std::string::npos);
  EXPECT_NE(errors.find("Class LC; extends itself"), std::string::npos);
}

// interface I extends I {}
TEST_F(ClassVCheckerTest, testInterfaceExtendingItselfFails) {
  Scope scope = create_empty_scope();
  scope.push_back(make_class("LI;", nullptr, {"LI;"}, kInterface));

  EXPECT_NE(hierarchy_errors(scope).find("Class LI; implements itself"),
            std::string::npos);
}

// interface I extends J {}  interface J extends I {}
TEST_F(ClassVCheckerTest, testCyclicSuperinterfacesFail) {
  Scope scope = create_empty_scope();
  scope.push_back(make_class("LI;", nullptr, {"LJ;"}, kInterface));
  scope.push_back(make_class("LJ;", nullptr, {"LI;"}, kInterface));

  EXPECT_NE(hierarchy_errors(scope).find(
                "Class LI; is its own supertype: LI; -> LJ; -> LI;"),
            std::string::npos);
}

// class B {}  class D extends B {}
TEST_F(ClassVCheckerTest, testNonFinalSuperclassPasses) {
  Scope scope = create_empty_scope();
  scope.push_back(make_class("LB;", nullptr));
  scope.push_back(make_class("LD;", "LB;"));

  EXPECT_EQ(hierarchy_errors(scope), "");
}

// final class F {}  // external
// class D extends F {}
TEST_F(ClassVCheckerTest, testFinalSuperclassFails) {
  Scope scope = create_empty_scope();
  make_class("LF;", nullptr, {}, ACC_PUBLIC | ACC_FINAL, /* external */ true);
  scope.push_back(make_class("LD;", "LF;"));

  EXPECT_NE(
      hierarchy_errors(scope).find("Superclass LF; of LD; is declared final"),
      std::string::npos);
}

// Two library classes that do not fit together fail without any class of the
// program referring to them:
// interface I {}  // external
// class E extends I {}  // external
TEST_F(ClassVCheckerTest, testInconsistentExternalClassesFail) {
  Scope scope = create_empty_scope();
  make_class("LI;", nullptr, {}, kInterface, /* external */ true);
  make_class("LE;", "LI;", {}, ACC_PUBLIC, /* external */ true);

  EXPECT_NE(
      hierarchy_errors(scope).find("Superclass LI; of LE; is an interface"),
      std::string::npos);
}

// Types missing from the input can be either kind, final or not:
// class C extends MissingClass implements MissingInterface {}
// interface J extends MissingInterface {}
TEST_F(ClassVCheckerTest, testMissingSupertypesPass) {
  Scope scope = create_empty_scope();
  scope.push_back(make_class("LC;", "LMissingClass;", {"LMissingInterface;"}));
  scope.push_back(
      make_class("LJ;", nullptr, {"LMissingInterface;"}, kInterface));

  EXPECT_EQ(hierarchy_errors(scope), "");
}

// ClassChecker::run reports a hierarchy the runtime cannot link:
// interface I {}  // external
// class C extends I {}
TEST_F(ClassVCheckerTest, testClassCheckerRunFailsOnUnlinkableHierarchy) {
  Scope scope = create_empty_scope();
  make_class("LI;", nullptr, {}, kInterface, /* external */ true);
  scope.push_back(make_class("LC;", "LI;"));

  ClassChecker checker;
  checker.run(scope);
  EXPECT_TRUE(checker.fail());
  EXPECT_NE(checker.print_failed_classes().str().find(
                "Superclass LI; of LC; is an interface"),
            std::string::npos);
}

// The other checks walk the hierarchy, so they do not run on one the runtime
// cannot link, and only the hierarchy error is reported:
// class A { final void foo(int) }  class B extends A { void foo(int) }
// abstract class S {}  // external
// class Lite implements S {}
TEST_F(ClassVCheckerTest,
       testClassCheckerRunSkipsOtherChecksOnUnlinkableHierarchy) {
  auto* int_return_void = DexProto::make_proto(
      type::_void(), DexTypeList::make_type_list({type::_int()}));
  auto scope = make_scope_with_a_foo_b_foo(
      int_return_void, ACC_PUBLIC | ACC_FINAL, int_return_void, ACC_PUBLIC);
  make_class("LS;", nullptr, {}, ACC_PUBLIC | ACC_ABSTRACT,
             /* external */ true);
  scope.push_back(make_class("LLite;", nullptr, {"LS;"}));

  ClassChecker checker;
  checker.run(scope);
  EXPECT_TRUE(checker.fail());
  auto report = checker.print_failed_classes().str();
  EXPECT_NE(report.find("Class LLite; implements non-interface class LS;"),
            std::string::npos);
  EXPECT_EQ(report.find("Methods incorrectly overriding"), std::string::npos);
}

// A type missing from the input stays a legitimate supertype for
// ClassChecker::run, as it is for check_class_hierarchy:
// class C extends MissingClass implements MissingInterface {}
TEST_F(ClassVCheckerTest, testClassCheckerRunAcceptsMissingSupertypes) {
  Scope scope = create_empty_scope();
  scope.push_back(make_class("LC;", "LMissingClass;", {"LMissingInterface;"}));

  ClassChecker checker;
  checker.run(scope);
  EXPECT_FALSE(checker.fail());
}

// ClassChecker::run stops at a cycle instead of walking it:
// class A extends B {}  class B extends A {}
TEST_F(ClassVCheckerTest, testClassCheckerRunFailsOnCycle) {
  Scope scope = create_empty_scope();
  scope.push_back(make_class("LA;", "LB;"));
  scope.push_back(make_class("LB;", "LA;"));

  ClassChecker checker;
  checker.run(scope);
  EXPECT_TRUE(checker.fail());
  EXPECT_NE(checker.print_failed_classes().str().find(
                "Class LA; is its own supertype: LA; -> LB; -> LA;"),
            std::string::npos);
}
