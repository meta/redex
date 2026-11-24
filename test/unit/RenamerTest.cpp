/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <functional>

#include <gtest/gtest.h>

#include "DexAnnotation.h"
#include "DexClass.h"
#include "DexMethodHandle.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "RedexTest.h"
#include "ScopeHelper.h"
#include "Show.h"
#include "Trace.h"
#include "TypeUtil.h"
#include "VirtScopeHelper.h"
#include "VirtualRenamer.h"
#include "Walkers.h"

namespace {

bool has_method(DexType* type, const DexString* name) {
  for (const auto& vmeth : type_class(type)->get_vmethods()) {
    if (vmeth->get_name() == name) {
      return true;
    }
  }
  return false;
}

void check_intf_common() {
  // there is an untouched F.equals()
  EXPECT_TRUE(
      has_method(DexType::get_type("LF;"), DexString::get_string("equals")));
  // C has an override both in D and E
  EXPECT_TRUE(
      type_class(DexType::get_type("LD;"))->get_vmethods()[0]->get_name() ==
          type_class(DexType::get_type("LC;"))->get_vmethods()[0]->get_name() ||
      type_class(DexType::get_type("LD;"))->get_vmethods()[1]->get_name() ==
          type_class(DexType::get_type("LC;"))->get_vmethods()[0]->get_name());
  EXPECT_TRUE(
      type_class(DexType::get_type("LE;"))->get_vmethods()[0]->get_name() ==
          type_class(DexType::get_type("LC;"))->get_vmethods()[0]->get_name() ||
      type_class(DexType::get_type("LE;"))->get_vmethods()[1]->get_name() ==
          type_class(DexType::get_type("LC;"))->get_vmethods()[0]->get_name());
  // the interface method name must be in both B and D
  EXPECT_TRUE(
      type_class(DexType::get_type("LB;"))->get_vmethods()[0]->get_name() ==
          type_class(DexType::get_type("LIntf1;"))
              ->get_vmethods()[0]
              ->get_name() ||
      type_class(DexType::get_type("LB;"))->get_vmethods()[1]->get_name() ==
          type_class(DexType::get_type("LIntf1;"))
              ->get_vmethods()[0]
              ->get_name());
  EXPECT_TRUE(
      type_class(DexType::get_type("LD;"))->get_vmethods()[0]->get_name() ==
          type_class(DexType::get_type("LIntf1;"))
              ->get_vmethods()[0]
              ->get_name() ||
      type_class(DexType::get_type("LB;"))->get_vmethods()[1]->get_name() ==
          type_class(DexType::get_type("LIntf1;"))
              ->get_vmethods()[0]
              ->get_name());
  // Intf2 method name must be in I, C, D, E
  EXPECT_TRUE(
      type_class(DexType::get_type("LI;"))->get_vmethods()[0]->get_name() ==
      type_class(DexType::get_type("LIntf2;"))->get_vmethods()[0]->get_name());
  EXPECT_TRUE(
      type_class(DexType::get_type("LC;"))->get_vmethods()[0]->get_name() ==
      type_class(DexType::get_type("LIntf2;"))->get_vmethods()[0]->get_name());
  EXPECT_TRUE(
      type_class(DexType::get_type("LD;"))->get_vmethods()[0]->get_name() ==
          type_class(DexType::get_type("LIntf2;"))
              ->get_vmethods()[0]
              ->get_name() ||
      type_class(DexType::get_type("LD;"))->get_vmethods()[1]->get_name() ==
          type_class(DexType::get_type("LIntf2;"))
              ->get_vmethods()[0]
              ->get_name());
  EXPECT_TRUE(
      type_class(DexType::get_type("LE;"))->get_vmethods()[0]->get_name() ==
          type_class(DexType::get_type("LIntf2;"))
              ->get_vmethods()[0]
              ->get_name() ||
      type_class(DexType::get_type("LE;"))->get_vmethods()[1]->get_name() ==
          type_class(DexType::get_type("LIntf2;"))
              ->get_vmethods()[0]
              ->get_name());
}

void print_scope(Scope& scope) {
  TRACE(OBFUSCATE, 2, "------------------------------------------------");
  for (const auto& cls : scope) {
    TRACE_NO_LINE(OBFUSCATE, 2, "** %s extends %s", SHOW(cls),
                  SHOW(cls->get_super_class()));
    if (!cls->get_interfaces()->empty()) {
      TRACE_NO_LINE(OBFUSCATE, 2, " implements ");
      for (const auto& intf : *cls->get_interfaces()) {
        TRACE_NO_LINE(OBFUSCATE, 2, "%s, ", SHOW(intf));
      }
    }
    TRACE(OBFUSCATE, 2, "");
    for (const auto& field : cls->get_sfields()) {
      TRACE(OBFUSCATE, 2, "\t%s", SHOW(field));
    }
    for (const auto& meth : cls->get_dmethods()) {
      TRACE(OBFUSCATE, 2, "\t%s", SHOW(meth));
    }
    for (const auto& field : cls->get_ifields()) {
      TRACE(OBFUSCATE, 2, "\t%s", SHOW(field));
    }
    for (const auto& meth : cls->get_vmethods()) {
      TRACE(OBFUSCATE, 2, "\t%s", SHOW(meth));
    }
  }
  TRACE(OBFUSCATE, 2, "------------------------------------------------");
}

} // namespace

//
// Tests
//

/**
 * Simple class hierarchy
 *
 * class java.lang.Object { // Object methods ... }
 * class A { void f() {} }
 * class B { void g() {} }
 */

class RenamerTest : public RedexTest {};

TEST_F(RenamerTest, NoOverload) {
  std::vector<DexClass*> scope = create_scope_1();

  print_scope(scope);
  EXPECT_EQ(2, rename_virtuals(scope));
  walk::methods(scope, [&](DexMethod* meth) {
    ASSERT_NE(meth->get_name(), DexString::make_string("f"));
    ASSERT_NE(meth->get_name(), DexString::make_string("g"));
  });
  // A.f() and B.g() should be mapped to the same name
  EXPECT_EQ(
      type_class(DexType::get_type("LA;"))->get_vmethods()[0]->get_name(),
      type_class(DexType::get_type("LB;"))->get_vmethods()[0]->get_name());
  print_scope(scope);
}

/**
 * Simple class hierarchy with override
 *
 * class java.lang.Object { // Object methods ... }
 * class A { void f() {} }
 * class B { void g() {} void f() {} }
 *   class C extends B { }
 *     class D extends C { void f() {} }
 *     class E extends C { void g() {} }
 */
TEST_F(RenamerTest, Override) {
  std::vector<DexClass*> scope = create_scope_2();

  print_scope(scope);
  EXPECT_EQ(5, rename_virtuals(scope));
  walk::methods(scope, [&](DexMethod* meth) {
    ASSERT_NE(meth->get_name(), DexString::make_string("f"));
    ASSERT_NE(meth->get_name(), DexString::make_string("g"));
  });
  // B.f() and D.f() are renamed
  EXPECT_TRUE(
      type_class(DexType::get_type("LD;"))->get_vmethods()[0]->get_name() ==
          type_class(DexType::get_type("LB;"))->get_vmethods()[0]->get_name() ||
      type_class(DexType::get_type("LD;"))->get_vmethods()[0]->get_name() ==
          type_class(DexType::get_type("LB;"))->get_vmethods()[1]->get_name());
  // B.g() and E.g() are renamed
  EXPECT_TRUE(
      type_class(DexType::get_type("LE;"))->get_vmethods()[0]->get_name() ==
          type_class(DexType::get_type("LB;"))->get_vmethods()[0]->get_name() ||
      type_class(DexType::get_type("LE;"))->get_vmethods()[0]->get_name() ==
          type_class(DexType::get_type("LB;"))->get_vmethods()[1]->get_name());
  print_scope(scope);
}

/**
 * Simple class hierarchy with override and overload
 *
 * class java.lang.Object { // Object methods ... }
 * class A { void f() {} }
 *   class F extends A { void f(int) {} boolean equals(Object) {} }
 * class B { void g() {} void f() {} }
 *   class C extends B { void g(int) {} }
 *     class D extends C { void f() {} void g(int) {} }
 *     class E extends C { void g() {} void g(int) {}}
 */
TEST_F(RenamerTest, OverrideOverload) {
  std::vector<DexClass*> scope = create_scope_3();

  print_scope(scope);
  EXPECT_EQ(9, rename_virtuals(scope));
  walk::methods(scope, [&](DexMethod* meth) {
    ASSERT_NE(meth->get_name(), DexString::make_string("f"));
    ASSERT_NE(meth->get_name(), DexString::make_string("g"));
  });
  // there is an untouched F.equals()
  EXPECT_TRUE(
      type_class(DexType::get_type("LF;"))->get_vmethods()[0]->get_name() ==
          DexString::get_string("equals") ||
      type_class(DexType::get_type("LF;"))->get_vmethods()[1]->get_name() ==
          DexString::get_string("equals"));
  // F and A methods have different names
  EXPECT_TRUE(
      type_class(DexType::get_type("LF;"))->get_vmethods()[0]->get_name() !=
          type_class(DexType::get_type("LA;"))->get_vmethods()[0]->get_name() &&
      type_class(DexType::get_type("LF;"))->get_vmethods()[1]->get_name() !=
          type_class(DexType::get_type("LA;"))->get_vmethods()[0]->get_name());
  // C has an override both in D and E
  EXPECT_TRUE(
      type_class(DexType::get_type("LD;"))->get_vmethods()[0]->get_name() ==
          type_class(DexType::get_type("LC;"))->get_vmethods()[0]->get_name() ||
      type_class(DexType::get_type("LD;"))->get_vmethods()[1]->get_name() ==
          type_class(DexType::get_type("LC;"))->get_vmethods()[0]->get_name());
  EXPECT_TRUE(
      type_class(DexType::get_type("LE;"))->get_vmethods()[0]->get_name() ==
          type_class(DexType::get_type("LC;"))->get_vmethods()[0]->get_name() ||
      type_class(DexType::get_type("LE;"))->get_vmethods()[1]->get_name() ==
          type_class(DexType::get_type("LC;"))->get_vmethods()[0]->get_name());
  // B and C have all names different
  EXPECT_TRUE(
      type_class(DexType::get_type("LB;"))->get_vmethods()[0]->get_name() !=
          type_class(DexType::get_type("LC;"))->get_vmethods()[0]->get_name() &&
      type_class(DexType::get_type("LB;"))->get_vmethods()[1]->get_name() !=
          type_class(DexType::get_type("LC;"))->get_vmethods()[0]->get_name());
  print_scope(scope);
}

/**
 * Add interface to previous
 *
 * interface Intf1 { void f(); }
 * class java.lang.Object { // Object methods ... }
 * class A { void f() {} }
 *   class F extends A { void f(int) {} boolean equals(Object) {} }
 * class B implements Intf1 { void g() {} void f() {} }
 *   class C extends B { void g(int) {} }
 *     class D extends C { void f() {} void g(int) {} }
 *     class E extends C { void g() {} void g(int) {}}
 */
TEST_F(RenamerTest, Interface) {
  std::vector<DexClass*> scope = create_scope_4();

  print_scope(scope);
  EXPECT_EQ(10, rename_virtuals(scope));
  walk::methods(scope, [&](DexMethod* meth) {
    ASSERT_NE(meth->get_name(), DexString::make_string("f"));
    ASSERT_NE(meth->get_name(), DexString::make_string("g"));
  });
  // there is an untouched F.equals()
  EXPECT_TRUE(
      has_method(DexType::get_type("LF;"), DexString::get_string("equals")));
  // F and A methods have different names
  EXPECT_TRUE(
      type_class(DexType::get_type("LF;"))->get_vmethods()[0]->get_name() !=
          type_class(DexType::get_type("LA;"))->get_vmethods()[0]->get_name() &&
      type_class(DexType::get_type("LF;"))->get_vmethods()[1]->get_name() !=
          type_class(DexType::get_type("LA;"))->get_vmethods()[0]->get_name());
  // C has an override both in D and E
  EXPECT_TRUE(
      type_class(DexType::get_type("LD;"))->get_vmethods()[0]->get_name() ==
          type_class(DexType::get_type("LC;"))->get_vmethods()[0]->get_name() ||
      type_class(DexType::get_type("LD;"))->get_vmethods()[1]->get_name() ==
          type_class(DexType::get_type("LC;"))->get_vmethods()[0]->get_name());
  EXPECT_TRUE(
      type_class(DexType::get_type("LE;"))->get_vmethods()[0]->get_name() ==
          type_class(DexType::get_type("LC;"))->get_vmethods()[0]->get_name() ||
      type_class(DexType::get_type("LE;"))->get_vmethods()[1]->get_name() ==
          type_class(DexType::get_type("LC;"))->get_vmethods()[0]->get_name());
  // B and C have all names different
  EXPECT_TRUE(
      type_class(DexType::get_type("LB;"))->get_vmethods()[0]->get_name() !=
          type_class(DexType::get_type("LC;"))->get_vmethods()[0]->get_name() &&
      type_class(DexType::get_type("LB;"))->get_vmethods()[1]->get_name() !=
          type_class(DexType::get_type("LC;"))->get_vmethods()[0]->get_name());
  // the interface method name must be in both B and D
  EXPECT_TRUE(
      type_class(DexType::get_type("LB;"))->get_vmethods()[0]->get_name() ==
          type_class(DexType::get_type("LIntf1;"))
              ->get_vmethods()[0]
              ->get_name() ||
      type_class(DexType::get_type("LB;"))->get_vmethods()[1]->get_name() ==
          type_class(DexType::get_type("LIntf1;"))
              ->get_vmethods()[0]
              ->get_name());
  EXPECT_TRUE(
      type_class(DexType::get_type("LD;"))->get_vmethods()[0]->get_name() ==
          type_class(DexType::get_type("LIntf1;"))
              ->get_vmethods()[0]
              ->get_name() ||
      type_class(DexType::get_type("LB;"))->get_vmethods()[1]->get_name() ==
          type_class(DexType::get_type("LIntf1;"))
              ->get_vmethods()[0]
              ->get_name());

  print_scope(scope);
}

/**
 * Multiple interfaces. Add the G hierarchy
 *
 * interface Intf1 { void f(); }
 * interface Intf2 { void g(int); }
 * class java.lang.Object { // Object methods ... }
 * class A { void f() {} }
 *   class F extends A { void f(int) {} boolean equals(Object) {} }
 *     class G extends F { void g(int) {} }
 *       class H extends G implements Intf2 { void g(int) {} }
 *         class I extends H { void g(int) {} }
 *         class J extends H {}
 *       class K extends G { void g(int) {} }
 *     class L extends F { void g(int) {} }
 * class B implements Intf1 { void g() {} void f() {} }
 *   class C extends B implements Intf2 { void g(int) {} }
 *     class D extends C { void f() {} void g(int) {} }
 *     class E extends C { void g() {} void g(int) {} }
 */
TEST_F(RenamerTest, Interface1) {
  std::vector<DexClass*> scope = create_scope_5();

  print_scope(scope);
  EXPECT_EQ(16, rename_virtuals(scope));
  walk::methods(scope, [&](DexMethod* meth) {
    ASSERT_NE(meth->get_name(), DexString::make_string("f"));
    ASSERT_NE(meth->get_name(), DexString::make_string("g"));
  });
  check_intf_common();
  // Intf2 method name must also be in H
  EXPECT_TRUE(
      type_class(DexType::get_type("LH;"))->get_vmethods()[0]->get_name() ==
      type_class(DexType::get_type("LIntf2;"))->get_vmethods()[0]->get_name());
  print_scope(scope);
}

/**
 * Multiple interfaces. Interface implemented twice on a branch
 *
 * interface Intf1 { void f(); }
 * interface Intf2 { void g(int); }
 * class java.lang.Object { // Object methods ... }
 * class A { void f() {} }
 *   class F extends A { void f(int) {} boolean equals(Object) {} }
 *   class G extends F { void g(int) {} }
 *     class H extends G implements Intf2 { void g(int) {} }
 *       class I extends H { void g(int) {} }
 *       class J extends H {}
 *     class K extends G { void g(int) {} }
 *   class L extends F { void g(int) {} }
 * class B implements Intf1 { void g() {} void f() {} }
 *   class C extends B implements Intf2 { void g(int) {} }
 *     class D extends C implements Intf2 { void f() {} void g(int) {} }
 *     class E extends C { void g() {} void g(int) {}}
 */
TEST_F(RenamerTest, Interface2) {
  std::vector<DexClass*> scope = create_scope_6();

  print_scope(scope);
  EXPECT_EQ(16, rename_virtuals(scope));
  walk::methods(scope, [&](DexMethod* meth) {
    ASSERT_NE(meth->get_name(), DexString::make_string("f"));
    ASSERT_NE(meth->get_name(), DexString::make_string("g"));
  });
  check_intf_common();
  // Intf2 method name must also be in H
  EXPECT_TRUE(
      type_class(DexType::get_type("LH;"))->get_vmethods()[0]->get_name() ==
      type_class(DexType::get_type("LIntf2;"))->get_vmethods()[0]->get_name());
  print_scope(scope);
}

/**
 * Multiple interfaces. Interface implemented twice on a branch and
 * with a parent not implemeting the interface
 *
 * interface Intf1 { void f(); }
 * interface Intf2 { void g(int); }
 * class java.lang.Object { // Object methods ... }
 * class A { void f() {} }
 *   class F extends A { void f(int) {} boolean equals(Object) {} void g(int); }
 *     class G extends F { void g(int) {} }
 *       class H extends G implements Intf2 { void g(int) {} }
 *         class I extends H { void g(int) {} }
 *         class J extends H {}
 *       class K extends G { void g(int) {} }
 *     class L extends F { void g(int) {} }
 * class B implements Intf1 { void g() {} void f() {} }
 *   class C extends B implements Intf2 { void g(int) {} }
 *     class D extends C implements Intf2 { void f() {} void g(int) {} }
 *     class E extends C { void g() {} void g(int) {}}
 */
TEST_F(RenamerTest, Interface3) {
  std::vector<DexClass*> scope = create_scope_7();

  print_scope(scope);
  EXPECT_EQ(17, rename_virtuals(scope));
  walk::methods(scope, [&](DexMethod* meth) {
    ASSERT_NE(meth->get_name(), DexString::make_string("f"));
    ASSERT_NE(meth->get_name(), DexString::make_string("g"));
  });
  check_intf_common();
  // Intf2 method name must also be in H and F
  const auto* name =
      type_class(DexType::get_type("LIntf2;"))->get_vmethods()[0]->get_name();
  EXPECT_TRUE(has_method(DexType::get_type("LF;"), name));
  EXPECT_TRUE(has_method(DexType::get_type("LH;"), name));
  print_scope(scope);
}

/**
 * Multiple interfaces. Interface implemented twice on a branch and
 * one implementation missing (needs pure miranda)
 *
 * interface Intf1 { void f(); }
 * interface Intf2 { void g(int); }
 * class java.lang.Object { // Object methods ... }
 * class A { void f() {} }
 *   class F extends A { void f(int) {} boolean equals(Object) {} void g(int); }
 *   class G extends F { void g(int) {} }
 *     class H extends G implements Intf2 { }
 *       class I extends H { void g(int) {} }
 *       class J extends H {}
 *     class K extends G { void g(int) {} }
 *   class L extends F { void g(int) {} }
 * class B implements Intf1 { void g() {} void f() {} }
 *   class C extends B implements Intf2 { void g(int) {} }
 *     class D extends C implements Intf2 { void f() {} void g(int) {} }
 *     class E extends C { void g() {} void g(int) {}}
 */
TEST_F(RenamerTest, Interface3Miranda) {
  std::vector<DexClass*> scope = create_scope_8();

  print_scope(scope);
  EXPECT_EQ(16, rename_virtuals(scope));
  walk::methods(scope, [&](DexMethod* meth) {
    ASSERT_NE(meth->get_name(), DexString::make_string("f"));
    ASSERT_NE(meth->get_name(), DexString::make_string("g"));
  });
  check_intf_common();
  // Intf2 method name must also be in F, G, I, K
  const auto* name =
      type_class(DexType::get_type("LIntf2;"))->get_vmethods()[0]->get_name();
  EXPECT_TRUE(has_method(DexType::get_type("LF;"), name));
  EXPECT_TRUE(has_method(DexType::get_type("LG;"), name));
  EXPECT_TRUE(has_method(DexType::get_type("LI;"), name));
  EXPECT_TRUE(has_method(DexType::get_type("LK;"), name));
  print_scope(scope);
}

/**
 * Multiple interfaces with the same sig.
 *
 * interface Intf1 { void f(); }
 * interface Intf2 { void g(int); }
 * interface Intf3 { void f()); }
 * class java.lang.Object { // Object methods ... }
 * class A { void f() {} }
 *   class F extends A { void f(int) {} boolean equals(Object) {} void g(int); }
 *   class G extends F { void g(int) {} }
 *     class H extends G implements Intf2 { }
 *       class I extends H { void g(int) {} }
 *       class J extends H {}
 *     class K extends G { void g(int) {} }
 *   class L extends F { void g(int) {} }
 * class B implements Intf1 { void g() {} void f() {} }
 *   class C extends B implements Intf2 { void g(int) {} }
 *     class D extends C implements Intf2, Intf3 { void f() {} void g(int) {} }
 *     class E extends C { void g() {} void g(int) {} }
 */
TEST_F(RenamerTest, Interface3MirandaMultiIntf) {
  std::vector<DexClass*> scope = create_scope_9();

  print_scope(scope);
  EXPECT_EQ(17, rename_virtuals(scope));
  walk::methods(scope, [&](DexMethod* meth) {
    ASSERT_NE(meth->get_name(), DexString::make_string("f"));
    ASSERT_NE(meth->get_name(), DexString::make_string("g"));
  });
  check_intf_common();
  // Intf2 method name must also be in F, G, I, K
  const auto* name =
      type_class(DexType::get_type("LIntf2;"))->get_vmethods()[0]->get_name();
  EXPECT_TRUE(has_method(DexType::get_type("LF;"), name));
  EXPECT_TRUE(has_method(DexType::get_type("LG;"), name));
  EXPECT_TRUE(has_method(DexType::get_type("LI;"), name));
  EXPECT_TRUE(has_method(DexType::get_type("LK;"), name));
  // Intf1 and Intf3 have the same method name
  EXPECT_TRUE(
      type_class(DexType::get_type("LIntf1;"))->get_vmethods()[0]->get_name() ==
      type_class(DexType::get_type("LIntf3;"))->get_vmethods()[0]->get_name());
  print_scope(scope);
}

/**
 * Interfaces inheritance.
 *
 * interface Intf1 implements Intf2 { void f(); }
 * interface Intf2 { void g(int); }
 * interface Intf3 implements Intf4 { void f()); }
 * interface Intf4 { void f()); }
 * class java.lang.Object { // Object methods ... }
 * class A { void f() {} }
 *   class F extends A { void f(int) {} boolean equals(Object) {} void g(int); }
 *   class G extends F { void g(int) {} }
 *     class H extends G implements Intf2 { }
 *       class I extends H { void g(int) {} }
 *       class J extends H {}
 *     class K extends G { void g(int) {} }
 *   class L extends F { void g(int) {} }
 * class B implements Intf1 { void g() {} void f() {} }
 *   class C extends B implements Intf2 { void g(int) {} }
 *     class D extends C implements Intf2, Intf3 { void f() {} void g(int) {} }
 *     class E extends C { void g() {} void g(int) {} }
 */
TEST_F(RenamerTest, Interface3IntfOverride) {
  std::vector<DexClass*> scope = create_scope_10();

  print_scope(scope);
  EXPECT_EQ(18, rename_virtuals(scope));
  walk::methods(scope, [&](DexMethod* meth) {
    ASSERT_NE(meth->get_name(), DexString::make_string("f"));
    ASSERT_NE(meth->get_name(), DexString::make_string("g"));
  });
  check_intf_common();
  // Intf2 method name must also be in F, G, I, K
  const auto* name =
      type_class(DexType::get_type("LIntf2;"))->get_vmethods()[0]->get_name();
  EXPECT_TRUE(has_method(DexType::get_type("LF;"), name));
  EXPECT_TRUE(has_method(DexType::get_type("LG;"), name));
  EXPECT_TRUE(has_method(DexType::get_type("LI;"), name));
  EXPECT_TRUE(has_method(DexType::get_type("LK;"), name));
  // Intf1 and Intf3 have the same method name
  EXPECT_TRUE(
      type_class(DexType::get_type("LIntf1;"))->get_vmethods()[0]->get_name() ==
      type_class(DexType::get_type("LIntf3;"))->get_vmethods()[0]->get_name());
  print_scope(scope);
}

/**
 * interface Intf1 implements Intf2 { void f(); }
 * interface Intf2 { void g(int); }
 * interface Intf3 implements Intf4 { void f()); }
 * interface Intf4 { void f()); }
 * class java.lang.Object { // Object methods ... }
 * class A { void f() {} }
 *   class F extends A { void f(int) {} boolean equals(Object) {} void g(int); }
 *     class G extends F { void g(int) {} }
 *       class H extends G implements Intf2 { }
 *         class I extends H { void g(int) {} }
 *         class J extends H {}
 *       class K extends G { void g(int) {} }
 *     class L extends F { void g(int) {} }
 * class B implements Intf1 { void g() {} void f() {} }
 *   class C extends B implements Intf2 { void g(int) {} }
 *     class D extends C implements Intf2, Intf3 { void f() {} void g(int) {} }
 *     class E extends C { void g() {} void g(int) {}}
 * class M { void f(int) {} }
 *   class N externds M implements EscIntf { void h(int) {}}
 */
TEST_F(RenamerTest, Interface3IntfOverEscape) {
  std::vector<DexClass*> scope = create_scope_11();
  // add static void A() {} in class A
  auto* cls = type_class(DexType::get_type("LA;"));
  create_empty_method(
      cls, "A",
      DexProto::make_proto(type::_void(), DexTypeList::make_type_list({})),
      ACC_PUBLIC | ACC_STATIC);

  print_scope(scope);
  EXPECT_EQ(18, rename_virtuals(scope));
  walk::methods(scope, [&](DexMethod* meth) {
    if (meth->get_name() == DexString::make_string("f")) {
      EXPECT_TRUE(meth->get_class() == DexType::get_type("LM;"));
      return;
    }
    if (meth->get_name() == DexString::make_string("h")) {
      EXPECT_TRUE(meth->get_class() == DexType::get_type("LN;"));
      return;
    }
    ASSERT_NE(meth->get_name(), DexString::make_string("f"));
    ASSERT_NE(meth->get_name(), DexString::make_string("g"));
  });
  check_intf_common();
  // Intf2 method name must also be in F, G, I, K
  const auto* name =
      type_class(DexType::get_type("LIntf2;"))->get_vmethods()[0]->get_name();
  EXPECT_TRUE(has_method(DexType::get_type("LF;"), name));
  EXPECT_TRUE(has_method(DexType::get_type("LG;"), name));
  EXPECT_TRUE(has_method(DexType::get_type("LI;"), name));
  EXPECT_TRUE(has_method(DexType::get_type("LK;"), name));
  // Intf1 and Intf3 have the same method name
  EXPECT_TRUE(
      type_class(DexType::get_type("LIntf1;"))->get_vmethods()[0]->get_name() ==
      type_class(DexType::get_type("LIntf3;"))->get_vmethods()[0]->get_name());
  // M.f(int) and N.h(int) stay the same
  EXPECT_TRUE(
      type_class(DexType::get_type("LM;"))->get_vmethods()[0]->get_name() ==
      DexString::get_string("f"));
  EXPECT_TRUE(
      type_class(DexType::get_type("LN;"))->get_vmethods()[0]->get_name() ==
      DexString::get_string("h"));
  print_scope(scope);
}

/**
 * A method handle (tool-generated here) that names a renamed method through a
 * subclass follows the rename, like an invoke of that method would.
 *
 * class A { void f() {} }
 *   class B extends A { }
 * class C { static void run() { const-method-handle invoke-instance LB;.f } }
 */
TEST_F(RenamerTest, MethodHandleOfInheritedMethod) {
  std::vector<DexClass*> scope = create_empty_scope();
  auto* obj_t = type::java_lang_Object();
  auto* a_cls = create_internal_class(DexType::make_type("LA;"), obj_t, {});
  scope.push_back(a_cls);
  auto* void_void =
      DexProto::make_proto(type::_void(), DexTypeList::make_type_list({}));
  auto* a_f = create_empty_method(a_cls, "f", void_void);
  auto* b_t = DexType::make_type("LB;");
  scope.push_back(create_internal_class(b_t, a_cls->get_type(), {}));
  auto* c_cls = create_internal_class(DexType::make_type("LC;"), obj_t, {});
  scope.push_back(c_cls);
  auto* run = DexMethod::make_method("LC;.run:()V")
                  ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                                  assembler::ircode_from_string(R"((
                                    (const-method-handle invoke-instance "LB;.f:()V")
                                    (move-result-pseudo-object v0)
                                    (return-void)
                                  ))"),
                                  /* is_virtual */ false);
  c_cls->add_method(run);

  rename_virtuals(scope);

  ASSERT_NE(a_f->get_name(), DexString::make_string("f"));
  auto* insn = run->get_code()->begin()->insn;
  ASSERT_EQ(insn->opcode(), OPCODE_CONST_METHOD_HANDLE);
  EXPECT_EQ(insn->get_methodhandle()->methodref()->get_name(), a_f->get_name());
}

namespace {

// Makes a scope in which `B` inherits `A.f`, and `C` holds `method_handle`, an
// invoke-instance handle of `LB;.f:()V`, as `hold` attaches it. Returns `A.f`.
DexMethod* make_scope_with_handle_of_inherited_method(
    std::vector<DexClass*>& scope,
    DexMethodHandle*& method_handle,
    const std::function<void(DexClass*, DexMethodHandle*)>& hold) {
  scope = create_empty_scope();
  auto* obj_t = type::java_lang_Object();
  auto* a_cls = create_internal_class(DexType::make_type("LA;"), obj_t, {});
  scope.push_back(a_cls);
  auto* void_void =
      DexProto::make_proto(type::_void(), DexTypeList::make_type_list({}));
  auto* a_f = create_empty_method(a_cls, "f", void_void);
  auto* b_t = DexType::make_type("LB;");
  scope.push_back(create_internal_class(b_t, a_cls->get_type(), {}));
  auto* c_cls = create_internal_class(DexType::make_type("LC;"), obj_t, {});
  scope.push_back(c_cls);
  method_handle = new DexMethodHandle(METHOD_HANDLE_TYPE_INVOKE_INSTANCE,
                                      DexMethod::make_method("LB;.f:()V"));
  g_redex->publish_methodhandle(method_handle);
  hold(c_cls, method_handle);
  return a_f;
}

} // namespace

/**
 * A method handle that an annotation or a static field value holds follows
 * the rename too.
 *
 * class A { void f() {} }
 *   class B extends A { }
 * @Callback(invoke-instance LB;.f) class C { }
 * class C { static MethodHandle HANDLE = invoke-instance LB;.f }
 */
TEST_F(RenamerTest, AnnotationMethodHandleOfInheritedMethod) {
  std::vector<DexClass*> scope;
  DexMethodHandle* method_handle = nullptr;
  auto* a_f = make_scope_with_handle_of_inherited_method(
      scope, method_handle, [](DexClass* cls, DexMethodHandle* handle) {
        auto annotation = std::make_unique<DexAnnotation>(
            DexType::make_type("LCallback;"), DAV_RUNTIME);
        annotation->add_element(
            "value", std::make_unique<DexEncodedValueMethodHandle>(handle));
        auto annotation_set = std::make_unique<DexAnnotationSet>();
        annotation_set->add_annotation(std::move(annotation));
        ASSERT_TRUE(cls->attach_annotation_set(std::move(annotation_set)));
      });

  rename_virtuals(scope);

  ASSERT_NE(a_f->get_name(), DexString::make_string("f"));
  EXPECT_EQ(method_handle->methodref()->get_name(), a_f->get_name());
}

TEST_F(RenamerTest, StaticFieldValueMethodHandleOfInheritedMethod) {
  std::vector<DexClass*> scope;
  DexMethodHandle* method_handle = nullptr;
  auto* a_f = make_scope_with_handle_of_inherited_method(
      scope, method_handle, [](DexClass* cls, DexMethodHandle* handle) {
        cls->add_field(
            DexField::make_field("LC;.HANDLE:Ljava/lang/invoke/MethodHandle;")
                ->make_concrete(
                    ACC_PUBLIC | ACC_STATIC | ACC_FINAL,
                    std::make_unique<DexEncodedValueMethodHandle>(handle)));
      });

  rename_virtuals(scope);

  ASSERT_NE(a_f->get_name(), DexString::make_string("f"));
  EXPECT_EQ(method_handle->methodref()->get_name(), a_f->get_name());
}
