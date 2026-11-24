/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "DeterministicContainers.h"
#include "DexClass.h"
#include "RedexTest.h"
#include "Resolver.h"
#include "ScopeHelper.h"
#include "TypeUtil.h"
#include "VirtualScopes.h"

namespace {

DexProto* void_proto() {
  return DexProto::make_proto(type::_void(), DexTypeList::make_type_list({}));
}

DexProto* void_int_proto() {
  return DexProto::make_proto(type::_void(),
                              DexTypeList::make_type_list({type::_int()}));
}

DexClass* make_class(Scope& scope,
                     const char* name,
                     DexType* super,
                     const std::vector<DexType*>& interfaces = {},
                     DexAccessFlags access = ACC_PUBLIC) {
  auto* cls = create_internal_class(DexType::make_type(name), super, interfaces,
                                    access);
  scope.push_back(cls);
  return cls;
}

DexClass* make_intf(Scope& scope,
                    const char* name,
                    const std::vector<DexType*>& supers = {}) {
  return make_class(scope, name, type::java_lang_Object(), supers,
                    ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
}

// The scope rooted at `type` whose top def carries `name`, or nullptr.
const virtual_scope::VirtualScope* scope_for(
    const virtual_scope::VirtualScopes& vs,
    const DexType* type,
    const char* name) {
  for (const auto* s : vs.at(type)) {
    if (s->top_def()->get_name()->str() == name) {
      return s;
    }
  }
  return nullptr;
}

bool has_member(const virtual_scope::VirtualScope* s, const DexMethod* m) {
  for (const auto* member : s->methods()) {
    if (member == m) {
      return true;
    }
  }
  return false;
}

} // namespace

class VirtualScopesTest : public RedexTest {};

// Object <- A{m} <- B{m override}. The scope is rooted at A and contains both.
TEST_F(VirtualScopesTest, SimpleOverrideChain) {
  auto scope = create_empty_scope();
  auto* a = make_class(scope, "LA;", type::java_lang_Object());
  auto* b = make_class(scope, "LB;", a->get_type());
  auto* am = create_empty_method(a, "m", void_proto());
  create_empty_method(b, "m", void_proto());

  virtual_scope::VirtualScopes vs(scope);

  const auto& a_scopes = vs.at(a->get_type());
  ASSERT_EQ(a_scopes.size(), 1u);
  const auto* s = a_scopes[0];
  EXPECT_EQ(s->root(), a->get_type());
  EXPECT_EQ(s->top_def(), am);
  EXPECT_EQ(s->methods().size(), 2u); // A.m and B.m
  EXPECT_EQ(s->methods()[0], am); // top first
  EXPECT_FALSE(s->implements_interface());
  EXPECT_TRUE(s->has_def());
  EXPECT_FALSE(s->is_effectively_final());

  // B.m overrides A.m, so it does not root a scope at B.
  EXPECT_TRUE(vs.at(b->get_type()).empty());
}

// A single leaf method honoring no interface is effectively final.
TEST_F(VirtualScopesTest, SingleFinalMethod) {
  auto scope = create_empty_scope();
  auto* c = make_class(scope, "LC;", type::java_lang_Object());
  auto* cf = create_empty_method(c, "f", void_proto());

  virtual_scope::VirtualScopes vs(scope);

  const auto& c_scopes = vs.at(c->get_type());
  ASSERT_EQ(c_scopes.size(), 1u);
  const auto* s = c_scopes[0];
  EXPECT_EQ(s->top_def(), cf);
  EXPECT_EQ(s->methods().size(), 1u);
  EXPECT_TRUE(s->is_effectively_final());
  EXPECT_FALSE(s->implements_interface());
}

// interface I{n}; class C implements I { n }. C.n roots an impl scope.
TEST_F(VirtualScopesTest, InterfaceImplementation) {
  auto scope = create_empty_scope();
  auto* i = make_class(scope, "LI;", type::java_lang_Object(), {},
                       ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  create_abstract_method(i, "n", void_proto());
  auto* c = make_class(scope, "LC;", type::java_lang_Object(), {i->get_type()});
  auto* cn = create_empty_method(c, "n", void_proto());

  virtual_scope::VirtualScopes vs(scope);

  // Interface classes never root class scopes.
  EXPECT_TRUE(vs.at(i->get_type()).empty());

  const auto& c_scopes = vs.at(c->get_type());
  ASSERT_EQ(c_scopes.size(), 1u);
  const auto* s = c_scopes[0];
  EXPECT_EQ(s->top_def(), cn);
  EXPECT_TRUE(s->implements_interface());
  EXPECT_EQ(s->implemented_interfaces().count(i->get_type()), 1u);
  EXPECT_TRUE(s->has_def());
}

// interface I{n}; abstract C implements I with an *abstract* n; D extends C
// with a concrete n. The abstract root method anchors the scope (top_def is the
// abstract C.n -- a real method, never nullptr) and D.n folds in as an
// override.
TEST_F(VirtualScopesTest, AbstractRootMethodAnchorsScope) {
  auto scope = create_empty_scope();
  auto* i = make_class(scope, "LI;", type::java_lang_Object(), {},
                       ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  create_abstract_method(i, "n", void_proto());
  auto* c = make_class(scope, "LC;", type::java_lang_Object(), {i->get_type()},
                       ACC_PUBLIC | ACC_ABSTRACT);
  auto* cn = create_abstract_method(c, "n", void_proto());
  auto* d = make_class(scope, "LD;", c->get_type());
  create_empty_method(d, "n", void_proto());

  virtual_scope::VirtualScopes vs(scope);

  const auto& c_scopes = vs.at(c->get_type());
  ASSERT_EQ(c_scopes.size(), 1u);
  const auto* s = c_scopes[0];
  EXPECT_EQ(s->root(), c->get_type());
  EXPECT_EQ(s->top_def(), cn); // abstract, but a real method
  EXPECT_EQ(s->methods().size(), 2u); // C.n (abstract) + D.n (concrete)
  EXPECT_TRUE(s->has_def()); // D.n is concrete
  EXPECT_TRUE(s->implements_interface());
  EXPECT_EQ(s->implemented_interfaces().count(i->get_type()), 1u);

  // D.n overrides C.n, so it does not root its own scope.
  EXPECT_TRUE(vs.at(d->get_type()).empty());
}

// class A{f(), f(int)}; class B extends A overrides both. Methods sharing a
// name but differing in proto form SEPARATE scopes (scopes are keyed by name +
// proto).
TEST_F(VirtualScopesTest, OverloadsFormSeparateScopes) {
  auto scope = create_empty_scope();
  auto* a = make_class(scope, "LA;", type::java_lang_Object());
  auto* af = create_empty_method(a, "f", void_proto());
  auto* afi = create_empty_method(a, "f", void_int_proto());
  auto* b = make_class(scope, "LB;", a->get_type());
  create_empty_method(b, "f", void_proto());
  create_empty_method(b, "f", void_int_proto());

  virtual_scope::VirtualScopes vs(scope);

  const auto& a_scopes = vs.at(a->get_type());
  ASSERT_EQ(a_scopes.size(), 2u); // f() and f(int) are distinct scopes
  const virtual_scope::VirtualScope* void_scope = nullptr;
  const virtual_scope::VirtualScope* int_scope = nullptr;
  for (const auto* s : a_scopes) {
    if (s->top_def() == af) {
      void_scope = s;
    } else if (s->top_def() == afi) {
      int_scope = s;
    }
  }
  ASSERT_NE(void_scope, nullptr);
  ASSERT_NE(int_scope, nullptr);
  EXPECT_EQ(void_scope->methods().size(), 2u); // A.f() + B.f()
  EXPECT_EQ(int_scope->methods().size(), 2u); // A.f(int) + B.f(int)
}

// interfaces I{n} and J{n} (same signature); class A implements I with n; class
// B extends A implements J, overriding n. The single scope rooted at A
// satisfies BOTH interfaces, so implemented_interfaces() reports {I, J}.
TEST_F(VirtualScopesTest, ScopeImplementingMultipleInterfaces) {
  auto scope = create_empty_scope();
  auto* i = make_class(scope, "LI;", type::java_lang_Object(), {},
                       ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  create_abstract_method(i, "n", void_proto());
  auto* j = make_class(scope, "LJ;", type::java_lang_Object(), {},
                       ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  create_abstract_method(j, "n", void_proto());
  auto* a = make_class(scope, "LA;", type::java_lang_Object(), {i->get_type()});
  auto* an = create_empty_method(a, "n", void_proto());
  auto* b = make_class(scope, "LB;", a->get_type(), {j->get_type()});
  create_empty_method(b, "n", void_proto());

  virtual_scope::VirtualScopes vs(scope);

  const auto& a_scopes = vs.at(a->get_type());
  ASSERT_EQ(a_scopes.size(), 1u);
  const auto* s = a_scopes[0];
  EXPECT_EQ(s->top_def(), an);
  EXPECT_EQ(s->methods().size(), 2u); // A.n + B.n
  EXPECT_TRUE(s->implements_interface());
  EXPECT_EQ(s->implemented_interfaces().size(), 2u);
  EXPECT_EQ(s->implemented_interfaces().count(i->get_type()), 1u);
  EXPECT_EQ(s->implemented_interfaces().count(j->get_type()), 1u);
}

// interface Base{n}; interface Derived extends Base, redeclares n; class C
// implements Derived with a concrete n. implemented_interfaces() reports both
// the directly-implemented Derived and its transitive super-interface Base.
TEST_F(VirtualScopesTest, TransitiveSuperInterfacesReported) {
  auto scope = create_empty_scope();
  auto* base = make_class(scope, "LBase;", type::java_lang_Object(), {},
                          ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  create_abstract_method(base, "n", void_proto());
  auto* derived =
      make_class(scope, "LDerived;", type::java_lang_Object(),
                 {base->get_type()}, ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  create_abstract_method(derived, "n", void_proto());
  auto* c =
      make_class(scope, "LC;", type::java_lang_Object(), {derived->get_type()});
  auto* cn = create_empty_method(c, "n", void_proto());

  virtual_scope::VirtualScopes vs(scope);

  const auto& c_scopes = vs.at(c->get_type());
  ASSERT_EQ(c_scopes.size(), 1u);
  const auto* s = c_scopes[0];
  EXPECT_EQ(s->top_def(), cn);
  EXPECT_TRUE(s->implements_interface());
  EXPECT_EQ(s->implemented_interfaces().count(derived->get_type()), 1u);
  EXPECT_EQ(s->implemented_interfaces().count(base->get_type()), 1u);
}

// methods() must reproduce the legacy signature-map order: the root's top def
// first, then a pre-order DFS of the override tree with siblings visited in
// ascending defining-class type order. MOG stores children in an UnorderedBag,
// so without imposing this order the result would be nondeterministic and leak
// into ClassMerging output. The hierarchy here distinguishes DFS from a flat
// type sort: A{m}; B extends A; E extends B; D extends A. Pre-order DFS yields
// [A, B, E, D] (B's subtree before sibling D), whereas a flat sort by type
// would give [A, B, D, E].
TEST_F(VirtualScopesTest, MethodsFollowLegacyPreorderDfsOrder) {
  auto scope = create_empty_scope();
  auto* a = make_class(scope, "LA;", type::java_lang_Object());
  auto* am = create_empty_method(a, "m", void_proto());
  auto* b = make_class(scope, "LB;", a->get_type());
  auto* bm = create_empty_method(b, "m", void_proto());
  auto* e = make_class(scope, "LE;", b->get_type());
  auto* em = create_empty_method(e, "m", void_proto());
  auto* d = make_class(scope, "LD;", a->get_type());
  auto* dm = create_empty_method(d, "m", void_proto());

  virtual_scope::VirtualScopes vs(scope);

  const auto& a_scopes = vs.at(a->get_type());
  ASSERT_EQ(a_scopes.size(), 1u);
  const auto& methods = a_scopes[0]->methods();
  ASSERT_EQ(methods.size(), 4u);
  EXPECT_EQ(methods[0], am); // top def
  EXPECT_EQ(methods[1], bm); // B (sibling B < D)
  EXPECT_EQ(methods[2], em); // E, B's subtree, before sibling D
  EXPECT_EQ(methods[3], dm); // D last
}

// The shapes below were found on a real app (b4a) while migrating consumers off
// the legacy virtual-scope machinery. Each one distinguishes a scope layout
// that the simpler shapes above do not reach, so they are kept as regression
// cover.

// androidx MenuBuilder/SubMenuBuilder: the root implements the interface and
// defines the method, and a subclass overrides it. Both belong to one scope.
TEST_F(VirtualScopesTest, IntfImplOnRootWithSubclassOverride) {
  auto scope = create_empty_scope();
  auto* i = make_intf(scope, "LI;");
  create_abstract_method(i, "m", void_proto());
  auto* c = make_class(scope, "LC;", type::java_lang_Object(), {i->get_type()});
  auto* cm = create_empty_method(c, "m", void_proto());
  auto* d = make_class(scope, "LD;", c->get_type());
  auto* dm = create_empty_method(d, "m", void_proto());

  virtual_scope::VirtualScopes vs(scope);

  const auto* s = scope_for(vs, c->get_type(), "m");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(s->top_def(), cm);
  EXPECT_EQ(s->methods().size(), 2u);
  EXPECT_TRUE(has_member(s, dm));
  EXPECT_TRUE(s->implements_interface());
}

// rendercore RenderUnit: the root does NOT implement the interface (a plain top
// def); a subclass both declares the interface and overrides the method. The
// override still belongs to the root's scope, and the scope picks up the
// interface from that subclass.
TEST_F(VirtualScopesTest, SubclassImplementsIntfRootDoesNot) {
  auto scope = create_empty_scope();
  auto* i = make_intf(scope, "LI;");
  create_abstract_method(i, "m", void_proto());
  auto* c = make_class(scope, "LC;", type::java_lang_Object());
  auto* cm = create_empty_method(c, "m", void_proto());
  auto* d = make_class(scope, "LD;", c->get_type(), {i->get_type()});
  auto* dm = create_empty_method(d, "m", void_proto());

  virtual_scope::VirtualScopes vs(scope);

  const auto* s = scope_for(vs, c->get_type(), "m");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(s->top_def(), cm);
  EXPECT_EQ(s->methods().size(), 2u);
  EXPECT_TRUE(has_member(s, dm));
  EXPECT_TRUE(s->implements_interface());
  EXPECT_TRUE(vs.at(d->get_type()).empty());
}

// The subclass declares a SUB-interface of the one the root declares.
TEST_F(VirtualScopesTest, SubclassDeclaresSubIntfAndOverrides) {
  auto scope = create_empty_scope();
  auto* base_i = make_intf(scope, "LI;");
  create_abstract_method(base_i, "m", void_proto());
  auto* sub_i = make_intf(scope, "LSubI;", {base_i->get_type()});
  auto* c =
      make_class(scope, "LC;", type::java_lang_Object(), {base_i->get_type()});
  auto* cm = create_empty_method(c, "m", void_proto());
  auto* d = make_class(scope, "LD;", c->get_type(), {sub_i->get_type()});
  auto* dm = create_empty_method(d, "m", void_proto());

  virtual_scope::VirtualScopes vs(scope);

  const auto* s = scope_for(vs, c->get_type(), "m");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(s->top_def(), cm);
  EXPECT_EQ(s->methods().size(), 2u);
  EXPECT_TRUE(has_member(s, dm));
  EXPECT_TRUE(s->implements_interface());
}

// A method an earlier pass detached from its class is NOT a scope member.
//
// `DexClass::remove_method` only erases the method from the class's vmethod
// list: the DexMethod stays interned, keeps is_def(), and is still returned by
// `DexMethod::get_method`. The legacy machinery reached interface obligations
// through that global lookup and so resurrected such methods as scope members;
// VirtualScopes walks only live vmethods. Excluding them is correct -- a method
// in no class's method list is not in the dex and cannot be dispatched -- and
// this difference was the entire measured size delta of the VirtualRenamer
// migration.
TEST_F(VirtualScopesTest, DetachedMethodIsNotAScopeMember) {
  auto scope = create_empty_scope();
  auto* i = make_intf(scope, "LI;");
  create_abstract_method(i, "m", void_proto());
  auto* c = make_class(scope, "LC;", type::java_lang_Object(), {i->get_type()});
  auto* cm = create_empty_method(c, "m", void_proto());
  auto* d = make_class(scope, "LD;", c->get_type(), {i->get_type()});
  auto* dm = create_empty_method(d, "m", void_proto());

  d->remove_method(dm);
  // Still interned and still findable -- this is what legacy picked up.
  ASSERT_TRUE(dm->is_def());
  ASSERT_EQ(
      DexMethod::get_method(d->get_type(), dm->get_name(), dm->get_proto()),
      static_cast<DexMethodRef*>(dm));

  virtual_scope::VirtualScopes vs(scope);

  const auto* s = scope_for(vs, c->get_type(), "m");
  ASSERT_NE(s, nullptr);
  EXPECT_TRUE(has_member(s, cm));
  EXPECT_FALSE(has_member(s, dm));
  EXPECT_EQ(s->methods().size(), 1u);
}

// A detached override is not a live scope member, but the subclass's interface
// obligation still applies to the inherited implementation at the root.
TEST_F(VirtualScopesTest,
       DetachedSubclassInterfaceMarksInheritedImplementation) {
  auto scope = create_empty_scope();
  auto* i = make_intf(scope, "LI;");
  create_abstract_method(i, "m", void_proto());
  auto* c = make_class(scope, "LC;", type::java_lang_Object());
  auto* cm = create_empty_method(c, "m", void_proto());
  auto* d = make_class(scope, "LD;", c->get_type(), {i->get_type()});
  auto* dm = create_empty_method(d, "m", void_proto());

  d->remove_method(dm);
  virtual_scope::VirtualScopes vs(scope);

  const auto* s = scope_for(vs, c->get_type(), "m");
  ASSERT_NE(s, nullptr);
  EXPECT_TRUE(has_member(s, cm));
  EXPECT_FALSE(has_member(s, dm));
  EXPECT_EQ(s->methods().size(), 1u);
  EXPECT_TRUE(s->implements_interface());
  EXPECT_EQ(s->implemented_interfaces().count(i->get_type()), 1u);
}

// `find` climbs the method's own superclass chain to the scope root. Two
// hierarchies declaring the same signature must resolve to their own scope,
// never to each other's.
TEST_F(VirtualScopesTest, FindResolvesMethodToItsOwnScopeRoot) {
  auto scope = create_empty_scope();
  auto* a = make_class(scope, "LA;", type::java_lang_Object());
  auto* am = create_empty_method(a, "m", void_proto());
  auto* b = make_class(scope, "LB;", a->get_type());
  auto* bm = create_empty_method(b, "m", void_proto());
  auto* p = make_class(scope, "LP;", type::java_lang_Object());
  auto* pm = create_empty_method(p, "m", void_proto());
  // Static methods are direct, so they belong to no virtual scope.
  auto* as = create_empty_method(a, "s", void_proto(), ACC_PUBLIC | ACC_STATIC);

  virtual_scope::VirtualScopes vs(scope);

  const auto* a_scope = scope_for(vs, a->get_type(), "m");
  ASSERT_NE(a_scope, nullptr);
  EXPECT_EQ(vs.find(am), a_scope);
  EXPECT_EQ(vs.find(bm), a_scope); // B.m climbs to the root at A

  const auto* p_scope = scope_for(vs, p->get_type(), "m");
  ASSERT_NE(p_scope, nullptr);
  EXPECT_NE(p_scope, a_scope);
  EXPECT_EQ(vs.find(pm), p_scope);

  EXPECT_EQ(vs.find(as), nullptr);
}

// The walker groups by (name, proto) across unrelated hierarchies and unions
// their interfaces: I{n} and J{n} are disjoint, but C.n and E.n share a
// signature, so they form ONE group carrying both interfaces. VirtualRenamer
// depends on this -- scopes in a group must be renamed together, or a class
// implementing both interfaces would lose dispatch.
TEST_F(VirtualScopesTest, WalkInterfaceScopesGroupsSignatureAcrossInterfaces) {
  auto scope = create_empty_scope();
  auto* i = make_intf(scope, "LI;");
  create_abstract_method(i, "n", void_proto());
  auto* j = make_intf(scope, "LJ;");
  create_abstract_method(j, "n", void_proto());
  auto* c = make_class(scope, "LC;", type::java_lang_Object(), {i->get_type()});
  create_empty_method(c, "n", void_proto());
  auto* e = make_class(scope, "LE;", type::java_lang_Object(), {j->get_type()});
  create_empty_method(e, "n", void_proto());
  // Implements nothing, so it must not be reported.
  auto* a = make_class(scope, "LA;", type::java_lang_Object());
  create_empty_method(a, "m", void_proto());

  virtual_scope::VirtualScopes vs(scope);

  size_t groups = 0;
  vs.walk_interface_scopes(
      [&](const DexString* name, const DexProto* proto,
          const std::vector<const virtual_scope::VirtualScope*>& scopes,
          const TypeSet& intfs) {
        ++groups;
        EXPECT_EQ(name->str(), "n");
        EXPECT_EQ(proto, void_proto());
        EXPECT_EQ(scopes.size(), 2u);
        UnorderedSet<const DexType*> roots;
        for (const auto* s : scopes) {
          roots.insert(s->root());
        }
        EXPECT_EQ(roots.count(c->get_type()), 1u);
        EXPECT_EQ(roots.count(e->get_type()), 1u);
        EXPECT_EQ(intfs.size(), 2u);
        EXPECT_EQ(intfs.count(i->get_type()), 1u);
        EXPECT_EQ(intfs.count(j->get_type()), 1u);
      });
  EXPECT_EQ(groups, 1u);
}

// class C { public void wait(int timeout) {} } is legal Java: it overloads, and
// does not override, the final Object.wait(), wait(long) and wait(long, int).
// So C.wait(int) roots its own effectively final scope.
TEST_F(VirtualScopesTest, ObjectWaitIntOverloadRootsOwnScope) {
  auto scope = create_empty_scope();
  auto* c = make_class(scope, "LC;", type::java_lang_Object());
  auto* cw = create_empty_method(c, "wait", void_int_proto());

  const auto* wait_long = resolve_method(
      type_class(type::java_lang_Object()), DexString::make_string("wait"),
      DexProto::make_proto(type::_void(),
                           DexTypeList::make_type_list({type::_long()})),
      MethodSearch::Virtual);
  ASSERT_NE(wait_long, nullptr);
  EXPECT_TRUE(is_public(wait_long));
  EXPECT_TRUE(is_final(wait_long));

  virtual_scope::VirtualScopes vs(scope);

  const auto& c_scopes = vs.at(c->get_type());
  ASSERT_EQ(c_scopes.size(), 1u);
  EXPECT_EQ(c_scopes[0]->top_def(), cw);
  EXPECT_EQ(c_scopes[0]->methods().size(), 1u);
  EXPECT_TRUE(c_scopes[0]->is_effectively_final());
}
