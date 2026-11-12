/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "ClassHierarchy.h"
#include "Creators.h"
#include "DexStore.h"
#include "DexUtil.h"
#include "IRAssembler.h"
#include "RedexTest.h"
#include "SpecializeRtype.h"

class SpecializeRtypeTest : public RedexTest {};

TEST_F(SpecializeRtypeTest, keeps_default_method_of_interface) {
  // `C.get()` returning `String` would override `I.get()`, which `C` does not
  // override today.
  create_object_class();
  ClassCreator intf_creator(DexType::make_type("LI;"));
  intf_creator.set_super(type::java_lang_Object());
  intf_creator.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  auto* default_method = DexMethod::make_method("LI;.get:()Ljava/lang/String;")
                             ->make_concrete(ACC_PUBLIC, true);
  default_method->set_code(assembler::ircode_from_string(R"((
    (load-param-object v1)
    (const-string "default")
    (move-result-pseudo-object v0)
    (return-object v0)
  ))"));
  intf_creator.add_method(default_method);
  auto* intf = intf_creator.create();

  ClassCreator creator(DexType::make_type("LC;"));
  creator.set_super(type::java_lang_Object());
  creator.add_interface(intf->get_type());
  auto* get = DexMethod::make_method("LC;.get:()Ljava/lang/Object;")
                  ->make_concrete(ACC_PUBLIC, true);
  get->set_code(assembler::ircode_from_string(R"((
    (load-param-object v1)
    (const-string "C")
    (move-result-pseudo-object v0)
    (return-object v0)
  ))"));
  creator.add_method(get);
  auto* cls = creator.create();

  DexStore store("classes");
  store.add_classes({intf, cls});
  DexStoresVector stores{store};
  Scope scope{intf, cls};
  resolve_refs::MethodToInferredReturnType candidates{
      {get, type::java_lang_String()}};
  resolve_refs::RtypeSpecialization specialization(
      candidates, XStoreRefs(stores, /* normal_primary_dex */ false));
  specialization.specialize_rtypes(scope, build_subtype_maps(scope));

  EXPECT_EQ(get->get_proto()->get_rtype(), type::java_lang_Object());
}

TEST_F(SpecializeRtypeTest, keeps_group_whose_root_collides) {
  // `Z.m()` is implemented by `B.m()`, which `S` inherits. Once the group of
  // `A.m()` returns `P`, `Z.m()` returning `P` would collide with it, so the
  // group of `Z.m()` keeps its signature, `B.m()` included.
  create_object_class();
  auto* q = DexType::make_type("LQ;");
  auto* p = DexType::make_type("LP;");
  auto make_class =
      [](DexType* type, DexType* super, const std::vector<DexType*>& interfaces,
         DexAccessFlags access,
         const std::vector<std::pair<std::string, bool>>& methods) {
        ClassCreator creator(type);
        creator.set_super(super);
        creator.set_access(access);
        for (auto* intf : interfaces) {
          creator.add_interface(intf);
        }
        for (const auto& [signature, abstract] : methods) {
          auto* method = DexMethod::make_method(signature)->make_concrete(
              abstract ? ACC_PUBLIC | ACC_ABSTRACT : ACC_PUBLIC, true);
          if (!abstract) {
            method->set_code(assembler::ircode_from_string(R"((
          (load-param-object v1)
          (new-instance "LP;")
          (move-result-pseudo-object v0)
          (return-object v0)
        ))"));
          }
          creator.add_method(method);
        }
        return creator.create();
      };
  const auto interface_access = ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT;
  auto* q_cls = make_class(q, type::java_lang_Object(), {}, ACC_PUBLIC, {});
  auto* p_cls = make_class(p, q, {}, ACC_PUBLIC, {});
  auto* a = make_class(DexType::make_type("LA;"), type::java_lang_Object(), {},
                       interface_access, {{"LA;.m:()LQ;", true}});
  auto* z = make_class(DexType::make_type("LZ;"), type::java_lang_Object(),
                       {a->get_type()}, interface_access,
                       {{"LZ;.m:()Ljava/lang/Object;", true}});
  auto* b = make_class(DexType::make_type("LB;"), type::java_lang_Object(), {},
                       ACC_PUBLIC, {{"LB;.m:()Ljava/lang/Object;", false}});
  auto* s = make_class(DexType::make_type("LS;"), b->get_type(),
                       {z->get_type()}, ACC_PUBLIC, {{"LS;.m:()LQ;", false}});
  auto* t = make_class(DexType::make_type("LT;"), type::java_lang_Object(),
                       {a->get_type()}, ACC_PUBLIC, {{"LT;.m:()LQ;", false}});

  Scope scope{q_cls, p_cls, a, z, b, s, t};
  DexStore store("classes");
  store.add_classes(scope);
  DexStoresVector stores{store};
  auto def = [](const char* signature) {
    return DexMethod::get_method(signature)->as_def();
  };
  resolve_refs::MethodToInferredReturnType candidates{
      {def("LB;.m:()Ljava/lang/Object;"), p},
      {def("LS;.m:()LQ;"), p},
      {def("LT;.m:()LQ;"), p}};
  resolve_refs::RtypeSpecialization specialization(
      candidates, XStoreRefs(stores, /* normal_primary_dex */ false));
  specialization.specialize_rtypes(scope, build_subtype_maps(scope));

  EXPECT_NE(DexMethod::get_method("LA;.m:()LP;"), nullptr);
  EXPECT_NE(DexMethod::get_method("LS;.m:()LP;"), nullptr);
  EXPECT_NE(DexMethod::get_method("LT;.m:()LP;"), nullptr);
  EXPECT_NE(DexMethod::get_method("LZ;.m:()Ljava/lang/Object;"), nullptr);
  EXPECT_NE(DexMethod::get_method("LB;.m:()Ljava/lang/Object;"), nullptr);
}

TEST_F(SpecializeRtypeTest, keeps_override_whose_subclass_has_new_signature) {
  // `U.m()` returning `P` does not override `T.m()`. Once `T.m()` returns
  // `P`, it would.
  create_object_class();
  auto* p = DexType::make_type("LP;");
  auto make_method = [](const char* signature, bool abstract) {
    auto* method = DexMethod::make_method(signature)->make_concrete(
        abstract ? ACC_PUBLIC | ACC_ABSTRACT : ACC_PUBLIC, true);
    if (!abstract) {
      method->set_code(assembler::ircode_from_string(R"((
        (load-param-object v1)
        (new-instance "LP;")
        (move-result-pseudo-object v0)
        (return-object v0)
      ))"));
    }
    return method;
  };
  ClassCreator p_creator(p);
  p_creator.set_super(type::java_lang_Object());
  auto* p_cls = p_creator.create();

  ClassCreator a_creator(DexType::make_type("LA;"));
  a_creator.set_super(type::java_lang_Object());
  a_creator.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  a_creator.add_method(make_method("LA;.m:()Ljava/lang/Object;", true));
  auto* a = a_creator.create();

  ClassCreator t_creator(DexType::make_type("LT;"));
  t_creator.set_super(type::java_lang_Object());
  t_creator.add_interface(a->get_type());
  auto* t_m = make_method("LT;.m:()Ljava/lang/Object;", false);
  t_creator.add_method(t_m);
  auto* t = t_creator.create();

  ClassCreator u_creator(DexType::make_type("LU;"));
  u_creator.set_super(t->get_type());
  u_creator.add_method(make_method("LU;.m:()LP;", false));
  auto* u = u_creator.create();

  Scope scope{p_cls, a, t, u};
  DexStore store("classes");
  store.add_classes(scope);
  DexStoresVector stores{store};
  resolve_refs::MethodToInferredReturnType candidates{{t_m, p}};
  resolve_refs::RtypeSpecialization specialization(
      candidates, XStoreRefs(stores, /* normal_primary_dex */ false));
  specialization.specialize_rtypes(scope, build_subtype_maps(scope));

  EXPECT_EQ(t_m->get_proto()->get_rtype(), type::java_lang_Object());
}

TEST_F(SpecializeRtypeTest, keeps_method_whose_subclass_has_default_method) {
  // `U` inherits `T.m()` and implements `J`. Once `T.m()` returns `String`,
  // it implements `J.m()` in `U` instead of the default method.
  create_object_class();
  ClassCreator j_creator(DexType::make_type("LJ;"));
  j_creator.set_super(type::java_lang_Object());
  j_creator.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  auto* default_method = DexMethod::make_method("LJ;.m:()Ljava/lang/String;")
                             ->make_concrete(ACC_PUBLIC, true);
  default_method->set_code(assembler::ircode_from_string(R"((
    (load-param-object v1)
    (const-string "default")
    (move-result-pseudo-object v0)
    (return-object v0)
  ))"));
  j_creator.add_method(default_method);
  auto* j = j_creator.create();

  ClassCreator t_creator(DexType::make_type("LT;"));
  t_creator.set_super(type::java_lang_Object());
  auto* m = DexMethod::make_method("LT;.m:()Ljava/lang/Object;")
                ->make_concrete(ACC_PUBLIC, true);
  m->set_code(assembler::ircode_from_string(R"((
    (load-param-object v1)
    (const-string "T")
    (move-result-pseudo-object v0)
    (return-object v0)
  ))"));
  t_creator.add_method(m);
  auto* t = t_creator.create();

  ClassCreator u_creator(DexType::make_type("LU;"));
  u_creator.set_super(t->get_type());
  u_creator.add_interface(j->get_type());
  auto* u = u_creator.create();

  Scope scope{j, t, u};
  DexStore store("classes");
  store.add_classes(scope);
  DexStoresVector stores{store};
  resolve_refs::MethodToInferredReturnType candidates{
      {m, type::java_lang_String()}};
  resolve_refs::RtypeSpecialization specialization(
      candidates, XStoreRefs(stores, /* normal_primary_dex */ false));
  specialization.specialize_rtypes(scope, build_subtype_maps(scope));

  EXPECT_EQ(m->get_proto()->get_rtype(), type::java_lang_Object());
}

TEST_F(SpecializeRtypeTest,
       keeps_method_whose_class_inherits_interface_method) {
  // The abstract `B` implements `I` without declaring `I.m()`. Once `C.m()`
  // returns `String`, it implements `I.m()`.
  create_object_class();
  ClassCreator intf_creator(DexType::make_type("LI;"));
  intf_creator.set_super(type::java_lang_Object());
  intf_creator.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  intf_creator.add_method(DexMethod::make_method("LI;.m:()Ljava/lang/String;")
                              ->make_concrete(ACC_PUBLIC | ACC_ABSTRACT, true));
  auto* intf = intf_creator.create();

  ClassCreator b_creator(DexType::make_type("LB;"));
  b_creator.set_super(type::java_lang_Object());
  b_creator.set_access(ACC_PUBLIC | ACC_ABSTRACT);
  b_creator.add_interface(intf->get_type());
  auto* b = b_creator.create();

  ClassCreator c_creator(DexType::make_type("LC;"));
  c_creator.set_super(b->get_type());
  auto* m = DexMethod::make_method("LC;.m:()Ljava/lang/Object;")
                ->make_concrete(ACC_PUBLIC, true);
  m->set_code(assembler::ircode_from_string(R"((
    (load-param-object v1)
    (const-string "C")
    (move-result-pseudo-object v0)
    (return-object v0)
  ))"));
  c_creator.add_method(m);
  auto* c = c_creator.create();

  Scope scope{intf, b, c};
  DexStore store("classes");
  store.add_classes(scope);
  DexStoresVector stores{store};
  resolve_refs::MethodToInferredReturnType candidates{
      {m, type::java_lang_String()}};
  resolve_refs::RtypeSpecialization specialization(
      candidates, XStoreRefs(stores, /* normal_primary_dex */ false));
  specialization.specialize_rtypes(scope, build_subtype_maps(scope));

  EXPECT_EQ(m->get_proto()->get_rtype(), type::java_lang_Object());
}

TEST_F(SpecializeRtypeTest, keeps_interface_method_whose_implementor_has_it) {
  // `G` implements `A` through the abstract `E` and declares `m()` returning
  // `String`. Once the group of `A.m()` returns `String`, `G.m()` implements
  // `A.m()`.
  create_object_class();
  auto make_class = [](const char* name, DexType* super,
                       DexAccessFlags access) {
    ClassCreator creator(DexType::make_type(name));
    creator.set_super(super);
    creator.set_access(access);
    return creator;
  };
  auto make_method = [](const char* signature, const char* value) {
    auto* method =
        DexMethod::make_method(signature)->make_concrete(ACC_PUBLIC, true);
    method->set_code(assembler::ircode_from_string(std::string(R"((
      (load-param-object v1)
      (const-string ")") + value + R"(")
      (move-result-pseudo-object v0)
      (return-object v0)
    ))"));
    return method;
  };
  auto a_creator = make_class("LA;", type::java_lang_Object(),
                              ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  auto* a_m = DexMethod::make_method("LA;.m:()Ljava/lang/Object;")
                  ->make_concrete(ACC_PUBLIC | ACC_ABSTRACT, true);
  a_creator.add_method(a_m);
  auto* a = a_creator.create();

  auto t_creator = make_class("LT;", type::java_lang_Object(), ACC_PUBLIC);
  t_creator.add_interface(a->get_type());
  auto* t_m = make_method("LT;.m:()Ljava/lang/Object;", "T");
  t_creator.add_method(t_m);
  auto* t = t_creator.create();

  auto e_creator =
      make_class("LE;", type::java_lang_Object(), ACC_PUBLIC | ACC_ABSTRACT);
  e_creator.add_interface(a->get_type());
  auto* e = e_creator.create();

  auto g_creator = make_class("LG;", e->get_type(), ACC_PUBLIC);
  g_creator.add_method(make_method("LG;.m:()Ljava/lang/String;", "G"));
  auto* g = g_creator.create();

  Scope scope{a, t, e, g};
  DexStore store("classes");
  store.add_classes(scope);
  DexStoresVector stores{store};
  resolve_refs::MethodToInferredReturnType candidates{
      {t_m, type::java_lang_String()}};
  resolve_refs::RtypeSpecialization specialization(
      candidates, XStoreRefs(stores, /* normal_primary_dex */ false));
  specialization.specialize_rtypes(scope, build_subtype_maps(scope));

  EXPECT_EQ(a_m->get_proto()->get_rtype(), type::java_lang_Object());
  EXPECT_EQ(t_m->get_proto()->get_rtype(), type::java_lang_Object());
}
