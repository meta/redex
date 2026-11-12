/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "ClassHierarchy.h"
#include "Creators.h"
#include "DexClass.h"
#include "RedexTest.h"
#include "Resolver.h"

DexFieldRef* make_field_ref(DexType* cls, const char* name, DexType* type) {
  return DexField::make_field(cls, DexString::make_string(name), type);
}

DexField* make_field_def(DexType* cls,
                         const char* name,
                         DexType* type,
                         DexAccessFlags access = ACC_PUBLIC,
                         bool external = false) {
  auto* field = dynamic_cast<DexField*>(
      DexField::make_field(cls, DexString::make_string(name), type));
  if (external) {
    field->set_access(access);
    field->set_external();
  } else {
    field->make_concrete(access);
  }
  return field;
}

DexClass* create_class(DexType* type,
                       DexType* super,
                       std::vector<DexType*>& intfs,
                       std::vector<DexField*>& fields,
                       DexAccessFlags access = ACC_PUBLIC,
                       bool external = false) {
  ClassCreator creator(type);
  creator.set_access(access);
  if (external) {
    creator.set_external();
  }
  if (super != nullptr) {
    creator.set_super(super);
  }
  for (auto* const intf : intfs) {
    creator.add_interface(intf);
  }
  for (const auto& field : fields) {
    creator.add_field(field);
  }
  return creator.create();
}

DexClass* create_class(DexType* type,
                       DexType* super,
                       std::vector<DexField*>& fields,
                       DexAccessFlags access = ACC_PUBLIC,
                       bool external = false) {
  std::vector<DexType*> intfs{};
  return create_class(type, super, intfs, fields, access, external);
}

DexMethodRef* create_method(DexClass* cls,
                            const char* method_name,
                            DexAccessFlags access = ACC_PUBLIC,
                            bool concrete = true,
                            bool is_virtual = true) {
  DexProto* proto =
      DexProto::make_proto(type::_void(), DexTypeList::make_type_list({}));
  DexMethodRef* method_ref = DexMethod::make_method(
      cls->get_type(), DexString::make_string(method_name), proto);
  if (concrete) {
    DexMethod* method = method_ref->make_concrete(access, is_virtual);
    cls->add_method(method);
  }
  return method_ref;
}

/**
 * Create the following hierarchy:
 *
 * interface IntF
 *   static final int fin_f
 * external class A
 *   int f1
 * class B extends A
 *   static String f2
 * class C extends B
 *
 * class D
 *   A f
 *
 * class E extends U
 */
void create_field_scope() {
  auto* obj_t = DexType::make_type("Ljava/lang/Object;");
  auto* int_t = DexType::make_type("I");
  auto* string_t = DexType::make_type("Ljava/lang/String;");
  auto* intf = DexType::make_type("Intf");
  auto* a = DexType::make_type("A");
  auto* b = DexType::make_type("B");
  auto* c = DexType::make_type("C");
  auto* d = DexType::make_type("D");
  [[maybe_unused]] auto* u = DexType::make_type("U");
  auto* e = DexType::make_type("E");
  std::vector<DexField*> intf_fields{make_field_def(
      intf, "fin_f", int_t, ACC_PUBLIC | ACC_STATIC | ACC_FINAL, true)};
  [[maybe_unused]] auto* class_Intf =
      create_class(intf, obj_t, intf_fields, ACC_PUBLIC | ACC_INTERFACE);
  std::vector<DexField*> a_fields{
      make_field_def(a, "f1", int_t, ACC_PUBLIC, true)};
  [[maybe_unused]] auto* cls_A =
      create_class(a, obj_t, a_fields, ACC_PUBLIC, true);
  std::vector<DexField*> b_fields{
      make_field_def(b, "f2", string_t, ACC_PUBLIC | ACC_STATIC)};
  std::vector<DexType*> intfs{intf};
  [[maybe_unused]] auto* cls_B = create_class(b, a, intfs, b_fields);
  std::vector<DexField*> no_fields{};
  [[maybe_unused]] auto* cls_C = create_class(c, b, no_fields);
  std::vector<DexField*> d_fields{make_field_def(d, "f", a)};
  [[maybe_unused]] auto* cls_D = create_class(d, obj_t, d_fields);
  [[maybe_unused]] auto* cls_E = create_class(e, obj_t, no_fields);
}

/**
 * Create the following hierarchy:
 *
 * interface A
 *   void method()
 * class B implements A
 *   void method()
 *   static void surprise()
 * class C extends B
 *   void surprise()
 *
 * class D extends C
 *   void method()
 *
 * interface E
 *   void method()
 * abstract class F implements E
 * abstract class G extends F
 * class H extends G
 *   void method()
 */
void create_method_scope() {
  auto* obj_t = DexType::make_type("Ljava/lang/Object;");
  auto* a = DexType::make_type("A");
  auto* b = DexType::make_type("B");
  auto* c = DexType::make_type("C");
  auto* d = DexType::make_type("D");
  auto* e = DexType::make_type("E");
  auto* f = DexType::make_type("F");
  auto* g = DexType::make_type("G");
  auto* h = DexType::make_type("H");
  std::vector<DexField*> no_fields{};
  std::vector<DexType*> interfaces_a{a};
  std::vector<DexType*> no_interfaces{};
  std::vector<DexType*> interfaces_e{e};
  auto* interface_a =
      create_class(a, obj_t, no_fields, ACC_PUBLIC | ACC_INTERFACE);
  create_method(interface_a, "method", ACC_PUBLIC | ACC_INTERFACE);
  auto* cls_b = create_class(b, obj_t, interfaces_a, no_fields, ACC_PUBLIC);
  create_method(cls_b, "method", ACC_PUBLIC);
  create_method(cls_b, "surprise", ACC_PUBLIC | ACC_STATIC, /* concrete */ true,
                /* is_virtual */ false);
  auto* cls_c = create_class(c, b, interfaces_a, no_fields, ACC_PUBLIC);
  create_method(cls_c, "method", ACC_PUBLIC, /* concrete */ false);
  create_method(cls_c, "surprise", ACC_PUBLIC);
  auto* cls_d = create_class(d, c, interfaces_a, no_fields, ACC_PUBLIC);
  create_method(cls_d, "method", ACC_PUBLIC);

  auto* interface_e =
      create_class(e, obj_t, no_fields, ACC_PUBLIC | ACC_INTERFACE);
  create_method(interface_e, "method", ACC_PUBLIC | ACC_INTERFACE);
  auto* cls_f = create_class(f, obj_t, interfaces_e, no_fields,
                             ACC_PUBLIC | ACC_ABSTRACT);
  create_method(cls_f, "method", ACC_PUBLIC, /* concrete */ false);
  auto* cls_g =
      create_class(g, f, no_interfaces, no_fields, ACC_PUBLIC | ACC_ABSTRACT);
  create_method(cls_g, "method", ACC_PUBLIC, /* concrete */ false);
  auto* cls_h = create_class(h, g, no_interfaces, no_fields, ACC_PUBLIC);
  create_method(cls_h, "method", ACC_PUBLIC);
}

class ResolverTest : public RedexTest {};

TEST_F(ResolverTest, ResolveField) {
  create_field_scope();

  // different cases for int A.f1
  DexFieldRef* fdef =
      DexField::get_field(DexType::get_type("A"), DexString::get_string("f1"),
                          DexType::get_type("I"));
  EXPECT_TRUE(fdef != nullptr && fdef->is_def());
  DexFieldRef* fref =
      make_field_ref(DexType::get_type("A"), "f1", DexType::get_type("I"));
  EXPECT_TRUE(fdef->is_def());
  EXPECT_TRUE(resolve_field(fref) == fdef);
  EXPECT_TRUE(resolve_field(fref, FieldSearch::Instance) == fdef);
  EXPECT_TRUE(resolve_field(DexType::get_type("A"),
                            DexString::get_string("f1"),
                            DexType::get_type("I"),
                            FieldSearch::Static) == nullptr);
  EXPECT_TRUE(resolve_field(DexType::get_type("D"),
                            DexString::get_string("f1"),
                            DexType::get_type("I"),
                            FieldSearch::Static) == nullptr);
  EXPECT_TRUE(resolve_field(DexType::get_type("B"),
                            DexString::get_string("f1"),
                            DexType::get_type("I"),
                            FieldSearch::Instance) == fdef);
  EXPECT_TRUE(resolve_field(DexType::get_type("B"),
                            DexString::get_string("f1"),
                            DexType::get_type("I"),
                            FieldSearch::Static) == nullptr);
  EXPECT_TRUE(resolve_field(DexType::get_type("C"),
                            DexString::get_string("f1"),
                            DexType::get_type("I")) == fdef);
  EXPECT_TRUE(resolve_field(DexType::get_type("C"),
                            DexString::get_string("f1"),
                            DexType::get_type("I"),
                            FieldSearch::Static) == nullptr);
  fref = make_field_ref(DexType::get_type("B"), "f1", DexType::get_type("I"));
  EXPECT_FALSE(fref->is_def());
  EXPECT_TRUE(resolve_field(fref) == fdef);
  EXPECT_TRUE(resolve_field(fref, FieldSearch::Instance) == fdef);
  EXPECT_TRUE(resolve_field(fref, FieldSearch::Static) == nullptr);
  fref = make_field_ref(DexType::get_type("C"), "f1", DexType::get_type("I"));
  EXPECT_FALSE(fref->is_def());
  EXPECT_TRUE(resolve_field(fref) == fdef);
  EXPECT_TRUE(resolve_field(fref, FieldSearch::Instance) == fdef);
  EXPECT_TRUE(resolve_field(fref, FieldSearch::Static) == nullptr);

  // different cases for static String B.f2
  fdef =
      DexField::get_field(DexType::get_type("B"), DexString::get_string("f2"),
                          DexType::get_type("Ljava/lang/String;"));
  EXPECT_TRUE(fdef != nullptr && fdef->is_def());
  fref = make_field_ref(DexType::get_type("A"), "f2",
                        DexType::get_type("Ljava/lang/String;"));
  EXPECT_FALSE(fref->is_def());
  EXPECT_TRUE(resolve_field(fref) == nullptr);
  EXPECT_TRUE(resolve_field(fref, FieldSearch::Instance) == nullptr);
  EXPECT_TRUE(resolve_field(fref, FieldSearch::Static) == nullptr);
  fref = make_field_ref(DexType::get_type("B"), "f2",
                        DexType::get_type("Ljava/lang/String;"));
  EXPECT_TRUE(fref->is_def());
  EXPECT_TRUE(resolve_field(fref) == fdef);
  EXPECT_TRUE(resolve_field(fref, FieldSearch::Instance) == fdef);
  fref = make_field_ref(DexType::get_type("C"), "f2",
                        DexType::get_type("Ljava/lang/String;"));
  EXPECT_FALSE(fref->is_def());
  EXPECT_TRUE(resolve_field(fref) == fdef);
  EXPECT_TRUE(resolve_field(fref, FieldSearch::Static) == fdef);
  EXPECT_TRUE(resolve_field(fref, FieldSearch::Instance) == nullptr);

  // different cases for D.f
  fdef = DexField::get_field(DexType::get_type("D"), DexString::get_string("f"),
                             DexType::get_type("A"));
  EXPECT_TRUE(fdef != nullptr && fdef->is_def());
  EXPECT_TRUE(resolve_field(fdef) == fdef);
  EXPECT_TRUE(resolve_field(fdef, FieldSearch::Instance) == fdef);

  // interface final field
  fdef = DexField::get_field(DexType::get_type("Intf"),
                             DexString::get_string("fin_f"),
                             DexType::get_type("I"));
  EXPECT_TRUE(fdef != nullptr && fdef->is_def());
  EXPECT_TRUE(resolve_field(fdef) == fdef);
  EXPECT_TRUE(resolve_field(fdef, FieldSearch::Static) == fdef);
  fref =
      make_field_ref(DexType::get_type("B"), "fin_f", DexType::get_type("I"));
  EXPECT_FALSE(fref->is_def());
  EXPECT_TRUE(resolve_field(fref) == fdef);
  EXPECT_TRUE(resolve_field(fref, FieldSearch::Static) == fdef);
  EXPECT_TRUE(resolve_field(fref, FieldSearch::Instance) == nullptr);
  fref =
      make_field_ref(DexType::get_type("C"), "fin_f", DexType::get_type("I"));
  EXPECT_FALSE(fref->is_def());
  EXPECT_TRUE(resolve_field(fref) == fdef);
  EXPECT_TRUE(resolve_field(fref, FieldSearch::Static) == fdef);
  EXPECT_TRUE(resolve_field(fref, FieldSearch::Instance) == nullptr);

  // random non existent field
  fdef =
      DexField::make_field(DexType::get_type("U"), DexString::get_string("f"),
                           DexType::get_type("I"));
  EXPECT_FALSE(fdef->is_def());
  EXPECT_TRUE(resolve_field(fdef) == nullptr);
  EXPECT_TRUE(resolve_field(fdef, FieldSearch::Instance) == nullptr);
  EXPECT_TRUE(resolve_field(fdef, FieldSearch::Static) == nullptr);
  EXPECT_TRUE(resolve_field(DexType::get_type("E"),
                            DexString::get_string("f1"),
                            DexType::get_type("I"),
                            FieldSearch::Static) == nullptr);
  EXPECT_TRUE(resolve_field(DexType::get_type("E"),
                            DexString::get_string("f1"),
                            DexType::get_type("Ljava/lang/String;"),
                            FieldSearch::Instance) == nullptr);
  EXPECT_TRUE(resolve_field(DexType::get_type("E"),
                            DexString::get_string("f1"),
                            DexType::get_type("I")) == nullptr);
}

TEST_F(ResolverTest, ResolveMethod) {
  create_method_scope();

  auto* a_method = DexMethod::get_method("A.method:()V");
  EXPECT_TRUE(a_method != nullptr && a_method->is_def());

  auto* b_method = DexMethod::get_method("B.method:()V");
  EXPECT_TRUE(b_method != nullptr && b_method->is_def());
  auto* b_surprise = DexMethod::get_method("B.surprise:()V");
  EXPECT_TRUE(b_surprise != nullptr && b_surprise->is_def());

  auto* c_method = DexMethod::get_method("C.method:()V");
  EXPECT_TRUE(c_method != nullptr && !c_method->is_def());
  auto* c_surprise = DexMethod::get_method("C.surprise:()V");
  EXPECT_TRUE(c_surprise != nullptr && c_surprise->is_def());

  auto* d_method = DexMethod::get_method("D.method:()V");
  EXPECT_TRUE(d_method != nullptr && d_method->is_def());

  auto* a_method_def = a_method->as_def();
  auto* b_method_def = b_method->as_def();
  auto* c_surprise_def = c_surprise->as_def();
  auto* d_method_def = d_method->as_def();

  EXPECT_TRUE(resolve_method_deprecated(a_method, MethodSearch::Direct) ==
              a_method);
  EXPECT_TRUE(resolve_method_deprecated(a_method, MethodSearch::Static) ==
              a_method);
  EXPECT_TRUE(resolve_method_deprecated(a_method, MethodSearch::Virtual) ==
              a_method);
  EXPECT_TRUE(resolve_method_deprecated(a_method, MethodSearch::Any) ==
              a_method);
  EXPECT_TRUE(resolve_method_deprecated(a_method, MethodSearch::Interface) ==
              a_method);

  EXPECT_TRUE(resolve_method_deprecated(b_method, MethodSearch::Direct) ==
              b_method);
  EXPECT_TRUE(resolve_method_deprecated(b_method, MethodSearch::Static) ==
              b_method);
  EXPECT_TRUE(resolve_method_deprecated(b_method, MethodSearch::Virtual) ==
              b_method);
  EXPECT_TRUE(resolve_method_deprecated(b_method, MethodSearch::Any) ==
              b_method);
  EXPECT_TRUE(resolve_method_deprecated(b_method, MethodSearch::Interface) ==
              b_method);

  EXPECT_TRUE(resolve_method_deprecated(c_method, MethodSearch::Direct) ==
              nullptr);
  EXPECT_TRUE(resolve_method_deprecated(c_method, MethodSearch::Static) ==
              nullptr);
  EXPECT_TRUE(resolve_method_deprecated(c_method, MethodSearch::Virtual) ==
              b_method);
  EXPECT_TRUE(resolve_method_deprecated(c_method, MethodSearch::Any) ==
              b_method);

  EXPECT_TRUE(resolve_method_deprecated(d_method, MethodSearch::Direct) ==
              d_method);
  EXPECT_TRUE(resolve_method_deprecated(d_method, MethodSearch::Static) ==
              d_method);
  EXPECT_TRUE(resolve_method_deprecated(d_method, MethodSearch::Virtual) ==
              d_method);
  EXPECT_TRUE(resolve_method_deprecated(d_method, MethodSearch::Any) ==
              d_method);
  EXPECT_TRUE(resolve_method_deprecated(d_method, MethodSearch::Interface) ==
              d_method);

  // Super class of A doesn't have such method.
  EXPECT_TRUE(resolve_method_deprecated(a_method, MethodSearch::Super,
                                        a_method_def) == nullptr);
  EXPECT_TRUE(
      resolve_method_deprecated(type_class(a_method->get_class()),
                                a_method->get_name(), a_method->get_proto(),
                                MethodSearch::Super, a_method_def) == nullptr);
  // A is an interface, B cannot use invoke-super on method def in A.
  EXPECT_TRUE(resolve_method_deprecated(b_method, MethodSearch::Super,
                                        b_method_def) == nullptr);
  EXPECT_TRUE(
      resolve_method_deprecated(type_class(b_method->get_class()),
                                b_method->get_name(), b_method->get_proto(),
                                MethodSearch::Super, b_method_def) == nullptr);
  // Generally class in the method ref doesn't matter.
  EXPECT_TRUE(resolve_method_deprecated(a_method, MethodSearch::Super,
                                        d_method_def) == b_method);
  EXPECT_TRUE(
      resolve_method_deprecated(type_class(a_method->get_class()),
                                a_method->get_name(), a_method->get_proto(),
                                MethodSearch::Super, d_method_def) == b_method);
  EXPECT_TRUE(resolve_method_deprecated(b_method, MethodSearch::Super,
                                        d_method_def) == b_method);
  EXPECT_TRUE(
      resolve_method_deprecated(type_class(b_method->get_class()),
                                b_method->get_name(), b_method->get_proto(),
                                MethodSearch::Super, d_method_def) == b_method);
  EXPECT_TRUE(resolve_method_deprecated(d_method, MethodSearch::Super,
                                        d_method_def) == b_method);
  EXPECT_TRUE(
      resolve_method_deprecated(type_class(d_method->get_class()),
                                d_method->get_name(), d_method->get_proto(),
                                MethodSearch::Super, d_method_def) == b_method);
  // Super search doesn't consider static methods
  EXPECT_TRUE(resolve_method_deprecated(c_surprise, MethodSearch::Super,
                                        c_surprise_def) == nullptr);

  MethodRefCache ref_cache;
  EXPECT_TRUE(resolve_method_deprecated(c_method, MethodSearch::Direct,
                                        ref_cache) == nullptr);
  EXPECT_TRUE(resolve_method_deprecated(c_method, MethodSearch::Static,
                                        ref_cache) == nullptr);
  EXPECT_TRUE(resolve_method_deprecated(c_method, MethodSearch::Virtual,
                                        ref_cache) == b_method);
  EXPECT_TRUE(resolve_method_deprecated(c_method, MethodSearch::Any,
                                        ref_cache) == b_method);

  auto* e_method = DexMethod::get_method("E.method:()V");
  EXPECT_TRUE(e_method != nullptr && e_method->is_def());

  auto* f_method = DexMethod::get_method("F.method:()V");
  EXPECT_TRUE(f_method != nullptr && !f_method->is_def());

  auto* g_method = DexMethod::get_method("G.method:()V");
  EXPECT_TRUE(g_method != nullptr && !g_method->is_def());

  auto* h_method = DexMethod::get_method("H.method:()V");
  EXPECT_TRUE(h_method != nullptr && h_method->is_def());

  EXPECT_TRUE(resolve_method_deprecated(e_method, MethodSearch::Direct) ==
              e_method);
  EXPECT_TRUE(resolve_method_deprecated(h_method, MethodSearch::Virtual) ==
              h_method);
  EXPECT_TRUE(resolve_method_deprecated(h_method, MethodSearch::Any) ==
              h_method);
  EXPECT_TRUE(resolve_method_deprecated(f_method, MethodSearch::Virtual) ==
              nullptr);
  EXPECT_TRUE(resolve_method_deprecated(g_method, MethodSearch::Virtual) ==
              nullptr);
  EXPECT_TRUE(resolve_method_deprecated(
                  f_method, MethodSearch::InterfaceVirtual) == e_method);
  EXPECT_TRUE(resolve_method_deprecated(
                  g_method, MethodSearch::InterfaceVirtual) == e_method);
}

TEST_F(ResolverTest, HasSignatureCollision) {
  auto* string_proto = DexProto::make_proto(type::java_lang_String(),
                                            DexTypeList::make_type_list({}));
  auto add_method = [](ClassCreator& creator, const std::string& signature,
                       DexAccessFlags access, bool is_virtual) {
    auto* method =
        DexMethod::make_method(signature)->make_concrete(access, is_virtual);
    creator.add_method(method);
    return method;
  };
  auto make_interface = [&](const char* name, const char* method_name,
                            DexAccessFlags access,
                            const std::vector<DexClass*>& super_intfs) {
    ClassCreator creator(DexType::make_type(name));
    creator.set_super(type::java_lang_Object());
    creator.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
    for (auto* super_intf : super_intfs) {
      creator.add_interface(super_intf->get_type());
    }
    add_method(creator,
               std::string(name) + "." + method_name + ":()Ljava/lang/String;",
               access, true);
    return creator.create();
  };
  const auto abstract = ACC_PUBLIC | ACC_ABSTRACT;
  // `I` extends `I2`, which extends `I3` with a default method.
  auto* deep_intf = make_interface("LI3;", "from_deep_default", ACC_PUBLIC, {});
  auto* middle_intf =
      make_interface("LI2;", "from_middle_interface", abstract, {deep_intf});
  auto* intf = make_interface("LI;", "from_interface", abstract, {middle_intf});
  // `Base` implements `J` without declaring its method.
  auto* super_intf =
      make_interface("LJ;", "from_super_interface", abstract, {});
  // The subclass `D` implements `K`, which extends `K2`.
  auto* sub_super_intf =
      make_interface("LK2;", "from_subclass_super_interface", abstract, {});
  auto* sub_intf = make_interface("LK;", "from_subclass_interface", abstract,
                                  {sub_super_intf});

  ClassCreator base_creator(DexType::make_type("LBase;"));
  base_creator.set_super(type::java_lang_Object());
  base_creator.add_interface(super_intf->get_type());
  add_method(base_creator, "LBase;.inherited_static:()Ljava/lang/String;",
             ACC_PUBLIC | ACC_STATIC, false);
  add_method(base_creator, "LBase;.inherited_virtual:()Ljava/lang/String;",
             ACC_PUBLIC, true);
  add_method(base_creator, "LBase;.static_hidden:()Ljava/lang/String;",
             ACC_PUBLIC | ACC_STATIC, false);
  auto* base = base_creator.create();

  ClassCreator creator(DexType::make_type("LC;"));
  creator.set_super(base->get_type());
  creator.add_interface(intf->get_type());
  auto add_candidate = [&](const std::string& name) {
    return add_method(creator, "LC;." + name + ":()Ljava/lang/Object;",
                      ACC_PUBLIC, true);
  };
  auto add_static_candidate = [&](const std::string& name) {
    return add_method(creator, "LC;." + name + ":()Ljava/lang/Object;",
                      ACC_PUBLIC | ACC_STATIC, false);
  };
  auto* no_collision = add_candidate("no_collision");
  auto* own = add_candidate("own");
  add_method(creator, "LC;.own:()Ljava/lang/String;", ACC_PUBLIC | ACC_STATIC,
             false);
  auto* interned = add_candidate("interned");
  DexMethod::make_method("LC;.interned:()Ljava/lang/String;");
  auto* inherited_static = add_candidate("inherited_static");
  auto* inherited_virtual = add_candidate("inherited_virtual");
  auto* from_interface = add_candidate("from_interface");
  auto* from_super_interface = add_candidate("from_super_interface");
  auto* in_subclass = add_candidate("in_subclass");
  auto* referenced_on_subclass = add_candidate("referenced_on_subclass");
  auto* from_subclass_interface = add_candidate("from_subclass_interface");
  auto* from_middle_interface = add_candidate("from_middle_interface");
  auto* from_deep_default = add_candidate("from_deep_default");
  auto* from_subclass_super_interface =
      add_candidate("from_subclass_super_interface");
  auto* static_own = add_static_candidate("static_own");
  add_method(creator, "LC;.static_own:()Ljava/lang/String;",
             ACC_PUBLIC | ACC_STATIC, false);
  auto* static_hidden = add_static_candidate("static_hidden");
  auto* static_in_subclass = add_static_candidate("static_in_subclass");
  auto* cls = creator.create();

  ClassCreator sub_creator(DexType::make_type("LD;"));
  sub_creator.set_super(cls->get_type());
  sub_creator.add_interface(sub_intf->get_type());
  add_method(sub_creator, "LD;.in_subclass:()Ljava/lang/String;", ACC_PUBLIC,
             true);
  add_method(sub_creator, "LD;.static_in_subclass:()Ljava/lang/String;",
             ACC_PUBLIC, true);
  auto* sub = sub_creator.create();
  DexMethod::make_method("LD;.referenced_on_subclass:()Ljava/lang/String;");

  // Interface methods: `Impl` implements `L` and declares the new signature;
  // `Derived` implements `L` and inherits it from `Unrelated`.
  ClassCreator l_creator(DexType::make_type("LL;"));
  l_creator.set_super(type::java_lang_Object());
  l_creator.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  auto* in_implementor = add_method(
      l_creator, "LL;.in_implementor:()Ljava/lang/Object;", abstract, true);
  auto* inherited_by_implementor =
      add_method(l_creator, "LL;.inherited_by_implementor:()Ljava/lang/Object;",
                 abstract, true);
  auto* l_intf = l_creator.create();
  // `N` extends `M`, which declares the new signature; `N` has no implementor.
  auto* m_intf = make_interface("LM;", "from_super_of_interface", abstract, {});
  ClassCreator n_creator(DexType::make_type("LN;"));
  n_creator.set_super(type::java_lang_Object());
  n_creator.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  n_creator.add_interface(m_intf->get_type());
  auto* from_super_of_interface =
      add_method(n_creator, "LN;.from_super_of_interface:()Ljava/lang/Object;",
                 abstract, true);
  auto* n_intf = n_creator.create();
  // `Q` extends `P` and declares the new signature.
  ClassCreator p_creator(DexType::make_type("LP;"));
  p_creator.set_super(type::java_lang_Object());
  p_creator.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  auto* in_subinterface = add_method(
      p_creator, "LP;.in_subinterface:()Ljava/lang/Object;", abstract, true);
  auto* p_intf = p_creator.create();
  auto* q_intf = make_interface("LQ;", "in_subinterface", abstract, {p_intf});
  ClassCreator impl_creator(DexType::make_type("LImpl;"));
  impl_creator.set_super(type::java_lang_Object());
  impl_creator.add_interface(l_intf->get_type());
  add_method(impl_creator, "LImpl;.in_implementor:()Ljava/lang/String;",
             ACC_PUBLIC, true);
  auto* impl = impl_creator.create();
  ClassCreator unrelated_creator(DexType::make_type("LUnrelated;"));
  unrelated_creator.set_super(type::java_lang_Object());
  add_method(unrelated_creator,
             "LUnrelated;.inherited_by_implementor:()Ljava/lang/String;",
             ACC_PUBLIC, true);
  auto* unrelated = unrelated_creator.create();
  ClassCreator derived_creator(DexType::make_type("LDerived;"));
  derived_creator.set_super(unrelated->get_type());
  derived_creator.add_interface(l_intf->get_type());
  auto* derived = derived_creator.create();

  SubtypeMaps subtype_maps =
      build_subtype_maps({base, cls, sub, l_intf, n_intf, p_intf, q_intf, impl,
                          unrelated, derived});

  EXPECT_FALSE(
      has_signature_collision(subtype_maps, no_collision, string_proto));
  EXPECT_TRUE(has_signature_collision(subtype_maps, own, string_proto));
  // A reference on the method's own class holds the key it would take.
  EXPECT_TRUE(has_signature_collision(subtype_maps, interned, string_proto));
  EXPECT_TRUE(
      has_signature_collision(subtype_maps, inherited_static, string_proto));
  EXPECT_TRUE(
      has_signature_collision(subtype_maps, inherited_virtual, string_proto));
  EXPECT_TRUE(
      has_signature_collision(subtype_maps, from_interface, string_proto));
  EXPECT_TRUE(has_signature_collision(subtype_maps, from_super_interface,
                                      string_proto));
  EXPECT_TRUE(has_signature_collision(subtype_maps, in_subclass, string_proto));
  // References are resolved to their definitions, so a reference that no
  // definition backs does not count.
  EXPECT_FALSE(has_signature_collision(subtype_maps, referenced_on_subclass,
                                       string_proto));
  EXPECT_TRUE(has_signature_collision(subtype_maps, from_subclass_interface,
                                      string_proto));
  EXPECT_TRUE(has_signature_collision(subtype_maps, from_middle_interface,
                                      string_proto));
  EXPECT_TRUE(
      has_signature_collision(subtype_maps, from_deep_default, string_proto));
  EXPECT_TRUE(has_signature_collision(
      subtype_maps, from_subclass_super_interface, string_proto));
  EXPECT_TRUE(
      has_signature_collision(subtype_maps, in_implementor, string_proto));
  EXPECT_TRUE(has_signature_collision(subtype_maps, inherited_by_implementor,
                                      string_proto));
  EXPECT_TRUE(has_signature_collision(subtype_maps, from_super_of_interface,
                                      string_proto));
  EXPECT_TRUE(
      has_signature_collision(subtype_maps, in_subinterface, string_proto));
  // Static methods are not inherited, so only their own class counts.
  EXPECT_TRUE(has_signature_collision(subtype_maps, static_own, string_proto));
  EXPECT_FALSE(
      has_signature_collision(subtype_maps, static_hidden, string_proto));
  EXPECT_FALSE(
      has_signature_collision(subtype_maps, static_in_subclass, string_proto));
}

TEST_F(ResolverTest, HasSignatureCollisionForConstructors) {
  // `Sub.<init>(I)` taking `(Impl)` collides only with a constructor of `Sub`
  // itself, not with the ones of its superclass and subclass.
  auto make_class = [](const char* name, DexType* super,
                       const std::vector<const char*>& ctors) {
    ClassCreator creator(DexType::make_type(name));
    creator.set_super(super);
    for (const auto* ctor : ctors) {
      creator.add_method(
          DexMethod::make_method(std::string(name) + ".<init>:" + ctor)
              ->make_concrete(ACC_PUBLIC | ACC_CONSTRUCTOR, false));
    }
    return creator.create();
  };
  auto* base = make_class("LBase;", type::java_lang_Object(), {"(LImpl;)V"});
  auto* sub = make_class("LSub;", base->get_type(), {"(LI;)V"});
  auto* subsub = make_class("LSubSub;", sub->get_type(), {"(LImpl;)V"});
  auto* other =
      make_class("LOther;", type::java_lang_Object(), {"(LI;)V", "(LImpl;)V"});
  SubtypeMaps subtype_maps = build_subtype_maps({base, sub, subsub, other});
  auto* impl_proto = DexProto::make_proto(
      type::_void(),
      DexTypeList::make_type_list({DexType::make_type("LImpl;")}));

  EXPECT_FALSE(has_signature_collision(
      subtype_maps, sub->get_dmethods().front(), impl_proto));
  auto* other_ctor = DexMethod::get_method("LOther;.<init>:(LI;)V")->as_def();
  EXPECT_TRUE(has_signature_collision(subtype_maps, other_ctor, impl_proto));
}

TEST_F(ResolverTest, HasSignatureCollisionWithUndefinedInterface) {
  // `C` implements `Undefined`, which has no definition.
  ClassCreator creator(DexType::make_type("LC;"));
  creator.set_super(type::java_lang_Object());
  creator.add_interface(DexType::make_type("LUndefined;"));
  auto* method = DexMethod::make_method("LC;.m:()Ljava/lang/Object;")
                     ->make_concrete(ACC_PUBLIC, true);
  creator.add_method(method);
  auto* cls = creator.create();
  auto* string_proto = DexProto::make_proto(type::java_lang_String(),
                                            DexTypeList::make_type_list({}));

  EXPECT_FALSE(
      has_signature_collision(build_subtype_maps({cls}), method, string_proto));
}
