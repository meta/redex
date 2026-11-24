/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "CheckBreadcrumbs.h"

#include <gtest/gtest.h>

#include "ConfigFiles.h"
#include "Creators.h"
#include "DexClass.h"
#include "DexUtil.h"
#include "IRAssembler.h"
#include "PassManager.h"
#include "RedexException.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"
#include "Walkers.h"

// Create the following hierarchy
//
// package CheckBreadCrumbs;
//
// class no_modifiers {
//   static int no_modifier_field;
//   static void no_modifier_fun() {
//   }
// }
// class A {
//   static public int a_pub_field;
//   static protected int a_pro_field;
//   static private int a_pri_field;
//   static public void a_pub_fun() {
//   }
//   static protected void a_pro_fun() {
//   }
//   static private void a_pri_func() {
//   }
// }
//
// class B extends A {
//   public int call_a_pub_field() {
//     return a_pub_field;
//   }
//   public int call_a_pro_field() {
//     return a_pro_field;
//   }
//   public int call_a_pri_field() {
//     return a_pri_field;
//   };
//   public void call_a_pub_fun() {
//     a_pub_fun();
//   }
//   public void call_a_pro_fun() {
//     a_pro_fun();
//   }
//   public void call_a_pri_func() {
//     a_pri_func();
//   }
// }
//

namespace {

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

std::vector<DexMethod*> call_a_fields_and_methods_methods() {
  auto* call_a_pub_field = assembler::method_from_string(R"(
    (method (public) "LB;.call_a_pub_field:()I"
      (
        (sget "LB;.a_pub_field:I")
        (move-result-pseudo v0)
        (return v0)
      )
    )
  )");

  auto* call_a_pro_field = assembler::method_from_string(R"(
    (method (public) "LB;.call_a_proc_field:()I"
      (
        (sget "LB;.a_pro_field:I")
        (move-result-pseudo v0)
        (return v0)
      )
    )
  )");

  auto* call_a_pri_field = assembler::method_from_string(R"(
    (method (public) "LB;.call_a_pri_field:()I"
      (
        (sget "LB;.a_pri_field:I")
        (move-result-pseudo v0)
        (return v0)
      )
    )
  )");

  auto* call_a_pub_fun = assembler::method_from_string(R"(
    (method (public) "LB;.call_a_pub_fun:()V"
      (
        (invoke-static () "LA;.a_pub_fun:()V")
        (return-void)
      )
    )
  )");

  auto* call_a_pro_fun = assembler::method_from_string(R"(
    (method (public) "LB;.call_a_pro_fun:()V"
      (
        (invoke-static () "LA;.a_pro_fun:()V")
        (return-void)
      )
    )
  )");

  auto* call_a_pri_fun = assembler::method_from_string(R"(
    (method (public) "LB;.call_a_pri_fun:()V"
      (
        (invoke-static () "LA;.a_pri_fun:()V")
        (return-void)
      )
    )
  )");

  return std::vector<DexMethod*>{call_a_pub_field, call_a_pro_field,
                                 call_a_pri_field, call_a_pub_fun,
                                 call_a_pro_fun,   call_a_pri_fun};
}

DexClass* create_class(DexType* type,
                       DexType* super,
                       std::vector<DexMethod*>& methods,
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
  for (const auto& meth : methods) {
    creator.add_method(meth);
  }
  for (const auto& field : fields) {
    creator.add_field(field);
  }
  return creator.create();
}

DexClass* create_class_A() {
  auto* int_t = type::_int();
  auto* a_t = DexType::make_type("LA;");

  std::vector<DexField*> a_fields{
      make_field_def(a_t, "a_pub_field", int_t, ACC_PUBLIC | ACC_STATIC),
      make_field_def(a_t, "a_pro_field", int_t, ACC_PROTECTED | ACC_STATIC),
      make_field_def(a_t, "a_pri_field", int_t, ACC_PRIVATE | ACC_STATIC),
  };
  auto* a_pub_fun = DexMethod::make_method("LA;", "a_pub_fun", "V", {})
                        ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);

  auto* a_pro_fun = DexMethod::make_method("LA;", "a_pro_fun", "V", {})
                        ->make_concrete(ACC_PROTECTED | ACC_STATIC, false);

  auto* a_pri_fun = DexMethod::make_method("LA;", "a_pri_fun", "V", {})
                        ->make_concrete(ACC_PRIVATE | ACC_STATIC, false);
  std::vector<DexMethod*> a_methods{a_pub_fun, a_pro_fun, a_pri_fun};
  return create_class(a_t, type::java_lang_Object(), a_methods, a_fields,
                      ACC_PUBLIC);
}

DexClass* create_class_B(DexType* super) {
  auto* b_t = DexType::make_type("LB;");
  std::vector<DexMethod*> b_methods = call_a_fields_and_methods_methods();
  std::vector<DexField*> b_fields{};
  return create_class(b_t, super, b_methods, b_fields);
}

std::vector<DexClass*> create_classes() {
  std::vector<DexClass*> classes;
  // Create A
  auto* a_t = DexType::make_type("LA;");
  auto* cls_a = create_class_A();
  classes.push_back(cls_a);
  // Create B
  auto* cls_b = create_class_B(a_t);
  classes.push_back(cls_b);
  return classes;
}

class CheckBreadcrumbsTest : public RedexTest {
 public:
  ConfigFiles conf = ConfigFiles(Json::nullValue);

  // Runs the pass on `root_classes`, in the root store, and `module_classes`,
  // in a module store that the root store may not refer to, and returns the
  // report it fails with: of dangling references if there are any, and
  // otherwise of illegal cross-store references.
  static std::string failure_report(
      const std::vector<DexClass*>& root_classes,
      const std::vector<DexClass*>& module_classes) {
    DexMetadata dm_root;
    dm_root.set_id("classes");
    DexStore store_root(dm_root);
    store_root.add_classes(root_classes);
    DexMetadata dm_module;
    dm_module.set_id("Module");
    DexStore store_module(dm_module);
    store_module.add_classes(module_classes);
    std::vector<DexStore> stores;
    stores.emplace_back(std::move(store_root));
    stores.emplace_back(std::move(store_module));

    Json::Value json(Json::objectValue);
    json["CheckBreadcrumbsPass"]["fail"] = true;
    json["CheckBreadcrumbsPass"]["fail_if_illegal_refs"] = true;
    ConfigFiles config(json);
    config.parse_global_config();
    CheckBreadcrumbsPass pass;
    PassManager manager({&pass}, config);
    try {
      manager.run_passes(stores, config);
    } catch (const RedexException& e) {
      return e.what();
    }
    return "";
  }
};

//========== Test Cases ==========
TEST_F(CheckBreadcrumbsTest, AccessValidityTest) {
  std::vector<DexClass*> classes = create_classes();
  DexMetadata dm;
  dm.set_id("classes");
  DexStore store(dm);
  store.add_classes(classes);
  std::vector<DexStore> stores;
  stores.emplace_back(std::move(store));
  auto scope = build_class_scope(stores);
  Breadcrumbs bc(scope, "", stores, conf, "",
                 /* reject_illegal_refs_root_store= */ false,
                 /* only_verify_primary_dex= */ false,
                 /* verify_type_hierarchies= */ false,
                 /* verify_proto_cross_dex= */ false,
                 /* enforce_allowed_violations_file= */ false);
  std::vector<DexMethod*> method_list = call_a_fields_and_methods_methods();
  method_list[0]->get_code()->build_cfg();
  EXPECT_EQ(bc.has_illegal_access(method_list[0]), false);
  method_list[1]->get_code()->build_cfg();
  EXPECT_EQ(bc.has_illegal_access(method_list[1]), false);
  method_list[2]->get_code()->build_cfg();
  EXPECT_EQ(bc.has_illegal_access(method_list[2]), true);
  method_list[3]->get_code()->build_cfg();
  EXPECT_EQ(bc.has_illegal_access(method_list[3]), false);
  method_list[4]->get_code()->build_cfg();
  EXPECT_EQ(bc.has_illegal_access(method_list[4]), false);
  method_list[5]->get_code()->build_cfg();
  EXPECT_EQ(bc.has_illegal_access(method_list[5]), true);
  std::ostringstream expected;
  expected << "Bad methods in class LB;\n"
           << "\ta_pri_fun\n\n"
           << "Bad field refs in method LB;.call_a_pri_field\n"
           << "\ta_pri_field\n\n";
  EXPECT_EQ(expected.str(), bc.get_methods_with_bad_refs());
}

TEST_F(CheckBreadcrumbsTest, CrossStoreValidityTest) {
  std::vector<DexMethod*> empty_method_vec;
  std::vector<DexField*> empty_field_vecc;

  DexMetadata dm_root;
  dm_root.set_id("classes");
  std::vector<std::string> root_deps;
  DexStore store_root(dm_root);
  store_root.add_classes(
      {create_class(DexType::make_type("LClass1;"), type::java_lang_Object(),
                    empty_method_vec, empty_field_vecc)});

  DexMetadata dm_A;
  dm_A.set_id("A");
  std::vector<std::string> A_deps;
  dm_A.set_dependencies({"s_A_B", "s_A_B_C"});
  DexStore store_A(dm_A);
  store_A.add_classes(
      {create_class(DexType::make_type("LClass2;"), type::java_lang_Object(),
                    empty_method_vec, empty_field_vecc)});

  DexMetadata dm_B;
  dm_B.set_id("B");
  dm_B.set_dependencies({"s_A_B", "s_A_B_C", "s_B_C"});
  DexStore store_B(dm_B);
  store_B.add_classes(
      {create_class(DexType::make_type("LClass3;"), type::java_lang_Object(),
                    empty_method_vec, empty_field_vecc)});

  DexMetadata dm_C;
  dm_C.set_id("C");
  dm_C.set_dependencies({"s_A_B_C", "s_B_C"});
  DexStore store_C(dm_C);
  store_C.add_classes(
      {create_class(DexType::make_type("LClass4;"), type::java_lang_Object(),
                    empty_method_vec, empty_field_vecc)});

  DexMetadata dm_s_A_B_C;
  dm_s_A_B_C.set_id("s_A_B_C");
  DexStore store_s_A_B_C(dm_s_A_B_C);
  auto* type_s_A_B_C = DexType::make_type("LSABC;");
  store_s_A_B_C.add_classes(
      {create_class(type_s_A_B_C, type::java_lang_Object(), empty_method_vec,
                    empty_field_vecc)});

  DexMetadata dm_s_A_B;
  dm_s_A_B.set_id("s_A_B");
  DexStore store_s_A_B(dm_s_A_B);
  auto* type_s_A_B = DexType::make_type("LSAB;");
  store_s_A_B.add_classes({create_class(type_s_A_B, type_s_A_B_C,
                                        empty_method_vec, empty_field_vecc)});

  DexMetadata dm_s_B_C;
  dm_s_B_C.set_id("s_B_C");
  DexStore store_s_B_C(dm_s_B_C);
  auto* type_s_B_C = DexType::make_type("LSBC;");
  store_s_B_C.add_classes({create_class(type_s_B_C, type_s_A_B,
                                        empty_method_vec, empty_field_vecc)});

  std::vector<DexStore> stores;
  stores.emplace_back(std::move(store_root));
  stores.emplace_back(std::move(store_A));
  stores.emplace_back(std::move(store_B));
  stores.emplace_back(std::move(store_C));
  stores.emplace_back(std::move(store_s_A_B));
  stores.emplace_back(std::move(store_s_A_B_C));
  stores.emplace_back(std::move(store_s_B_C));

  auto scope = build_class_scope(stores);

  Breadcrumbs bc_shared(scope,
                        "",
                        stores,
                        conf,
                        "s_",
                        /* reject_illegal_refs_root_store= */ false,
                        /* only_verify_primary_dex= */ false,
                        /* verify_type_hierarchies= */ false,
                        /* verify_proto_cross_dex= */ false,
                        /* enforce_allowed_violations_file= */ false);
  EXPECT_EQ(bc_shared.is_illegal_cross_store(type_s_A_B, type_s_A_B_C).first,
            false);
  EXPECT_EQ(bc_shared.is_illegal_cross_store(type_s_B_C, type_s_A_B).first,
            true);
  EXPECT_EQ(bc_shared.is_illegal_cross_store(type_s_B_C, type_s_A_B).second,
            type_s_A_B);

  // standard behavior
  Breadcrumbs bc_standard(scope,
                          "",
                          stores,
                          conf,
                          "",
                          /* reject_illegal_refs_root_store= */ false,
                          /* only_verify_primary_dex= */ false,
                          /* verify_type_hierarchies= */ false,
                          /* verify_proto_cross_dex= */ false,
                          /* enforce_allowed_violations_file= */ false);
  EXPECT_EQ(bc_standard.is_illegal_cross_store(type_s_A_B, type_s_A_B_C).first,
            true);
  EXPECT_EQ(bc_standard.is_illegal_cross_store(type_s_A_B, type_s_A_B_C).second,
            type_s_A_B_C);
}

// An illegal reference through a type operand names the store of that type.
TEST_F(CheckBreadcrumbsTest, IllegalTypeRefNamesStoreOfType) {
  std::vector<DexMethod*> no_methods;
  std::vector<DexField*> no_fields;
  auto* other = create_class(DexType::make_type("LOther;"),
                             type::java_lang_Object(), no_methods, no_fields);
  std::vector<DexMethod*> user_methods{assembler::method_from_string(R"(
    (method (public static) "LUser;.use:()V"
      (
        (const-class "LOther;")
        (move-result-pseudo-object v0)
        (return-void)
      )
    )
  )")};
  auto* user = create_class(DexType::make_type("LUser;"),
                            type::java_lang_Object(), user_methods, no_fields);

  auto report = failure_report({user}, {other});
  EXPECT_NE(report.find("CONST_CLASS LOther; (Module1)  By  LOther; (Module1)"),
            std::string::npos)
      << report;
}

// An illegal reference to the type of a field names the store of that type.
TEST_F(CheckBreadcrumbsTest, IllegalFieldTypeRefNamesStoreOfType) {
  std::vector<DexMethod*> no_methods;
  std::vector<DexField*> no_fields;
  auto* other_t = DexType::make_type("LOther;");
  auto* other =
      create_class(other_t, type::java_lang_Object(), no_methods, no_fields);
  auto* holder_t = DexType::make_type("LHolder;");
  std::vector<DexField*> holder_fields{
      make_field_def(holder_t, "f", other_t, ACC_PUBLIC | ACC_STATIC)};
  auto* holder = create_class(holder_t, type::java_lang_Object(), no_methods,
                              holder_fields);
  std::vector<DexMethod*> user_methods{assembler::method_from_string(R"(
    (method (public static) "LUser;.use:()V"
      (
        (sget-object "LHolder;.f:LOther;")
        (move-result-pseudo-object v0)
        (return-void)
      )
    )
  )")};
  auto* user = create_class(DexType::make_type("LUser;"),
                            type::java_lang_Object(), user_methods, no_fields);

  auto report = failure_report({user, holder}, {other});
  EXPECT_NE(report.find("Illegal field type refs in method  (classes)\n"
                        "\tSGET_OBJECT LHolder;.f:LOther; (Module1)  By  "
                        "LOther; (Module1)\n"),
            std::string::npos)
      << report;
}

DexClass* create_class_with_methods(const char* name,
                                    std::vector<DexMethod*> methods) {
  std::vector<DexField*> no_fields;
  return create_class(DexType::make_type(name), type::java_lang_Object(),
                      methods, no_fields);
}

// The class `LOther;`, in the module store, with a static method `m()` and a
// static field `f`.
DexClass* create_module_class() {
  auto* other_t = DexType::make_type("LOther;");
  std::vector<DexField*> fields{
      make_field_def(other_t, "f", type::_int(), ACC_PUBLIC | ACC_STATIC)};
  std::vector<DexMethod*> methods{
      DexMethod::make_method("LOther;.m:()V")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, false)};
  return create_class(other_t, type::java_lang_Object(), methods, fields);
}

// `LUser;.use:()V`, in the root store, with `code` as its body.
DexClass* create_user_class(const std::string& code) {
  return create_class_with_methods(
      "LUser;",
      {DexMethod::make_method("LUser;.use:()V")
           ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                           assembler::ircode_from_string(code), false)});
}

// The method or field that a method handle names is referenced like the one
// an invoke or field instruction names.
TEST_F(CheckBreadcrumbsTest, MethodHandleOfModuleMethodIsIllegal) {
  auto report = failure_report({create_user_class(R"((
    (const-method-handle invoke-static "LOther;.m:()V")
    (move-result-pseudo-object v0)
    (return-void)
  ))")},
                               {create_module_class()});
  EXPECT_NE(report.find("Illegal method call in method  (classes)\n"
                        "\tCONST_METHOD_HANDLE "),
            std::string::npos)
      << report;
  EXPECT_NE(report.find("LOther;.m:()V (Module1)  By  LOther; (Module1)\n"),
            std::string::npos)
      << report;
}

TEST_F(CheckBreadcrumbsTest, MethodHandleOfModuleFieldIsIllegal) {
  auto report = failure_report({create_user_class(R"((
    (const-method-handle static-get "LOther;.f:I")
    (move-result-pseudo-object v0)
    (return-void)
  ))")},
                               {create_module_class()});
  EXPECT_NE(report.find("Illegal field class refs in method  (classes)\n"
                        "\tCONST_METHOD_HANDLE "),
            std::string::npos)
      << report;
  EXPECT_NE(report.find("LOther;.f:I (Module1)  By  LOther; (Module1)\n"),
            std::string::npos)
      << report;
}

// So are the types that a method type names.
TEST_F(CheckBreadcrumbsTest, MethodTypeOfModuleTypeIsIllegal) {
  auto report = failure_report({create_user_class(R"((
    (const-method-type "(LOther;)V")
    (move-result-pseudo-object v0)
    (return-void)
  ))")},
                               {create_module_class()});
  EXPECT_NE(report.find("Illegal type refs in method  (classes)\n"
                        "\tCONST_METHOD_TYPE (LOther;)V (Module1)  By  "
                        "LOther; (Module1)\n"),
            std::string::npos)
      << report;
}

// And the bootstrap method of a call site.
TEST_F(CheckBreadcrumbsTest, CallSiteOfModuleBootstrapMethodIsIllegal) {
  auto* user = create_user_class(R"((
    (invoke-static () "LUser;.placeholder:()V")
    (return-void)
  ))");
  redex::make_invoke_custom(user->get_dmethods().front()->get_code(), "run",
                            "()V");
  auto report = failure_report(
      {user}, {create_module_class(), create_class_with_methods("LBoot;", {})});
  EXPECT_NE(report.find("Illegal method call in method  (classes)\n"
                        "\tINVOKE_CUSTOM "),
            std::string::npos)
      << report;
  EXPECT_NE(report.find("(Module1)  By  LBoot; (Module1)\n"), std::string::npos)
      << report;
}

// A method handle of a method of a class that was deleted is a dangling
// reference.
TEST_F(CheckBreadcrumbsTest, MethodHandleOfDeletedClassIsDangling) {
  // Defined, but in no store.
  create_class_with_methods(
      "LGone;", {DexMethod::make_method("LGone;.m:()V")
                     ->make_concrete(ACC_PUBLIC | ACC_STATIC, false)});
  auto report = failure_report({create_user_class(R"((
    (const-method-handle invoke-static "LGone;.m:()V")
    (move-result-pseudo-object v0)
    (return-void)
  ))")},
                               {});
  EXPECT_NE(report.find("Reference to deleted type LGone; in instruction "
                        "CONST_METHOD_HANDLE"),
            std::string::npos)
      << report;
}

// A method handle of a private method of another class is an illegal access.
TEST_F(CheckBreadcrumbsTest, MethodHandleOfPrivateMethodIsIllegalAccess) {
  std::vector<DexClass*> classes = create_classes();
  DexMetadata dm;
  dm.set_id("classes");
  DexStore store(dm);
  store.add_classes(classes);
  std::vector<DexStore> stores;
  stores.emplace_back(std::move(store));
  auto scope = build_class_scope(stores);
  Breadcrumbs bc(scope, "", stores, conf, "",
                 /* reject_illegal_refs_root_store= */ false,
                 /* only_verify_primary_dex= */ false,
                 /* verify_type_hierarchies= */ false,
                 /* verify_proto_cross_dex= */ false,
                 /* enforce_allowed_violations_file= */ false);
  auto* method = assembler::method_from_string(R"(
    (method (public) "LB;.handle_a_pri_fun:()V"
      (
        (const-method-handle invoke-static "LA;.a_pri_fun:()V")
        (move-result-pseudo-object v0)
        (return-void)
      )
    )
  )");
  method->get_code()->build_cfg();
  EXPECT_TRUE(bc.has_illegal_access(method));
}
} // namespace
