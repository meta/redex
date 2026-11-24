/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "Creators.h"
#include "DexAnnotation.h"
#include "DexMethodHandle.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "PackagePrivatePreprocessor.h"
#include "PassManager.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"

namespace {

DexClass* make_class(std::string_view name,
                     DexType* super = type::java_lang_Object()) {
  ClassCreator cc(DexType::make_type(name));
  cc.set_super(super);
  cc.set_access(ACC_PUBLIC);
  return cc.create();
}

DexMethod* add_method(DexClass* cls,
                      const std::string& spec,
                      DexAccessFlags access,
                      bool is_virtual,
                      const std::string& code) {
  auto* m = DexMethod::make_method(spec)->make_concrete(
      access, assembler::ircode_from_string(code), is_virtual);
  cls->add_method(m);
  return m;
}

void run_package_private_preprocessor(const std::vector<DexClass*>& classes) {
  PackagePrivatePreprocessorPass pass;
  PassManager manager({&pass});
  ConfigFiles config(Json::nullValue);
  config.parse_global_config();
  DexStore store("classes");
  store.add_classes(classes);
  std::vector<DexStore> stores;
  stores.emplace_back(std::move(store));
  manager.run_passes(stores, config);
}

// Loads `handle`, a tool-generated method handle, and calls it with the
// call-site prototype `proto` and the arguments in `args`.
std::string call_handle_code(const std::string& load_params,
                             const std::string& handle,
                             const std::string& args,
                             const std::string& proto) {
  return "(" + load_params + "(const-method-handle " + handle +
         ")"
         "(move-result-pseudo-object v0)"
         "(invoke-polymorphic (v0" +
         args +
         ") \"Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/"
         "Object;)Ljava/lang/Object;\" \"" +
         proto +
         "\")"
         "(return-void))";
}

const DexMethodHandle* get_method_handle(const DexMethod* method) {
  for (const auto& mie : InstructionIterable(method->get_code())) {
    if (mie.insn->has_methodhandle()) {
      return mie.insn->get_methodhandle();
    }
  }
  return nullptr;
}

constexpr const char* kReturnVoid = "((return-void))";

} // namespace

class PackagePrivatePreprocessorMethodHandleTest : public RedexTest {};

// A method handle in the same package calls the package-private method, which
// is then made public, as for an invoke, so that later passes may rename the
// packages.
TEST_F(PackagePrivatePreprocessorMethodHandleTest,
       method_called_by_handle_is_made_public) {
  auto* a = make_class("Lp/A;");
  auto* m = add_method(a, "Lp/A;.m:()V", ACC_STATIC, false, kReturnVoid);
  auto* b = make_class("Lp/B;");
  add_method(b, "Lp/B;.use:()V", ACC_PUBLIC | ACC_STATIC, false,
             call_handle_code("", R"(invoke-static "Lp/A;.m:()V")", "", "()V"));

  run_package_private_preprocessor({a, b});

  EXPECT_TRUE(is_public(m));
}

// The same holds for a field that a method handle reads.
TEST_F(PackagePrivatePreprocessorMethodHandleTest,
       field_read_by_handle_is_made_public) {
  auto* a = make_class("Lp/A;");
  auto* f = DexField::make_field("Lp/A;.f:I")->make_concrete(ACC_STATIC);
  a->add_field(f);
  auto* b = make_class("Lp/B;");
  add_method(b, "Lp/B;.use:()V", ACC_PUBLIC | ACC_STATIC, false,
             call_handle_code("", R"(static-get "Lp/A;.f:I")", "", "()I"));

  run_package_private_preprocessor({a, b});

  EXPECT_TRUE(is_public(f));
}

// A static-get method handle of `Lp/B;.x:I` reads the static field `Lp/A;.x`,
// not the instance field `Lp/B;.x` that it names, so `Lp/A;.x` is made public.
TEST_F(PackagePrivatePreprocessorMethodHandleTest,
       field_of_handle_resolves_by_its_kind) {
  auto* a = make_class("Lp/A;");
  auto* a_x = DexField::make_field("Lp/A;.x:I")->make_concrete(ACC_STATIC);
  a->add_field(a_x);
  auto* b = make_class("Lp/B;", a->get_type());
  b->add_field(DexField::make_field("Lp/B;.x:I")->make_concrete(ACC_PUBLIC));
  auto* user = make_class("Lp/User;");
  add_method(user, "Lp/User;.use:()V", ACC_PUBLIC | ACC_STATIC, false,
             call_handle_code("", R"(static-get "Lp/B;.x:I")", "", "()I"));

  run_package_private_preprocessor({a, b, user});

  EXPECT_TRUE(is_public(a_x));
}

// `Lq/B;.m` does not override the package-private `Lp/A;.m`, so it is renamed.
// A method handle of `Lq/C;.m`, which resolves to `Lq/B;.m`, names the new
// name too, so that it does not resolve to `Lp/A;.m`.
TEST_F(PackagePrivatePreprocessorMethodHandleTest,
       handle_of_renamed_method_names_new_name) {
  auto* a = make_class("Lp/A;");
  add_method(a, "Lp/A;.m:()V", DexAccessFlags(0), true,
             "((load-param-object v0) (return-void))");
  auto* b = make_class("Lq/B;", a->get_type());
  auto* b_m = add_method(b, "Lq/B;.m:()V", ACC_PUBLIC, true,
                         "((load-param-object v0) (return-void))");
  auto* c = make_class("Lq/C;", b->get_type());
  auto* user = make_class("Lq/User;");
  auto* use = add_method(
      user, "Lq/User;.use:(Lq/C;)V", ACC_PUBLIC | ACC_STATIC, false,
      call_handle_code("(load-param-object v1)",
                       R"(invoke-instance "Lq/C;.m:()V")", " v1", "(Lq/C;)V"));

  run_package_private_preprocessor({a, b, c, user});

  ASSERT_NE(b_m->get_name()->str(), "m");
  const auto* handle = get_method_handle(use);
  ASSERT_NE(handle, nullptr);
  EXPECT_EQ(handle->type(), METHOD_HANDLE_TYPE_INVOKE_INSTANCE);
  EXPECT_EQ(handle->methodref()->get_class(), c->get_type());
  EXPECT_EQ(handle->methodref()->get_name(), b_m->get_name());
}

// `Lq/B;.m` and `Lq/C;.m`, which overrides it, do not override the
// package-private `Lp/A;.m`, so they are renamed. ART finds `Lq/B;.m` for an
// invoke-direct method handle of `Lq/C2;.m` in `Lq/D;`, though what the handle
// then runs differs by ART version, so the handle names the new name too.
TEST_F(PackagePrivatePreprocessorMethodHandleTest,
       invoke_direct_handle_of_renamed_method_names_new_name) {
  auto* a = make_class("Lp/A;");
  add_method(a, "Lp/A;.m:()V", DexAccessFlags(0), true,
             "((load-param-object v0) (return-void))");
  auto* b = make_class("Lq/B;", a->get_type());
  auto* b_m = add_method(b, "Lq/B;.m:()V", ACC_PUBLIC, true,
                         "((load-param-object v0) (return-void))");
  auto* c2 = make_class("Lq/C2;", b->get_type());
  auto* c = make_class("Lq/C;", c2->get_type());
  add_method(c, "Lq/C;.m:()V", ACC_PUBLIC, true,
             "((load-param-object v0) (return-void))");
  auto* d = make_class("Lq/D;", c->get_type());
  auto* use = add_method(
      d, "Lq/D;.use:(Lq/D;)V", ACC_PUBLIC | ACC_STATIC, false,
      call_handle_code("(load-param-object v1)",
                       R"(invoke-direct "Lq/C2;.m:()V")", " v1", "(Lq/C2;)V"));

  run_package_private_preprocessor({a, b, c2, c, d});

  ASSERT_NE(b_m->get_name()->str(), "m");
  const auto* handle = get_method_handle(use);
  ASSERT_NE(handle, nullptr);
  EXPECT_EQ(handle->type(), METHOD_HANDLE_TYPE_INVOKE_DIRECT);
  EXPECT_EQ(handle->methodref()->get_class(), c2->get_type());
  EXPECT_EQ(handle->methodref()->get_name(), b_m->get_name());
}

// A method handle that a static field value holds names the new name too.
TEST_F(PackagePrivatePreprocessorMethodHandleTest,
       static_value_handle_of_renamed_method_names_new_name) {
  auto* a = make_class("Lp/A;");
  add_method(a, "Lp/A;.m:()V", DexAccessFlags(0), true,
             "((load-param-object v0) (return-void))");
  auto* b = make_class("Lq/B;", a->get_type());
  auto* b_m = add_method(b, "Lq/B;.m:()V", ACC_PUBLIC, true,
                         "((load-param-object v0) (return-void))");
  auto* c = make_class("Lq/C;", b->get_type());
  auto* field =
      DexField::make_field("Lq/C;.HANDLE:Ljava/lang/invoke/MethodHandle;")
          ->make_concrete(
              ACC_PUBLIC | ACC_STATIC | ACC_FINAL,
              std::make_unique<DexEncodedValueMethodHandle>(
                  redex::make_method_handle(METHOD_HANDLE_TYPE_INVOKE_INSTANCE,
                                            "Lq/C;.m:()V")));
  c->add_field(field);

  run_package_private_preprocessor({a, b, c});

  ASSERT_NE(b_m->get_name()->str(), "m");
  const auto* handle = redex::encoded_value_as<DexEncodedValueMethodHandle>(
                           field->get_static_value())
                           ->methodhandle();
  EXPECT_EQ(handle->type(), METHOD_HANDLE_TYPE_INVOKE_INSTANCE);
  EXPECT_EQ(handle->methodref()->get_class(), c->get_type());
  EXPECT_EQ(handle->methodref()->get_name(), b_m->get_name());
}

// A method handle that a static field value holds calls the package-private
// method too, from the class that declares the field, so the method is made
// public.
TEST_F(PackagePrivatePreprocessorMethodHandleTest,
       method_called_by_static_value_handle_is_made_public) {
  auto* a = make_class("Lp/A;");
  auto* m = add_method(a, "Lp/A;.m:()V", ACC_STATIC, false, kReturnVoid);
  auto* b = make_class("Lp/B;");
  b->add_field(
      DexField::make_field("Lp/B;.HANDLE:Ljava/lang/invoke/MethodHandle;")
          ->make_concrete(
              ACC_PUBLIC | ACC_STATIC | ACC_FINAL,
              std::make_unique<DexEncodedValueMethodHandle>(
                  redex::make_method_handle(METHOD_HANDLE_TYPE_INVOKE_STATIC,
                                            "Lp/A;.m:()V"))));

  run_package_private_preprocessor({a, b});

  EXPECT_TRUE(is_public(m));
}

// A method handle in an annotation resolves its field by its kind too: a
// static-get handle of `Lp/B;.x:I` reads the static field `Lp/A;.x`, not the
// instance field `Lp/B;.x` that it names.
TEST_F(PackagePrivatePreprocessorMethodHandleTest,
       field_of_annotation_handle_resolves_by_its_kind) {
  auto* a = make_class("Lp/A;");
  auto* a_x = DexField::make_field("Lp/A;.x:I")->make_concrete(ACC_STATIC);
  a->add_field(a_x);
  auto* b = make_class("Lp/B;", a->get_type());
  b->add_field(DexField::make_field("Lp/B;.x:I")->make_concrete(ACC_PUBLIC));
  auto* user = make_class("Lp/User;");
  auto annotation = std::make_unique<DexAnnotation>(
      DexType::make_type("LAnno;"), DAV_RUNTIME);
  annotation->add_element(
      "value",
      std::make_unique<DexEncodedValueMethodHandle>(redex::make_method_handle(
          METHOD_HANDLE_TYPE_STATIC_GET, "Lp/B;.x:I")));
  auto annotation_set = std::make_unique<DexAnnotationSet>();
  annotation_set->add_annotation(std::move(annotation));
  ASSERT_TRUE(user->attach_annotation_set(std::move(annotation_set)));

  run_package_private_preprocessor({a, b, user});

  EXPECT_TRUE(is_public(a_x));
}
