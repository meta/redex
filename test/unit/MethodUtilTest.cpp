/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "MethodUtil.h"

#include "Creators.h"
#include "DexAnnotation.h"
#include "IRAssembler.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"
#include "TypeUtil.h"

class MethodUtilTest : public RedexTest {};

TEST_F(MethodUtilTest, test_count_opcodes) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v1 1)
      (const v2 2)
      (const v3 3)
      (const v4 4)
      (const v5 5)
      (const v6 6)
    )
  )");

  EXPECT_EQ(6, method::count_opcode_of_types(code.get(), {OPCODE_CONST}));
  code->build_cfg();
  EXPECT_EQ(6, method::count_opcode_of_types(code->cfg(), {OPCODE_CONST}));
  EXPECT_EQ(
      6,
      method::count_opcode_of_types(code->cfg().entry_block(), {OPCODE_CONST}));
  code->clear_cfg();
}

TEST_F(MethodUtilTest, can_change_signature) {
  auto make = [](const char* signature, DexAccessFlags access) {
    return DexMethod::make_method(signature)->make_concrete(access, false);
  };
  auto* plain = make("LA;.plain:()V", ACC_PUBLIC | ACC_STATIC);
  EXPECT_TRUE(method::can_change_signature(plain));

  auto* kept = make("LA;.kept:()V", ACC_PUBLIC | ACC_STATIC);
  kept->rstate.set_root();
  EXPECT_FALSE(method::can_change_signature(kept));

  auto* native = make("LA;.jni:()V", ACC_PUBLIC | ACC_STATIC | ACC_NATIVE);
  EXPECT_FALSE(method::can_change_signature(native));

  auto* no_optimizations = make("LA;.noOpt:()V", ACC_PUBLIC | ACC_STATIC);
  no_optimizations->rstate.set_no_optimizations();
  EXPECT_FALSE(method::can_change_signature(no_optimizations));
}

// A static initializer that makes a method handle call or a call through a call
// site may run any code, so it may have side effects.
TEST_F(MethodUtilTest, clinitWithDynamicInvokeMayHaveSideEffects) {
  auto make_class = [](const char* name, const std::string& body) {
    auto* clinit = assembler::method_from_string(
        std::string(R"((method (public static constructor) ")") + name +
        R"(.<clinit>:()V" )" + body + ")");
    ClassCreator creator(DexType::make_type(name));
    creator.set_super(type::java_lang_Object());
    creator.add_method(clinit);
    return creator.create();
  };
  auto* polymorphic = make_class("LPolymorphic;", R"(
    (
      (const-method-handle invoke-static "LBar;.run:()V")
      (move-result-pseudo-object v0)
      (invoke-polymorphic (v0) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "()V")
      (return-void)
    )
  )");
  EXPECT_NE(method::clinit_may_have_side_effects(
                polymorphic, /* allow_benign_method_invocations */ false),
            nullptr);

  // The `invoke-static` becomes an `invoke-custom`.
  auto* custom = make_class("LCustom;", R"(
    (
      (invoke-static () "LCustom;.placeholder:()V")
      (return-void)
    )
  )");
  redex::make_invoke_custom(custom->get_clinit()->get_code(), "run", "()V");
  EXPECT_NE(method::clinit_may_have_side_effects(
                custom, /* allow_benign_method_invocations */ false),
            nullptr);
}

// A method handle names its method wherever it is held: in code, among the
// bootstrap method and arguments of a call site, in a static field value or in
// an annotation. An
// invoke-instance handle that names a method by a subclass also names the
// method that it resolves to.
TEST_F(MethodUtilTest, gather_methods_named_by_method_handles) {
  auto make_class = [](const char* name, DexType* super,
                       const std::vector<const char*>& methods) {
    ClassCreator creator(DexType::make_type(name));
    creator.set_super(super);
    for (const auto* method : methods) {
      creator.add_method(assembler::method_from_string(method));
    }
    return creator.create();
  };
  auto* base = make_class("LBase;", type::java_lang_Object(), {R"(
    (method (public) "LBase;.run:()V" ((load-param-object v0) (return-void)))
  )"});
  make_class("LSub;", base->get_type(), {});
  make_class("LBoot;", type::java_lang_Object(), {R"(
    (method (public static) "LBoot;.bootstrap:(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodHandle;)Ljava/lang/invoke/CallSite;"
     ((const v0 0) (return-object v0)))
  )"});
  auto* foo = make_class("LFoo;", type::java_lang_Object(),
                         {
                             R"(
    (method (public static) "LFoo;.compute:(I)I" ((load-param v0) (return v0)))
  )",
                             R"(
    (method (public static) "LFoo;.linked:()V" ((return-void)))
  )",
                             R"(
    (method (public static) "LFoo;.stored:()V" ((return-void)))
  )",
                             R"(
    (method (public static) "LFoo;.annotated:()V" ((return-void)))
  )",
                             R"(
    (method (public static) "LFoo;.unnamed:()V" ((return-void)))
  )",
                         });
  auto* user = make_class("LUser;", type::java_lang_Object(), {R"(
    (method (public static) "LUser;.use:()V"
     (
      (const-method-handle invoke-static "LFoo;.compute:(I)I")
      (move-result-pseudo-object v0)
      (const-method-handle invoke-instance "LSub;.run:()V")
      (move-result-pseudo-object v0)
      (const-method-handle static-get "LFoo;.field:I")
      (move-result-pseudo-object v0)
      (invoke-static () "LUser;.placeholder:()V")
      (return-void)
     )
    )
  )"});
  std::vector<std::unique_ptr<DexEncodedValue>> bootstrap_args;
  bootstrap_args.push_back(
      std::make_unique<DexEncodedValueMethodHandle>(redex::make_method_handle(
          METHOD_HANDLE_TYPE_INVOKE_STATIC, "LFoo;.linked:()V")));
  redex::make_invoke_custom(
      DexMethod::get_method("LUser;.use:()V")->as_def()->get_code(), "run",
      "()V", std::move(bootstrap_args));
  user->add_field(
      DexField::make_field("LUser;.HANDLE:Ljava/lang/invoke/MethodHandle;")
          ->make_concrete(
              ACC_PUBLIC | ACC_STATIC | ACC_FINAL,
              std::make_unique<DexEncodedValueMethodHandle>(
                  redex::make_method_handle(METHOD_HANDLE_TYPE_INVOKE_STATIC,
                                            "LFoo;.stored:()V"))));
  auto annotation = std::make_unique<DexAnnotation>(
      DexType::make_type("LAnno;"), DAV_RUNTIME);
  annotation->add_element(
      "value",
      std::make_unique<DexEncodedValueMethodHandle>(redex::make_method_handle(
          METHOD_HANDLE_TYPE_INVOKE_STATIC, "LFoo;.annotated:()V")));
  auto annotation_set = std::make_unique<DexAnnotationSet>();
  annotation_set->add_annotation(std::move(annotation));
  ASSERT_TRUE(user->attach_annotation_set(std::move(annotation_set)));

  auto methods = method::gather_methods_named_by_method_handles(
      {base, type_class(DexType::get_type("LSub;")),
       type_class(DexType::get_type("LBoot;")), foo, user});

  auto named = [&](const char* method) {
    return methods.count(DexMethod::get_method(method)->as_def()) != 0;
  };
  EXPECT_TRUE(named("LFoo;.compute:(I)I"));
  EXPECT_TRUE(named("LBase;.run:()V"));
  EXPECT_TRUE(
      named("LBoot;.bootstrap:(Ljava/lang/invoke/MethodHandles$Lookup;"
            "Ljava/lang/String;Ljava/lang/invoke/MethodType;"
            "Ljava/lang/invoke/MethodHandle;)Ljava/lang/invoke/CallSite;"));
  EXPECT_TRUE(named("LFoo;.linked:()V"));
  EXPECT_TRUE(named("LFoo;.stored:()V"));
  EXPECT_TRUE(named("LFoo;.annotated:()V"));
  EXPECT_FALSE(named("LFoo;.unnamed:()V"));
  EXPECT_EQ(methods.size(), 6);
}

// An invoke-direct method handle of `LA;.m` in `LC;`, a subclass of `LB;`,
// which overrides `m`, names `LA;.m` and runs `LB;.m` on Android 9.
TEST_F(MethodUtilTest, gather_methods_named_by_invoke_direct_method_handle) {
  auto make_class = [](const char* name, DexType* super,
                       const std::vector<const char*>& methods) {
    ClassCreator creator(DexType::make_type(name));
    creator.set_super(super);
    for (const auto* method : methods) {
      creator.add_method(assembler::method_from_string(method));
    }
    return creator.create();
  };
  auto* a = make_class("LA;", type::java_lang_Object(), {R"(
    (method (public) "LA;.m:()V" ((load-param-object v0) (return-void)))
  )"});
  auto* b = make_class("LB;", a->get_type(), {R"(
    (method (public) "LB;.m:()V" ((load-param-object v0) (return-void)))
  )"});
  auto* c = make_class("LC;", b->get_type(), {R"(
    (method (public static) "LC;.use:()V"
     (
      (const-method-handle invoke-direct "LA;.m:()V")
      (move-result-pseudo-object v0)
      (return-void)
     )
    )
  )"});

  auto methods = method::gather_methods_named_by_method_handles({a, b, c});

  EXPECT_EQ(methods.count(DexMethod::get_method("LA;.m:()V")->as_def()), 1);
  EXPECT_EQ(methods.count(DexMethod::get_method("LB;.m:()V")->as_def()), 1);
  EXPECT_EQ(methods.size(), 2);
}

// A field method handle names its field wherever it is held: in code, in a
// static field value or in an annotation. A handle that names a field by a
// subclass names the field that it resolves to.
TEST_F(MethodUtilTest, gather_fields_named_by_method_handles) {
  ClassCreator base(DexType::make_type("LFields;"));
  base.set_super(type::java_lang_Object());
  for (const auto* field :
       {"LFields;.read:I", "LFields;.written:I", "LFields;.unnamed:I"}) {
    base.add_field(
        DexField::make_field(field)->make_concrete(ACC_PUBLIC | ACC_STATIC));
  }
  base.add_field(
      DexField::make_field("LFields;.annotated:I")->make_concrete(ACC_PUBLIC));
  auto* base_cls = base.create();
  ClassCreator sub(DexType::make_type("LSubFields;"));
  sub.set_super(base_cls->get_type());
  auto* sub_cls = sub.create();

  ClassCreator user(DexType::make_type("LFieldUser;"));
  user.set_super(type::java_lang_Object());
  user.add_method(assembler::method_from_string(R"(
    (method (public static) "LFieldUser;.use:()V"
     (
      (const-method-handle static-get "LSubFields;.read:I")
      (move-result-pseudo-object v0)
      (const-method-handle invoke-static "LFieldUser;.use:()V")
      (move-result-pseudo-object v0)
      (return-void)
     )
    )
  )"));
  user.add_field(
      DexField::make_field("LFieldUser;.HANDLE:Ljava/lang/invoke/MethodHandle;")
          ->make_concrete(
              ACC_PUBLIC | ACC_STATIC | ACC_FINAL,
              std::make_unique<DexEncodedValueMethodHandle>(
                  redex::make_method_handle(METHOD_HANDLE_TYPE_STATIC_PUT,
                                            "LFields;.written:I"))));
  auto* user_cls = user.create();
  auto annotation = std::make_unique<DexAnnotation>(
      DexType::make_type("LAnno;"), DAV_RUNTIME);
  annotation->add_element(
      "value",
      std::make_unique<DexEncodedValueMethodHandle>(redex::make_method_handle(
          METHOD_HANDLE_TYPE_INSTANCE_GET, "LFields;.annotated:I")));
  auto annotation_set = std::make_unique<DexAnnotationSet>();
  annotation_set->add_annotation(std::move(annotation));
  ASSERT_TRUE(user_cls->attach_annotation_set(std::move(annotation_set)));

  auto fields = method::gather_fields_named_by_method_handles(
      {base_cls, sub_cls, user_cls});

  auto named = [&](const char* field) {
    return fields.count(DexField::get_field(field)->as_def()) != 0;
  };
  EXPECT_TRUE(named("LFields;.read:I"));
  EXPECT_TRUE(named("LFields;.written:I"));
  EXPECT_TRUE(named("LFields;.annotated:I"));
  EXPECT_FALSE(named("LFields;.unnamed:I"));
  EXPECT_EQ(fields.size(), 3);
}

// Every field method handle names its field, wherever it is held: in code, in
// a static field value or in an annotation. A handle that calls a method names
// no field.
TEST_F(MethodUtilTest, gather_method_handle_fields) {
  ClassCreator holder(DexType::make_type("LHandleFields;"));
  holder.set_super(type::java_lang_Object());
  for (const auto* field :
       {"LHandleFields;.codePut:I", "LHandleFields;.valuePut:I",
        "LHandleFields;.codeGet:I", "LHandleFields;.unnamed:I"}) {
    holder.add_field(
        DexField::make_field(field)->make_concrete(ACC_PUBLIC | ACC_STATIC));
  }
  holder.add_field(DexField::make_field("LHandleFields;.annotatedPut:I")
                       ->make_concrete(ACC_PUBLIC));
  auto* holder_cls = holder.create();

  ClassCreator user(DexType::make_type("LHandleUser;"));
  user.set_super(type::java_lang_Object());
  user.add_method(assembler::method_from_string(R"(
    (method (public static) "LHandleUser;.use:()V"
     (
      (const-method-handle static-put "LHandleFields;.codePut:I")
      (move-result-pseudo-object v0)
      (const-method-handle static-get "LHandleFields;.codeGet:I")
      (move-result-pseudo-object v0)
      (const-method-handle invoke-static "LHandleUser;.use:()V")
      (move-result-pseudo-object v0)
      (return-void)
     )
    )
  )"));
  user.add_field(
      DexField::make_field(
          "LHandleUser;.HANDLE:Ljava/lang/invoke/MethodHandle;")
          ->make_concrete(
              ACC_PUBLIC | ACC_STATIC | ACC_FINAL,
              std::make_unique<DexEncodedValueMethodHandle>(
                  redex::make_method_handle(METHOD_HANDLE_TYPE_STATIC_PUT,
                                            "LHandleFields;.valuePut:I"))));
  auto* user_cls = user.create();
  auto annotation = std::make_unique<DexAnnotation>(
      DexType::make_type("LAnno;"), DAV_RUNTIME);
  annotation->add_element(
      "value",
      std::make_unique<DexEncodedValueMethodHandle>(redex::make_method_handle(
          METHOD_HANDLE_TYPE_INSTANCE_PUT, "LHandleFields;.annotatedPut:I")));
  auto annotation_set = std::make_unique<DexAnnotationSet>();
  annotation_set->add_annotation(std::move(annotation));
  ASSERT_TRUE(user_cls->attach_annotation_set(std::move(annotation_set)));

  auto fields = method::gather_method_handle_fields({holder_cls, user_cls});

  auto named = [&](const char* field) {
    return fields.contains(DexField::get_field(field)->as_def());
  };
  EXPECT_TRUE(named("LHandleFields;.codePut:I"));
  EXPECT_TRUE(named("LHandleFields;.valuePut:I"));
  EXPECT_TRUE(named("LHandleFields;.annotatedPut:I"));
  EXPECT_TRUE(named("LHandleFields;.codeGet:I"));
  EXPECT_FALSE(named("LHandleFields;.unnamed:I"));
  EXPECT_EQ(fields.defined.size(), 4);
  EXPECT_FALSE(fields.empty());
  EXPECT_TRUE(method::MethodHandleFields().empty());
}

// A handle may access a field that it names but that resolves to no
// definition, which can then be any library field of that name and type: here
// `slot` and `other`, which the app class `LAppSub;` inherits from the library
// class `LLibBase;`, which is not loaded, and `SDK_INT` of a library class that
// is not loaded either.
TEST_F(MethodUtilTest, gather_method_handle_fields_undefined) {
  ClassCreator app_sub(DexType::make_type("LAppSub;"));
  app_sub.set_super(DexType::make_type("LLibBase;"));
  app_sub.add_method(assembler::method_from_string(R"(
    (method (public static) "LAppSub;.use:()V"
     (
      (const-method-handle static-put "LAppSub;.slot:I")
      (move-result-pseudo-object v0)
      (const-method-handle static-put "Landroid/os/Build$VERSION;.SDK_INT:I")
      (move-result-pseudo-object v0)
      (const-method-handle static-get "LAppSub;.other:J")
      (move-result-pseudo-object v0)
      (return-void)
     )
    )
  )"));

  auto fields = method::gather_method_handle_fields({app_sub.create()});

  EXPECT_TRUE(fields.defined.empty());
  EXPECT_FALSE(fields.empty());
  // The library fields that the unresolved references can reach.
  ClassCreator lib(DexType::make_type("LLib;"));
  lib.set_super(type::java_lang_Object());
  lib.set_external();
  for (const auto* spec :
       {"LLib;.slot:I", "LLib;.slot:J", "LLib;.other:I", "LLib;.other:J"}) {
    lib.add_field(
        DexField::make_field(spec)->make_concrete(ACC_PUBLIC | ACC_STATIC));
  }
  lib.create();
  ClassCreator version(DexType::make_type("Landroid/os/Build$VERSION;"));
  version.set_super(type::java_lang_Object());
  version.set_external();
  version.add_field(DexField::make_field("Landroid/os/Build$VERSION;.SDK_INT:I")
                        ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL));
  version.create();
  auto named = [&](const char* field) {
    return fields.contains(DexField::get_field(field)->as_def());
  };
  EXPECT_TRUE(named("LLib;.slot:I"));
  EXPECT_TRUE(named("LLib;.other:J"));
  EXPECT_TRUE(named("Landroid/os/Build$VERSION;.SDK_INT:I"));
  EXPECT_FALSE(named("LLib;.slot:J"));
  EXPECT_FALSE(named("LLib;.other:I"));
  // A field that resolves to no definition cannot be a field of an app class.
  ClassCreator app_other(DexType::make_type("LAppOther;"));
  app_other.set_super(type::java_lang_Object());
  app_other.add_field(DexField::make_field("LAppOther;.slot:I")
                          ->make_concrete(ACC_PUBLIC | ACC_STATIC));
  app_other.create();
  EXPECT_FALSE(named("LAppOther;.slot:I"));
}

// A handle that names a field through a subclass names the field that the
// reference resolves to.
TEST_F(MethodUtilTest, gather_method_handle_fields_named_through_subclass) {
  ClassCreator base(DexType::make_type("LBase;"));
  base.set_super(type::java_lang_Object());
  base.add_field(DexField::make_field("LBase;.slot:I")
                     ->make_concrete(ACC_PUBLIC | ACC_STATIC));
  auto* base_cls = base.create();
  ClassCreator sub(DexType::make_type("LSub;"));
  sub.set_super(base_cls->get_type());
  sub.add_method(assembler::method_from_string(R"(
    (method (public static) "LSub;.use:()V"
     (
      (const-method-handle static-put "LSub;.slot:I")
      (move-result-pseudo-object v0)
      (return-void)
     )
    )
  )"));

  auto fields = method::gather_method_handle_fields({base_cls, sub.create()});

  EXPECT_TRUE(fields.contains(DexField::get_field("LBase;.slot:I")->as_def()));
  EXPECT_TRUE(fields.undefined.empty());
}

TEST_F(MethodUtilTest, runs_method_handle_target) {
  EXPECT_TRUE(method::runs_method_handle_target(DexMethod::make_method(
      "Ljava/lang/invoke/MethodHandle;.invokeWithArguments:([Ljava/lang/"
      "Object;)Ljava/lang/Object;")));
  EXPECT_TRUE(method::runs_method_handle_target(DexMethod::make_method(
      "Ljava/lang/invoke/MethodHandle;.invokeWithArguments:(Ljava/util/"
      "List;)Ljava/lang/Object;")));
  EXPECT_FALSE(method::runs_method_handle_target(DexMethod::make_method(
      "Ljava/lang/invoke/MethodHandle;.type:()Ljava/lang/invoke/MethodType;")));
  EXPECT_FALSE(method::runs_method_handle_target(
      DexMethod::make_method("LFoo;.invokeWithArguments:()V")));
}
