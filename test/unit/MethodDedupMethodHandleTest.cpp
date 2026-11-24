/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <string>
#include <vector>

#include <gtest/gtest.h>

#include "AnnoUtils.h"
#include "ConstantLifting.h"
#include "Creators.h"
#include "DexAnnotation.h"
#include "IRAssembler.h"
#include "NormalizeConstructor.h"
#include "RedexTest.h"
#include "TypeUtil.h"
#include "Walkers.h"

class MethodDedupMethodHandleTest : public RedexTest {};

namespace {

DexClass* make_class(const char* name, const std::vector<DexMethod*>& methods) {
  ClassCreator creator(DexType::make_type(name));
  creator.set_super(type::java_lang_Object());
  for (auto* method : methods) {
    creator.add_method(method);
  }
  return creator.create();
}

void build_cfgs(const Scope& scope) {
  walk::code(scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });
}

} // namespace

// The method handle (tool-generated here) names `get` without the parameter
// that constant lifting would add, and `invokeExact` passes no argument, so
// `get` must keep its prototype.
TEST_F(MethodDedupMethodHandleTest,
       constantLiftingKeepsPrototypeOfMethodNamedByMethodHandle) {
  create_object_class();
  auto* method_meta =
      DexType::make_type("Lcom/facebook/redex/annotations/MethodMeta;");
  // Concrete methods take no annotations, so annotate `get` first.
  auto* get = dynamic_cast<DexMethod*>(
      DexMethod::make_method("LFoo;.get:()Ljava/lang/String;"));
  ASSERT_NE(get, nullptr);
  ASSERT_TRUE(get->attach_annotation_set(create_anno_set(
      {{"constantTypes", "S"}, {"constantValues", "post_id"}}, method_meta)));
  get->make_concrete(ACC_PUBLIC | ACC_STATIC,
                     assembler::ircode_from_string(R"(
    (
      (const-string "post_id")
      (move-result-pseudo-object v0)
      (return-object v0)
    )
  )"),
                     /* is_virtual */ false);
  auto* use = assembler::method_from_string(R"(
    (method (public static) "LFoo;.use:()V"
     (
      (invoke-static () "LFoo;.get:()Ljava/lang/String;")
      (const-method-handle invoke-static "LFoo;.get:()Ljava/lang/String;")
      (move-result-pseudo-object v0)
      (invoke-polymorphic (v0) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "()Ljava/lang/String;")
      (return-void)
     )
    )
  )");
  Scope scope{make_class("LFoo;", {get, use})};
  build_cfgs(scope);

  ConstantLifting constant_lifting;
  ASSERT_TRUE(constant_lifting.is_applicable_to_constant_lifting(get));
  constant_lifting.lift_constants_from(scope, /* type_tags */ nullptr, {get},
                                       /* stud_method_threshold */ 100);

  EXPECT_EQ(show(get), "LFoo;.get:()Ljava/lang/String;");
}

// `A(String)` and `A(Integer)` only store their argument into `f`, so
// deduplication keeps one of them, generalized to `A(Object)`. The method
// handle (tool-generated here) names `A(Integer)`, and `invokeExact` passes an
// `Integer` to it, so `A(Integer)` must keep its prototype.
TEST_F(MethodDedupMethodHandleTest,
       constructorDedupKeepsPrototypeOfConstructorNamedByMethodHandle) {
  create_object_class();
  ClassCreator creator(DexType::make_type("LA;"));
  creator.set_super(type::java_lang_Object());
  creator.add_field(DexField::make_field("LA;.f:Ljava/lang/Object;")
                        ->make_concrete(ACC_PUBLIC));
  for (const auto* param : {"Ljava/lang/Integer;", "Ljava/lang/String;"}) {
    creator.add_method(assembler::method_from_string(
        std::string(R"((method (public constructor) "LA;.<init>:()") + param +
        R"()V"
         (
          (load-param-object v0)
          (load-param-object v1)
          (invoke-direct (v0) "Ljava/lang/Object;.<init>:()V")
          (iput-object v1 v0 "LA;.f:Ljava/lang/Object;")
          (return-void)
         )
        ))"));
  }
  auto* a = creator.create();
  auto* user = make_class("LU;", {assembler::method_from_string(R"(
    (method (public static) "LU;.use:(Ljava/lang/Integer;)LA;"
     (
      (load-param-object v1)
      (const-method-handle invoke-constructor "LA;.<init>:(Ljava/lang/Integer;)V")
      (move-result-pseudo-object v0)
      (invoke-polymorphic (v0 v1) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "(Ljava/lang/Integer;)LA;")
      (move-result-object v0)
      (return-object v0)
     )
    )
  )")});
  Scope scope{a, user};

  method_dedup::dedup_constructors({a}, scope);

  auto* ctor = DexMethod::get_method("LA;.<init>:(Ljava/lang/Integer;)V");
  ASSERT_NE(ctor, nullptr);
  EXPECT_NE(ctor->as_def(), nullptr);
}
