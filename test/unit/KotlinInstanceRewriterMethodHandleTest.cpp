/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <algorithm>

#include <gtest/gtest.h>

#include "Creators.h"
#include "DexAnnotation.h"
#include "IRAssembler.h"
#include "KotlinInstanceRewriter.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"
#include "Walkers.h"

// The method handles in these tests are tool-generated: a bytecode tool with
// an app-defined bootstrap method.

namespace {

class KotlinInstanceRewriterMethodHandleTest : public RedexTest {
 protected:
  // A non-capturing Kotlin lambda LLambda$0; whose <clinit> stores a new
  // instance in its INSTANCE field.
  KotlinInstanceRewriterMethodHandleTest() {
    auto* type = DexType::make_type("LLambda$0;");
    ClassCreator cc(type);
    cc.set_super(type::kotlin_jvm_internal_Lambda());
    cc.set_access(ACC_PUBLIC | ACC_FINAL);
    cc.add_interface(DexType::make_type("Lkotlin/jvm/functions/Function0;"));
    m_instance = DexField::make_field("LLambda$0;.INSTANCE:LLambda$0;")
                     ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL);
    cc.add_field(m_instance);
    cc.add_method(assembler::method_from_string(R"(
      (method (public) "LLambda$0;.invoke:()Ljava/lang/Object;"
        (
          (load-param-object v0)
          (const v1 0)
          (return-object v1)
        )
      )
    )"));
    cc.add_method(assembler::method_from_string(R"(
      (method (public constructor) "LLambda$0;.<init>:()V"
        (
          (load-param-object v0)
          (return-void)
        )
      )
    )"));
    cc.add_method(assembler::method_from_string(R"(
      (method (public static constructor) "LLambda$0;.<clinit>:()V"
        (
          (new-instance "LLambda$0;")
          (move-result-pseudo-object v0)
          (invoke-direct (v0) "LLambda$0;.<init>:()V")
          (sput-object v0 "LLambda$0;.INSTANCE:LLambda$0;")
          (return-void)
        )
      )
    )"));
    m_scope.push_back(cc.create());

    // The one ordinary read of INSTANCE.
    add_user_method(R"(
      (method (public static) "LUser;.get:()Ljava/lang/Object;"
        (
          (sget-object "LLambda$0;.INSTANCE:LLambda$0;")
          (move-result-pseudo-object v0)
          (return-object v0)
        )
      )
    )");
  }

  void add_user_method(const std::string& method) {
    user()->add_method(assembler::method_from_string(method));
  }

  DexClass* user() {
    if (m_user == nullptr) {
      ClassCreator cc(DexType::make_type("LUser;"));
      cc.set_super(type::java_lang_Object());
      cc.set_access(ACC_PUBLIC);
      m_user = cc.create();
      m_scope.push_back(m_user);
    }
    return m_user;
  }

  // Runs the steps of KotlinStatelessLambdaSingletonRemovalPass.
  void run_rewriter() {
    walk::code(m_scope, [](DexMethod*, IRCode& code) { code.build_cfg(); });
    KotlinInstanceRewriter rewriter;
    ConcurrentMap<DexFieldRef*, std::set<std::pair<IRInstruction*, DexMethod*>>>
        instance_map;
    rewriter.collect_instance_usage(m_scope, instance_map);
    rewriter.remove_escaping_instance(m_scope, instance_map);
    rewriter.transform(instance_map);
  }

  bool instance_field_kept() const {
    const auto& sfields = type_class(m_instance->get_class())->get_sfields();
    return std::find(sfields.begin(), sfields.end(), m_instance) !=
           sfields.end();
  }

  Scope m_scope;
  DexClass* m_user{nullptr};
  DexField* m_instance{nullptr};
};

} // namespace

// With one read, INSTANCE is replaced by a new instance at the read.
TEST_F(KotlinInstanceRewriterMethodHandleTest, single_read_is_rewritten) {
  run_rewriter();

  EXPECT_FALSE(instance_field_kept());
}

// A static-get method handle reads INSTANCE too. It cannot become a new
// instance, so INSTANCE stays.
TEST_F(KotlinInstanceRewriterMethodHandleTest, read_through_handle_keeps) {
  add_user_method(R"(
    (method (public static) "LUser;.handle:()Ljava/lang/invoke/MethodHandle;"
      (
        (const-method-handle static-get "LLambda$0;.INSTANCE:LLambda$0;")
        (move-result-pseudo-object v0)
        (return-object v0)
      )
    )
  )");

  run_rewriter();

  EXPECT_TRUE(instance_field_kept());
}

// So does a static-put method handle, which writes INSTANCE.
TEST_F(KotlinInstanceRewriterMethodHandleTest, write_through_handle_keeps) {
  add_user_method(R"(
    (method (public static) "LUser;.handle:()Ljava/lang/invoke/MethodHandle;"
      (
        (const-method-handle static-put "LLambda$0;.INSTANCE:LLambda$0;")
        (move-result-pseudo-object v0)
        (return-object v0)
      )
    )
  )");

  run_rewriter();

  EXPECT_TRUE(instance_field_kept());
}

// A method handle that no code holds, the value of a static field, reads
// INSTANCE too.
TEST_F(KotlinInstanceRewriterMethodHandleTest, read_through_field_value_keeps) {
  user()->add_field(
      DexField::make_field("LUser;.HANDLE:Ljava/lang/invoke/MethodHandle;")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL,
                          std::make_unique<DexEncodedValueMethodHandle>(
                              redex::make_method_handle(
                                  METHOD_HANDLE_TYPE_STATIC_GET,
                                  "LLambda$0;.INSTANCE:LLambda$0;"))));

  run_rewriter();

  EXPECT_TRUE(instance_field_kept());
}

// So does a method handle in an annotation.
TEST_F(KotlinInstanceRewriterMethodHandleTest, read_through_annotation_keeps) {
  auto annotation = std::make_unique<DexAnnotation>(
      DexType::make_type("LAnno;"), DAV_RUNTIME);
  annotation->add_element(
      "value",
      std::make_unique<DexEncodedValueMethodHandle>(redex::make_method_handle(
          METHOD_HANDLE_TYPE_STATIC_GET, "LLambda$0;.INSTANCE:LLambda$0;")));
  auto annotation_set = std::make_unique<DexAnnotationSet>();
  annotation_set->add_annotation(std::move(annotation));
  ASSERT_TRUE(user()->attach_annotation_set(std::move(annotation_set)));

  run_rewriter();

  EXPECT_TRUE(instance_field_kept());
}
