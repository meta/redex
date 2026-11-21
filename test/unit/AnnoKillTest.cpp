/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <algorithm>

#include <gtest/gtest.h>

#include "AnnoKill.h"
#include "Creators.h"
#include "DexAnnotation.h"
#include "DexClass.h"
#include "IRAssembler.h"
#include "RedexTest.h"
#include "TypeUtil.h"

class AnnoKillTest : public RedexTest {
 protected:
  void check_native_annotations(bool only_force_kill,
                                bool force_native,
                                bool define_annotations = true) {
    const AnnoKill::AnnoNames native_annos = {
        "Ldalvik/annotation/optimization/FastNative;",
        "Ldalvik/annotation/optimization/CriticalNative;"};
    const std::string irrelevant = "Lcom/example/BuildOnly;";
    Scope scope;
    for (const auto& name : native_annos) {
      auto* type = DexType::make_type(name);
      if (!define_annotations) {
        continue;
      }
      ClassCreator annotation(type);
      annotation.set_super(type::java_lang_Object());
      annotation.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT |
                            ACC_ANNOTATION);
      scope.push_back(annotation.create());
    }

    ClassCreator creator(DexType::make_type("Lcom/example/NativeMethods;"));
    creator.set_super(type::java_lang_Object());
    std::vector<DexMethod*> methods;
    for (size_t i = 0; i < native_annos.size(); ++i) {
      auto* method = dynamic_cast<DexMethod*>(DexMethod::make_method(
          "Lcom/example/NativeMethods;.call" + std::to_string(i) + ":(I)I"));
      ASSERT_NE(method, nullptr);
      auto annotations = std::make_unique<DexAnnotationSet>();
      annotations->add_annotation(std::make_unique<DexAnnotation>(
          DexType::get_type(native_annos[i]), DAV_BUILD));
      annotations->add_annotation(std::make_unique<DexAnnotation>(
          DexType::make_type(irrelevant), DAV_BUILD));
      ASSERT_TRUE(method->attach_annotation_set(std::move(annotations)));
      method->make_concrete(i == 0 ? ACC_PUBLIC | ACC_FINAL | ACC_NATIVE
                                   : ACC_PUBLIC | ACC_STATIC | ACC_NATIVE,
                            /*is_virtual=*/i == 0);
      creator.add_method(method);
      methods.push_back(method);
    }
    scope.push_back(creator.create());

    AnnoKill::AnnoNames force_kill = {irrelevant};
    if (force_native) {
      force_kill.insert(force_kill.end(), native_annos.begin(),
                        native_annos.end());
    }
    AnnoKill kill(scope, only_force_kill, false, {}, {}, force_kill, {}, {});
    EXPECT_FALSE(kill.kill_annotations());
    EXPECT_EQ(scope.size(), define_annotations ? 3u : 1u);
    for (size_t i = 0; i < methods.size(); ++i) {
      auto* annotations = methods[i]->get_anno_set();
      ASSERT_NE(annotations, nullptr);
      ASSERT_EQ(annotations->size(), 1u);
      EXPECT_EQ(annotations->get_annotations()[0]->type(),
                DexType::get_type(native_annos[i]));
      EXPECT_TRUE(annotations->get_annotations()[0]->build_visible());
      EXPECT_EQ(methods[i]->get_code(), nullptr);
    }
    EXPECT_EQ(kill.get_stats().annotations_killed, 2u);
  }

  // Whether the annotation class LAnno; survives AnnoKill when the only code
  // that names it is `code`, a static method of another class.
  static bool keeps_annotation_named_by(const std::string& code) {
    Scope scope;
    auto* annotation_type =
        DexType::make_type("Ljava/lang/annotation/Annotation;");
    ClassCreator annotation_interface(annotation_type);
    annotation_interface.set_super(type::java_lang_Object());
    annotation_interface.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
    annotation_interface.set_external();
    annotation_interface.add_method(
        DexMethod::make_method(
            "Ljava/lang/annotation/Annotation;.annotationType:()Ljava/lang/"
            "Class;")
            ->make_concrete(ACC_PUBLIC | ACC_ABSTRACT, /* is_virtual */ true));
    annotation_interface.create();

    auto* anno_type = DexType::make_type("LAnno;");
    ClassCreator annotation(anno_type);
    annotation.set_super(type::java_lang_Object());
    annotation.add_interface(annotation_type);
    annotation.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT |
                          ACC_ANNOTATION);
    annotation.add_method(DexMethod::make_method("LAnno;.value:()I")
                              ->make_concrete(ACC_PUBLIC | ACC_ABSTRACT,
                                              /* is_virtual */ true));
    scope.push_back(annotation.create());

    ClassCreator user(DexType::make_type("LUser;"));
    user.set_super(type::java_lang_Object());
    user.add_method(DexMethod::make_method("LUser;.use:()V")
                        ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                                        assembler::ircode_from_string(code),
                                        /* is_virtual */ false));
    scope.push_back(user.create());

    AnnoKill kill(scope, /* only_force_kill */ false,
                  /* kill_bad_signatures */ false, /* keep */ {}, /* kill */ {},
                  /* force_kill */ {}, /* class_hierarchy_keep_annos */ {},
                  /* annotated_keep_annos */ {});
    kill.kill_annotations();
    return std::find(scope.begin(), scope.end(), type_class(anno_type)) !=
           scope.end();
  }
};

TEST_F(AnnoKillTest, KeepsNativeCallingConventions) {
  check_native_annotations(false, false);
}

TEST_F(AnnoKillTest, KeepsNativeCallingConventionsWhenForced) {
  check_native_annotations(false, true);
}

TEST_F(AnnoKillTest, KeepsNativeCallingConventionsInForceOnlyMode) {
  check_native_annotations(true, true);
}

TEST_F(AnnoKillTest, KeepsNativeAnnotationsWithoutDefinitions) {
  check_native_annotations(false, false, false);
}

TEST_F(AnnoKillTest, KeepsForcedNativeAnnotationsWithoutDefinitions) {
  check_native_annotations(true, true, false);
}

// A call on an annotation-typed receiver names the annotation class even when
// the method is declared in `Annotation`.
TEST_F(AnnoKillTest, KeepsAnnotationNamedByCallOfInheritedMethod) {
  EXPECT_TRUE(keeps_annotation_named_by(R"((
    (const v0 0)
    (invoke-interface (v0) "LAnno;.annotationType:()Ljava/lang/Class;")
    (return-void)
  ))"));
}

TEST_F(AnnoKillTest, RemovesAnnotationNamedByNoCode) {
  EXPECT_FALSE(keeps_annotation_named_by(R"((
    (return-void)
  ))"));
}
