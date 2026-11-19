/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "AnnoKill.h"
#include "Creators.h"
#include "DexAnnotation.h"
#include "DexClass.h"
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
