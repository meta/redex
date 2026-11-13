/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <cstdlib>
#include <gtest/gtest.h>
#include <iostream>
#include <string>

#include "ApkResources.h"
#include "RedexResources.h"
#include "VerifyUtil.h"

void verify_layout(const std::string& filename) {
  resources::StringOrReferenceSet classes;
  std::unordered_multimap<std::string, resources::StringOrReference>
      unused_attr_values;
  ApkResources resources("");
  resources.collect_layout_classes_and_attributes_for_file(
      filename, {}, &classes, &unused_attr_values);

  EXPECT_EQ(classes.size(), 1)
      << "Expected 1 View in layout file: " << filename;
  auto cls_name = *unordered_any(classes);
  EXPECT_FALSE(cls_name.is_reference());
  EXPECT_EQ(cls_name.str.find("X."), 0)
      << "Got unexpected class name in layout: " << cls_name.str;
}

namespace {

const DexType* get_instance_of_type(const DexClasses& classes) {
  auto* cls = find_class_named(
      classes, "Lcom/facebook/redex/test/instr/RenameClassesV2Test;");
  if (cls == nullptr) {
    return nullptr;
  }
  auto* method =
      find_vmethod_named(*cls, "testRenamesArrayTypeWithoutLowerDimension");
  if (method == nullptr) {
    return nullptr;
  }
  auto* insn = dynamic_cast<DexOpcodeType*>(
      find_instruction(method, DOPCODE_INSTANCE_OF));
  if (insn == nullptr) {
    return nullptr;
  }
  return insn->get_type();
}

} // namespace

TEST_F(PreVerify, RenameClassesV2ArrayTypeWithoutLowerDimension) {
  const auto* type = get_instance_of_type(classes);
  ASSERT_NE(type, nullptr);
  EXPECT_EQ(type->str(), "[[Lcom/facebook/redex/test/instr/IForceRename;");
  // The case under test: the one-dimensional array types do not exist.
  EXPECT_EQ(DexType::get_type("[Lcom/facebook/redex/test/instr/IForceRename;"),
            nullptr);
  EXPECT_EQ(DexType::get_type("[Lcom/facebook/redex/test/instr/ForceRename;"),
            nullptr);
}

TEST_F(PostVerify, RenameClassesV2ArrayTypeWithoutLowerDimension) {
  const auto* type = get_instance_of_type(classes);
  ASSERT_NE(type, nullptr);
  EXPECT_EQ(type->str().find("[[LX/"), 0)
      << "Got unexpected array type name: " << type->str();
}

TEST_F(PostVerify, RenameClassesV2) {
  std::cout << "Loaded classes: " << classes.size() << "\n";
  verify_layout(resources["res/layout/simple_layout.xml"]);
}
