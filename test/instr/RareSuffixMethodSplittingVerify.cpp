/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "VerifyUtil.h"

namespace {

// The split method of `cls` named with `split_prefix` that `method` calls.
DexMethod* find_split(const DexClass& cls,
                      DexMethod* method,
                      std::string_view split_prefix) {
  for (auto* m : cls.get_dmethods()) {
    if (m->str().starts_with(split_prefix) &&
        find_invoke(method, DOPCODE_INVOKE_STATIC, m->str()) != nullptr) {
      return m;
    }
  }
  return nullptr;
}

} // namespace

TEST_F(PostVerify, SplitsThrowingSuffixes) {
  auto* throwing_suffixes =
      find_class_named(classes, "Lredex/ThrowingSuffixes;");
  ASSERT_NE(throwing_suffixes, nullptr);
  auto* checked = find_vmethod_named(*throwing_suffixes, "checked");
  ASSERT_NE(checked, nullptr);
  EXPECT_NE(find_split(*throwing_suffixes, checked, "checked$split$"), nullptr);

  auto* checked_init = find_class_named(classes, "Lredex/CheckedInit;");
  ASSERT_NE(checked_init, nullptr);
  auto* init = find_dmethod_named(*checked_init, "<init>");
  ASSERT_NE(init, nullptr);
  EXPECT_NE(find_split(*checked_init, init, "$init$$split$"), nullptr);
}

// The wrappers of Kotlin's parameter checks return after their null arm calls
// the builtin, so they are not split.
TEST_F(PostVerify, KeepsParameterCheckWrappers) {
  auto* intrinsics =
      find_class_named(classes, "Lkotlin/jvm/internal/Intrinsics;");
  ASSERT_NE(intrinsics, nullptr);
  for (const auto& [wrapper_name, builtin] :
       {std::pair{"$WrCheckParameter_V1_4", "checkNotNullParameter"},
        std::pair{"$WrCheckParameter_V1_3", "checkParameterIsNotNull"}}) {
    auto* wrapper = find_dmethod_named(*intrinsics, wrapper_name);
    ASSERT_NE(wrapper, nullptr);
    EXPECT_NE(find_invoke(wrapper, DOPCODE_INVOKE_STATIC, builtin), nullptr);
  }
}
