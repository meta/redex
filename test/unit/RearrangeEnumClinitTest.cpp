/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "gtest/gtest.h"
#include <memory>

#include "IRCode.h"
#include "RearrangeEnumClinit.h"

#include "Creators.h"
#include "DexClass.h"
#include "IRAssembler.h"
#include "MethodUtil.h"
#include "RedexTest.h"
#include "ScopedCFG.h"
#include "TypeUtil.h"

namespace rearrange_enum_clinit {

class RearrangeEnumClinitTest : public RedexTest {
 public:
  RearrangeEnumClinitTest() {
    auto create_test_class = [](const std::string& class_name,
                                const std::string& value_type) {
      auto* self = DexType::make_type(class_name);
      ClassCreator cc{self};

      cc.set_super(type::java_lang_Object()); // Should be Enum but does not
                                              // matter.

      for (const auto& s : {"ALPHA", "BETA", "GAMMA"}) {
        cc.add_field(DexField::make_field(self, DexString::make_string(s), self)
                         ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL));
      }

      cc.add_field(DexField::make_field(self, DexString::make_string("$VALUES"),
                                        type::make_array_type(self))
                       ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL));

      cc.add_field(DexField::make_field(self, DexString::make_string("OTHER"),
                                        type::make_array_type(self))
                       ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL));

      cc.add_method(
          DexMethod::make_method(class_name + ".<init>:(" + value_type + "I)V")
              ->make_concrete(ACC_PUBLIC | ACC_CONSTRUCTOR, false));

      auto* clinit_method =
          DexMethod::make_method(class_name + ".<clinit>:()V")
              ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_CONSTRUCTOR, false);
      cc.add_method(clinit_method);

      auto* values_method =
          DexMethod::make_method(class_name + ".values:()[" + class_name)
              ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
      cc.add_method(values_method);

      cc.create();

      return std::make_pair(clinit_method, values_method);
    };

    std::tie(clinit, values) =
        create_test_class("LTest;", "Ljava/lang/String;");
    std::tie(clinit_int, values_int) = create_test_class("LTestInt;", "I");
  }

  MethodResult run(IRCode* code,
                   bool with_int = false,
                   MethodStats* method_stats = nullptr) {
    cfg::ScopedCFG cfg(code);
    return RearrangeEnumClinitPass::run(with_int ? clinit_int : clinit, code,
                                        method_stats);
  }

  static std::string normalize(const std::string& in) {
    auto code = assembler::ircode_from_string(in);
    return assembler::to_string(code.get());
  }

  DexMethod* clinit;
  DexMethod* values;

  DexMethod* clinit_int;
  DexMethod* values_int;
};

TEST_F(RearrangeEnumClinitTest, Sgets) {
  const auto* src = R"(
  (
    (const v4 2)
    (const v3 1)
    (const v2 0)
    (new-instance "LTest;")
    (move-result-pseudo-object v0)
    (const-string ALPHA)
    (move-result-pseudo-object v1)
    (invoke-direct (v0 v1 v2) "LTest;.<init>:(Ljava/lang/String;I)V")
    (sput-object v0 "LTest;.ALPHA:LTest;")
    (new-instance "LTest;")
    (move-result-pseudo-object v0)
    (const-string BETA)
    (move-result-pseudo-object v1)
    (invoke-direct (v0 v1 v3) "LTest;.<init>:(Ljava/lang/String;I)V")
    (sput-object v0 "LTest;.BETA:LTest;")
    (new-instance "LTest;")
    (move-result-pseudo-object v0)
    (const-string GAMMA)
    (move-result-pseudo-object v1)
    (invoke-direct (v0 v1 v4) "LTest;.<init>:(Ljava/lang/String;I)V")
    (sput-object v0 "LTest;.GAMMA:LTest;")
    (const v0 3)
    (new-array v0 "[LTest;")
    (move-result-pseudo-object v0)
    (sget-object "LTest;.ALPHA:LTest;")
    (move-result-pseudo-object v1)
    (aput-object v1 v0 v2)
    (sget-object "LTest;.BETA:LTest;")
    (move-result-pseudo-object v1)
    (aput-object v1 v0 v3)
    (sget-object "LTest;.GAMMA:LTest;")
    (move-result-pseudo-object v1)
    (aput-object v1 v0 v4)
    (sput-object v0 "LTest;.$VALUES:[LTest;")
    (return-void)
   )
    )";

  auto code = assembler::ircode_from_string(src);
  auto res = run(code.get());

  ASSERT_EQ(res, MethodResult::kFailed);
  EXPECT_EQ(normalize(src), assembler::to_string(code.get()));
}

TEST_F(RearrangeEnumClinitTest, Regs) {
  const auto* src = R"(
  (
    (const v4 2)
    (const v3 1)
    (const v2 0)
    (new-instance "LTest;")
    (move-result-pseudo-object v0)
    (const-string ALPHA)
    (move-result-pseudo-object v1)
    (invoke-direct (v0 v1 v2) "LTest;.<init>:(Ljava/lang/String;I)V")
    (sput-object v0 "LTest;.ALPHA:LTest;")
    (move-object v16 v0)
    (new-instance "LTest;")
    (move-result-pseudo-object v0)
    (const-string BETA)
    (move-result-pseudo-object v1)
    (invoke-direct (v0 v1 v3) "LTest;.<init>:(Ljava/lang/String;I)V")
    (sput-object v0 "LTest;.BETA:LTest;")
    (move-object v17 v0)
    (new-instance "LTest;")
    (move-result-pseudo-object v0)
    (const-string GAMMA)
    (move-result-pseudo-object v1)
    (invoke-direct (v0 v1 v4) "LTest;.<init>:(Ljava/lang/String;I)V")
    (sput-object v0 "LTest;.GAMMA:LTest;")
    (move-object v18 v0)
    (const v0 3)
    (new-array v0 "[LTest;")
    (move-result-pseudo-object v0)
    (move-object v1 v16)
    (aput-object v1 v0 v2)
    (move-object v1 v17)
    (aput-object v1 v0 v3)
    (move-object v1 v18)
    (aput-object v1 v0 v4)
    (sput-object v0 "LTest;.$VALUES:[LTest;")
    (return-void)
   )
    )";

  auto code = assembler::ircode_from_string(src);
  auto res = run(code.get());

  ASSERT_EQ(res, MethodResult::kChanged);

  const auto* dst = R"(
  (
    (const v19 3)
    (new-array v19 "[LTest;")
    (move-result-pseudo-object v20)
    (const v4 2)
    (const v3 1)
    (const v2 0)
    (new-instance "LTest;")
    (move-result-pseudo-object v0)
    (const-string ALPHA)
    (move-result-pseudo-object v1)
    (invoke-direct (v0 v1 v2) "LTest;.<init>:(Ljava/lang/String;I)V")
    (const v21 0)
    (aput-object v0 v20 v21)
    (sput-object v0 "LTest;.ALPHA:LTest;")
    (move-object v16 v0)
    (new-instance "LTest;")
    (move-result-pseudo-object v0)
    (const-string BETA)
    (move-result-pseudo-object v1)
    (invoke-direct (v0 v1 v3) "LTest;.<init>:(Ljava/lang/String;I)V")
    (const v21 1)
    (aput-object v0 v20 v21)
    (sput-object v0 "LTest;.BETA:LTest;")
    (move-object v17 v0)
    (new-instance "LTest;")
    (move-result-pseudo-object v0)
    (const-string GAMMA)
    (move-result-pseudo-object v1)
    (invoke-direct (v0 v1 v4) "LTest;.<init>:(Ljava/lang/String;I)V")
    (const v21 2)
    (aput-object v0 v20 v21)
    (sput-object v0 "LTest;.GAMMA:LTest;")
    (move-object v18 v0)
    (const v0 3)
    (move-object v1 v16)
    (move-object v1 v17)
    (move-object v1 v18)
    (sput-object v20 "LTest;.$VALUES:[LTest;")
    (return-void)
  )
    )";

  EXPECT_EQ(normalize(dst), assembler::to_string(code.get()));
}

// The array size may be reused, e.g., if it's the same as a value
// for the enum.
TEST_F(RearrangeEnumClinitTest, SizeReused) {
  const auto* src = R"(
  (
    (const v4 2)
    (const v3 1)
    (const v2 0)
    (new-instance "LTestInt;")
    (move-result-pseudo-object v0)
    (const v1 1)
    (invoke-direct (v0 v1 v2) "LTestInt;.<init>:(II)V")
    (sput-object v0 "LTestInt;.ALPHA:LTestInt;")
    (move-object v16 v0)
    (new-instance "LTestInt;")
    (move-result-pseudo-object v0)
    (const v1 2)
    (invoke-direct (v0 v1 v3) "LTestInt;.<init>:(II)V")
    (sput-object v0 "LTestInt;.BETA:LTestInt;")
    (move-object v17 v0)
    (new-instance "LTestInt;")
    (move-result-pseudo-object v0)
    (const v1 3)
    (invoke-direct (v0 v1 v4) "LTestInt;.<init>:(II)V")
    (sput-object v0 "LTestInt;.GAMMA:LTestInt;")
    (move-object v18 v0)
    (new-array v1 "[LTestInt;")
    (move-result-pseudo-object v0)
    (move-object v1 v16)
    (aput-object v1 v0 v2)
    (move-object v1 v17)
    (aput-object v1 v0 v3)
    (move-object v1 v18)
    (aput-object v1 v0 v4)
    (sput-object v0 "LTestInt;.$VALUES:[LTestInt;")
    (return-void)
   )
    )";

  auto code = assembler::ircode_from_string(src);
  auto res = run(code.get(), /*with_int=*/true);

  ASSERT_EQ(res, MethodResult::kChanged);

  const auto* dst = R"(
  (
    (const v19 3)
    (new-array v19 "[LTestInt;")
    (move-result-pseudo-object v20)
    (const v4 2)
    (const v3 1)
    (const v2 0)
    (new-instance "LTestInt;")
    (move-result-pseudo-object v0)
    (const v1 1)
    (invoke-direct (v0 v1 v2) "LTestInt;.<init>:(II)V")
    (const v21 0)
    (aput-object v0 v20 v21)
    (sput-object v0 "LTestInt;.ALPHA:LTestInt;")
    (move-object v16 v0)
    (new-instance "LTestInt;")
    (move-result-pseudo-object v0)
    (const v1 2)
    (invoke-direct (v0 v1 v3) "LTestInt;.<init>:(II)V")
    (const v21 1)
    (aput-object v0 v20 v21)
    (sput-object v0 "LTestInt;.BETA:LTestInt;")
    (move-object v17 v0)
    (new-instance "LTestInt;")
    (move-result-pseudo-object v0)
    (const v1 3)
    (invoke-direct (v0 v1 v4) "LTestInt;.<init>:(II)V")
    (const v21 2)
    (aput-object v0 v20 v21)
    (sput-object v0 "LTestInt;.GAMMA:LTestInt;")
    (move-object v18 v0)
    (move-object v1 v16)
    (move-object v1 v17)
    (move-object v1 v18)
    (sput-object v20 "LTestInt;.$VALUES:[LTestInt;")
    (return-void)
  )
    )";

  EXPECT_EQ(normalize(dst), assembler::to_string(code.get()));
}

// Subclass to separate things a little.
class RearrangeEnumClinitFieldTest : public RearrangeEnumClinitTest {
 protected:
  testing::AssertionResult check_other(const std::string& values_src) {
    auto values_code = assembler::ircode_from_string(values_src);
    values->set_code(std::move(values_code));

    const auto* src = R"(
    (
      (const v4 2)
      (const v3 1)
      (const v2 0)
      (new-instance "LTest;")
      (move-result-pseudo-object v0)
      (const-string ALPHA)
      (move-result-pseudo-object v1)
      (invoke-direct (v0 v1 v2) "LTest;.<init>:(Ljava/lang/String;I)V")
      (sput-object v0 "LTest;.ALPHA:LTest;")
      (move-object v16 v0)
      (new-instance "LTest;")
      (move-result-pseudo-object v0)
      (const-string BETA)
      (move-result-pseudo-object v1)
      (invoke-direct (v0 v1 v3) "LTest;.<init>:(Ljava/lang/String;I)V")
      (sput-object v0 "LTest;.BETA:LTest;")
      (move-object v17 v0)
      (new-instance "LTest;")
      (move-result-pseudo-object v0)
      (const-string GAMMA)
      (move-result-pseudo-object v1)
      (invoke-direct (v0 v1 v4) "LTest;.<init>:(Ljava/lang/String;I)V")
      (sput-object v0 "LTest;.GAMMA:LTest;")
      (move-object v18 v0)
      (const v0 3)
      (new-array v0 "[LTest;")
      (move-result-pseudo-object v0)
      (move-object v1 v16)
      (aput-object v1 v0 v2)
      (move-object v1 v17)
      (aput-object v1 v0 v3)
      (move-object v1 v18)
      (aput-object v1 v0 v4)
      (sput-object v0 "LTest;.OTHER:[LTest;")
      (return-void)
    )
      )";

    auto code = assembler::ircode_from_string(src);
    auto res = run(code.get());

    if (res != MethodResult::kChanged) {
      return testing::AssertionFailure()
             << "Optimization not applied: " << static_cast<int>(res);
    }

    const auto* dst = R"(
    (
      (const v19 3)
      (new-array v19 "[LTest;")
      (move-result-pseudo-object v20)
      (const v4 2)
      (const v3 1)
      (const v2 0)
      (new-instance "LTest;")
      (move-result-pseudo-object v0)
      (const-string ALPHA)
      (move-result-pseudo-object v1)
      (invoke-direct (v0 v1 v2) "LTest;.<init>:(Ljava/lang/String;I)V")
      (const v21 0)
      (aput-object v0 v20 v21)
      (sput-object v0 "LTest;.ALPHA:LTest;")
      (move-object v16 v0)
      (new-instance "LTest;")
      (move-result-pseudo-object v0)
      (const-string BETA)
      (move-result-pseudo-object v1)
      (invoke-direct (v0 v1 v3) "LTest;.<init>:(Ljava/lang/String;I)V")
      (const v21 1)
      (aput-object v0 v20 v21)
      (sput-object v0 "LTest;.BETA:LTest;")
      (move-object v17 v0)
      (new-instance "LTest;")
      (move-result-pseudo-object v0)
      (const-string GAMMA)
      (move-result-pseudo-object v1)
      (invoke-direct (v0 v1 v4) "LTest;.<init>:(Ljava/lang/String;I)V")
      (const v21 2)
      (aput-object v0 v20 v21)
      (sput-object v0 "LTest;.GAMMA:LTest;")
      (move-object v18 v0)
      (const v0 3)
      (move-object v1 v16)
      (move-object v1 v17)
      (move-object v1 v18)
      (sput-object v20 "LTest;.OTHER:[LTest;")
      (return-void)
    )
      )";

    auto normalized = normalize(dst);
    auto code_str = assembler::to_string(code.get());
    if (normalized != code_str) {
      return testing::AssertionFailure() << "Unexpected output:\nExpected:\n"
                                         << normalized << "\nActual:\n"
                                         << code_str;
    }
    return testing::AssertionSuccess();
  }
};

TEST_F(RearrangeEnumClinitFieldTest, OtherDirect) {
  const auto* values_src = R"(
    (
      (sget-object "LTest;.OTHER:[LTest;")
      (move-result-pseudo-object v0)
      (return-object v0)
    )
  )";
  ASSERT_TRUE(check_other(values_src));
}

TEST_F(RearrangeEnumClinitFieldTest, OtherClone) {
  const auto* values_src = R"(
    (
      (sget-object "LTest;.OTHER:[LTest;")
      (move-result-pseudo-object v0)
      (invoke-virtual (v0) "LTest;.clone:()Ljava/lang/Object;")
      (move-result-pseudo-object v0)
      (check-cast v0 "[LTest;")
      (return-object v0)
    )
  )";
  ASSERT_TRUE(check_other(values_src));
}

TEST_F(RearrangeEnumClinitTest, SourceBlocksCoverage) {
  const auto* src = R"(
  (
    (.src_block "LTest;.<clinit>:()V" 0 (1.0 1.0))
    (const v4 2)
    (const v3 1)
    (const v2 0)
    (new-instance "LTest;")
    (move-result-pseudo-object v0)
    (.src_block "LTest;.<clinit>:()V" 1 (1.0 1.0))
    (const-string ALPHA)
    (move-result-pseudo-object v1)
    (invoke-direct (v0 v1 v2) "LTest;.<init>:(Ljava/lang/String;I)V")
    (.src_block "LTest;.<clinit>:()V" 2 (1.0 1.0))
    (sput-object v0 "LTest;.ALPHA:LTest;")
    (move-object v16 v0)
    (new-instance "LTest;")
    (move-result-pseudo-object v0)
    (.src_block "LTest;.<clinit>:()V" 3 (1.0 1.0))
    (const-string BETA)
    (move-result-pseudo-object v1)
    (invoke-direct (v0 v1 v3) "LTest;.<init>:(Ljava/lang/String;I)V")
    (.src_block "LTest;.<clinit>:()V" 4 (1.0 1.0))
    (sput-object v0 "LTest;.BETA:LTest;")
    (move-object v17 v0)
    (new-instance "LTest;")
    (move-result-pseudo-object v0)
    (.src_block "LTest;.<clinit>:()V" 5 (1.0 1.0))
    (const-string GAMMA)
    (move-result-pseudo-object v1)
    (invoke-direct (v0 v1 v4) "LTest;.<init>:(Ljava/lang/String;I)V")
    (.src_block "LTest;.<clinit>:()V" 6 (1.0 1.0))
    (sput-object v0 "LTest;.GAMMA:LTest;")
    (move-object v18 v0)
    (const v0 3)
    (new-array v0 "[LTest;")
    (move-result-pseudo-object v0)
    (move-object v1 v16)
    (aput-object v1 v0 v2)
    (move-object v1 v17)
    (aput-object v1 v0 v3)
    (move-object v1 v18)
    (aput-object v1 v0 v4)
    (sput-object v0 "LTest;.$VALUES:[LTest;")
    (return-void)
   )
    )";

  auto code = assembler::ircode_from_string(src);
  auto res = run(code.get());

  ASSERT_EQ(res, MethodResult::kChanged);

  cfg::ScopedCFG cfg(code.get());
  auto* block = cfg->entry_block();

  bool found_new_array = false;
  bool sb_after_new_array = false;
  int invoke_direct_count = 0;
  int sb_after_invoke_direct_count = 0;
  bool last_was_new_array_mrp = false;
  bool last_was_invoke_direct = false;

  for (auto& mie : *block) {
    if (mie.type == MFLOW_OPCODE) {
      if (mie.insn->opcode() == OPCODE_NEW_ARRAY) {
        found_new_array = true;
      } else if (found_new_array &&
                 opcode::is_a_move_result_pseudo(mie.insn->opcode()) &&
                 !last_was_new_array_mrp) {
        last_was_new_array_mrp = true;
        continue;
      } else if (opcode::is_an_invoke(mie.insn->opcode()) &&
                 method::is_constructor(mie.insn->get_method())) {
        invoke_direct_count++;
        last_was_invoke_direct = true;
        continue;
      }
      last_was_new_array_mrp = false;
      last_was_invoke_direct = false;
    } else if (mie.type == MFLOW_SOURCE_BLOCK) {
      if (last_was_new_array_mrp) {
        sb_after_new_array = true;
      }
      if (last_was_invoke_direct) {
        sb_after_invoke_direct_count++;
      }
      last_was_new_array_mrp = false;
      last_was_invoke_direct = false;
    }
  }

  EXPECT_TRUE(found_new_array);
  EXPECT_TRUE(sb_after_new_array)
      << "Expected source block after NEW_ARRAY's MOVE_RESULT_PSEUDO";
  EXPECT_EQ(invoke_direct_count, 3);
  EXPECT_EQ(sb_after_invoke_direct_count, 3)
      << "Expected source block after each INVOKE_DIRECT";
}

TEST_F(RearrangeEnumClinitTest, NativeValuesWithoutCodeIsNotAnalyzed) {
  values->set_access(ACC_PUBLIC | ACC_STATIC | ACC_NATIVE);
  ASSERT_EQ(values->get_code(), nullptr);
  const auto* source = R"((
    (const v0 1)
    (new-array v0 "[LTest;")
    (move-result-pseudo-object v0)
    (sput-object v0 "LTest;.OTHER:[LTest;")
    (return-void)
  ))";
  auto code = assembler::ircode_from_string(source);
  MethodStats stats;
  EXPECT_EQ(run(code.get(), false, &stats), MethodResult::kFailed);
  EXPECT_EQ(normalize(source), assembler::to_string(code.get()));
  EXPECT_EQ(stats.values_without_code, 1);
  EXPECT_EQ(stats.values_without_return, 0);
}

TEST_F(RearrangeEnumClinitTest, ThrowOnlyValuesWithoutReturnIsNotAnalyzed) {
  values->set_code(assembler::ircode_from_string(R"((
    (new-instance "Ljava/lang/RuntimeException;")
    (move-result-pseudo-object v0)
    (invoke-direct (v0) "Ljava/lang/RuntimeException;.<init>:()V")
    (throw v0)
  ))"));
  const auto* source = R"((
    (const v0 1)
    (new-array v0 "[LTest;")
    (move-result-pseudo-object v0)
    (sput-object v0 "LTest;.OTHER:[LTest;")
    (return-void)
  ))";
  auto code = assembler::ircode_from_string(source);
  MethodStats stats;
  EXPECT_EQ(run(code.get(), false, &stats), MethodResult::kFailed);
  EXPECT_EQ(normalize(source), assembler::to_string(code.get()));
  EXPECT_EQ(stats.values_without_code, 0);
  EXPECT_EQ(stats.values_without_return, 1);
}

} // namespace rearrange_enum_clinit
