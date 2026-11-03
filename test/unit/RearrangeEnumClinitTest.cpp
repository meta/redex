/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "gtest/gtest.h"
#include <array>
#include <memory>
#include <string_view>

#include "Debug.h"
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
                   MethodStats* method_stats = nullptr,
                   FailureReason* failure_reason = nullptr) {
    if (code == nullptr) {
      return RearrangeEnumClinitPass::run(with_int ? clinit_int : clinit, code,
                                          method_stats, failure_reason);
    }
    cfg::ScopedCFG cfg(code);
    return RearrangeEnumClinitPass::run(with_int ? clinit_int : clinit, code,
                                        method_stats, failure_reason);
  }

  static std::string mixed_array_initializer(const std::string& extra = "",
                                             const std::string& array = "v3") {
    const std::string prefix = R"((
      (const v2 0)
      (const-string ALPHA)
      (move-result-pseudo-object v1)
      (new-instance "LTest;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0 v1 v2) "LTest;.<init>:(Ljava/lang/String;I)V")
      (sput-object v0 "LTest;.ALPHA:LTest;")
      (const v3 2)
      (new-array v3 "[LTest;")
      (move-result-pseudo-object v3)
    )";
    return prefix + extra + "(aput-object v0 " + array + R"( v2)
      (sget-object "LTest;.BETA:LTest;")
      (move-result-pseudo-object v0)
      (const v2 1)
      (aput-object v0 )" +
           array + R"( v2)
      (sput-object )" +
           array + R"( "LTest;.$VALUES:[LTest;")
      (return-void)
    ))";
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

TEST_F(RearrangeEnumClinitTest, RejectDynamicSizeBeforeMutation) {
#ifdef NDEBUG
  ASSERT_FALSE(debug);
#endif
  const auto* source = R"((
    (const v2 0)
    (const-string ALPHA)
    (move-result-pseudo-object v1)
    (new-instance "LTest;")
    (move-result-pseudo-object v0)
    (invoke-direct (v0 v1 v2) "LTest;.<init>:(Ljava/lang/String;I)V")
    (invoke-static () "LInputs;.size:()I")
    (move-result v3)
    (new-array v3 "[LTest;")
    (move-result-pseudo-object v3)
    (aput-object v0 v3 v2)
    (sput-object v3 "LTest;.$VALUES:[LTest;")
    (return-void)
  ))";
  auto code = assembler::ircode_from_string(source);
  EXPECT_EQ(run(code.get()), MethodResult::kFailed);
  EXPECT_EQ(normalize(source), assembler::to_string(code.get()));
}

TEST_F(RearrangeEnumClinitTest, RejectDynamicIndexBeforeMutation) {
#ifdef NDEBUG
  ASSERT_FALSE(debug);
#endif
  const auto* source = R"((
    (const v2 0)
    (const-string ALPHA)
    (move-result-pseudo-object v1)
    (new-instance "LTest;")
    (move-result-pseudo-object v0)
    (invoke-direct (v0 v1 v2) "LTest;.<init>:(Ljava/lang/String;I)V")
    (const v3 1)
    (new-array v3 "[LTest;")
    (move-result-pseudo-object v3)
    (invoke-static () "LInputs;.index:()I")
    (move-result v2)
    (aput-object v0 v3 v2)
    (sput-object v3 "LTest;.$VALUES:[LTest;")
    (return-void)
  ))";
  auto code = assembler::ircode_from_string(source);
  EXPECT_EQ(run(code.get()), MethodResult::kFailed);
  EXPECT_EQ(normalize(source), assembler::to_string(code.get()));
}

TEST_F(RearrangeEnumClinitTest, LastInvalidStoreLeavesInitializerUnchanged) {
#ifdef NDEBUG
  ASSERT_FALSE(debug);
#endif
  const auto* source = R"((
    (const v2 0)
    (const-string ALPHA)
    (move-result-pseudo-object v1)
    (new-instance "LTest;")
    (move-result-pseudo-object v0)
    (invoke-direct (v0 v1 v2) "LTest;.<init>:(Ljava/lang/String;I)V")
    (const-string BETA)
    (move-result-pseudo-object v1)
    (new-instance "LTest;")
    (move-result-pseudo-object v4)
    (invoke-direct (v4 v1 v2) "LTest;.<init>:(Ljava/lang/String;I)V")
    (const v3 2)
    (new-array v3 "[LTest;")
    (move-result-pseudo-object v3)
    (aput-object v0 v3 v2)
    (invoke-static () "LInputs;.index:()I")
    (move-result v2)
    (aput-object v4 v3 v2)
    (sput-object v3 "LTest;.$VALUES:[LTest;")
    (return-void)
  ))";
  auto code = assembler::ircode_from_string(source);
  EXPECT_EQ(run(code.get()), MethodResult::kFailed);
  EXPECT_EQ(normalize(source), assembler::to_string(code.get()));
}

TEST_F(RearrangeEnumClinitTest, RejectUnsupportedShapesBeforeMutation) {
  const std::string prefix = R"((
    (const v2 0)
    (const-string ALPHA)
    (move-result-pseudo-object v1)
    (new-instance "LTest;")
    (move-result-pseudo-object v0)
    (invoke-direct (v0 v1 v2) "LTest;.<init>:(Ljava/lang/String;I)V")
    (sput-object v0 "LTest;.ALPHA:LTest;")
    (const v3 1)
    (new-array v3 "[LTest;")
    (move-result-pseudo-object v3)
  )";
  const std::string suffix = R"(
    (sput-object v3 "LTest;.$VALUES:[LTest;")
    (return-void)
  ))";
  const auto cases = std::to_array<std::pair<std::string_view, FailureReason>>({
      {"(const v2 -1) (aput-object v0 v3 v2)",
       FailureReason::UnsupportedElementOrIndex},
      {"(const v2 1) (aput-object v0 v3 v2)",
       FailureReason::UnsupportedElementOrIndex},
      {"(aput-object v0 v3 v2) (aput-object v0 v3 v2)",
       FailureReason::UnsupportedElementOrIndex},
      {R"((aput-object v0 v3 v2) (invoke-static (v3) "LObserver;.see:([LTest;)V"))",
       FailureReason::ArrayEscapes},
      {"", FailureReason::IncompleteArray},
  });
  for (const auto& [stores, expected] : cases) {
    const auto src = prefix + std::string(stores) + suffix;
    auto code = assembler::ircode_from_string(src);
    FailureReason reason;
    EXPECT_EQ(run(code.get(), false, nullptr, &reason), MethodResult::kFailed)
        << stores;
    EXPECT_EQ(reason, expected) << stores;
    EXPECT_EQ(normalize(src), assembler::to_string(code.get())) << stores;
  }
}

TEST_F(RearrangeEnumClinitTest, HelperProducerIsNotAnArray) {
  const auto* const src = R"((
    (invoke-static () "LTest;.$values:()[LTest;")
    (move-result-object v0)
    (sput-object v0 "LTest;.$VALUES:[LTest;")
    (return-void)
  ))";
  auto code = assembler::ircode_from_string(src);
  FailureReason reason;
  EXPECT_EQ(run(code.get(), false, nullptr, &reason), MethodResult::kFailed);
  EXPECT_EQ(reason, FailureReason::ValuesNotNewArray);
  EXPECT_EQ(normalize(src), assembler::to_string(code.get()));
}

TEST_F(RearrangeEnumClinitTest, RejectInitializationAfterPublication) {
  const auto* const src = R"((
    (const v2 0)
    (const-string ALPHA)
    (move-result-pseudo-object v1)
    (new-instance "LTest;")
    (move-result-pseudo-object v0)
    (invoke-direct (v0 v1 v2) "LTest;.<init>:(Ljava/lang/String;I)V")
    (const v3 1)
    (new-array v3 "[LTest;")
    (move-result-pseudo-object v3)
    (sput-object v3 "LTest;.$VALUES:[LTest;")
    (invoke-static () "LObserver;.readValues:()V")
    (aput-object v0 v3 v2)
    (return-void)
  ))";
  auto code = assembler::ircode_from_string(src);
  FailureReason reason;
  EXPECT_EQ(run(code.get(), false, nullptr, &reason), MethodResult::kFailed);
  EXPECT_EQ(reason, FailureReason::InitializationAfterPublication);
  EXPECT_EQ(normalize(src), assembler::to_string(code.get()));
}

TEST_F(RearrangeEnumClinitTest, RelaxedSuperclassConstructorIsSupported) {
  auto* subtype = DexType::make_type("LCase;");
  ClassCreator cc{subtype};
  cc.set_super(clinit->get_class());
  cc.create();
  auto code = assembler::ircode_from_string(R"((
    (const v2 0)
    (const-string ALPHA)
    (move-result-pseudo-object v1)
    (new-instance "LCase;")
    (move-result-pseudo-object v0)
    (invoke-direct (v0 v1 v2) "LTest;.<init>:(Ljava/lang/String;I)V")
    (const v3 1)
    (new-array v3 "[LTest;")
    (move-result-pseudo-object v3)
    (aput-object v0 v3 v2)
    (sput-object v3 "LTest;.$VALUES:[LTest;")
    (return-void)
  ))");
  FailureReason reason;
  EXPECT_EQ(run(code.get(), false, nullptr, &reason), MethodResult::kChanged);
  EXPECT_EQ(reason, FailureReason::None);
}

TEST_F(RearrangeEnumClinitTest, RejectConstructorAfterArrayStore) {
  const auto* source = R"((
    (const v2 0)
    (const-string ALPHA)
    (move-result-pseudo-object v1)
    (new-instance "LTest;")
    (move-result-pseudo-object v0)
    (const v3 1)
    (new-array v3 "[LTest;")
    (move-result-pseudo-object v3)
    (aput-object v0 v3 v2)
    (invoke-direct (v0 v1 v2) "LTest;.<init>:(Ljava/lang/String;I)V")
    (sput-object v3 "LTest;.$VALUES:[LTest;")
    (return-void)
  ))";
  auto code = assembler::ircode_from_string(source);
  FailureReason reason;
  EXPECT_EQ(run(code.get(), false, nullptr, &reason), MethodResult::kFailed);
  EXPECT_EQ(reason, FailureReason::UninitializedElement);
  EXPECT_EQ(normalize(source), assembler::to_string(code.get()));
}

TEST_F(RearrangeEnumClinitTest, RejectConstructorOnDifferentBranch) {
  const auto* source = R"((
    (const v2 0)
    (const-string ALPHA)
    (move-result-pseudo-object v1)
    (new-instance "LTest;")
    (move-result-pseudo-object v0)
    (const v4 0)
    (if-eqz v4 :skip)
    (invoke-direct (v0 v1 v2) "LTest;.<init>:(Ljava/lang/String;I)V")
    (:skip)
    (const v3 1)
    (new-array v3 "[LTest;")
    (move-result-pseudo-object v3)
    (aput-object v0 v3 v2)
    (sput-object v3 "LTest;.$VALUES:[LTest;")
    (return-void)
  ))";
  auto code = assembler::ircode_from_string(source);
  FailureReason reason;
  EXPECT_EQ(run(code.get(), false, nullptr, &reason),
            MethodResult::kNotOneBlock);
  EXPECT_EQ(reason, FailureReason::NotOneBlock);
  EXPECT_EQ(normalize(source), assembler::to_string(code.get()));
}

TEST_F(RearrangeEnumClinitTest, RejectConstructorInLoop) {
  const auto* source = R"((
    (:loop)
    (const v2 0)
    (const-string ALPHA)
    (move-result-pseudo-object v1)
    (new-instance "LTest;")
    (move-result-pseudo-object v0)
    (invoke-direct (v0 v1 v2) "LTest;.<init>:(Ljava/lang/String;I)V")
    (const v3 1)
    (new-array v3 "[LTest;")
    (move-result-pseudo-object v3)
    (aput-object v0 v3 v2)
    (sput-object v3 "LTest;.$VALUES:[LTest;")
    (goto :loop)
  ))";
  auto code = assembler::ircode_from_string(source);
  {
    cfg::ScopedCFG cfg(code.get());
    ASSERT_EQ(cfg->num_blocks(), 1);
    FailureReason reason;
    EXPECT_EQ(run(code.get(), false, nullptr, &reason), MethodResult::kFailed);
    EXPECT_EQ(reason, FailureReason::CyclicInitializer);
  }
  EXPECT_EQ(normalize(source), assembler::to_string(code.get()));
}

TEST_F(RearrangeEnumClinitTest, RejectIncompatibleConstructorOwner) {
  auto* other = DexType::make_type("LOther;");
  ClassCreator cc{other};
  cc.set_super(type::java_lang_Object());
  cc.add_method(DexMethod::make_method("LOther;.<init>:(Ljava/lang/String;I)V")
                    ->make_concrete(ACC_PUBLIC | ACC_CONSTRUCTOR, false));
  cc.create();
  const auto* source = R"((
    (const v2 0)
    (const-string ALPHA)
    (move-result-pseudo-object v1)
    (new-instance "LTest;")
    (move-result-pseudo-object v0)
    (invoke-direct (v0 v1 v2) "LOther;.<init>:(Ljava/lang/String;I)V")
    (const v3 1)
    (new-array v3 "[LTest;")
    (move-result-pseudo-object v3)
    (aput-object v0 v3 v2)
    (sput-object v3 "LTest;.$VALUES:[LTest;")
    (return-void)
  ))";
  auto code = assembler::ircode_from_string(source);
  FailureReason reason;
  EXPECT_EQ(run(code.get(), false, nullptr, &reason), MethodResult::kFailed);
  EXPECT_EQ(reason, FailureReason::UnsupportedConstructor);
  EXPECT_EQ(normalize(source), assembler::to_string(code.get()));
}

TEST_F(RearrangeEnumClinitTest, RejectIncompatibleElementBeforeMutation) {
  const auto* source = R"((
    (const-string NOT_AN_ENUM)
    (move-result-pseudo-object v0)
    (invoke-static () "LObserver;.mark:()V")
    (const v1 1)
    (new-array v1 "[LTest;")
    (move-result-pseudo-object v1)
    (const v2 0)
    (aput-object v0 v1 v2)
    (sput-object v1 "LTest;.$VALUES:[LTest;")
    (return-void)
  ))";
  auto code = assembler::ircode_from_string(source);
  FailureReason reason;
  EXPECT_EQ(run(code.get(), false, nullptr, &reason), MethodResult::kFailed);
  EXPECT_EQ(reason, FailureReason::UnsupportedElementProducer);
  EXPECT_EQ(normalize(source), assembler::to_string(code.get()));
}

TEST_F(RearrangeEnumClinitTest, NoCodeInitializerIsRejected) {
  FailureReason reason;
  EXPECT_EQ(run(nullptr, false, nullptr, &reason), MethodResult::kFailed);
  EXPECT_EQ(reason, FailureReason::ClinitWithoutCode);
}

TEST_F(RearrangeEnumClinitTest,
       RejectIncompatibleArrayComponentBeforeMutation) {
  const auto* source = R"((
    (const v2 0)
    (const-string ALPHA)
    (move-result-pseudo-object v1)
    (new-instance "LTest;")
    (move-result-pseudo-object v0)
    (invoke-direct (v0 v1 v2) "LTest;.<init>:(Ljava/lang/String;I)V")
    (const v3 1)
    (new-array v3 "[Ljava/lang/String;")
    (move-result-pseudo-object v3)
    (aput-object v0 v3 v2)
    (sput-object v3 "LTest;.$VALUES:[LTest;")
    (return-void)
  ))";
  auto code = assembler::ircode_from_string(source);
  FailureReason reason;
  EXPECT_EQ(run(code.get(), false, nullptr, &reason), MethodResult::kFailed);
  EXPECT_EQ(reason, FailureReason::UnsupportedArraySizeOrType);
  EXPECT_EQ(normalize(source), assembler::to_string(code.get()));
}

TEST_F(RearrangeEnumClinitTest, FactoryProducedElementRemainsSupported) {
  auto code = assembler::ircode_from_string(R"((
    (const v2 0)
    (invoke-static () "LInputs;.create:()LTest;")
    (move-result-object v0)
    (const v3 1)
    (new-array v3 "[LTest;")
    (move-result-pseudo-object v3)
    (aput-object v0 v3 v2)
    (sput-object v3 "LTest;.$VALUES:[LTest;")
    (return-void)
  ))");
  EXPECT_EQ(run(code.get()), MethodResult::kChanged);
  cfg::ScopedCFG cfg(code.get());
  std::vector<IROpcode> opcodes;
  for (auto& mie : cfg::InstructionIterable(*cfg)) {
    opcodes.push_back(mie.insn->opcode());
  }
  EXPECT_EQ(opcodes, (std::vector<IROpcode>{
                         OPCODE_CONST, OPCODE_NEW_ARRAY,
                         IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, OPCODE_CONST,
                         OPCODE_INVOKE_STATIC, OPCODE_MOVE_RESULT_OBJECT,
                         OPCODE_CONST, OPCODE_APUT_OBJECT, OPCODE_CONST,
                         OPCODE_SPUT_OBJECT, OPCODE_RETURN_VOID}));
}

TEST_F(RearrangeEnumClinitTest, MixedFieldReadsUseMovedArray) {
  auto code = assembler::ircode_from_string(mixed_array_initializer());
  MethodStats stats;
  ASSERT_EQ(run(code.get(), false, &stats), MethodResult::kChanged);
  EXPECT_EQ(stats.retained_field_stores, 1);
  EXPECT_EQ(stats.aliases, 0);
  EXPECT_EQ(stats.unsupported_uses, 0);
  cfg::ScopedCFG cfg(code.get());
  std::optional<reg_t> array;
  size_t stores = 0;
  for (auto& mie : cfg::InstructionIterable(*cfg)) {
    if (mie.insn->opcode() == OPCODE_NEW_ARRAY) {
      array = cfg->move_result_of(cfg->find_insn(mie.insn))->insn->dest();
    } else if (mie.insn->opcode() == OPCODE_APUT_OBJECT) {
      ASSERT_TRUE(array);
      EXPECT_EQ(mie.insn->src(1), *array);
      ++stores;
    } else if (mie.insn->opcode() == OPCODE_SPUT_OBJECT &&
               mie.insn->get_field()->get_name()->str() == "$VALUES") {
      ASSERT_TRUE(array);
      EXPECT_EQ(mie.insn->src(0), *array);
    }
  }
  EXPECT_EQ(stores, 2);
}

TEST_F(RearrangeEnumClinitTest, RetargetArrayAliasesAndPublication) {
  auto code = assembler::ircode_from_string(mixed_array_initializer(R"(
    (move-object v4 v3)
    (const v3 99)
    (invoke-static (v3) "LObserver;.seeInt:(I)V")
  )",
                                                                    "v4"));
  MethodStats stats;
  ASSERT_EQ(run(code.get(), false, &stats), MethodResult::kChanged);
  EXPECT_EQ(stats.retained_field_stores, 1);
  EXPECT_EQ(stats.aliases, 1);
  EXPECT_EQ(stats.unsupported_uses, 0);
  cfg::ScopedCFG cfg(code.get());
  std::optional<reg_t> array;
  size_t aliases = 0;
  size_t stores = 0;
  size_t publications = 0;
  for (auto& mie : cfg::InstructionIterable(*cfg)) {
    if (mie.insn->opcode() == OPCODE_NEW_ARRAY) {
      array = cfg->move_result_of(cfg->find_insn(mie.insn))->insn->dest();
    } else if (mie.insn->opcode() == OPCODE_MOVE_OBJECT) {
      ASSERT_TRUE(array);
      EXPECT_EQ(mie.insn->src(0), *array);
      ++aliases;
    } else if (mie.insn->opcode() == OPCODE_APUT_OBJECT) {
      ASSERT_TRUE(array);
      EXPECT_EQ(mie.insn->src(1), *array);
      ++stores;
    } else if (mie.insn->opcode() == OPCODE_SPUT_OBJECT &&
               mie.insn->get_field()->get_name()->str() == "$VALUES") {
      ASSERT_TRUE(array);
      EXPECT_EQ(mie.insn->src(0), *array);
      ++publications;
    } else if (mie.insn->opcode() == OPCODE_INVOKE_STATIC) {
      EXPECT_EQ(mie.insn->src(0), 3);
    }
  }
  EXPECT_EQ(aliases, 1);
  EXPECT_EQ(stores, 2);
  EXPECT_EQ(publications, 1);
}

TEST_F(RearrangeEnumClinitTest, RejectUnsupportedArrayUsesBeforeMutation) {
  for (const auto* extra :
       {R"((invoke-static (v3 v3) "LObserver;.see:([LTest;[LTest;)V"))",
        R"((aget-object v3 v2) (move-result-pseudo-object v5))",
        R"((array-length v3) (move-result-pseudo v5))",
        R"((check-cast v3 "Ljava/lang/Object;")
              (move-result-pseudo-object v5))",
        R"((sput-object v3 "LTest;.OTHER:[LTest;"))",
        R"((filled-new-array (v3) "[[LTest;") (move-result-object v5))",
        R"((move-object v4 v3)
           (invoke-static (v4) "LObserver;.see:([LTest;)V"))",
        R"((const v5 1) (new-array v5 "[Ljava/lang/Object;")
           (move-result-pseudo-object v5) (aput-object v3 v5 v2))"}) {
    auto source = mixed_array_initializer(extra);
    auto code = assembler::ircode_from_string(source);
    MethodStats stats;
    EXPECT_EQ(run(code.get(), false, &stats), MethodResult::kFailed) << extra;
    EXPECT_EQ(normalize(source), assembler::to_string(code.get())) << extra;
    EXPECT_EQ(stats.retained_field_stores, 0);
    EXPECT_EQ(stats.aliases, 0);
    EXPECT_GT(stats.unsupported_uses, 0);
  }
}

TEST_F(RearrangeEnumClinitTest, RetargetChainedArrayAliases) {
  auto code = assembler::ircode_from_string(mixed_array_initializer(R"(
    (move-object v4 v3)
    (move-object v6 v4)
  )",
                                                                    "v6"));
  MethodStats stats;
  ASSERT_EQ(run(code.get(), false, &stats), MethodResult::kChanged);
  EXPECT_EQ(stats.aliases, 2);
  cfg::ScopedCFG cfg(code.get());
  std::optional<reg_t> array;
  for (auto& mie : cfg::InstructionIterable(*cfg)) {
    if (mie.insn->opcode() == OPCODE_NEW_ARRAY) {
      array = cfg->move_result_of(cfg->find_insn(mie.insn))->insn->dest();
    } else if (mie.insn->opcode() == OPCODE_MOVE_OBJECT) {
      ASSERT_TRUE(array);
      EXPECT_EQ(mie.insn->src(0), *array);
    }
  }
}

TEST_F(RearrangeEnumClinitTest, RepeatedValuePreservesOrderAndSourceBlocks) {
  auto code = assembler::ircode_from_string(R"((
    (.src_block "LTest;.<clinit>:()V" 0 (1.0 1.0))
    (const v2 0)
    (const v4 1)
    (const-string ALPHA)
    (move-result-pseudo-object v1)
    (new-instance "LTest;")
    (move-result-pseudo-object v0)
    (.src_block "LTest;.<clinit>:()V" 1 (1.0 1.0))
    (invoke-direct (v0 v1 v2) "LTest;.<init>:(Ljava/lang/String;I)V")
    (.src_block "LTest;.<clinit>:()V" 2 (1.0 1.0))
    (const v3 2)
    (new-array v3 "[LTest;")
    (move-result-pseudo-object v3)
    (.src_block "LTest;.<clinit>:()V" 3 (1.0 1.0))
    (aput-object v0 v3 v2)
    (.src_block "LTest;.<clinit>:()V" 4 (1.0 1.0))
    (aput-object v0 v3 v4)
    (sput-object v3 "LTest;.$VALUES:[LTest;")
    (return-void)
  ))");
  ASSERT_EQ(run(code.get()), MethodResult::kChanged);
  cfg::ScopedCFG cfg(code.get());
  bool covered = false;
  std::optional<int64_t> last_const;
  std::vector<int64_t> indices;
  for (auto& mie : *cfg->entry_block()) {
    if (mie.type == MFLOW_SOURCE_BLOCK) {
      covered = true;
    } else if (mie.type == MFLOW_OPCODE) {
      if (mie.insn->opcode() == OPCODE_CONST) {
        last_const = mie.insn->get_literal();
      }
      if (mie.insn->opcode() == OPCODE_APUT_OBJECT) {
        EXPECT_TRUE(covered);
        ASSERT_TRUE(last_const);
        indices.push_back(*last_const);
      }
      if (opcode::can_throw(mie.insn->opcode())) {
        covered = false;
      }
    }
  }
  EXPECT_EQ(indices, (std::vector<int64_t>{0, 1}));
}

TEST_F(RearrangeEnumClinitTest, OtherElementUsesRemainValid) {
  auto code = assembler::ircode_from_string(mixed_array_initializer(R"(
    (invoke-static (v0) "LObserver;.seeElement:(LTest;)V")
  )"));
  FailureReason reason;
  EXPECT_EQ(run(code.get(), false, nullptr, &reason), MethodResult::kChanged);
  EXPECT_EQ(reason, FailureReason::None);
  cfg::ScopedCFG cfg(code.get());
  size_t calls = 0;
  for (auto& mie : cfg::InstructionIterable(*cfg)) {
    if (mie.insn->opcode() == OPCODE_INVOKE_STATIC) {
      EXPECT_EQ(mie.insn->get_method()->get_name()->str(), "seeElement");
      EXPECT_EQ(mie.insn->src(0), 0);
      ++calls;
    }
  }
  EXPECT_EQ(calls, 1);
}

} // namespace rearrange_enum_clinit
