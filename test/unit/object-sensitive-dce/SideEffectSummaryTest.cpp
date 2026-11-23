/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "SideEffectSummary.h"

#include <gtest/gtest.h>

#include "Creators.h"
#include "DexAccess.h"
#include "IRAssembler.h"
#include "LocalPointersAnalysis.h"
#include "RedexTest.h"

using namespace side_effects;

namespace ptrs = local_pointers;

class SideEffectSummaryTest : public RedexTest {};

Summary analyze_code_effects(const IRCode* code) {
  InvokeToSummaryMap effect_summaries;

  const_cast<IRCode*>(code)->build_cfg();
  const auto& cfg = code->cfg();

  ptrs::FixpointIterator ptrs_fp_iter(cfg);
  ptrs_fp_iter.run(ptrs::Environment());
  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      {}, /* create_init_class_insns */ false);
  return analyze_code(
      init_classes_with_side_effects, effect_summaries, ptrs_fp_iter, code);
}

TEST_F(SideEffectSummaryTest, pure) {
  {
    auto code = assembler::ircode_from_string(R"(
      (
       (const v0 0)
       (return v0)
      )
    )");
    EXPECT_EQ(analyze_code_effects(code.get()), Summary(EFF_NONE, {}));
  }

  {
    auto code = assembler::ircode_from_string(R"(
      (
       (sget "LFoo;.bar:I")
       (move-result-pseudo v0)
       (return v0)
      )
    )");
    EXPECT_EQ(analyze_code_effects(code.get()), Summary(EFF_NONE, {}, true));
  }
}

TEST_F(SideEffectSummaryTest, modifiesParams) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (const v2 0)
      (iput v2 v1 "LFoo;.bar:I")
      (return-void)
    )
  )");
  EXPECT_EQ(analyze_code_effects(code.get()), Summary(EFF_NONE, {1}));
}

TEST_F(SideEffectSummaryTest, throws) {
  auto code = assembler::ircode_from_string(R"(
    (
      (new-instance "Ljava/lang/RuntimeException;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "Ljava/lang/RuntimeException;.<init>:()V")
      (throw v0)
    )
  )");
  EXPECT_EQ(analyze_code_effects(code.get()),
            Summary(EFF_THROWS | EFF_UNKNOWN_INVOKE, {}));
}

TEST_F(SideEffectSummaryTest, locks) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (monitor-enter v0)
      (iget v0 "LFoo;.bar:I")
      (move-result-pseudo v1)
      (monitor-exit v0)
      (return v1)
    )
  )");
  EXPECT_EQ(analyze_code_effects(code.get()), Summary(EFF_LOCKS, {}, true));
}

TEST_F(SideEffectSummaryTest, InvokePolymorphicHasUnknownEffects) {
  ClassCreator handles(DexType::make_type("Ljava/lang/invoke/MethodHandle;"));
  handles.set_super(type::java_lang_Object());
  handles.add_method(
      DexMethod::make_method(
          "Ljava/lang/invoke/MethodHandle;.invoke:([Ljava/lang/Object;)"
          "Ljava/lang/Object;")
          ->make_concrete(ACC_PUBLIC | ACC_NATIVE, true));
  handles.create();
  auto code = assembler::ircode_from_string(R"(
    ((load-param-object v0)
     (invoke-polymorphic (v0) "Ljava/lang/invoke/MethodHandle;.invoke:([Ljava/lang/Object;)Ljava/lang/Object;")
     (move-result-object v1)
     (return-void))
  )");
  auto summary = analyze_code_effects(code.get());
  EXPECT_NE(summary.effects & EFF_UNKNOWN_INVOKE, 0u);
}

TEST_F(SideEffectSummaryTest, unknownWrite) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (sput v0 "LFoo;.qux:I")
      (return-void)
    )
  )");
  EXPECT_EQ(analyze_code_effects(code.get()),
            Summary(EFF_WRITE_MAY_ESCAPE, {}));
}
