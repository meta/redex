/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "CopyPropagation.h"
#include "IRAssembler.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"

using namespace copy_propagation_impl;

class CopyPropagationTest : public RedexTest {};

TEST_F(CopyPropagationTest, simple) {
  auto code = assembler::ircode_from_string(R"(
    (
     (const v0 0)
     (move v1 v0)
     (move v2 v1)
     (return v2)
    )
)");
  code->set_registers_size(3);
  code->build_cfg();
  copy_propagation_impl::Config config;
  CopyPropagation(config).run(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (const v0 0)
     ; these moves don't get deleted, but running DCE after will clean them up
     (move v1 v0) ; this makes v0 the representative for v1
     ; this source register is remapped by replace_with_representative
     (move v2 v0)
     (return v0)
    )
)");
  code->clear_cfg();
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(CopyPropagationTest, deleteRepeatedMove) {
  auto code = assembler::ircode_from_string(R"(
    (
     (const v0 0)
     (move-object v1 v0) ; this load doesn't get deleted, so that any reg
                         ; operands that cannot get remapped (like the
                         ; monitor-* instructions below) still remain valid

     (move-object v1 v0) ; this move can be deleted

     (monitor-enter v1) ; these won't be remapped to avoid breaking
                        ; ART verification
     (monitor-exit v1)
     (return v1)
    )
)");
  code->set_registers_size(2);
  code->build_cfg();
  copy_propagation_impl::Config config;
  CopyPropagation(config).run(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (const v0 0)
     (move-object v1 v0)
     (monitor-enter v1)
     (monitor-exit v1)
     (return v0)
    )
)");
  code->clear_cfg();
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(CopyPropagationTest, noRemapRange) {

  auto code = assembler::ircode_from_string(R"(
    (
     (const v0 0)
     (move-object v1 v0)

     ; v1 won't get remapped here because it's part of an instruction that
     ; will be converted to /range form during the lowering step
     (invoke-static (v1 v2 v3 v4 v5 v6) "LFoo;.bar:(IIIIII)V")

     (return v1)
    )
)");
  code->set_registers_size(7);
  code->build_cfg();
  copy_propagation_impl::Config config;
  config.regalloc_has_run = true;
  CopyPropagation(config).run(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (const v0 0)
     (move-object v1 v0)
     (invoke-static (v1 v2 v3 v4 v5 v6) "LFoo;.bar:(IIIIII)V")
     (return v0)
    )
)");
  code->clear_cfg();
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(CopyPropagationTest, deleteSelfMove) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v1 0)
      (move v0 v0)
      (return-void)
    )
)");
  code->set_registers_size(2);
  code->build_cfg();
  copy_propagation_impl::Config config;
  CopyPropagation(config).run(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v1 0)
      (return-void)
    )
)");
  code->clear_cfg();
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(CopyPropagationTest, representative) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (move v1 v0)
      (invoke-static (v0) "Lcls;.foo:(I)V")
      (invoke-static (v1) "Lcls;.bar:(I)V")
      (return-void)
    )
)");
  code->set_registers_size(2);
  code->build_cfg();
  copy_propagation_impl::Config config;
  CopyPropagation(config).run(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (move v1 v0)
      (invoke-static (v0) "Lcls;.foo:(I)V")
      (invoke-static (v0) "Lcls;.bar:(I)V")
      (return-void)
    )
)");
  code->clear_cfg();
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(CopyPropagationTest, verifyEnabled) {
  // assuming verify-none is disabled for this test
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (int-to-float v1 v0) ; use v0 as float
      (const v0 0)
      (float-to-int v1 v0) ; use v0 as int
      (return-void)
    )
)");
  code->set_registers_size(2);
  code->build_cfg();
  copy_propagation_impl::Config config;
  CopyPropagation(config).run(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (int-to-float v1 v0) ; use v0 as int
      (const v0 0) ; DON'T delete this. Verifier needs it
      (float-to-int v1 v0) ; use v0 as float
      (return-void)
    )
)");
  code->clear_cfg();
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(CopyPropagationTest, consts_safe_by_constant_uses) {
  // even with verify-none being disabled, the following is safe
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (int-to-float v1 v0) ; use v0 as int
      (const v0 0)
      (int-to-double v1 v0) ; use v0 as int
      (return-void)
    )
)");
  code->set_registers_size(2);
  code->build_cfg();
  copy_propagation_impl::Config config;
  CopyPropagation(config).run(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (int-to-float v1 v0) ; use v0 as int
      (int-to-double v1 v0) ; use v0 as int
      (return-void)
    )
)");
  code->clear_cfg();
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(CopyPropagationTest, non_zero_constant_cannot_have_object_type_demand) {
  // if-s on non-zero constants cannot effectively include Object in the
  // type demand, reducing the type demand to Int, allowing for more
  // copy-propagation
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:()V"
     (
      (const v0 42)
      (if-eqz v0 :L1) ; must be int, as it's non-zero
      (const v0 42)
      (add-int v1 v0 v0) ; int demand
      (:L1)
      (return-void)
     )
    )
)");
  auto* code = method->get_code();
  code->set_registers_size(2);
  code->build_cfg();
  copy_propagation_impl::Config config;
  CopyPropagation(config).run(code, method);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 42)
      (if-eqz v0 :L1) ; must be int, as it's non-zero
      (add-int v1 v0 v0) ; int demand
      (:L1)
      (return-void)
    )
)");
  code->clear_cfg();
  EXPECT_CODE_EQ(code, expected_code.get());
}

TEST_F(CopyPropagationTest, if_eqz_can_create_demand) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:(ZZ)V"
     (
      (load-param v1)
      (load-param v2)
      (const v0 0)
      ; zero could be int, object (or float)
      (if-eqz v1 :L1)
      (if-eqz v2 :L2)
      (sget "LFoo;.a:I")
      (move-result-pseudo v0)
      (:L2)
      ; the combined type of v0 is now int,
      ; and if-eqz projects back this combined type demand,
      ; and thus v0 must have been an int
      (if-eqz v0 :L3)
      (:L3)
      (return-void)

      (:L1)
      (const v0 0)
      (add-int v1 v0 v0) ; int demand
      (return-void)
     )
    )
)");
  auto* code = method->get_code();
  code->set_registers_size(2);
  code->build_cfg();
  copy_propagation_impl::Config config;
  CopyPropagation(config).run(code, method);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v1)
      (load-param v2)
      (const v0 0)
      (if-eqz v1 :L1)
      (if-eqz v2 :L2)
      (sget "LFoo;.a:I")
      (move-result-pseudo v0)
      (:L2)
      (if-eqz v0 :L3)
      (:L3)
      (return-void)

      (:L1)
      ; The next instruction can be removed, as, in both cases, the type demand is int.
      ; (const v0 0)
      (add-int v1 v0 v0) ; int demand
      (return-void)
    )
)");
  code->clear_cfg();
  EXPECT_CODE_EQ(code, expected_code.get());
}

TEST_F(CopyPropagationTest, consts_safe_by_constant_uses_aput) {

  // even with verify-none being disabled, the following is safe

  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:()V"
     (
      (const v0 0)
      (new-array v0 "[I")
      (move-result-pseudo-object v1)
      (const v0 0)
      (const v2 0) ; can be deleted
      (aput v0 v1 v2)
      (const v0 0) ; can be deleted
      (int-to-double v1 v0)
      (return-void)
     )
    )
)");
  auto* code = method->get_code();
  code->set_registers_size(3);
  code->build_cfg();
  copy_propagation_impl::Config config;
  CopyPropagation(config).run(code, method);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (new-array v0 "[I")
      (move-result-pseudo-object v1)
      (const v2 0) ; dead, and local-dce would delete later
      (aput v0 v1 v0)
      (int-to-double v1 v0)
      (return-void)
    )
)");
  code->clear_cfg();
  EXPECT_CODE_EQ(code, expected_code.get());
}

TEST_F(CopyPropagationTest, consts_unsafe_by_constant_uses_aput) {

  // the following is not safe, and shall not be fully optimized
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:()V"
     (
      (const v0 0)
      (new-array v0 "[F") ; array of float
      (move-result-pseudo-object v1)
      (const v0 0) ; used as float
      (const v2 0) ; used as int
      (aput v0 v1 v2)
      (const v0 0) ; used as int
      (int-to-double v1 v0)
      (return-void)
     )
    )
)");
  auto* code = method->get_code();
  code->set_registers_size(3);
  code->build_cfg();
  copy_propagation_impl::Config config;
  CopyPropagation(config).run(code, method);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (new-array v0 "[F") ; array of float
      (move-result-pseudo-object v1)
      (const v0 0) ; used as float
      (const v2 0) ; used as int
      (aput v0 v1 v2)
      (const v0 0) ; used as int, redundant with v2!
      (int-to-double v1 v2)
      (return-void)
    )
)");
  code->clear_cfg();
  EXPECT_CODE_EQ(code, expected_code.get());
}

TEST_F(CopyPropagationTest, wide_consts_safe_by_constant_uses) {
  // even with verify-none being disabled, the following is safe
  auto code = assembler::ircode_from_string(R"(
    (
      (const-wide v0 0)
      (long-to-float v2 v0) ; use v0 as long
      (const-wide v0 0)
      (long-to-double v2 v0) ; use v0 as long
      (return-void)
    )
)");
  code->set_registers_size(4);
  code->build_cfg();
  copy_propagation_impl::Config config;
  CopyPropagation(config).run(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const-wide v0 0)
      (long-to-float v2 v0) ; use v0 as long
      (long-to-double v2 v0) ; use v0 as long
      (return-void)
    )
)");
  code->clear_cfg();
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(CopyPropagationTest, if_constraints_with_constant_uses) {

  // if-eq and if-ne require that *both* of their incoming registers agree on
  // either being an object reference, or an integer.
  // This provides for further refinement of constant uses, allowing to
  // copy-propagate in more cases (but also disallowing in others).
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:()V"
     (
       (const v0 0)
       (const v2 0)
       (new-array v2 "[I")
       (move-result-pseudo-object v1)
       (if-eq v0 v1 :somewhere)

       (const v4 0)
       (move-object v3 v4) ; can be rewritten to refer to v0 instead of v4
       (return-object v3) ; can be rewritten to refer to v0 instead of v3

       (:somewhere)
       (return-object v1)
     )
    )
)");
  auto* code = method->get_code();
  code->set_registers_size(4);
  code->build_cfg();
  copy_propagation_impl::Config config;
  CopyPropagation(config).run(code, method);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v2 0)
      (new-array v2 "[I")
      (move-result-pseudo-object v1)
      (if-eq v0 v1 :somewhere)

      (const v4 0)
      (move-object v3 v0)
      (return-object v0)

      (:somewhere)
      (return-object v1)
    )
)");
  code->clear_cfg();
  EXPECT_CODE_EQ(code, expected_code.get());
}

TEST_F(CopyPropagationTest, cliqueAliasing) {
  auto code = assembler::ircode_from_string(R"(
    (
      (move v1 v2)
      (move v0 v1)
      (move v1 v3)
      (move v0 v2)
      (return-void)
    )
  )");
  code->set_registers_size(4);
  code->build_cfg();
  copy_propagation_impl::Config config;
  config.replace_with_representative = false;
  CopyPropagation(config).run(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (move v1 v2)
      (move v0 v1)
      (move v1 v3)
      (return-void)
    )
  )");
  code->clear_cfg();
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(CopyPropagationTest, loopNoChange) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 10)

      (:loop)
      (if-eq v0 v1 :end)
      (add-int/lit v0 v0 1)
      (goto :loop)

      (:end)
      (return-void)
    )
  )");
  code->set_registers_size(2);
  code->build_cfg();
  copy_propagation_impl::Config config;
  CopyPropagation(config).run(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 10)

      (:loop)
      (if-eq v0 v1 :end)
      (add-int/lit v0 v0 1)
      (goto :loop)

      (:end)
      (return-void)
    )
  )");
  code->clear_cfg();
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(CopyPropagationTest, branchNoChange) {
  const auto* no_change = R"(
    (
      (if-eqz v0 :true)

      (move v1 v2)

      (:end)
      (move v1 v3)
      (return-void)

      (:true)
      (move v3 v2)
      (goto :end)
    )
  )";

  auto code = assembler::ircode_from_string(no_change);
  code->set_registers_size(4);
  code->build_cfg();
  copy_propagation_impl::Config config;
  CopyPropagation(config).run(code.get());

  auto expected_code = assembler::ircode_from_string(no_change);
  code->clear_cfg();
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(CopyPropagationTest, intersect1) {
  auto code = assembler::ircode_from_string(R"(
    (
      (if-eqz v0 :true)

      (move v1 v2)

      (:end)
      (move v1 v2)
      (return-void)

      (:true)
      (move v1 v2)
      (goto :end)
    )
  )");
  code->set_registers_size(4);
  code->build_cfg();
  copy_propagation_impl::Config config;
  CopyPropagation(config).run(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (if-eqz v0 :true)

      (move v1 v2)

      (:end)
      (return-void)

      (:true)
      (move v1 v2)
      (goto :end)
    )
  )");
  code->clear_cfg();
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(CopyPropagationTest, intersect2) {
  const auto* no_change = R"(
    (
      (move v0 v1)
      (if-eqz v0 :true)

      (move v3 v1)

      (:end)
      (move v3 v4)
      (return-void)

      (:true)
      (move v4 v1)
      (goto :end)
    )
  )";
  auto code = assembler::ircode_from_string(no_change);
  code->set_registers_size(5);
  code->build_cfg();
  copy_propagation_impl::Config config;
  config.replace_with_representative = false;
  CopyPropagation(config).run(code.get());

  auto expected_code = assembler::ircode_from_string(no_change);
  code->clear_cfg();
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(CopyPropagationTest, wide) {
  auto code = assembler::ircode_from_string(R"(
    (
      (move-wide v0 v2)
      (move-wide v0 v2)
      (return-void)
    )
  )");
  code->set_registers_size(4);
  code->build_cfg();
  copy_propagation_impl::Config config;
  config.wide_registers = true;
  CopyPropagation(config).run(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (move-wide v0 v2)
      (return-void)
    )
  )");
  code->clear_cfg();
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

// After register allocation, a wide argument of an invoke cannot move to v15:
// lowering expands it to the pair v15, v16, which the non-range form cannot
// encode, and with v2 before it the registers are not a range either.
TEST_F(CopyPropagationTest, wideMethodHandleCallArgumentNotInV15) {
  auto code = assembler::ircode_from_string(R"(
    (
      (move-wide v0 v15)
      (invoke-polymorphic (v2 v0) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" "(J)V")
      (return-void)
    )
  )");
  auto expected_code = std::make_unique<IRCode>(*code);
  code->set_registers_size(17);
  code->build_cfg();
  copy_propagation_impl::Config config;
  config.wide_registers = true;
  config.regalloc_has_run = true;
  CopyPropagation(config).run(code.get());
  code->clear_cfg();
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(CopyPropagationTest, wideCallSiteCallArgumentNotInV15) {
  auto code = assembler::ircode_from_string(R"(
    (
      (move-wide v0 v15)
      (invoke-static (v2 v0) "LFoo;.placeholder:(IJ)V")
      (return-void)
    )
  )");
  redex::make_invoke_custom(code.get(), "run", "(IJ)V");
  auto expected_code = std::make_unique<IRCode>(*code);
  code->set_registers_size(17);
  code->build_cfg();
  copy_propagation_impl::Config config;
  config.wide_registers = true;
  config.regalloc_has_run = true;
  CopyPropagation(config).run(code.get());
  code->clear_cfg();
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(CopyPropagationTest, wideClobber) {
  auto code = assembler::ircode_from_string(R"(
    (
      (move v1 v4)
      (move-wide v0 v2)
      (move v1 v4)
      (return-void)
    )
  )");
  code->set_registers_size(5);
  code->build_cfg();
  copy_propagation_impl::Config config;
  config.wide_registers = false;
  CopyPropagation(config).run(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (move v1 v4)
      (move-wide v0 v2)
      (move v1 v4)
      (return-void)
    )
  )");
  code->clear_cfg();
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(CopyPropagationTest, wideClobberWideTrue) {
  auto code = assembler::ircode_from_string(R"(
    (
      (move v1 v4)
      (move-wide v0 v2)
      (move v1 v4)
      (return-void)
    )
  )");
  code->set_registers_size(5);
  code->build_cfg();
  copy_propagation_impl::Config config;
  config.wide_registers = true;
  CopyPropagation(config).run(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (move v1 v4)
      (move-wide v0 v2)
      (move v1 v4)
      (return-void)
    )
  )");
  code->clear_cfg();
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(CopyPropagationTest, wideClobberWideOddUp) {
  auto code = assembler::ircode_from_string(R"(
    (
      (move-wide v3 v2)
      (move-wide v2 v3)
      (return-void)
    )
  )");
  code->set_registers_size(5);
  code->build_cfg();
  copy_propagation_impl::Config config;
  config.wide_registers = true;
  CopyPropagation(config).run(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (move-wide v3 v2)
      (move-wide v2 v3)
      (return-void)
    )
  )");
  code->clear_cfg();
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(CopyPropagationTest, wideClobberWideOddDown) {
  auto code = assembler::ircode_from_string(R"(
    (
      (move-wide v1 v2)
      (move-wide v2 v1)
      (return-void)
    )
  )");
  code->set_registers_size(5);
  code->build_cfg();
  copy_propagation_impl::Config config;
  config.wide_registers = true;
  CopyPropagation(config).run(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (move-wide v1 v2)
      (move-wide v2 v1)
      (return-void)
    )
  )");
  code->clear_cfg();
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(CopyPropagationTest, repWide) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const-wide v0 0)
      (move-wide v2 v0)
      (const v1 0)
      (move-wide v4 v2)
      (return-void)
    )
  )");
  code->set_registers_size(5);
  code->build_cfg();
  copy_propagation_impl::Config config;
  config.wide_registers = true;
  config.replace_with_representative = true;
  CopyPropagation(config).run(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const-wide v0 0)
      (move-wide v2 v0)
      (const v1 0)
      (move-wide v4 v2) ; don't switch v2 to v0
                        ; because `const v1` invalidated v0
      (return-void)
    )
  )");
  code->clear_cfg();
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

// whichRep and whichRep2 make sure that we deterministically choose the
// representative after a merge point.
TEST_F(CopyPropagationTest, whichRep) {
  const auto* no_change = R"(
    (
      (if-eqz v0 :true)

      (move v1 v2)

      (:end)
      (move v3 v1)
      (return-void)

      (:true)
      (move v2 v1)
      (goto :end)
    )
  )";
  auto code = assembler::ircode_from_string(no_change);
  code->set_registers_size(4);
  code->build_cfg();
  copy_propagation_impl::Config config;
  config.replace_with_representative = true;
  CopyPropagation(config).run(code.get());

  auto expected_code = assembler::ircode_from_string(no_change);
  code->clear_cfg();
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(CopyPropagationTest, whichRep2) {
  const auto* no_change = R"(
    (
      (if-eqz v0 :true)

      (move v2 v1)
      (goto :end)

      (:true)
      (move v1 v2)

      (:end)
      (move v3 v1)
      (return-void)
    )
  )";
  auto code = assembler::ircode_from_string(no_change);
  code->set_registers_size(4);
  code->build_cfg();
  copy_propagation_impl::Config config;
  config.replace_with_representative = true;
  CopyPropagation(config).run(code.get());
  code->clear_cfg();
  auto expected_code = assembler::ircode_from_string(no_change);
}

// make sure we keep using the oldest representative even after a merge
TEST_F(CopyPropagationTest, whichRepPreserve) {
  auto code = assembler::ircode_from_string(R"(
    (
      (if-eqz v0 :true)

      (move v1 v2)

      (:end)
      (move v3 v1)
      (return-void)

      (:true)
      (move v1 v2)
      (goto :end)
    )
  )");
  code->set_registers_size(4);
  code->build_cfg();
  copy_propagation_impl::Config config;
  config.replace_with_representative = true;
  CopyPropagation(config).run(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (if-eqz v0 :true)

      (move v1 v2)

      (:end)
      (move v3 v2)
      (return-void)

      (:true)
      (move v1 v2)
      (goto :end)
    )
  )");
  code->clear_cfg();
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(CopyPropagationTest, wideInvokeSources) {

  const auto* no_change = R"(
    (
      (move-wide v0 v15)
      (invoke-static (v0) "Lcom;.foo:(J)V")
      (return-void)
    )
  )";
  auto code = assembler::ircode_from_string(no_change);
  code->set_registers_size(16);
  code->build_cfg();
  copy_propagation_impl::Config config;
  config.replace_with_representative = true;
  config.wide_registers = true;
  config.regalloc_has_run = true;
  CopyPropagation(config).run(code.get());

  auto expected_code = assembler::ircode_from_string(no_change);
  code->clear_cfg();
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(CopyPropagationTest, use_does_not_kill_type_demands) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:()Ljava/lang/Object;"
     (
       (const v0 0)
       (monitor-enter v0)
       (monitor-exit v0)
       (const v0 0) ; can be deleted
       (return-object v0)
    )
  )
)");
  auto* code = method->get_code();
  code->set_registers_size(2);
  code->build_cfg();
  copy_propagation_impl::Config config;
  CopyPropagation(config).run(code, method);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (monitor-enter v0)
      (monitor-exit v0)
      (return-object v0)
    )
)");
  code->clear_cfg();
  EXPECT_CODE_EQ(code, expected_code.get());
}

TEST_F(CopyPropagationTest, instance_of_kills_type_demands) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:()Ljava/lang/Object;"
     (
       (const v0 0)
       (instance-of v0 "Ljava/lang/String;")
       (move-result-pseudo v1)
       (const v0 0) ; can not be deleted
       (return-object v0)
    )
  )
)");
  auto* code = method->get_code();
  code->set_registers_size(2);
  code->build_cfg();
  copy_propagation_impl::Config config;
  CopyPropagation(config).run(code, method);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (instance-of v0 "Ljava/lang/String;")
      (move-result-pseudo v1)
      (const v0 0) ; can not be deleted
      (return-object v0)
    )
)");
  code->clear_cfg();
  EXPECT_CODE_EQ(code, expected_code.get());
}

TEST_F(CopyPropagationTest, ResueConst) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:()Ljava/lang/Object;"
    (
      (const v2 1)
      (const v3 1)  ; this can be deleted
      (const v4 1)  ; this can be deleted
      (const v5 1)  ; this can be deleted
      (const v6 1)  ; this can be deleted
      (invoke-static (v1 v2 v3 v4 v5 v6) "LFoo;.bar:(IIIIII)V")
    )
  )
)");

  auto* code = method->get_code();
  code->set_registers_size(4);
  code->build_cfg();
  copy_propagation_impl::Config config;
  config.regalloc_has_run = false;
  CopyPropagation(config).run(code, method);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v2 1)
      (const v3 1)
      (const v4 1)
      (const v5 1)
      (const v6 1)
      (invoke-static (v1 v2 v2 v2 v2 v2) "LFoo;.bar:(IIIIII)V")
    )
)");
  code->clear_cfg();
  EXPECT_CODE_EQ(code, expected_code.get());
}

TEST_F(CopyPropagationTest, lock_canonicalization_none) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:()Ljava/lang/Object;"
     (
       (const v0 0)
       (move-object v1 v0)
       (monitor-enter v1)
       (monitor-exit v1)

       (const-class "LFoo;")
       (move-result-pseudo-object v2)
       (move-object v3 v2)
       (monitor-enter v3)
       (monitor-exit v3)
    )
  )
)");
  auto* code = method->get_code();
  code->set_registers_size(4);
  code->build_cfg();
  copy_propagation_impl::Config config;
  CopyPropagation(config).run(code, method);

  auto expected_code = assembler::ircode_from_string(R"(
    (
       (const v0 0)
       (move-object v1 v0)
       (monitor-enter v1)
       (monitor-exit v1)

       (const-class "LFoo;")
       (move-result-pseudo-object v2)
       (move-object v3 v2)
       (monitor-enter v3)
       (monitor-exit v3)
    )
)");
  code->clear_cfg();
  EXPECT_CODE_EQ(code, expected_code.get());
}

TEST_F(CopyPropagationTest, lock_canonicalization) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:()Ljava/lang/Object;"
     (
       (const v0 0)
       (move-object v1 v0)
       (monitor-enter v1)
       (monitor-exit v1)

       (move-object v1 v0)
       (monitor-enter v1)
       (monitor-exit v1)
    )
  )
)");
  auto* code = method->get_code();
  code->set_registers_size(2);
  code->build_cfg();
  copy_propagation_impl::Config config;
  CopyPropagation(config).run(code, method);

  auto expected_code = assembler::ircode_from_string(R"(
    (
       (const v0 0)
       (move-object v2 v0)
       (move-object v1 v0)
       (monitor-enter v2)
       (monitor-exit v2)

       (monitor-enter v2)
       (monitor-exit v2)
    )
)");
  code->clear_cfg();
  EXPECT_CODE_EQ(code, expected_code.get());
}

TEST_F(CopyPropagationTest, check_cast_throw_targets_regs) {
  // In this piece of code, instruction lowering will result in
  //   move-object v1, v0
  //   check-cast v0, "LCls;"
  // The register allocator tries to avoid that `v1` is not holding a live value
  // to make that work. Similarly, CopyProp must not replace `v2` with `v1` in
  // the catch block.
  const auto* code_str = R"(
    (
      (load-param v0)
      (const v1 0)
      (move v2 v1)
      (.try_start a)
      (check-cast v0 "LCls;")
      (move-result-pseudo-object v1)
      (return v1)
      (.try_end a)

      (.catch (a))
      (add-int v2 v2 v2)
      (const v2 0)
      (return v2)
    )
  )";
  auto* method = assembler::method_from_string(
      std::string("(method (public) \"LFoo;.bar:()Ljava/lang/Object;\" ") +
      code_str + ")");

  auto* code = method->get_code();
  code->set_registers_size(3);
  code->build_cfg();
  copy_propagation_impl::Config config;
  config.replace_with_representative = true;
  config.eliminate_const_literals_with_same_type_demands = true;
  CopyPropagation(config).run(code, method);

  code->clear_cfg();
  // Expect that `v2` is not replaced in `add-int`.
  auto expected_code = assembler::ircode_from_string(code_str);
  EXPECT_CODE_EQ(code, expected_code.get());
}
