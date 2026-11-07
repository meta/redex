/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <string>

#include <boost/thread/thread.hpp>

#include "IRAssembler.h"
#include "LinearScan.h"
#include "RedexTest.h"

struct FastRegAllocTest : public RedexTest {
  FastRegAllocTest() { g_redex->instrument_mode = false; }
};

/*
 * Check function: allocate() in class: LinearScanAllocator
 * Note: current expected_code is based on the behavior of the non-spill
 * version.
 */
TEST_F(FastRegAllocTest, RegAlloc) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:()Z"
      (
        (const v0 1)
        (const v2 0)
        (add-int v1 v0 v2)
        (const v3 -1)
        (add-int v3 v0 v3)
        (add-int v1 v0 v3)
        (const v4 2)
        (add-int v1 v0 v4)
        (return v1)
      )
    )
)");

  {
    fastregalloc::LinearScanAllocator allocator(method);
    allocator.allocate();
  }

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v4 1)
      (const v3 0)
      (add-int v2 v4 v3)
      (const v3 -1)
      (add-int v3 v4 v3)
      (add-int v1 v4 v3)
      (const v3 2)
      (add-int v0 v4 v3)
      (return v0)
    )
)");
  EXPECT_CODE_EQ(method->get_code(), expected_code.get());
}

/*
 * Check allocation behavior when there is dead code (vreg defined but no use).
 * If a vreg is defined but never used, we assume its live interval lasts until
 * end of code.
 */
TEST_F(FastRegAllocTest, NoUseVReg) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:()Z"
      (
        (const v1 1)
        (const v3 2)
        (return v3)
      )
    )
)");

  {
    fastregalloc::LinearScanAllocator allocator(method);
    allocator.allocate();
  }

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v1 1)
      (const v0 2)
      (return v0)
    )
)");
  EXPECT_CODE_EQ(method->get_code(), expected_code.get());
}

/*
 * Check allocation behavior on control flow.
 */
TEST_F(FastRegAllocTest, ControlFlow) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:()Z"
      (
        (const v2 1)
        (const v1 1)
        (if-eqz v2 :branch)
        (return v2)

        (:branch)
        (add-int v2 v2 v1)
        (return v2)
      )
    )
)");

  {
    fastregalloc::LinearScanAllocator allocator(method);
    allocator.allocate();
  }

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v2 1)
      (const v1 1)
      (if-eqz v2 :branch)
      (return v2)

      (:branch)
      (add-int v0 v2 v1)
      (return v0)
    )
)");
  EXPECT_CODE_EQ(method->get_code(), expected_code.get());
}

/*
 * Check if input code is linearized.
 * Note : code may not be able to fully linearize, especially when there're
 * loops. See the next testcase.
 */
TEST_F(FastRegAllocTest, CheckCodeFlow) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:()Z"
      (
        (goto :def)

        (:use)
        (return v2)

        (:def)
        (const v2 3)
        (goto :use)
      )
    )
)");

  {
    fastregalloc::LinearScanAllocator allocator(method);
    allocator.allocate();
  }

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 3)
      (return v0)
    )
)");
  EXPECT_CODE_EQ(method->get_code(), expected_code.get());
}

/*
 * Check allocation behavior when there're loops. Live interval endpoint of a
 * vreg in loop header can be neither a Use or a Def of the vreg.
 */
TEST_F(FastRegAllocTest, CheckVRegInLoop) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:()Z"
      (
        (const v1 10)
        (const v2 1)
        (:LHead)
        (if-gt v1 v2 :Loop)
        (add-int/lit v3 v1 1)
        (move v0 v3)
        (return v0)
        (:Loop)
        (add-int/lit v1 v1 -1)
        (goto :LHead)
      )
    )
)");

  {
    fastregalloc::LinearScanAllocator allocator(method);
    allocator.allocate();
  }

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v2 10)
      (const v3 1)
      (:LHead)
      (if-gt v2 v3 :Loop)
      (add-int/lit v1 v2 1)
      (move v0 v1)
      (return v0)
      (:Loop)
      (add-int/lit v2 v2 -1)
      (goto :LHead)
    )
)");
  EXPECT_CODE_EQ(method->get_code(), expected_code.get());
}

/*
 * Test behavior when there is wide arguments.
 */
TEST_F(FastRegAllocTest, WideVReg) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:()J"
      (
        (const v2 1)
        (add-int/lit v3 v2 1)
        (const-wide v2 9223372036854775807)
        (return v3)
      )
    )
)");

  {
    fastregalloc::LinearScanAllocator allocator(method);
    allocator.allocate();
  }

  auto expected_code = assembler::ircode_from_string(R"(
    (
        (const v3 1)
        (add-int/lit v2 v3 1)
        (const-wide v0 9223372036854775807)
        (return v2)
    )
)");
  EXPECT_CODE_EQ(method->get_code(), expected_code.get());
}

/*
 * Check live analysis behavior when a vreg has multiple definitions in a basic
 * block. Later Def in the same block should not overwrite the first one. In one
 * block, any Def except the first one should not be recorded as a start/end
 * point anyway.
 */
TEST_F(FastRegAllocTest, ParamAlloc) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LUnexplainedConfig$3;.create:(LLacrimaConfig;)Ljava/lang/Object;"
      (
        (load-param-object v0)
        (load-param-object v1)
        (invoke-virtual (v1) "LLacrimaConfig;.getSessionManager:()LSessionManager;")
        (move-result-object v2)
        (invoke-virtual (v1) "LLacrimaConfig;.getSessionManager:()LSessionManager;")
        (move-result-object v3)
        (iget-object v3 "LSessionManager;.mProcessName:Ljava/lang/String;")
        (move-result-pseudo-object v5)
        (invoke-virtual (v2 v5) "LSessionManager;.getPreviousSessionDir:(Ljava/lang/String;)Ljava/io/File;")
        (move-result-object v2)
        (if-nez v2 :B2)
        (const v1 0)
        (return-object v1)
        (:B2)
        (invoke-virtual (v1) "LLacrimaConfig;.getSessionManager:()LSessionManager;")
        (move-result-object v4)
        (invoke-virtual (v1) "LLacrimaConfig;.getForegroundEntityMapperProvider:()LProvider;")
        (move-result-object v1)
        (invoke-interface (v1) "LProvider;.get:()Ljava/lang/Object;")
        (move-result-object v1)
        (check-cast v1 "LForegroundEntityMapper;")
        (move-result-pseudo-object v1)
        (new-instance "LAppStateCollector;")
        (move-result-pseudo-object v3)
        (invoke-direct (v3 v2 v4 v1) "LAppStateCollector;.<init>:(Ljava/io/File;LSessionManager;LForegroundEntityMapper;)V")
        (return-object v3)
      )
    )
)");

  {
    fastregalloc::LinearScanAllocator allocator(method);
    allocator.allocate();
  }

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param-object v1)
      (load-param-object v7)
      (invoke-virtual (v7) "LLacrimaConfig;.getSessionManager:()LSessionManager;")
      (move-result-object v9)
      (invoke-virtual (v7) "LLacrimaConfig;.getSessionManager:()LSessionManager;")
      (move-result-object v10)
      (iget-object v10 "LSessionManager;.mProcessName:Ljava/lang/String;")
      (move-result-pseudo-object v8)
      (invoke-virtual (v9 v8) "LSessionManager;.getPreviousSessionDir:(Ljava/lang/String;)Ljava/io/File;")
      (move-result-object v4)
      (if-nez v4 :B2)
      (const v0 0)
      (return-object v0)
      (:B2)
      (invoke-virtual (v7) "LLacrimaConfig;.getSessionManager:()LSessionManager;")
      (move-result-object v3)
      (invoke-virtual (v7) "LLacrimaConfig;.getForegroundEntityMapperProvider:()LProvider;")
      (move-result-object v6)
      (invoke-interface (v6) "LProvider;.get:()Ljava/lang/Object;")
      (move-result-object v5)
      (check-cast v5 "LForegroundEntityMapper;")
      (move-result-pseudo-object v2)
      (new-instance "LAppStateCollector;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0 v4 v3 v2) "LAppStateCollector;.<init>:(Ljava/io/File;LSessionManager;LForegroundEntityMapper;)V")
      (return-object v0)
    )
)");
  EXPECT_CODE_EQ(method->get_code(), expected_code.get());
}

TEST_F(FastRegAllocTest, EmptyBlocks) {
  // In "instrument_mode", empty blocks with source-block information are not
  // always merged into with their successor blocks, leaving behind blocks with
  // no instructions that need to be dealt with properly
  g_redex->instrument_mode = true;
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:()Z"
      (
        (const v999 0)
        (switch v999 (:empty_block :successor_block))

        (:empty_block 1)
        (.src_block "LFoo;.bar:()V" 0)

        (:successor_block 2)
        (return v999)
      )
    )
)");

  {
    fastregalloc::LinearScanAllocator allocator(method);
    allocator.allocate();
  }

  auto expected_code = assembler::ircode_from_string(R"(
    (
        (const v0 0)
        (switch v0 (:empty_block :successor_block))

        (:empty_block 1)
        (.src_block "LFoo;.bar:()V" 0)

        (:successor_block 2)
        (return v0)
    )
)");
  EXPECT_CODE_EQ(method->get_code(), expected_code.get());
}

TEST_F(FastRegAllocTest, DefUseIntervalBoundaries) {
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:()Z"
      (
        (const v0 0)
        (move v1 v0)
        (move v2 v1)
        (return v2)
      )
    )
)");

  {
    fastregalloc::LinearScanAllocator allocator(method);
    allocator.allocate();
  }

  auto expected_code = assembler::ircode_from_string(R"(
    (
        (const v1 0)
        (move v1 v1)
        (move v0 v1)
        (return v0)
    )
)");
  EXPECT_CODE_EQ(method->get_code(), expected_code.get());
}

TEST_F(FastRegAllocTest, CheckCast) {
  // The move-result-pseudo-object associated with a check-cast must not have
  // the same dest register as the src(0) of the check cast, if that dest
  // register is live-in to any catch handler of the check-cast. See
  // Interference.cpp / GraphBuilder::build for the long explanation. This is a
  // regression test to ensure that the two registers do *NOT* the unified, even
  // though they don't have overlapping live ranges.
  auto* method = assembler::method_from_string(R"(
    (method (public static) "LFoo;.bar:(Ljava/lang/Object;)Ljava/lang/Object;"
      (
        (load-param-object v111)

        (.try_start a)
        (check-cast v111 "LX;")
        (move-result-pseudo-object v999)
        (return v999)
        (.try_end a)

        (.catch (a))
        (return v111)
      )
    )
)");

  {
    fastregalloc::LinearScanAllocator allocator(method);
    allocator.allocate();
  }

  auto expected_code = assembler::ircode_from_string(R"(
    (
        (load-param-object v1)

        (.try_start a)
        (check-cast v1 "LX;")
        (move-result-pseudo-object v0)
        (return v0)
        (.try_end a)

        (.catch (a))
        (return v1)
    )
)");
  EXPECT_CODE_EQ(method->get_code(), expected_code.get());
}

TEST_F(FastRegAllocTest, CheckCast2) {
  // Don't unify v0 and v1!
  auto* method = assembler::method_from_string(R"(
    (method (public) "LFoo;.bar:(LBaseType;Z)LSubType;"
     (
        (load-param-object v2)
        (load-param v3)
        (const v1 0)
        (if-eqz v3 :L0)
        (return-object v1)

        (.try_start c0)
        (:L0)
        (check-cast v2 "LSubType;")
        (move-result-pseudo-object v0)
        (return-object v0)

        (.try_end c0)
        (.catch (c0))
        (return-object v1)
     )
    )
)");
  method->get_code()->set_registers_size(2);

  {
    fastregalloc::LinearScanAllocator allocator(method);
    allocator.allocate();
  }

  auto expected_code = assembler::ircode_from_string(R"(
    (
        (load-param-object v2)
        (load-param v3)
        (const v1 0)
        (if-eqz v3 :L0)
        (return-object v1)

        (.try_start c0)
        (:L0)
        (check-cast v2 "LSubType;")
        (move-result-pseudo-object v0)
        (return-object v0)

        (.try_end c0)
        (.catch (c0))
        (return-object v1)
    )
)");
  EXPECT_CODE_EQ(method->get_code(), expected_code.get());
}

/*
 * Ordering the blocks must not take native stack space per block: a long chain
 * of blocks would overflow a small stack, such as the 512 KiB that macOS gives
 * secondary threads.
 */
TEST_F(FastRegAllocTest, LongBlockChainOnSmallStack) {
  std::string code = "((load-param v0)\n";
  for (int i = 0; i < 5000; ++i) {
    auto label = ":L" + std::to_string(i);
    code += "(if-eqz v0 " + label + ")\n(const v1 " + std::to_string(i) +
            ")\n(" + label + ")\n";
  }
  code += "(return-void))";
  auto* method = assembler::method_from_string(
      R"((method (public static) "LFoo;.bar:(I)V" )" + code + ")");
  auto* reference = assembler::method_from_string(
      R"((method (public static) "LFoo;.baz:(I)V" )" + code + ")");

  boost::thread::attributes attributes;
  attributes.set_stack_size(size_t{512} * 1024);
  boost::thread thread(attributes, [method] {
    fastregalloc::LinearScanAllocator allocator(method);
    allocator.allocate();
  });
  thread.join();

  {
    fastregalloc::LinearScanAllocator allocator(reference);
    allocator.allocate();
  }
  EXPECT_CODE_EQ(method->get_code(), reference->get_code());
}
