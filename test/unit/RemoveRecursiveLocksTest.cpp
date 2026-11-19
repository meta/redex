/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "RemoveRecursiveLocks.h"

#include <gtest/gtest.h>

#include "IRAssembler.h"
#include "IRCode.h"
#include "RedexTest.h"

class RemoveRecursiveLocksTest : public RedexTest {
 public:
  static void normalize(IRCode* code) {
    code->build_cfg();
    code->clear_cfg();
  }
};

TEST_F(RemoveRecursiveLocksTest, no_single_blocks) {
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
    ))");
  method->get_code()->build_cfg();
  auto res = RemoveRecursiveLocksPass::run(method, method->get_code());
  ASSERT_FALSE(res);
}

TEST_F(RemoveRecursiveLocksTest, recursion) {
  auto* method = assembler::method_from_string(R"(
    (method (public static ) "LTest;.foo:(Ljava/lang/Object;Ljava/lang/Object;)V"
      (
          (load-param-object v0)
          (load-param-object v1)
          (monitor-enter v0)
        (.try_start c3)
          (monitor-enter v0)
        (.try_end c3)
        (.try_start c1)
          (monitor-exit v0)
        (.try_end c1)
        (.try_start c4)
          (monitor-exit v0)
        (.try_end c4)
          (monitor-enter v1)
        (.try_start c0)
          (monitor-exit v1)
          (return-void)
        (.catch (c0))
          (move-exception v0)
          (monitor-exit v1)
        (.try_end c0)
          (throw v0)
        (.catch (c1))
        (.catch (c2))
          (move-exception v1)
        (.try_start c2)
          (monitor-exit v0)
        (.try_end c2)
        (.try_start c5)
          (throw v1)
        (.catch (c3))
        (.catch (c4))
        (.catch (c5))
          (move-exception v1)
          (monitor-exit v0)
        (.try_end c5)
          (throw v1)
      )
    ))");
  auto* code = method->get_code();
  code->build_cfg();
  auto res = RemoveRecursiveLocksPass::run(method, code);
  ASSERT_TRUE(res);
  code->clear_cfg();
  auto expected_code = assembler::ircode_from_string(R"(
    (
        (load-param-object v0)
        (load-param-object v1)
        (monitor-enter v0)
      (.try_start c1)
        (monitor-exit v0)
      (.try_end c1)
        (monitor-enter v1)
      (.try_start c0)
        (monitor-exit v1)
        (return-void)
      (.catch (c0))
        (move-exception v0)
        (monitor-exit v1)
      (.try_end c0)
        (throw v0)
      (.try_start c1)
        (.catch (c1))
        (move-exception v1)
        (monitor-exit v0)
      (.try_end c1)
        (throw v1)
    ))");
  EXPECT_CODE_EQ(code, expected_code.get());
}

TEST_F(RemoveRecursiveLocksTest, recursion_nested) {
  auto* method = assembler::method_from_string(R"(
    (method (public static ) "LTest;.foo:(Ljava/lang/Object;Ljava/lang/Object;)V"
      (
          (load-param-object v1)
          (load-param-object v2)
          (monitor-enter v1)
        (.try_start c8)
          (monitor-enter v2)
        (.try_end c8)
        (.try_start c5)
          (monitor-enter v1)
        (.try_end c5)
        (.try_start c2)
          (monitor-enter v2)
        (.try_end c2)
        (.try_start c0)
          (monitor-exit v2)
        (.try_end c0)
        (.try_start c3)
          (monitor-exit v1)
        (.try_end c3)
        (.try_start c6)
          (monitor-exit v2)
        (.try_end c6)
        (.try_start c9)
          (monitor-exit v1)
        (.try_end c9)
          (return-void)
        (.catch (c0))
        (.catch (c1))
          (move-exception v0)
        (.try_start c1)
          (monitor-exit v2)
        (.try_end c1)
        (.try_start c4)
          (throw v0)
        (.catch (c2))
        (.catch (c3))
        (.catch (c4))
          (move-exception v0)
          (monitor-exit v1)
        (.try_end c4)
        (.try_start c7)
          (throw v0)
        (.catch (c5))
        (.catch (c6))
        (.catch (c7))
          (move-exception v0)
          (monitor-exit v2)
        (.try_end c7)
        (.try_start c10)
          (throw v0)
        (.catch (c8))
        (.catch (c9))
        (.catch (c10))
          (move-exception v2)
          (monitor-exit v1)
        (.try_end c10)
          (throw v2)
      )
    ))");
  auto* code = method->get_code();
  code->build_cfg();
  auto res = RemoveRecursiveLocksPass::run(method, code);
  ASSERT_TRUE(res);
  code->clear_cfg();
  auto expected_code = assembler::ircode_from_string(R"(
    (
        (load-param-object v1)
        (load-param-object v2)
        (monitor-enter v1)
      (.try_start c1)
        (monitor-enter v2)
      (.try_end c1)
      (.try_start c0)
        (monitor-exit v2)
      (.try_end c0)
      (.try_start c1)
        (monitor-exit v1)
        (return-void)
      (.try_end c1)
      (.try_start c0)
      (.catch (c0))
        (move-exception v0)
        (monitor-exit v2)
      (.try_end c0)
      (.try_start c1)
        (throw v0)
      (.catch (c1))
        (move-exception v2)
        (monitor-exit v1)
      (.try_end c1)
        (throw v2)
    ))");
  EXPECT_CODE_EQ(code, expected_code.get());
}
