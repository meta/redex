/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <array>
#include <gtest/gtest.h>
#include <utility>

#include "Creators.h"
#include "DedupBlocks.h"
#include "DexAsm.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "IROpcode.h"
#include "RedexTest.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "Walkers.h"

struct Branch {
  MethodItemEntry* source;
  MethodItemEntry* target;
};

struct DedupBlocksTest : public RedexTest {
  DexClass* m_class;
  DexTypeList* m_args;
  DexProto* m_proto;
  DexType* m_type;
  ClassCreator* m_creator;

  DedupBlocksTest() {
    m_args = DexTypeList::make_type_list({});
    m_proto = DexProto::make_proto(type::_void(), m_args);
    m_type = DexType::make_type("LTestClass");

    m_creator = new ClassCreator(m_type);
    m_creator->set_super(type::java_lang_Object());
    m_class = m_creator->get_class();
  }

  DexMethod* get_fresh_method(const std::string& name) {
    DexMethod* method =
        DexMethod::make_method(m_type, DexString::make_string(name), m_proto)
            ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
    method->set_code(std::make_unique<IRCode>(method, 1));
    m_creator->add_method(method);
    return method;
  }

  void run_dedup_blocks() {
    walk::code(std::vector<DexClass*>{m_class},
               [&](DexMethod* method, IRCode& code) {
                 code.build_cfg();
                 dedup_blocks_impl::Config config;
                 dedup_blocks_impl::DedupBlocks impl(&config, method);
                 impl.run();
                 code.clear_cfg();
               });
  }

  void run_dedup_blocks_with_iteration(DexMethod* method,
                                       uint32_t max_iteration) {
    method->get_code()->build_cfg();

    dedup_blocks_impl::Config config;
    config.max_iteration = max_iteration;
    dedup_blocks_impl::DedupBlocks impl(&config, method);
    impl.run();
    method->get_code()->clear_cfg();
  }

  ~DedupBlocksTest() {}
};

// in Code:     A B E C D          (where C == D)
// in CFG:      A -> B -> C -> E
//               \            /
//                >  --   D  >
//
// out Code:    A B E C
// out CFG:     A -> B -> C -> E
//               \       /
//                > --- >
TEST_F(DedupBlocksTest, simplestCase) {
  using namespace dex_asm;
  DexMethod* method = get_fresh_method("simplestCase");

  const auto* str = R"(
    (
      ; A
      (const v0 0)
      (mul-int v0 v0 v0)
      (if-eqz v0 :D)

      ; B
      (mul-int v0 v0 v0)
      (goto :C)

      (:E)
      (return-void)

      (:C)
      (add-int v0 v0 v0)
      (goto :E)

      (:D)
      (add-int v0 v0 v0)
      (goto :E)
    )
  )";

  auto code = assembler::ircode_from_string(str);
  method->set_code(std::move(code));

  run_dedup_blocks();

  const auto* expected_str = R"(
    (
      ; A
      (const v0 0)
      (mul-int v0 v0 v0)
      (if-eqz v0 :C)

      ; B
      (mul-int v0 v0 v0)

      (:C)
      (add-int v0 v0 v0)

      ; E
      (return-void)

      ; no D!
    )
  )";
  auto expected_code = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected_code.get(), method->get_code());
}

// in Code:     A B E C D          (where C and D ends with same instructions)
// in CFG:      A -> B -> C -> E
//               \            /
//                >  --   D  >
//
// out Code:    A B E C
// out CFG:     A -> B -> C' -> F -> E
//               \             /
//                > --------- D'
TEST_F(DedupBlocksTest, simplestPostfixCase) {
  using namespace dex_asm;
  DexMethod* method = get_fresh_method("simplestPostfixCase");

  const auto* str = R"(
    (
      ; A
      (const v0 0)
      (mul-int v0 v0 v0)
      (if-eqz v0 :D)

      ; B
      (mul-int v0 v0 v0)
      (goto :C)

      (:E)
      (return-void)

      (:C)
      (mul-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (goto :E)

      (:D)
      (const v1 1)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (goto :E)
    )
  )";

  auto code = assembler::ircode_from_string(str);
  method->set_code(std::move(code));

  run_dedup_blocks();

  const auto* expected_str = R"(
    (
      ; A
      (const v0 0)
      (mul-int v0 v0 v0)
      (if-eqz v0 :D)

      ; B
      (mul-int v0 v0 v0)

      ; C
      (mul-int v0 v0 v0)

      (:F)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)

      (:E)
      (return-void)

      (:D)
      (const v1 1)
      (goto :F)
    )
  )";
  auto expected_code = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected_code.get(), method->get_code());
}

TEST_F(DedupBlocksTest, postfixDiscardingOneCase) {
  using namespace dex_asm;
  DexMethod* method = get_fresh_method("postfixDiscardingOneCase");

  const auto* str = R"(
    (
      ; A
      (const v0 0)
      (mul-int v0 v0 v0)
      (if-eqz v0 :D)

      ; B
      (mul-int v0 v0 v0)
      (goto :C)

      (:E)
      (add-int v0 v0 v0)
      (return-void)

      (:C)
      (mul-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (goto :E)

      (:D)
      (if-eqz v0 :F)
      (goto :G)

      (:F)
      (const v2 2)
      (goto :E)

      (:G)
      (const v1 1)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (goto :E)
    )
  )";

  auto code = assembler::ircode_from_string(str);
  method->set_code(std::move(code));

  run_dedup_blocks();

  const auto* expected_str = R"(
    (
      ; A
      (const v0 0)
      (mul-int v0 v0 v0)
      (if-eqz v0 :D)

      ; B
      (mul-int v0 v0 v0)

      (:C)
      (mul-int v0 v0 v0)

      (:H)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)

      (:E)
      (add-int v0 v0 v0)
      (return-void)

      (:D)
      (if-eqz v0 :F)

      (:G)
      (const v1 1)
      (goto :H)

      (:F)
      (const v2 2)
      (goto :E)

    )
  )";
  auto expected_code = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected_code.get(), method->get_code());
}

TEST_F(DedupBlocksTest, deepestIsNotTheBestCase) {
  using namespace dex_asm;
  DexMethod* method = get_fresh_method("deepestIsNotTheBestCase");

  const auto* str = R"(
    (
      (const v0 0)
      (const v1 1)
      (switch v0 (:a :b :c :d :e :f))
      (return v0)

      (:a 0)
      (return v0)

      (:b 1)
      (const v1 1)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v1)

      (:c 2)
      (const v1 2)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v1)

      (:d 3)
      (const v0 0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v1)

      (:e 4)
      (const v0 0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v1)

      (:f 5)
      (const v0 0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v1)
    )
  )";

  auto code = assembler::ircode_from_string(str);
  method->set_code(std::move(code));

  run_dedup_blocks();

  const auto* expected_str = R"(
    (
      (const v0 0)
      (const v1 1)
      (switch v0 (:a :b :c :d :e :f))

      (:a 0)
      (return v0)

      (:f 5)
      (:e 4)
      (:d 3)
      (const v0 0)
      (goto :g)

      (:c 2)
      (const v1 2)
      (goto :g)

      (:b 1)
      (const v1 1)

      (:g)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v1)
    )
  )";

  auto expected_code = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected_code.get(), method->get_code());
}

TEST_F(DedupBlocksTest, postfixSwitchCase) {
  using namespace dex_asm;
  DexMethod* method = get_fresh_method("postfixSwitchCase");

  const auto* str = R"(
    (
      (const v0 0)
      (const v1 1)
      (switch v0 (:a :b :c))

      (:a 0)
      (return v0)

      (:b 1)
      (const v1 1)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v1)

      (:c 2)
      (const v0 0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v1)
    )
  )";

  auto code = assembler::ircode_from_string(str);
  method->set_code(std::move(code));

  run_dedup_blocks();

  const auto* expected_str = R"(
    (
      (const v0 0)
      (const v1 1)
      (switch v0 (:a :b :c))

      (:a 0)
      (return v0)

      (:c 2)
      (const v0 0)
      (goto :d)

      (:b 1)
      (const v1 1)

      (:d)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v1)
    )
  )";
  auto expected_code = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected_code.get(), method->get_code());
}

TEST_F(DedupBlocksTest, noDups) {
  const auto* str = R"(
    (
      (const v0 0)
      (if-eqz v0 :lbl)

      (const v0 1)

      (:lbl)
      (return v0)
    )
  )";

  auto* method = get_fresh_method("noDups");
  auto code = assembler::ircode_from_string(str);
  method->set_code(std::move(code));

  run_dedup_blocks();

  auto expected_code = assembler::ircode_from_string(str);

  EXPECT_CODE_EQ(expected_code.get(), method->get_code());
}

TEST_F(DedupBlocksTest, repeatedSwitchBlocks) {
  auto input_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 1)
      (switch v0 (:a :b :c))
      (return v0)

      (:a 0)
      (return v0)

      (:b 1)
      (return v1)

      (:c 2)
      (return v1)
    )
  )");

  auto* method = get_fresh_method("repeatedSwitchBlocks");
  method->set_code(std::move(input_code));
  auto* code = method->get_code();

  run_dedup_blocks();

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 1)
      (switch v0 (:a :b :c))

      (:a 0)
      (return v0)

      (:c 2)
      (:b 1)
      (return v1)
    )
  )");

  EXPECT_CODE_EQ(expected_code.get(), code);
}

TEST_F(DedupBlocksTest, diffSuccessorsNoChange1) {
  const auto* str = R"(
    (
      (const v0 0)
      (const v2 3)
      (if-eqz v0 :left)

      ; right
      ; same code as `:left` block but different successors
      (const v1 1)
      (if-eqz v1 :right2)

      (:middle)
      (add-int v0 v0 v2)
      (return-void)

      (:right2)
      (const v3 3)
      (goto :middle)

      (:left)
      (const v1 1)
      (if-eqz v1 :left2)
      (goto :middle)

      (:left2)
      (const v2 2)
      (goto :middle)

    )
  )";

  auto input_code = assembler::ircode_from_string(str);
  auto* method = get_fresh_method("diffSuccessorsNoChange1");
  method->set_code(std::move(input_code));
  auto* code = method->get_code();

  run_dedup_blocks();

  auto expected_code = assembler::ircode_from_string(str);

  EXPECT_CODE_EQ(expected_code.get(), code);
}

TEST_F(DedupBlocksTest, diffSuccessorsNoChange2) {
  const auto* str = R"(
    (
      (const v0 0)
      (const v2 3)
      (if-eqz v0 :left)

      ; right
      ; same code as `:left` block but different successors
      (const v1 1)
      (if-eqz v1 :middle)

      ; right2
      (const v3 3)

      (:middle)
      (add-int v0 v0 v2)
      (return-void)

      (:left)
      (const v1 1)
      (if-eqz v1 :middle)

      ; left2
      (const v2 2)
      (goto :middle)

    )
  )";

  auto input_code = assembler::ircode_from_string(str);
  auto* method = get_fresh_method("diffSuccessorsNoChange2");
  method->set_code(std::move(input_code));
  auto* code = method->get_code();

  run_dedup_blocks();

  auto expected_code = assembler::ircode_from_string(str);

  EXPECT_CODE_EQ(expected_code.get(), code);
}

TEST_F(DedupBlocksTest, diamond) {
  auto input_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (if-eqz v0 :left)
      (goto :right)

      (:left)
      (const v1 1)
      (goto :middle)

      (:right)
      (const v1 1)

      (:middle)
      (return-void)
    )
  )");

  auto* method = get_fresh_method("diamond");
  method->set_code(std::move(input_code));
  auto* code = method->get_code();

  run_dedup_blocks();

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (if-eqz v0 :left)

      (:left)
      (const v1 1)

      (:middle)
      (return-void)
    )
  )");

  EXPECT_CODE_EQ(expected_code.get(), code);
}

// The entry block (:start) duplicates the lower-id :other block, so it is the
// block that gets replaced. The method must still define v0 before use().
TEST_F(DedupBlocksTest, dedupEntryBlock) {
  auto input_code = assembler::ircode_from_string(R"(
    (
      (goto :start)

      (:other)
      (const v0 1)
      (goto :join)

      (:start)
      (const v0 1)

      (:join)
      (invoke-static (v0) "LFoo;.use:(I)Z")
      (move-result v1)
      (if-eqz v1 :other)
      (return-void)
    )
  )");

  auto* method = get_fresh_method("dedupEntryBlock");
  method->set_code(std::move(input_code));
  auto* code = method->get_code();

  run_dedup_blocks();

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (:other)
      (const v0 1)
      (invoke-static (v0) "LFoo;.use:(I)Z")
      (move-result v1)
      (if-eqz v1 :other)
      (return-void)
    )
  )");

  EXPECT_CODE_EQ(expected_code.get(), code);
}

// in Code:  A B C (where B == C,
//      and they contain a pair of new-instance and constructor instructions)
// in CFG:   A -> B
//            \
//             > C
// out Code: A B
// out CFG:  A -> B
TEST_F(DedupBlocksTest, blockWithNewInstanceAndConstroctor) {
  auto input_code = assembler::ircode_from_string(R"(
    (
      (:a)
      (const v0 0)
      (const v1 1)
      (if-eqz v0 :c)

      (:b)
      (new-instance "LTestClass")
      (move-result-pseudo-object v0)
      (invoke-direct (v0 v1) "LTestClass.<init>:(I)V")
      (throw v0)

      (:c)
      (new-instance "LTestClass")
      (move-result-pseudo-object v0)
      (invoke-direct (v0 v1) "LTestClass.<init>:(I)V")
      (throw v0)
    )
  )");
  auto* method = get_fresh_method("blockWithNewInstanceAndConstroctor");
  method->set_code(std::move(input_code));
  auto* code = method->get_code();

  run_dedup_blocks();

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (:a)
      (const v0 0)
      (const v1 1)
      (if-eqz v0 :c)

      (:b)
      (:c)
      (new-instance "LTestClass")
      (move-result-pseudo-object v0)
      (invoke-direct (v0 v1) "LTestClass.<init>:(I)V")
      (throw v0)
    )
  )");

  EXPECT_CODE_EQ(expected_code.get(), code);
}

// in Code: A B C D E (where C == E,
//      and they construct an object from B and D respectively)
// in CFG:  A -> B -> C
//           \
//            > D -> E
// out Code: the same as the in Code
// out CFG: the same as the in CFG
TEST_F(DedupBlocksTest, constructsObjectFromAnotherBlock) {
  std::string str_code = R"(
    (
      (:a)
      (const v0 0)
      (if-eqz v0 :d)

      (:b)
      (new-instance "LTestClass")
      (move-result-pseudo-object v0)

      (:c)
      (const v1 1)
      (invoke-direct (v0 v1) "LTestClass.<init>:(I)V")
      (throw v0)

      (:d)
      (new-instance "LTestClass")
      (move-result-pseudo-object v0)
      (const v1 2)

      (:e)
      (const v1 1)
      (invoke-direct (v0 v1) "LTestClass.<init>:(I)V")
      (throw v0)
    )
  )";
  auto input_code = assembler::ircode_from_string(str_code);
  auto* method = get_fresh_method("constructsObjectFromAnotherBlock");
  method->set_code(std::move(input_code));
  auto* code = method->get_code();
  run_dedup_blocks();
  auto expect_code = assembler::ircode_from_string(str_code);
  EXPECT_CODE_EQ(expect_code.get(), code);
}

// newly created instances may be moved around, but that doesn't change that
// we must not dedup in the face of multiple new-instance instructions
TEST_F(DedupBlocksTest, constructsObjectFromAnotherBlockViaMove) {
  std::string str_code = R"(
    (
      (:a)
      (const v0 0)
      (if-eqz v0 :d)

      (:b)
      (new-instance "LTestClass")
      (move-result-pseudo-object v2)

      (:c)
      (move-object v0 v2)
      (const v1 1)
      (invoke-direct (v0 v1) "LTestClass.<init>:(I)V")
      (throw v0)

      (:d)
      (new-instance "LTestClass")
      (move-result-pseudo-object v2)
      (const v1 2)

      (:e)
      (move-object v0 v2)
      (const v1 1)
      (invoke-direct (v0 v1) "LTestClass.<init>:(I)V")
      (throw v0)
    )
  )";
  auto input_code = assembler::ircode_from_string(str_code);
  auto* method = get_fresh_method("constructsObjectFromAnotherBlock");
  method->set_code(std::move(input_code));
  auto* code = method->get_code();
  run_dedup_blocks();
  auto expect_code = assembler::ircode_from_string(str_code);
  EXPECT_CODE_EQ(expect_code.get(), code);
}

TEST_F(DedupBlocksTest, dedupCatchBlocks) {
  std::string str_code = R"(
    (
      (.try_start t_0)
      (new-instance "LTestClass")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LTestClass.<init>:()V")
      (.try_end t_0)

      (.try_start t_2)
      (iget v0 "LTestClass;.a:I")
      (move-result-pseudo v2)
      (.try_end t_2)

      (.try_start t_1)
      (iget v0 "LTestClass;.b:I")
      (move-result-pseudo v3)
      (.try_end t_1)

      (return-void)

      (:block_catch_t_0)
      (.catch (t_0))
      (move-exception v2)
      (throw v2)

      (:block_catch_t_1)
      (.catch (t_1))
      (move-exception v2)
      (throw v2)

      (:block_catch_t_2)
      (.catch (t_2))
      (throw v0)
    )
  )";
  auto input_code = assembler::ircode_from_string(str_code);
  auto* method = get_fresh_method("dedupCatchBlocks");
  method->set_code(std::move(input_code));
  auto* code = method->get_code();
  run_dedup_blocks();

  std::string expect_str = R"(
    (
      (.try_start t_0)
      (new-instance "LTestClass")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LTestClass.<init>:()V")
      (.try_end t_0)

      (.try_start t_2)
      (iget v0 "LTestClass;.a:I")
      (move-result-pseudo v2)
      (.try_end t_2)

      (.try_start t_0)
      (iget v0 "LTestClass;.b:I")
      (move-result-pseudo v3)
      (.try_end t_0)

      (return-void)

      (:block_catch_t_0)
      (.catch (t_0))
      (move-exception v2)
      (throw v2)

      (:block_catch_t_2)
      (.catch (t_2))
      (throw v0)
    )
  )";
  auto expect_code = assembler::ircode_from_string(expect_str);
  expect_code->build_cfg();
  expect_code->clear_cfg();

  EXPECT_CODE_EQ(expect_code.get(), code);
}

TEST_F(DedupBlocksTest, dontDedupCatchBlockAndNonCatchBlock) {
  std::string str_code = R"(
    (
      (.try_start t_0)
      (new-instance "LTestClass")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LTestClass.<init>:()V")
      (.try_end t_0)

      (if-eqz v0 :block_no_catch)
      (return-void)

      (:block_catch_t_0)
      (.catch (t_0))
      (move-exception v2)
      (throw v2)

      (:block_no_catch)
      (move-exception v2)
      (throw v2)
    )
  )";
  auto input_code = assembler::ircode_from_string(str_code);
  auto* method = get_fresh_method("dontDedupCatchBlockAndNonCatchBlock");
  method->set_code(std::move(input_code));
  auto* code = method->get_code();
  run_dedup_blocks();

  auto expect_code = assembler::ircode_from_string(str_code);
  expect_code->build_cfg();
  expect_code->clear_cfg();

  EXPECT_CODE_EQ(expect_code.get(), code);
}

TEST_F(DedupBlocksTest, respectTypes) {
  using namespace dex_asm;
  DexMethod* method = get_fresh_method("v");

  const auto* str = R"(
    (
      ; A
      (const-string "hello")
      (move-result-pseudo-object v0)
      (if-eqz v0 :D)

      ; B
      (const v0 1)
      (if-eqz v0 :C)

      (:E)
      (return-void)

      (:C)
      (if-nez v0 :E)
      (goto :E)

      (:D)
      (if-nez v0 :E)
      (goto :E)
    )
  )";

  auto code = assembler::ircode_from_string(str);
  method->set_code(std::move(code));

  run_dedup_blocks();

  const auto* expected_str = str;
  auto expected_code = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected_code.get(), method->get_code());
}

TEST_F(DedupBlocksTest, dontRespectDexTypes) {
  using namespace dex_asm;
  DexMethod* method = get_fresh_method("v");

  const auto* str = R"(
    (
      ; A
      (const-string "hello")
      (move-result-pseudo-object v0)
      (if-eqz v0 :D)

      ; B
      (const-class "Lbaz;")
      (move-result-pseudo-object v0)
      (if-eqz v0 :C)

      (:E)
      (return-void)

      (:C)
      (if-nez v0 :E)
      (goto :E)

      (:D)
      (if-nez v0 :E)
      (goto :E)
    )
  )";

  auto code = assembler::ircode_from_string(str);
  method->set_code(std::move(code));

  run_dedup_blocks();

  const auto* expected_str = R"(
    (
      ; A
      (const-string "hello")
      (move-result-pseudo-object v0)
      (if-eqz v0 :C)

      ; B
      (const-class "Lbaz;")
      (move-result-pseudo-object v0)
      (if-eqz v0 :C)

      (:E)
      (return-void)

      (:C)
      (if-nez v0 :E)
      (goto :E)
    )
  )";
  auto expected_code = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected_code.get(), method->get_code());
}

TEST_F(DedupBlocksTest, dontRespectDexTypesIncludingArraysIfNotUsedAsSuch) {
  using namespace dex_asm;
  DexMethod* method = get_fresh_method("v");

  const auto* str = R"(
    (
      ; A
      (const v0 0)
      (new-array v0 "[Ljava/lang/Object;")
      (move-result-pseudo-object v0)
      (if-eqz v0 :D)

      ; B
      (const-class "Lbaz;")
      (move-result-pseudo-object v0)
      (if-eqz v0 :C)

      (:E)
      (return-void)

      (:C)
      (if-nez v0 :E)
      (goto :E)

      (:D)
      (if-nez v0 :E)
      (goto :E)
    )
  )";

  auto code = assembler::ircode_from_string(str);
  method->set_code(std::move(code));

  run_dedup_blocks();

  const auto* expected_str = R"(
    (
      ; A
      (const v0 0)
      (new-array v0 "[Ljava/lang/Object;")
      (move-result-pseudo-object v0)
      (if-eqz v0 :C)

      ; B
      (const-class "Lbaz;")
      (move-result-pseudo-object v0)
      (if-eqz v0 :C)

      (:E)
      (return-void)

      (:C)
      (if-nez v0 :E)
      (goto :E)
    )
  )";
  auto expected_code = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected_code.get(), method->get_code());
}

TEST_F(DedupBlocksTest, referenceAndPrimitiveArraysHaveNoCommonBaseType) {
  using namespace dex_asm;
  DexMethod* method = get_fresh_method("I");

  const auto* str = R"(
    (
      ; A
      (const v1 0)
      (new-array v1 "[Ljava/lang/Object;")
      (move-result-pseudo-object v0)
      (if-eqz v0 :D)

      ; B
      (new-array v1 "[I")
      (move-result-pseudo-object v0)
      (if-eqz v0 :C)

      (:E)
      (return v1)

      (:C)
      (array-length v0)
      (move-result-pseudo v1)
      (if-nez v0 :E)
      (goto :E)

      (:D)
      (array-length v0)
      (move-result-pseudo v1)
      (if-nez v0 :E)
      (goto :E)
    )
  )";

  auto code = assembler::ircode_from_string(str);
  method->set_code(std::move(code));

  run_dedup_blocks();

  const auto* expected_str = str;
  auto expected_code = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected_code.get(), method->get_code());
}

TEST_F(DedupBlocksTest, allReferenceArraysHaveCommonBaseType) {
  using namespace dex_asm;
  DexMethod* method = get_fresh_method("I");

  ClassCreator object_creator(type::java_lang_Object());
  object_creator.create()->set_external();

  ClassCreator some_object_creator(DexType::make_type("LSomeObject;"));
  some_object_creator.set_super(type::java_lang_Object());
  some_object_creator.create();

  const auto* str = R"(
    (
      ; A
      (const v1 0)
      (new-array v1 "[Ljava/lang/Object;")
      (move-result-pseudo-object v0)
      (if-eqz v0 :D)

      ; B
      (new-array v1 "[LSomeObject;")
      (move-result-pseudo-object v0)
      (if-eqz v0 :C)

      (:E)
      (return v1)

      (:C)
      (array-length v0)
      (move-result-pseudo v1)
      (if-nez v0 :E)
      (goto :E)

      (:D)
      (array-length v0)
      (move-result-pseudo v1)
      (if-nez v0 :E)
      (goto :E)
    )
  )";

  auto code = assembler::ircode_from_string(str);
  method->set_code(std::move(code));

  run_dedup_blocks();

  const auto* expected_str = R"(
    (
      ; A
      (const v1 0)
      (new-array v1 "[Ljava/lang/Object;")
      (move-result-pseudo-object v0)
      (if-eqz v0 :C)

      ; B
      (new-array v1 "[LSomeObject;")
      (move-result-pseudo-object v0)
      (if-eqz v0 :C)

      (:E)
      (return v1)

      (:C)
      (array-length v0)
      (move-result-pseudo v1)
      (if-nez v0 :E)
      (goto :E)
    )
  )";

  auto expected_code = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected_code.get(), method->get_code());
}

TEST_F(DedupBlocksTest, androidIsAfraidOfArraysOfInterfaces) {
  using namespace dex_asm;
  DexMethod* method = get_fresh_method("I");

  ClassCreator object_creator(type::java_lang_Object());
  object_creator.create();

  ClassCreator i_creator(DexType::make_type("LI;"));
  i_creator.set_access(ACC_INTERFACE);
  i_creator.set_super(type::java_lang_Object());
  auto* i_cls = i_creator.create();

  ClassCreator a_creator(DexType::make_type("LA;"));
  a_creator.add_interface(i_cls->get_type());
  a_creator.set_super(type::java_lang_Object());
  a_creator.create();

  ClassCreator b_creator(DexType::make_type("LB;"));
  b_creator.add_interface(i_cls->get_type());
  b_creator.set_super(type::java_lang_Object());

  const auto* str = R"(
    (
      ; A
      (const v1 0)
      (new-array v1 "[LA;")
      (move-result-pseudo-object v0)
      (if-eqz v0 :D)

      ; B
      (new-array v1 "[LB;")
      (move-result-pseudo-object v0)
      (if-eqz v0 :C)

      (:E)
      (return v1)

      (:C)
      (invoke-static (v0) "LTotallyLegit;.method:([LI;)V")
      (return v1)

      (:D)
      (invoke-static (v0) "LTotallyLegit;.method:([LI;)V")
      (return v1)
    )
  )";

  auto code = assembler::ircode_from_string(str);
  method->set_code(std::move(code));

  run_dedup_blocks();

  const auto* expected_str = str;
  auto expected_code = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected_code.get(), method->get_code());
}

TEST_F(DedupBlocksTest, trivialJoinOfArrayOfClassesIsFine) {
  using namespace dex_asm;
  DexMethod* method = get_fresh_method("I");

  ClassCreator object_creator(type::java_lang_Object());
  object_creator.create();

  ClassCreator i_creator(DexType::make_type("LI;"));
  i_creator.set_access(ACC_INTERFACE);
  i_creator.set_super(type::java_lang_Object());
  auto* i_cls = i_creator.create();

  ClassCreator a_creator(DexType::make_type("LA;"));
  a_creator.add_interface(i_cls->get_type());
  a_creator.set_super(type::java_lang_Object());
  a_creator.create();

  const auto* str = R"(
    (
      ; A
      (const v1 0)
      (new-array v1 "[LA;")
      (move-result-pseudo-object v0)
      (if-eqz v0 :D)

      ; B
      (new-array v1 "[LA;")
      (move-result-pseudo-object v0)
      (if-eqz v0 :C)

      (:E)
      (return v1)

      (:C)
      (invoke-static (v0) "LTotallyLegit;.method:([LI;)V")
      (return v1)

      (:D)
      (invoke-static (v0) "LTotallyLegit;.method:([LI;)V")
      (return v1)
    )
  )";

  auto code = assembler::ircode_from_string(str);
  method->set_code(std::move(code));

  run_dedup_blocks();

  const auto* expected_str = R"(
    (
      ; A
      (const v1 0)
      (new-array v1 "[LA;")
      (move-result-pseudo-object v0)
      (if-eqz v0 :C)

      ; B
      (new-array v1 "[LA;")
      (move-result-pseudo-object v0)
      (if-eqz v0 :C)

      (:E)
      (return v1)

      (:C)
      (invoke-static (v0) "LTotallyLegit;.method:([LI;)V")
      (goto :E)
    )
  )";

  auto expected_code = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected_code.get(), method->get_code());
}

TEST_F(DedupBlocksTest, self_loops_are_alike) {
  auto input_code = assembler::ircode_from_string(R"(
    (
      (:a)
      (const v0 0)
      (if-eqz v0 :c)

      (:b)
      (nop)
      (goto :b)

      (:c)
      (nop)
      (goto :c)
    )
  )");
  auto* method = get_fresh_method("self_loops_are_alike");
  method->set_code(std::move(input_code));
  auto* code = method->get_code();

  run_dedup_blocks();

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (:a)
      (const v0 0)
      (if-eqz v0 :c)

      (:b)
      (:c)
      (nop)
      (goto :b)
    )
  )");

  EXPECT_CODE_EQ(expected_code.get(), code);
}

TEST_F(DedupBlocksTest, conditional_self_loops_are_alike) {
  auto input_code = assembler::ircode_from_string(R"(
    (
      (:a)
      (const v0 0)
      (const v1 0)
      (if-eqz v1 :c)

      (:b)
      (nop)
      (if-eqz v0 :b)
      (goto :end)

      (:c)
      (nop)
      (if-eqz v0 :c)

      (:end)
      (return-void)
    )
  )");
  auto* method = get_fresh_method("conditional_self_loops_are_alike");
  method->set_code(std::move(input_code));
  auto* code = method->get_code();

  run_dedup_blocks();

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (:a)
      (const v0 0)
      (const v1 0)
      (if-eqz v1 :c)

      (:b)
      (:c)
      (nop)
      (if-eqz v0 :b)
      (return-void)
    )
  )");

  EXPECT_CODE_EQ(expected_code.get(), code);
}

TEST_F(DedupBlocksTest, return_if_single) {
  auto input_code = assembler::ircode_from_string(R"(
    (
      (const v0 1)
      (if-eqz v0 :label)
      (return-void)
      (:label)
      (return-void)
    )
  )");
  auto* method = get_fresh_method("conditional_self_loops_are_alike");
  method->set_code(std::move(input_code));
  auto* code = method->get_code();

  run_dedup_blocks();

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 1)
      (if-eqz v0 :label)
      (:label)
      (return-void)
    )
  )");

  EXPECT_CODE_EQ(expected_code.get(), code);
}

// Blocks B and C are different only in register allocation.
TEST_F(DedupBlocksTest, conditional_hashed_alike) {
  auto input_code = assembler::ircode_from_string(R"(
    (
      (:a)
      (const v0 0)
      (const v1 0)
      (const v2 0)
      (if-eqz v1 :c)

      (:b)
      (move-exception v3)
      (monitor-exit  v2)
      (throw v3)
      (if-eqz v0 :b)
      (goto :end)

      (:c)
      (move-exception v4)
      (monitor-exit  v2)
      (throw v4)
      (if-eqz v0 :c)

      (:end)
    )
  )");
  auto* method = get_fresh_method("conditional_hashed_alike");
  method->set_code(std::move(input_code));
  auto* code = method->get_code();

  run_dedup_blocks();

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 0)
      (const v2 0)
      (if-eqz v1 :c)

      (:c)
      (move-exception v3)
      (monitor-exit  v2)
      (throw v3)
    )
  )");

  EXPECT_CODE_EQ(expected_code.get(), code);
}

// Value for add-int are different so this cannont be deduplicated.
TEST_F(DedupBlocksTest, conditional_hashed_not_alike) {
  auto input_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 1)
      (const v2 2)
      (if-eqz v0 :b)

      (add-int v0 v1 v0)
      (goto :end)

      (:b)
      (add-int v0 v2 v0)
      (goto :end)

      (add-int v0 v2 v0)
      (:end)
      (add-int v0 v2 v0)
      (return-void)
    )
  )");

  auto* method = get_fresh_method("conditional_hashed_not_alike");
  method->set_code(std::move(input_code));
  auto* code = method->get_code();

  run_dedup_blocks();

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 1)
      (const v2 2)
      (if-eqz v0 :b)

      (add-int v0 v1 v0)

      (:end)
      (add-int v0 v2 v0)
      (return-void)

      (:b)
      (add-int v0 v2 v0)
      (goto :end)
    )
  )");

  EXPECT_CODE_EQ(expected_code.get(), code);
}

// dedup throws
TEST_F(DedupBlocksTest, dedup_throws) {
  auto input_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (if-eqz v0 :a)
      (goto :b)
      (:a)
      (throw v0)
      (:b)
      (throw v0)
    )
  )");
  auto* method = get_fresh_method("dedup_throws");
  method->set_code(std::move(input_code));
  auto* code = method->get_code();

  run_dedup_blocks();

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (if-eqz v0 :a)
      (:a)
      (throw v0)
    )
  )");

  EXPECT_CODE_EQ(expected_code.get(), code);
}

// Don't dedup direct calls to fillInStackTrace
TEST_F(DedupBlocksTest, dont_dedup_fill_in_stack_trace) {
  ClassCreator throwable_creator(type::java_lang_Throwable());
  throwable_creator.set_super(type::java_lang_Object());
  auto* fillInStackeTrace_method =
      method::java_lang_Throwable_fillInStackTrace();
  fillInStackeTrace_method->set_virtual(true);
  fillInStackeTrace_method->set_external();
  throwable_creator.add_method(method::java_lang_Throwable_fillInStackTrace());
  throwable_creator.create()->set_external();

  auto input_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 1)
      (if-eqz v1 :lbl)

      (invoke-virtual (v0) "Ljava/lang/Throwable;.fillInStackTrace:()Ljava/lang/Throwable;")
      (return-object v0)

      (:lbl)
      (invoke-virtual (v0) "Ljava/lang/Throwable;.fillInStackTrace:()Ljava/lang/Throwable;")
      (return-object v0)
    )
  )");
  auto* method = get_fresh_method("dont_dedup_fill_in_stack_trace");
  method->set_code(std::move(input_code));
  auto* code = method->get_code();

  run_dedup_blocks();

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 1)
      (if-eqz v1 :lbl)

      (invoke-virtual (v0) "Ljava/lang/Throwable;.fillInStackTrace:()Ljava/lang/Throwable;")
      (return-object v0)

      (:lbl)
      (invoke-virtual (v0) "Ljava/lang/Throwable;.fillInStackTrace:()Ljava/lang/Throwable;")
      (return-object v0)
    )
  )");

  EXPECT_CODE_EQ(expected_code.get(), code);
}

// Don't dedup indirect calls to fillInStackTrace via Throwable constructors
TEST_F(DedupBlocksTest, dont_dedup_indirect_fill_in_stack_trace) {
  ClassCreator throwable_creator(type::java_lang_Throwable());
  throwable_creator.set_super(type::java_lang_Object());
  auto* throwable_cls = throwable_creator.create();
  throwable_cls->set_external();

  ClassCreator throwable2_creator(DexType::make_type("LThrowable2;"));
  throwable2_creator.set_super(throwable_cls->get_type());
  throwable2_creator.create()->set_external();

  auto input_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 1)
      (if-eqz v1 :lbl)

      (new-instance "LThrowable2;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LThrowable2;.<init>:()V")
      (return-object v0)

      (:lbl)
      (new-instance "LThrowable2;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LThrowable2;.<init>:()V")
      (return-object v0)
    )
  )");
  auto* method = get_fresh_method("dont_dedup_indirect_fill_in_stack_trace");
  method->set_code(std::move(input_code));
  auto* code = method->get_code();

  run_dedup_blocks();

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 1)
      (if-eqz v1 :lbl)

      (new-instance "LThrowable2;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LThrowable2;.<init>:()V")
      (return-object v0)

      (:lbl)
      (new-instance "LThrowable2;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "LThrowable2;.<init>:()V")
      (return-object v0)
    )
  )");

  EXPECT_CODE_EQ(expected_code.get(), code);
}

// Don't dedup blocks calling kotlin.jvm.internal.Intrinsics throw* helpers.
// These static helpers throw an exception inside their body; their call-site
// PC is what symbolicates in the resulting stack trace, so collapsing two
// callers into a single shared call site mis-attributes runtime exceptions
// (e.g. a lateinit-access UninitializedPropertyAccessException) to whichever
// caller happened to emit its position MIE just before the dedupped block.
TEST_F(DedupBlocksTest, dont_dedup_kotlin_intrinsics_throw_helper) {
  auto input_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 1)
      (if-eqz v1 :lbl)

      (const-string "fieldA")
      (move-result-pseudo-object v0)
      (invoke-static (v0) "Lkotlin/jvm/internal/Intrinsics;.throwUninitializedPropertyAccessException:(Ljava/lang/String;)V")
      (return-void)

      (:lbl)
      (const-string "fieldB")
      (move-result-pseudo-object v0)
      (invoke-static (v0) "Lkotlin/jvm/internal/Intrinsics;.throwUninitializedPropertyAccessException:(Ljava/lang/String;)V")
      (return-void)
    )
  )");
  auto* method = get_fresh_method("dont_dedup_kotlin_intrinsics_throw_helper");
  method->set_code(std::move(input_code));
  auto* code = method->get_code();

  run_dedup_blocks();

  // The two invoke-static blocks differ only in the const-string they pass.
  // Even though the (invoke-static + return-void) tail is byte-identical, it
  // must NOT be merged because each call-site's PC is the throw-site that
  // surfaces in the stack trace.
  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 1)
      (if-eqz v1 :lbl)

      (const-string "fieldA")
      (move-result-pseudo-object v0)
      (invoke-static (v0) "Lkotlin/jvm/internal/Intrinsics;.throwUninitializedPropertyAccessException:(Ljava/lang/String;)V")
      (return-void)

      (:lbl)
      (const-string "fieldB")
      (move-result-pseudo-object v0)
      (invoke-static (v0) "Lkotlin/jvm/internal/Intrinsics;.throwUninitializedPropertyAccessException:(Ljava/lang/String;)V")
      (return-void)
    )
  )");

  EXPECT_CODE_EQ(expected_code.get(), code);
}

// Same protection applies to other Intrinsics throw* helpers (throwNpe is
// emitted by Kotlin for `!!` non-null assertions).
TEST_F(DedupBlocksTest, dont_dedup_kotlin_intrinsics_throw_npe) {
  auto input_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 1)
      (if-eqz v1 :lbl)

      (invoke-static () "Lkotlin/jvm/internal/Intrinsics;.throwNpe:()V")
      (return-void)

      (:lbl)
      (invoke-static () "Lkotlin/jvm/internal/Intrinsics;.throwNpe:()V")
      (return-void)
    )
  )");
  auto* method = get_fresh_method("dont_dedup_kotlin_intrinsics_throw_npe");
  method->set_code(std::move(input_code));
  auto* code = method->get_code();

  run_dedup_blocks();

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 1)
      (if-eqz v1 :lbl)

      (invoke-static () "Lkotlin/jvm/internal/Intrinsics;.throwNpe:()V")
      (return-void)

      (:lbl)
      (invoke-static () "Lkotlin/jvm/internal/Intrinsics;.throwNpe:()V")
      (return-void)
    )
  )");

  EXPECT_CODE_EQ(expected_code.get(), code);
}

// Redex's own UnreachableException.createAndThrow synthetic helper has the
// same property and the same protection requirement.
TEST_F(DedupBlocksTest, dont_dedup_redex_unreachable_create_and_throw) {
  auto input_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 1)
      (if-eqz v1 :lbl)

      (invoke-static () "Lcom/redex/UnreachableException;.createAndThrow:()Lcom/redex/UnreachableException;")
      (move-result-object v0)
      (throw v0)

      (:lbl)
      (invoke-static () "Lcom/redex/UnreachableException;.createAndThrow:()Lcom/redex/UnreachableException;")
      (move-result-object v0)
      (throw v0)
    )
  )");
  auto* method =
      get_fresh_method("dont_dedup_redex_unreachable_create_and_throw");
  method->set_code(std::move(input_code));
  auto* code = method->get_code();

  run_dedup_blocks();

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 1)
      (if-eqz v1 :lbl)

      (invoke-static () "Lcom/redex/UnreachableException;.createAndThrow:()Lcom/redex/UnreachableException;")
      (move-result-object v0)
      (throw v0)

      (:lbl)
      (invoke-static () "Lcom/redex/UnreachableException;.createAndThrow:()Lcom/redex/UnreachableException;")
      (move-result-object v0)
      (throw v0)
    )
  )");

  EXPECT_CODE_EQ(expected_code.get(), code);
}

// Any method declared to return com.redex.UnreachableException is a throw
// helper, whatever its name, so two of its call sites that differ only in
// their positions stay apart.
TEST_F(DedupBlocksTest, dont_dedup_methods_returning_unreachable_exception) {
  auto input_code = assembler::ircode_from_string(R"(
    (
      (const-string "name")
      (move-result-pseudo-object v2)
      (const v1 1)
      (if-eqz v1 :lbl)

      (.pos:dbg_0 "LFoo;.caller:()V" "Foo.java" 10)
      (invoke-static (v2) "LFoo;.a:(Ljava/lang/String;)Lcom/redex/UnreachableException;")
      (move-result-object v0)
      (throw v0)

      (:lbl)
      (.pos:dbg_1 "LFoo;.caller:()V" "Foo.java" 20)
      (invoke-static (v2) "LFoo;.a:(Ljava/lang/String;)Lcom/redex/UnreachableException;")
      (move-result-object v0)
      (throw v0)
    )
  )");
  auto* method =
      get_fresh_method("dont_dedup_methods_returning_unreachable_exception");
  method->set_code(std::move(input_code));
  auto* code = method->get_code();

  run_dedup_blocks();

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const-string "name")
      (move-result-pseudo-object v2)
      (const v1 1)
      (if-eqz v1 :lbl)

      (.pos:dbg_0 "LFoo;.caller:()V" "Foo.java" 10)
      (invoke-static (v2) "LFoo;.a:(Ljava/lang/String;)Lcom/redex/UnreachableException;")
      (move-result-object v0)
      (throw v0)

      (:lbl)
      (.pos:dbg_1 "LFoo;.caller:()V" "Foo.java" 20)
      (invoke-static (v2) "LFoo;.a:(Ljava/lang/String;)Lcom/redex/UnreachableException;")
      (move-result-object v0)
      (throw v0)
    )
  )");

  EXPECT_CODE_EQ(expected_code.get(), code);
}

// Don't dedup invocations to methods marked as dont-inline
TEST_F(DedupBlocksTest, dont_dedup_dont_inline) {
  auto callee_code = assembler::ircode_from_string(R"(
    (
      (return-void)
    )
  )");
  auto* callee = get_fresh_method("bar");
  callee->rstate.set_dont_inline();
  callee->set_code(std::move(callee_code));

  auto input_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 1)
      (if-eqz v1 :lbl)

      (invoke-static () "LTestClass.bar:()V")
      (return-object v0)

      (:lbl)
      (invoke-static () "LTestClass.bar:()V")
      (return-object v0)
    )
  )");
  auto* method = get_fresh_method("dont_dedup_dont_inline");
  method->set_code(std::move(input_code));
  auto* code = method->get_code();

  run_dedup_blocks();

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 1)
      (if-eqz v1 :lbl)

      (invoke-static () "LTestClass.bar:()V")
      (return-object v0)

      (:lbl)
      (invoke-static () "LTestClass.bar:()V")
      (return-object v0)
    )
  )");

  EXPECT_CODE_EQ(expected_code.get(), code);
}

TEST_F(DedupBlocksTest, retainPositionWhenMayThrow) {
  using namespace dex_asm;
  DexMethod* method = get_fresh_method("postfixSwitchCase");

  const auto* str = R"(
    (
      (.pos:dbg_0 "LFoo;.caller:()V" "Foo.java" 10)
      (const v0 0)
      (const v1 1)
      (switch v0 (:a :b :c))

      (:a 0)
      (return v0)

      (:b 1)
      (const v1 1)
      (invoke-static () "LMay;.throw:()V")
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v1)

      (:c 2)
      (.pos:dbg_1 "LFoo;.caller:()V" "Foo.java" 20)
      (const v0 0)
      (invoke-static () "LMay;.throw:()V")
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v1)
    )
  )";

  auto code = assembler::ircode_from_string(str);
  method->set_code(std::move(code));

  run_dedup_blocks();

  const auto* expected_str = R"(
    (
      (.pos:dbg_0 "LFoo;.caller:()V" "Foo.java" 10)
      (const v0 0)
      (const v1 1)
      (switch v0 (:a :b :c))

      (:a 0)
      (return v0)

      (:c 2)
      (.pos:dbg_1 "LFoo;.caller:()V" "Foo.java" 20)
      (const v0 0)
      (goto :d)

      (:b 1)
      (.pos:dbg_0 "LFoo;.caller:()V" "Foo.java" 10)
      (const v1 1)

      (:d)
      (.pos:dbg_2 "LFoo;.caller:()V" "Foo.java" 10)
      (invoke-static () "LMay;.throw:()V")
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return v1)
    )
  )";
  auto expected_code = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected_code.get(), method->get_code());

  // The shared tail runs for both `:b` (line 10) and `:c` (line 20), so its
  // copy of line 10 is marked. `:b`'s own `const` was never folded, so the
  // copy stays a separate entry rather than being merged into the unmarked
  // position in front of it.
  std::vector<DexPosition*> line_10;
  for (auto& mie : *method->get_code()) {
    if (mie.type == MFLOW_POSITION && mie.pos->line == 10) {
      line_10.push_back(mie.pos.get());
    }
  }
  ASSERT_EQ(line_10.size(), 3u);
  EXPECT_FALSE(line_10[0]->is_unreliable());
  EXPECT_FALSE(line_10[1]->is_unreliable());
  EXPECT_TRUE(line_10[2]->is_unreliable());
}

// The following two test cases illustrate an edge case we can work on
// to improve build time. The handling of deduping four throws takes
// two iterations. While it may be done in one iteration.
TEST_F(DedupBlocksTest, blockWithIterativeLimit1) {
  auto input_code = assembler::ircode_from_string(R"(
    (
      (:a)
      (const v0 0)
      (const v1 0)
      (const v2 1)
      (if-eqz v0 :h)

      (:b)
      (if-eqz v1 :j)

      (:c)
      (if-eqz v2 :i)

      (:d)
      (const-class "LTestClass")
      (move-result-pseudo-object v3)
      (monitor-enter v3)

      (:e)
      (new-instance "LTestClass")
      (move-result-pseudo-object v4)
      (invoke-direct (v4 v2) "LTestClass.<init>:(I)V")

      (:f)
      (move-exception v4)
      (monitor-exit v3)

      (:g)
      (throw v4)
      (goto :n)

      (:h)
      (new-instance "Ljava/lang/Throwable;")
      (move-result-pseudo-object v4)
      (invoke-direct (v4 v2) "Ljava/lang/Throwable;.<init>:(I)V")
      (throw v4)
      (goto :n)

      (:i)
      (new-instance "Ljava/lang/Throwable;")
      (move-result-pseudo-object v6)
      (invoke-direct (v6 v2) "Ljava/lang/Throwable;.<init>:(I)V")
      (throw v6)
      (goto :n)

      (:j)
      (const-class "LTestClass")
      (move-result-pseudo-object v5)
      (monitor-enter v5)

      (:k)
      (new-instance "LTestClass")
      (move-result-pseudo-object v6)
      (invoke-direct (v6 v2) "LTestClass.<init>:(I)V")

      (:l)
      (move-exception v6)
      (monitor-exit v5)

      (:m)
      (throw v6)
      (goto :n)

      (:n)
    )
  )");
  auto* method = get_fresh_method("blockWithIterativeExecution");
  method->set_code(std::move(input_code));
  auto* code = method->get_code();

  run_dedup_blocks_with_iteration(method, 1);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (:a)
      (const v0 0)
      (const v1 0)
      (const v2 1)
      (if-eqz v0 :h)

      (:b)
      (if-eqz v1 :j)

      (:c)
      (if-eqz v2 :i)

      (:d)
      (const-class "LTestClass")
      (move-result-pseudo-object v3)
      (monitor-enter v3)

      (:e)
      (new-instance "LTestClass")
      (move-result-pseudo-object v4)
      (invoke-direct (v4 v2) "LTestClass.<init>:(I)V")

      (:f)
      (move-exception v4)
      (monitor-exit v3)

      (:g)
      (throw v4)

      (:h)
      (new-instance "Ljava/lang/Throwable;")
      (move-result-pseudo-object v4)
      (invoke-direct (v4 v2) "Ljava/lang/Throwable;.<init>:(I)V")
      (goto :g)

      (:i)
      (new-instance "Ljava/lang/Throwable;")
      (move-result-pseudo-object v6)
      (invoke-direct (v6 v2) "Ljava/lang/Throwable;.<init>:(I)V")
      (throw v6)

      (:j)
      (const-class "LTestClass")
      (move-result-pseudo-object v5)
      (monitor-enter v5)

      (:k)
      (new-instance "LTestClass")
      (move-result-pseudo-object v6)
      (invoke-direct (v6 v2) "LTestClass.<init>:(I)V")

      (:l)
      (move-exception v6)
      (monitor-exit v5)

      (:m)
      (throw v6)
    )
  )");

  EXPECT_CODE_EQ(expected_code.get(), code);
}

TEST_F(DedupBlocksTest, blockWithIterativeLimit2) {
  auto input_code = assembler::ircode_from_string(R"(
    (
      (:a)
      (const v0 0)
      (const v1 0)
      (const v2 1)
      (if-eqz v0 :h)

      (:b)
      (if-eqz v1 :j)

      (:c)
      (if-eqz v2 :i)

      (:d)
      (const-class "LTestClass")
      (move-result-pseudo-object v3)
      (monitor-enter v3)

      (:e)
      (new-instance "LTestClass")
      (move-result-pseudo-object v4)
      (invoke-direct (v4 v2) "LTestClass.<init>:(I)V")

      (:f)
      (move-exception v4)
      (monitor-exit v3)

      (:g)
      (throw v4)
      (goto :n)

      (:h)
      (new-instance "Ljava/lang/Throwable;")
      (move-result-pseudo-object v4)
      (invoke-direct (v4 v2) "Ljava/lang/Throwable;.<init>:(I)V")
      (throw v4)
      (goto :n)

      (:i)
      (new-instance "Ljava/lang/Throwable;")
      (move-result-pseudo-object v6)
      (invoke-direct (v6 v2) "Ljava/lang/Throwable;.<init>:(I)V")
      (throw v6)
      (goto :n)

      (:j)
      (const-class "LTestClass")
      (move-result-pseudo-object v5)
      (monitor-enter v5)

      (:k)
      (new-instance "LTestClass")
      (move-result-pseudo-object v6)
      (invoke-direct (v6 v2) "LTestClass.<init>:(I)V")

      (:l)
      (move-exception v6)
      (monitor-exit v5)

      (:m)
      (throw v6)
      (goto :n)

      (:n)
    )
  )");
  auto* method = get_fresh_method("blockWithIterativeExecution");
  method->set_code(std::move(input_code));
  auto* code = method->get_code();

  run_dedup_blocks_with_iteration(method, 2);

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (:a)
      (const v0 0)
      (const v1 0)
      (const v2 1)
      (if-eqz v0 :h)

      (:b)
      (if-eqz v1 :j)

      (:c)
      (if-eqz v2 :i)

      (:d)
      (const-class "LTestClass")
      (move-result-pseudo-object v3)
      (monitor-enter v3)

      (:e)
      (new-instance "LTestClass")
      (move-result-pseudo-object v4)
      (invoke-direct (v4 v2) "LTestClass.<init>:(I)V")

      (:f)
      (move-exception v4)
      (monitor-exit v3)

      (:g)
      (throw v4)

      (:h)
      (new-instance "Ljava/lang/Throwable;")
      (move-result-pseudo-object v4)
      (invoke-direct (v4 v2) "Ljava/lang/Throwable;.<init>:(I)V")
      (goto :g)

      (:j)
      (const-class "LTestClass")
      (move-result-pseudo-object v5)
      (monitor-enter v5)

      (:k)
      (new-instance "LTestClass")
      (move-result-pseudo-object v6)
      (invoke-direct (v6 v2) "LTestClass.<init>:(I)V")

      (:l)
      (move-exception v6)
      (monitor-exit v5)
      (goto :m)

      (:i)
      (new-instance "Ljava/lang/Throwable;")
      (move-result-pseudo-object v6)
      (invoke-direct (v6 v2) "Ljava/lang/Throwable;.<init>:(I)V")

      (:m)
      (throw v6)
    )
  )");

  EXPECT_CODE_EQ(expected_code.get(), code);
}

// Verify that split_postfix preserves source block coverage for blocks ending
// with a may-throw instruction. When split_postfix splits a block at a
// may-throw instruction, the source block covering the post-throw segment gets
// moved to the new split block. After dedup merges the split block with another
// identical block, the original block must still have source block coverage.
TEST_F(DedupBlocksTest, splitPostfixPreservesSourceBlockCoverage) {
  DexMethod* method =
      get_fresh_method("splitPostfixPreservesSourceBlockCoverage");
  method->set_deobfuscated_name(show(method));

  // Two branches sharing a common postfix (add-int, add-int, return-void).
  // Branch A has invoke-static (may-throw) before the common postfix.
  const auto* str = R"(
    (
      (const v0 0)
      (if-eqz v0 :C)

      (invoke-static () "LFoo;.bar:()V")
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return-void)

      (:C)
      (const v1 1)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return-void)
    )
  )";

  auto code = assembler::ircode_from_string(str);
  method->set_code(std::move(code));

  auto& code_ref = *method->get_code();
  code_ref.build_cfg();
  auto& cfg = code_ref.cfg();

  // Add a source block to every non-exit block.
  for (auto* block : cfg.blocks()) {
    if (block == cfg.exit_block()) {
      continue;
    }
    auto sb = std::make_unique<SourceBlock>(
        method->get_deobfuscated_name_or_null(), block->id(),
        std::vector<SourceBlock::Val>{SourceBlock::Val(1.0f, 1.0f)});
    source_blocks::impl::BlockAccessor::push_source_block(block, std::move(sb));
  }

  // Add a second source block after the invoke-static (simulating a
  // throw-delineated segment boundary, like the real-world SB@3).
  for (auto* block : cfg.blocks()) {
    for (auto it = block->begin(); it != block->end(); ++it) {
      if (it->type == MFLOW_OPCODE &&
          it->insn->opcode() == OPCODE_INVOKE_STATIC) {
        auto* first_sb = source_blocks::get_first_source_block(block);
        if (first_sb != nullptr) {
          auto sb_after = std::make_unique<SourceBlock>(*first_sb);
          sb_after->id = 100;
          sb_after->next = nullptr;
          source_blocks::impl::BlockAccessor::insert_source_block_after(
              block, it, std::move(sb_after));
        }
        break;
      }
    }
  }

  dedup_blocks_impl::Config config;
  dedup_blocks_impl::DedupBlocks impl(&config, method);
  impl.run();

  // After dedup, every non-exit block must have a source block, and any block
  // ending with a may-throw instruction must have a source block after it.
  for (auto* block : cfg.blocks()) {
    if (block == cfg.exit_block()) {
      continue;
    }

    auto* sb = source_blocks::get_first_source_block(block);
    EXPECT_NE(sb, nullptr) << "Block B" << block->id()
                           << " missing source block";

    auto last_it = block->get_last_insn();
    if (last_it != block->end() && opcode::can_throw(last_it->insn->opcode())) {
      bool found_sb_after = false;
      for (auto check_it = std::next(IRList::iterator(last_it));
           check_it != block->end();
           ++check_it) {
        if (check_it->type == MFLOW_SOURCE_BLOCK) {
          found_sb_after = true;
          break;
        }
      }
      EXPECT_TRUE(found_sb_after)
          << "Block B" << block->id()
          << " missing source block after may-throw instruction";
    }
  }

  code_ref.clear_cfg();
}

namespace {
// The two duplicate arms of the diamond fixture both define v1; find them.
std::vector<cfg::Block*> v1_defining_blocks(cfg::ControlFlowGraph& cfg) {
  std::vector<cfg::Block*> out;
  for (auto* b : cfg.blocks()) {
    for (auto& mie : *b) {
      if (mie.type == MFLOW_OPCODE && mie.insn->opcode() == OPCODE_CONST &&
          mie.insn->dest() == 1) {
        out.push_back(b);
        break;
      }
    }
  }
  return out;
}
} // namespace

// Golden: DedupBlocks folds two identical arms into one; the survivor's count
// is the SUM of the merged duplicates (10 + 3 = 13), not the MAX (10). This is
// the non-instrument path (`max`->`add`, M11).
TEST_F(DedupBlocksTest, DedupMergesSourceBlockCountsBySum) {
  auto input_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (if-eqz v0 :left)
      (goto :right)
      (:left)
      (const v1 1)
      (goto :middle)
      (:right)
      (const v1 1)
      (:middle)
      (return-void)
    )
  )");
  auto* method = get_fresh_method("DedupMergesSourceBlockCountsBySum");
  method->set_deobfuscated_name(show(method));
  method->set_code(std::move(input_code));
  auto* code = method->get_code();
  code->build_cfg();
  auto& cfg = code->cfg();

  auto arms = v1_defining_blocks(cfg);
  ASSERT_EQ(arms.size(), 2u);
  std::sort(arms.begin(), arms.end(),
            [](cfg::Block* a, cfg::Block* b) { return a->id() < b->id(); });
  const std::array<float, 2> vals = {10.0f, 3.0f};
  for (size_t i = 0; i < 2; i++) {
    auto sb = std::make_unique<SourceBlock>(
        method->get_deobfuscated_name_or_null(), arms[i]->id(),
        std::vector<SourceBlock::Val>{SourceBlock::Val(vals[i], 100.0f)});
    source_blocks::impl::BlockAccessor::push_source_block(arms[i],
                                                          std::move(sb));
  }

  dedup_blocks_impl::Config config;
  dedup_blocks_impl::DedupBlocks impl(&config, method);
  impl.run();

  auto survivors = v1_defining_blocks(cfg);
  ASSERT_EQ(survivors.size(), 1u); // the two arms merged into one
  auto* sb = source_blocks::get_first_source_block(survivors[0]);
  ASSERT_NE(sb, nullptr);
  EXPECT_FLOAT_EQ(sb->get_val(0).value_or(-1.0f), 13.0f); // SUM, not MAX (10)
}

// Binary-NFC: on today's 0/1 data the same merge preserves support (`add>0` iff
// `max>0`) -- the merged arm stays covered and no surviving SB is zeroed.
TEST_F(DedupBlocksTest, DedupSourceBlockMergeIsBinaryNfc) {
  auto input_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (if-eqz v0 :left)
      (goto :right)
      (:left)
      (const v1 1)
      (goto :middle)
      (:right)
      (const v1 1)
      (:middle)
      (return-void)
    )
  )");
  auto* method = get_fresh_method("DedupSourceBlockMergeIsBinaryNfc");
  method->set_deobfuscated_name(show(method));
  method->set_code(std::move(input_code));
  auto* code = method->get_code();
  code->build_cfg();
  auto& cfg = code->cfg();

  // Boolean data: every block covered at val = 1.
  for (auto* b : cfg.blocks()) {
    if (b == cfg.exit_block()) {
      continue;
    }
    auto sb = std::make_unique<SourceBlock>(
        method->get_deobfuscated_name_or_null(), b->id(),
        std::vector<SourceBlock::Val>{SourceBlock::Val(1.0f, 1.0f)});
    source_blocks::impl::BlockAccessor::push_source_block(b, std::move(sb));
  }

  dedup_blocks_impl::Config config;
  dedup_blocks_impl::DedupBlocks impl(&config, method);
  impl.run();

  // Support preserved: no surviving SB is zeroed, and the merged arm is covered
  // (val = 1 + 1 = 2 > 0 -- the point is `>0`, not the magnitude).
  auto survivors = v1_defining_blocks(cfg);
  ASSERT_EQ(survivors.size(), 1u);
  auto* merged = source_blocks::get_first_source_block(survivors[0]);
  ASSERT_NE(merged, nullptr);
  EXPECT_GT(merged->get_val(0).value_or(-1.0f), 0.0f); // still covered
  for (auto* b : cfg.blocks()) {
    source_blocks::foreach_source_block(b, [&](SourceBlock* sb) {
      auto v = sb->get_val(0);
      if (v) {
        EXPECT_GT(*v, 0.0f) << "a covered SB was zeroed by the merge";
      }
    });
  }
}

// Verify that normal dedup behavior (postfix deduplication) is not regressed
// by the source block coverage fix.
TEST_F(DedupBlocksTest, splitPostfixNormalBehaviorPreserved) {
  DexMethod* method = get_fresh_method("splitPostfixNormalBehaviorPreserved");
  method->set_deobfuscated_name(show(method));

  const auto* str = R"(
    (
      (const v0 0)
      (if-eqz v0 :C)

      (invoke-static () "LFoo;.bar:()V")
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return-void)

      (:C)
      (const v1 1)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return-void)
    )
  )";

  auto code_val = assembler::ircode_from_string(str);
  method->set_code(std::move(code_val));

  run_dedup_blocks();

  const auto* expected_str = R"(
    (
      (const v0 0)
      (if-eqz v0 :C)

      (invoke-static () "LFoo;.bar:()V")

      (:F)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return-void)

      (:C)
      (const v1 1)
      (goto :F)
    )
  )";
  auto expected_code = assembler::ircode_from_string(expected_str);
  EXPECT_CODE_EQ(expected_code.get(), method->get_code());
}

// A Remark must be transparent to DedupBlocks' merge decision: two blocks that
// are structurally identical except for their redex-internal remark must merge
// exactly as they would with no remark present, and the discarded duplicate's
// remark must not survive. Guards structural_equals/is_metadata transparency
// and the remove_instructions MFLOW_REMARK handling.
TEST_F(DedupBlocksTest, remarksAreTransparentToWholeBlockMerge) {
  DexMethod* with = get_fresh_method("remarksMergeWith");
  with->set_code(assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (mul-int v0 v0 v0)
      (if-eqz v0 :D)

      (mul-int v0 v0 v0)
      (goto :C)

      (:E)
      (return-void)

      (:C)
      (.remark "P" "c" 1)
      (add-int v0 v0 v0)
      (goto :E)

      (:D)
      (.remark "P" "d" 2)
      (add-int v0 v0 v0)
      (goto :E)
    )
  )"));

  DexMethod* without = get_fresh_method("remarksMergeWithout");
  without->set_code(assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (mul-int v0 v0 v0)
      (if-eqz v0 :D)

      (mul-int v0 v0 v0)
      (goto :C)

      (:E)
      (return-void)

      (:C)
      (add-int v0 v0 v0)
      (goto :E)

      (:D)
      (add-int v0 v0 v0)
      (goto :E)
    )
  )"));

  run_dedup_blocks();

  // Opcodes/structure must be identical with and without the remarks;
  // structural_equals ignores metadata (incl. remarks), so this asserts the
  // merge decision was unaffected by the differing remarks.
  EXPECT_TRUE(with->get_code()->structural_equals(*without->get_code()));

  // The merged-away duplicate's remark is gone; exactly one remark survives.
  size_t remarks = 0;
  for (const auto& mie : *with->get_code()) {
    if (mie.type == MFLOW_REMARK) {
      ++remarks;
    }
  }
  EXPECT_EQ(remarks, 1u);
}

// Regression test for the remark-transparency of split_postfix source-block
// restoration. A leading MFLOW_REMARK at a split boundary must not derail the
// restoration: the pre-fix code did split_block->begin()->insn->opcode() and
// keyed off begin()->type, both of which misread a leading remark (the MIE
// union aliases IRInstruction* with unique_ptr<Remark>). Mirrors
// splitPostfixPreservesSourceBlockCoverage, but places a remark immediately
// before the throw-delineated source block so it heads the moved segment.
TEST_F(DedupBlocksTest, splitPostfixSourceBlockRestorationSkipsLeadingRemark) {
  DexMethod* method =
      get_fresh_method("splitPostfixSourceBlockRestorationSkipsLeadingRemark");
  method->set_deobfuscated_name(show(method));

  const auto* str = R"(
    (
      (const v0 0)
      (if-eqz v0 :C)

      (invoke-static () "LFoo;.bar:()V")
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return-void)

      (:C)
      (const v1 1)
      (add-int v0 v0 v0)
      (add-int v0 v0 v0)
      (return-void)
    )
  )";
  method->set_code(assembler::ircode_from_string(str));

  auto& code_ref = *method->get_code();
  code_ref.build_cfg();
  auto& cfg = code_ref.cfg();

  // A source block at every non-exit block head.
  for (auto* block : cfg.blocks()) {
    if (block == cfg.exit_block()) {
      continue;
    }
    auto sb = std::make_unique<SourceBlock>(
        method->get_deobfuscated_name_or_null(), block->id(),
        std::vector<SourceBlock::Val>{SourceBlock::Val(1.0f, 1.0f)});
    source_blocks::impl::BlockAccessor::push_source_block(block, std::move(sb));
  }

  // A second source block after the may-throw invoke, with a remark placed
  // immediately BEFORE it so the throw-delineated segment begins [remark, sb].
  const auto* producer = DexString::make_string("P");
  const auto* val_str = DexString::make_string("");
  for (auto* block : cfg.blocks()) {
    for (auto it = block->begin(); it != block->end(); ++it) {
      if (it->type == MFLOW_OPCODE &&
          it->insn->opcode() == OPCODE_INVOKE_STATIC) {
        auto* first_sb = source_blocks::get_first_source_block(block);
        if (first_sb != nullptr) {
          auto sb_after = std::make_unique<SourceBlock>(*first_sb);
          sb_after->id = 100;
          sb_after->next = nullptr;
          source_blocks::impl::BlockAccessor::insert_source_block_after(
              block, it, std::move(sb_after));
          // Put the remark between the invoke and sb@100 so it leads the moved
          // segment after the split.
          block->insert_before(std::next(IRList::iterator(it)),
                               std::make_unique<Remark>(producer, val_str, 7));
        }
        break;
      }
    }
  }

  dedup_blocks_impl::Config config;
  dedup_blocks_impl::DedupBlocks impl(&config, method);
  impl.run();

  // Every non-exit block still has source-block coverage, and any may-throw
  // block still has a source block after the throwing instruction -- proving
  // the leading remark did not derail restoration (and did not crash on the
  // union).
  for (auto* block : cfg.blocks()) {
    if (block == cfg.exit_block()) {
      continue;
    }
    EXPECT_NE(source_blocks::get_first_source_block(block), nullptr)
        << "Block B" << block->id() << " missing source block";

    auto last_it = block->get_last_insn();
    if (last_it != block->end() && opcode::can_throw(last_it->insn->opcode())) {
      bool found_sb_after = false;
      for (auto check_it = std::next(IRList::iterator(last_it));
           check_it != block->end();
           ++check_it) {
        if (check_it->type == MFLOW_SOURCE_BLOCK) {
          found_sb_after = true;
          break;
        }
      }
      EXPECT_TRUE(found_sb_after)
          << "Block B" << block->id()
          << " missing source block after may-throw instruction";
    }
  }

  code_ref.clear_cfg();
}

namespace {

// The position in effect at the first instruction that can throw, which is the
// only kind of position a stack trace can land on.
DexPosition* position_at_first_throwing_insn(IRCode* code) {
  DexPosition* pos = nullptr;
  for (auto& mie : *code) {
    if (mie.type == MFLOW_POSITION) {
      pos = mie.pos.get();
    } else if (mie.type == MFLOW_OPCODE &&
               opcode::can_throw(mie.insn->opcode())) {
      return pos;
    }
  }
  return nullptr;
}

} // namespace

// Two arms whose instructions are identical but whose source lines are not.
// Folding them leaves one line standing for both, and the survivor has to say
// so. The arms also carry a different NUMBER of position entries, which is the
// case that breaks any pairing done by MethodItemEntry ordinal rather than by
// instruction ordinal -- block equality ignores positions, so this is legal
// input, not a contrivance.
TEST_F(DedupBlocksTest, mergedBlocksMarkTheSurvivingPositionUnreliable) {
  DexMethod* method = get_fresh_method("mergedBlocksMarkUnreliable");

  const auto* str = R"(
    (
      (const v0 0)
      (if-eqz v0 :left)
      (.pos "LTestClass;.m:()V" "Test.java" 20)
      (invoke-static () "LTestClass;.helper:()V")
      (return-void)
      (:left)
      (.pos "LTestClass;.m:()V" "Test.java" 30)
      (.pos "LTestClass;.m:()V" "Test.java" 31)
      (invoke-static () "LTestClass;.helper:()V")
      (return-void)
    )
  )";
  auto code = assembler::ircode_from_string(str);
  method->set_code(std::move(code));
  run_dedup_blocks();

  auto* pos = position_at_first_throwing_insn(method->get_code());
  ASSERT_NE(pos, nullptr);
  EXPECT_TRUE(pos->is_unreliable());
}

// The same shape, but both arms report the same line. Folding them costs no
// accuracy -- the surviving line was already correct for both -- so nothing is
// recorded. It is not upgraded either: agreement here proves only that these
// two halves agree, not that the line is the only place the code came from.
TEST_F(DedupBlocksTest, mergedBlocksAgreeingOnTheirLineRecordNothing) {
  DexMethod* method = get_fresh_method("mergedBlocksAgreeing");

  const auto* str = R"(
    (
      (const v0 0)
      (if-eqz v0 :left)
      (.pos "LTestClass;.m:()V" "Test.java" 20)
      (invoke-static () "LTestClass;.helper:()V")
      (return-void)
      (:left)
      (.pos "LTestClass;.m:()V" "Test.java" 20)
      (invoke-static () "LTestClass;.helper:()V")
      (return-void)
    )
  )";
  auto code = assembler::ircode_from_string(str);
  method->set_code(std::move(code));
  run_dedup_blocks();

  auto* pos = position_at_first_throwing_insn(method->get_code());
  ASSERT_NE(pos, nullptr);
  EXPECT_FALSE(pos->is_unreliable());
}

// Three arms folding into one. The survivor stands for all of them, so one
// disagreement anywhere in the group is enough to make its line unreliable.
TEST_F(DedupBlocksTest, mergedBlocksMarkUnreliableAcrossAThreeWayGroup) {
  DexMethod* method = get_fresh_method("mergedBlocksThreeWay");

  const auto* str = R"(
    (
      (const v0 0)
      (if-eqz v0 :second)
      (if-eqz v0 :third)
      (.pos "LTestClass;.m:()V" "Test.java" 20)
      (invoke-static () "LTestClass;.helper:()V")
      (return-void)
      (:second)
      (.pos "LTestClass;.m:()V" "Test.java" 30)
      (invoke-static () "LTestClass;.helper:()V")
      (return-void)
      (:third)
      (.pos "LTestClass;.m:()V" "Test.java" 40)
      (invoke-static () "LTestClass;.helper:()V")
      (return-void)
    )
  )";
  auto code = assembler::ircode_from_string(str);
  method->set_code(std::move(code));
  run_dedup_blocks();

  auto* pos = position_at_first_throwing_insn(method->get_code());
  ASSERT_NE(pos, nullptr);
  EXPECT_TRUE(pos->is_unreliable());
}

// Neither arm opens with a position. The effective position is outside the
// duplicate block, and marking it could affect code this merge never touched.
// Count the merge as unrecorded instead of reaching back through CFG order,
// which is not dominance order.
TEST_F(DedupBlocksTest, mergedBlocksDoNotMarkAPositionOutsideTheBlock) {
  DexMethod* method = get_fresh_method("mergedBlocksOutsidePosition");

  const auto* str = R"(
    (
      (.pos "LTestClass;.m:()V" "Test.java" 10)
      (const v0 0)
      (if-eqz v0 :left)
      (invoke-static () "LTestClass;.helper:()V")
      (return-void)
      (:left)
      (invoke-static () "LTestClass;.helper:()V")
      (return-void)
    )
  )";
  auto code = assembler::ircode_from_string(str);
  method->set_code(std::move(code));
  run_dedup_blocks();

  auto* pos = position_at_first_throwing_insn(method->get_code());
  ASSERT_NE(pos, nullptr);
  EXPECT_EQ(pos->line, 10u);
  EXPECT_FALSE(pos->is_unreliable());
}

// Java-like shape of the two arms (hand-written, not compiler output): each
// arm calls `helper()` on its own line, then runs `callee()`'s line 5 inlined
// under line 20.
//
//   kept arm:    line 20: helper();   line 20 -> Callee.java:5: helper();
//   folded arm:  line 21: helper();   line 20 -> Callee.java:5: helper();
//
// Line 20 also stands for line 21, but the inlined line has the same caller and
// callee lines in both arms, so it still names one place even though its
// caller is the position that gets marked.
TEST_F(DedupBlocksTest, mergedBlocksKeepInlinedLineExactWhenItsCallerIsMarked) {
  DexMethod* method = get_fresh_method("mergedBlocksInlinedCaller");

  const auto* str = R"(
    (
      (const v0 0)
      (if-eqz v0 :left)
      (.pos:dbg_0 "LTestClass;.m:()V" "Test.java" 20)
      (invoke-static () "LTestClass;.helper:()V")
      (.pos:dbg_1 "LTestClass;.callee:()V" "Callee.java" 5 dbg_0)
      (invoke-static () "LTestClass;.helper:()V")
      (return-void)
      (:left)
      (.pos "LTestClass;.m:()V" "Test.java" 21)
      (invoke-static () "LTestClass;.helper:()V")
      (.pos:dbg_2 "LTestClass;.m:()V" "Test.java" 20)
      (.pos:dbg_3 "LTestClass;.callee:()V" "Callee.java" 5 dbg_2)
      (invoke-static () "LTestClass;.helper:()V")
      (return-void)
    )
  )";
  auto code = assembler::ircode_from_string(str);
  method->set_code(std::move(code));
  run_dedup_blocks();

  DexPosition* caller = position_at_first_throwing_insn(method->get_code());
  ASSERT_NE(caller, nullptr);
  ASSERT_EQ(caller->line, 20u);
  std::vector<DexPosition*> inlined;
  for (auto& mie : *method->get_code()) {
    if (mie.type == MFLOW_POSITION && mie.pos->line == 5) {
      inlined.push_back(mie.pos.get());
    }
  }
  ASSERT_EQ(inlined.size(), 1u);
  ASSERT_EQ(inlined[0]->parent, caller);
  EXPECT_TRUE(caller->is_unreliable());
  EXPECT_FALSE(inlined[0]->is_unreliable());
}
