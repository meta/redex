/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "Debug.h"
#include "OptionalIO.h"
#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include "CppUtil.h"
#include "Creators.h"
#include "IRAssembler.h"
#include "RedexContext.h"
#include "RedexTest.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "SwitchEquivFinder.h"

using namespace testing;

namespace {
void setup() {
  std::vector<std::string> empty_types_to_create = {"LBar;", "LBaz;", "LBoo;",
                                                    "LMoo;"};
  for (const auto& s : empty_types_to_create) {
    ClassCreator cc(DexType::make_type(s));
    cc.set_super(type::java_lang_Object());
    cc.create();
  }
  ClassCreator cc(DexType::make_type("LFoo;"));
  cc.set_super(type::java_lang_Object());
  auto* field = DexField::make_field("LFoo;.table:[LBar;")
                    ->make_concrete(ACC_PUBLIC | ACC_STATIC);
  cc.add_field(field);
  cc.create();
}

void print_extra_loads(const SwitchEquivFinder::ExtraLoads& extra_loads) {
  for (const auto& [b, loads] : UnorderedIterable(extra_loads)) {
    std::cerr << "B" << b->id() << "{";
    bool first = true;
    for (const auto& [r, i] : loads) {
      if (!first) {
        std::cerr << ", ";
      }
      std::cerr << "v" << r << " ~ " << SHOW(i);
      first = false;
    }
    std::cerr << "} " << "\n";
  }
}

// Assumes the first instruction in the block is a const instruction and returns
// the literal.
inline int64_t get_first_instruction_literal(cfg::Block* b) {
  return b->get_first_insn()->insn->get_literal();
}

cfg::InstructionIterator get_first_branch(cfg::ControlFlowGraph& cfg) {
  auto iterable = InstructionIterable(cfg);
  for (auto it = iterable.begin(); it != iterable.end(); ++it) {
    if (opcode::is_branch(it->insn->opcode())) {
      return it;
    }
  }
  return iterable.end();
}

cfg::InstructionIterator get_first_occurrence(cfg::ControlFlowGraph& cfg,
                                              const IROpcode& opcode) {
  auto iterable = InstructionIterable(cfg);
  for (auto it = iterable.begin(); it != iterable.end(); ++it) {
    if (it->insn->opcode() == opcode) {
      return it;
    }
  }
  return iterable.end();
}
} // namespace

class SwitchEquivFinderTest : public RedexTest {
 protected:
  void expect_nonconstant_comparison_rejected(const std::string& ir,
                                              bool instrument_mode = false) {
    const auto original_instrument_mode = g_redex->instrument_mode;
    g_redex->instrument_mode = instrument_mode;
    ScopeGuard restore_instrument_mode{[original_instrument_mode]() {
      g_redex->instrument_mode = original_instrument_mode;
    }};
    for (auto strategy :
         {SwitchEquivFinder::NOT_ALLOWED, SwitchEquivFinder::EXECUTION_ORDER}) {
      for (uint32_t threshold : {0u, 50u}) {
        auto code = assembler::ircode_from_string(ir);
        code->build_cfg();
        auto& cfg = code->cfg();
        const auto before = show(cfg);
        auto root = get_first_branch(cfg);
        SwitchEquivFinder finder(&cfg, root, 0, threshold, nullptr, strategy,
                                 {});
        EXPECT_FALSE(finder.success());
        EXPECT_TRUE(finder.key_to_case().empty());
        EXPECT_TRUE(finder.extra_loads().empty());
        EXPECT_EQ(before, show(cfg));
      }
    }
  }
};

TEST_F(SwitchEquivFinderTest, nonconstant_comparison_shared_default) {
  expect_nonconstant_comparison_rejected(R"(
    (
      (load-param v0)
      (load-param v1)
      (const v2 1)
      (if-eq v0 v2 :one)
      (if-eq v0 v1 :default)
      (if-eqz v0 :zero)
      (:default)
      (const v3 0)
      (return v3)
      (:one)
      (const v3 10)
      (return v3)
      (:zero)
      (const v3 20)
      (return v3)
    )
  )");
}

TEST_F(SwitchEquivFinderTest, nonconstant_comparison_duplicate_key) {
  expect_nonconstant_comparison_rejected(R"(
    (
      (load-param v0)
      (load-param v1)
      (const v2 7)
      (if-ne v0 v2 :default)
      (if-eq v0 v1 :equal)
      (const v3 40)
      (return v3)
      (:equal)
      (const v3 20)
      (return v3)
      (:default)
      (const v3 0)
      (return v3)
    )
  )");
}

TEST_F(SwitchEquivFinderTest, nonconstant_comparison_root) {
  expect_nonconstant_comparison_rejected(R"(
    (
      (load-param v0)
      (load-param v1)
      (if-eq v1 v0 :default)
      (if-eqz v0 :zero)
      (:default)
      (const v2 0)
      (return v2)
      (:zero)
      (const v2 20)
      (return v2)
    )
  )");
}

TEST_F(SwitchEquivFinderTest, nonconstant_comparison_class) {
  setup();
  expect_nonconstant_comparison_rejected(R"(
    (
      (load-param-object v0)
      (load-param-object v1)
      (const-class "LBar;")
      (move-result-pseudo-object v2)
      (if-eq v0 v2 :bar)
      (if-eq v0 v1 :default)
      (const-class "LBaz;")
      (move-result-pseudo-object v2)
      (if-eq v0 v2 :baz)
      (:default)
      (const v3 0)
      (return v3)
      (:bar)
      (const v3 1)
      (return v3)
      (:baz)
      (const v3 3)
      (return v3)
    )
  )");
}

TEST_F(SwitchEquivFinderTest, nonconstant_comparison_divergent_loads) {
  expect_nonconstant_comparison_rejected(R"(
    (
      (load-param v0)
      (load-param v1)
      (const v2 1)
      (if-eq v0 v2 :one)
      (const v2 2)
      (if-eq v0 v1 :default)
      (const v2 3)
      (if-eqz v0 :zero)
      (:default)
      (return v2)
      (:one)
      (const v3 10)
      (return v3)
      (:zero)
      (return v2)
    )
  )");
}

TEST_F(SwitchEquivFinderTest, nonconstant_comparison_source_blocks) {
  expect_nonconstant_comparison_rejected(R"(
    (
      (load-param v0)
      (load-param v1)
      (const v2 1)
      (if-eq v0 v2 :one)
      (.src_block "LNonConstant;.f:(II)I" 0 (1.0 1.0))
      (if-eq v0 v1 :default)
      (.src_block "LNonConstant;.f:(II)I" 1 (1.0 1.0))
      (if-eqz v0 :zero)
      (:default)
      (const v3 0)
      (return v3)
      (:one)
      (const v3 10)
      (return v3)
      (:zero)
      (const v3 20)
      (return v3)
    )
  )",
                                         true);
}

TEST_F(SwitchEquivFinderTest, nonconstant_comparison_same_register) {
  expect_nonconstant_comparison_rejected(R"(
    (
      (load-param v0)
      (const v1 7)
      (if-ne v0 v1 :default)
      (if-eq v0 v0 :equal)
      (:default)
      (const v2 0)
      (return v2)
      (:equal)
      (const v2 20)
      (return v2)
    )
  )");
}

// A sled -- a block holding only SourceBlocks -- is replaced by a copy of its
// successor, so the successor's count ends up in two places. Total execution
// mass across the copies must equal what the original block had.
TEST_F(SwitchEquivFinderTest, sled_normalization_splits_the_successors_count) {
  g_redex->preserve_count_integrity = true;
  ScopeGuard restore_count_integrity{
      []() { g_redex->preserve_count_integrity = false; }};

  auto* method = assembler::method_from_string(R"(
    (method (public static) "LSled;.m:(I)V"
      (
        (load-param v0)
        (.src_block "LSled;.m:(I)V" 0 (10.0 1.0))
        (if-eqz v0 :other)

        (.src_block "LSled;.m:(I)V" 1 (4.0 1.0))
        ; placeholder so the block survives cfg construction; removed below to
        ; leave a block holding only a SourceBlock, as seen in the wild
        (const-class "LBar;")
        (goto :dest)

        (:other)
        (.src_block "LSled;.m:(I)V" 2 (6.0 1.0))
        (const v1 1)
        (goto :dest)

        (:dest)
        (.src_block "LSled;.m:(I)V" 3 (10.0 1.0))
        (return-void)
      )
    )
  )");
  method->get_code()->build_cfg();
  auto& cfg = method->get_code()->cfg();

  for (auto it = cfg::InstructionIterator(cfg, true); !it.is_end(); ++it) {
    if (opcode::is_const_class(it->insn->opcode())) {
      cfg.remove_insn(it);
      break;
    }
  }

  constexpr uint32_t kLeafDupThreshold = 50;
  SwitchEquivEditor::normalize_sled_blocks(&cfg, kLeafDupThreshold);

  // Sum every copy of the successor's SourceBlock (id 3). The successor ran 10
  // times; duplicating it must not manufacture more executions.
  float total = 0.0f;
  for (auto* b : cfg.blocks()) {
    for (auto* sb : source_blocks::gather_source_blocks(b)) {
      if (sb->id == 3) {
        auto v = sb->get_val(0);
        ASSERT_TRUE(v.has_value());
        total += *v;
      }
    }
  }
  EXPECT_FLOAT_EQ(total, 10.0f);
}

// Two sleds sharing one successor run the split twice against the same
// original, which shrinks in between. This path duplicates inside the loop, so
// each copy is taken from the already-reduced `dest` and the shares compose --
// pinning that here, since `move_edges` reaches the same helper with copies
// made up front, where they do not.
TEST_F(SwitchEquivFinderTest, two_sleds_sharing_a_successor_conserve_mass) {
  g_redex->preserve_count_integrity = true;
  ScopeGuard restore_count_integrity{
      []() { g_redex->preserve_count_integrity = false; }};

  auto* method = assembler::method_from_string(R"(
    (method (public static) "LSled2;.m:(I)V"
      (
        (load-param v0)
        (.src_block "LSled2;.m:(I)V" 0 (10.0 1.0))
        (switch v0 (:a :b))

        (.src_block "LSled2;.m:(I)V" 1 (2.0 1.0))
        (const v1 1)
        (goto :dest)

        (:a 0)
        (.src_block "LSled2;.m:(I)V" 2 (3.0 1.0))
        ; placeholders so the blocks survive cfg construction; both removed
        ; below to leave two blocks holding only a SourceBlock
        (const-class "LBar;")
        (goto :dest)

        (:b 1)
        (.src_block "LSled2;.m:(I)V" 3 (5.0 1.0))
        (const-class "LBaz;")
        (goto :dest)

        (:dest)
        (.src_block "LSled2;.m:(I)V" 4 (10.0 1.0))
        (return-void)
      )
    )
  )");
  method->get_code()->build_cfg();
  auto& cfg = method->get_code()->cfg();

  // Remove BOTH placeholders, leaving two sleds.
  bool removed_any = true;
  while (removed_any) {
    removed_any = false;
    for (auto it = cfg::InstructionIterator(cfg, true); !it.is_end(); ++it) {
      if (opcode::is_const_class(it->insn->opcode())) {
        cfg.remove_insn(it);
        removed_any = true;
        break;
      }
    }
  }

  constexpr uint32_t kLeafDupThreshold = 50;
  SwitchEquivEditor::normalize_sled_blocks(&cfg, kLeafDupThreshold);

  // The successor ran 10 times, reached 3 + 5 + 2. Duplicating it once per sled
  // must redistribute that count, not manufacture more.
  float total = 0.0f;
  for (auto* b : cfg.blocks()) {
    for (auto* sb : source_blocks::gather_source_blocks(b)) {
      if (sb->id == 4) {
        auto v = sb->get_val(0);
        ASSERT_TRUE(v.has_value());
        total += *v;
      }
    }
  }
  EXPECT_FLOAT_EQ(total, 10.0f);
}

TEST_F(SwitchEquivFinderTest, if_chain) {
  setup();

  auto code = assembler::ircode_from_string(R"(
    (
      (load-param-object v1)
      (sget-object "LFoo;.table:[LBar;")
      (move-result-pseudo v0)
      (invoke-virtual (v1) "LEnum;.ordinal:()I")
      (move-result v1)
      (aget v0 v1)
      (move-result-pseudo v0)
      (const v2 0)
      (if-eq v2 v0 :case0)

      (const v2 1)
      (if-eq v2 v0 :case1)

      (return v0)

      (:case0)
      (return v0)

      (:case1)
      (invoke-static (v2) "LFoo;.useReg:(I)V")
      (return v1)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();
  SwitchEquivFinder finder(&cfg, get_first_branch(cfg), 0);
  ASSERT_TRUE(finder.success());
  ASSERT_TRUE(finder.are_keys_uniform(SwitchEquivFinder::KeyKind::INT));
  bool checked_one = false;
  bool checked_zero = false;
  bool found_fallthrough = false;
  for (const auto& key_and_case : finder.key_to_case()) {
    auto key = key_and_case.first;
    cfg::Block* leaf = key_and_case.second;
    if (SwitchEquivFinder::is_default_case(key)) {
      always_assert(!found_fallthrough);
      found_fallthrough = true;
      continue;
    }
    auto key_int = boost::get<int32_t>(key);
    const auto& extra_loads = finder.extra_loads();
    const auto& search = extra_loads.find(leaf);
    if (key_int == 1) {
      EXPECT_NE(extra_loads.end(), search);
      const auto& loads = search->second;
      EXPECT_EQ(1, loads.size());
      auto reg_and_insn = *loads.begin();
      EXPECT_EQ(2, reg_and_insn.first);
      EXPECT_EQ(OPCODE_CONST, reg_and_insn.second->opcode());
      EXPECT_EQ(1, reg_and_insn.second->get_literal());
      checked_one = true;
    } else if (key_int == 0) {
      EXPECT_EQ(extra_loads.end(), search);
      checked_zero = true;
    }
  }
  EXPECT_TRUE(found_fallthrough);
  EXPECT_TRUE(checked_one);
  EXPECT_TRUE(checked_zero);
  code->clear_cfg();
}

TEST_F(SwitchEquivFinderTest, test_mix_of_if_and_switch) {
  setup();

  // Following IR code was derived from:
  // public static final String foo(int i) {
  //     switch (i) {
  //     case 1:
  //         return "a";
  //     case 2:
  //         return "b";
  //     case 3:
  //         return "a";
  //     case 4:
  //         return "b";
  //     case 5:
  //         return "a";
  //     case 6:
  //         return "b";
  //     case 7:
  //         return "a";
  //     case 8:
  //         return "b";
  //     case 9:
  //         return "a";
  //     case 10:
  //         return "b";
  //     case 99:
  //         return "z";
  //     default:
  //         return "";
  //     }
  // }
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v2)
      (const-string b)
      (move-result-pseudo-object v0)
      (const-string a)
      (move-result-pseudo-object v1)
      (const v0 99)
      (if-eq v2 v0 :L10)
      (switch v2 (:L0 :L1 :L2 :L3 :L4 :L5 :L6 :L7 :L8 :L9))
      (const-string "")
      (move-result-pseudo-object v2)
      (return-object v2)
      (:L0 10)
      (return-object v0)
      (:L1 9)
      (return-object v1)
      (:L2 8)
      (return-object v0)
      (:L3 7)
      (return-object v1)
      (:L4 6)
      (return-object v0)
      (:L5 5)
      (return-object v1)
      (:L6 4)
      (return-object v0)
      (:L7 3)
      (return-object v1)
      (:L8 2)
      (return-object v0)
      (:L9 1)
      (return-object v1)
      (:L10)
      (const-string z)
      (move-result-pseudo-object v2)
      (return-object v2)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();
  SwitchEquivFinder finder(&cfg, get_first_branch(cfg), /* switching_reg */ 2);
  EXPECT_TRUE(finder.success());
  EXPECT_EQ(finder.key_to_case().size(), 12);
  bool has_default_case{false};
  std::vector<int32_t> keys;
  for (auto&& [key, block] : finder.key_to_case()) {
    if (SwitchEquivFinder::is_default_case(key)) {
      has_default_case = true;
    } else {
      keys.emplace_back(boost::get<int32_t>(key));
    }
  }
  EXPECT_TRUE(has_default_case);
  EXPECT_THAT(
      keys, ::testing::UnorderedElementsAre(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 99));
}

TEST_F(SwitchEquivFinderTest, extra_loads_intersect) {
  setup();

  auto code = assembler::ircode_from_string(R"(
    (
      (const v2 0)
      (sget-object "LFoo;.table:[LBar;")
      (move-result-pseudo v0)
      (const v1 0)
      (invoke-virtual (v1) "LEnum;.ordinal:()I")
      (move-result v1)
      (aget v0 v1)
      (move-result-pseudo v0)
      (const v1 1)
      (if-gt v0 v1 :greater_than_one)

      (const v1 1)
      (if-ne v0 v1 :not_one)

      (:fallthrough)
      (return-void)

      (:greater_than_one)
      (const v2 1)
      (if-eqz v0 :case0)
      (goto :fallthrough)

      (:not_one)
      (if-eqz v0 :case0)
      (goto :fallthrough)

      (:case0)
      (invoke-static (v2) "LFoo;.useReg:(I)V")
      (return v0)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();
  SwitchEquivFinder finder(&cfg, get_first_branch(cfg), 0);
  ASSERT_FALSE(finder.success());
}

TEST_F(SwitchEquivFinderTest, extra_loads_wide) {
  setup();

  auto code = assembler::ircode_from_string(R"(
    (
      (const v3 0)
      (sget-object "LFoo;.table:[LBar;")
      (move-result-pseudo v0)
      (const v1 0)
      (invoke-virtual (v1) "LEnum;.ordinal:()I")
      (move-result v1)
      (aget v0 v1)
      (move-result-pseudo v0)
      (const v1 1)
      (if-gt v0 v1 :greater_than_one)

      (const v1 1)
      (if-ne v0 v1 :not_one)

      (:fallthrough)
      (return-void)

      (:greater_than_one)
      (const v3 1)
      (const-wide v2 1)
      (if-eqz v0 :case0)
      (goto :fallthrough)

      (:not_one)
      (const v3 1)
      (if-eqz v0 :case0)
      (goto :fallthrough)

      (:case0)
      (invoke-static (v3) "LFoo;.useReg:(I)V")
      (return v0)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();
  SwitchEquivFinder finder(&cfg, get_first_branch(cfg), 0);
  ASSERT_FALSE(finder.success());
}

TEST_F(SwitchEquivFinderTest, extra_loads_wide2) {
  setup();

  auto code = assembler::ircode_from_string(R"(
    (
      (sget-object "LFoo;.table:[LBar;")
      (move-result-pseudo v0)
      (const v1 0)
      (invoke-virtual (v1) "LEnum;.ordinal:()I")
      (move-result v1)
      (aget v0 v1)
      (move-result-pseudo v0)
      (const v1 1)
      (if-lt v0 v1 :less_than_one)

      (:fallthrough)
      (return-void)

      (:less_than_one)
      (const-wide v2 1)
      (const v2 1)
      (if-eqz v0 :case0)
      (goto :fallthrough)

      (:case0)
      (invoke-static (v2) "LFoo;.useReg:(I)V")
      (return v0)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();
  SwitchEquivFinder finder(&cfg, get_first_branch(cfg), 0);
  ASSERT_FALSE(finder.success());
  code->clear_cfg();
}

TEST_F(SwitchEquivFinderTest, overwrite) {
  setup();

  auto code = assembler::ircode_from_string(R"(
    (
      (sget-object "LFoo;.table:[LBar;")
      (move-result-pseudo v0)
      (const v1 0)
      (invoke-virtual (v1) "LEnum;.ordinal:()I")
      (move-result v1)
      (aget v0 v1)
      (move-result-pseudo v1)
      (const v2 0)
      (if-le v2 v1 :case0)

      ; overwrite the switching reg, making this block a leaf
      (const v1 1)
      (if-eq v2 v1 :case1)

      (:case0)
      (return v0)

      (:case1)
      (return v1)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();
  SwitchEquivFinder finder(&cfg, get_first_branch(cfg), 1);
  ASSERT_FALSE(finder.success());
  code->clear_cfg();
}

TEST_F(SwitchEquivFinderTest, overwrite_wide) {
  setup();

  auto code = assembler::ircode_from_string(R"(
    (
      (sget-object "LFoo;.table:[LBar;")
      (move-result-pseudo v0)
      (const v1 0)
      (invoke-virtual (v1) "LEnum;.ordinal:()I")
      (move-result v1)
      (aget v0 v1)
      (move-result-pseudo v1)
      (const v2 0)
      (if-le v2 v1 :case0)

      ; overwrite the switching reg with the upper half of the load, making this
      ; block a leaf
      (const-wide v0 1)
      (if-eq v2 v1 :case1)

      (:case0)
      (return v0)

      (:case1)
      (return v1)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();
  SwitchEquivFinder finder(&cfg, get_first_branch(cfg), 1);
  ASSERT_FALSE(finder.success());
  code->clear_cfg();
}

TEST_F(SwitchEquivFinderTest, loop) {
  setup();

  auto code = assembler::ircode_from_string(R"(
    (
      (sget-object "LFoo;.table:[LBar;")
      (move-result-pseudo v0)
      (const v1 0)
      (invoke-virtual (v1) "LEnum;.ordinal:()I")
      (move-result v1)
      (aget v0 v1)
      (move-result-pseudo v1)
      (const v2 0)
      (if-le v2 v1 :case0)

      (:loop)
      (const v2 1)
      (if-eq v2 v1 :loop)

      (:case0)
      (return v0)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();
  SwitchEquivFinder finder(&cfg, get_first_branch(cfg), 1);
  ASSERT_FALSE(finder.success());
  code->clear_cfg();
}

TEST_F(SwitchEquivFinderTest, other_entry_points) {
  setup();

  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v2)
      (if-eqz v2 :case1)

      (sget-object "LFoo;.table:[LBar;")
      (move-result-pseudo v0)
      (const v1 0)
      (invoke-virtual (v1) "LEnum;.ordinal:()I")
      (move-result v1)
      (aget v0 v1)
      (move-result-pseudo v1)
      (const v2 0)
      (if-le v2 v1 :case0)

      (const v2 1)
      (if-eq v2 v1 :case1)

      (:case0)
      (return v0)

      (:case1)
      (invoke-static (v2) "LFoo;.useReg:(I)V")
      (return v1)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();
  SwitchEquivFinder finder(&cfg, get_first_occurrence(cfg, OPCODE_IF_LE), 1);
  ASSERT_FALSE(finder.success());
  code->clear_cfg();
}

TEST_F(SwitchEquivFinderTest, goto_default) {
  setup();

  auto code = assembler::ircode_from_string(R"(
    (
      (load-param-object v1)
      (sget-object "LFoo;.table:[LBar;")
      (move-result-pseudo v0)
      (invoke-virtual (v1) "LEnum;.ordinal:()I")
      (move-result v1)
      (aget v0 v1)
      (move-result-pseudo v1)
      (switch v1 (:a :b))

      (:fallthrough)
      (return-void)

      (:a 0)
      (invoke-static (v1) "LFoo;.useReg:(I)V")
      (goto :fallthrough)

      (:b 1)
      (invoke-static (v1) "LFoo;.useReg:(I)V")
      (goto :fallthrough)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();
  SwitchEquivFinder finder(&cfg, get_first_branch(cfg), 1);
  ASSERT_TRUE(finder.success());
  code->clear_cfg();
}

TEST_F(SwitchEquivFinderTest, goto_default_stops_at_unsupported) {
  setup();

  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (const v1 1)
      (const v2 2)

      (if-eq v0 v1 :case1)

      (if-le v0 v2 :inequality)
      (return-void)

      (:inequality)
      (return-void)

      (:case1)
      (return-void)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();
  SwitchEquivFinder finder(
      &cfg, get_first_branch(cfg), 0, SwitchEquivFinder::NO_LEAF_DUPLICATION,
      nullptr, SwitchEquivFinder::DuplicateCaseStrategy::EXECUTION_ORDER, {});
  EXPECT_FALSE(finder.success());
  code->clear_cfg();
}

TEST_F(SwitchEquivFinderTest, divergent_leaf_entry_state) {
  setup();

  auto code = assembler::ircode_from_string(R"(
    (
      (sget-object "LFoo;.table:[LBar;")
      (move-result-pseudo v0)
      (const v2 0)
      (invoke-virtual (v2) "LEnum;.ordinal:()I")
      (move-result v1)
      (aget v0 v1)
      (move-result-pseudo v0)
      (const v1 1)
      (if-eq v0 v1 :end)

      (const v1 2)
      (if-eq v0 v1 :end)

      (const v0 3)
      (return v0)

      (:end)
      (return v1)
    )
  )");

  code->build_cfg();
  auto& cfg = code->cfg();
  SwitchEquivFinder finder(&cfg, get_first_branch(cfg), 0);
  ASSERT_FALSE(finder.success());
  code->clear_cfg();
}

TEST_F(SwitchEquivFinderTest, test_class_switch) {
  setup();

  auto code = assembler::ircode_from_string(R"(
    (
      (load-param-object v1)

      (const-class "LBar;")
      (move-result-pseudo-object v0)
      (if-eq v1 v0 :case0)

      (const-class "LBaz;")
      (move-result-pseudo-object v0)
      (if-eq v1 v0 :case1)

      (:case_default)
      (const v0 -1)
      (goto :out)

      (:case0)
      (const v0 100)
      (goto :out)

      (:case1)
      (const v0 101)

      (:out)
      (return v0)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();
  SwitchEquivFinder finder(&cfg, get_first_branch(cfg), 1);
  EXPECT_TRUE(finder.success());
  EXPECT_TRUE(finder.are_keys_uniform(SwitchEquivFinder::KeyKind::CLASS));
  const auto& key_to_case = finder.key_to_case();
  EXPECT_EQ(key_to_case.size(), 3);

  auto default_case = finder.default_case();
  EXPECT_NE(default_case, std::nullopt);
  EXPECT_EQ(get_first_instruction_literal(*default_case), -1);

  auto* bar_type = DexType::get_type("LBar;");
  auto* bar_block = key_to_case.at(bar_type);
  EXPECT_EQ(get_first_instruction_literal(bar_block), 100);

  auto* baz_type = DexType::get_type("LBaz;");
  auto* baz_block = key_to_case.at(baz_type);
  EXPECT_EQ(get_first_instruction_literal(baz_block), 101);
}

TEST_F(SwitchEquivFinderTest, test_class_switch_with_extra_loads) {
  setup();
  auto* baz_type = DexType::get_type("LBaz;");

  // extra load never gets used in successor block
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param-object v1)

      (const-class "LBar;")
      (move-result-pseudo-object v0)
      (if-eq v1 v0 :case0)

      (const-class "LBaz;")
      (move-result-pseudo-object v0)
      (const-class "LFoo;")
      (move-result-pseudo-object v2)
      (if-eq v1 v0 :case1)

      (:case_default)
      (const v0 -1)
      (goto :out)

      (:case0)
      (const v0 100)
      (goto :out)

      (:case1)
      (const v0 101)

      (:out)
      (return v0)
    )
)");

  {
    code->build_cfg();
    auto& cfg = code->cfg();
    SwitchEquivFinder finder(&cfg, get_first_branch(cfg), 1);
    EXPECT_TRUE(finder.success());
    const auto& extra_loads = finder.extra_loads();
    print_extra_loads(extra_loads);
    EXPECT_EQ(extra_loads.size(), 0);
  }

  // Has an extra allowed instruction from the non-leaf, make sure this is
  // tracked.
  auto code_with_load = assembler::ircode_from_string(R"(
    (
      (load-param-object v1)

      (const-class "LBar;")
      (move-result-pseudo-object v0)
      (if-eq v1 v0 :case0)

      (const-class "LBaz;")
      (move-result-pseudo-object v0)
      (const v2 2000)
      (const v2 200)
      (if-eq v1 v0 :case1)

      (:case_default)
      (const v0 -1)
      (goto :out)

      (:case0)
      (const v0 100)
      (goto :out)

      (:case1)
      (const v0 101)
      (add-int v0 v0 v2)

      (:out)
      (return v0)
    )
)");

  {
    code_with_load->build_cfg();
    auto& cfg = code_with_load->cfg();
    SwitchEquivFinder finder(&cfg, get_first_branch(cfg), 1);
    EXPECT_TRUE(finder.success());
    const auto& extra_loads = finder.extra_loads();
    EXPECT_EQ(extra_loads.size(), 2);
    for (const auto& [b, loads] : UnorderedIterable(extra_loads)) {
      auto id = b->id();
      EXPECT_TRUE(id == 2 || id == 4);
      EXPECT_EQ(loads.size(), 1);
      // v2
      EXPECT_EQ(loads.begin()->first, 2);
    }
    // Load of v2 above should be counted as an extra load for case1 and
    // case_default, should get tracked as the surviving value of 200.
    auto instructions_copied =
        SwitchEquivEditor::copy_extra_loads_to_leaf_blocks(finder, &cfg);
    EXPECT_EQ(instructions_copied, 2);
    auto* case1 = finder.key_to_case().at(baz_type);
    auto it = case1->get_first_insn();
    EXPECT_EQ(it->insn->opcode(), OPCODE_CONST);
    EXPECT_EQ(it->insn->get_literal(), 200);
    auto* default_case = *finder.default_case();
    it = default_case->get_first_insn();
    EXPECT_EQ(it->insn->get_literal(), 200);
  }

  // Similar to above, but the extra load is from a const-class
  auto code_with_cls_load = assembler::ircode_from_string(R"(
    (
      (load-param-object v1)

      (const-class "LBar;")
      (move-result-pseudo-object v0)
      (if-eq v1 v0 :case0)

      (const-class "LBaz;")
      (move-result-pseudo-object v0)
      (const v2 2000)
      (const-class "LFoo;")
      (move-result-pseudo-object v2)
      (if-eq v1 v0 :case1)

      (:case_default)
      (const v0 -1)
      (invoke-virtual (v2) "Ljava/lang/Object;.hashCode:()I")
      (move-result v0)
      (goto :out)

      (:case0)
      (const v0 100)
      (goto :out)

      (:case1)
      (const v0 101)

      (:out)
      (return v0)
    )
)");

  {
    code_with_cls_load->build_cfg();
    auto& cfg = code_with_cls_load->cfg();
    SwitchEquivFinder finder(&cfg, get_first_branch(cfg), 1);
    EXPECT_TRUE(finder.success());
    const auto& extra_loads = finder.extra_loads();
    EXPECT_EQ(extra_loads.size(), 2);
    for (const auto& [b, loads] : UnorderedIterable(extra_loads)) {
      auto id = b->id();
      EXPECT_TRUE(id == 2 || id == 4);
      EXPECT_EQ(loads.size(), 1);
      // v2
      EXPECT_EQ(loads.begin()->first, 2);
    }
    // Load of v2 above should be counted as an extra load for case1 and
    // case_default, and both the const-class and move result should be able to
    // be copied to leafs.
    auto instructions_copied =
        SwitchEquivEditor::copy_extra_loads_to_leaf_blocks(finder, &cfg);
    EXPECT_EQ(instructions_copied, 4);
    auto* case1 = finder.key_to_case().at(baz_type);
    auto it = case1->get_first_insn();
    EXPECT_EQ(it->insn->opcode(), OPCODE_CONST_CLASS);
    EXPECT_EQ((++it)->insn->opcode(), IOPCODE_MOVE_RESULT_PSEUDO_OBJECT);
    auto* default_case = *finder.default_case();
    it = default_case->get_first_insn();
    EXPECT_EQ(it->insn->opcode(), OPCODE_CONST_CLASS);
    EXPECT_EQ((++it)->insn->opcode(), IOPCODE_MOVE_RESULT_PSEUDO_OBJECT);
  }
}

TEST_F(SwitchEquivFinderTest, test_unsupported_insn) {
  setup();

  auto code = assembler::ircode_from_string(R"(
    (
      (load-param-object v1)

      (const-class "LBar;")
      (move-result-pseudo-object v0)
      (if-eq v1 v0 :case0)

      (const-class "LBaz;")
      (move-result-pseudo-object v0)
      : the following instruction will now make this block a leaf and end the
      : representation of cases
      (invoke-virtual (v0) "Ljava/lang/Object;.notifyAll:()V")
      (if-eq v1 v0 :case1)

      (:case_default)
      (const v0 -1)
      (goto :out)

      (:case0)
      (const v0 100)
      (goto :out)

      (:case1)
      (const v0 101)

      (:out)
      (return v0)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();
  SwitchEquivFinder finder(&cfg, get_first_branch(cfg), 1);
  EXPECT_TRUE(finder.success());
  // conspicuous invoke-virtual won't be considered valid in the middle of a if
  // else series.
  const auto& key_to_case = finder.key_to_case();
  EXPECT_EQ(key_to_case.size(), 2);

  auto default_case = finder.default_case();
  EXPECT_NE(default_case, std::nullopt);
  EXPECT_EQ((*default_case)->get_first_insn()->insn->opcode(),
            OPCODE_CONST_CLASS);

  auto* bar_type = DexType::get_type("LBar;");
  auto* bar_block = key_to_case.at(bar_type);
  EXPECT_EQ(get_first_instruction_literal(bar_block), 100);
}

TEST_F(SwitchEquivFinderTest, test_class_switch_different_regs) {
  setup();

  auto code = assembler::ircode_from_string(R"(
    (
      (load-param-object v1)
      (load-param-object v2)

      (const-class "LBar;")
      (move-result-pseudo-object v0)
      (if-eq v1 v0 :case0)

      : this is a leaf since it branches on a different reg const is here just
      : for ease of asserts
      (const v3 999)
      (const-class "LBaz;")
      (move-result-pseudo-object v0)
      (if-eq v2 v0 :case1)

      (const-class "LMoo;")
      (move-result-pseudo-object v0)
      (if-eq v1 v0 :case1)

      (:case_default)
      (const v0 -1)
      (goto :out)

      (:case0)
      (const v0 100)
      (goto :out)

      (:case1)
      (const v0 101)
      (goto :out)

      (:case2)
      (const v0 102)

      (:out)
      (return v0)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();
  std::cerr << SHOW(cfg) << "\n";
  SwitchEquivFinder finder(&cfg, get_first_branch(cfg), 1);
  EXPECT_TRUE(finder.success());
  EXPECT_TRUE(finder.are_keys_uniform(SwitchEquivFinder::KeyKind::CLASS));
  const auto& key_to_case = finder.key_to_case();
  EXPECT_EQ(key_to_case.size(), 2);

  auto default_case = finder.default_case();
  EXPECT_NE(default_case, std::nullopt);
  EXPECT_EQ(get_first_instruction_literal(*default_case), 999);

  auto* bar_type = DexType::get_type("LBar;");
  auto* bar_block = key_to_case.at(bar_type);
  EXPECT_EQ(get_first_instruction_literal(bar_block), 100);
}

TEST_F(SwitchEquivFinderTest, test_class_switch_with_duplicate_keys) {
  setup();

  auto code_with_dup = assembler::ircode_from_string(R"(
    (
      (load-param-object v1)

      (const-class "LBar;")
      (move-result-pseudo-object v0)
      (if-eq v1 v0 :case0)

      (const-class "LBaz;")
      (move-result-pseudo-object v0)
      (if-eq v1 v0 :case1)

      (const-class "LBoo;")
      (move-result-pseudo-object v0)
      (if-eq v1 v0 :case2)

      (const-class "LBar;")
      (move-result-pseudo-object v0)
      (if-eq v1 v0 :case_decoy)

      (const-class "LFoo;")
      (move-result-pseudo-object v0)
      (if-eq v1 v0 :case3)

      (:case_default)
      (const v0 -1)
      (goto :out)

      (:case0)
      (const v0 100)
      (goto :out)

      (:case1)
      (const v0 101)
      (goto :out)

      (:case2)
      (const v0 102)
      (goto :out)

      (:case_decoy)
      (const v0 9999)
      (goto :out)

      (:case3)
      (const v0 103)

      (:out)
      (return v0)
    )
)");
  // Same as above, but the branch statements are negated so that the tracking
  // of cases encountered is clearly not dependent on the ordering of which
  // successor block gets processed first.
  auto code_inverse = assembler::ircode_from_string(R"(
    (
      (load-param-object v1)

      (const-class "LBar;")
      (move-result-pseudo-object v0)
      (if-ne v1 v0 :not_bar)
      (const v0 100)
      (goto :out)

      (:not_bar)
      (const-class "LBaz;")
      (move-result-pseudo-object v0)
      (if-ne v1 v0 :not_baz)
      (const v0 101)
      (goto :out)

      (:not_baz)
      (const-class "LBoo;")
      (move-result-pseudo-object v0)
      (if-ne v1 v0 :not_boo)
      (const v0 102)
      (goto :out)

      (:not_boo)
      (const-class "LBar;")
      (move-result-pseudo-object v0)
      (if-ne v1 v0 :definitely_not_bar)
      (const v0 9999)
      (goto :out)

      (:definitely_not_bar)
      (const-class "LFoo;")
      (move-result-pseudo-object v0)
      (if-ne v1 v0 :case_default)
      (const v0 103)
      (goto :out)

      (:case_default)
      (const v0 -1)

      (:out)
      (return v0)
    )
)");

  std::vector<std::unique_ptr<IRCode>> vec;
  vec.push_back(std::move(code_with_dup));
  vec.push_back(std::move(code_inverse));
  for (auto& code : vec) {
    code->build_cfg();
    auto& cfg = code->cfg();
    // By default, duplicated cases like this will not return success. Run this
    // variant and make sure it behaves reasonably.
    {
      SwitchEquivFinder finder(&cfg, get_first_branch(cfg), 1);
      EXPECT_FALSE(finder.success());
    }
    // Turn on option to support dup
    SwitchEquivFinder finder(&cfg,
                             get_first_branch(cfg),
                             1,
                             SwitchEquivFinder::NO_LEAF_DUPLICATION,
                             {},
                             SwitchEquivFinder::EXECUTION_ORDER);
    EXPECT_TRUE(finder.success());
    EXPECT_TRUE(finder.are_keys_uniform(SwitchEquivFinder::KeyKind::CLASS));
    const auto& key_to_case = finder.key_to_case();
    EXPECT_EQ(key_to_case.size(), 5);

    auto default_case = finder.default_case();
    EXPECT_NE(default_case, std::nullopt);
    EXPECT_EQ(get_first_instruction_literal(*default_case), -1);

    auto* bar_type = DexType::get_type("LBar;");
    auto* bar_block = key_to_case.at(bar_type);
    // The finder should not get confused, the case_decoy block should NOT be
    // chosen here!
    EXPECT_EQ(get_first_instruction_literal(bar_block), 100);

    auto* baz_type = DexType::get_type("LBaz;");
    auto* baz_block = key_to_case.at(baz_type);
    EXPECT_EQ(get_first_instruction_literal(baz_block), 101);

    auto* boo_type = DexType::get_type("LBoo;");
    auto* boo_block = key_to_case.at(boo_type);
    EXPECT_EQ(get_first_instruction_literal(boo_block), 102);

    auto* foo_type = DexType::get_type("LFoo;");
    auto* foo_block = key_to_case.at(foo_type);
    EXPECT_EQ(get_first_instruction_literal(foo_block), 103);
  }
}

TEST_F(SwitchEquivFinderTest, test_class_switch_with_dup_keys_extra_load) {
  setup();

  auto code = assembler::ircode_from_string(R"(
    (
      (load-param-object v1)

      (const-class "LBar;")
      (move-result-pseudo-object v0)
      (if-eq v1 v0 :case0)

      (const-class "LBaz;")
      (move-result-pseudo-object v0)
      (if-eq v1 v0 :case1)

      (const-class "LBoo;")
      (move-result-pseudo-object v0)
      (if-eq v1 v0 :case2)

      (const-class "LBar;")
      (move-result-pseudo-object v0)
      (const-class "LMoo;")
      (move-result-pseudo-object v2)
      (if-eq v1 v0 :case_decoy)

      (const-class "LFoo;")
      (move-result-pseudo-object v0)
      (if-eq v1 v0 :case3)

      (:case_default)
      (const v0 -1)
      (invoke-static (v2) "Ljava/lang/String;.valueOf:(Ljava/lang/Object;)Ljava/lang/String;")
      (move-result-object v3)
      (goto :out)

      (:case0)
      (const v0 100)
      (goto :out)

      (:case1)
      (const v0 101)
      (goto :out)

      (:case2)
      (const v0 102)
      (goto :out)

      (:case_decoy)
      (const v0 9999)
      (goto :out)

      (:case3)
      (const v0 103)

      (:out)
      (return v0)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();
  std::cerr << SHOW(cfg) << "\n";
  SwitchEquivFinder finder(&cfg,
                           get_first_branch(cfg),
                           1,
                           SwitchEquivFinder::NO_LEAF_DUPLICATION,
                           {},
                           SwitchEquivFinder::EXECUTION_ORDER);
  // The block that checks the duplicated case key has some extra instructions
  // that survive to leafs; this will not successfully represent out of caution.
  EXPECT_FALSE(finder.success());
}

TEST_F(SwitchEquivFinderTest, test_class_switch_with_move_duplicate) {
  setup();

  // A form where the result of a const-class gets moved into a higher register
  // for use again later in a check. Derived from a real world example.
  auto code_with_move_dup = assembler::ircode_from_string(R"(
    (
      (load-param-object v1)

      (const-class "LBaz;")
      (move-result-pseudo-object v0)
      (if-ne v1 v0 :not_baz)
      (const v0 101)
      (goto :out)

      (:not_baz)
      (const-class "LBar;")
      (move-result-pseudo-object v0)
      (move-object v2 v0)
      (if-ne v1 v0 :not_bar)
      (const v0 100)
      (invoke-virtual (v2) "Ljava/lang/Object;.hashCode:()I")
      (goto :out)

      (:not_bar)
      (const-class "LBoo;")
      (move-result-pseudo-object v0)
      (if-ne v1 v0 :not_boo)
      (const v0 102)
      (invoke-virtual (v2) "Ljava/lang/Object;.hashCode:()I")
      (goto :out)

      (:not_boo)
      (if-ne v1 v2 :definitely_not_bar)
      (const v0 9999)
      (goto :out)

      (:definitely_not_bar)
      (const-class "LFoo;")
      (move-result-pseudo-object v0)
      (if-ne v1 v0 :case_default)
      (const v0 103)
      (goto :out)

      (:case_default)
      (const v0 -1)

      (:out)
      (return v0)
    )
)");

  // Make this code conform to SwitchEquivFinder expectations so that
  // move-object does not appear in non-leaf block.
  SwitchEquivEditor::simplify_moves(code_with_move_dup.get());

  code_with_move_dup->build_cfg();
  auto& cfg = code_with_move_dup->cfg();
  // By default, duplicated cases like this will not return success. Run this
  // variant and make sure it behaves reasonably.
  {
    SwitchEquivFinder finder(&cfg, get_first_branch(cfg), 1);
    EXPECT_FALSE(finder.success());
  }
  // Turn on option to support dup
  SwitchEquivFinder finder(&cfg,
                           get_first_branch(cfg),
                           1,
                           SwitchEquivFinder::NO_LEAF_DUPLICATION,
                           {},
                           SwitchEquivFinder::EXECUTION_ORDER);
  EXPECT_TRUE(finder.success());
  EXPECT_TRUE(finder.are_keys_uniform(SwitchEquivFinder::KeyKind::CLASS));
  const auto& key_to_case = finder.key_to_case();
  EXPECT_EQ(key_to_case.size(), 5);

  auto default_case = finder.default_case();
  EXPECT_NE(default_case, std::nullopt);
  EXPECT_EQ(get_first_instruction_literal(*default_case), -1);

  auto* bar_type = DexType::get_type("LBar;");
  auto* bar_block = key_to_case.at(bar_type);
  // The finder should not get confused, the case_decoy block should NOT be
  // chosen here!
  EXPECT_EQ(get_first_instruction_literal(bar_block), 100);

  auto* baz_type = DexType::get_type("LBaz;");
  auto* baz_block = key_to_case.at(baz_type);
  EXPECT_EQ(get_first_instruction_literal(baz_block), 101);

  auto* boo_type = DexType::get_type("LBoo;");
  auto* boo_block = key_to_case.at(boo_type);
  EXPECT_EQ(get_first_instruction_literal(boo_block), 102);

  auto* foo_type = DexType::get_type("LFoo;");
  auto* foo_block = key_to_case.at(foo_type);
  EXPECT_EQ(get_first_instruction_literal(foo_block), 103);

  // Make sure that the use of v2 from leaf blocks is handled properly.
  auto instructions_copied =
      SwitchEquivEditor::copy_extra_loads_to_leaf_blocks(finder, &cfg);
  std::cerr << "Post edit " << SHOW(cfg) << "\n";
  EXPECT_GT(instructions_copied, 0);
  // Ensure the blocks that use v2 get a new def that makes sense. More than
  // these two blocks will get the new instructions (as it is overly broad) but
  // these are the only two that actually matter to check for correctness
  // purposes.
  EXPECT_EQ(bar_block->begin()->insn->opcode(), OPCODE_CONST_CLASS);
  EXPECT_EQ(bar_block->begin()->insn->get_type(), bar_type);
  EXPECT_EQ(boo_block->begin()->insn->opcode(), OPCODE_CONST_CLASS);
  EXPECT_EQ(boo_block->begin()->insn->get_type(), bar_type);
}

TEST_F(SwitchEquivFinderTest,
       test_switch_with_extra_loads_and_multiple_leaf_preds) {
  // This is a test case in which non-leafs load surviving const values, with a
  // leaf block that jumps to another!! This needs to be carefully handled such
  // that extra loads map is not invalidated. Goal is to make sure a simple case
  // of an empty leaf block could be supported.
  setup();

  constexpr uint32_t DEFAULT_LEAF_DUP_THRESHOLD = 50;
  const auto* const method_name = "LTesting;.with_source_blocks:(I)I";
  auto* method = DexMethod::make_method(method_name)
                     ->make_concrete(ACC_PUBLIC, /* is_virtual */ false);
  method->set_deobfuscated_name(method_name);
  {
    auto code = assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (const v1 0)
      (if-eq v1 v0 :case0)

      (const v1 1)
      (if-eq v1 v0 :case1)

      (const v1 2)
      (if-eq v1 v0 :case2)

      (const v1 3)
      (if-eq v1 v0 :case3)

      (const v3 99)
      (return v3)

      (:case0)
      (const v3 100)
      (return v3)

      (:case1)
      (invoke-static (v1) "LFoo;.useReg:(I)V")
      (const v3 101)
      (return v3)

      (:case2)
      ; NOTE: this next instruction will get forcibly removed so that we can
      ; create the appropriate CFG structure under test. I am not sure how to
      ; force an unsimplified empty block.
      (const-class "LBar;")
      ;
      (goto :case3)

      (:case3)
      (invoke-static (v1) "LFoo;.useReg:(I)V")
      (const v3 103)
      (return v3)
    )
)");
    method->set_code(std::move(code));
  }

  method->get_code()->build_cfg();
  auto& cfg = method->get_code()->cfg();

  source_blocks::insert_source_blocks(method, &cfg);

  // Further manipulation to make it the right form like we saw in the wild. All
  // this is doing is making sure we have a block with a source block but actual
  // instructions and only 1 successor. Do this by just removing a silly
  // instruction we put in the s-expr.
  for (auto it = cfg::InstructionIterator(cfg, true); !it.is_end(); ++it) {
    if (opcode::is_const_class(it->insn->opcode())) {
      cfg.remove_insn(it);
      break;
    }
  }

  // This munges the cfg into a supported form; finder would fail otherwise.
  SwitchEquivEditor::normalize_sled_blocks(&cfg, DEFAULT_LEAF_DUP_THRESHOLD);

  SwitchEquivFinder finder(&cfg, get_first_branch(cfg), 0,
                           DEFAULT_LEAF_DUP_THRESHOLD);
  EXPECT_TRUE(finder.success());
  ASSERT_TRUE(finder.are_keys_uniform(SwitchEquivFinder::KeyKind::INT));
  const auto& key_to_case = finder.key_to_case();
  EXPECT_EQ(key_to_case.size(), 5);

  const auto& extra_loads = finder.extra_loads();
  EXPECT_NE(extra_loads.size(), 0);
  print_extra_loads(extra_loads);

  auto verify_const_at_block = [&](uint32_t key, int64_t v1_expected_literal) {
    EXPECT_EQ(key_to_case.count(key), 1)
        << "Should have a case block for " << key;
    auto* case_block = key_to_case.at(key);
    EXPECT_EQ(extra_loads.count(case_block), 1)
        << "Should have an extra load at B" << case_block->id();
    auto* insn = extra_loads.at(case_block).begin()->second;
    EXPECT_TRUE(insn->has_literal());
    EXPECT_EQ(insn->get_literal(), v1_expected_literal)
        << "Wrong const value flowing into B" << case_block->id();
  };

  verify_const_at_block(1, 1);
  verify_const_at_block(2, 2);
  verify_const_at_block(3, 3);
}

TEST_F(SwitchEquivFinderTest, test_with_eq_not_constant) {
  setup();

  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)

      (const-class "LBar;")
      (move-result-pseudo-object v4)
      (invoke-virtual (v4) "Ljava/lang/Object;.hashCode:()I")
      (move-result v2)

      (const v1 1)
      (if-eq v0 v1 :one)

      (if-eq v0 v2 :two)

      (if-eqz v0 :zero)

      (const v3 999)
      (return v3)

      (:two)
      (const v3 200)
      (return v3)

      (:one)
      (const v3 100)
      (return v3)

      (:zero)
      (const v3 0)
      (return v3)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();

  SwitchEquivFinder finder(&cfg, get_first_branch(cfg), 0,
                           SwitchEquivFinder::NO_LEAF_DUPLICATION, {},
                           SwitchEquivFinder::EXECUTION_ORDER);
  EXPECT_FALSE(finder.success());

  code->clear_cfg();
}

TEST_F(SwitchEquivFinderTest, ends_with_less_than) {
  setup();

  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (const v1 1)
      (if-eq v0 v1 :one)
      (const v2 2)
      (if-eq v0 v2 :two)
      (if-lez v0 :maybe_zero)

      (const v3 999)
      (return v3)

      (:two)
      (const v3 200)
      (return v3)

      (:one)
      (const v3 100)
      (return v3)

      (:maybe_zero)
      (const v3 0)
      (return v3)
    )
)");

  code->build_cfg();
  auto& cfg = code->cfg();

  SwitchEquivFinder finder(&cfg, get_first_branch(cfg), 0,
                           SwitchEquivFinder::NO_LEAF_DUPLICATION, {},
                           SwitchEquivFinder::EXECUTION_ORDER);
  EXPECT_FALSE(finder.success());

  code->clear_cfg();
}

namespace {
// Count source blocks in a block.
size_t count_source_blocks(cfg::Block* b) {
  size_t count = 0;
  for (const auto& mie : *b) {
    if (mie.type == MFLOW_SOURCE_BLOCK) {
      count++;
    }
  }
  return count;
}

// Helper to test source block duplication behavior based on instrument_mode.
// Creates an if-else chain, inserts source blocks, runs SwitchEquivFinder,
// and returns the number of source blocks in the default case block.
size_t get_default_case_source_block_count(const char* method_name,
                                           bool instrument_mode) {
  constexpr uint32_t DEFAULT_LEAF_DUP_THRESHOLD = 50;
  auto* method = DexMethod::make_method(method_name)
                     ->make_concrete(ACC_PUBLIC, /* is_virtual */ false);
  method->set_deobfuscated_name(method_name);

  // Create an if-else chain that will be transformed into a switch.
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (const v1 0)
      (if-eq v1 v0 :case0)

      (const v1 1)
      (if-eq v1 v0 :case1)

      (const v1 2)
      (if-eq v1 v0 :case2)

      (const v3 99)
      (return v3)

      (:case0)
      (const v3 100)
      (return v3)

      (:case1)
      (const v3 101)
      (return v3)

      (:case2)
      (const v3 102)
      (return v3)
    )
)");
  method->set_code(std::move(code));

  method->get_code()->build_cfg();
  auto& cfg = method->get_code()->cfg();

  // Insert source blocks - each block gets a source block.
  source_blocks::insert_source_blocks(method, &cfg);

  // Set instrument mode for this test.
  g_redex->instrument_mode = instrument_mode;

  SwitchEquivFinder finder(&cfg, get_first_branch(cfg), 0,
                           DEFAULT_LEAF_DUP_THRESHOLD);
  always_assert(finder.success());

  // Find the default case block.
  cfg::Block* default_case = nullptr;
  for (const auto& [key, block] : finder.key_to_case()) {
    if (SwitchEquivFinder::is_default_case(key)) {
      default_case = block;
      break;
    }
  }
  always_assert(default_case != nullptr);

  return count_source_blocks(default_case);
}
} // namespace

// Test that source blocks are duplicated to leaf blocks when instrument_mode is
// enabled. This ensures that instrumented builds correctly log hits in a way
// that is faithful to the original if-else chain structure.
TEST_F(SwitchEquivFinderTest, source_blocks_duplicated_in_instrument_mode) {
  setup();

  size_t source_block_count = get_default_case_source_block_count(
      "LTesting;.source_blocks_instrument_mode:(I)I",
      /* instrument_mode */ true);

  // In instrument mode, the default case should have source blocks duplicated
  // from the non-leaf blocks it passes through. It should have more than 1
  // source block (its own plus duplicates from the if-else chain).
  EXPECT_GT(source_block_count, 1)
      << "In instrument mode, source blocks should be duplicated to leaf "
         "blocks";
}

// Test that source blocks are NOT duplicated to leaf blocks when
// instrument_mode is disabled. In production builds, duplicating source blocks
// would create nonsensical data where a hot block appears to flow directly to a
// cold block.
TEST_F(SwitchEquivFinderTest,
       source_blocks_not_duplicated_in_non_instrument_mode) {
  setup();

  size_t source_block_count = get_default_case_source_block_count(
      "LTesting;.source_blocks_non_instrument_mode:(I)I",
      /* instrument_mode */ false);

  // In non-instrument mode, the default case should only have its original
  // source block (1), not duplicates from the non-leaf blocks.
  EXPECT_EQ(source_block_count, 1)
      << "In non-instrument mode, source blocks should NOT be duplicated to "
         "leaf blocks";
}
