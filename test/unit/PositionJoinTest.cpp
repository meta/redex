/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "DexPosition.h"
#include "IRList.h"
#include "PositionJoin.h"
#include "RedexTest.h"

using namespace positions;

namespace {

class PositionJoinTest : public RedexTest {
 protected:
  static std::unique_ptr<DexPosition> pos(const char* file, uint32_t line) {
    return std::make_unique<DexPosition>(DexString::make_string(file), line);
  }
};

TEST_F(PositionJoinTest, defaults_make_no_claim) {
  auto p = pos("Foo.java", 12);
  EXPECT_FALSE(p->is_unreliable());
}

TEST_F(PositionJoinTest, marking_is_absorbing) {
  auto p = pos("Foo.java", 12);
  p->mark_unreliable();
  EXPECT_TRUE(p->is_unreliable());
  p->mark_unreliable();
  EXPECT_TRUE(p->is_unreliable());
}

// Line 0 is what every position Redex makes up carries, and what Java prints
// as a frame without a line. Being part of position identity, it needs no
// separate mark.
TEST_F(PositionJoinTest, a_line_zero_position_is_synthetic) {
  auto made_up = pos("UnknownSource", 0);
  EXPECT_TRUE(made_up->is_synthetic());
  EXPECT_FALSE(made_up->is_unreliable());

  auto source = pos("Foo.java", 12);
  EXPECT_FALSE(source->is_synthetic());
  EXPECT_FALSE(source->is_unreliable());
}

TEST_F(PositionJoinTest, synthetic_and_unreliable_are_independent) {
  auto p = pos("UnknownSource", 0);
  EXPECT_TRUE(p->is_synthetic());
  EXPECT_FALSE(p->is_unreliable());

  p->mark_unreliable();
  EXPECT_TRUE(p->is_synthetic());
  EXPECT_TRUE(p->is_unreliable());
}

// Copies, clones and interned copies keep the line, so a position Redex made
// up stays recognizable through every pass that duplicates positions.
TEST_F(PositionJoinTest, a_synthetic_position_stays_synthetic_when_copied) {
  auto p = pos("UnknownSource", 0);
  DexPosition copy(*p);
  EXPECT_TRUE(copy.is_synthetic());
  MethodItemEntry mie(std::move(p));
  auto clone = std::make_unique<MethodItemEntry>(mie);
  ASSERT_EQ(clone->type, MFLOW_POSITION);
  EXPECT_NE(clone->pos.get(), mie.pos.get());
  EXPECT_TRUE(clone->pos->is_synthetic());
}

TEST_F(PositionJoinTest, provenance_survives_copying) {
  auto p = pos("Foo.java", 12);
  p->mark_unreliable();
  DexPosition copy(*p);
  EXPECT_TRUE(copy.is_unreliable());
}

TEST_F(PositionJoinTest, provenance_is_not_part_of_identity) {
  auto plain = pos("Foo.java", 12);
  auto unreliable = pos("Foo.java", 12);
  unreliable->mark_unreliable();

  EXPECT_EQ(*plain, *unreliable);
  EXPECT_EQ(InternedPositionHash{}(*plain),
            InternedPositionHash{}(*unreliable));
  EXPECT_TRUE(InternedPositionEqual{}(*plain, *unreliable));
}

TEST_F(PositionJoinTest, agreeing_positions_make_the_same_claim) {
  auto survivor = pos("Foo.java", 12);
  auto victim = pos("Foo.java", 12);

  EXPECT_TRUE(same_source_claim(survivor.get(), victim.get()));
}

TEST_F(PositionJoinTest, disagreeing_positions_are_unreliable) {
  auto survivor = pos("Foo.java", 12);
  auto victim = pos("Bar.java", 99);

  EXPECT_FALSE(same_source_claim(survivor.get(), victim.get()));
  EXPECT_EQ(mark_merged(survivor.get()), FidelityChange::BecameUnreliable);
  EXPECT_TRUE(survivor->is_unreliable());
}

TEST_F(PositionJoinTest, a_victim_without_a_position_is_still_ambiguity) {
  auto survivor = pos("Foo.java", 12);
  EXPECT_FALSE(same_source_claim(survivor.get(), nullptr));
}

TEST_F(PositionJoinTest, a_null_survivor_is_a_precondition_violation) {
  EXPECT_THROW(mark_merged(nullptr), RedexException);
}

TEST_F(PositionJoinTest, unreliability_is_absorbing) {
  auto survivor = pos("Foo.java", 12);
  ASSERT_EQ(mark_merged(survivor.get()), FidelityChange::BecameUnreliable);

  EXPECT_EQ(mark_merged(survivor.get()), FidelityChange::Unchanged);
  EXPECT_TRUE(survivor->is_unreliable());
}

TEST_F(PositionJoinTest,
       an_unreliable_victim_disagrees_with_an_equal_survivor) {
  auto survivor = pos("Foo.java", 12);
  auto victim = pos("Foo.java", 12);
  victim->mark_unreliable();

  EXPECT_FALSE(same_source_claim(survivor.get(), victim.get()));
}

TEST_F(PositionJoinTest, an_unreliable_parent_taints_an_agreeing_leaf) {
  auto survivor_parent = pos("Caller.java", 1);
  auto victim_parent = pos("Caller.java", 1);
  victim_parent->mark_unreliable();
  auto survivor = pos("Foo.java", 12);
  survivor->parent = survivor_parent.get();
  auto victim = pos("Foo.java", 12);
  victim->parent = victim_parent.get();

  EXPECT_FALSE(same_source_claim(survivor.get(), victim.get()));
  EXPECT_EQ(mark_merged(survivor.get()), FidelityChange::BecameUnreliable);
  EXPECT_TRUE(survivor->is_unreliable());
  EXPECT_FALSE(survivor_parent->is_unreliable());
}

// Two copies of one inlined line under the SAME callsite object. Whatever
// the callsite lost is already on the survivor's own chain, so the leaf has
// nothing to carry over and must stay as it is.
TEST_F(PositionJoinTest, a_shared_unreliable_parent_does_not_taint_the_leaf) {
  auto caller = pos("Caller.java", 1);
  caller->mark_unreliable();
  auto survivor = pos("Foo.java", 12);
  survivor->parent = caller.get();
  auto victim = pos("Foo.java", 12);
  victim->parent = caller.get();

  EXPECT_TRUE(same_source_claim(survivor.get(), victim.get()));
  EXPECT_FALSE(survivor->is_unreliable());
}

TEST_F(PositionJoinTest, a_synthetic_parent_taints_an_agreeing_leaf) {
  auto survivor_parent = pos("Caller.java", 1);
  auto victim_parent = pos("Caller.java", 0);
  auto survivor = pos("Foo.java", 12);
  survivor->parent = survivor_parent.get();
  auto victim = pos("Foo.java", 12);
  victim->parent = victim_parent.get();

  EXPECT_FALSE(same_source_claim(survivor.get(), victim.get()));
}

TEST_F(PositionJoinTest, identical_synthetic_chains_agree) {
  auto survivor_parent = pos("Caller.java", 0);
  auto victim_parent = pos("Caller.java", 0);
  auto survivor = pos("Foo.java", 12);
  survivor->parent = survivor_parent.get();
  auto victim = pos("Foo.java", 12);
  victim->parent = victim_parent.get();

  EXPECT_TRUE(same_source_claim(survivor.get(), victim.get()));
}

TEST_F(PositionJoinTest, a_synthetic_position_agrees_with_itself) {
  auto survivor = pos("UnknownSource", 0);
  EXPECT_TRUE(same_source_claim(survivor.get(), survivor.get()));
}

TEST_F(PositionJoinTest, equal_precise_parent_chains_agree) {
  auto survivor_parent = pos("Caller.java", 1);
  auto victim_parent = pos("Caller.java", 1);
  auto survivor = pos("Foo.java", 12);
  survivor->parent = survivor_parent.get();
  auto victim = pos("Foo.java", 12);
  victim->parent = victim_parent.get();

  EXPECT_TRUE(same_source_claim(survivor.get(), victim.get()));
}

TEST_F(PositionJoinTest, differing_parents_make_positions_disagree) {
  auto caller_a = pos("Caller.java", 1);
  auto caller_b = pos("Caller.java", 2);
  auto survivor = pos("Foo.java", 12);
  survivor->parent = caller_a.get();
  auto victim = pos("Foo.java", 12);
  victim->parent = caller_b.get();

  EXPECT_FALSE(same_source_claim(survivor.get(), victim.get()));
}

TEST_F(PositionJoinTest, a_position_agrees_with_itself) {
  auto survivor = pos("Foo.java", 12);
  EXPECT_TRUE(same_source_claim(survivor.get(), survivor.get()));
}

TEST_F(PositionJoinTest, provenance_survives_cloning_a_method_item_entry) {
  auto p = pos("Foo.java", 12);
  p->mark_unreliable();
  MethodItemEntry mie(std::move(p));
  auto clone = std::make_unique<MethodItemEntry>(mie);
  clone->pos->line = 13;
  ASSERT_EQ(clone->type, MFLOW_POSITION);
  EXPECT_NE(clone->pos.get(), mie.pos.get());
  EXPECT_EQ(mie.pos->line, 12);
  EXPECT_EQ(clone->pos->line, 13);
  EXPECT_TRUE(clone->pos->is_unreliable());
}

TEST(PositionJoinStatsTest, accumulates_changes_and_unrecorded_merges) {
  JoinStats left;
  left.account(FidelityChange::Unchanged);
  left.account(FidelityChange::BecameUnreliable);
  left.count_unrecorded();

  JoinStats right;
  right.account(FidelityChange::BecameUnreliable);
  right.count_unrecorded();
  right.count_unrecorded();

  left += right;
  EXPECT_EQ(left.marked_unreliable, 2u);
  EXPECT_EQ(left.not_recorded, 3u);
}

} // namespace
