/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

// Meta-tests for the cold-region splitter test fixture library.
// These tests validate the fixture builders themselves before any
// production test depends on them.

#include <gtest/gtest.h>

#include "ControlFlow.h"
#include "DexClass.h"
#include "IRAssembler.h"
#include "MethodSplitterRegionTestFixture.h"
#include "RedexTest.h"
#include "SourceBlocks.h"

namespace mt = method_splitting_region_test;

class MethodSplitterRegionTestFixtureTest : public RedexTest {};

TEST_F(MethodSplitterRegionTestFixtureTest, FixtureSmoke_HotColdHotCfgParses) {
  auto code = assembler::ircode_from_string(
      mt::hotColdHotCfg(mt::coldBodySputs(20), "(I)V"));
  ASSERT_NE(code, nullptr);
  code->build_cfg();
  EXPECT_GE(code->cfg().num_blocks(), 3u);
}

TEST_F(MethodSplitterRegionTestFixtureTest,
       FixtureSmoke_MultiBlockHammockCfgParses) {
  auto code = assembler::ircode_from_string(mt::multiBlockHammockCfg(
      mt::coldBodySputs(5), mt::coldBodySputs(5), mt::coldBodySputs(5)));
  ASSERT_NE(code, nullptr);
  code->build_cfg();
  EXPECT_GE(code->cfg().num_blocks(), 5u);
}

TEST_F(MethodSplitterRegionTestFixtureTest,
       FixtureSmoke_TemplatesHaveNoThrowEdgesOnColdBoundary) {
  auto code = assembler::ircode_from_string(
      mt::hotColdHotCfg(mt::coldBodySputs(20), "(I)V"));
  code->build_cfg();
  for (auto* b : code->cfg().blocks()) {
    for (const auto* e : b->preds()) {
      EXPECT_NE(e->type(), cfg::EDGE_THROW);
    }
    for (const auto* e : b->succs()) {
      EXPECT_NE(e->type(), cfg::EDGE_THROW);
    }
  }
}

TEST_F(MethodSplitterRegionTestFixtureTest,
       FixtureSmoke_HotnessConstantsClassifyExpectedBlocks) {
  // Hot constants -> at least one block classifies as hot; cold
  // constants -> at least one block classifies as cold.
  auto code = assembler::ircode_from_string(
      mt::hotColdHotCfg(mt::coldBodySputs(20), "(I)V"));
  code->build_cfg();
  // Named for what it computes: `foreach_val_early` stops at the first
  // positive val, so this is ANY-val, not all-vals. The fixtures emit uniformly
  // (1.0 1.0) or (0.0 0.0) blocks, so the two agree here -- but a future
  // fixture mixing hot and cold vals in one block would be classified hot.
  auto has_any_hot_val = [](cfg::Block* b) -> bool {
    const auto* sb = source_blocks::get_first_source_block(b);
    if (sb == nullptr) {
      return false;
    }
    bool hot = false;
    sb->foreach_val_early([&hot](const auto& v) {
      hot = (v && v->val > 0.0f);
      return hot;
    });
    return hot;
  };
  bool saw_hot = false;
  bool saw_cold = false;
  for (auto* b : code->cfg().blocks()) {
    if (source_blocks::get_first_source_block(b) == nullptr) {
      continue;
    }
    if (has_any_hot_val(b)) {
      saw_hot = true;
    } else {
      saw_cold = true;
    }
  }
  EXPECT_TRUE(saw_hot);
  EXPECT_TRUE(saw_cold);
}

// `regionTestConfig()` deliberately departs from the production defaults so
// that tiny hand-written fixtures are splittable at all. Those departures are
// what every region test silently depends on, so they are pinned here: if one
// drifts back toward production, this fails in one obvious place instead of
// turning a dozen unrelated fixtures un-splittable for no visible reason.
TEST_F(MethodSplitterRegionTestFixtureTest,
       FixtureSmoke_RegionTestConfigLowersProductionFloors) {
  auto cfg = mt::regionTestConfig();
  method_splitting_impl::Config prod;

  EXPECT_TRUE(cfg.enable_region_splitting)
      << "region tests need the feature on; it is off by default";

  // Fixtures are a few dozen code units, far below the production floors.
  EXPECT_LT(cfg.min_hot_cold_split_size, prod.min_hot_cold_split_size);
  EXPECT_LT(cfg.min_hot_split_size, prod.min_hot_split_size);
  EXPECT_LE(cfg.min_hot_cold_split_size, 4u);
  EXPECT_LE(cfg.min_hot_split_size, 4u);

  // Block splitting must not fire and reshape a fixture's CFG under the test.
  EXPECT_GT(cfg.split_block_size, prod.split_block_size);
}

TEST_F(MethodSplitterRegionTestFixtureTest,
       FixtureSmoke_RunRegionSplitterEmitsOnlySuffixSplits) {
  // Region discovery is not implemented yet, so with the flag on every
  // emitted split must still be a suffix split. The fixture is large enough
  // for the suffix splitter to extract something, so the absence of
  // SplitKind::Region is meaningful rather than vacuous.
  auto res =
      mt::runRegionSplitter("(I)V", mt::hotColdHotCfg(mt::coldBodySputs(100)));
  EXPECT_EQ(res.region_splits.size(), 0u);
}

TEST_F(MethodSplitterRegionTestFixtureTest,
       FixtureSmoke_DeterminismHarnessRunsTwiceCleanly) {
  // The harness itself should run without crashing on a fixture that
  // produces no region splits. Both runs see zero region splits, so
  // the comparison passes vacuously.
  bool ok = mt::runTwiceAndCompare([](std::string_view prefix) {
    return mt::runRegionSplitter("(I)V",
                                 mt::hotColdHotCfg(mt::coldBodySputs(20)),
                                 mt::regionTestConfig(), prefix);
  });
  EXPECT_TRUE(ok);
}
