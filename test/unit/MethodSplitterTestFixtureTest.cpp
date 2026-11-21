/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

// Meta-tests for the splitter test fixture library.
// These tests validate the fixture builders themselves before any
// production test depends on them.

#include <gtest/gtest.h>

#include "ControlFlow.h"
#include "Creators.h"
#include "DexClass.h"
#include "IRAssembler.h"
#include "MethodSplitterTestFixture.h"
#include "RedexTest.h"
#include "SourceBlocks.h"

namespace mt = method_splitting_test;

class MethodSplitterTestFixtureTest : public RedexTest {};

TEST_F(MethodSplitterTestFixtureTest, FixtureSmoke_HotColdHotCfgParses) {
  auto code = assembler::ircode_from_string(
      mt::hotColdHotCfg(mt::sputChain(20, ""), "(I)V"));
  ASSERT_NE(code, nullptr);
  code->build_cfg();
  EXPECT_GE(code->cfg().num_blocks(), 3u);
}

TEST_F(MethodSplitterTestFixtureTest, FixtureSmoke_MultiBlockHammockCfgParses) {
  auto code = assembler::ircode_from_string(mt::multiBlockHammockCfg(
      mt::sputChain(5, ""), mt::sputChain(5, ""), mt::sputChain(5, "")));
  ASSERT_NE(code, nullptr);
  code->build_cfg();
  EXPECT_GE(code->cfg().num_blocks(), 5u);
}

TEST_F(MethodSplitterTestFixtureTest,
       FixtureSmoke_TemplatesHaveNoThrowEdgesOnColdBoundary) {
  auto code = assembler::ircode_from_string(
      mt::hotColdHotCfg(mt::sputChain(20, ""), "(I)V"));
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

TEST_F(MethodSplitterTestFixtureTest,
       FixtureSmoke_HotnessConstantsClassifyExpectedBlocks) {
  // Hot constants -> at least one block classifies as hot; cold
  // constants -> at least one block classifies as cold.
  auto code = assembler::ircode_from_string(
      mt::hotColdHotCfg(mt::sputChain(20, ""), "(I)V"));
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

// Every region test relies on `regionTestConfig()` lowering the production
// size floors, so that a fixture a few dozen code units long is split at all.
// The same small cold chain moves out under it, and stays in the host under
// the production defaults with only region splitting turned on.
TEST_F(MethodSplitterTestFixtureTest,
       FixtureSmoke_RegionTestConfigLowersProductionFloors) {
  const auto code = mt::hotColdHotCfg(mt::sputChain(20, "c"));

  auto lowered = mt::runSplitter("(I)V", code, mt::regionTestConfig());
  EXPECT_EQ(mt::countFieldRefsIn(lowered, "c", mt::Where::AllSplits), 20u)
      << mt::describeSelection(lowered);
  EXPECT_EQ(mt::countFieldRefs(lowered.main_method, "c"), 0u);

  method_splitting_impl::Config production;
  production.enable_region_splitting = true;
  auto unlowered = mt::runSplitter("(I)V", code, production);
  EXPECT_TRUE(unlowered.region_splits.empty());
  EXPECT_TRUE(unlowered.suffix_splits.empty());
  EXPECT_EQ(mt::countFieldRefs(unlowered.main_method, "c"), 20u);
}

TEST_F(MethodSplitterTestFixtureTest,
       FixtureSmoke_RunRegionSplitterEmitsOnlySuffixSplits) {
  // With region splitting on but no region discovered, every emitted split
  // must be a suffix split. The fixture is large enough
  // for the suffix splitter to extract something, so the absence of
  // SplitKind::Region is meaningful rather than vacuous.
  auto res = mt::runSplitter("(I)V",
                             mt::hotColdHotCfg(mt::sputChain(100, "")),
                             mt::regionTestConfig());
  EXPECT_EQ(res.region_splits.size(), 0u);
}

TEST_F(MethodSplitterTestFixtureTest,
       FixtureSmoke_DeterminismHarnessRunsTwiceCleanly) {
  // The harness itself should run without crashing on a fixture that
  // produces no region splits. Both runs see zero region splits, so
  // the comparison passes vacuously.
  bool ok = mt::runTwiceAndCompare([](std::string_view prefix) {
    return mt::runSplitter("(I)V", mt::hotColdHotCfg(mt::sputChain(20, "")),
                           mt::regionTestConfig(), prefix);
  });
  EXPECT_TRUE(ok);
}

TEST_F(MethodSplitterTestFixtureTest, FixtureSmoke_SputChainStoresTheGivenReg) {
  EXPECT_EQ(mt::sputChain(2, "x", "v3"),
            "(sput v3 \"LFoo;.x_0:I\")\n(sput v3 \"LFoo;.x_1:I\")\n");
}

TEST_F(MethodSplitterTestFixtureTest, FixtureSmoke_SizedChainRoundsUp) {
  EXPECT_EQ(mt::sizedChain(4, "c"), mt::sputChain(2, "c"));
  EXPECT_EQ(mt::sizedChain(5, "c"), mt::sputChain(3, "c"));
}

// The hook gets the host before the splitter does: marked `no_outlining`
// there, the host is not split, while the same code unmarked is.
TEST_F(MethodSplitterTestFixtureTest, FixtureSmoke_BeforeSplitSeesTheHost) {
  const auto code = mt::hotColdHotCfg(mt::sputChain(100, ""));
  auto unmarked = mt::runSplitter("(I)V", code);
  ASSERT_FALSE(unmarked.suffix_splits.empty());
  DexMethod* seen = nullptr;
  auto marked = mt::runSplitter("(I)V", code, mt::splitterTestConfig(), "LFoo",
                                [&seen](DexMethod* m) {
                                  seen = m;
                                  m->rstate.set_no_outlining();
                                });
  EXPECT_EQ(seen, marked.main_method);
  EXPECT_TRUE(marked.suffix_splits.empty());
}

TEST_F(MethodSplitterTestFixtureTest,
       FixtureSmoke_TypeCheckFailureNamesErrors) {
  auto make = [](const std::string& name, const std::string& code) {
    auto* m = DexMethod::make_method("LTypeCheckSmoke;." + name + ":(I)V")
                  ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                                  assembler::ircode_from_string(code),
                                  /* is_virtual */ false);
    m->get_code()->build_cfg();
    return m;
  };
  EXPECT_EQ(mt::typeCheckFailure(make("good", R"(
    (
      (load-param v0)
      (sput v0 "LFoo;.f:I")
      (return-void)
    ))")),
            "");
  EXPECT_NE(mt::typeCheckFailure(make("bad", R"(
    (
      (load-param v0)
      (sput-object v0 "LFoo;.o:Ljava/lang/Object;")
      (return-void)
    ))")),
            "");
}

// `typeCheckFailure` accepts what constructor inlining leaves when it inlines
// a `Sub.<init>` that only calls `super()`: a `new-instance` of `Sub`
// initialized by `Base.<init>`.
TEST_F(MethodSplitterTestFixtureTest,
       FixtureSmoke_TypeCheckFailureAcceptsASuperclassInit) {
  ClassCreator base(DexType::make_type("LBaseTypeCheckSmoke;"));
  base.set_super(type::java_lang_Object());
  auto* base_type = base.create()->get_type();
  ClassCreator sub(DexType::make_type("LSubTypeCheckSmoke;"));
  sub.set_super(base_type);
  sub.create();
  auto* m = assembler::method_from_string(R"(
    (method (public static) "LTypeCheckSmoke;.superInit:()V"
      (
        (new-instance "LSubTypeCheckSmoke;")
        (move-result-pseudo-object v0)
        (invoke-direct (v0) "LBaseTypeCheckSmoke;.<init>:()V")
        (return-void)
      )
    )
  )");
  m->get_code()->build_cfg();
  EXPECT_EQ(mt::typeCheckFailure(m), "");
}
