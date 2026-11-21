/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

// Tests of cold regions that return no value.

#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "Creators.h"
#include "DexClass.h"
#include "IRAssembler.h"
#include "MethodClosures.h"
#include "MethodSplitterTestFixture.h"
#include "MethodSplittingStats.h"
#include "RedexTest.h"

namespace mt = method_splitting_test;
namespace msi = method_splitting_impl;

class MethodSplitterRegionNoLiveOutTest : public RedexTest {};

namespace {

// Region discovery alone, on the CFG the splitter hands it: normalized, then
// reduced. `stats` receives the outcome recorded for each candidate head.
std::vector<msi::Closure> discoverRegions(std::string_view sig,
                                          const std::string& code,
                                          msi::Stats& stats) {
  static size_t methods = 0;
  auto* method =
      DexMethod::make_method("LDiscover" + std::to_string(methods++) +
                             ";.bar:" + std::string(sig))
          ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                          assembler::ircode_from_string(code),
                          /* is_virtual */ false);
  method->get_code()->build_cfg();
  msi::normalize_cfg_for_splitting(method);
  auto rcfg = msi::reduce_cfg(method);
  return msi::RegionStrategy(stats).discover(method, *rcfg);
}

size_t fateCount(const msi::Stats& stats, msi::CandidateFate fate) {
  return stats.region_fates.snapshot()[fate];
}

} // namespace

TEST_F(MethodSplitterRegionNoLiveOutTest,
       NoLiveOut_DiscoveryAdmitsSingleColdBlock) {
  msi::Stats stats;
  auto closures =
      discoverRegions("(I)V", mt::hotColdHotCfg(mt::sputChain(20, "")), stats);
  ASSERT_EQ(closures.size(), 1u);
  const auto& region = closures.front().region;
  ASSERT_TRUE(region.has_value());
  ASSERT_EQ(region->members.blocks().size(), 1u);
  EXPECT_EQ(region->members.blocks().front(), closures.front().target);
  // A head that discovery admits is counted as a candidate with no refusal
  // reason.
  EXPECT_EQ(stats.region_fates.candidates.load(), 1u);
  EXPECT_EQ(stats.region_fates.snapshot().recorded(), 0u);
}

TEST_F(MethodSplitterRegionNoLiveOutTest,
       NoLiveOut_DiscoveryRejectsTrivialRejoin) {
  // The continuation (`:rejoin`) holds only a return, so
  // normalize_cfg_for_splitting merges it into the cold predecessor, which then
  // ends in a return and is refused.
  const char* code = R"(
    (
      (load-param v0)
      (.src_block "LFoo;.bar:(I)V" 0 (1.0 1.0))
      (if-eqz v0 :rejoin)
      (.src_block "LFoo;.bar:(I)V" 1 (0.0 0.0))
      (sput v0 "LFoo;.a:I")
      (:rejoin)
      (.src_block "LFoo;.bar:(I)V" 2 (1.0 1.0))
      (return-void)
    ))";
  msi::Stats stats;
  EXPECT_TRUE(discoverRegions("(I)V", code, stats).empty());
  EXPECT_EQ(fateCount(stats, msi::CandidateFate::Discovery_Return), 1u);
}

TEST_F(MethodSplitterRegionNoLiveOutTest,
       NoLiveOut_DiscoveryRejectsABlockWithALiveOut) {
  // Cold body defines v0 via add-int; v0 is live at the continuation
  // (`:rejoin`). Only regions with no result the host reads afterwards are
  // admitted, so this is rejected.
  const char* code = R"(
    (
      (load-param v0)
      (.src_block "LFoo;.bar:(I)V" 0 (1.0 1.0))
      (if-eqz v0 :rejoin)
      (.src_block "LFoo;.bar:(I)V" 1 (0.0 0.0))
      (add-int v0 v0 v0)
      (:rejoin)
      (.src_block "LFoo;.bar:(I)V" 2 (1.0 1.0))
      (add-int v0 v0 v0)
      (return-void)
    ))";
  msi::Stats stats;
  EXPECT_TRUE(discoverRegions("(I)V", code, stats).empty());
  EXPECT_EQ(fateCount(stats, msi::CandidateFate::Discovery_TooManyLiveOuts),
            1u);
}

// When constructor inlining inlines a `T.<init>` that only calls `super()`, it
// leaves `new-instance T; invoke-direct Super.<init>` in the caller. From API
// 21 on, ART accepts that pair in any method, so a split may hold it as the
// host does. Discovery takes a block that constructs an object like any other.
TEST_F(MethodSplitterRegionNoLiveOutTest,
       NoLiveOut_DiscoveryAdmitsObjectConstruction) {
  const std::string cold_body = mt::sputChain(20, "") + R"(
    (new-instance "LFoo$Listener;")
    (move-result-pseudo-object v1)
    (invoke-direct (v1) "LBaseListener;.<init>:()V")
    (sput-object v1 "LFoo;.listener:LBaseListener;")
  )";
  msi::Stats stats;
  EXPECT_EQ(discoverRegions("(I)V", mt::hotColdHotCfg(cold_body), stats).size(),
            1u);
}

namespace {
// Hot-cold-hot fixture whose cold body is `cold_body` (S-expression of
// instructions). Params: v0 = object (lock candidate), v1 = int control. The
// cold body is padded with sputs of v1 so it clears the size floors.
std::string monitorFixture(std::string_view cold_body) {
  std::string s = "(\n  (load-param-object v0)\n  (load-param v1)\n";
  s += "  (.src_block \"LFoo;.bar:(Ljava/lang/Object;I)V\" 0 (1.0 1.0))\n";
  s += "  (if-eqz v1 :rejoin)\n";
  s += "  (.src_block \"LFoo;.bar:(Ljava/lang/Object;I)V\" 1 (0.0 0.0))\n";
  for (int i = 0; i < 20; i++) {
    s += "  (sput v1 \"LFoo;.f" + std::to_string(i) + ":I\")\n";
  }
  s += "  ";
  s += cold_body;
  s += "\n  (:rejoin)\n";
  s += "  (.src_block \"LFoo;.bar:(Ljava/lang/Object;I)V\" 2 (1.0 1.0))\n";
  s += "  (add-int v1 v1 v1)\n"; // non-return: keep reduce_cfg from merging
  s += "  (return-void)\n)";
  return s;
}
} // namespace

TEST_F(MethodSplitterRegionNoLiveOutTest,
       NoLiveOut_RejectsRegionEnteredWithAMonitorHeld) {
  // The cold block holds no monitor op, but the method enters it holding the
  // lock that `monitor-enter v0` took. Discovery conservatively keeps every
  // block entered with a monitor held in the host.
  std::string code = "(\n  (load-param-object v0)\n  (load-param v1)\n";
  code += "  (.src_block \"LFoo;.bar:(Ljava/lang/Object;I)V\" 0 (1.0 1.0))\n";
  code += "  (monitor-enter v0)\n  (if-eqz v1 :rejoin)\n";
  code += "  (.src_block \"LFoo;.bar:(Ljava/lang/Object;I)V\" 1 (0.0 0.0))\n";
  for (int i = 0; i < 20; i++) {
    code += "  (sput v1 \"LFoo;.f" + std::to_string(i) + ":I\")\n";
  }
  code += "  (:rejoin)\n";
  code += "  (.src_block \"LFoo;.bar:(Ljava/lang/Object;I)V\" 2 (1.0 1.0))\n";
  code += "  (monitor-exit v0)\n  (add-int v1 v1 v1)\n  (return-void)\n)";
  msi::Stats stats;
  EXPECT_TRUE(discoverRegions("(Ljava/lang/Object;I)V", code, stats).empty());
  EXPECT_EQ(fateCount(stats, msi::CandidateFate::Discovery_Monitor), 1u);
}

TEST_F(MethodSplitterRegionNoLiveOutTest,
       NoLiveOut_RejectsMonitorBearingRegion) {
  // A cold region block holding a monitor op must NOT be extracted. If the
  // matching op of a monitor-enter or monitor-exit lives outside the region,
  // the split has an unbalanced monitor stack, which the verifier rejects
  // (monitor-stack mismatch). Discovery conservatively excludes any block
  // holding a monitor op. The control case, without a monitor op, is admitted,
  // which shows the fixture is otherwise a region.
  msi::Stats control_stats;
  EXPECT_EQ(discoverRegions("(Ljava/lang/Object;I)V",
                            monitorFixture("(const v2 0)"), control_stats)
                .size(),
            1u);

  msi::Stats stats;
  EXPECT_TRUE(discoverRegions("(Ljava/lang/Object;I)V",
                              monitorFixture("(monitor-enter v0)\n"
                                             "  (monitor-exit v0)"),
                              stats)
                  .empty());
  EXPECT_EQ(fateCount(stats, msi::CandidateFate::Discovery_Monitor), 1u);
}

TEST_F(MethodSplitterRegionNoLiveOutTest,
       NoLiveOut_DiscoveryRejectsMoveExceptionStart) {
  // A cold catch-handler block starts with `move-exception`, which the region
  // eligibility check (`starts_with_move_exception`) rejects -- preds cannot be
  // redirected through the catch boundary. The handler goes back to the normal
  // path at a block that is not return-only, so it is not refused as a return
  // block first.
  const char* code = R"(
    (
      (load-param-object v0)
      (.src_block "LFoo;.bar:(Ljava/lang/Object;)V" 0 (1.0 1.0))
      (.try_start handler)
      (.src_block "LFoo;.bar:(Ljava/lang/Object;)V" 3 (1.0 1.0))
      (invoke-virtual (v0) "Ljava/lang/Object;.hashCode:()I")
      (.try_end handler)
      (:rejoin)
      (.src_block "LFoo;.bar:(Ljava/lang/Object;)V" 1 (1.0 1.0))
      (const v1 0)
      (return-void)
      (.catch (handler))
      (.src_block "LFoo;.bar:(Ljava/lang/Object;)V" 2 (0.0 0.0))
      (move-exception v0)
      (goto :rejoin)
    ))";
  msi::Stats stats;
  EXPECT_TRUE(discoverRegions("(Ljava/lang/Object;)V", code, stats).empty());
  EXPECT_EQ(fateCount(stats, msi::CandidateFate::Discovery_ResultReadingHead),
            1u);
}

TEST_F(MethodSplitterRegionNoLiveOutTest, NoLiveOut_DiscoveryRejectsThrowEdge) {
  // A cold block inside a try: an exception thrown in the split would reach the
  // host's handler without the register writes the split made before it.
  const char* code = R"(
    (
      (load-param v0)
      (.src_block "LFoo;.bar:(I)V" 0 (1.0 1.0))
      (if-eqz v0 :rejoin)
      (.try_start handler)
      (.src_block "LFoo;.bar:(I)V" 1 (0.0 0.0))
      (invoke-static (v0) "LFoo;.mayThrow:(I)V")
      (.try_end handler)
      (:rejoin)
      (.src_block "LFoo;.bar:(I)V" 2 (1.0 1.0))
      (add-int v0 v0 v0)
      (return-void)
      (.catch (handler))
      (.src_block "LFoo;.bar:(I)V" 3 (0.0 0.0))
      (move-exception v1)
      (goto :rejoin)
    ))";
  msi::Stats stats;
  EXPECT_TRUE(discoverRegions("(I)V", code, stats).empty());
  EXPECT_EQ(fateCount(stats, msi::CandidateFate::Discovery_ThrowEdge), 1u);
}

TEST_F(MethodSplitterRegionNoLiveOutTest, NoLiveOut_DiscoveryRejectsNoRejoin) {
  // A cold block that ends in an uncaught `throw` has no goto to hand control
  // back by.
  const char* code = R"(
    (
      (load-param v0)
      (load-param-object v1)
      (.src_block "LFoo;.bar:(ILjava/lang/RuntimeException;)V" 0 (1.0 1.0))
      (if-eqz v0 :cold)
      (.src_block "LFoo;.bar:(ILjava/lang/RuntimeException;)V" 1 (1.0 1.0))
      (add-int v0 v0 v0)
      (return-void)
      (:cold)
      (.src_block "LFoo;.bar:(ILjava/lang/RuntimeException;)V" 2 (0.0 0.0))
      (sput v0 "LFoo;.a:I")
      (throw v1)
    ))";
  msi::Stats stats;
  EXPECT_TRUE(
      discoverRegions("(ILjava/lang/RuntimeException;)V", code, stats).empty());
  EXPECT_EQ(fateCount(stats, msi::CandidateFate::Discovery_NoRejoin), 1u);
}

TEST_F(MethodSplitterRegionNoLiveOutTest, NoLiveOut_DiscoveryRejectsCycle) {
  // Two cold blocks that loop: their node of the reduced CFG holds both.
  const char* code = R"(
    (
      (load-param v0)
      (.src_block "LFoo;.bar:(I)V" 0 (1.0 1.0))
      (if-eqz v0 :rejoin)
      (:loop)
      (.src_block "LFoo;.bar:(I)V" 1 (0.0 0.0))
      (sput v0 "LFoo;.a:I")
      (goto :next)
      (:next)
      (.src_block "LFoo;.bar:(I)V" 2 (0.0 0.0))
      (sput v0 "LFoo;.b:I")
      (if-eqz v0 :loop)
      (:rejoin)
      (.src_block "LFoo;.bar:(I)V" 3 (1.0 1.0))
      (add-int v0 v0 v0)
      (return-void)
    ))";
  msi::Stats stats;
  EXPECT_TRUE(discoverRegions("(I)V", code, stats).empty());
  EXPECT_EQ(fateCount(stats, msi::CandidateFate::Discovery_Cycle), 1u);
}

// A constructor's put to a final field of its own class must stay in the
// constructor. The control writes a field that is not final and is admitted,
// which shows the fixture is otherwise a region.
TEST_F(MethodSplitterRegionNoLiveOutTest,
       NoLiveOut_DiscoveryRejectsFinalFieldPut) {
  static size_t classes = 0;
  const auto discover_init = [](std::string_view field, msi::Stats& stats) {
    const std::string cls = "LFinalPut" + std::to_string(classes++) + ";";
    ClassCreator cc(DexType::make_type(cls));
    cc.set_super(type::java_lang_Object());
    cc.add_field(DexField::make_field(cls + ".f:I")
                     ->make_concrete(ACC_PUBLIC | ACC_FINAL));
    cc.add_field(DexField::make_field(cls + ".g:I")->make_concrete(ACC_PUBLIC));
    const std::string init = cls + ".<init>:(I)V";
    const std::string sb = "(.src_block \"" + init + "\" ";
    const std::string put =
        "(iput v0 v1 \"" + cls + "." + std::string(field) + ":I\")";
    const std::string code = "((load-param-object v1) (load-param v0) " + sb +
                             "0 (1.0 1.0)) (if-eqz v0 :rejoin) " + sb +
                             "1 (0.0 0.0)) " + put + " (:rejoin) " + sb +
                             "2 (1.0 1.0)) (add-int v0 v0 v0) (return-void))";
    auto* method = DexMethod::make_method(init)->make_concrete(
        ACC_PUBLIC | ACC_CONSTRUCTOR, assembler::ircode_from_string(code),
        /* is_virtual */ false);
    cc.add_method(method);
    cc.create();
    method->get_code()->build_cfg();
    msi::normalize_cfg_for_splitting(method);
    auto rcfg = msi::reduce_cfg(method);
    return msi::RegionStrategy(stats).discover(method, *rcfg);
  };
  msi::Stats control_stats;
  EXPECT_EQ(discover_init("g", control_stats).size(), 1u);
  msi::Stats stats;
  EXPECT_TRUE(discover_init("f", stats).empty());
  EXPECT_EQ(fateCount(stats, msi::CandidateFate::Discovery_FinalFieldPut), 1u);
}

TEST_F(MethodSplitterRegionNoLiveOutTest,
       NoLiveOut_DiscoveryRejectsSwitchEntry) {
  // A cold block that ends in a switch is refused: it leaves by more than one
  // edge, and a region here leaves by one, to its continuation (`:rejoin`).
  const char* code = R"(
    (
      (load-param v0)
      (.src_block "LFoo;.bar:(I)V" 0 (1.0 1.0))
      (sput v0 "LFoo;.h_0:I")
      (if-eqz v0 :rejoin)
      (.src_block "LFoo;.bar:(I)V" 1 (0.0 0.0))
      (sput v0 "LFoo;.s_0:I")
      (switch v0 (:case0 :case1 :case2))
      (sput v0 "LFoo;.a:I")
      (goto :rejoin)
      (:case0 0)
      (sput v0 "LFoo;.b:I")
      (goto :rejoin)
      (:case1 1)
      (sput v0 "LFoo;.c:I")
      (goto :rejoin)
      (:case2 2)
      (sput v0 "LFoo;.d:I")
      (goto :rejoin)
      (:rejoin)
      (.src_block "LFoo;.bar:(I)V" 2 (1.0 1.0))
      (add-int v0 v0 v0)
      (return-void)
    ))";
  msi::Stats stats;
  EXPECT_TRUE(discoverRegions("(I)V", code, stats).empty());
  EXPECT_EQ(fateCount(stats, msi::CandidateFate::Discovery_Branch), 1u);
}
