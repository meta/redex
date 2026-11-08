/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

// Tests for `suffix_net_gate`. Without the gate, a hot-cold suffix split is
// decided by the size floor (`min_hot_cold_split_size`, 100) and the overhead
// ratio alone. With it, the floor drops to `min_suffix_sub_floor_split_size`
// (80), and each hot-cold suffix split must have a positive net saving
// (`split_net_saving`). So a cold tail of 80 to 99 code units that pays is
// split, and a tail that does not pay is refused. The tests also check
// `suffix_net_gate_cold` for the cold kind, and how suffix splits are costed
// (switch-group dispatch, duplicated tails, recreated constants).

#include <gtest/gtest.h>

#include <algorithm>
#include <cmath>
#include <functional>
#include <limits>
#include <sstream>
#include <string>

#include "ControlFlow.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "JsonWrapper.h"
#include "MethodSplitterTestFixture.h"
#include "MethodSplittingPass.h"
#include "RedexTest.h"
#include "ReduceGotos.h"
#include "SplitNetSaving.h"

namespace mt = method_splitting_test;
namespace msi = method_splitting_impl;

namespace {

// The launchpad a void suffix split leaves in its host: `invoke-static;
// return-void`.
size_t suffixLaunchpadCodeUnits() {
  return msi::opcode_code_units(OPCODE_INVOKE_STATIC) +
         msi::opcode_code_units(OPCODE_RETURN_VOID);
}

// Hot entry branches to either a COLD tail that returns or a hot block that
// returns, so the cold tail is a suffix closure. `sputs` sizes the cold tail
// (2 code units each).
std::string hotColdTailCfg(size_t sputs) {
  std::ostringstream oss;
  oss << "(\n  (load-param v0)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 0 (1.0 1.0))\n"
      << "  (if-eqz v0 :hot_ret)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 1 (0.0 0.0))\n"
      << mt::sputChain(sputs, "") << "  (return-void)\n"
      << "  (:hot_ret)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 2 (1.0 1.0))\n"
      << "  (return-void)\n)\n";
  return oss.str();
}

// The gate: relaxed floor AND the net cost model deciding.
method_splitting_impl::Config gateConfig() {
  auto c = mt::splitterTestConfig();
  c.suffix_net_gate = true;
  c.min_hot_cold_split_size =
      100; // the real suffix floor (fixture lowers to 4)
  c.min_hot_split_size = 1; // don't let the remaining-size gate interfere
  // Pin the OAT:dex weight so these tests stay independent of the default.
  // They assert on which side of the net gate a specific tail falls, and that
  // boundary moves with W by construction: a larger W admits tails these tests
  // require to be rejected. 2.0 is the value their arithmetic was computed
  // against.
  c.net_oat_weight = 2.0f;
  return c;
}

// The control: the gate off, so hot-cold suffixes are admitted on the size
// floors and the overhead ratio alone.
method_splitting_impl::Config baseConfig() {
  auto c = gateConfig();
  c.suffix_net_gate = false;
  return c;
}

// The suffix floor lowered to the sub-floor by configuration, with no gate:
// sub-floor cold tails become candidates, decided by the size floors and the
// overhead ratio alone. The control for what the gate filters out.
method_splitting_impl::Config netBlindSubFloorConfig() {
  auto c = baseConfig();
  c.min_hot_cold_split_size = c.min_suffix_sub_floor_split_size;
  return c;
}

// A method that is cold throughout: a cold entry branches to a cold tail that
// returns or a cold block that returns. The tail's predecessor is cold, so it
// is a Cold suffix (`!any_src_hot`). The fixture marks the host compiled, so
// this is the case `suffix_net_gate_cold` is for.
std::string coldOnlyTailCfg(size_t sputs) {
  std::ostringstream oss;
  oss << "(\n  (load-param v0)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 0 (0.0 0.0))\n"
      // Cold filler in the ENTRY block (not a suffix candidate) so the
      // post-split remainder clears the estimated-remaining floor.
      << mt::sputChain(30, "") << "  (if-eqz v0 :ret2)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 1 (0.0 0.0))\n"
      << mt::sputChain(sputs, "") << "  (return-void)\n"
      << "  (:ret2)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 2 (0.0 0.0))\n"
      << "  (return-void)\n)\n";
  return oss.str();
}

// The gate for the cold kind.
method_splitting_impl::Config coldGateConfig() {
  auto c = mt::splitterTestConfig();
  c.suffix_net_gate_cold = true;
  c.min_cold_split_size = 100; // real legacy cold floor (fixture lowers to 4)
  c.min_hot_split_size = 1;
  return c;
}

// The control for the cold kind: the cold gate off.
method_splitting_impl::Config coldBaseConfig() {
  auto c = coldGateConfig();
  c.suffix_net_gate_cold = false;
  return c;
}

// The cold floor lowered to the sub-floor by configuration, with no gate.
method_splitting_impl::Config coldNetBlindSubFloorConfig() {
  auto c = coldBaseConfig();
  c.min_cold_split_size = c.min_suffix_sub_floor_split_size;
  return c;
}

} // namespace

class MethodSplitterSuffixNetGateTest : public RedexTest {};

// `net_oat_weight` multiplies every net saving, so an infinite, NaN, zero or
// negative weight makes them non-finite or inverts the ranking; the pass
// refuses such a configuration when it is bound.
TEST_F(MethodSplitterSuffixNetGateTest,
       BindingRefusesANonFiniteOrNonPositiveWeight) {
  for (double weight : {std::numeric_limits<double>::infinity(),
                        -std::numeric_limits<double>::infinity(),
                        std::numeric_limits<double>::quiet_NaN(), -1.0, 0.0}) {
    SCOPED_TRACE(weight);
    Json::Value json;
    json["net_oat_weight"] = weight;
    MethodSplittingPass pass;
    EXPECT_THROW(pass.parse_config(JsonWrapper(json)), RedexException);
  }
  Json::Value json;
  json["net_oat_weight"] = 5.0;
  MethodSplittingPass pass;
  EXPECT_NO_THROW(pass.parse_config(JsonWrapper(json)));
}

// A 50-code-unit cold tail sits below the 100-code-unit hot-cold floor, so with
// the gate off it is not split; with the gate on the floor drops and the
// tail's net saving on a compiled host is positive, so exactly one more suffix
// split appears.
TEST_F(MethodSplitterSuffixNetGateTest, GateAdmitsNetPositiveSubFloorTail) {
  auto off = mt::runSplitter("(I)V", hotColdTailCfg(25), baseConfig());
  auto on = mt::runSplitter("(I)V", hotColdTailCfg(25), gateConfig());
  EXPECT_EQ(on.suffix_splits.size(), off.suffix_splits.size() + 1);
}

// The gate admits a tail only when its net saving is strictly positive. The
// test evaluates the tail above once and then raises the per-split metadata
// cost by exactly that net saving. At a net saving of 0 the tail is refused; at
// 1 it is split.
TEST_F(MethodSplitterSuffixNetGateTest,
       GateRefusesATailWithANetSavingOfExactlyZero) {
  auto cfg = gateConfig();
  cfg.max_iteration = 1;
  auto evaluated = [](const mt::SplitResult& res) {
    std::vector<msi::CandidateEvaluation> out;
    for (const auto& e : mt::evaluationsOf(res, msi::SplitKind::Suffix)) {
      if (e.terms) {
        out.push_back(e);
      }
    }
    return out;
  };
  auto probe = mt::runSplitter("(I)V", hotColdTailCfg(25), cfg);
  const auto first = evaluated(probe);
  ASSERT_EQ(first.size(), 1u) << mt::describeSelection(probe);
  ASSERT_EQ(first[0].fate, msi::CandidateFate::Emitted);
  // W = 2 and every term is a whole number of code units, so the net is too.
  const double net = first[0].terms->net;
  ASSERT_GT(net, 1.0);
  ASSERT_DOUBLE_EQ(net, std::floor(net));
  const auto metadata = cfg.net_cu_method_metadata;

  cfg.net_cu_method_metadata = metadata + static_cast<size_t>(net);
  auto at_zero = mt::runSplitter("(I)V", hotColdTailCfg(25), cfg);
  const auto zero = evaluated(at_zero);
  ASSERT_EQ(zero.size(), 1u) << mt::describeSelection(at_zero);
  EXPECT_DOUBLE_EQ(zero[0].terms->net, 0.0);
  EXPECT_EQ(zero[0].fate, msi::CandidateFate::Evaluation_NetNotPositive);
  EXPECT_EQ(at_zero.suffix_splits.size() + 1, probe.suffix_splits.size());

  cfg.net_cu_method_metadata = metadata + static_cast<size_t>(net) - 1;
  auto at_one = mt::runSplitter("(I)V", hotColdTailCfg(25), cfg);
  const auto one = evaluated(at_one);
  ASSERT_EQ(one.size(), 1u) << mt::describeSelection(at_one);
  EXPECT_DOUBLE_EQ(one[0].terms->net, 1.0);
  EXPECT_EQ(one[0].fate, msi::CandidateFate::Emitted);
  EXPECT_EQ(at_one.suffix_splits.size(), probe.suffix_splits.size());
}

// A suffix split does not always take out what it copies. Emission redirects
// only the edges into the heads, and `SplitMethod::create` copies the whole
// host, so a block of the split that the host can still enter from outside
// exists in both methods: duplicated, not moved. `net_saving_input` therefore
// counts only `evicted_size` as saved and charges the duplicated code as dex
// added; crediting the whole closure, or not charging the duplicate, would
// split too much.
//
// `:tail` is still entered from `:hot_mid`, so it is duplicated: the closure
// has 60 code units, 30 taken out and 30 duplicated. Credited whole, the net
// saving would be +85 and the tail split; charged for the duplicate, it is -5
// and the tail is refused.
//
// The test checks what the split holds, not how many splits there are: another
// candidate chosen instead would satisfy a count. The control run without the
// gate shows that the tail is splittable at all, since an empty `zzA` count is
// also what "nothing split" looks like.
TEST_F(MethodSplitterSuffixNetGateTest,
       SuffixNet_DuplicatedTailNotCreditedAsEvicted) {
  auto cfg = gateConfig();
  std::ostringstream oss;
  oss << "(\n  (load-param v0)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 0 " << mt::kHotWeights << ")\n"
      << mt::sputChain(20, "") << "  (if-eqz v0 :hot_mid)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 1 " << mt::kColdWeights << ")\n"
      << mt::sputChain(15, "zzA") << "  (goto :tail)\n"
      << "  (:hot_mid)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 2 " << mt::kHotWeights << ")\n"
      << "  (sput v0 \"LFoo;.mid:I\")\n  (goto :tail)\n"
      << "  (:tail)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 3 " << mt::kColdWeights << ")\n"
      << mt::sputChain(15, "zzT") << "  (return-void)\n)\n";

  // Control: the same shape with the floor lowered but no gate. It is split
  // there, so `zzA` reaching no split below is the gate's doing and not an
  // unsplittable fixture.
  auto control = mt::runSplitter("(I)V", oss.str(), netBlindSubFloorConfig());
  const size_t control_a_refs =
      mt::countFieldRefsIn(control, "zzA", mt::Where::SuffixSplits);
  ASSERT_GT(control_a_refs, 0u)
      << "the over-credited tail is not split even with the gate off, so the "
         "assertion below would hold for the wrong reason";

  auto res = mt::runSplitter("(I)V", oss.str(), cfg);

  const size_t a_refs =
      mt::countFieldRefsIn(res, "zzA", mt::Where::SuffixSplits);
  EXPECT_EQ(a_refs, 0u)
      << "the over-credited tail was admitted: its body reached a suffix split";
}

// A 4-code-unit cold tail has a negative net saving once the 28 code units of
// per-split metadata are charged: with the gate on and the floor lowered, the
// gate still refuses it, so there are as many suffix splits as with the gate
// off.
TEST_F(MethodSplitterSuffixNetGateTest, GateRejectsNetNegativeTinyTail) {
  auto off = mt::runSplitter("(I)V", hotColdTailCfg(2), baseConfig());
  auto on = mt::runSplitter("(I)V", hotColdTailCfg(2), gateConfig());
  EXPECT_EQ(on.suffix_splits.size(), off.suffix_splits.size());
}

// On an uncompiled host no split saves compiled code, so the net decides
// nothing there: the hot-cold gate leaves such a host to the legacy floors.
TEST_F(MethodSplitterSuffixNetGateTest,
       HotColdGateLeavesAnUncompiledHostToTheLegacyFloors) {
  const auto code = hotColdTailCfg(60);
  auto off = mt::runSplitterOnUncompiledHost("(I)V", code, baseConfig());
  ASSERT_FALSE(off.suffix_splits.empty());
  auto on = mt::runSplitterOnUncompiledHost("(I)V", code, gateConfig());
  EXPECT_EQ(mt::splitSignature(on), mt::splitSignature(off))
      << "the hot-cold gate changed legacy splitting on an uncompiled host";
}

// The gate is a filter, not just a lower floor. A tiny cold tail clears the
// relaxed floor but does not pay for its own launchpad:
//
//   floor lowered, no gate  -> admitted, because nothing tests whether it pays
//   net gate                -> rejected, because the net cost model says it
//                              does not
TEST_F(MethodSplitterSuffixNetGateTest, SubFloorAdmitsWhatTheNetGateRejects) {
  auto off = mt::runSplitter("(I)V", hotColdTailCfg(2), baseConfig());
  auto floor_only =
      mt::runSplitter("(I)V", hotColdTailCfg(2), netBlindSubFloorConfig());
  auto floor_and_gate =
      mt::runSplitter("(I)V", hotColdTailCfg(2), gateConfig());

  EXPECT_EQ(floor_only.suffix_splits.size(), off.suffix_splits.size() + 1)
      << "the lowered floor alone must make the sub-floor tail a candidate and "
         "admit it net-blind";
  EXPECT_EQ(floor_and_gate.suffix_splits.size(), off.suffix_splits.size())
      << "the net gate must reject the same tail, which does not pay";
}

// Symmetric check on a tail that DOES pay: the net gate must not reject it, so
// floor-only and floor+gate agree. Together with the test above this pins both
// directions -- the gate is a filter, not a second floor.
TEST_F(MethodSplitterSuffixNetGateTest, NetGateKeepsSubFloorTailThatPays) {
  auto off = mt::runSplitter("(I)V", hotColdTailCfg(25), baseConfig());
  auto floor_only =
      mt::runSplitter("(I)V", hotColdTailCfg(25), netBlindSubFloorConfig());
  auto floor_and_gate =
      mt::runSplitter("(I)V", hotColdTailCfg(25), gateConfig());

  EXPECT_EQ(floor_only.suffix_splits.size(), off.suffix_splits.size() + 1);
  EXPECT_EQ(floor_and_gate.suffix_splits.size(),
            floor_only.suffix_splits.size())
      << "a net-positive sub-floor tail must survive the gate";
}

// A 50-code-unit cold tail below the cold floor (100) is not split with the
// cold gate off; with it on, the floor drops and the tail's positive net saving
// on a compiled host admits it.
TEST_F(MethodSplitterSuffixNetGateTest, ColdGateAdmitsNetPositiveSubFloorTail) {
  auto off = mt::runSplitter("(I)V", coldOnlyTailCfg(25), coldBaseConfig());
  auto on = mt::runSplitter("(I)V", coldOnlyTailCfg(25), coldGateConfig());
  EXPECT_EQ(on.suffix_splits.size(), off.suffix_splits.size() + 1);
  // The one split the gate adds is the one only its lowered floors admit.
  EXPECT_EQ(on.stats.suffix_sub_floor_emitted, 1u);
  EXPECT_EQ(off.stats.suffix_sub_floor_emitted, 0u);
}

// The Cold counterpart of `SubFloorAdmitsWhatTheNetGateRejects`: a
// 4-code-unit cold tail has a negative net saving, so the cold gate refuses
// what the lowered cold floor alone admits. This matters most for the cold
// kind: `min_cold_split_size` guards inlining and compilability constraints
// the net saving does not model, which is why the gate lowers it only for the
// tails it evaluates.
TEST_F(MethodSplitterSuffixNetGateTest, ColdSubFloorAdmitsWhatTheGateRejects) {
  auto off = mt::runSplitter("(I)V", coldOnlyTailCfg(2), coldBaseConfig());
  auto floor_only =
      mt::runSplitter("(I)V", coldOnlyTailCfg(2), coldNetBlindSubFloorConfig());
  auto floor_and_gate =
      mt::runSplitter("(I)V", coldOnlyTailCfg(2), coldGateConfig());

  EXPECT_EQ(floor_only.suffix_splits.size(), off.suffix_splits.size() + 1)
      << "the lowered cold floor alone must admit the sub-floor tail";
  EXPECT_EQ(floor_and_gate.suffix_splits.size(), off.suffix_splits.size())
      << "the cold net gate must reject the same tail, which does not pay";
}

// `suffix_net_gate_cold` lowers the remaining-size floor too, and evaluates
// every tail only the lowered floors admit. Here the tail is above
// `min_cold_split_size` but the remainder sits below it: the legacy floors
// refuse the tail, and the gate keeps it because it pays.
TEST_F(MethodSplitterSuffixNetGateTest,
       ColdGateEvaluatesATailOnlyItsLoweredRemainingFloorAdmits) {
  auto off = mt::runSplitter("(I)V", coldOnlyTailCfg(60), coldBaseConfig());
  ASSERT_EQ(off.suffix_splits.size(), 0u)
      << "precondition: the remainder is below `min_cold_split_size`";
  auto on = mt::runSplitter("(I)V", coldOnlyTailCfg(60), coldGateConfig());
  EXPECT_EQ(on.suffix_splits.size(), 1u);
  // The net saving decides: a prohibitive split cost turns it down.
  auto expensive = coldGateConfig();
  expensive.net_cu_method_metadata = 100000;
  auto refused = mt::runSplitter("(I)V", coldOnlyTailCfg(60), expensive);
  EXPECT_EQ(refused.suffix_splits.size(), 0u);
  EXPECT_EQ(
      refused.stats.suffix_fates[msi::CandidateFate::Evaluation_NetNotPositive],
      1u);
}

// The sibling above pins the OUTCOME for a tail that pays. This test pins the
// REASON for one that does not: the net model evaluated the sub-floor tail and
// refused it.
TEST_F(MethodSplitterSuffixNetGateTest, ColdGateRejectsATailThatDoesNotPay) {
  auto on = mt::runSplitter("(I)V", coldOnlyTailCfg(2), coldGateConfig());
  EXPECT_EQ(
      on.stats.suffix_fates[msi::CandidateFate::Evaluation_NetNotPositive], 1u)
      << "the sub-floor cold tail must reach the net model and be refused";
}

// The same for the cold gate: it neither lowers the floors nor evaluates a tail
// on an uncompiled host.
TEST_F(MethodSplitterSuffixNetGateTest,
       ColdGateLeavesAnUncompiledHostToTheLegacyFloors) {
  const auto code = coldOnlyTailCfg(25);
  auto off = mt::runSplitterOnUncompiledHost("(I)V", code, coldBaseConfig());
  auto on = mt::runSplitterOnUncompiledHost("(I)V", code, coldGateConfig());
  EXPECT_EQ(mt::splitSignature(on), mt::splitSignature(off));
  EXPECT_EQ(
      on.stats.suffix_fates[msi::CandidateFate::Evaluation_NetNotPositive], 0u);
}

namespace {

// The remaining floor's fixture: a hot entry (`kEntrySputs` writes) branches to
// a head block (`kHeadSputs` writes) or to a hot block (`kOtherSputs`), and
// both jump to a hot join (`kJoinSputs` writes, then `return-void`). The suffix
// at the head takes the head and the join, and the host keeps the join too: it
// still reaches it through the hot block. The head is cold, and with
// `cold_entry` every block is.
constexpr size_t kEntrySputs = 100;
constexpr size_t kHeadSputs = 150;
constexpr size_t kOtherSputs = 5;
constexpr size_t kJoinSputs = 5;

std::string sharedJoinCfg(bool cold_entry = false) {
  const auto entry = cold_entry ? mt::kColdWeights : mt::kHotWeights;
  const auto hot = cold_entry ? mt::kColdWeights : mt::kHotWeights;
  const auto head = mt::kColdWeights;
  std::ostringstream oss;
  oss << "(\n  (load-param v0)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 0 " << entry << ")\n"
      << mt::sputChain(kEntrySputs, "entry") << "  (if-eqz v0 :other)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 1 " << head << ")\n"
      << mt::sputChain(kHeadSputs, "head") << "  (goto :join)\n"
      << "  (:other)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 2 " << hot << ")\n"
      << mt::sputChain(kOtherSputs, "other") << "  (goto :join)\n"
      << "  (:join)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 3 " << hot << ")\n"
      << mt::sputChain(kJoinSputs, "join") << "  (return-void)\n)\n";
  return oss.str();
}

// What the host keeps of `sharedJoinCfg` once the head's suffix is split: the
// entry, the hot block, and the join it duplicates.
constexpr size_t kKeptCodeUnits =
    kEntrySputs * mt::kSputCodeUnits + 2 /* if-eqz */ +
    kOtherSputs * mt::kSputCodeUnits + kJoinSputs * mt::kSputCodeUnits +
    1 /* return-void */;

// Whether the head's suffix of `code` is split under `cfg`.
bool headSplit(const std::string& code, const msi::Config& cfg) {
  auto res = mt::runSplitter("(I)V", code, cfg);
  return mt::countFieldRefsIn(res, "head", mt::Where::SuffixSplits) > 0;
}

} // namespace

// Under the cold net gate both floors drop to
// `min_suffix_sub_floor_split_size`; the remaining one reads what the host
// keeps, the join the split copies included.
TEST_F(MethodSplitterSuffixNetGateTest, RemainingFloor_GatedColdAtItsBoundary) {
  auto cfg = mt::splitterTestConfig();
  cfg.suffix_net_gate_cold = true;
  cfg.min_cold_split_size = std::numeric_limits<size_t>::max();
  cfg.min_suffix_sub_floor_split_size = kKeptCodeUnits;
  const auto code = sharedJoinCfg(/*cold_entry=*/true);
  EXPECT_TRUE(headSplit(code, cfg));
  cfg.min_suffix_sub_floor_split_size = kKeptCodeUnits + 1;
  EXPECT_FALSE(headSplit(code, cfg));
}

// Under the hot-cold net gate the remaining floor drops to
// `min_suffix_sub_floor_split_size`, and it reads what the host keeps, the join
// the split copies included.
TEST_F(MethodSplitterSuffixNetGateTest,
       RemainingFloor_GatedHotColdAtItsBoundary) {
  auto cfg = gateConfig();
  cfg.min_hot_split_size = std::numeric_limits<size_t>::max();
  cfg.min_suffix_sub_floor_split_size = kKeptCodeUnits;
  EXPECT_TRUE(headSplit(sharedJoinCfg(), cfg));
  cfg.min_suffix_sub_floor_split_size = kKeptCodeUnits + 1;
  EXPECT_FALSE(headSplit(sharedJoinCfg(), cfg));
}

namespace {

// The hot-cold suffix splits among `splits`. The fixtures' hot blocks are
// small enough to be hot-split as well under `baseConfig`'s hot floor, which
// these tests do not ask about.
std::vector<DexMethod*> hotColdSplits(const std::vector<DexMethod*>& splits) {
  std::vector<DexMethod*> res;
  for (auto* m : splits) {
    if (m->str().find("$hot_cold") != std::string::npos) {
      res.push_back(m);
    }
  }
  return res;
}

// A hot `switch` whose default and cases 1 and 2 are cold tails that return,
// and whose case `kept_key` is hot. Every cold tail reads the selector `v0`;
// the hot case does not. With `sixteen_registers` the entry also writes `v16`,
// so ReduceGotos finds no 4-bit temp register for `const; if-eq`, a form the
// net cost model does not model.
std::string coldSwitchGroupCfg(int32_t kept_key = 0,
                               bool sixteen_registers = false) {
  std::ostringstream oss;
  oss << "(\n  (load-param v0)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 0 (1.0 1.0))\n"
      << (sixteen_registers ? "  (const v16 7)\n  (sput v16 \"LFoo;.r:I\")\n"
                            : "")
      << "  (switch v0 (:a :b :c))\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 1 (0.0 0.0))\n"
      << mt::sputChain(3, "d") << "  (return-void)\n"
      << "  (:a " << kept_key << ")\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 2 (1.0 1.0))\n"
      << "  (return-void)\n"
      << "  (:b 1)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 3 (0.0 0.0))\n"
      << mt::sputChain(3, "b") << "  (return-void)\n"
      << "  (:c 2)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 4 (0.0 0.0))\n"
      << mt::sputChain(3, "c") << "  (return-void)\n)\n";
  return oss.str();
}

// `coldSwitchGroupCfg(5)` switching on a constant `v1` instead: the split
// recreates it rather than taking it as an argument, and only case 1's head
// reads it.
std::string constSelectorGroupCfg() {
  std::ostringstream oss;
  oss << "(\n  (load-param v0)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 0 (1.0 1.0))\n"
      << "  (const v1 1)\n"
      << "  (switch v1 (:a :b :c))\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 1 (0.0 0.0))\n"
      << mt::sputChain(3, "d") << "  (return-void)\n"
      << "  (:a 5)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 2 (1.0 1.0))\n"
      << "  (return-void)\n"
      << "  (:b 1)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 3 (0.0 0.0))\n"
      << "  (sput v1 \"LFoo;.selector:I\")\n"
      << mt::sputChain(2, "b") << "  (return-void)\n"
      << "  (:c 2)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 4 (0.0 0.0))\n"
      << mt::sputChain(3, "c") << "  (return-void)\n)\n";
  return oss.str();
}

// The one block reachable from the entry that dispatches on a switch or an
// `if`: in these fixtures every other block returns.
cfg::Block* dispatchBlockOf(cfg::ControlFlowGraph& cfg) {
  cfg::Block* found = nullptr;
  for (auto* b : cfg.blocks()) {
    if (b->preds().empty() && b != cfg.entry_block()) {
      continue;
    }
    const auto branching = b->branchingness();
    if (branching == opcode::BRANCH_SWITCH || branching == opcode::BRANCH_IF) {
      EXPECT_EQ(found, nullptr) << "expected one dispatch";
      found = b;
    }
  }
  always_assert(found != nullptr);
  return found;
}

// The one switch reachable from the entry. A suffix split is an untrimmed deep
// copy of its host, so it can still hold the host's switch in an unreachable
// block.
cfg::Block* switchBlockOf(cfg::ControlFlowGraph& cfg) {
  cfg::Block* found = nullptr;
  std::vector<cfg::Block*> work{cfg.entry_block()};
  UnorderedSet<cfg::Block*> seen{cfg.entry_block()};
  while (!work.empty()) {
    auto* b = work.back();
    work.pop_back();
    auto last = b->get_last_insn();
    if (last != b->end() && opcode::is_switch(last->insn->opcode())) {
      EXPECT_EQ(found, nullptr) << "expected one switch";
      found = b;
    }
    for (auto* e : b->succs()) {
      if (seen.insert(e->target()).second) {
        work.push_back(e->target());
      }
    }
  }
  return found;
}

} // namespace

// `suffix_net_gate` lowers the hot-cold suffix floor to
// `min_suffix_sub_floor_split_size` where that is lower. With that configured
// ABOVE the suffix floor, turning the gate on must not raise the floor and drop
// a tail the suffix floor already admits and that pays.
TEST_F(MethodSplitterSuffixNetGateTest, GateNeverRaisesTheSuffixFloor) {
  auto on_cfg = gateConfig();
  on_cfg.min_suffix_sub_floor_split_size = 150;
  auto off_cfg = on_cfg;
  off_cfg.suffix_net_gate = false;

  const auto off = hotColdSplits(
      mt::runSplitter("(I)V", hotColdTailCfg(55), off_cfg).suffix_splits);
  const auto on = hotColdSplits(
      mt::runSplitter("(I)V", hotColdTailCfg(55), on_cfg).suffix_splits);
  ASSERT_EQ(off.size(), 1u)
      << "the tail must clear the suffix floor on its own";
  EXPECT_EQ(on.size(), off.size());
}

namespace {

// `units` code units of `sput`s to fields named after `marker`, and a one-unit
// `move` when `units` is odd.
std::string paddingOf(size_t units, std::string_view marker) {
  return mt::sputChain(units / mt::kSputCodeUnits, marker) +
         (units % mt::kSputCodeUnits != 0 ? "  (move v1 v0)\n" : "");
}

// A cold tail that splits at exactly `split_size` code units under `cfg` and
// leaves exactly `kept_size` in the host. The split counts `cost_split_method`
// plus the tail and its `return-void`; the host keeps its entry, the entry's
// `if-eqz` and the other arm's `return-void`. `entry` gives the weights of the
// entry and the other arm: hot weights make the tail a hot-cold suffix, cold
// ones a Cold suffix.
std::string sizedTailCfg(size_t split_size,
                         size_t kept_size,
                         const msi::Config& cfg,
                         std::string_view entry) {
  std::ostringstream oss;
  oss << "(\n  (load-param v0)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 0 " << entry << ")\n"
      << paddingOf(kept_size - 2 /* if-eqz */ - 1 /* return-void */, "entry")
      << "  (if-eqz v0 :other)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 1 " << mt::kColdWeights << ")\n"
      << paddingOf(split_size - cfg.cost_split_method - 1 /* return-void */,
                   "tail")
      << "  (return-void)\n"
      << "  (:other)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 2 " << entry << ")\n"
      << "  (return-void)\n)\n";
  return oss.str();
}

// Whether the tail of `sizedTailCfg` is split under `cfg`.
bool sizedTailSplit(size_t split_size,
                    size_t kept_size,
                    const msi::Config& cfg,
                    std::string_view entry) {
  auto res = mt::runSplitter(
      "(I)V", sizedTailCfg(split_size, kept_size, cfg, entry), cfg);
  return mt::countFieldRefsIn(res, "tail", mt::Where::SuffixSplits) > 0;
}

} // namespace

// With the gate on, both hot-cold floors drop to the default
// `min_suffix_sub_floor_split_size`, 80 code units: a tail that pays is split
// when it takes 80 and the host keeps 80, and refused when either is 79, where
// only the floor refuses it.
TEST_F(MethodSplitterSuffixNetGateTest, DefaultSubFloorIsEightyCodeUnits) {
  auto cfg = gateConfig();
  cfg.min_suffix_sub_floor_split_size =
      msi::Config{}.min_suffix_sub_floor_split_size;
  cfg.min_hot_split_size = 100;
  EXPECT_EQ(cfg.min_suffix_sub_floor_split_size, 80u);
  const auto hot = mt::kHotWeights;
  EXPECT_TRUE(sizedTailSplit(80, 80, cfg, hot));
  EXPECT_FALSE(sizedTailSplit(79, 80, cfg, hot));
  EXPECT_FALSE(sizedTailSplit(120, 79, cfg, hot));
  auto lower = cfg;
  lower.min_suffix_sub_floor_split_size = 79;
  EXPECT_TRUE(sizedTailSplit(79, 79, lower, hot))
      << "the tail must pay, so that only the floors refuse it";
}

// The cold gate drops both Cold floors to the same default, 80 code units.
TEST_F(MethodSplitterSuffixNetGateTest,
       ColdGateDefaultSubFloorIsEightyCodeUnits) {
  auto cfg = coldGateConfig();
  cfg.min_suffix_sub_floor_split_size =
      msi::Config{}.min_suffix_sub_floor_split_size;
  const auto cold = mt::kColdWeights;
  EXPECT_TRUE(sizedTailSplit(80, 80, cfg, cold));
  EXPECT_FALSE(sizedTailSplit(79, 80, cfg, cold));
  EXPECT_FALSE(sizedTailSplit(120, 79, cfg, cold));
  auto lower = cfg;
  lower.min_suffix_sub_floor_split_size = 79;
  EXPECT_TRUE(sizedTailSplit(79, 79, lower, cold))
      << "the tail must pay, so that only the floors refuse it";
}

namespace {

// Splits `code` under the gate and checks that the net saving of its
// switch-group split charges the dispatch as the dex holds it after
// ReduceGotos: the copy of the switch the split starts with, less what the
// host's switch sheds. `recreated` is the dex code units of the constants the
// split recreates.
void expectDispatchChargedAsEmitted(const std::string& code,
                                    int64_t recreated) {
  auto cfg = gateConfig();
  cfg.max_iteration = 1;

  auto res = mt::runSplitter("(I)V", code, cfg);
  const auto splits = hotColdSplits(res.suffix_splits);
  ASSERT_EQ(splits.size(), 1u) << mt::describeSelection(res);
  auto* split = splits.front();
  ASSERT_NE(switchBlockOf(split->get_code()->cfg()), nullptr)
      << "not a switch-group split";
  auto original = assembler::ircode_from_string(code);
  original->build_cfg();
  for (auto* c :
       {split->get_code(), res.main_method->get_code(), original.get()}) {
    ReduceGotosPass::process_code(c);
  }
  const int64_t split_dispatch =
      dispatchBlockOf(split->get_code()->cfg())->estimate_code_units();
  const int64_t host_shrink =
      static_cast<int64_t>(
          dispatchBlockOf(original->cfg())->estimate_code_units()) -
      static_cast<int64_t>(dispatchBlockOf(res.main_method->get_code()->cfg())
                               ->estimate_code_units());
  ASSERT_GT(host_shrink, 0);

  // The group's net saving, from its evaluation record. Each cold case can also
  // split on its own, at a different net saving, so only the split that
  // dispatches counts.
  int64_t dex_added_cost = 0;
  for (const auto& e : mt::evaluationsOf(res, msi::SplitKind::Suffix,
                                         msi::CandidateFate::Emitted)) {
    if (e.split == split) {
      ASSERT_TRUE(e.terms.has_value());
      dex_added_cost = e.terms->dex_added;
    }
  }
  // One more method, its launchpad (`invoke; return-void`), one load-param per
  // argument, the recreated constants and the dispatch delta the dex holds.
  // Nothing here is duplicated, and one argument needs no range spill.
  const size_t args = split->get_proto()->get_args()->size();
  const auto wrapper = static_cast<int64_t>(cfg.net_cu_method_metadata +
                                            suffixLaunchpadCodeUnits() +
                                            cfg.net_cu_load_param * args);
  EXPECT_EQ(dex_added_cost, wrapper + recreated + split_dispatch - host_shrink);
}

} // namespace

// A suffix switch-group split copies the switch, with the grouped keys'
// payload, into the split as its landing pad, and the host's switch keeps only
// the keys left behind -- here key 0, which ReduceGotos turns into `if-eqz`.
TEST_F(MethodSplitterSuffixNetGateTest,
       NetSavingChargesTheSwitchGroupDispatch) {
  expectDispatchChargedAsEmitted(coldSwitchGroupCfg(), 0);
}

// The host's switch keeps key 5 alone and reads its selector nowhere else, but
// its default edge goes to the launchpad, which passes the selector to the
// split. So the selector stays live and ReduceGotos keeps a switch, not
// `rsub-int/lit8; if-eqz`.
TEST_F(MethodSplitterSuffixNetGateTest,
       NetSavingChargesASelectorTheLaunchpadPassesAsLive) {
  expectDispatchChargedAsEmitted(
      coldSwitchGroupCfg(/*kept_key=*/5, /*sixteen_registers=*/true), 0);
}

// Only the head of a deleted key reads the selector, a constant the split
// recreates rather than takes. The host reads it nowhere once its switch keeps
// key 5 alone, so ReduceGotos turns the switch into `rsub-int/lit8; if-eqz`.
TEST_F(MethodSplitterSuffixNetGateTest,
       NetSavingChargesASelectorReadOnlyAtADeletedKeysHeadAsDead) {
  expectDispatchChargedAsEmitted(constSelectorGroupCfg(),
                                 /* const/4 */ 1);
}

namespace {

// The net saving `split_net_saving` gives the split `wanted` picks out of a run
// of `code`.
method_splitting_impl::ClosureNetTerms netSavingTerms(
    const std::string& code,
    size_t min_hot_split_size,
    const std::function<bool(DexMethod*)>& wanted) {
  auto c = gateConfig();
  c.max_iteration = 1;
  // The sub-floor these fixtures were written against, pinned so that what
  // they evaluate does not move with the default.
  c.min_suffix_sub_floor_split_size = 40;
  c.min_hot_split_size = min_hot_split_size;
  auto res = mt::runSplitter("(I)V", code, c, "LNetSaving");
  for (const auto& e : mt::evaluationsOf(res, msi::SplitKind::Suffix,
                                         msi::CandidateFate::Emitted)) {
    if (!e.terms) {
      continue;
    }
    for (auto* split : res.suffix_splits) {
      if (split == e.split && wanted(split)) {
        return *e.terms;
      }
    }
  }
  ADD_FAILURE() << "no evaluated split was emitted"
                << mt::describeSelection(res);
  return {};
}

// The `saved - added_ccuc` `split_net_saving` gives the same split.
int64_t netCompiledSaving(const std::string& code,
                          size_t min_hot_split_size,
                          const std::function<bool(DexMethod*)>& wanted) {
  const auto terms = netSavingTerms(code, min_hot_split_size, wanted);
  return terms.saved - terms.added_ccuc;
}

// A hot `switch` whose cold default and cold cases 2 and 3 split as a group,
// with case 3's head reached from case 2's tail `:m`. When `kept_reaches_m`,
// the hot case 0 jumps into `:m` too; otherwise it returns.
std::string keptCaseCfg(bool kept_reaches_m) {
  std::ostringstream oss;
  oss << "(\n  (load-param v0)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 0 (1.0 1.0))\n"
      << mt::sputChain(50, "e") << "  (switch v0 (:k :h2 :h3))\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 1 (0.0 0.0))\n"
      << mt::sputChain(3, "d") << "  (return-void)\n"
      << "  (:k 0)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 2 (1.0 1.0))\n"
      << "  (sput v0 \"LFoo;.kept:I\")\n"
      << (kept_reaches_m ? "  (goto :m)\n" : "  (return-void)\n")
      << "  (:h2 2)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 3 (0.0 0.0))\n"
      << mt::sputChain(6, "a") << "  (:m)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 4 (0.0 0.0))\n"
      << "  (const v1 3)\n";
  for (int i = 0; i < 4; i++) {
    oss << "  (sput v1 \"LFoo;.m" << i << ":I\")\n";
  }
  oss << "  (:h3 3)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 5 (0.0 0.0))\n"
      << mt::sputChain(6, "c") << "  (return-void)\n)\n";
  return oss.str();
}

} // namespace

TEST_F(MethodSplitterSuffixNetGateTest,
       SuffixGroupDuplicatesWhatAKeptCaseStillReaches) {
  // The cold default and cases 2 and 3 are grouped; case 0 is hot and kept.
  // `:m` is the tail that case 2 falls through to, and it falls through into
  // case 3's head. When the kept case jumps into `:m`, the host keeps both `:m`
  // and case 3's head: its switch loses only the grouped keys, so the kept case
  // still reaches `:m` and, through it, case 3's head. The split copies them.
  // Each cold case alone is below the suffix floor, so only the group splits.
  // The hot floor keeps the hot case out of the group, and the hot filler
  // before the switch keeps the remainder above that floor.
  const auto is_group = [](DexMethod* m) {
    return switchBlockOf(m->get_code()->cfg()) != nullptr;
  };
  const auto reaches = keptCaseCfg(true);
  const auto returns = keptCaseCfg(false);
  const int64_t dex_reaches = netSavingTerms(reaches, 90, is_group).dex_added;
  const int64_t dex_returns = netSavingTerms(returns, 90, is_group).dex_added;
  // `:m` is `const/4` and 4 sputs; case 3's head is 6 sputs and the return.
  EXPECT_EQ(dex_reaches - dex_returns,
            static_cast<int64_t>(1 + 4 * mt::kSputCodeUnits +
                                 6 * mt::kSputCodeUnits + 1));
  // `saved` is what leaves the host, in the units the profile counts compiled
  // code in (`const` at 3). When the kept case reaches `:m`, that is the
  // default's 3 sputs and return and case 2's 6 sputs. Otherwise `:m` and case
  // 3 leave too. Every other term is the same in both.
  const int64_t moved_reaches = netCompiledSaving(reaches, 90, is_group);
  const int64_t moved_returns = netCompiledSaving(returns, 90, is_group);
  EXPECT_EQ(moved_returns - moved_reaches,
            static_cast<int64_t>(3 + 4 * mt::kSputCodeUnits +
                                 6 * mt::kSputCodeUnits + 1));
}

TEST_F(MethodSplitterSuffixNetGateTest, HotCodeTheSuffixTakesEarnsNothing) {
  // The tail's head is cold, so the suffix is hot-cold, but one arm below it
  // is hot. The split is not compiled, so taking that arm out of the compiled
  // host saves no compiled cold code; only the cold blocks count as `saved`.
  std::ostringstream oss;
  oss << "(\n  (load-param v0)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 0 (1.0 1.0))\n"
      << "  (if-eqz v0 :hot_ret)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 1 (0.0 0.0))\n"
      << mt::sputChain(10, "a") << "  (if-nez v0 :cold_arm)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 2 (1.0 1.0))\n"
      << mt::sputChain(8, "h") << "  (return-void)\n"
      << "  (:cold_arm)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 3 (0.0 0.0))\n"
      << mt::sputChain(5, "c") << "  (return-void)\n"
      << "  (:hot_ret)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 4 (1.0 1.0))\n"
      << "  (return-void)\n)\n";
  const auto code = oss.str();
  const auto any = [](DexMethod*) { return true; };
  const auto cfg = gateConfig();
  // `saved` minus the launchpad the host gains, `invoke; return-void`.
  const int64_t saved = netCompiledSaving(code, 1, any) +
                        static_cast<int64_t>(suffixLaunchpadCodeUnits());
  // The cold head (10 sputs and its `if-nez`) and the cold arm (5 sputs and
  // its return).
  EXPECT_EQ(saved,
            static_cast<int64_t>(10 * mt::kSputCodeUnits + 2 +
                                 5 * mt::kSputCodeUnits + 1));
}

// The hot-cold gate lowers the remaining-size floor of the suffixes it
// evaluates as well: here the host keeps less than `min_hot_split_size`, which
// refuses the tail on the legacy floors, and the gate keeps it because it pays.
TEST_F(MethodSplitterSuffixNetGateTest,
       HotColdGateEvaluatesATailOnlyItsLoweredRemainingFloorAdmits) {
  std::ostringstream oss;
  oss << "(\n  (load-param v0)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 0 (1.0 1.0))\n"
      << mt::sputChain(30, "h") << "  (if-eqz v0 :hot_ret)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 1 (0.0 0.0))\n"
      << mt::sputChain(60, "c") << "  (return-void)\n"
      << "  (:hot_ret)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 2 (1.0 1.0))\n"
      << "  (return-void)\n)\n";
  auto base = baseConfig();
  base.min_hot_split_size = 1000;
  auto off = mt::runSplitter("(I)V", oss.str(), base);
  ASSERT_TRUE(hotColdSplits(off.suffix_splits).empty())
      << "precondition: the remainder is below `min_hot_split_size`";
  auto gate = gateConfig();
  gate.min_hot_split_size = 1000;
  auto on = mt::runSplitter("(I)V", oss.str(), gate);
  EXPECT_EQ(hotColdSplits(on.suffix_splits).size(), 1u);
  // The net saving decides: a prohibitive split cost turns it down.
  gate.net_cu_method_metadata = 100000;
  EXPECT_TRUE(
      hotColdSplits(mt::runSplitter("(I)V", oss.str(), gate).suffix_splits)
          .empty());
}

// A switch group taking the default and the one case key 5: the split's copy
// of the switch keeps key 5 alone, and its cases overwrite the selector before
// reading it, so ReduceGotos leaves `rsub-int/lit8; if-eqz` there. The cost
// is what the dex keeps.
TEST_F(MethodSplitterSuffixNetGateTest,
       NetSavingChargesAOneKeyDispatchAsReduceGotosLeavesIt) {
  std::ostringstream oss;
  oss << "(\n  (load-param v0)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 0 (1.0 1.0))\n"
      << "  (switch v0 (:a :b))\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 1 (0.0 0.0))\n"
      << "  (const v0 7)\n"
      << mt::sputChain(3, "d") << "  (return-void)\n"
      << "  (:a 0)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 2 (1.0 1.0))\n"
      << "  (return-void)\n"
      << "  (:b 5)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 3 (0.0 0.0))\n"
      << "  (const v0 8)\n"
      << mt::sputChain(3, "b") << "  (return-void)\n)\n";
  const auto code = oss.str();
  auto cfg = gateConfig();
  cfg.max_iteration = 1;
  auto res = mt::runSplitter("(I)V", code, cfg);
  const auto splits = hotColdSplits(res.suffix_splits);
  ASSERT_EQ(splits.size(), 1u);
  auto* split = splits.front();
  ASSERT_NE(switchBlockOf(split->get_code()->cfg()), nullptr)
      << "not a switch-group split";
  auto original = assembler::ircode_from_string(code);
  original->build_cfg();
  for (auto* c :
       {split->get_code(), res.main_method->get_code(), original.get()}) {
    ReduceGotosPass::process_code(c);
  }
  const int64_t split_dispatch =
      dispatchBlockOf(split->get_code()->cfg())->estimate_code_units();
  // `rsub-int/lit8` and `if-eqz`.
  ASSERT_EQ(split_dispatch, 4);
  const int64_t host_shrink =
      static_cast<int64_t>(
          dispatchBlockOf(original->cfg())->estimate_code_units()) -
      static_cast<int64_t>(dispatchBlockOf(res.main_method->get_code()->cfg())
                               ->estimate_code_units());
  int64_t dex_added_cost = 0;
  for (const auto& e : mt::evaluationsOf(res, msi::SplitKind::Suffix,
                                         msi::CandidateFate::Emitted)) {
    if (e.split == split) {
      ASSERT_TRUE(e.terms.has_value());
      dex_added_cost = e.terms->dex_added;
    }
  }
  // One more method, its launchpad (`invoke; return-void`), one load-param for
  // the selector, and the dispatch delta the dex holds.
  const auto wrapper =
      static_cast<int64_t>(cfg.net_cu_method_metadata +
                           suffixLaunchpadCodeUnits() + cfg.net_cu_load_param);
  EXPECT_EQ(dex_added_cost, wrapper + split_dispatch - host_shrink);
}

// A switch group taking the default and cases 6 and 9 over a constant
// selector, which the split recreates rather than takes: nothing the host
// keeps reads the selector after its switch, which is left with key 5 alone,
// so ReduceGotos leaves `rsub-int/lit8; if-eqz` in the host. The cost is what
// the dex keeps there.
TEST_F(MethodSplitterSuffixNetGateTest,
       NetSavingChargesTheHostsOneKeyDispatchAsReduceGotosLeavesIt) {
  std::ostringstream oss;
  oss << "(\n  (load-param v0)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 0 (1.0 1.0))\n"
      << mt::sputChain(50, "e") << "  (const v0 6)\n"
      << "  (switch v0 (:a :b :c))\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 1 (0.0 0.0))\n"
      << "  (const v0 7)\n"
      << mt::sputChain(3, "d") << "  (return-void)\n"
      << "  (:a 5)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 2 (1.0 1.0))\n"
      << "  (const v1 1)\n"
      << "  (sput v1 \"LFoo;.kept:I\")\n"
      << "  (return-void)\n"
      << "  (:b 6)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 3 (0.0 0.0))\n"
      << "  (const v0 8)\n"
      << mt::sputChain(3, "b") << "  (return-void)\n"
      << "  (:c 9)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 4 (0.0 0.0))\n"
      << "  (const v0 9)\n"
      << mt::sputChain(3, "c") << "  (return-void)\n)\n";
  const auto code = oss.str();
  auto cfg = gateConfig();
  cfg.max_iteration = 1;
  auto res = mt::runSplitter("(I)V", code, cfg);
  const auto splits = hotColdSplits(res.suffix_splits);
  ASSERT_EQ(splits.size(), 1u) << mt::describeSelection(res);
  auto* split = splits.front();
  ASSERT_NE(switchBlockOf(split->get_code()->cfg()), nullptr)
      << "not a switch-group split";
  auto original = assembler::ircode_from_string(code);
  original->build_cfg();
  for (auto* c :
       {split->get_code(), res.main_method->get_code(), original.get()}) {
    ReduceGotosPass::process_code(c);
  }
  auto* host_block = dispatchBlockOf(res.main_method->get_code()->cfg());
  const int64_t host_dispatch = host_block->estimate_code_units();
  auto last = host_block->get_last_insn();
  ASSERT_EQ(last->insn->opcode(), OPCODE_IF_EQZ);
  ASSERT_EQ(std::prev(last)->insn->opcode(), OPCODE_RSUB_INT_LIT);
  const int64_t split_dispatch =
      dispatchBlockOf(split->get_code()->cfg())->estimate_code_units();
  const int64_t host_shrink =
      static_cast<int64_t>(
          dispatchBlockOf(original->cfg())->estimate_code_units()) -
      host_dispatch;
  int64_t dex_added_cost = 0;
  for (const auto& e : mt::evaluationsOf(res, msi::SplitKind::Suffix,
                                         msi::CandidateFate::Emitted)) {
    if (e.split == split) {
      ASSERT_TRUE(e.terms.has_value());
      dex_added_cost = e.terms->dex_added;
    }
  }
  // One more method, its launchpad (`invoke; return-void`), no parameter, and
  // the dispatch delta the dex holds. There is no parameter because the split
  // recreates the selector's `const` (1).
  ASSERT_TRUE(split->get_proto()->get_args()->empty());
  const auto wrapper = static_cast<int64_t>(cfg.net_cu_method_metadata +
                                            suffixLaunchpadCodeUnits() + 1);
  EXPECT_EQ(dex_added_cost, wrapper + split_dispatch - host_shrink);
}

// A constant the cold tail reads is recreated in the split rather than passed
// to it: it costs its own dex size, and no load-param; the parameter it also
// reads is passed.
TEST_F(MethodSplitterSuffixNetGateTest, ARecreatedConstantCostsNoLoadParam) {
  std::ostringstream oss;
  oss << "(\n  (load-param v0)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 0 (1.0 1.0))\n"
      << "  (const v1 1000)\n"
      << "  (if-eqz v0 :hot_ret)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 1 (0.0 0.0))\n"
      << "  (sput v1 \"LFoo;.r:I\")\n"
      << mt::sputChain(60, "c") << "  (return-void)\n"
      << "  (:hot_ret)\n"
      << "  (.src_block \"LFoo;.bar:(I)V\" 2 (1.0 1.0))\n"
      << "  (return-void)\n)\n";
  const auto code = oss.str();
  const auto any = [](DexMethod*) { return true; };
  const auto dex = netSavingTerms(code, 1, any).dex_added;
  // The parameter passed, `const/16` (2) recreated: metadata, the launchpad
  // `invoke; return-void`, one load-param, and the constant.
  const auto cfg = gateConfig();
  EXPECT_EQ(dex,
            static_cast<int64_t>(cfg.net_cu_method_metadata +
                                 suffixLaunchpadCodeUnits() +
                                 cfg.net_cu_load_param + 2));
}
