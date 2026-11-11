/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

// The net-saving model on its own: every term of `split_net_saving`, at the
// default code-unit table, for the launchpads, return shapes and switch edits
// the emitter produces. Each expectation spells out the instructions it costs.

#include <gtest/gtest.h>

#include <memory>
#include <vector>

#include "ControlFlow.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "InstructionLowering.h"
#include "RedexTest.h"
#include "SplitNetSaving.h"
#include "SwitchFixture.h"

namespace msi = method_splitting_impl;
using method_splitting_test::SwitchFixture;

class SplitNetSavingTest : public RedexTest {};

namespace {

// 100 code units evicted from a compiled host, two narrow arguments.
msi::NetSavingInput suffix_input() {
  return msi::NetSavingInput{
      .split = msi::NetSavingInput::Suffix{.returns_value = true},
      .dispatch = std::nullopt,
      .evicted = 100,
      .duplicated = 5,
      .passed_args = 2,
      .passed_arg_registers = 2,
      .recreated_defs = 0,
  };
}

// The default costs the expectations below spell out: the per-split metadata,
// and a `load-param` per argument.
int64_t metadata() {
  return static_cast<int64_t>(msi::Config{}.net_cu_method_metadata);
}
int64_t load_params(int64_t args) {
  return args * static_cast<int64_t>(msi::Config{}.net_cu_load_param);
}

void expect_terms(const msi::ClosureNetTerms& terms,
                  int64_t saved,
                  int64_t added_ccuc,
                  int64_t dex_added) {
  EXPECT_EQ(terms.saved, saved);
  EXPECT_EQ(terms.added_ccuc, added_ccuc);
  EXPECT_EQ(terms.dex_added, dex_added);
  EXPECT_DOUBLE_EQ(terms.net,
                   static_cast<double>(msi::Config{}.net_oat_weight) *
                           static_cast<double>(saved - added_ccuc) -
                       static_cast<double>(dex_added));
}

} // namespace

TEST_F(SplitNetSavingTest, DexCodeUnitsSizeEachConstByItsLiteral) {
  // `const/4`, `const/16`, `const/high16`, `const`; `const-wide/16`,
  // `const-wide/32`, `const-wide/high16`, `const-wide`; then `return-void`.
  auto code = assembler::ircode_from_string(R"((
    (const v0 7)
    (const v0 -8)
    (const v0 1000)
    (const v0 65536)
    (const v0 74565)
    (const-wide v2 5)
    (const-wide v2 305419896)
    (const-wide v2 281474976710656)
    (const-wide v2 1311768467463790320)
    (return-void)
  ))");
  code->build_cfg();
  ASSERT_EQ(code->cfg().blocks().size(), 1u);
  const auto* b = code->cfg().blocks().front();
  EXPECT_EQ(b->estimate_code_units(), 5 * 3 + 4 * 5 + 1);
  EXPECT_EQ(msi::dex_code_units(b), 1 + 1 + 2 + 2 + 3 + 2 + 3 + 2 + 5 + 1);
}

TEST_F(SplitNetSavingTest, PartitionSwitchSplitsEveryKeyByItsTarget) {
  SwitchFixture f;
  auto p = f.partition({f.case0, f.dflt});
  EXPECT_EQ(p.all.size(), 2u);
  EXPECT_EQ(p.grouped.size(), 1u);
  EXPECT_EQ(p.kept.size(), 1u);
  EXPECT_TRUE(p.default_grouped);
  EXPECT_FALSE(f.partition({f.case0, f.case1}).default_grouped);
}

TEST_F(SplitNetSavingTest, HostDispatchAfterTheEdit) {
  SwitchFixture f;
  auto p = f.partition({f.case0, f.dflt});
  // Deleting key 0 leaves a switch over key 1, with a payload of 4 + 2: the
  // selector stays live into the launchpad, so ReduceGotos keeps the switch in
  // any method with 16 registers or more. A switch over key 0 becomes
  // `if-eqz` (2).
  EXPECT_EQ(host_dispatch_after(p, msi::HostSwitchEdit::DeleteGrouped,
                                /*selector_live=*/true),
            3u + 6u);
  auto keeps0 = f.partition({f.case1, f.dflt});
  EXPECT_EQ(host_dispatch_after(keeps0, msi::HostSwitchEdit::DeleteGrouped,
                                /*selector_live=*/true),
            2u);
  // A switch left with no key is removed.
  auto all = f.partition({f.case0, f.case1, f.dflt});
  EXPECT_EQ(host_dispatch_after(all, msi::HostSwitchEdit::DeleteGrouped,
                                /*selector_live=*/true),
            0u);
}

TEST_F(SplitNetSavingTest, SwitchOverOneKeyIsChargedAsReduceGotosLeavesIt) {
  const auto keys = [](std::initializer_list<int32_t> ks) {
    instruction_lowering::CaseKeysExtentBuilder b;
    for (auto k : ks) {
      b.insert(k);
    }
    return b;
  };
  EXPECT_EQ(msi::switch_dispatch_code_units(keys({}), true), 0u);
  // Key 0: `if-eqz` (2), whether the selector is read later or not.
  EXPECT_EQ(msi::switch_dispatch_code_units(keys({0}), true), 2u);
  EXPECT_EQ(msi::switch_dispatch_code_units(keys({0}), false), 2u);
  // Another key: `rsub-int/lit8; if-eqz` (2 + 2) when the selector is dead
  // after the switch. When the selector is read later, or the key needs more
  // than 8 bits, the switch stays, with its packed payload (3 + 4 + 2).
  EXPECT_EQ(msi::switch_dispatch_code_units(keys({5}), false), 4u);
  EXPECT_EQ(msi::switch_dispatch_code_units(keys({5}), true), 9u);
  EXPECT_EQ(msi::switch_dispatch_code_units(keys({200}), false), 9u);
  // Two keys stay a switch.
  EXPECT_EQ(msi::switch_dispatch_code_units(keys({4, 5}), false), 3u + 4u + 4u);
}

TEST_F(SplitNetSavingTest, SuffixTerminalLaunchpad) {
  msi::Config config;
  // The launchpad `invoke; move-result; return` (5) re-enters the compiled
  // host. Dex grows by the launchpad, the metadata, a load-param per argument,
  // and the 5 duplicated code units.
  expect_terms(split_net_saving(suffix_input(), config, /*host_compiled=*/true),
               100, 5, 5 + metadata() + load_params(2) + 5);
  // An uncompiled host evicts nothing from compiled code.
  expect_terms(
      split_net_saving(suffix_input(), config, /*host_compiled=*/false), 0, 0,
      5 + metadata() + load_params(2) + 5);
  // A void host's launchpad has no `move-result`.
  auto void_host = suffix_input();
  void_host.split = msi::NetSavingInput::Suffix{.returns_value = false};
  expect_terms(split_net_saving(void_host, config, true), 100, 4,
               4 + metadata() + load_params(2) + 5);
}

TEST_F(SplitNetSavingTest,
       EveryCompiledCopyLosesTheEvictedCodeAndGainsALaunchpad) {
  msi::Config config;
  // A host ART inlines into three compiled callers: each copy loses the 100
  // evicted code units and gains the 5-unit launchpad, while the dex pays for
  // the split once.
  auto inlined = suffix_input();
  inlined.compiled_copies = 3;
  expect_terms(split_net_saving(inlined, config, /*host_compiled=*/true), 300,
               15, 5 + metadata() + load_params(2) + 5);
  // By default the host itself is the one compiled copy.
  EXPECT_EQ(suffix_input().compiled_copies, 1u);
}

TEST_F(SplitNetSavingTest, AHotSplitKeepsOneCompiledCopyOfWhatItEvicts) {
  msi::Config config;
  // A Hot split is compiled: with one compiled copy of the host, the evicted
  // code moves into the split and stays compiled, so nothing is saved.
  auto hot = suffix_input();
  hot.split_compiled = true;
  expect_terms(split_net_saving(hot, config, /*host_compiled=*/true), 0, 5,
               5 + metadata() + load_params(2) + 5);
  // With three compiled copies, two of them lose the evicted code; each keeps
  // a launchpad.
  hot.compiled_copies = 3;
  expect_terms(split_net_saving(hot, config, /*host_compiled=*/true), 200, 15,
               5 + metadata() + load_params(2) + 5);
}

TEST_F(SplitNetSavingTest, RecreatedConstantsCostTheirDexSizeNotALoadParam) {
  msi::Config config;
  auto in = suffix_input();
  // One argument passed, and a `const/16` recreated in the split.
  in.passed_args = 1;
  in.passed_arg_registers = 1;
  in.recreated_defs = 2;
  expect_terms(split_net_saving(in, config, true), 100, 5,
               5 + metadata() + load_params(1) + 2 + 5);
}

TEST_F(SplitNetSavingTest, SuffixRangeInvokeSpillsEveryArgumentRegister) {
  msi::Config config;
  auto in = suffix_input();
  in.passed_arg_registers = 5;
  expect_terms(split_net_saving(in, config, true), 100, 5,
               5 + metadata() + load_params(2) + 5);
  in.passed_arg_registers = 6;
  expect_terms(split_net_saving(in, config, true), 100, 5 + 6,
               5 + 6 + metadata() + load_params(2) + 5);
}

TEST_F(SplitNetSavingTest, SuffixGroupCopiesTheSwitchAndShedsItsKeys) {
  SwitchFixture f;
  msi::Config config;
  auto p = f.partition({f.case0, f.dflt});
  auto in = suffix_input();
  in.dispatch.emplace(
      msi::NetSavingInput::Dispatch{.partition = p,
                                    .selector_live_in_split = true,
                                    .selector_live_in_host_before = true,
                                    .selector_live_in_host_after = true});
  // The split's copy keeps key 0: `if-eqz` (2). The host's switch goes from
  // keys 0..1 (3 + 8) to key 1 (3 + 6), and the 2 code units shed leave the
  // host.
  expect_terms(split_net_saving(in, config, true), 100 + 2, 5,
               5 + metadata() + load_params(2) + 5 + 2 - 2);
}
