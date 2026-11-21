/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

// Direct tests of the region split builder (`SplitMethod::create` with a
// `RegionEmission`) and of the call block it gives the host
// (`apply_code_changes`), on region candidates assembled from discovery's
// closures.

#include <gtest/gtest.h>

#include <memory>
#include <string>
#include <string_view>

#include "ControlFlow.h"
#include "Creators.h"
#include "DexClass.h"
#include "DexPosition.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "MethodClosures.h"
#include "MethodSplitter.h"
#include "MethodSplittingStats.h"
#include "RedexTest.h"
#include "RegionPlan.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "SplittableClosures.h"
#include "TypeUtil.h"

namespace msi = method_splitting_impl;

class MethodSplitterRegionBuilderTest : public RedexTest {};

namespace {

// A new class holding one static method `bar:(I)V` with body `code`, its CFG
// built and normalized as the splitter leaves it.
DexMethod* make_host(const std::string& code) {
  static size_t classes = 0;
  const std::string cls_name =
      "LRegionBuilder" + std::to_string(classes++) + ";";
  ClassCreator cc(DexType::make_type(cls_name));
  cc.set_super(type::java_lang_Object());
  auto* m = DexMethod::make_method(cls_name + ".bar:(I)V")
                ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                                assembler::ircode_from_string(code),
                                /* is_virtual */ false);
  m->set_deobfuscated_name(show(m));
  m->get_code()->build_cfg();
  cc.add_method(m);
  cc.create();
  msi::normalize_cfg_for_splitting(m);
  return m;
}

// The region closures discovery finds in `m`, owned by a `MethodClosures` as
// the splitter's are.
std::shared_ptr<msi::MethodClosures> discover(DexMethod* m) {
  auto rcfg = msi::reduce_cfg(m);
  msi::Stats stats;
  auto closures = msi::RegionStrategy(stats).discover(m, *rcfg);
  const auto original_size = rcfg->code_size();
  return std::make_shared<msi::MethodClosures>(
      msi::MethodClosures{.method = m,
                          .original_size = original_size,
                          .rcfg = std::move(rcfg),
                          .closures = std::move(closures)});
}

// The closure whose head stores to a field named `<prefix>_0`.
const msi::Closure& closure_storing(const msi::MethodClosures& mcs,
                                    std::string_view prefix) {
  const std::string field = std::string(prefix) + "_0";
  for (const auto& c : mcs.closures) {
    for (const auto& mie : InstructionIterable(c.target)) {
      if (mie.insn->has_field() && mie.insn->get_field()->str() == field) {
        return c;
      }
    }
  }
  always_assert_log(false, "no region closure stores to %s", field.c_str());
  return mcs.closures.front();
}

// The region candidate of `closure`, which passes `v0` as its one parameter.
msi::SplittableClosure candidate(
    const std::shared_ptr<msi::MethodClosures>& mcs,
    const msi::Closure& closure) {
  msi::SplittableClosure sc{
      .method_closures = mcs,
      .switch_block = nullptr,
      .closures = {&closure},
      .grouped_heads = {closure.target->id()},
      .args = {msi::ClosureArgument{
          .reg = 0, .type = type::_int(), .def = nullptr}},
      .kind = msi::SplitKind::Region,
      .hot_split_kind = msi::HotSplitKind::HotCold,
  };
  sc.region_plan = msi::RegionPlan::make(sc.closures);
  return sc;
}

// Builds the split of `sc` and applies it to the host, with the continuation
// read from the live CFG at this point.
DexMethod* apply_split(const msi::SplittableClosure& sc,
                       std::string_view name) {
  const msi::RegionEmission emission{
      .plan = &*sc.region_plan,
      .continuation = msi::live_continuation(*sc.closures.front())};
  auto split = msi::SplitMethod::create(
      sc, sc.method_closures->method->get_class(), DexString::make_string(name),
      sc.get_arg_types(), emission);
  split.add_to_target();
  split.apply_code_changes();
  return split.get_new_method();
}

size_t count_fields(DexMethod* m, std::string_view prefix) {
  size_t n = 0;
  for (const auto& mie : cfg::InstructionIterable(m->get_code()->cfg())) {
    if (mie.insn->has_field() &&
        mie.insn->get_field()->str().starts_with(prefix)) {
      n++;
    }
  }
  return n;
}

// The host block that invokes `split`.
cfg::Block* launchpad_of(DexMethod* host, const DexMethod* split) {
  for (auto* b : host->get_code()->cfg().blocks()) {
    for (const auto& mie : InstructionIterable(b)) {
      if (opcode::is_an_invoke(mie.insn->opcode()) &&
          mie.insn->get_method() == split) {
        return b;
      }
    }
  }
  return nullptr;
}

} // namespace

// The split of a cold block is a static void method that takes the block's
// argument, starts at a synthetic entry position, runs the block and returns
// from a block with a SourceBlock of its own. The call block replaces the
// block, calls the split and jumps to the continuation.
TEST_F(MethodSplitterRegionBuilderTest, ColdBlockBecomesSplitAndLaunchpad) {
  auto* host = make_host(R"(
    (
      (load-param v0)
      (.src_block "LFoo;.bar:(I)V" 0 (1.0 1.0))
      (.pos:dbg_0 "LFoo;.bar:(I)V" "Foo.java" 100)
      (if-eqz v0 :rejoin)
      (.src_block "LFoo;.bar:(I)V" 1 (0.0 0.0))
      (.pos:dbg_1 "LFoo;.bar:(I)V" "Foo.java" 200)
      (sput v0 "LFoo;.cold_0:I")
      (sput v0 "LFoo;.cold_1:I")
      (sput v0 "LFoo;.cold_2:I")
      (:rejoin)
      (.src_block "LFoo;.bar:(I)V" 2 (1.0 1.0))
      (sput v0 "LFoo;.rejoin_0:I")
      (return-void)
    )
  )");
  auto mcs = discover(host);
  ASSERT_EQ(mcs->closures.size(), 1u);
  const auto& closure = mcs->closures.front();
  auto* rejoin = closure.region->rejoin_block();
  ASSERT_NE(rejoin, nullptr);
  auto sc = candidate(mcs, closure);
  auto* split = apply_split(sc, "bar$split$test");

  EXPECT_EQ(show(split->get_proto()), "(I)V");
  EXPECT_TRUE(is_static(split));
  auto& split_cfg = split->get_code()->cfg();
  EXPECT_EQ(count_fields(split, "cold_"), 3u) << show(split_cfg);
  EXPECT_EQ(count_fields(split, "rejoin_"), 0u) << show(split_cfg);
  // The synthetic entry position follows the load-params.
  const DexPosition* entry_pos = nullptr;
  for (const auto& mie : *split_cfg.entry_block()) {
    if (mie.type == MFLOW_POSITION) {
      entry_pos = mie.pos.get();
      break;
    }
  }
  ASSERT_NE(entry_pos, nullptr) << show(split_cfg);
  EXPECT_EQ(entry_pos->method,
            DexString::make_string(show_deobfuscated(split)));
  size_t returns = 0;
  for (auto* b : split_cfg.blocks()) {
    auto last = b->get_last_insn();
    if (last != b->end() && last->insn->opcode() == OPCODE_RETURN_VOID) {
      returns++;
      EXPECT_NE(source_blocks::get_first_source_block(b), nullptr);
    }
  }
  EXPECT_EQ(returns, 1u) << show(split_cfg);

  auto* launchpad = launchpad_of(host, split);
  ASSERT_NE(launchpad, nullptr) << show(host->get_code()->cfg());
  EXPECT_EQ(launchpad->goes_to(), rejoin);
  // Nothing reaches the cold block any more.
  host->get_code()->cfg().simplify();
  EXPECT_EQ(count_fields(host, "cold_"), 0u) << show(host->get_code()->cfg());
}

// A cold block holding what constructor inlining leaves behind, `new-instance
// Sub` initialized by `Base.<init>`, becomes a split like any other block: the
// split type-checks under the same constructor rule as its host.
TEST_F(MethodSplitterRegionBuilderTest, ColdBlockWithASuperclassInitSplits) {
  ClassCreator base(DexType::make_type("LBuilderBase;"));
  base.set_super(type::java_lang_Object());
  auto* base_type = base.create()->get_type();
  ClassCreator sub(DexType::make_type("LBuilderSub;"));
  sub.set_super(base_type);
  sub.create();
  auto* host = make_host(R"(
    (
      (load-param v0)
      (.src_block "LFoo;.bar:(I)V" 0 (1.0 1.0))
      (if-eqz v0 :rejoin)
      (.src_block "LFoo;.bar:(I)V" 1 (0.0 0.0))
      (new-instance "LBuilderSub;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1) "LBuilderBase;.<init>:()V")
      (sput-object v1 "LFoo;.cold_0:LBuilderBase;")
      (sput v0 "LFoo;.cold_1:I")
      (:rejoin)
      (.src_block "LFoo;.bar:(I)V" 2 (1.0 1.0))
      (sput v0 "LFoo;.rejoin_0:I")
      (return-void)
    )
  )");
  auto mcs = discover(host);
  ASSERT_EQ(mcs->closures.size(), 1u);
  auto* split =
      apply_split(candidate(mcs, mcs->closures.front()), "bar$split$test");
  EXPECT_EQ(count_fields(split, "cold_"), 2u) << show(split->get_code()->cfg());
}

// Two regions emitted one after the other: `b` jumps to `a`, and `a` is a
// region of its own. The split of `a` takes every edge into `a`, `b`'s goto
// included. The split of `b`, built next, must continue at `a`'s call block:
// `a` itself, which discovery recorded as `b`'s continuation, now runs only if
// something jumps to it again.
TEST_F(MethodSplitterRegionBuilderTest,
       ASecondRegionFollowsTheFirstSplitsLaunchpad) {
  auto* host = make_host(R"(
    (
      (load-param v0)
      (.src_block "LFoo;.bar:(I)V" 0 (1.0 1.0))
      (if-eqz v0 :h2)
      (.src_block "LFoo;.bar:(I)V" 1 (0.0 0.0))
      (sput v0 "LFoo;.bodyb_0:I")
      (sput v0 "LFoo;.bodyb_1:I")
      (goto :a)
      (:h2)
      (.src_block "LFoo;.bar:(I)V" 2 (1.0 1.0))
      (if-eqz v0 :rejoin)
      (:a)
      (.src_block "LFoo;.bar:(I)V" 3 (0.0 0.0))
      (sput v0 "LFoo;.bodya_0:I")
      (sput v0 "LFoo;.bodya_1:I")
      (goto :rejoin)
      (:rejoin)
      (.src_block "LFoo;.bar:(I)V" 4 (1.0 1.0))
      (sput v0 "LFoo;.rejoin_0:I")
      (return-void)
    )
  )");
  auto mcs = discover(host);
  ASSERT_EQ(mcs->closures.size(), 2u);
  const auto& region_a = closure_storing(*mcs, "bodya");
  const auto& region_b = closure_storing(*mcs, "bodyb");
  auto* a_block = region_a.target;
  EXPECT_EQ(region_b.region->rejoin_block(), a_block);

  auto sc_a = candidate(mcs, region_a);
  auto* split_a = apply_split(sc_a, "bar$split$test0");
  auto* launchpad_a = launchpad_of(host, split_a);
  ASSERT_NE(launchpad_a, nullptr);
  EXPECT_EQ(msi::live_continuation(region_b), launchpad_a);

  auto sc_b = candidate(mcs, region_b);
  auto* split_b = apply_split(sc_b, "bar$split$test1");
  auto* launchpad_b = launchpad_of(host, split_b);
  ASSERT_NE(launchpad_b, nullptr);
  EXPECT_EQ(launchpad_b->goes_to(), launchpad_a);

  // No path reaches `a` any more, so dropping unreachable blocks leaves
  // neither body in the host.
  host->get_code()->cfg().simplify();
  EXPECT_EQ(count_fields(host, "bodya_"), 0u) << show(host->get_code()->cfg());
  EXPECT_EQ(count_fields(host, "bodyb_"), 0u) << show(host->get_code()->cfg());
  EXPECT_EQ(count_fields(split_a, "bodya_"), 2u);
  EXPECT_EQ(count_fields(split_b, "bodyb_"), 2u);
}
