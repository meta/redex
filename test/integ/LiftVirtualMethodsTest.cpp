/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <algorithm>
#include <limits>
#include <string>

#include <gtest/gtest.h>

#include "ApiLevelChecker.h"
#include "DexStore.h"
#include "FrameworkApi.h"
#include "IRAssembler.h"
#include "JarLoader.h"
#include "LiftVirtualMethods.h"
#include "MethodProfiles.h"
#include "RedexTest.h"
#include "Resolver.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "Walkers.h"

namespace {

bool declares_m(const char* cls) {
  const auto* type = DexType::get_type(cls);
  always_assert(type != nullptr);
  const auto& vmethods = type_class(type)->get_vmethods();
  return std::any_of(vmethods.begin(), vmethods.end(), [](auto* m) {
    return m->get_name()->str() == "m" && show(m->get_proto()) == "(I)I";
  });
}

DexMethod* get_m(const char* cls) {
  return DexMethod::get_method(std::string(cls) + ".m:(I)I")->as_def();
}

bool casts_receiver_to_lift_i(DexMethod* method) {
  auto* lift_i = DexType::get_type("Lcom/facebook/redextest/LiftI;");
  for (const auto& mie : cfg::InstructionIterable(method->get_code()->cfg())) {
    if (mie.insn->opcode() == OPCODE_CHECK_CAST &&
        mie.insn->get_type() == lift_i) {
      return true;
    }
  }
  return false;
}

size_t rejections(const lift_virtual_methods::Stats& stats,
                  lift_virtual_methods::Rejection rejection) {
  return stats.rejections[static_cast<size_t>(rejection)];
}

} // namespace

class LiftVirtualMethodsTest : public RedexIntegrationTest {
 protected:
  void prepare() {
    // Lifting checks every ancestor up to java.lang.Object, so it needs the
    // framework classes a real build loads.
    EXPECT_TRUE(
        load_jar_file(DexLocation::make_location("", android_sdk_jar_path())));
    auto scope = build_class_scope(stores);
    walk::parallel::code(scope, [&](auto*, auto& code) { code.build_cfg(); });
    api::LevelChecker::init(0, scope);
  }

  lift_virtual_methods::Stats run_lift(
      double max_inheritors_per_copy = std::numeric_limits<double>::infinity(),
      bool normal_primary_dex = true) {
    return lift_virtual_methods::lift(stores, m_method_profiles,
                                      normal_primary_dex, &m_min_sdk_api,
                                      max_inheritors_per_copy);
  }

  method_profiles::MethodProfiles m_method_profiles;
  // The forwarders reference no framework class but Object.
  api::AndroidSDK m_min_sdk_api = api::AndroidSDK::from_string(
      "Ljava/lang/Object; 1 Ljava/lang/Object; 0 0");
};

using lift_virtual_methods::Rejection;

TEST_F(LiftVirtualMethodsTest, lift) {
  prepare();
  auto stats = run_lift();

  EXPECT_TRUE(declares_m("Lcom/facebook/redextest/UBase;"));
  EXPECT_FALSE(declares_m("Lcom/facebook/redextest/UA;"));
  EXPECT_FALSE(declares_m("Lcom/facebook/redextest/UB;"));
  EXPECT_FALSE(is_final(get_m("Lcom/facebook/redextest/UBase;")));
  // The forwarders pass `this` as LiftI, which UBase does not implement.
  EXPECT_TRUE(
      casts_receiver_to_lift_i(get_m("Lcom/facebook/redextest/UBase;")));

  EXPECT_TRUE(declares_m("Lcom/facebook/redextest/MBase;"));
  EXPECT_FALSE(declares_m("Lcom/facebook/redextest/MA;"));
  EXPECT_FALSE(declares_m("Lcom/facebook/redextest/MB;"));
  EXPECT_TRUE(declares_m("Lcom/facebook/redextest/MC;"));

  EXPECT_FALSE(declares_m("Lcom/facebook/redextest/ABase;"));
  EXPECT_TRUE(declares_m("Lcom/facebook/redextest/AA;"));
  EXPECT_TRUE(declares_m("Lcom/facebook/redextest/AB;"));
  // ABase, and LA after LBase took its m.
  EXPECT_EQ(rejections(stats, Rejection::kAncestorDeclaresMethod), 2);

  EXPECT_FALSE(declares_m("Lcom/facebook/redextest/SBase;"));
  EXPECT_TRUE(declares_m("Lcom/facebook/redextest/SA;"));
  EXPECT_EQ(rejections(stats, Rejection::kSubtreeConflict), 1);

  EXPECT_TRUE(declares_m("Lcom/facebook/redextest/TBase;"));
  for (const auto* cls :
       {"Lcom/facebook/redextest/TMid;", "Lcom/facebook/redextest/TA;",
        "Lcom/facebook/redextest/TB;", "Lcom/facebook/redextest/TM1;",
        "Lcom/facebook/redextest/TM2;"}) {
    EXPECT_FALSE(declares_m(cls)) << cls;
  }

  EXPECT_FALSE(declares_m("Lcom/facebook/redextest/RBase;"));
  EXPECT_EQ(rejections(stats, Rejection::kInterfaceDeclaresMethod), 1);

  EXPECT_TRUE(declares_m("Lcom/facebook/redextest/EdgeBase;"));
  EXPECT_FALSE(declares_m("Lcom/facebook/redextest/EdgeDeep;"));
  EXPECT_TRUE(declares_m("Lcom/facebook/redextest/EdgeShield;"));
  EXPECT_TRUE(declares_m("Lcom/facebook/redextest/EdgeShieldDeep1;"));
  EXPECT_TRUE(declares_m("Lcom/facebook/redextest/EdgeShieldDeep2;"));
  // EdgeShield declares m, so its subclasses' copies cannot move into it.
  EXPECT_EQ(rejections(stats, Rejection::kTargetHasMethod), 1);

  // UBase, MBase, TBase, EdgeBase and LBase.
  EXPECT_EQ(stats.lifted_methods, 5);
  // UB, MB, TB, TM1 and TM2 (below TMid, which declares no copy), EdgeB and
  // EdgeDeep (below EdgeA's copy), LB.
  EXPECT_EQ(stats.removed_methods, 8);
  EXPECT_EQ(stats.receiver_casts, 5);
  // UBase and UOther, MBase, TBase and TMid, EdgeBase and its four EdgeGap*
  // subclasses, LBase.
  EXPECT_EQ(stats.new_vtable_slots, 11);
}

TEST_F(LiftVirtualMethodsTest, merges_profiles) {
  prepare();
  auto add_source_block = [](const char* cls, float val, float appear100) {
    auto* m = get_m(cls);
    auto* entry = m->get_code()->cfg().entry_block();
    entry->insert_before(
        entry->begin(),
        std::make_unique<SourceBlock>(
            DexString::make_string(show(m)), 0,
            std::vector<SourceBlock::Val>{SourceBlock::Val(val, appear100)}));
  };
  add_source_block("Lcom/facebook/redextest/UA;", 3, 50);
  add_source_block("Lcom/facebook/redextest/UB;", 4, 20);
  auto stats_of = [](double appear_percent, double call_count) {
    method_profiles::Stats stats;
    stats.appear_percent = appear_percent;
    stats.call_count = call_count;
    return stats;
  };
  m_method_profiles = method_profiles::MethodProfiles::initialize(
      "ColdStart",
      {{get_m("Lcom/facebook/redextest/UA;"), stats_of(30, 3)},
       {get_m("Lcom/facebook/redextest/UB;"), stats_of(20, 4)}});

  run_lift();

  auto* lifted = get_m("Lcom/facebook/redextest/UBase;");
  const auto* sb = source_blocks::get_first_source_block_of_method(lifted);
  ASSERT_NE(sb, nullptr);
  EXPECT_EQ(sb->get_val(0), 7);
  EXPECT_EQ(sb->get_appear100(0), 50);
  auto lifted_stats = m_method_profiles.get_method_stat("ColdStart", lifted);
  ASSERT_TRUE(lifted_stats);
  EXPECT_EQ(lifted_stats->appear_percent, 50);
  EXPECT_EQ(lifted_stats->call_count, 7);
}

TEST_F(LiftVirtualMethodsTest, limits_inheritors) {
  prepare();
  // UBase: two new slots (UBase, UOther) for UB's copy. RBase: two (RBase,
  // RIter) for RB's copy. EdgeBase: five for two copies. MBase: one for MB's
  // copy. TBase: two (TBase, TMid) for three copies.
  auto stats = run_lift(/* max_inheritors_per_copy */ 1);
  EXPECT_FALSE(declares_m("Lcom/facebook/redextest/UBase;"));
  EXPECT_TRUE(declares_m("Lcom/facebook/redextest/UA;"));
  EXPECT_FALSE(declares_m("Lcom/facebook/redextest/EdgeBase;"));
  EXPECT_TRUE(declares_m("Lcom/facebook/redextest/MBase;"));
  EXPECT_TRUE(declares_m("Lcom/facebook/redextest/TBase;"));
  EXPECT_EQ(rejections(stats, Rejection::kTooManyInheritors), 3);
  // MBase and LBase.
  EXPECT_EQ(stats.new_vtable_slots, 4);
}

TEST_F(LiftVirtualMethodsTest, counts_target_slot) {
  prepare();
  // Without EdgeDeep's copy, EdgeB's copy pays for five slots: EdgeBase and
  // its four EdgeGap* subclasses.
  get_m("Lcom/facebook/redextest/EdgeDeep;")->rstate.set_no_optimizations();
  run_lift(/* max_inheritors_per_copy */ 4);
  EXPECT_FALSE(declares_m("Lcom/facebook/redextest/EdgeBase;"));
}

TEST_F(LiftVirtualMethodsTest, keeps_copies_that_cannot_change) {
  prepare();
  get_m("Lcom/facebook/redextest/EdgeDeep;")->rstate.set_no_optimizations();
  get_m("Lcom/facebook/redextest/TM1;")->rstate.set_root();
  run_lift();
  EXPECT_TRUE(declares_m("Lcom/facebook/redextest/EdgeBase;"));
  EXPECT_TRUE(declares_m("Lcom/facebook/redextest/EdgeDeep;"));
  EXPECT_TRUE(declares_m("Lcom/facebook/redextest/TBase;"));
  EXPECT_TRUE(declares_m("Lcom/facebook/redextest/TM1;"));
  EXPECT_FALSE(declares_m("Lcom/facebook/redextest/TM2;"));
}

TEST_F(LiftVirtualMethodsTest, clears_final) {
  prepare();
  auto* a = get_m("Lcom/facebook/redextest/UA;");
  set_final(a);
  run_lift();
  EXPECT_EQ(get_m("Lcom/facebook/redextest/UBase;"), a);
  EXPECT_FALSE(is_final(a));
}

TEST_F(LiftVirtualMethodsTest, ignores_interfaces_below_copies) {
  prepare();
  // EdgeInherited already inherits EdgeDeep's m, whatever its interfaces.
  type_class(DexType::get_type("Lcom/facebook/redextest/EdgeInherited;"))
      ->set_interfaces(DexTypeList::make_type_list(
          {DexType::make_type("Lunknown/EdgeInterface;")}));
  run_lift();
  EXPECT_TRUE(declares_m("Lcom/facebook/redextest/EdgeBase;"));
  EXPECT_FALSE(declares_m("Lcom/facebook/redextest/EdgeDeep;"));
}

TEST_F(LiftVirtualMethodsTest, rejects_interface_of_new_inheritor) {
  prepare();
  type_class(DexType::get_type("Lcom/facebook/redextest/EdgeGapLeaf;"))
      ->set_interfaces(DexTypeList::make_type_list(
          {DexType::get_type("Lcom/facebook/redextest/LiftI;")}));
  auto stats = run_lift();
  EXPECT_FALSE(declares_m("Lcom/facebook/redextest/EdgeBase;"));
  // RBase and EdgeBase.
  EXPECT_EQ(rejections(stats, Rejection::kInterfaceDeclaresMethod), 2);
}

TEST_F(LiftVirtualMethodsTest, rejects_unknown_interface_of_new_inheritor) {
  prepare();
  type_class(DexType::get_type("Lcom/facebook/redextest/EdgeGapLeaf;"))
      ->set_interfaces(DexTypeList::make_type_list(
          {DexType::make_type("Lunknown/EdgeInterface;")}));
  auto stats = run_lift();
  EXPECT_FALSE(declares_m("Lcom/facebook/redextest/EdgeBase;"));
  EXPECT_EQ(rejections(stats, Rejection::kInterfaceDeclaresMethod), 2);
}

TEST_F(LiftVirtualMethodsTest, rejects_unknown_ancestor) {
  prepare();
  type_class(DexType::get_type("Lcom/facebook/redextest/EdgeBase;"))
      ->set_super_class(DexType::make_type("Lunknown/EdgeAncestor;"));
  auto stats = run_lift();
  EXPECT_FALSE(declares_m("Lcom/facebook/redextest/EdgeBase;"));
  EXPECT_EQ(rejections(stats, Rejection::kUnknownAncestor), 1);
}

TEST_F(LiftVirtualMethodsTest, rejects_reference_on_target) {
  prepare();
  DexMethod::make_method("Lcom/facebook/redextest/EdgeBase;.m:(I)I");
  auto stats = run_lift();
  EXPECT_FALSE(declares_m("Lcom/facebook/redextest/EdgeBase;"));
  EXPECT_EQ(rejections(stats, Rejection::kTargetHasMethod), 2);
}

TEST_F(LiftVirtualMethodsTest, rejects_unresolved_reference_on_new_inheritor) {
  prepare();
  // Invoking it throws NoSuchMethodError today.
  auto* ref = DexMethod::make_method("Lcom/facebook/redextest/EdgeGap;.m:(I)I");
  auto stats = run_lift();
  EXPECT_FALSE(declares_m("Lcom/facebook/redextest/EdgeBase;"));
  EXPECT_EQ(resolve_method(ref, MethodSearch::Virtual), nullptr);
  EXPECT_EQ(rejections(stats, Rejection::kSubtreeConflict), 2);
}

TEST_F(LiftVirtualMethodsTest, rejects_source_block_mismatch) {
  prepare();
  auto* deep = get_m("Lcom/facebook/redextest/EdgeDeep;");
  auto* entry = deep->get_code()->cfg().entry_block();
  entry->insert_before(
      entry->begin(),
      std::make_unique<SourceBlock>(
          DexString::make_string(show(deep)), 0,
          std::vector<SourceBlock::Val>{SourceBlock::Val(1, 1)}));
  auto stats = run_lift();
  EXPECT_FALSE(declares_m("Lcom/facebook/redextest/EdgeBase;"));
  EXPECT_EQ(rejections(stats, Rejection::kSourceBlockMismatch), 1);
}

namespace {

IRInstruction* find_invoke(DexMethod* method) {
  for (const auto& mie : cfg::InstructionIterable(method->get_code()->cfg())) {
    if (mie.insn->opcode() == OPCODE_INVOKE_VIRTUAL) {
      return mie.insn;
    }
  }
  return nullptr;
}

} // namespace

TEST_F(LiftVirtualMethodsTest, keeps_rewritten_calls_accessible) {
  prepare();
  // A caller in another package can call m through the public EdgeB.
  auto* caller_type = DexType::get_type("Lcom/facebook/redextest/EdgeCaller;");
  caller_type->set_name(DexString::make_string("Lother/EdgeCaller;"));
  set_public(type_class(DexType::get_type("Lcom/facebook/redextest/EdgeB;")));
  auto* call = find_invoke(
      DexMethod::get_method("Lother/EdgeCaller;.call:(Lcom/facebook/redextest/"
                            "EdgeB;I)I")
          ->as_def());
  ASSERT_NE(call, nullptr);
  run_lift();
  EXPECT_EQ(call->get_method(), get_m("Lcom/facebook/redextest/EdgeBase;"));
  EXPECT_TRUE(is_public(type_class(call->get_method()->get_class())));
}

TEST_F(LiftVirtualMethodsTest, keeps_receiver_cast_accessible) {
  prepare();
  // A public superclass in another package; LiftI is package-private.
  auto* base = DexType::get_type("Lcom/facebook/redextest/EdgeBase;");
  set_public(type_class(base));
  base->set_name(DexString::make_string("Lother/EdgeBase;"));
  auto* a = get_m("Lcom/facebook/redextest/EdgeA;");
  run_lift();
  ASSERT_EQ(a->get_class(), base);
  EXPECT_TRUE(casts_receiver_to_lift_i(a));
  EXPECT_TRUE(is_public(
      type_class(DexType::get_type("Lcom/facebook/redextest/LiftI;"))));
}

namespace {

// Moves `names` from the root store into a new module store.
void move_to_module_store(DexStoresVector& stores,
                          const std::vector<const char*>& names) {
  auto& root_classes = stores.at(0).get_dexen().at(0);
  std::vector<DexClass*> moved;
  for (const auto* name : names) {
    auto* cls = type_class(DexType::get_type(name));
    always_assert(cls != nullptr);
    moved.push_back(cls);
    root_classes.erase(
        std::find(root_classes.begin(), root_classes.end(), cls));
  }
  DexMetadata metadata;
  metadata.set_id("LiftModule");
  DexStore module(metadata);
  module.add_classes(moved);
  stores.emplace_back(module);
}

} // namespace

constexpr std::initializer_list<const char*> kUSubclassesAndCallees = {
    "Lcom/facebook/redextest/UA;", "Lcom/facebook/redextest/UB;",
    "Lcom/facebook/redextest/UOther;", "Lcom/facebook/redextest/LiftI;",
    "Lcom/facebook/redextest/LiftI_CC;"};

// UBase stays in the root store, while its subclasses and the types the
// forwarders reference live in a module that depends on it.
TEST_F(LiftVirtualMethodsTest, rejects_references_illegal_in_target_store) {
  prepare();
  move_to_module_store(stores, kUSubclassesAndCallees);
  auto stats = run_lift();
  EXPECT_FALSE(declares_m("Lcom/facebook/redextest/UBase;"));
  // Every forwarder group that the other checks admit calls LiftI_CC.
  EXPECT_GT(rejections(stats, Rejection::kCrossStore), 0);
  EXPECT_EQ(stats.lifted_methods, 0);
}

// UBase in the primary dex, its subclasses and the forwarders' callees in a
// secondary dex, in an app whose primary dex may not reference secondary ones.
TEST_F(LiftVirtualMethodsTest, rejects_references_illegal_in_primary_dex) {
  prepare();
  auto& dexen = stores.at(0).get_dexen();
  DexClasses secondary;
  for (const auto* name : kUSubclassesAndCallees) {
    auto* cls = type_class(DexType::get_type(name));
    dexen.at(0).erase(std::find(dexen.at(0).begin(), dexen.at(0).end(), cls));
    secondary.push_back(cls);
  }
  dexen.push_back(secondary);
  auto stats = run_lift(std::numeric_limits<double>::infinity(),
                        /* normal_primary_dex */ false);
  EXPECT_FALSE(declares_m("Lcom/facebook/redextest/UBase;"));
  // Every forwarder group that the other checks admit calls LiftI_CC.
  EXPECT_GT(rejections(stats, Rejection::kCrossStore), 0);
  EXPECT_EQ(stats.lifted_methods, 0);
}

// `MethodHandle.invoke(this)` in Java: the call site's prototype, which the
// instruction does not carry, decides what type the receiver must have.
TEST_F(LiftVirtualMethodsTest, rejects_receiver_passed_to_invoke_polymorphic) {
  prepare();
  for (const auto* cls :
       {"Lcom/facebook/redextest/UA;", "Lcom/facebook/redextest/UB;"}) {
    auto* m = get_m(cls);
    m->set_code(assembler::ircode_from_string(R"(
      (
        (load-param-object v0)
        (load-param v1)
        (const v2 0)
        (invoke-polymorphic (v2 v0) "Ljava/lang/invoke/MethodHandle;.invoke:([Ljava/lang/Object;)Ljava/lang/Object;")
        (return v1)
      )
    )"));
    m->get_code()->build_cfg();
  }
  auto stats = run_lift();
  EXPECT_FALSE(declares_m("Lcom/facebook/redextest/UBase;"));
  EXPECT_EQ(rejections(stats, Rejection::kReceiverType), 1);
}

// After LBase takes LA's m, the group of LA's subclasses targets LA, which no
// longer declares m but now inherits LBase's.
TEST_F(LiftVirtualMethodsTest,
       rejects_target_that_lost_method_to_earlier_lift) {
  prepare();
  auto* call = find_invoke(
      DexMethod::get_method("Lcom/facebook/redextest/LCaller;.call:(Lcom/"
                            "facebook/redextest/LA;I)I")
          ->as_def());
  ASSERT_NE(call, nullptr);
  auto* la_m = get_m("Lcom/facebook/redextest/LA;");
  auto stats = run_lift();
  EXPECT_TRUE(declares_m("Lcom/facebook/redextest/LBase;"));
  EXPECT_FALSE(declares_m("Lcom/facebook/redextest/LA;"));
  EXPECT_FALSE(declares_m("Lcom/facebook/redextest/LB;"));
  EXPECT_TRUE(declares_m("Lcom/facebook/redextest/LP;"));
  EXPECT_TRUE(declares_m("Lcom/facebook/redextest/LQ;"));
  EXPECT_EQ(la_m->get_class(),
            DexType::get_type("Lcom/facebook/redextest/LBase;"));
  EXPECT_EQ(call->get_method(), la_m);
  EXPECT_EQ(rejections(stats, Rejection::kAncestorDeclaresMethod), 2);
}

// A pass that asked for one method's exit block leaves it cached on that
// method only.
TEST_F(LiftVirtualMethodsTest, ignores_exit_block_cached_on_representative) {
  prepare();
  get_m("Lcom/facebook/redextest/UA;")
      ->get_code()
      ->cfg()
      .calculate_exit_block();
  run_lift();
  EXPECT_TRUE(declares_m("Lcom/facebook/redextest/UBase;"));
  EXPECT_FALSE(declares_m("Lcom/facebook/redextest/UB;"));
}

TEST_F(LiftVirtualMethodsTest, ignores_exit_block_cached_on_copy) {
  prepare();
  get_m("Lcom/facebook/redextest/UB;")
      ->get_code()
      ->cfg()
      .calculate_exit_block();
  run_lift();
  EXPECT_TRUE(declares_m("Lcom/facebook/redextest/UBase;"));
  EXPECT_FALSE(declares_m("Lcom/facebook/redextest/UB;"));
}

// Unreachable code carries no profile and never runs.
TEST_F(LiftVirtualMethodsTest, lifts_copies_with_unreachable_code) {
  prepare();
  for (const auto* cls :
       {"Lcom/facebook/redextest/UA;", "Lcom/facebook/redextest/UB;"}) {
    auto& cfg = get_m(cls)->get_code()->cfg();
    auto* unreachable = cfg.create_block();
    unreachable->push_back(
        (new IRInstruction(OPCODE_CONST))->set_dest(0)->set_literal(1));
    unreachable->push_back((new IRInstruction(OPCODE_RETURN))->set_src(0, 0));
  }
  run_lift();
  EXPECT_TRUE(declares_m("Lcom/facebook/redextest/UBase;"));
  EXPECT_FALSE(declares_m("Lcom/facebook/redextest/UB;"));
}
