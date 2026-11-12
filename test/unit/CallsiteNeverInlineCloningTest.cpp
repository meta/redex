/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <memory>
#include <sstream>

#include <gtest/gtest.h>

#include "CallsiteNeverInlineCloningPass.h"

#include "BaselineProfile.h"
#include "Creators.h"
#include "DexAccess.h"
#include "DexClass.h"
#include "IRAssembler.h"
#include "MethodProfiles.h"
#include "RedexTest.h"
#include "Show.h"
#include "SourceBlocks.h"

namespace {

class CallsiteNeverInlineCloningTest : public RedexTest {
 public:
  // Creates a class named "LFoo;" with one method per (name, sig, code)
  // triple, and returns the class together with the methods in the same
  // order. Every method's CFG is built, matching what `run_pass` always sees
  // from `PassManager`. The class name is fixed (not counter-suffixed): each
  // TEST_F gets its own fresh RedexContext (RedexTest's SetUp), so there is
  // no cross-test collision, and a fixed name lets every test body reference
  // "LFoo;.<method>:<sig>" directly in its S-expression invoke targets.
  DexClass* create_class(
      std::vector<std::tuple<std::string, std::string, std::string>> methods,
      std::vector<DexMethod**> out,
      bool make_virtual = false) {
    const std::string name = "LFoo;";
    ClassCreator cc{DexType::make_type(name)};
    cc.set_super(type::java_lang_Object());
    for (size_t i = 0; i < methods.size(); i++) {
      const auto& [method_name, sig, code_str] = methods[i];
      bool is_virtual = make_virtual && i == 0;
      auto access =
          is_virtual ? (ACC_PUBLIC | ACC_FINAL) : (ACC_PUBLIC | ACC_STATIC);
      auto* m = DexMethod::make_method(name + "." + method_name + ":" + sig)
                    ->make_concrete(access,
                                    assembler::ircode_from_string(code_str),
                                    is_virtual);
      m->set_deobfuscated_name(show(m));
      m->get_code()->build_cfg();
      cc.add_method(m);
      *out[i] = m;
    }
    return cc.create();
  }

  // A permissive base config for tests that exercise this pass's mechanics
  // (clone shape, opcode preservation, catch handling, blocklist,
  // no_optimizations, ...) rather than the profitability model itself: zero
  // method-ref cost means any callee with >=2 cold call sites nets positive
  // regardless of its size, so these tests do not need to hand-tune a
  // callee's estimated code units against `Config`'s real-world defaults.
  // `hot_block_appear_threshold`/`hot_method_appear_threshold` are set
  // explicitly to 80/20 (mirroring instagram.refig.inc/fb4a.refig.inc's own
  // settings), since `Config`'s bare defaults are -1/-1 (disabled, matching
  // ArtProfileWriterPass's own global default) and these tests need the
  // hot/cold SourceBlock distinction to actually work.
  // `CostModel*`-named tests below use `Config{}` (real defaults) or their
  // own explicit overrides instead, specifically to exercise the model.
  static CallsiteNeverInlineCloningPass::Config test_config() {
    CallsiteNeverInlineCloningPass::Config config;
    config.hot_block_appear_threshold = 80.0f;
    config.hot_method_appear_threshold = 20.0f;
    config.min_hot_callsites = 1;
    config.min_cold_callsites = 1;
    config.min_estimated_oat_code_units_saved = 0;
    config.method_ref_cost = 0;
    return config;
  }

  static CallsiteNeverInlineCloningPass::Config default_config() {
    return CallsiteNeverInlineCloningPass::Config{};
  }

  // The profitability-model tests below want the REAL cost-model defaults
  // (min_cold_callsites, method_ref_cost, the caps, ...) exercised
  // faithfully, but still need a working hot/cold distinction -- so this
  // starts from `default_config()` and adds only the two thresholds
  // instagram.refig.inc/fb4a.refig.inc actually configure.
  static CallsiteNeverInlineCloningPass::Config profitability_config() {
    auto config = default_config();
    config.hot_block_appear_threshold = 80.0f;
    config.hot_method_appear_threshold = 20.0f;
    return config;
  }

  // Marks every given method as AOT-"compiled" (baseline-profile hot) --
  // this pass only ever inspects call sites inside such a caller, and only
  // ever considers a callee "possibly hot" if the callee itself is marked
  // this way too.
  static baseline_profiles::BaselineProfile compiled(
      const std::vector<DexMethod*>& methods) {
    baseline_profiles::BaselineProfile bp;
    for (auto* m : methods) {
      bp.methods[m] = baseline_profiles::MethodFlags{.hot = true};
    }
    return bp;
  }

  static method_profiles::MethodProfiles empty_method_profiles() {
    return method_profiles::MethodProfiles();
  }

 protected:
  static std::atomic<size_t> s_counter;
};
std::atomic<size_t> CallsiteNeverInlineCloningTest::s_counter{0};

DexMethod* find_invoked_method(DexMethod* caller) {
  for (auto& mie : InstructionIterable(caller->get_code()->cfg())) {
    auto* insn = mie.insn;
    if (opcode::is_an_invoke(insn->opcode())) {
      return insn->get_method()->as_def();
    }
  }
  return nullptr;
}

IROpcode find_invoke_opcode(DexMethod* caller) {
  for (auto& mie : InstructionIterable(caller->get_code()->cfg())) {
    auto* insn = mie.insn;
    if (opcode::is_an_invoke(insn->opcode())) {
      return insn->opcode();
    }
  }
  return OPCODE_NOP;
}

bool class_has_method(DexClass* cls, DexMethod* method) {
  for (auto* m : cls->get_all_methods()) {
    if (m == method) {
      return true;
    }
  }
  return false;
}

} // namespace

TEST_F(CallsiteNeverInlineCloningTest, MixedHotnessClonesAndRedirects) {
  DexMethod *callee, *hot_caller, *cold_caller, *cold_caller2;
  auto* cls = create_class(
      {
          {"callee", "()V",
           R"((
                (.src_block "LFoo;.callee:()V" 0 (0.7 60))
                (const v0 1)
                (const v1 2)
                (add-int v0 v0 v1)
                (add-int v0 v0 v1)
                (return-void)
              ))"},
          {"hot_caller", "()V",
           R"((
                (.src_block "LFoo;.hot_caller:()V" 0 (1.0 100))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
          {"cold_caller", "()V",
           R"((
                (.src_block "LFoo;.cold_caller:()V" 0 (0 0))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
          {"cold_caller2", "()V",
           R"((
                (.src_block "LFoo;.cold_caller2:()V" 0 (0 0))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
      },
      {&callee, &hot_caller, &cold_caller, &cold_caller2});

  Scope scope{cls};
  auto baseline_profile =
      compiled({callee, hot_caller, cold_caller, cold_caller2});
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, test_config(), /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_EQ(stats.mixed_hotness_callees, 1u);
  EXPECT_EQ(stats.clones_created, 1u);
  EXPECT_EQ(stats.cold_callsites_redirected, 2u);

  // The hot caller keeps calling the original, with its opcode unchanged.
  EXPECT_EQ(find_invoked_method(hot_caller), callee);
  EXPECT_EQ(find_invoke_opcode(hot_caller), OPCODE_INVOKE_STATIC);

  // Both cold callers now call a clone, not the original -- same opcode,
  // only the method operand changed.
  auto* clone = find_invoked_method(cold_caller);
  ASSERT_NE(clone, nullptr);
  EXPECT_NE(clone, callee);
  EXPECT_EQ(clone->get_class(), callee->get_class());
  EXPECT_EQ(find_invoke_opcode(cold_caller), OPCODE_INVOKE_STATIC);
  EXPECT_EQ(find_invoked_method(cold_caller2), clone);

  // The clone keeps the original's access flags (here: static) verbatim.
  EXPECT_TRUE(is_static(clone));
  EXPECT_EQ(clone->get_access() & (ACC_PUBLIC | ACC_STATIC),
            callee->get_access() & (ACC_PUBLIC | ACC_STATIC));

  // The clone is never-inline-by-Redex and generated, carries its own built
  // CFG (the pass CFG-built invariant), and is a real member of its class.
  EXPECT_TRUE(clone->rstate.dont_inline());
  EXPECT_TRUE(clone->rstate.is_generated());
  EXPECT_TRUE(clone->rstate.force_hot_in_baseline_profile());
  EXPECT_FALSE(clone->rstate.force_startup_in_baseline_profile());
  EXPECT_TRUE(clone->get_code()->cfg_built());
  EXPECT_TRUE(class_has_method(cls, clone));

  // The clone's own SourceBlock values are zeroed.
  auto* clone_sb = source_blocks::get_first_source_block(
      clone->get_code()->cfg().entry_block());
  ASSERT_NE(clone_sb, nullptr);
  clone_sb->foreach_val([](auto& val) {
    EXPECT_TRUE(static_cast<bool>(val));
    EXPECT_FLOAT_EQ(val->val, 0.0f);
    EXPECT_FLOAT_EQ(val->appear100, 0.0f);
  });

  // The original callee's own body/SourceBlock is untouched.
  auto* orig_sb = source_blocks::get_first_source_block(
      callee->get_code()->cfg().entry_block());
  ASSERT_NE(orig_sb, nullptr);
  orig_sb->foreach_val([](auto& val) { EXPECT_FLOAT_EQ(val->val, 0.7f); });
}

TEST_F(CallsiteNeverInlineCloningTest, MultipleColdCallsitesAllRedirected) {
  // Two distinct cold callers, plus one hot caller: both cold call sites must
  // be redirected to the very same clone.
  DexMethod *callee, *hot_caller, *cold_caller1, *cold_caller2;
  auto* cls = create_class(
      {
          {"callee", "()V",
           R"((
                (.src_block "LFoo;.callee:()V" 0 (0.7 60))
                (const v0 1)
                (const v1 2)
                (add-int v0 v0 v1)
                (add-int v0 v0 v1)
                (return-void)
              ))"},
          {"hot_caller", "()V",
           R"((
                (.src_block "LFoo;.hot_caller:()V" 0 (1.0 100))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
          {"cold_caller1", "()V",
           R"((
                (.src_block "LFoo;.cold_caller1:()V" 0 (0 0))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
          {"cold_caller2", "()V",
           R"((
                (.src_block "LFoo;.cold_caller2:()V" 0 (0 0))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
      },
      {&callee, &hot_caller, &cold_caller1, &cold_caller2});

  Scope scope{cls};
  auto baseline_profile =
      compiled({callee, hot_caller, cold_caller1, cold_caller2});
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, test_config(), /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_EQ(stats.mixed_hotness_callees, 1u);
  EXPECT_EQ(stats.clones_created, 1u);
  EXPECT_EQ(stats.cold_callsites_redirected, 2u);

  auto* clone1 = find_invoked_method(cold_caller1);
  auto* clone2 = find_invoked_method(cold_caller2);
  ASSERT_NE(clone1, nullptr);
  EXPECT_EQ(clone1, clone2);
  EXPECT_EQ(find_invoked_method(hot_caller), callee);
}

TEST_F(CallsiteNeverInlineCloningTest, AllColdCalleeIsNotCloned) {
  // Every call site is cold: nothing to split away from, so this pass leaves
  // it for a later ArtProfileWriterPass to annotate directly.
  DexMethod *callee, *cold_caller;
  auto* cls = create_class(
      {
          {"callee", "()V",
           R"((
                (.src_block "LFoo;.callee:()V" 0 (0 0))
                (return-void)
              ))"},
          {"cold_caller", "()V",
           R"((
                (.src_block "LFoo;.cold_caller:()V" 0 (0 0))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
      },
      {&callee, &cold_caller});

  Scope scope{cls};
  auto baseline_profile = compiled({callee, cold_caller});
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, test_config(), /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_EQ(stats.mixed_hotness_callees, 0u);
  EXPECT_EQ(stats.clones_created, 0u);
  EXPECT_EQ(stats.callees_all_cold_no_clone_needed, 1u);
  EXPECT_EQ(find_invoked_method(cold_caller), callee);
}

TEST_F(CallsiteNeverInlineCloningTest, UncompiledCallerContributesNoEdges) {
  // Neither caller is marked "compiled" in the baseline profile: this pass
  // only ever inspects call sites inside a compiled caller, so nothing is
  // classified at all (not even as "all cold") and nothing is cloned.
  DexMethod *callee, *hot_caller, *cold_caller;
  auto* cls = create_class(
      {
          {"callee", "()V",
           R"((
                (.src_block "LFoo;.callee:()V" 0 (0.7 60))
                (return-void)
              ))"},
          {"hot_caller", "()V",
           R"((
                (.src_block "LFoo;.hot_caller:()V" 0 (1.0 100))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
          {"cold_caller", "()V",
           R"((
                (.src_block "LFoo;.cold_caller:()V" 0 (0 0))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
      },
      {&callee, &hot_caller, &cold_caller});

  Scope scope{cls};
  baseline_profiles::BaselineProfile empty_baseline_profile;
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, test_config(), /* iteration */ 0, empty_baseline_profile,
      empty_method_profiles());

  EXPECT_EQ(stats.callers_not_compiled, 3u);
  EXPECT_EQ(stats.mixed_hotness_callees, 0u);
  EXPECT_EQ(stats.clones_created, 0u);
  EXPECT_EQ(find_invoked_method(cold_caller), callee);
  EXPECT_EQ(find_invoked_method(hot_caller), callee);
}

TEST_F(CallsiteNeverInlineCloningTest, MissingSourceBlockIsConservativelyHot) {
  // The callee's own body carries a SourceBlock (needed for the eligibility
  // scan), but the CALL SITE's containing block has none at all. Missing
  // profiling data reads as "maybe hot" (source_blocks::maybe_hot's own
  // documented conservative default), so this call site is never treated as
  // cold, and this callee is never a cloning candidate.
  DexMethod *callee, *caller;
  auto* cls = create_class(
      {
          {"callee", "()V",
           R"((
                (.src_block "LFoo;.callee:()V" 0 (0.7 60))
                (return-void)
              ))"},
          {"caller", "()V",
           R"((
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
      },
      {&callee, &caller});

  Scope scope{cls};
  auto baseline_profile = compiled({callee, caller});
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, test_config(), /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_EQ(stats.mixed_hotness_callees, 0u);
  EXPECT_EQ(stats.clones_created, 0u);
  EXPECT_EQ(find_invoked_method(caller), callee);
}

TEST_F(CallsiteNeverInlineCloningTest, NonFinalNonTrueVirtualCalleeIsCloned) {
  // A non-final virtual method that no other method anywhere in `scope`
  // overrides (or is overridden by) is a "non-true-virtual" per Redex's own
  // method-override graph -- the same exact-dispatch notion
  // MethodInliner/HotColdMethodSpecializingPass/CallGraph rely on for their
  // own devirtualization decisions. This pass accepts it too, even though
  // it is not declared `final`.
  DexMethod *callee, *hot_caller, *cold_caller;
  size_t c = s_counter.fetch_add(1);
  std::string name = std::string("LBar") + std::to_string(c) + ";";
  ClassCreator cc{DexType::make_type(name)};
  cc.set_super(type::java_lang_Object());
  callee = DexMethod::make_method(name + ".callee:()V")
               ->make_concrete(
                   ACC_PUBLIC,
                   assembler::ircode_from_string(("(\n"
                                                  "  (.src_block \"" +
                                                  name +
                                                  ".callee:()V\" 0 (0.7 60))\n"
                                                  "  (const v0 1)\n"
                                                  "  (const v1 2)\n"
                                                  "  (add-int v0 v0 v1)\n"
                                                  "  (add-int v0 v0 v1)\n"
                                                  "  (return-void)\n"
                                                  ")")),
                   /* is_virtual */ true);
  callee->set_deobfuscated_name(show(callee));
  callee->get_code()->build_cfg();
  cc.add_method(callee);
  hot_caller = DexMethod::make_method(name + ".hot_caller:(" + name + ")V")
                   ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                                   assembler::ircode_from_string(
                                       ("(\n"
                                        "  (load-param-object v0)\n"
                                        "  (.src_block \"" +
                                        name + ".hot_caller:(" + name +
                                        ")V\" 0 (1.0 100))\n"
                                        "  (invoke-virtual (v0) \"" +
                                        name +
                                        ".callee:()V\")\n"
                                        "  (return-void)\n"
                                        ")")),
                                   false);
  hot_caller->set_deobfuscated_name(show(hot_caller));
  hot_caller->get_code()->build_cfg();
  cc.add_method(hot_caller);
  cold_caller = DexMethod::make_method(name + ".cold_caller:(" + name + ")V")
                    ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                                    assembler::ircode_from_string(
                                        ("(\n"
                                         "  (load-param-object v0)\n"
                                         "  (.src_block \"" +
                                         name + ".cold_caller:(" + name +
                                         ")V\" 0 (0 0))\n"
                                         "  (invoke-virtual (v0) \"" +
                                         name +
                                         ".callee:()V\")\n"
                                         "  (return-void)\n"
                                         ")")),
                                    false);
  cold_caller->set_deobfuscated_name(show(cold_caller));
  cold_caller->get_code()->build_cfg();
  cc.add_method(cold_caller);
  auto* cold_caller2 =
      DexMethod::make_method(name + ".cold_caller2:(" + name + ")V")
          ->make_concrete(
              ACC_PUBLIC | ACC_STATIC,
              assembler::ircode_from_string(("(\n"
                                             "  (load-param-object v0)\n"
                                             "  (.src_block \"" +
                                             name + ".cold_caller2:(" + name +
                                             ")V\" 0 (0 0))\n"
                                             "  (invoke-virtual (v0) \"" +
                                             name +
                                             ".callee:()V\")\n"
                                             "  (return-void)\n"
                                             ")")),
              false);
  cold_caller2->set_deobfuscated_name(show(cold_caller2));
  cold_caller2->get_code()->build_cfg();
  cc.add_method(cold_caller2);
  auto* cls = cc.create();

  Scope scope{cls};
  auto baseline_profile =
      compiled({callee, hot_caller, cold_caller, cold_caller2});
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, test_config(), /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_EQ(stats.mixed_hotness_callees, 1u);
  EXPECT_EQ(stats.clones_created, 1u);
  EXPECT_EQ(stats.invokes_ambiguous_virtual_callee, 0u);
  EXPECT_EQ(find_invoked_method(hot_caller), callee);
  auto* clone = find_invoked_method(cold_caller);
  ASSERT_NE(clone, nullptr);
  EXPECT_NE(clone, callee);
  EXPECT_EQ(find_invoked_method(cold_caller2), clone);
  EXPECT_TRUE(clone->is_virtual());
}

TEST_F(CallsiteNeverInlineCloningTest, TrueVirtualOverriddenCalleeIsNotCloned) {
  // A virtual method that a subclass in `scope` DOES override is a genuine
  // true-virtual: a call through it is not exact (a differently-typed
  // receiver could reach the override instead), so this pass (no
  // receiver-type inference) leaves it untouched even though the call sites
  // on the base-typed receiver are mixed hot/cold.
  size_t c = s_counter.fetch_add(1);
  std::string base_name = std::string("LTvBase") + std::to_string(c) + ";";
  std::string sub_name = std::string("LTvSub") + std::to_string(c) + ";";

  ClassCreator base_cc{DexType::make_type(base_name)};
  base_cc.set_super(type::java_lang_Object());
  auto* callee = DexMethod::make_method(base_name + ".callee:()V")
                     ->make_concrete(ACC_PUBLIC,
                                     assembler::ircode_from_string(
                                         ("(\n"
                                          "  (.src_block \"" +
                                          base_name +
                                          ".callee:()V\" 0 (0.7 60))\n"
                                          "  (const v0 1)\n"
                                          "  (const v1 2)\n"
                                          "  (add-int v0 v0 v1)\n"
                                          "  (add-int v0 v0 v1)\n"
                                          "  (return-void)\n"
                                          ")")),
                                     /* is_virtual */ true);
  callee->set_deobfuscated_name(show(callee));
  callee->get_code()->build_cfg();
  base_cc.add_method(callee);
  auto* hot_caller =
      DexMethod::make_method(base_name + ".hot_caller:(" + base_name + ")V")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                          assembler::ircode_from_string(
                              ("(\n"
                               "  (load-param-object v0)\n"
                               "  (.src_block \"" +
                               base_name + ".hot_caller:(" + base_name +
                               ")V\" 0 (1.0 100))\n"
                               "  (invoke-virtual (v0) \"" +
                               base_name +
                               ".callee:()V\")\n"
                               "  (return-void)\n"
                               ")")),
                          false);
  hot_caller->set_deobfuscated_name(show(hot_caller));
  hot_caller->get_code()->build_cfg();
  base_cc.add_method(hot_caller);
  auto* cold_caller =
      DexMethod::make_method(base_name + ".cold_caller:(" + base_name + ")V")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                          assembler::ircode_from_string(
                              ("(\n"
                               "  (load-param-object v0)\n"
                               "  (.src_block \"" +
                               base_name + ".cold_caller:(" + base_name +
                               ")V\" 0 (0 0))\n"
                               "  (invoke-virtual (v0) \"" +
                               base_name +
                               ".callee:()V\")\n"
                               "  (return-void)\n"
                               ")")),
                          false);
  cold_caller->set_deobfuscated_name(show(cold_caller));
  cold_caller->get_code()->build_cfg();
  base_cc.add_method(cold_caller);
  auto* base_cls = base_cc.create();

  ClassCreator sub_cc{DexType::make_type(sub_name)};
  sub_cc.set_super(DexType::make_type(base_name));
  auto* override_method = DexMethod::make_method(sub_name + ".callee:()V")
                              ->make_concrete(ACC_PUBLIC,
                                              assembler::ircode_from_string(R"((
                                (return-void)
                              ))"),
                                              /* is_virtual */ true);
  override_method->set_deobfuscated_name(show(override_method));
  override_method->get_code()->build_cfg();
  sub_cc.add_method(override_method);
  auto* sub_cls = sub_cc.create();

  Scope scope{base_cls, sub_cls};
  auto baseline_profile = compiled({callee, hot_caller, cold_caller});
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, test_config(), /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_EQ(stats.mixed_hotness_callees, 0u);
  EXPECT_EQ(stats.clones_created, 0u);
  EXPECT_GE(stats.invokes_ambiguous_virtual_callee, 1u);
  EXPECT_EQ(find_invoked_method(cold_caller), callee);
}

TEST_F(CallsiteNeverInlineCloningTest,
       CrossClassFinalVirtualCloneStaysVirtualAndAccessible) {
  // `callee` is a PUBLIC FINAL virtual method (exact dispatch: it cannot be
  // overridden). Its callers live in a DIFFERENT class. The clone must keep
  // the exact same access flags (public, final, virtual) as the original --
  // demoting it to private (and its call sites to invoke-direct) would make
  // it inaccessible to these cross-class callers.
  size_t c = s_counter.fetch_add(1);
  std::string callee_cls_name =
      std::string("LCallee") + std::to_string(c) + ";";
  ClassCreator callee_cc{DexType::make_type(callee_cls_name)};
  callee_cc.set_super(type::java_lang_Object());
  auto* callee = DexMethod::make_method(callee_cls_name + ".callee:()V")
                     ->make_concrete(ACC_PUBLIC | ACC_FINAL,
                                     assembler::ircode_from_string(
                                         ("(\n"
                                          "  (.src_block \"" +
                                          callee_cls_name +
                                          ".callee:()V\" 0 (0.7 60))\n"
                                          "  (const v1 1)\n"
                                          "  (const v2 2)\n"
                                          "  (add-int v1 v1 v2)\n"
                                          "  (add-int v1 v1 v2)\n"
                                          "  (return-void)\n"
                                          ")")),
                                     /* is_virtual */ true);
  callee->set_deobfuscated_name(show(callee));
  callee->get_code()->build_cfg();
  callee_cc.add_method(callee);
  auto* callee_cls = callee_cc.create();

  std::string caller_cls_name =
      std::string("LCaller") + std::to_string(c) + ";";
  ClassCreator caller_cc{DexType::make_type(caller_cls_name)};
  caller_cc.set_super(type::java_lang_Object());
  auto* hot_caller =
      DexMethod::make_method(caller_cls_name + ".hot_caller:(" +
                             callee_cls_name + ")V")
          ->make_concrete(
              ACC_PUBLIC | ACC_STATIC,
              assembler::ircode_from_string(("(\n"
                                             "  (load-param-object v0)\n"
                                             "  (.src_block \"" +
                                             caller_cls_name + ".hot_caller:(" +
                                             callee_cls_name +
                                             ")V\" 0 (1.0 100))\n"
                                             "  (invoke-virtual (v0) \"" +
                                             callee_cls_name +
                                             ".callee:()V\")\n"
                                             "  (return-void)\n"
                                             ")")),
              false);
  hot_caller->set_deobfuscated_name(show(hot_caller));
  hot_caller->get_code()->build_cfg();
  caller_cc.add_method(hot_caller);
  auto* cold_caller =
      DexMethod::make_method(caller_cls_name + ".cold_caller:(" +
                             callee_cls_name + ")V")
          ->make_concrete(
              ACC_PUBLIC | ACC_STATIC,
              assembler::ircode_from_string(
                  ("(\n"
                   "  (load-param-object v0)\n"
                   "  (.src_block \"" +
                   caller_cls_name + ".cold_caller:(" + callee_cls_name +
                   ")V\" 0 (0 0))\n"
                   "  (invoke-virtual (v0) \"" +
                   callee_cls_name +
                   ".callee:()V\")\n"
                   "  (return-void)\n"
                   ")")),
              false);
  cold_caller->set_deobfuscated_name(show(cold_caller));
  cold_caller->get_code()->build_cfg();
  caller_cc.add_method(cold_caller);
  auto* cold_caller2 =
      DexMethod::make_method(caller_cls_name + ".cold_caller2:(" +
                             callee_cls_name + ")V")
          ->make_concrete(
              ACC_PUBLIC | ACC_STATIC,
              assembler::ircode_from_string(
                  ("(\n"
                   "  (load-param-object v0)\n"
                   "  (.src_block \"" +
                   caller_cls_name + ".cold_caller2:(" + callee_cls_name +
                   ")V\" 0 (0 0))\n"
                   "  (invoke-virtual (v0) \"" +
                   callee_cls_name +
                   ".callee:()V\")\n"
                   "  (return-void)\n"
                   ")")),
              false);
  cold_caller2->set_deobfuscated_name(show(cold_caller2));
  cold_caller2->get_code()->build_cfg();
  caller_cc.add_method(cold_caller2);
  auto* caller_cls = caller_cc.create();

  Scope scope{callee_cls, caller_cls};
  auto baseline_profile =
      compiled({callee, hot_caller, cold_caller, cold_caller2});
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, test_config(), /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_EQ(stats.mixed_hotness_callees, 1u);
  EXPECT_EQ(stats.clones_created, 1u);
  EXPECT_EQ(find_invoked_method(hot_caller), callee);
  EXPECT_EQ(find_invoke_opcode(hot_caller), OPCODE_INVOKE_VIRTUAL);

  auto* clone = find_invoked_method(cold_caller);
  ASSERT_NE(clone, nullptr);
  EXPECT_NE(clone, callee);
  EXPECT_EQ(find_invoked_method(cold_caller2), clone);
  // Not demoted: still virtual, still public, still final, so a cross-class
  // caller can still reach it via an unchanged invoke-virtual.
  EXPECT_TRUE(clone->is_virtual());
  EXPECT_TRUE(is_public(clone));
  EXPECT_TRUE(is_final(clone));
  EXPECT_FALSE(is_private(clone));
  EXPECT_EQ(find_invoke_opcode(cold_caller), OPCODE_INVOKE_VIRTUAL);
  EXPECT_TRUE(class_has_method(callee_cls, clone));
}

TEST_F(CallsiteNeverInlineCloningTest, InvokeSuperIsNeverRedirected) {
  // `invoke-super` call sites are always left alone, whatever their
  // hot/cold mix, however monomorphic the target might otherwise look. The
  // callers are static methods taking an "LFoo;" instance as an explicit
  // parameter purely so the invoke has a receiver register to name --
  // real bytecode restricts invoke-super to a method that itself overrides
  // the target, but this pass never inspects that invariant (it rejects
  // purely by opcode), so this simplified shape is enough to exercise it.
  DexMethod *callee, *hot_caller, *cold_caller;
  auto* cls = create_class(
      {
          {
              "callee",
              "()V",
              R"((
                (.src_block "LFoo;.callee:()V" 0 (0.7 60))
                (return-void)
              ))",
          },
      },
      {&callee}, /* make_virtual */ true);
  hot_caller = DexMethod::make_method("LFoo;.hot_caller:(LFoo;)V")
                   ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                                   assembler::ircode_from_string(
                                       R"((
                                  (load-param-object v0)
                                  (.src_block "LFoo;.hot_caller:(LFoo;)V" 0 (1.0 100))
                                  (invoke-super (v0) "LFoo;.callee:()V")
                                  (return-void)
                                ))"),
                                   false);
  hot_caller->set_deobfuscated_name(show(hot_caller));
  hot_caller->get_code()->build_cfg();
  cls->add_method(hot_caller);
  cold_caller = DexMethod::make_method("LFoo;.cold_caller:(LFoo;)V")
                    ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                                    assembler::ircode_from_string(
                                        R"((
                                  (load-param-object v0)
                                  (.src_block "LFoo;.cold_caller:(LFoo;)V" 0 (0 0))
                                  (invoke-super (v0) "LFoo;.callee:()V")
                                  (return-void)
                                ))"),
                                    false);
  cold_caller->set_deobfuscated_name(show(cold_caller));
  cold_caller->get_code()->build_cfg();
  cls->add_method(cold_caller);

  Scope scope{cls};
  auto baseline_profile = compiled({callee, hot_caller, cold_caller});
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, test_config(), /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_GE(stats.invokes_super_opcode, 2u);
  EXPECT_EQ(stats.mixed_hotness_callees, 0u);
  EXPECT_EQ(stats.clones_created, 0u);
  EXPECT_EQ(find_invoked_method(cold_caller), callee);
  EXPECT_EQ(find_invoke_opcode(cold_caller), OPCODE_INVOKE_SUPER);
}

TEST_F(CallsiteNeverInlineCloningTest, BlocklistedCalleeIsNotCloned) {
  DexMethod *callee, *hot_caller, *cold_caller;
  auto* cls = create_class(
      {
          {"callee", "()V",
           R"((
                (.src_block "LFoo;.callee:()V" 0 (0.7 60))
                (return-void)
              ))"},
          {"hot_caller", "()V",
           R"((
                (.src_block "LFoo;.hot_caller:()V" 0 (1.0 100))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
          {"cold_caller", "()V",
           R"((
                (.src_block "LFoo;.cold_caller:()V" 0 (0 0))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
      },
      {&callee, &hot_caller, &cold_caller});

  Scope scope{cls};
  auto baseline_profile = compiled({callee, hot_caller, cold_caller});
  auto config = test_config();
  config.blocklist.emplace_back("LFoo;");
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, config, /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_EQ(stats.invokes_blocklisted_callee, 2u);
  EXPECT_EQ(stats.mixed_hotness_callees, 0u);
  EXPECT_EQ(stats.clones_created, 0u);
  EXPECT_EQ(find_invoked_method(cold_caller), callee);
}

TEST_F(CallsiteNeverInlineCloningTest, NoOptimizationsCalleeIsNotCloned) {
  DexMethod *callee, *hot_caller, *cold_caller;
  auto* cls = create_class(
      {
          {"callee", "()V",
           R"((
                (.src_block "LFoo;.callee:()V" 0 (0.7 60))
                (return-void)
              ))"},
          {"hot_caller", "()V",
           R"((
                (.src_block "LFoo;.hot_caller:()V" 0 (1.0 100))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
          {"cold_caller", "()V",
           R"((
                (.src_block "LFoo;.cold_caller:()V" 0 (0 0))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
      },
      {&callee, &hot_caller, &cold_caller});
  callee->rstate.set_no_optimizations();

  Scope scope{cls};
  auto baseline_profile = compiled({callee, hot_caller, cold_caller});
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, test_config(), /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_EQ(stats.invokes_no_optimizations_callee, 2u);
  EXPECT_EQ(stats.mixed_hotness_callees, 0u);
  EXPECT_EQ(stats.clones_created, 0u);
  EXPECT_EQ(find_invoked_method(cold_caller), callee);
}

TEST_F(CallsiteNeverInlineCloningTest, NoOutliningCalleeIsNotCloned) {
  DexMethod *callee, *hot_caller, *cold_caller;
  auto* cls = create_class(
      {
          {"callee", "()V",
           R"((
                (.src_block "LFoo;.callee:()V" 0 (0.7 60))
                (return-void)
              ))"},
          {"hot_caller", "()V",
           R"((
                (.src_block "LFoo;.hot_caller:()V" 0 (1.0 100))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
          {"cold_caller", "()V",
           R"((
                (.src_block "LFoo;.cold_caller:()V" 0 (0 0))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
      },
      {&callee, &hot_caller, &cold_caller});
  // ReachableNativesPass pins load-library entry points with this bit. It is
  // the body-cloning constraint; dont-inline alone constrains only Redex's
  // inliner.
  callee->rstate.set_no_outlining();

  Scope scope{cls};
  auto baseline_profile = compiled({callee, hot_caller, cold_caller});
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, test_config(), /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_EQ(stats.invokes_no_outlining_callee, 2u);
  EXPECT_EQ(stats.mixed_hotness_callees, 0u);
  EXPECT_EQ(stats.clones_created, 0u);
  EXPECT_EQ(find_invoked_method(cold_caller), callee);
}

TEST_F(CallsiteNeverInlineCloningTest, DontInlineOnlyCalleeIsCloned) {
  DexMethod *callee, *hot_caller, *cold_caller, *cold_caller2;
  auto* cls = create_class(
      {
          {"callee", "()V",
           R"((
                (.src_block "LFoo;.callee:()V" 0 (0.7 60))
                (const v0 1)
                (const v1 2)
                (add-int v0 v0 v1)
                (add-int v0 v0 v1)
                (return-void)
              ))"},
          {"hot_caller", "()V",
           R"((
                (.src_block "LFoo;.hot_caller:()V" 0 (1.0 100))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
          {"cold_caller", "()V",
           R"((
                (.src_block "LFoo;.cold_caller:()V" 0 (0 0))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
          {"cold_caller2", "()V",
           R"((
                (.src_block "LFoo;.cold_caller2:()V" 0 (0 0))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
      },
      {&callee, &hot_caller, &cold_caller, &cold_caller2});
  callee->rstate.set_dont_inline();

  Scope scope{cls};
  auto baseline_profile =
      compiled({callee, hot_caller, cold_caller, cold_caller2});
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, test_config(), /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_EQ(stats.invokes_no_outlining_callee, 0u);
  EXPECT_EQ(stats.clones_created, 1u);
  EXPECT_EQ(find_invoked_method(hot_caller), callee);
  EXPECT_NE(find_invoked_method(cold_caller), callee);
  EXPECT_EQ(find_invoked_method(cold_caller2),
            find_invoked_method(cold_caller));
}

TEST_F(CallsiteNeverInlineCloningTest,
       NonRenamableMethodInRenamableClassIsCloned) {
  DexMethod *callee, *hot_caller, *cold_caller, *cold_caller2;
  auto* cls = create_class(
      {
          {"callee", "()V",
           R"((
                (.src_block "LFoo;.callee:()V" 0 (0.7 60))
                (const v0 1)
                (const v1 2)
                (add-int v0 v0 v1)
                (add-int v0 v0 v1)
                (return-void)
              ))"},
          {"hot_caller", "()V",
           R"((
                (.src_block "LFoo;.hot_caller:()V" 0 (1.0 100))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
          {"cold_caller", "()V",
           R"((
                (.src_block "LFoo;.cold_caller:()V" 0 (0 0))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
          {"cold_caller2", "()V",
           R"((
                (.src_block "LFoo;.cold_caller2:()V" 0 (0 0))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
      },
      {&callee, &hot_caller, &cold_caller, &cold_caller2});
  callee->rstate.set_keepnames();
  ASSERT_FALSE(callee->rstate.can_rename());
  ASSERT_TRUE(cls->rstate.can_rename());

  Scope scope{cls};
  auto baseline_profile =
      compiled({callee, hot_caller, cold_caller, cold_caller2});
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, test_config(), /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_EQ(stats.invokes_non_renamable_callee_class, 0u);
  EXPECT_EQ(stats.clones_created, 1u);
  EXPECT_EQ(find_invoked_method(hot_caller), callee);
  EXPECT_NE(find_invoked_method(cold_caller), callee);
  EXPECT_EQ(find_invoked_method(cold_caller2),
            find_invoked_method(cold_caller));
}

TEST_F(CallsiteNeverInlineCloningTest, NonRenamableCalleeClassIsNotCloned) {
  DexMethod *callee, *hot_caller, *cold_caller;
  auto* cls = create_class(
      {
          {"callee", "()V",
           R"((
                (.src_block "LFoo;.callee:()V" 0 (0.7 60))
                (return-void)
              ))"},
          {"hot_caller", "()V",
           R"((
                (.src_block "LFoo;.hot_caller:()V" 0 (1.0 100))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
          {"cold_caller", "()V",
           R"((
                (.src_block "LFoo;.cold_caller:()V" 0 (0 0))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
      },
      {&callee, &hot_caller, &cold_caller});
  // A kept class may be observed through reflection. Adding a generated
  // method would change its declared-method set even though the original
  // callee remains untouched.
  cls->rstate.set_keepnames();
  ASSERT_FALSE(cls->rstate.can_rename());

  Scope scope{cls};
  auto baseline_profile = compiled({callee, hot_caller, cold_caller});
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, test_config(), /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_EQ(stats.invokes_non_renamable_callee_class, 2u);
  EXPECT_EQ(stats.mixed_hotness_callees, 0u);
  EXPECT_EQ(stats.clones_created, 0u);
  EXPECT_EQ(find_invoked_method(cold_caller), callee);
}

TEST_F(CallsiteNeverInlineCloningTest, NoOptimizationsCallerIsSkippedEntirely) {
  DexMethod *callee, *hot_caller, *cold_caller;
  auto* cls = create_class(
      {
          {"callee", "()V",
           R"((
                (.src_block "LFoo;.callee:()V" 0 (0.7 60))
                (return-void)
              ))"},
          {"hot_caller", "()V",
           R"((
                (.src_block "LFoo;.hot_caller:()V" 0 (1.0 100))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
          {"cold_caller", "()V",
           R"((
                (.src_block "LFoo;.cold_caller:()V" 0 (0 0))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
      },
      {&callee, &hot_caller, &cold_caller});
  cold_caller->rstate.set_no_optimizations();

  Scope scope{cls};
  auto baseline_profile = compiled({callee, hot_caller, cold_caller});
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, test_config(), /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_EQ(stats.callers_no_optimizations, 1u);
  // With its only cold call site now invisible to this pass, `callee` never
  // becomes a candidate at all.
  EXPECT_EQ(stats.mixed_hotness_callees, 0u);
  EXPECT_EQ(stats.clones_created, 0u);
  EXPECT_EQ(find_invoked_method(cold_caller), callee);
}

TEST_F(CallsiteNeverInlineCloningTest,
       CallsiteAndCalleeBothWithCatchIsNotRedirected) {
  // The cold call site's containing block has an outgoing throw edge (it is
  // inside a try region), and the callee itself has a catch block: this
  // exact combination is skipped (mirrors ArtProfileWriterPass's own gate),
  // so the callee never accumulates a cold call site and is never a
  // candidate.
  DexMethod *callee, *hot_caller, *cold_caller;
  auto* cls = create_class(
      {
          {"callee", "()V",
           R"((
                (.src_block "LFoo;.callee:()V" 0 (0.7 60))
                (.try_start a)
                (new-instance "Ljava/lang/Exception;")
                (move-result-pseudo-object v0)
                (throw v0)
                (.try_end a)
                (.catch (a))
                (return-void)
              ))"},
          {"hot_caller", "()V",
           R"((
                (.src_block "LFoo;.hot_caller:()V" 0 (1.0 100))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
          {"cold_caller", "()V",
           R"((
                (.src_block "LFoo;.cold_caller:()V" 0 (0 0))
                (.try_start b)
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
                (.try_end b)
                (.catch (b))
                (return-void)
              ))"},
      },
      {&callee, &hot_caller, &cold_caller});

  Scope scope{cls};
  auto baseline_profile = compiled({callee, hot_caller, cold_caller});
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, test_config(), /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_EQ(stats.invokes_callsite_and_callee_both_have_catch, 1u);
  EXPECT_EQ(stats.mixed_hotness_callees, 0u);
  EXPECT_EQ(stats.clones_created, 0u);
  EXPECT_EQ(find_invoked_method(cold_caller), callee);
}

TEST_F(CallsiteNeverInlineCloningTest, TooSmallCalleeIsNotCloned) {
  DexMethod *callee, *hot_caller, *cold_caller;
  auto* cls = create_class(
      {
          {"callee", "()V",
           R"((
                (.src_block "LFoo;.callee:()V" 0 (0.7 60))
                (const v0 1)
                (const v1 2)
                (add-int v0 v0 v1)
                (add-int v0 v0 v1)
                (return-void)
              ))"},
          {"hot_caller", "()V",
           R"((
                (.src_block "LFoo;.hot_caller:()V" 0 (1.0 100))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
          {"cold_caller", "()V",
           R"((
                (.src_block "LFoo;.cold_caller:()V" 0 (0 0))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
      },
      {&callee, &hot_caller, &cold_caller});

  Scope scope{cls};
  auto baseline_profile = compiled({callee, hot_caller, cold_caller});
  auto config = test_config();
  // `callee`'s body is just (src_block, return-void): 1 real opcode.
  config.min_callee_instructions = 100;
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, config, /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_EQ(stats.callees_too_small, 1u);
  EXPECT_EQ(stats.mixed_hotness_callees, 0u);
  EXPECT_EQ(stats.clones_created, 0u);
}

// --- Profitability model: thresholds, ranking, caps, estimate_only ---

namespace {

// A callee whose body is padded with `filler` self-add instructions plus a
// return, called from `hot_count` hot callers and `cold_count` distinct cold
// callers (each calling exactly once). Sized to land inside
// `Config`'s real-world default bounds: above `method_ref_cost` (16, so
// `cold_count >= 2` clears a positive net) and below `max_callee_code_units`
// (40, the shape-eligibility ceiling).
struct ProfitabilityFixture {
  DexClass* cls;
  DexMethod* callee;
  std::vector<DexMethod*> hot_callers;
  std::vector<DexMethod*> cold_callers;
};

ProfitabilityFixture make_profitability_fixture(const std::string& callee_name,
                                                size_t hot_count,
                                                size_t cold_count) {
  static std::atomic<size_t> fixture_counter{0};
  std::string cls_name =
      "LProfitFixture" + std::to_string(fixture_counter.fetch_add(1)) + ";";
  std::ostringstream callee_code;
  callee_code << "(\n  (.src_block \"" << cls_name << "." << callee_name
              << ":()V\" 0 (0.7 60))\n  (const v0 1)\n";
  // 14 uniform 1-code-unit-ish instructions: estimated code units land
  // safely between `method_ref_cost`'s default (16, so >=2 cold call sites
  // clear a positive net) and `max_callee_code_units`'s default (40, the
  // shape eligibility ceiling), without depending on immediate-encoding
  // width the way varying `const` operands would.
  for (size_t i = 0; i < 14; i++) {
    callee_code << "  (add-int v0 v0 v0)\n";
  }
  callee_code << "  (return-void)\n)";

  ClassCreator cc{DexType::make_type(cls_name)};
  cc.set_super(type::java_lang_Object());
  auto* callee =
      DexMethod::make_method(cls_name + "." + callee_name + ":()V")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                          assembler::ircode_from_string(callee_code.str()),
                          false);
  callee->set_deobfuscated_name(show(callee));
  callee->get_code()->build_cfg();
  cc.add_method(callee);

  std::vector<DexMethod*> hot_callers;
  for (size_t i = 0; i < hot_count; i++) {
    std::string name = "hot_caller" + std::to_string(i);
    auto* m =
        DexMethod::make_method(cls_name + "." + name + ":()V")
            ->make_concrete(
                ACC_PUBLIC | ACC_STATIC,
                assembler::ircode_from_string(
                    "(\n  (.src_block \"" + cls_name + "." + name +
                    ":()V\" 0 (1.0 100))\n  (invoke-static () \"" + cls_name +
                    "." + callee_name + ":()V\")\n  (return-void)\n)"),
                false);
    m->set_deobfuscated_name(show(m));
    m->get_code()->build_cfg();
    cc.add_method(m);
    hot_callers.emplace_back(m);
  }

  std::vector<DexMethod*> cold_callers;
  for (size_t i = 0; i < cold_count; i++) {
    std::string name = "cold_caller" + std::to_string(i);
    auto* m = DexMethod::make_method(cls_name + "." + name + ":()V")
                  ->make_concrete(
                      ACC_PUBLIC | ACC_STATIC,
                      assembler::ircode_from_string(
                          "(\n  (.src_block \"" + cls_name + "." + name +
                          ":()V\" 0 (0 0))\n  (invoke-static () \"" + cls_name +
                          "." + callee_name + ":()V\")\n  (return-void)\n)"),
                      false);
    m->set_deobfuscated_name(show(m));
    m->get_code()->build_cfg();
    cc.add_method(m);
    cold_callers.emplace_back(m);
  }

  auto* cls = cc.create();
  return ProfitabilityFixture{cls, callee, hot_callers, cold_callers};
}

baseline_profiles::BaselineProfile compile_fixture(
    const ProfitabilityFixture& fx) {
  baseline_profiles::BaselineProfile bp;
  bp.methods[fx.callee] = baseline_profiles::MethodFlags{.hot = true};
  for (auto* m : fx.hot_callers) {
    bp.methods[m] = baseline_profiles::MethodFlags{.hot = true};
  }
  for (auto* m : fx.cold_callers) {
    bp.methods[m] = baseline_profiles::MethodFlags{.hot = true};
  }
  return bp;
}

} // namespace

TEST_F(CallsiteNeverInlineCloningTest, CostModelRejectsBelowMinColdCallsites) {
  // Real-world defaults (min_cold_callsites=2): a callee with only 1 cold
  // call site is never cloned, whatever its size.
  auto fx = make_profitability_fixture("callee", /* hot */ 1, /* cold */ 1);
  Scope scope{fx.cls};
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, profitability_config(), /* iteration */ 0, compile_fixture(fx),
      empty_method_profiles());

  EXPECT_EQ(stats.mixed_hotness_callees, 1u);
  EXPECT_EQ(stats.rejected_insufficient_cold_callsites, 1u);
  EXPECT_EQ(stats.clones_created, 0u);
  EXPECT_EQ(find_invoked_method(fx.cold_callers[0]), fx.callee);
}

TEST_F(CallsiteNeverInlineCloningTest, CostModelRejectsBelowMinHotCallsites) {
  auto fx = make_profitability_fixture("callee", /* hot */ 1, /* cold */ 3);
  Scope scope{fx.cls};
  auto config = profitability_config();
  config.min_hot_callsites = 2;
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, config, /* iteration */ 0, compile_fixture(fx),
      empty_method_profiles());

  EXPECT_EQ(stats.rejected_insufficient_hot_callsites, 1u);
  EXPECT_EQ(stats.clones_created, 0u);
}

TEST_F(CallsiteNeverInlineCloningTest, CostModelAcceptsWithDefaultsAtScale) {
  // The "null-check-scale population" case the profitability model's
  // defaults are meant to admit: a small, unremarkable callee reached from
  // one hot call site and several (>= default min_cold_callsites=2) cold
  // call sites clones successfully under real-world default thresholds --
  // no config override at all.
  auto fx = make_profitability_fixture("callee", /* hot */ 1, /* cold */ 4);
  Scope scope{fx.cls};
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, profitability_config(), /* iteration */ 0, compile_fixture(fx),
      empty_method_profiles());

  EXPECT_EQ(stats.clones_created, 1u);
  EXPECT_EQ(stats.cold_callsites_redirected, 4u);
  EXPECT_GT(stats.total_estimated_net, 0);
  EXPECT_GT(stats.total_estimated_oat_code_units_saved, 0);
  EXPECT_EQ(stats.total_estimated_method_refs, 2u);
  EXPECT_GT(stats.total_cloned_code_units, 0u);
  for (auto* cc : fx.cold_callers) {
    EXPECT_NE(find_invoked_method(cc), fx.callee);
  }
  EXPECT_EQ(find_invoked_method(fx.hot_callers[0]), fx.callee);
}

TEST_F(CallsiteNeverInlineCloningTest,
       CostModelRejectsBelowMinEstimatedSavedThreshold) {
  auto fx = make_profitability_fixture("callee", /* hot */ 1, /* cold */ 4);
  Scope scope{fx.cls};
  auto config = profitability_config();
  // Set the floor above what this fixture's cold-callsite-count * ecu can
  // ever reach.
  config.min_estimated_oat_code_units_saved = 1000000;
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, config, /* iteration */ 0, compile_fixture(fx),
      empty_method_profiles());

  EXPECT_EQ(stats.rejected_insufficient_estimated_savings, 1u);
  EXPECT_EQ(stats.clones_created, 0u);
}

TEST_F(CallsiteNeverInlineCloningTest, CostModelRejectsNonPositiveNet) {
  // A large `method_ref_cost` overwhelms any callee's estimated saving.
  auto fx = make_profitability_fixture("callee", /* hot */ 1, /* cold */ 4);
  Scope scope{fx.cls};
  auto config = profitability_config();
  config.method_ref_cost = 1000000;
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, config, /* iteration */ 0, compile_fixture(fx),
      empty_method_profiles());

  EXPECT_EQ(stats.rejected_non_positive_net, 1u);
  EXPECT_EQ(stats.clones_created, 0u);
}

TEST_F(CallsiteNeverInlineCloningTest, EstimateOnlyMutatesNothing) {
  auto fx = make_profitability_fixture("callee", /* hot */ 1, /* cold */ 4);
  Scope scope{fx.cls};
  auto config = profitability_config();
  config.estimate_only = true;
  size_t methods_before = fx.cls->get_all_methods().size();
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, config, /* iteration */ 0, compile_fixture(fx),
      empty_method_profiles());

  // The model ran and reports what it WOULD have done...
  EXPECT_EQ(stats.selected_candidates, 1u);
  EXPECT_GT(stats.total_estimated_net, 0);
  EXPECT_GT(stats.total_estimated_oat_code_units_saved, 0);
  EXPECT_EQ(stats.total_estimated_method_refs, 2u);
  EXPECT_GT(stats.total_cloned_code_units, 0u);
  // ...but performed no mutation whatsoever: no new method, no call site
  // rewritten.
  EXPECT_EQ(stats.clones_created, 0u);
  EXPECT_EQ(stats.cold_callsites_redirected, 0u);
  EXPECT_EQ(fx.cls->get_all_methods().size(), methods_before);
  for (auto* cc : fx.cold_callers) {
    EXPECT_EQ(find_invoked_method(cc), fx.callee);
  }
  EXPECT_EQ(find_invoked_method(fx.hot_callers[0]), fx.callee);
}

TEST_F(CallsiteNeverInlineCloningTest,
       RankingAndCapsAcceptHighestNetCandidateFirst) {
  // Two independent, otherwise-equally-eligible candidates: `low_net` (4
  // cold call sites) and `high_net` (6 cold call sites, a larger estimated
  // saving). With `max_total_clones=1`, only the higher-net candidate is
  // accepted, regardless of which one this pass happened to discover first
  // (both come from the same `Scope`, in whatever order
  // `unordered_to_ordered_keys` produces before ranking).
  auto fx_low = make_profitability_fixture("low_net", /* hot */ 1,
                                           /* cold */ 4);
  auto fx_high = make_profitability_fixture("high_net", /* hot */ 1,
                                            /* cold */ 6);

  Scope scope{fx_low.cls, fx_high.cls};
  auto config = profitability_config();
  config.max_total_clones = 1;
  baseline_profiles::BaselineProfile bp = compile_fixture(fx_high);
  auto bp_low = compile_fixture(fx_low);
  for (auto& p : UnorderedIterable(bp_low.methods)) {
    bp.methods[p.first] = p.second;
  }

  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, config, /* iteration */ 0, bp, empty_method_profiles());

  EXPECT_EQ(stats.mixed_hotness_callees, 2u);
  EXPECT_EQ(stats.clones_created, 1u);
  EXPECT_EQ(stats.rejected_cap_max_total_clones, 1u);
  // The higher-net candidate (fx_high, 6 cold call sites) is the one
  // actually cloned; the lower-net one (fx_low, 4 cold call sites) is not.
  for (auto* cc : fx_high.cold_callers) {
    EXPECT_NE(find_invoked_method(cc), fx_high.callee);
  }
  for (auto* cc : fx_low.cold_callers) {
    EXPECT_EQ(find_invoked_method(cc), fx_low.callee);
  }
}

TEST_F(CallsiteNeverInlineCloningTest,
       RankingAndCapsRespectMaxTotalClonedCodeUnits) {
  auto fx = make_profitability_fixture("callee", /* hot */ 1, /* cold */ 4);
  Scope scope{fx.cls};
  auto config = profitability_config();
  // A cap of 1 code unit is below any real callee's size, so the one
  // candidate is rejected by the code-units cap specifically (not by
  // max_total_clones, which stays at its permissive default).
  config.max_total_cloned_code_units = 1;
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, config, /* iteration */ 0, compile_fixture(fx),
      empty_method_profiles());

  EXPECT_EQ(stats.rejected_cap_max_total_cloned_code_units, 1u);
  EXPECT_EQ(stats.clones_created, 0u);
}

// --- method_ref_cost: charged per distinct cold-caller class ---

namespace {

// One callee (its own class), one hot caller (same class), and one cold
// caller per entry of a fresh class -- so the cold call sites span exactly
// `num_cold_caller_classes` distinct classes, each contributing exactly one
// cold call site. The callee's body is identical to
// `make_profitability_fixture`'s (same instruction count), so a test
// comparing this fixture against that one is comparing candidates with the
// same `callee_code_units` and the same `cold_count`, isolating the effect
// of `estimated_incremental_mrefs` alone.
struct CrossClassProfitabilityFixture {
  DexClass* callee_cls;
  DexMethod* callee;
  DexMethod* hot_caller;
  std::vector<DexClass*> cold_caller_classes;
  std::vector<DexMethod*> cold_callers;
};

CrossClassProfitabilityFixture make_cross_class_profitability_fixture(
    size_t num_cold_caller_classes, size_t cold_callers_per_class = 1) {
  static std::atomic<size_t> counter{0};
  size_t c = counter.fetch_add(1);
  std::string callee_cls_name = "LMrefCallee" + std::to_string(c) + ";";
  ClassCreator callee_cc{DexType::make_type(callee_cls_name)};
  callee_cc.set_super(type::java_lang_Object());
  std::ostringstream callee_code;
  callee_code << "(\n  (.src_block \"" << callee_cls_name
              << ".callee:()V\" 0 (0.7 60))\n  (const v0 1)\n";
  for (size_t i = 0; i < 14; i++) {
    callee_code << "  (add-int v0 v0 v0)\n";
  }
  callee_code << "  (return-void)\n)";
  auto* callee =
      DexMethod::make_method(callee_cls_name + ".callee:()V")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                          assembler::ircode_from_string(callee_code.str()),
                          false);
  callee->set_deobfuscated_name(show(callee));
  callee->get_code()->build_cfg();
  callee_cc.add_method(callee);
  auto* callee_cls = callee_cc.create();

  auto* hot_caller =
      DexMethod::make_method(callee_cls_name + ".hot_caller:()V")
          ->make_concrete(
              ACC_PUBLIC | ACC_STATIC,
              assembler::ircode_from_string(
                  "(\n  (.src_block \"" + callee_cls_name +
                  ".hot_caller:()V\" 0 (1.0 100))\n  (invoke-static () \"" +
                  callee_cls_name + ".callee:()V\")\n  (return-void)\n)"),
              false);
  hot_caller->set_deobfuscated_name(show(hot_caller));
  hot_caller->get_code()->build_cfg();
  callee_cls->add_method(hot_caller);

  std::vector<DexClass*> cold_caller_classes;
  std::vector<DexMethod*> cold_callers;
  for (size_t i = 0; i < num_cold_caller_classes; i++) {
    std::string cls_name =
        "LMrefCaller" + std::to_string(c) + "_" + std::to_string(i) + ";";
    ClassCreator cc{DexType::make_type(cls_name)};
    cc.set_super(type::java_lang_Object());
    for (size_t j = 0; j < cold_callers_per_class; j++) {
      std::string method_name = "cold_caller" + std::to_string(j);
      auto* m =
          DexMethod::make_method(cls_name + "." + method_name + ":()V")
              ->make_concrete(
                  ACC_PUBLIC | ACC_STATIC,
                  assembler::ircode_from_string(
                      "(\n  (.src_block \"" + cls_name + "." + method_name +
                      ":()V\" 0 (0 0))\n  (invoke-static () \"" +
                      callee_cls_name + ".callee:()V\")\n  (return-void)\n)"),
                  false);
      m->set_deobfuscated_name(show(m));
      m->get_code()->build_cfg();
      cc.add_method(m);
      cold_callers.emplace_back(m);
    }
    cold_caller_classes.emplace_back(cc.create());
  }

  return CrossClassProfitabilityFixture{callee_cls, callee, hot_caller,
                                        cold_caller_classes, cold_callers};
}

baseline_profiles::BaselineProfile compile_cross_class_fixture(
    const CrossClassProfitabilityFixture& fx) {
  baseline_profiles::BaselineProfile bp;
  bp.methods[fx.callee] = baseline_profiles::MethodFlags{.hot = true};
  bp.methods[fx.hot_caller] = baseline_profiles::MethodFlags{.hot = true};
  for (auto* m : fx.cold_callers) {
    bp.methods[m] = baseline_profiles::MethodFlags{.hot = true};
  }
  return bp;
}

Scope cross_class_fixture_scope(const CrossClassProfitabilityFixture& fx) {
  Scope scope;
  scope.emplace_back(fx.callee_cls);
  for (auto* cls : fx.cold_caller_classes) {
    scope.emplace_back(cls);
  }
  return scope;
}

} // namespace

TEST_F(CallsiteNeverInlineCloningTest,
       MethodRefCostScalesWithDistinctCallerClasses) {
  // 2 distinct calling classes, 2 cold call sites each (cold_count=4, so the
  // net stays positive under the higher mref charge -- see the algebra in
  // MethodRefCostPerClassRejectsWhatPerCloneWouldHaveAccepted for why a
  // smaller cold_count here would not).
  auto fx = make_cross_class_profitability_fixture(
      /* num_cold_caller_classes */ 2, /* cold_callers_per_class */ 2);
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      cross_class_fixture_scope(fx), profitability_config(), /* iteration */ 0,
      compile_cross_class_fixture(fx), empty_method_profiles());

  EXPECT_EQ(stats.clones_created, 1u);
  // 1 for the clone's own definition + 2 distinct cold-caller classes.
  EXPECT_EQ(stats.total_estimated_method_refs, 3u);
}

TEST_F(CallsiteNeverInlineCloningTest,
       MethodRefCostPerClassRejectsWhatPerCloneWouldHaveAccepted) {
  // Same callee body (so the same `callee_code_units`) and the same total
  // cold call-site count (4) in both fixtures -- the only difference is
  // whether those 4 cold call sites live in 1 calling class or 4. Set
  // `method_ref_cost` to exactly the callee's own `estimate_code_units()`:
  // algebraically, with `cold_count=4`, this makes `estimated_net` positive
  // at `estimated_incremental_mrefs=2` (1 class) and negative at
  // `estimated_incremental_mrefs=5` (4 classes) regardless of the actual
  // code-unit count, so this is not sensitive to instruction-encoding
  // changes to the shared test fixture body.
  auto narrow = make_profitability_fixture("narrow_callee", /* hot */ 1,
                                           /* cold */ 4);
  auto wide = make_cross_class_profitability_fixture(
      /* num_cold_caller_classes */ 4);
  auto config = profitability_config();
  config.method_ref_cost = narrow.callee->get_code()->estimate_code_units();

  auto narrow_stats =
      CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
          Scope{narrow.cls}, config, /* iteration */ 0, compile_fixture(narrow),
          empty_method_profiles());
  EXPECT_EQ(narrow_stats.clones_created, 1u);
  EXPECT_EQ(narrow_stats.total_estimated_method_refs, 2u);

  auto wide_stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      cross_class_fixture_scope(wide), config, /* iteration */ 0,
      compile_cross_class_fixture(wide), empty_method_profiles());
  EXPECT_EQ(wide_stats.clones_created, 0u);
  EXPECT_EQ(wide_stats.rejected_non_positive_net, 1u);
}

// --- constructors, interface dispatch, safety gates ---

TEST_F(CallsiteNeverInlineCloningTest, InitCalleeIsNeverCloned) {
  // `<init>` cannot be cloned under a different name -- the JVM/ART require
  // the literal name "<init>" for a constructor -- so this pass must reject
  // it before ever attempting to build a `$cnic$`-suffixed clone name,
  // however mixed its call sites.
  size_t c = s_counter.fetch_add(1);
  std::string name = std::string("LCtor") + std::to_string(c) + ";";
  ClassCreator cc{DexType::make_type(name)};
  cc.set_super(type::java_lang_Object());
  auto* ctor = DexMethod::make_method(name + ".<init>:(I)V")
                   ->make_concrete(ACC_PUBLIC,
                                   assembler::ircode_from_string(
                                       ("(\n"
                                        "  (.src_block \"" +
                                        name +
                                        ".<init>:(I)V\" 0 (0.7 60))\n"
                                        "  (load-param-object v0)\n"
                                        "  (load-param v1)\n"
                                        "  (return-void)\n"
                                        ")")),
                                   /* is_virtual */ false);
  ctor->set_deobfuscated_name(show(ctor));
  ctor->get_code()->build_cfg();
  cc.add_method(ctor);
  auto* hot_caller =
      DexMethod::make_method(name + ".hot_caller:(" + name + "I)V")
          ->make_concrete(
              ACC_PUBLIC | ACC_STATIC,
              assembler::ircode_from_string(("(\n"
                                             "  (load-param-object v0)\n"
                                             "  (load-param v1)\n"
                                             "  (.src_block \"" +
                                             name + ".hot_caller:(" + name +
                                             "I)V\" 0 (1.0 100))\n"
                                             "  (invoke-direct (v0 v1) \"" +
                                             name +
                                             ".<init>:(I)V\")\n"
                                             "  (return-void)\n"
                                             ")")),
              false);
  hot_caller->set_deobfuscated_name(show(hot_caller));
  hot_caller->get_code()->build_cfg();
  cc.add_method(hot_caller);
  auto* cold_caller =
      DexMethod::make_method(name + ".cold_caller:(" + name + "I)V")
          ->make_concrete(
              ACC_PUBLIC | ACC_STATIC,
              assembler::ircode_from_string(("(\n"
                                             "  (load-param-object v0)\n"
                                             "  (load-param v1)\n"
                                             "  (.src_block \"" +
                                             name + ".cold_caller:(" + name +
                                             "I)V\" 0 (0 0))\n"
                                             "  (invoke-direct (v0 v1) \"" +
                                             name +
                                             ".<init>:(I)V\")\n"
                                             "  (return-void)\n"
                                             ")")),
              false);
  cold_caller->set_deobfuscated_name(show(cold_caller));
  cold_caller->get_code()->build_cfg();
  cc.add_method(cold_caller);
  auto* cls = cc.create();

  Scope scope{cls};
  auto baseline_profile = compiled({ctor, hot_caller, cold_caller});
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, test_config(), /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_EQ(stats.invokes_init_callee, 2u);
  EXPECT_EQ(stats.mixed_hotness_callees, 0u);
  EXPECT_EQ(stats.clones_created, 0u);
  EXPECT_EQ(find_invoked_method(cold_caller), ctor);
}

TEST_F(CallsiteNeverInlineCloningTest, ClinitCalleeIsNeverCloned) {
  // `<clinit>` cannot be cloned under a different name either, for the same
  // reason as `<init>`. Real bytecode never calls it explicitly (the
  // runtime invokes it once per class), but this pass rejects it purely by
  // name, so an explicit invoke-static exercises the same guard.
  DexMethod *clinit, *hot_caller, *cold_caller;
  auto* cls = create_class(
      {
          {"<clinit>", "()V",
           R"((
                (.src_block "LFoo;.<clinit>:()V" 0 (0.7 60))
                (return-void)
              ))"},
          {"hot_caller", "()V",
           R"((
                (.src_block "LFoo;.hot_caller:()V" 0 (1.0 100))
                (invoke-static () "LFoo;.<clinit>:()V")
                (return-void)
              ))"},
          {"cold_caller", "()V",
           R"((
                (.src_block "LFoo;.cold_caller:()V" 0 (0 0))
                (invoke-static () "LFoo;.<clinit>:()V")
                (return-void)
              ))"},
      },
      {&clinit, &hot_caller, &cold_caller});

  Scope scope{cls};
  auto baseline_profile = compiled({clinit, hot_caller, cold_caller});
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, test_config(), /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_EQ(stats.invokes_init_callee, 2u);
  EXPECT_EQ(stats.mixed_hotness_callees, 0u);
  EXPECT_EQ(stats.clones_created, 0u);
  EXPECT_EQ(find_invoked_method(cold_caller), clinit);
}

TEST_F(CallsiteNeverInlineCloningTest, InvokeInterfaceIsNeverRedirected) {
  // `invoke-interface` call sites are always left alone, whatever their
  // hot/cold mix: this pass only ever redirects invoke-static, invoke-direct,
  // or an invoke-virtual to a non-true-virtual callee.
  DexMethod *callee, *hot_caller, *cold_caller;
  auto* cls = create_class(
      {
          {
              "callee",
              "()V",
              R"((
                (.src_block "LFoo;.callee:()V" 0 (0.7 60))
                (return-void)
              ))",
          },
      },
      {&callee}, /* make_virtual */ true);
  hot_caller = DexMethod::make_method("LFoo;.hot_caller:(LFoo;)V")
                   ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                                   assembler::ircode_from_string(
                                       R"((
                                  (load-param-object v0)
                                  (.src_block "LFoo;.hot_caller:(LFoo;)V" 0 (1.0 100))
                                  (invoke-interface (v0) "LFoo;.callee:()V")
                                  (return-void)
                                ))"),
                                   false);
  hot_caller->set_deobfuscated_name(show(hot_caller));
  hot_caller->get_code()->build_cfg();
  cls->add_method(hot_caller);
  cold_caller = DexMethod::make_method("LFoo;.cold_caller:(LFoo;)V")
                    ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                                    assembler::ircode_from_string(
                                        R"((
                                  (load-param-object v0)
                                  (.src_block "LFoo;.cold_caller:(LFoo;)V" 0 (0 0))
                                  (invoke-interface (v0) "LFoo;.callee:()V")
                                  (return-void)
                                ))"),
                                    false);
  cold_caller->set_deobfuscated_name(show(cold_caller));
  cold_caller->get_code()->build_cfg();
  cls->add_method(cold_caller);

  Scope scope{cls};
  auto baseline_profile = compiled({callee, hot_caller, cold_caller});
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, test_config(), /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_GE(stats.invokes_interface_opcode, 2u);
  EXPECT_EQ(stats.mixed_hotness_callees, 0u);
  EXPECT_EQ(stats.clones_created, 0u);
  EXPECT_EQ(find_invoked_method(cold_caller), callee);
  EXPECT_EQ(find_invoke_opcode(cold_caller), OPCODE_INVOKE_INTERFACE);
}

TEST_F(CallsiteNeverInlineCloningTest,
       PrivateInstanceMethodViaInvokeDirectIsCloned) {
  // An ordinary private instance method reached via invoke-direct (not a
  // constructor) is eligible like any other exact-dispatch callee.
  size_t c = s_counter.fetch_add(1);
  std::string name = std::string("LPriv") + std::to_string(c) + ";";
  ClassCreator cc{DexType::make_type(name)};
  cc.set_super(type::java_lang_Object());
  auto* callee = DexMethod::make_method(name + ".callee:()V")
                     ->make_concrete(ACC_PRIVATE,
                                     assembler::ircode_from_string(
                                         ("(\n"
                                          "  (load-param-object v0)\n"
                                          "  (.src_block \"" +
                                          name +
                                          ".callee:()V\" 0 (0.7 60))\n"
                                          "  (const v1 1)\n"
                                          "  (const v2 2)\n"
                                          "  (add-int v1 v1 v2)\n"
                                          "  (add-int v1 v1 v2)\n"
                                          "  (return-void)\n"
                                          ")")),
                                     /* is_virtual */ false);
  callee->set_deobfuscated_name(show(callee));
  callee->get_code()->build_cfg();
  cc.add_method(callee);
  auto* hot_caller =
      DexMethod::make_method(name + ".hot_caller:(" + name + ")V")
          ->make_concrete(
              ACC_PUBLIC | ACC_STATIC,
              assembler::ircode_from_string(("(\n"
                                             "  (load-param-object v0)\n"
                                             "  (.src_block \"" +
                                             name + ".hot_caller:(" + name +
                                             ")V\" 0 (1.0 100))\n"
                                             "  (invoke-direct (v0) \"" +
                                             name +
                                             ".callee:()V\")\n"
                                             "  (return-void)\n"
                                             ")")),
              false);
  hot_caller->set_deobfuscated_name(show(hot_caller));
  hot_caller->get_code()->build_cfg();
  cc.add_method(hot_caller);
  auto* cold_caller =
      DexMethod::make_method(name + ".cold_caller:(" + name + ")V")
          ->make_concrete(
              ACC_PUBLIC | ACC_STATIC,
              assembler::ircode_from_string(("(\n"
                                             "  (load-param-object v0)\n"
                                             "  (.src_block \"" +
                                             name + ".cold_caller:(" + name +
                                             ")V\" 0 (0 0))\n"
                                             "  (invoke-direct (v0) \"" +
                                             name +
                                             ".callee:()V\")\n"
                                             "  (return-void)\n"
                                             ")")),
              false);
  cold_caller->set_deobfuscated_name(show(cold_caller));
  cold_caller->get_code()->build_cfg();
  cc.add_method(cold_caller);
  auto* cold_caller2 =
      DexMethod::make_method(name + ".cold_caller2:(" + name + ")V")
          ->make_concrete(
              ACC_PUBLIC | ACC_STATIC,
              assembler::ircode_from_string(("(\n"
                                             "  (load-param-object v0)\n"
                                             "  (.src_block \"" +
                                             name + ".cold_caller2:(" + name +
                                             ")V\" 0 (0 0))\n"
                                             "  (invoke-direct (v0) \"" +
                                             name +
                                             ".callee:()V\")\n"
                                             "  (return-void)\n"
                                             ")")),
              false);
  cold_caller2->set_deobfuscated_name(show(cold_caller2));
  cold_caller2->get_code()->build_cfg();
  cc.add_method(cold_caller2);
  auto* cls = cc.create();

  Scope scope{cls};
  auto baseline_profile =
      compiled({callee, hot_caller, cold_caller, cold_caller2});
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, test_config(), /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_EQ(stats.mixed_hotness_callees, 1u);
  EXPECT_EQ(stats.clones_created, 1u);
  EXPECT_EQ(find_invoked_method(hot_caller), callee);
  EXPECT_EQ(find_invoke_opcode(hot_caller), OPCODE_INVOKE_DIRECT);
  auto* clone = find_invoked_method(cold_caller);
  ASSERT_NE(clone, nullptr);
  EXPECT_NE(clone, callee);
  EXPECT_EQ(find_invoke_opcode(cold_caller), OPCODE_INVOKE_DIRECT);
  EXPECT_EQ(find_invoked_method(cold_caller2), clone);
  EXPECT_TRUE(is_private(clone));
}

TEST_F(CallsiteNeverInlineCloningTest, AlreadyNeverInlineCalleeIsNotCloned) {
  DexMethod *callee, *hot_caller, *cold_caller;
  auto* cls = create_class(
      {
          {"callee", "()V",
           R"((
                (.src_block "LFoo;.callee:()V" 0 (0.7 60))
                (return-void)
              ))"},
          {"hot_caller", "()V",
           R"((
                (.src_block "LFoo;.hot_caller:()V" 0 (1.0 100))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
          {"cold_caller", "()V",
           R"((
                (.src_block "LFoo;.cold_caller:()V" 0 (0 0))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
      },
      {&callee, &hot_caller, &cold_caller});
  // `attach_annotation_set` refuses a concrete non-synthetic method (the
  // ordinary way a real `@NeverInline`-annotated method reaches this state
  // is via javac/ObfuscatePass bookkeeping this test does not replicate);
  // marking it synthetic satisfies that precondition without changing
  // anything this pass itself inspects.
  callee->set_access(callee->get_access() | ACC_SYNTHETIC);
  DexAnnotationSet anno_set;
  anno_set.add_annotation(std::make_unique<DexAnnotation>(
      type::dalvik_annotation_optimization_NeverInline(),
      DexAnnotationVisibility::DAV_BUILD));
  bool attached = callee->attach_annotation_set(
      std::make_unique<DexAnnotationSet>(anno_set));
  ASSERT_TRUE(attached);

  Scope scope{cls};
  auto baseline_profile = compiled({callee, hot_caller, cold_caller});
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, test_config(), /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_EQ(stats.invokes_already_never_inline_callee, 2u);
  EXPECT_EQ(stats.mixed_hotness_callees, 0u);
  EXPECT_EQ(stats.clones_created, 0u);
  EXPECT_EQ(find_invoked_method(cold_caller), callee);
}

TEST_F(CallsiteNeverInlineCloningTest,
       CallerTooManyInstructionsIsSkippedEntirely) {
  DexMethod *callee, *hot_caller, *cold_caller;
  auto* cls = create_class(
      {
          {"callee", "()V",
           R"((
                (.src_block "LFoo;.callee:()V" 0 (0.7 60))
                (return-void)
              ))"},
          {"hot_caller", "()V",
           R"((
                (.src_block "LFoo;.hot_caller:()V" 0 (1.0 100))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
          {"cold_caller", "()V",
           R"((
                (.src_block "LFoo;.cold_caller:()V" 0 (0 0))
                (const v0 1)
                (const v1 2)
                (add-int v0 v0 v1)
                (add-int v0 v0 v1)
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
      },
      {&callee, &hot_caller, &cold_caller});

  Scope scope{cls};
  auto baseline_profile = compiled({callee, hot_caller, cold_caller});
  auto config = test_config();
  // `hot_caller` has 2 real opcodes (invoke, return); `cold_caller` has 6.
  config.max_caller_instructions = 3;
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, config, /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_EQ(stats.callers_too_many_instructions, 1u);
  EXPECT_EQ(stats.mixed_hotness_callees, 0u);
  EXPECT_EQ(stats.clones_created, 0u);
  EXPECT_EQ(find_invoked_method(cold_caller), callee);
}

TEST_F(CallsiteNeverInlineCloningTest,
       CallerVirtualRegistersDoNotExcludeCallSites) {
  DexMethod *callee, *hot_caller, *cold_caller;
  auto* cls = create_class(
      {
          {"callee", "()V",
           R"((
                (.src_block "LFoo;.callee:()V" 0 (0.7 60))
                (return-void)
              ))"},
          {"hot_caller", "()V",
           R"((
                (.src_block "LFoo;.hot_caller:()V" 0 (1.0 100))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
          {"cold_caller", "()V",
           R"((
                (.src_block "LFoo;.cold_caller:()V" 0 (0 0))
                (const v0 1)
                (const v1 1)
                (const v2 1)
                (const v3 1)
                (const v127 1)
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
      },
      {&callee, &hot_caller, &cold_caller});

  Scope scope{cls};
  auto baseline_profile = compiled({callee, hot_caller, cold_caller});
  auto config = test_config();
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, config, /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_EQ(stats.callees_too_small, 1u);
  EXPECT_EQ(stats.mixed_hotness_callees, 0u);
  EXPECT_EQ(stats.clones_created, 0u);
  EXPECT_EQ(find_invoked_method(cold_caller), callee);
}

// --- pre-rename blocklist matching ---

TEST_F(CallsiteNeverInlineCloningTest,
       BlocklistMatchesClassNameEvenWithDefaultDeobfuscatedName) {
  // This pass runs before any renaming pass; whether or not this specific
  // class already carries a deobfuscated name at this point, it must match
  // against a blocklist entry naming its own class ("LFoo;") -- the
  // dedicated `BlocklistPrefersDeobfuscatedNameOverRawClassName` test below
  // isolates the case where the two names actually differ.
  DexMethod *callee, *hot_caller, *cold_caller;
  auto* cls = create_class(
      {
          {"callee", "()V",
           R"((
                (.src_block "LFoo;.callee:()V" 0 (0.7 60))
                (return-void)
              ))"},
          {"hot_caller", "()V",
           R"((
                (.src_block "LFoo;.hot_caller:()V" 0 (1.0 100))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
          {"cold_caller", "()V",
           R"((
                (.src_block "LFoo;.cold_caller:()V" 0 (0 0))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
      },
      {&callee, &hot_caller, &cold_caller});

  Scope scope{cls};
  auto baseline_profile = compiled({callee, hot_caller, cold_caller});
  auto config = test_config();
  config.blocklist.emplace_back("LFoo;");
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, config, /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_EQ(stats.invokes_blocklisted_callee, 2u);
  EXPECT_EQ(stats.mixed_hotness_callees, 0u);
  EXPECT_EQ(stats.clones_created, 0u);
  EXPECT_EQ(find_invoked_method(cold_caller), callee);
}

TEST_F(CallsiteNeverInlineCloningTest,
       BlocklistPrefersDeobfuscatedNameOverRawClassName) {
  // Once a deobfuscated name IS set (e.g. a later run, after renaming), the
  // blocklist must match against it, not the (now differently-named) raw
  // class name.
  size_t c = s_counter.fetch_add(1);
  std::string raw_name = std::string("LA") + std::to_string(c) + ";";
  std::string deobf_name =
      std::string("Lcom/blocked/Original") + std::to_string(c) + ";";
  ClassCreator cc{DexType::make_type(raw_name)};
  cc.set_super(type::java_lang_Object());
  auto* callee = DexMethod::make_method(raw_name + ".callee:()V")
                     ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                                     assembler::ircode_from_string(
                                         ("(\n"
                                          "  (.src_block \"" +
                                          raw_name +
                                          ".callee:()V\" 0 (0.7 60))\n"
                                          "  (return-void)\n"
                                          ")")),
                                     false);
  callee->set_deobfuscated_name(show(callee));
  callee->get_code()->build_cfg();
  cc.add_method(callee);
  auto* hot_caller = DexMethod::make_method(raw_name + ".hot_caller:()V")
                         ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                                         assembler::ircode_from_string(
                                             ("(\n"
                                              "  (.src_block \"" +
                                              raw_name +
                                              ".hot_caller:()V\" 0 (1.0 100))\n"
                                              "  (invoke-static () \"" +
                                              raw_name +
                                              ".callee:()V\")\n"
                                              "  (return-void)\n"
                                              ")")),
                                         false);
  hot_caller->set_deobfuscated_name(show(hot_caller));
  hot_caller->get_code()->build_cfg();
  cc.add_method(hot_caller);
  auto* cold_caller = DexMethod::make_method(raw_name + ".cold_caller:()V")
                          ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                                          assembler::ircode_from_string(
                                              ("(\n"
                                               "  (.src_block \"" +
                                               raw_name +
                                               ".cold_caller:()V\" 0 (0 0))\n"
                                               "  (invoke-static () \"" +
                                               raw_name +
                                               ".callee:()V\")\n"
                                               "  (return-void)\n"
                                               ")")),
                                          false);
  cold_caller->set_deobfuscated_name(show(cold_caller));
  cold_caller->get_code()->build_cfg();
  cc.add_method(cold_caller);
  auto* cls = cc.create();
  cls->set_deobfuscated_name(deobf_name);

  Scope scope{cls};
  auto baseline_profile = compiled({callee, hot_caller, cold_caller});
  auto config = test_config();
  config.blocklist.emplace_back("Lcom/blocked/");
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, config, /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  // Blocked via the deobfuscated name -- the raw name ("LA<n>;") would never
  // have matched this prefix.
  EXPECT_EQ(stats.invokes_blocklisted_callee, 2u);
  EXPECT_EQ(stats.mixed_hotness_callees, 0u);
  EXPECT_EQ(stats.clones_created, 0u);
  EXPECT_EQ(find_invoked_method(cold_caller), callee);
}

// --- -1/-1 defaults are a safe no-op ---

TEST_F(CallsiteNeverInlineCloningTest,
       BareDefaultThresholdsClassifyEveryCompiledCalleeAsHot) {
  // `Config{}`'s own hot_block/hot_method thresholds default to -1
  // (disabled), matching ArtProfileWriterPass's own global default: with no
  // explicit override, a call site to a baseline-profile-compiled callee
  // always classifies hot, so this pass never finds a "mixed-hotness"
  // callee and is a safe no-op unless an app explicitly configures these
  // two thresholds (as instagram.refig.inc/fb4a.refig.inc do).
  DexMethod *callee, *hot_caller, *cold_caller;
  auto* cls = create_class(
      {
          {"callee", "()V",
           R"((
                (.src_block "LFoo;.callee:()V" 0 (0.7 60))
                (const v0 1)
                (const v1 2)
                (add-int v0 v0 v1)
                (add-int v0 v0 v1)
                (return-void)
              ))"},
          {"hot_caller", "()V",
           R"((
                (.src_block "LFoo;.hot_caller:()V" 0 (1.0 100))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
          {"cold_caller", "()V",
           R"((
                (.src_block "LFoo;.cold_caller:()V" 0 (0 0))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
      },
      {&callee, &hot_caller, &cold_caller});

  Scope scope{cls};
  auto baseline_profile = compiled({callee, hot_caller, cold_caller});
  // Bare defaults for the two thresholds; only the volume knobs are relaxed
  // (irrelevant here since no callee ever becomes a cold-callsite candidate
  // at all).
  auto config = default_config();
  config.min_hot_callsites = 1;
  config.min_cold_callsites = 1;
  config.min_estimated_oat_code_units_saved = 0;
  config.method_ref_cost = 0;
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, config, /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_EQ(stats.mixed_hotness_callees, 0u);
  EXPECT_EQ(stats.clones_created, 0u);
  EXPECT_EQ(find_invoked_method(cold_caller), callee);
  EXPECT_EQ(find_invoked_method(hot_caller), callee);
}

// --- precomputed callee facts, never a live CFG dereference in the
//     parallel caller walk ---

TEST_F(CallsiteNeverInlineCloningTest,
       CalleeOutsideGivenScopeIsNeverConsidered) {
  // The callee's class is never passed in `scope`, even though the caller
  // is and the callee itself is fully built (code, CFG, baseline-profile
  // compiled): the precomputed callee-facts map only ever covers `scope`,
  // so this callee is treated the same as an external/no-code one -- never
  // a candidate, never dereferenced.
  size_t c = s_counter.fetch_add(1);
  std::string callee_cls_name =
      std::string("LOutOfScope") + std::to_string(c) + ";";
  ClassCreator callee_cc{DexType::make_type(callee_cls_name)};
  callee_cc.set_super(type::java_lang_Object());
  auto* callee = DexMethod::make_method(callee_cls_name + ".callee:()V")
                     ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                                     assembler::ircode_from_string(
                                         ("(\n"
                                          "  (.src_block \"" +
                                          callee_cls_name +
                                          ".callee:()V\" 0 (0.7 60))\n"
                                          "  (return-void)\n"
                                          ")")),
                                     false);
  callee->set_deobfuscated_name(show(callee));
  callee->get_code()->build_cfg();
  callee_cc.add_method(callee);
  callee_cc.create();

  std::string caller_cls_name =
      std::string("LOutOfScopeCaller") + std::to_string(c) + ";";
  ClassCreator caller_cc{DexType::make_type(caller_cls_name)};
  caller_cc.set_super(type::java_lang_Object());
  auto* hot_caller = DexMethod::make_method(caller_cls_name + ".hot_caller:()V")
                         ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                                         assembler::ircode_from_string(
                                             ("(\n"
                                              "  (.src_block \"" +
                                              caller_cls_name +
                                              ".hot_caller:()V\" 0 (1.0 100))\n"
                                              "  (invoke-static () \"" +
                                              callee_cls_name +
                                              ".callee:()V\")\n"
                                              "  (return-void)\n"
                                              ")")),
                                         false);
  hot_caller->set_deobfuscated_name(show(hot_caller));
  hot_caller->get_code()->build_cfg();
  caller_cc.add_method(hot_caller);
  auto* cold_caller =
      DexMethod::make_method(caller_cls_name + ".cold_caller:()V")
          ->make_concrete(
              ACC_PUBLIC | ACC_STATIC,
              assembler::ircode_from_string(("(\n"
                                             "  (.src_block \"" +
                                             caller_cls_name +
                                             ".cold_caller:()V\" 0 (0 0))\n"
                                             "  (invoke-static () \"" +
                                             callee_cls_name +
                                             ".callee:()V\")\n"
                                             "  (return-void)\n"
                                             ")")),
              false);
  cold_caller->set_deobfuscated_name(show(cold_caller));
  cold_caller->get_code()->build_cfg();
  caller_cc.add_method(cold_caller);
  auto* caller_cls = caller_cc.create();

  // Only the caller's class is in scope; the callee's class is not, even
  // though the callee itself is fully built and compiled.
  Scope scope{caller_cls};
  auto baseline_profile = compiled({callee, hot_caller, cold_caller});
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, test_config(), /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_EQ(stats.invokes_external_or_no_code_callee, 2u);
  EXPECT_EQ(stats.mixed_hotness_callees, 0u);
  EXPECT_EQ(stats.clones_created, 0u);
  EXPECT_EQ(find_invoked_method(cold_caller), callee);
}

// --- throw-adjacent skip mirrors ArtProfileWriterPass ---

TEST_F(CallsiteNeverInlineCloningTest,
       ThrowAdjacentColdLookingCallsiteIsNeverClassified) {
  // `cold_caller`'s only call to `callee` sits immediately before this
  // block's own exception construction and throw -- exactly the pattern
  // ArtProfileWriterPass itself skips (it is not a normal call site, just
  // the argument-evaluation step for the exception about to be thrown).
  // Without that skip, this callee would look mixed-hotness (1 hot, 1
  // cold) and get cloned; with it, the only "cold" site vanishes entirely,
  // so there is nothing to clone.
  DexMethod *callee, *hot_caller, *cold_caller;
  auto* cls = create_class(
      {
          {"callee", "()V",
           R"((
                (.src_block "LFoo;.callee:()V" 0 (0.7 60))
                (return-void)
              ))"},
          {"hot_caller", "()V",
           R"((
                (.src_block "LFoo;.hot_caller:()V" 0 (1.0 100))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
          {"cold_caller", "()V",
           R"((
                (.src_block "LFoo;.cold_caller:()V" 0 (0 0))
                (invoke-static () "LFoo;.callee:()V")
                (new-instance "Ljava/lang/Exception;")
                (move-result-pseudo-object v0)
                (invoke-direct (v0) "Ljava/lang/Exception;.<init>:()V")
                (throw v0)
              ))"},
      },
      {&callee, &hot_caller, &cold_caller});

  Scope scope{cls};
  auto baseline_profile = compiled({callee, hot_caller, cold_caller});
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, test_config(), /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_GE(stats.invokes_throw_adjacent, 1u);
  EXPECT_EQ(stats.mixed_hotness_callees, 0u);
  EXPECT_EQ(stats.clones_created, 0u);
  EXPECT_EQ(find_invoked_method(hot_caller), callee);
  EXPECT_EQ(find_invoked_method(cold_caller), callee);
}

// --- PartialApplication-style generated names ---

TEST_F(CallsiteNeverInlineCloningTest, GeneratedNameUsesStableIdentity) {
  // `$cnic$` is a reserved generated namespace, like PartialApplication's
  // `$spa$` / `$ipa$`. A legacy unhashed spelling therefore does not block the
  // stable method-identity suffix used by the actual clone.
  DexMethod *callee, *hot_caller, *cold_caller, *cold_caller2;
  auto* cls = create_class(
      {
          {"callee", "()V",
           R"((
                (.src_block "LFoo;.callee:()V" 0 (0.7 60))
                (const v0 1)
                (const v1 2)
                (add-int v0 v0 v1)
                (add-int v0 v0 v1)
                (return-void)
              ))"},
          {"hot_caller", "()V",
           R"((
                (.src_block "LFoo;.hot_caller:()V" 0 (1.0 100))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
          {"cold_caller", "()V",
           R"((
                (.src_block "LFoo;.cold_caller:()V" 0 (0 0))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
          {"cold_caller2", "()V",
           R"((
                (.src_block "LFoo;.cold_caller2:()V" 0 (0 0))
                (invoke-static () "LFoo;.callee:()V")
                (return-void)
              ))"},
      },
      {&callee, &hot_caller, &cold_caller, &cold_caller2});
  auto* legacy_unhashed =
      DexMethod::make_method(callee->get_class(),
                             DexString::make_string("callee$cnic$0"),
                             callee->get_proto())
          ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                          assembler::ircode_from_string(R"((
                                (return-void)
                              ))"),
                          false);
  legacy_unhashed->set_deobfuscated_name(show(legacy_unhashed));
  legacy_unhashed->get_code()->build_cfg();
  cls->add_method(legacy_unhashed);

  Scope scope{cls};
  auto baseline_profile =
      compiled({callee, hot_caller, cold_caller, cold_caller2});
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, test_config(), /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_EQ(stats.clones_created, 1u);
  auto* clone = find_invoked_method(cold_caller);
  ASSERT_NE(clone, nullptr);
  EXPECT_NE(clone, callee);
  EXPECT_NE(clone, legacy_unhashed);
  EXPECT_EQ(find_invoked_method(cold_caller2), clone);
  EXPECT_EQ(clone->get_name()->str().find("callee$cnic$0$"), 0u);
}

TEST_F(CallsiteNeverInlineCloningTest,
       StableHashCollisionIndexIsDeterministic) {
  // `aH` and `bA` intentionally collide under PartialApplication's
  // polynomial hash: 'a' * 7 + 'H' == 'b' * 7 + 'A'. List `bA` first to
  // prove that the collision index follows deterministic method order rather
  // than class insertion order.
  DexMethod *callee_ba, *callee_ah, *hot_ba, *cold_ba1, *cold_ba2, *hot_ah,
      *cold_ah1, *cold_ah2;
  auto* cls = create_class(
      {
          {"bA", "()V",
           R"((
                (.src_block "LFoo;.bA:()V" 0 (0.7 60))
                (const v0 1)
                (const v1 2)
                (add-int v0 v0 v1)
                (add-int v0 v0 v1)
                (return-void)
              ))"},
          {"aH", "()V",
           R"((
                (.src_block "LFoo;.aH:()V" 0 (0.7 60))
                (const v0 1)
                (const v1 2)
                (add-int v0 v0 v1)
                (add-int v0 v0 v1)
                (return-void)
              ))"},
          {"hot_ba", "()V",
           R"((
                (.src_block "LFoo;.hot_ba:()V" 0 (1.0 100))
                (invoke-static () "LFoo;.bA:()V")
                (return-void)
              ))"},
          {"cold_ba1", "()V",
           R"((
                (.src_block "LFoo;.cold_ba1:()V" 0 (0 0))
                (invoke-static () "LFoo;.bA:()V")
                (return-void)
              ))"},
          {"cold_ba2", "()V",
           R"((
                (.src_block "LFoo;.cold_ba2:()V" 0 (0 0))
                (invoke-static () "LFoo;.bA:()V")
                (return-void)
              ))"},
          {"hot_ah", "()V",
           R"((
                (.src_block "LFoo;.hot_ah:()V" 0 (1.0 100))
                (invoke-static () "LFoo;.aH:()V")
                (return-void)
              ))"},
          {"cold_ah1", "()V",
           R"((
                (.src_block "LFoo;.cold_ah1:()V" 0 (0 0))
                (invoke-static () "LFoo;.aH:()V")
                (return-void)
              ))"},
          {"cold_ah2", "()V",
           R"((
                (.src_block "LFoo;.cold_ah2:()V" 0 (0 0))
                (invoke-static () "LFoo;.aH:()V")
                (return-void)
              ))"},
      },
      {&callee_ba, &callee_ah, &hot_ba, &cold_ba1, &cold_ba2, &hot_ah,
       &cold_ah1, &cold_ah2});

  auto stable_hash = [](const std::string& s) {
    uint64_t hash{s.size()};
    for (auto c : s) {
      hash = hash * 7 + c;
    }
    return hash;
  };
  ASSERT_EQ(stable_hash(show(callee_ah)), stable_hash(show(callee_ba)));

  Scope scope{cls};
  auto baseline_profile = compiled({callee_ba, callee_ah, hot_ba, cold_ba1,
                                    cold_ba2, hot_ah, cold_ah1, cold_ah2});
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, test_config(), /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_EQ(stats.clones_created, 2u);
  auto* clone_ah = find_invoked_method(cold_ah1);
  auto* clone_ba = find_invoked_method(cold_ba1);
  ASSERT_NE(clone_ah, nullptr);
  ASSERT_NE(clone_ba, nullptr);
  EXPECT_EQ(find_invoked_method(cold_ah2), clone_ah);
  EXPECT_EQ(find_invoked_method(cold_ba2), clone_ba);
  EXPECT_TRUE(clone_ah->get_name()->str().ends_with("$0"));
  EXPECT_TRUE(clone_ba->get_name()->str().ends_with("$1"));
}

// --- two-phase cloning is order-independent ---

TEST_F(CallsiteNeverInlineCloningTest,
       ChainedCandidateClonesFromPreRewriteState) {
  // `x` is itself cloned (`y`'s calls to it are mixed hot/cold), and `x`'s
  // own body calls `b` -- another mixed-hotness candidate -- from a block
  // this pass proves cold. Cloning is two-phase specifically so that the
  // outcome does not depend on whether `x` or `b` gets ranked (and
  // therefore processed) first: every clone is created from the program as
  // it stood before ANY call site was rewritten, so `x`'s clone is always a
  // snapshot that still calls the ORIGINAL `b`, never `b`'s clone -- while
  // `x` itself (the original, still used by `x`'s own hot caller) gets its
  // own internal call to `b` redirected like any other cold call site.
  DexMethod *x, *b, *y_hot, *y_cold1, *y_cold2, *z_hot, *z_cold;
  auto* cls = create_class(
      {
          {"b", "()V",
           R"((
                (.src_block "LFoo;.b:()V" 0 (0.7 60))
                (const v0 1)
                (const v1 2)
                (add-int v0 v0 v1)
                (add-int v0 v0 v1)
                (return-void)
              ))"},
          {"x", "()V",
           R"((
                (.src_block "LFoo;.x:()V" 0 (0.7 60))
                (invoke-static () "LFoo;.b:()V")
                (const v0 1)
                (const v1 2)
                (add-int v0 v0 v1)
                (add-int v0 v0 v1)
                (return-void)
              ))"},
          {"y_hot", "()V",
           R"((
                (.src_block "LFoo;.y_hot:()V" 0 (1.0 100))
                (invoke-static () "LFoo;.x:()V")
                (return-void)
              ))"},
          {"y_cold1", "()V",
           R"((
                (.src_block "LFoo;.y_cold1:()V" 0 (0 0))
                (invoke-static () "LFoo;.x:()V")
                (return-void)
              ))"},
          {"y_cold2", "()V",
           R"((
                (.src_block "LFoo;.y_cold2:()V" 0 (0 0))
                (invoke-static () "LFoo;.x:()V")
                (return-void)
              ))"},
          {"z_hot", "()V",
           R"((
                (.src_block "LFoo;.z_hot:()V" 0 (1.0 100))
                (invoke-static () "LFoo;.b:()V")
                (return-void)
              ))"},
          {"z_cold", "()V",
           R"((
                (.src_block "LFoo;.z_cold:()V" 0 (0 0))
                (invoke-static () "LFoo;.b:()V")
                (return-void)
              ))"},
      },
      {&b, &x, &y_hot, &y_cold1, &y_cold2, &z_hot, &z_cold});

  Scope scope{cls};
  auto baseline_profile =
      compiled({x, b, y_hot, y_cold1, y_cold2, z_hot, z_cold});
  auto stats = CallsiteNeverInlineCloningPass::clone_mixed_hotness_callees(
      scope, test_config(), /* iteration */ 0, baseline_profile,
      empty_method_profiles());

  EXPECT_EQ(stats.mixed_hotness_callees, 2u);
  EXPECT_EQ(stats.clones_created, 2u);

  // `y`'s cold calls now reach `x`'s clone; `y_hot` still reaches original
  // `x`.
  EXPECT_EQ(find_invoked_method(y_hot), x);
  auto* x_clone = find_invoked_method(y_cold1);
  ASSERT_NE(x_clone, nullptr);
  EXPECT_NE(x_clone, x);
  EXPECT_EQ(find_invoked_method(y_cold2), x_clone);

  // `z`'s cold call now reaches `b`'s clone; `z_hot` still reaches original
  // `b`.
  EXPECT_EQ(find_invoked_method(z_hot), b);
  auto* b_clone = find_invoked_method(z_cold);
  ASSERT_NE(b_clone, nullptr);
  EXPECT_NE(b_clone, b);

  // The ORIGINAL `x`'s own internal call to `b` (a cold call site
  // contributed by `x` acting as `b`'s caller) is redirected to `b`'s
  // clone, same as any other cold call site.
  EXPECT_EQ(find_invoked_method(x), b_clone);

  // `x`'s CLONE, however, is a snapshot of `x` from before ANY call site
  // was rewritten: its own copy of that same call still targets the
  // ORIGINAL `b`, not `b`'s clone. This is what makes the outcome
  // independent of whichever of `x`/`b` this pass happened to rank (and
  // therefore clone) first.
  EXPECT_EQ(find_invoked_method(x_clone), b);
}
