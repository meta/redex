/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

// Genuine two-pass proof: runs the actual, unmodified
// `CallsiteNeverInlineCloningPass::run_pass` and
// `ArtProfileWriterPass::run_pass` through a real `PassManager`/`ConfigFiles`,
// with register allocation between them in the register-budget cases, on a
// hand-built (no dexfile, no BUCK def_integ_test) fixture -- so this fails if
// the clone ever stops reaching
// `ArtProfileWriterPass`'s own `hot_cold_callees` bucket, or if that pass's
// own annotation logic ever starts vetoing it, not just if the two passes'
// shape-eligibility checks (already covered by
// `never_inline_analysis::never_inline_eligibility`'s own tests) disagree.

#include <algorithm>
#include <array>
#include <fstream>
#include <string>

#include <gtest/gtest.h>
#include <json/value.h>

#include "ArtProfileWriterPass.h"
#include "CallsiteNeverInlineCloningPass.h"
#include "ControlFlow.h"
#include "Creators.h"
#include "DexAccess.h"
#include "DexClass.h"
#include "DexUtil.h"
#include "IRAssembler.h"
#include "IRMetaIO.h"
#include "MethodProfiles.h"
#include "PassManager.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"
#include "RegAlloc.h"
#include "Show.h"

namespace {

DexMethod* find_invoked_method(DexMethod* caller) {
  // `PassManager::run_passes` clears every method's CFG back to linear IRList
  // form once every pass has finished (so the pipeline can proceed to DEX
  // output); a caller inspecting the result after `run_passes` returns must
  // walk that linear form, not a (by then absent) CFG.
  for (auto& mie : InstructionIterable(*caller->get_code())) {
    if (opcode::is_an_invoke(mie.insn->opcode())) {
      return mie.insn->get_method()->as_def();
    }
  }
  return nullptr;
}

bool profile_has_hot_cnic_method(const std::string& path) {
  std::ifstream input(path);
  if (!input.is_open()) {
    ADD_FAILURE() << "Unable to open baseline profile: " << path;
    return false;
  }
  std::string line;
  while (std::getline(input, line)) {
    if (line.starts_with("H") && line.find("$cnic$") != std::string::npos) {
      return true;
    }
  }
  return false;
}

// A callee reached from one hot and two cold call sites -- "mixed-hotness"
// in this pass's own terms -- built directly with `ClassCreator`, entirely
// independent of any dexfile or BUCK `def_integ_test` fixture.
struct MixedHotnessFixture {
  DexMethod* callee;
  DexMethod* hot_caller;
  DexMethod* cold_caller1;
  DexMethod* cold_caller2;
  std::vector<DexStore> stores;
};

MixedHotnessFixture make_mixed_hotness_fixture(size_t caller_registers = 0,
                                               size_t hot_parameters = 0,
                                               size_t cold_parameters = 0) {
  ClassCreator cc{DexType::make_type("LCnicE2e;")};
  cc.set_super(type::java_lang_Object());

  // A sizable, non-trivial body -- shape-eligible for both passes (has a
  // return block, within the code-unit/instruction bounds, not a trivial
  // forwarder).
  std::ostringstream callee_code;
  callee_code << "(\n  (.src_block \"LCnicE2e;.callee:()V\" 0 (0.7 60))\n"
                 "  (const v0 1)\n";
  for (size_t i = 0; i < 14; i++) {
    callee_code << "  (add-int v0 v0 v0)\n";
  }
  callee_code << "  (return-void)\n)";
  auto* callee =
      DexMethod::make_method("LCnicE2e;.callee:()V")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                          assembler::ircode_from_string(callee_code.str()),
                          false);
  callee->set_deobfuscated_name(show(callee));
  callee->get_code()->build_cfg();
  cc.add_method(callee);

  std::string register_use;
  if (caller_registers != 0) {
    register_use =
        "  (const v" + std::to_string(caller_registers - 1) + " 0)\n";
  }
  auto make_caller = [&](const std::string& name, const std::string& profile,
                         size_t parameter_registers) {
    std::string parameters;
    for (size_t i = 0; i < parameter_registers; ++i) {
      parameters += "  (load-param v" + std::to_string(i) + ")\n";
    }
    std::string caller_proto =
        "(" + std::string(parameter_registers, 'I') + ")V";
    std::string descriptor = "LCnicE2e;." + name + ":" + caller_proto;
    auto* m = DexMethod::make_method(descriptor)
                  ->make_concrete(
                      ACC_PUBLIC | ACC_STATIC,
                      assembler::ircode_from_string(
                          "(\n" + parameters + "  (.src_block \"" + descriptor +
                          "\" 0 " + profile + ")\n" + register_use +
                          "  (invoke-static () \"LCnicE2e;.callee:()V\")\n"
                          "  (return-void)\n)"),
                      false);
    m->set_deobfuscated_name(show(m));
    m->get_code()->build_cfg();
    cc.add_method(m);
    return m;
  };
  auto* hot_caller = make_caller("hot_caller", "(1.0 100)", hot_parameters);
  auto* cold_caller1 = make_caller("cold_caller1", "(0 0)", cold_parameters);
  auto* cold_caller2 = make_caller("cold_caller2", "(0 0)", cold_parameters);

  DexStore store("classes");
  store.add_classes({cc.create()});
  std::vector<DexStore> stores;
  stores.emplace_back(std::move(store));

  return MixedHotnessFixture{callee, hot_caller, cold_caller1, cold_caller2,
                             std::move(stores)};
}

// `ConfigFiles::get_baseline_profile_configs()` always carries a "default"
// entry (`ConfigFiles.cpp` inserts one unconditionally when no
// `baseline_profile` json key is present), and
// `baseline_profiles::get_baseline_profiles()` derives its "manual" baseline
// profile for that entry from three fixed, config-independent
// method-profiles interaction ids ("manual_startup"/"manual_post_startup"/
// "manual_hot") -- exactly the mechanism this helper drives, so every pass
// reading `ConfigFiles` sees the same "compiled" methods without a real
// baseline-profile file or agg_method_stats CSV.
void mark_compiled(ConfigFiles& conf, const std::vector<DexMethod*>& methods) {
  method_profiles::Stats hot_stats;
  hot_stats.appear_percent = 100.0;
  hot_stats.call_count = 100.0;
  UnorderedMap<const DexMethodRef*, method_profiles::Stats> manual_hot_stats;
  for (auto* m : methods) {
    manual_hot_stats[m] = hot_stats;
  }
  conf.get_method_profiles() = method_profiles::MethodProfiles::initialize(
      "manual_hot", manual_hot_stats);
}

// A NON-FINAL virtual callee, in a non-final class, that no other method
// anywhere in the fixture overrides -- a "non-true-virtual" -- reached from
// one hot and two cold call sites via `invoke-virtual`. Otherwise identical
// in shape to `MixedHotnessFixture`.
struct NonFinalVirtualMixedHotnessFixture {
  DexMethod* callee;
  DexMethod* hot_caller;
  DexMethod* cold_caller1;
  DexMethod* cold_caller2;
  std::vector<DexStore> stores;
};

NonFinalVirtualMixedHotnessFixture
make_non_final_virtual_mixed_hotness_fixture() {
  ClassCreator cc{DexType::make_type("LCnicE2eVirtual;")};
  cc.set_super(type::java_lang_Object());

  std::ostringstream callee_code;
  callee_code << "(\n  (load-param-object v0)\n"
                 "  (.src_block \"LCnicE2eVirtual;.callee:()V\" 0 (0.7 60))\n"
                 "  (const v1 1)\n";
  for (size_t i = 0; i < 14; i++) {
    callee_code << "  (add-int v1 v1 v1)\n";
  }
  callee_code << "  (return-void)\n)";
  auto* callee =
      DexMethod::make_method("LCnicE2eVirtual;.callee:()V")
          ->make_concrete(ACC_PUBLIC,
                          assembler::ircode_from_string(callee_code.str()),
                          /* is_virtual */ true);
  callee->set_deobfuscated_name(show(callee));
  callee->get_code()->build_cfg();
  cc.add_method(callee);

  auto make_caller = [&](const std::string& name, const std::string& sb) {
    auto* m =
        DexMethod::make_method("LCnicE2eVirtual;." + name +
                               ":(LCnicE2eVirtual;)V")
            ->make_concrete(
                ACC_PUBLIC | ACC_STATIC,
                assembler::ircode_from_string(
                    "(\n  (load-param-object v0)\n  (.src_block \"" +
                    std::string("LCnicE2eVirtual;.") + name +
                    ":(LCnicE2eVirtual;)V\" 0 " + sb +
                    ")\n"
                    "  (invoke-virtual (v0) \"LCnicE2eVirtual;.callee:()V\")\n"
                    "  (return-void)\n)"),
                false);
    m->set_deobfuscated_name(show(m));
    m->get_code()->build_cfg();
    cc.add_method(m);
    return m;
  };
  auto* hot_caller = make_caller("hot_caller", "(1.0 100)");
  auto* cold_caller1 = make_caller("cold_caller1", "(0 0)");
  auto* cold_caller2 = make_caller("cold_caller2", "(0 0)");

  DexStore store("classes");
  store.add_classes({cc.create()});
  std::vector<DexStore> stores;
  stores.emplace_back(std::move(store));

  return NonFinalVirtualMixedHotnessFixture{callee, hot_caller, cold_caller1,
                                            cold_caller2, std::move(stores)};
}

} // namespace

class CallsiteNeverInlineCloningEndToEndTest : public RedexTest {};

struct CallerRegisterCase {
  size_t virtual_registers;
  size_t hot_parameters;
  size_t cold_parameters;
  bool annotated;
};

class CallsiteNeverInlineCloningRegisterTest
    : public CallsiteNeverInlineCloningEndToEndTest,
      public ::testing::WithParamInterface<CallerRegisterCase> {};

TEST_F(CallsiteNeverInlineCloningEndToEndTest, RejectsLegacyIRMetadataLayout) {
  auto tmp_dir = redex::make_tmp_dir("cnic_old_irmeta_%%%%%%%%");
  std::ofstream output(tmp_dir.path + "/irmeta.bin", std::ios::binary);
  ASSERT_TRUE(output.is_open());
  // Include the trailing NUL in the legacy IRMeta header.
  constexpr std::array<char, 8> old_header = {'r',  'd',    'x',    '.',
                                              '\n', '\x14', '\x12', '\0'};
  output.write(old_header.data(), old_header.size());
  const uint32_t zero = 0;
  const uint32_t old_rstate_size = 4;
  output.write(reinterpret_cast<const char*>(&zero), sizeof(zero));
  output.write(reinterpret_cast<const char*>(&zero), sizeof(zero));
  output.write(reinterpret_cast<const char*>(&zero), sizeof(zero));
  output.write(reinterpret_cast<const char*>(&old_rstate_size),
               sizeof(old_rstate_size));
  ASSERT_TRUE(output.good());
  output.close();

  EXPECT_FALSE(ir_meta_io::load(tmp_dir.path));
}

TEST_F(CallsiteNeverInlineCloningEndToEndTest,
       ForceHotAndStartupBitsSurviveIRMetadataRoundTrip) {
  auto fx = make_mixed_hotness_fixture();
  auto scope = build_class_scope(fx.stores);
  auto tmp_dir = redex::make_tmp_dir("cnic_irmeta_%%%%%%%%");
  fx.callee->rstate.set_force_hot_in_baseline_profile();
  fx.callee->rstate.set_force_startup_in_baseline_profile();

  ir_meta_io::dump(scope, tmp_dir.path);
  fx.callee->rstate.reset_force_hot_in_baseline_profile();
  fx.callee->rstate.reset_force_startup_in_baseline_profile();
  ASSERT_FALSE(fx.callee->rstate.force_hot_in_baseline_profile());
  ASSERT_FALSE(fx.callee->rstate.force_startup_in_baseline_profile());
  ASSERT_TRUE(ir_meta_io::load(tmp_dir.path));
  EXPECT_TRUE(fx.callee->rstate.force_hot_in_baseline_profile());
  EXPECT_TRUE(fx.callee->rstate.force_startup_in_baseline_profile());
}

TEST_F(CallsiteNeverInlineCloningEndToEndTest,
       ForcedHotAndStartupFlagsAreAppliedIndependently) {
  auto fx = make_mixed_hotness_fixture();
  auto scope = build_class_scope(fx.stores);
  fx.callee->rstate.set_force_hot_in_baseline_profile();
  fx.hot_caller->rstate.set_force_startup_in_baseline_profile();

  baseline_profiles::BaselineProfile profile;
  profile.methods[fx.callee].post_startup = true;
  EXPECT_EQ(baseline_profiles::apply_forced_method_flags(scope, &profile), 2u);
  const auto& hot_flags = profile.methods.at(fx.callee);
  EXPECT_TRUE(hot_flags.hot);
  EXPECT_FALSE(hot_flags.startup);
  EXPECT_TRUE(hot_flags.post_startup);
  const auto& startup_flags = profile.methods.at(fx.hot_caller);
  EXPECT_FALSE(startup_flags.hot);
  EXPECT_TRUE(startup_flags.startup);
  EXPECT_FALSE(startup_flags.post_startup);
  EXPECT_EQ(baseline_profiles::apply_forced_method_flags(scope, &profile), 0u);
}

TEST_F(CallsiteNeverInlineCloningEndToEndTest,
       ForcedMethodEntersEveryMaterializedProfile) {
  auto fx = make_mixed_hotness_fixture();
  auto scope = build_class_scope(fx.stores);
  fx.callee->rstate.set_force_hot_in_baseline_profile();

  // CNIC, like existing profile-guided inlining and outlining, makes one
  // whole-program structural decision from aggregated profile information. It
  // does not materialize a different transformed program for each ART profile,
  // so the forced flag follows that global decision into every profile.
  baseline_profiles::BaselineProfile first_profile;
  baseline_profiles::BaselineProfile second_profile;
  EXPECT_EQ(baseline_profiles::apply_forced_method_flags(scope, &first_profile),
            1u);
  EXPECT_EQ(
      baseline_profiles::apply_forced_method_flags(scope, &second_profile), 1u);
  EXPECT_TRUE(first_profile.methods.at(fx.callee).hot);
  EXPECT_TRUE(second_profile.methods.at(fx.callee).hot);
}

TEST_F(CallsiteNeverInlineCloningEndToEndTest,
       ForcedMethodIsAppliedEvenAfterItsCodeIsReleased) {
  auto fx = make_mixed_hotness_fixture();
  auto scope = build_class_scope(fx.stores);
  fx.callee->rstate.set_force_hot_in_baseline_profile();
  // Forced profile bits live on `ReferencedState`, so they remain valid after
  // `IRCode` is released; a code walker would miss this method.
  auto released = fx.callee->release_code();
  ASSERT_EQ(fx.callee->get_code(), nullptr);

  baseline_profiles::BaselineProfile profile;
  EXPECT_EQ(baseline_profiles::apply_forced_method_flags(scope, &profile), 1u);
  EXPECT_TRUE(profile.methods.at(fx.callee).hot);

  fx.callee->set_code(std::move(released));
}

TEST_P(CallsiteNeverInlineCloningRegisterTest,
       CloningAndAnnotationUseTheirOwnRegisterPhase) {
  const auto& c = GetParam();
  auto fx = make_mixed_hotness_fixture(c.virtual_registers, c.hot_parameters,
                                       c.cold_parameters);
  std::vector<DexMethod*> callers{fx.hot_caller, fx.cold_caller1,
                                  fx.cold_caller2};
  for (auto* caller : callers) {
    auto params =
        caller == fx.hot_caller ? c.hot_parameters : c.cold_parameters;
    ASSERT_EQ(caller->get_code()->cfg().get_registers_size(),
              std::max(c.virtual_registers, params));
  }

  // A permissive CallsiteNeverInlineCloningPass config (mirrors this pass's
  // own test suite's `test_config()`), and
  // `never_inline_attach_annotations=true` on ArtProfileWriterPass, which
  // defaults to false (a dry classification run that never touches
  // bytecode).
  Json::Value json_conf;
  json_conf["CallsiteNeverInlineCloningPass"]["hot_block_appear_threshold"] =
      80.0;
  json_conf["CallsiteNeverInlineCloningPass"]["hot_method_appear_threshold"] =
      20.0;
  json_conf["CallsiteNeverInlineCloningPass"]["min_hot_callsites"] = 1;
  json_conf["CallsiteNeverInlineCloningPass"]["min_cold_callsites"] = 2;
  json_conf["CallsiteNeverInlineCloningPass"]
           ["min_estimated_oat_code_units_saved"] = 0;
  json_conf["CallsiteNeverInlineCloningPass"]["method_ref_cost"] = 0;
  json_conf["ArtProfileWriterPass"]["never_inline_attach_annotations"] = true;

  ConfigFiles conf(json_conf);
  conf.parse_global_config();
  auto tmp_dir = redex::make_tmp_dir("cnic_e2e_%%%%%%%%");
  conf.set_outdir(tmp_dir.path);
  mark_compiled(conf,
                {fx.callee, fx.hot_caller, fx.cold_caller1, fx.cold_caller2});

  CallsiteNeverInlineCloningPass cnic_pass;
  regalloc::RegAllocPass regalloc_pass;
  ArtProfileWriterPass apw_pass;
  PassManager manager({&cnic_pass, &regalloc_pass, &apw_pass}, conf,
                      RedexOptions{});
  manager.run_passes(fx.stores, conf);

  for (const auto& info : manager.get_pass_info()) {
    if (info.pass == &apw_pass) {
      EXPECT_EQ(
          info.metrics.at("never_inline_callers_too_many_registers"),
          (c.hot_parameters > 32 ? 1 : 0) + (c.cold_parameters > 32 ? 2 : 0));
    }
  }
  auto* never_inline_anno = type::dalvik_annotation_optimization_NeverInline();
  for (auto* caller : callers) {
    auto params =
        caller == fx.hot_caller ? c.hot_parameters : c.cold_parameters;
    EXPECT_GE(caller->get_code()->get_registers_size(), params);
    if (params <= 32) {
      EXPECT_LE(caller->get_code()->get_registers_size(), 32u);
    } else {
      EXPECT_GT(caller->get_code()->get_registers_size(), 32u);
    }
  }

  // The hot caller keeps calling the original; both cold callers are
  // redirected, so the original has no eligible cold call site.
  EXPECT_EQ(find_invoked_method(fx.hot_caller), fx.callee);
  EXPECT_FALSE(has_anno(fx.callee, never_inline_anno));

  // Both cold callers call a clone. The writer annotates it only if the
  // callers' allocated frames pass its register budget.
  auto* clone = find_invoked_method(fx.cold_caller1);
  ASSERT_NE(clone, nullptr);
  EXPECT_NE(clone, fx.callee);
  EXPECT_EQ(find_invoked_method(fx.cold_caller2), clone);
  EXPECT_EQ(has_anno(clone, never_inline_anno), c.annotated);
  EXPECT_TRUE(clone->rstate.force_hot_in_baseline_profile());
  EXPECT_FALSE(clone->rstate.force_startup_in_baseline_profile());
  EXPECT_TRUE(profile_has_hot_cnic_method(
      tmp_dir.path + "/meta/additional-baseline-profiles.list"));
}

INSTANTIATE_TEST_SUITE_P(VirtualCallerRegisters,
                         CallsiteNeverInlineCloningRegisterTest,
                         ::testing::Values(CallerRegisterCase{0, 0, 0, true},
                                           CallerRegisterCase{32, 0, 0, true},
                                           CallerRegisterCase{33, 0, 0, true},
                                           CallerRegisterCase{128, 0, 0, true},
                                           CallerRegisterCase{0, 32, 32, true},
                                           CallerRegisterCase{0, 33, 33, false},
                                           CallerRegisterCase{0, 33, 0, true}));

TEST_F(CallsiteNeverInlineCloningEndToEndTest,
       ArtProfileWriterAloneNeverAnnotatesTheMixedHotnessOriginal) {
  // The negative control: without CallsiteNeverInlineCloningPass running
  // first, ArtProfileWriterPass on its own -- unmodified, same
  // `never_inline_attach_annotations=true` -- refuses to annotate a callee
  // that still has a call site it cannot prove cold. This is the exact
  // conflict CallsiteNeverInlineCloningPass exists to resolve; this test
  // proves ArtProfileWriterPass really does have that veto on its own, so
  // the other test's "unannotated original" outcome is not a vacuous
  // assertion.
  auto fx = make_mixed_hotness_fixture();

  Json::Value json_conf;
  json_conf["ArtProfileWriterPass"]["never_inline_attach_annotations"] = true;

  ConfigFiles conf(json_conf);
  conf.parse_global_config();
  auto tmp_dir = redex::make_tmp_dir("cnic_e2e_%%%%%%%%");
  conf.set_outdir(tmp_dir.path);
  mark_compiled(conf,
                {fx.callee, fx.hot_caller, fx.cold_caller1, fx.cold_caller2});

  ArtProfileWriterPass apw_pass;
  PassManager manager({&apw_pass}, conf, RedexOptions{});
  manager.run_passes(fx.stores, conf);

  auto* never_inline_anno = type::dalvik_annotation_optimization_NeverInline();
  EXPECT_FALSE(has_anno(fx.callee, never_inline_anno));
  EXPECT_EQ(find_invoked_method(fx.hot_caller), fx.callee);
  EXPECT_EQ(find_invoked_method(fx.cold_caller1), fx.callee);
  EXPECT_EQ(find_invoked_method(fx.cold_caller2), fx.callee);
}

TEST_F(CallsiteNeverInlineCloningEndToEndTest,
       NonFinalNonTrueVirtualCloneIsMarkedFinalAndAnnotated) {
  // A non-final virtual callee that no other method overrides (a
  // "non-true-virtual") is only eligible for cloning at all because of
  // CallsiteNeverInlineCloningPass's own MethodOverrideGraph-based
  // eligibility check -- but its clone, left at the original's own
  // non-final access flags, would itself be invisible to
  // ArtProfileWriterPass's narrower `is_final(method) || is_final(cls)`
  // virtual-eligibility check. This proves the fix holds end to end: the
  // clone is marked `final` (collision-checked first), stays virtual,
  // public, and reachable via the exact same `invoke-virtual` opcode its
  // callers already used, and ArtProfileWriterPass genuinely annotates it.
  auto fx = make_non_final_virtual_mixed_hotness_fixture();
  ASSERT_FALSE(is_final(fx.callee));
  ASSERT_FALSE(is_final(type_class(fx.callee->get_class())));

  Json::Value json_conf;
  json_conf["CallsiteNeverInlineCloningPass"]["hot_block_appear_threshold"] =
      80.0;
  json_conf["CallsiteNeverInlineCloningPass"]["hot_method_appear_threshold"] =
      20.0;
  json_conf["CallsiteNeverInlineCloningPass"]["min_hot_callsites"] = 1;
  json_conf["CallsiteNeverInlineCloningPass"]["min_cold_callsites"] = 2;
  json_conf["CallsiteNeverInlineCloningPass"]
           ["min_estimated_oat_code_units_saved"] = 0;
  json_conf["CallsiteNeverInlineCloningPass"]["method_ref_cost"] = 0;
  json_conf["ArtProfileWriterPass"]["never_inline_attach_annotations"] = true;

  ConfigFiles conf(json_conf);
  conf.parse_global_config();
  auto tmp_dir = redex::make_tmp_dir("cnic_e2e_%%%%%%%%");
  conf.set_outdir(tmp_dir.path);
  mark_compiled(conf,
                {fx.callee, fx.hot_caller, fx.cold_caller1, fx.cold_caller2});

  CallsiteNeverInlineCloningPass cnic_pass;
  ArtProfileWriterPass apw_pass;
  PassManager manager({&cnic_pass, &apw_pass}, conf, RedexOptions{});
  manager.run_passes(fx.stores, conf);

  auto* never_inline_anno = type::dalvik_annotation_optimization_NeverInline();

  EXPECT_EQ(find_invoked_method(fx.hot_caller), fx.callee);
  EXPECT_FALSE(has_anno(fx.callee, never_inline_anno));
  EXPECT_FALSE(is_final(fx.callee));

  auto* clone = find_invoked_method(fx.cold_caller1);
  ASSERT_NE(clone, nullptr);
  EXPECT_NE(clone, fx.callee);
  EXPECT_EQ(find_invoked_method(fx.cold_caller2), clone);
  // Preserved unchanged from the original.
  EXPECT_TRUE(clone->is_virtual());
  EXPECT_TRUE(is_public(clone));
  // The one access-flag change this pass makes for exactly this category of
  // candidate.
  EXPECT_TRUE(is_final(clone));
  EXPECT_TRUE(has_anno(clone, never_inline_anno));
}
