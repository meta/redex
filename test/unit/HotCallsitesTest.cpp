/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <string>

#include <gtest/gtest.h>

#include "BaselineProfile.h"
#include "Creators.h"
#include "DexClass.h"
#include "HotCallsites.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "MethodProfiles.h"
#include "RedexTest.h"
#include "TypeUtil.h"

namespace nia = never_inline_analysis;

class HotCallsitesTest : public RedexTest {};

namespace {

DexMethod* make_static(ClassCreator& cc,
                       const std::string& descriptor,
                       const std::string& code) {
  auto* m = DexMethod::make_method(descriptor)
                ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                                assembler::ircode_from_string(code), false);
  m->get_code()->build_cfg();
  cc.add_method(m);
  return m;
}

// A callee of four instructions, which no rule refuses for its shape.
const std::string kCalleeBody = R"((
  (load-param v0)
  (add-int v1 v0 v0)
  (add-int v1 v1 v0)
  (add-int v1 v1 v0)
  (add-int v1 v1 v0)
  (return-void)
))";

std::string call(const std::string& callee) {
  return "(invoke-static (v0) \"" + callee + "\")";
}

nia::HotCallsiteThresholds thresholds(float hot_block_appear_threshold) {
  return nia::HotCallsiteThresholds{
      .hot_block_appear_threshold = hot_block_appear_threshold,
      .hot_method_appear_threshold = nia::kDefaultAppearThreshold,
      .max_caller_instructions = nia::kDefaultMaxCallerInstructions,
      .max_caller_registers = nia::kDefaultMaxCallerRegisters,
  };
}

nia::NeverInlineCriteria criteria() {
  return nia::NeverInlineCriteria{
      .max_callee_code_units = nia::kDefaultMaxCalleeCodeUnits,
      .min_callee_instructions = nia::kDefaultMinCalleeInstructions,
      .min_hot_callsites = nia::kDefaultMinHotCallsites,
      .min_hot_callsites_min_code_units =
          nia::kDefaultMinHotCallsitesMinCodeUnits,
  };
}

} // namespace

// A compiled caller's call sites split into hot and not hot; an uncompiled
// caller's are not read.
TEST_F(HotCallsitesTest, ClassifiesCompiledCallersSites) {
  ClassCreator cc{DexType::make_type("LHotCallsites;")};
  cc.set_super(type::java_lang_Object());
  const std::string callee_name = "LHotCallsites;.callee:(I)V";
  auto* callee = make_static(cc, callee_name, kCalleeBody);
  auto* hot_caller =
      make_static(cc, "LHotCallsites;.hot:()V",
                  R"(((.src_block "" 0 (1.0 100)) (const v0 0))" +
                      call(callee_name) + call(callee_name) + "(return-void))");
  auto* cold_caller = make_static(cc, "LHotCallsites;.cold:()V",
                                  R"(((.src_block "" 0 (0 0)) (const v0 0))" +
                                      call(callee_name) + "(return-void))");
  make_static(cc, "LHotCallsites;.uncompiled:()V",
              "((const v0 0)" + call(callee_name) + "(return-void))");
  Scope scope{cc.create()};

  baseline_profiles::BaselineProfile profile;
  profile.methods[hot_caller].hot = true;
  profile.methods[cold_caller].hot = true;
  profile.methods[callee].hot = true;
  method_profiles::MethodProfiles method_profiles;
  nia::HotCallsites callsites(scope, profile, method_profiles,
                              thresholds(/*hot_block_appear_threshold=*/50));

  EXPECT_EQ(callsites.hot_callsite_counts.load(callee), 2u);
  EXPECT_EQ(callsites.hot_cold_callees.count_unsafe(callee), 1u);
}

// The writer's decision, rule by rule.
TEST_F(HotCallsitesTest, DecidesNeverInlineAsTheWriter) {
  auto code = assembler::ircode_from_string(kCalleeBody);
  code->build_cfg();
  using D = nia::NeverInlineDecision;
  EXPECT_EQ(nia::decide_never_inline(*code, true, true, 0, criteria()).decision,
            D::kAlreadyNeverInline);
  EXPECT_EQ(
      nia::decide_never_inline(*code, false, false, 0, criteria()).decision,
      D::kNoCandidate);
  EXPECT_EQ(
      nia::decide_never_inline(*code, false, true, 1, criteria()).decision,
      D::kTooHot);
  EXPECT_EQ(
      nia::decide_never_inline(*code, false, true, 0, criteria()).decision,
      D::kAnnotate);
  auto large = criteria();
  large.max_callee_code_units = 2;
  auto verdict = nia::decide_never_inline(*code, false, true, 0, large);
  EXPECT_EQ(verdict.decision, D::kIneligible);
  EXPECT_EQ(verdict.ineligibility, nia::Ineligibility::kTooLarge);
  auto min_hot = criteria();
  min_hot.min_hot_callsites = 1;
  verdict = nia::decide_never_inline(*code, false, false, 3, min_hot);
  EXPECT_EQ(verdict.decision, D::kAnnotate);
  EXPECT_TRUE(verdict.min_hot_callsites_rule_met);
}
