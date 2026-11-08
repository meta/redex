/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <string>

#include <gtest/gtest.h>

#include "BaselineProfile.h"
#include "BaselineProfileConfig.h"
#include "DeterministicContainers.h"
#include "DexClass.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "MethodProfiles.h"
#include "NeverCompileSelection.h"
#include "RedexTest.h"

namespace nca = never_compile_analysis;

class NeverCompileSelectionTest : public RedexTest {};

namespace {

DexMethod* make_static(const std::string& descriptor, const std::string& code) {
  auto* m = DexMethod::make_method(descriptor)
                ->make_concrete(ACC_PUBLIC | ACC_STATIC,
                                assembler::ircode_from_string(code), false);
  m->get_code()->build_cfg();
  return m;
}

const std::string kStraight = "((const v0 1) (return-void))";
const std::string kLoop =
    "((const v0 1) (:loop) (add-int v0 v0 v0) (if-nez v0 :loop) "
    "(return-void))";

// A configuration whose call-count rule selects every method the
// interactions call at most 0 times: with no interactions, all of them.
baseline_profiles::BaselineProfileConfig callcount_config() {
  baseline_profiles::BaselineProfileConfig config;
  config.harvest_config.enable_never_compile = true;
  config.harvest_config.never_compile_callcount_threshold = 0;
  return config;
}

} // namespace

// The call-count rule selects a method the profile marks hot, and a method
// with a loop or without a hot profile entry is not considered.
TEST_F(NeverCompileSelectionTest, CallcountRuleSelectsHotLoopFreeMethods) {
  auto* straight = make_static("LNeverCompileSel;.straight:()V", kStraight);
  auto* loop = make_static("LNeverCompileSel;.loop:()V", kLoop);
  auto* cold = make_static("LNeverCompileSel;.cold:()V", kStraight);
  baseline_profiles::BaselineProfile profile;
  profile.methods[straight].hot = true;
  profile.methods[loop].hot = true;
  const auto config = callcount_config();
  method_profiles::MethodProfiles method_profiles;
  const auto excluded = nca::excluded_interaction_ids(config);

  auto rules =
      nca::select_never_compile(straight, *straight->get_code(), profile,
                                config, excluded, method_profiles);
  ASSERT_TRUE(rules.has_value());
  EXPECT_TRUE(rules->callcount);
  EXPECT_TRUE(rules->any());

  EXPECT_FALSE(nca::select_never_compile(loop, *loop->get_code(), profile,
                                         config, excluded, method_profiles)
                   .has_value());
  EXPECT_FALSE(nca::select_never_compile(cold, *cold->get_code(), profile,
                                         config, excluded, method_profiles)
                   .has_value());
}

// With `never_compile_ignore_hot`, a method without a hot profile entry is
// considered too.
TEST_F(NeverCompileSelectionTest, IgnoreHotConsidersEveryMethod) {
  auto* cold = make_static("LNeverCompileSelIgnore;.cold:()V", kStraight);
  auto config = callcount_config();
  config.harvest_config.never_compile_ignore_hot = true;
  baseline_profiles::BaselineProfile profile;
  method_profiles::MethodProfiles method_profiles;
  auto rules = nca::select_never_compile(
      cold, *cold->get_code(), profile, config,
      nca::excluded_interaction_ids(config), method_profiles);
  ASSERT_TRUE(rules.has_value());
  EXPECT_TRUE(rules->callcount);
}

// No rule configured selects nothing, though the method is considered.
TEST_F(NeverCompileSelectionTest, NoRuleSelectsNothing) {
  auto* straight = make_static("LNeverCompileSelNone;.straight:()V", kStraight);
  baseline_profiles::BaselineProfileConfig config;
  config.harvest_config.enable_never_compile = true;
  baseline_profiles::BaselineProfile profile;
  profile.methods[straight].hot = true;
  method_profiles::MethodProfiles method_profiles;
  auto rules = nca::select_never_compile(
      straight, *straight->get_code(), profile, config,
      nca::excluded_interaction_ids(config), method_profiles);
  ASSERT_TRUE(rules.has_value());
  EXPECT_FALSE(rules->any());
}

// The excluded interactions are the ones whose name the pattern matches.
TEST_F(NeverCompileSelectionTest, ExcludedInteractionsMatchThePattern) {
  baseline_profiles::BaselineProfileConfig config;
  config.interactions = {{"1", "ColdStart"}, {"2", "Scroll"}, {"3", "Cold"}};
  config.harvest_config.never_compile_excluded_interaction_pattern = "Cold.*";
  const auto excluded = nca::excluded_interaction_ids(config);
  EXPECT_EQ(excluded.size(), 2u);
  EXPECT_EQ(excluded.count("1"), 1u);
  EXPECT_EQ(excluded.count("3"), 1u);
}
