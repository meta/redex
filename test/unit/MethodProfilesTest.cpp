/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "MethodProfiles.h"

#include <algorithm>
#include <bit>
#include <cstdint>

#include "BaselineProfile.h"
#include "Creators.h"
#include "GlobalConfig.h"
#include "RedexTest.h"
#include "TypeUtil.h"

using namespace method_profiles;

class MethodProfilesTest : public RedexTest {
 protected:
  DexMethod* make_method(const std::string& name) {
    return DexMethod::make_method("LProfiles;." + name + ":()V")
        ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  }

  void expect_same_stats(const Stats& a, const Stats& b) {
    EXPECT_EQ(std::bit_cast<uint64_t>(a.appear_percent),
              std::bit_cast<uint64_t>(b.appear_percent));
    EXPECT_EQ(std::bit_cast<uint64_t>(a.call_count),
              std::bit_cast<uint64_t>(b.call_count));
    EXPECT_EQ(std::bit_cast<uint64_t>(a.order_percent),
              std::bit_cast<uint64_t>(b.order_percent));
    EXPECT_EQ(a.min_api_level, b.min_api_level);
  }

  void check_permutations(bool substitute) {
    auto* a = make_method("a");
    auto* b = make_method("b");
    auto* c = make_method("c");
    auto* target = make_method("target");
    auto profiles =
        MethodProfiles::initialize(COLD_START, {{a, {0.1, 0.1, 30.0, 23}},
                                                {b, {0.2, 0.2, 20.0, 21}},
                                                {c, {0.3, 0.3, 10.0, 22}}});
    std::vector<DexMethod*> sources{a, b, c};
    std::optional<Stats> expected;
    do {
      auto permutation_profiles = MethodProfiles::initialize(
          COLD_START, profiles.method_stats(COLD_START));
      const auto original_sources = sources;
      auto changed =
          substitute ? permutation_profiles.substitute_stats(target, sources)
                     : permutation_profiles.derive_stats(target, sources);
      EXPECT_EQ(changed, 1u);
      EXPECT_EQ(sources, original_sources);
      auto stats = permutation_profiles.get_method_stat(COLD_START, target);
      ASSERT_TRUE(stats);
      if (expected) {
        expect_same_stats(*expected, *stats);
      } else {
        expected = stats;
      }
      EXPECT_EQ(stats->order_percent, 10.0);
      EXPECT_EQ(stats->min_api_level, 21);
      if (!substitute) {
        EXPECT_EQ(stats->appear_percent, 0.3);
      }
      for (auto* source : sources) {
        expect_same_stats(
            *profiles.get_method_stat(COLD_START, source),
            *permutation_profiles.get_method_stat(COLD_START, source));
      }
    } while (std::next_permutation(sources.begin(), sources.end(),
                                   compare_dexmethods));
  }

  void check_profile_threshold(bool substitute) {
    auto* a = make_method("a");
    auto* b = make_method("b");
    auto* c = make_method("c");
    auto* target = make_method("target");
    target->set_code(assembler::ircode_from_string("((return-void))"));
    target->get_code()->build_cfg();
    ClassCreator creator(target->get_class());
    creator.set_super(type::java_lang_Object());
    creator.add_method(target);
    Scope scope{creator.create()};
    baseline_profiles::BaselineProfileConfig config{};
    config.interaction_configs[COLD_START] = {};
    baseline_profiles::BaselineProfileConfigMap configs{{"default", config}};
    std::vector<DexMethod*> sources{a, b, c};
    do {
      auto profiles =
          MethodProfiles::initialize(COLD_START, {{a, {90.0, 0.1, 10.0, 21}},
                                                  {b, {90.0, 0.2, 10.0, 21}},
                                                  {c, {90.0, 0.7, 10.0, 21}}});
      if (substitute) {
        profiles.substitute_stats(target, sources);
      } else {
        profiles.derive_stats(target, sources);
      }
      auto profile = baseline_profiles::get_default_baseline_profile(
          scope, configs, profiles, /* coldstart_classes */ {},
          baseline_profiles::DEFAULT_ART_HUGE_METHOD_MAX);
      auto it = profile.methods.find(target);
      ASSERT_NE(it, profile.methods.end());
      EXPECT_TRUE(it->second.hot);
    } while (std::next_permutation(sources.begin(), sources.end(),
                                   compare_dexmethods));
  }
};

TEST_F(MethodProfilesTest, derive_stats_is_order_independent) {
  check_permutations(false);
}

TEST_F(MethodProfilesTest, substitute_stats_is_order_independent) {
  check_permutations(true);
}

TEST_F(MethodProfilesTest, derived_profile_membership_is_order_independent) {
  check_profile_threshold(false);
}

TEST_F(MethodProfilesTest,
       substituted_profile_membership_is_order_independent) {
  check_profile_threshold(true);
}

TEST_F(MethodProfilesTest, preserves_missing_duplicate_and_existing_sources) {
  auto* a = make_method("a");
  auto* missing = make_method("missing");
  auto* target = make_method("target");
  const Stats original{20.0, 0.5, 30.0, 21};
  auto profiles = MethodProfiles::initialize(COLD_START, {{a, original}});
  EXPECT_EQ(profiles.derive_stats(target, {}), 0u);
  EXPECT_FALSE(profiles.get_method_stat(COLD_START, target));
  EXPECT_EQ(profiles.derive_stats(target, {missing, a, nullptr, a}), 1u);
  expect_same_stats(*profiles.get_method_stat(COLD_START, target),
                    Stats{20.0, 1.0, 30.0, 21});
  EXPECT_EQ(profiles.derive_stats(target, {a}), 0u);
  EXPECT_EQ(profiles.substitute_stats(target, {a, a, missing, nullptr}), 1u);
  expect_same_stats(*profiles.get_method_stat(COLD_START, target),
                    Stats{40.0, 1.0, 30.0, 21});
  EXPECT_EQ(profiles.substitute_stats(target, {a, a}), 0u);
  EXPECT_EQ(profiles.substitute_stats(target, {target, a}), 1u);
  expect_same_stats(*profiles.get_method_stat(COLD_START, target),
                    Stats{60.0, 1.5, 30.0, 21});
  EXPECT_EQ(profiles.substitute_stats(target, {missing}), 1u);
  EXPECT_FALSE(profiles.get_method_stat(COLD_START, target));
  EXPECT_EQ(profiles.substitute_stats(target, {}), 0u);
  expect_same_stats(*profiles.get_method_stat(COLD_START, a), original);
}
