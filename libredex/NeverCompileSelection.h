/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <optional>
#include <string>

#include "DeterministicContainers.h"

class DexMethod;
class IRCode;

namespace baseline_profiles {
struct BaselineProfile;
struct BaselineProfileConfig;
} // namespace baseline_profiles

namespace method_profiles {
class MethodProfiles;
} // namespace method_profiles

// The never-compile selection of a baseline profile's harvest configuration:
// methods `ArtProfileWriterPass` drops from a profile whose configuration sets
// `enable_never_compile`, so that dex2oat leaves them uncompiled. Shared so
// that a pass predicting what gets compiled cannot drift from it.
namespace never_compile_analysis {

// The interactions of `baseline_profile_config` matching its
// `never_compile_excluded_interaction_pattern`.
UnorderedSet<std::string> excluded_interaction_ids(
    const baseline_profiles::BaselineProfileConfig& baseline_profile_config);

// Which of the configuration's never-compile rules select a method.
struct NeverCompileRules {
  bool callcount{false};
  bool perf{false};
  bool called_coverage{false};
  bool strings_lookup{false};

  bool any() const {
    return callcount || perf || called_coverage || strings_lookup;
  }
};

// The rules of `baseline_profile_config` that select `method`, whose code is
// `code` with its CFG built, or nullopt when the configuration does not
// consider it: a class initializer, a method `baseline_profile` does not mark
// hot unless the configuration ignores hotness, one an excluded interaction
// calls often enough, or one with a loop.
std::optional<NeverCompileRules> select_never_compile(
    DexMethod* method,
    IRCode& code,
    const baseline_profiles::BaselineProfile& baseline_profile,
    const baseline_profiles::BaselineProfileConfig& baseline_profile_config,
    const UnorderedSet<std::string>& excluded_interaction_ids,
    const method_profiles::MethodProfiles& method_profiles);

} // namespace never_compile_analysis
