/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <cstddef>

#include "ConcurrentContainers.h"
#include "DexClass.h"

namespace baseline_profiles {
struct BaselineProfile;
} // namespace baseline_profiles

namespace method_profiles {
class MethodProfiles;
} // namespace method_profiles

namespace never_inline_analysis {

// The bounds of the call-site classification below. The caller bounds each
// shadow a threshold inside ART's own inliner; the appear thresholds say which
// call sites count as hot, a negative one leaving its check out.
struct HotCallsiteThresholds {
  float hot_block_appear_threshold;
  float hot_method_appear_threshold;
  size_t max_caller_instructions;
  size_t max_caller_registers;
};

// `ArtProfileWriterPass`'s defaults for these bounds, which its doc strings
// explain, for a pass that reads the configuration that pass runs with.
inline constexpr float kDefaultAppearThreshold = -1.0f;
inline constexpr size_t kDefaultMaxCallerInstructions = 1100;
inline constexpr size_t kDefaultMaxCallerRegisters = 32;

// The call sites at which a baseline-compiled caller may inline its callee,
// each classified as hot or not, per callee. A call site counts when its
// caller is compiled and within the caller bounds, its callee resolves (an
// `invoke-virtual` through the receiver type the caller proves, and through
// trivial forwarders, see `is_simple`) to a method with code in a non-external
// class that is not a true virtual, it is not in a `try` when its callee has
// one, and it does not construct an exception its block then throws. It is hot
// when its callee is compiled and both appear thresholds hold.
//
// The analysis behind `ArtProfileWriterPass`'s `@NeverInline` annotations,
// shared so that a pass predicting those annotations cannot drift from it.
// Every method in `scope` with code must have its CFG built.
struct HotCallsites {
  HotCallsites(const Scope& scope,
               const baseline_profiles::BaselineProfile& baseline_profile,
               const method_profiles::MethodProfiles& method_profiles,
               const HotCallsiteThresholds& thresholds);

  // Compiled callers skipped for exceeding a caller bound.
  size_t callers_too_many_instructions{0};
  size_t callers_too_many_registers{0};
  // Callees with at least one call site that is not hot.
  InsertOnlyConcurrentSet<DexMethod*> hot_cold_callees;
  // Per callee with at least one hot call site, how many it has.
  AtomicMap<DexMethod*, size_t> hot_callsite_counts;
};

} // namespace never_inline_analysis
