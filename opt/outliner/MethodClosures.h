/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <array>
#include <cstdint>
#include <memory>
#include <optional>
#include <string_view>
#include <vector>

#include "DeterministicContainers.h"
#include "ReducedControlFlow.h"

namespace method_splitting_impl {

// What became of a split candidate: the stage that decided it, and why. Every
// candidate is recorded exactly once, at its final fate. So for each kind, the
// number of candidates a run considered equals the sum of its fate counts.
//
// A suffix candidate is one the overhead-ratio sweep scored. `Emitted` is the
// only fate that is not a drop.
enum class CandidateFate : uint8_t {
  // Per-candidate evaluation.
  Evaluation_EmptyHead,
  Evaluation_TooManyLiveIns,
  Evaluation_LiveInUntypable,
  // A synthesized argument type is not loadable: external and above the
  // min-sdk floor, or cross-store illegal. A nonzero count on a run that also
  // reports `min_sdk_no_file` means the gate rejected external types for want
  // of an api model rather than on a real min-sdk violation.
  Evaluation_ArgTypeIllegal,
  Evaluation_LiveInUninitialized,
  // Selection, emission.
  Selection_Displaced, // an overlapping candidate ranked ahead claimed it
  Emission_DexLimit,
  Emitted,
};

inline constexpr size_t kCandidateFateCount =
    static_cast<size_t>(CandidateFate::Emitted) + 1;

// The metric name of each fate. Each entry names its fate, so the table can be
// checked against the enum's order.
struct CandidateFateName {
  CandidateFate fate;
  std::string_view name;
};
inline constexpr std::array<CandidateFateName, kCandidateFateCount>
    kCandidateFateNames{{
        {CandidateFate::Evaluation_EmptyHead, "evaluation_empty_head"},
        {CandidateFate::Evaluation_TooManyLiveIns,
         "evaluation_too_many_live_ins"},
        {CandidateFate::Evaluation_LiveInUntypable,
         "evaluation_live_in_untypable"},
        {CandidateFate::Evaluation_ArgTypeIllegal,
         "evaluation_arg_type_illegal"},
        {CandidateFate::Evaluation_LiveInUninitialized,
         "evaluation_live_in_uninitialized"},
        {CandidateFate::Selection_Displaced, "selection_displaced"},
        {CandidateFate::Emission_DexLimit, "emission_dex_limit"},
        {CandidateFate::Emitted, "emitted"},
    }};
static_assert(
    [] {
      for (size_t i = 0; i < kCandidateFateCount; ++i) {
        if (kCandidateFateNames[i].fate != static_cast<CandidateFate>(i) ||
            kCandidateFateNames[i].name.empty()) {
          return false;
        }
      }
      return true;
    }(),
    "one name per CandidateFate, in enum order");

inline std::string_view describe(CandidateFate fate) {
  return kCandidateFateNames[static_cast<size_t>(fate)].name;
}

// A "closure" here represents the transitive closure of all blocks reachable
// from a given reduced block.
struct Closure {
  const ReducedBlock* reduced_block;
  UnorderedSet<const ReducedBlock*> reduced_components;
  UnorderedSet<cfg::Block*> srcs;
  cfg::Block* target;
};

// A set of closures associated with a particular method.
struct MethodClosures {
  DexMethod* method;
  size_t original_size;
  std::shared_ptr<const ReducedControlFlowGraph> rcfg;
  std::vector<Closure> closures;
};

// Normalizes `method`'s CFG IN PLACE so it is ready to be split: merges every
// return-only successor block into its sole predecessor, and drops unreachable
// blocks. Optionally also splits oversized blocks.
//
// Merges every return-only successor into its sole predecessor, so a rejoin
// block whose only instruction is a `return` does not survive: its return is
// absorbed into the cold predecessor, which then reads as a return-shaped block
// and is rejected downstream with no useful error. A rejoin needs at least one
// non-return instruction (fixtures get one from `nonMergeableRejoin()`).
void normalize_cfg_for_splitting(
    DexMethod* method, std::optional<uint64_t> split_block_size = std::nullopt);

// Builds the reduced view of an already-normalized CFG. Does NOT modify the
// method -- the pointer is non-const only because `ReducedControlFlowGraph`
// takes a mutable `cfg&`.
//
// Precondition: `normalize_cfg_for_splitting` has run on `method`. Asserted,
// because a reduced graph built over an unnormalized CFG is silently wrong
// rather than obviously broken.
std::shared_ptr<const ReducedControlFlowGraph> reduce_cfg(DexMethod* method);

// Strategy that produces a set of `Closure` candidates for a single
// method. Callers may run more than one strategy and concatenate the
// candidates before scoring.
class ClosureDiscoveryStrategy {
 public:
  virtual ~ClosureDiscoveryStrategy() = default;
  virtual std::vector<Closure> discover(
      DexMethod* method, const ReducedControlFlowGraph& rcfg) const = 0;
};

class SuffixStrategy : public ClosureDiscoveryStrategy {
 public:
  std::vector<Closure> discover(
      DexMethod* method, const ReducedControlFlowGraph& rcfg) const override;
};

// Find potentially relevant closures for a method. Thin dispatcher
// over `SuffixStrategy` retained for callers that don't yet have a
// strategy registry; new code should construct a strategy directly.
std::shared_ptr<MethodClosures> discover_closures(
    DexMethod* method, std::shared_ptr<const ReducedControlFlowGraph> rcfg);

} // namespace method_splitting_impl
