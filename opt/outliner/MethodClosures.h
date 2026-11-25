/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <memory>
#include <vector>

#include "DeterministicContainers.h"
#include "ReducedControlFlow.h"

namespace method_splitting_impl {

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
