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

#include "Debug.h"
#include "DeterministicContainers.h"
#include "ReducedControlFlow.h"

namespace method_splitting_impl {

struct Stats; // MethodSplittingStats.h

// What became of a split candidate: the stage that decided it, and why. Every
// candidate is recorded exactly once, at its final outcome. So for each kind,
// the number of candidates a run considered equals the sum of its outcome
// counts.
//
// A region candidate is a region head: a cold node with a hot predecessor. A
// suffix candidate is one the overhead-ratio sweep scored. `Emitted` is the
// only outcome that is not a drop.
enum class CandidateFate : uint8_t {
  // Region discovery, at the head's own node.
  Discovery_Cycle, // the region would hold a cycle
  Discovery_Return, // ends in a return
  Discovery_Branch, // ends in an `if` or a `switch`
  Discovery_ResultReadingHead, // starts with `move-result*`/`move-exception`
  Discovery_ThrowEdge, // a block with a throw edge
  Discovery_Monitor, // entered with a monitor held, or holds a monitor op
  Discovery_FinalFieldPut,
  // Region discovery, at the continuation where the host resumes.
  Discovery_NoRejoin, // leaves for no block the host may resume at
  Discovery_TooManyLiveOuts, // returns more values than a split can return
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
  Evaluation_ReceiverUninitialized,
  Evaluation_NetNotPositive,
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
        {CandidateFate::Discovery_Cycle, "discovery_cycle"},
        {CandidateFate::Discovery_Return, "discovery_return"},
        {CandidateFate::Discovery_Branch, "discovery_branch"},
        {CandidateFate::Discovery_ResultReadingHead,
         "discovery_result_reading_head"},
        {CandidateFate::Discovery_ThrowEdge, "discovery_throw_edge"},
        {CandidateFate::Discovery_Monitor, "discovery_monitor"},
        {CandidateFate::Discovery_FinalFieldPut, "discovery_final_field_put"},
        {CandidateFate::Discovery_NoRejoin, "discovery_no_rejoin"},
        {CandidateFate::Discovery_TooManyLiveOuts,
         "discovery_too_many_live_outs"},
        {CandidateFate::Evaluation_EmptyHead, "evaluation_empty_head"},
        {CandidateFate::Evaluation_TooManyLiveIns,
         "evaluation_too_many_live_ins"},
        {CandidateFate::Evaluation_LiveInUntypable,
         "evaluation_live_in_untypable"},
        {CandidateFate::Evaluation_ArgTypeIllegal,
         "evaluation_arg_type_illegal"},
        {CandidateFate::Evaluation_LiveInUninitialized,
         "evaluation_live_in_uninitialized"},
        {CandidateFate::Evaluation_ReceiverUninitialized,
         "evaluation_receiver_uninitialized"},
        {CandidateFate::Evaluation_NetNotPositive,
         "evaluation_net_not_positive"},
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

// The order every region walk visits blocks in: by id, which does not vary
// between runs as pointer order does.
inline bool block_id_less(const cfg::Block* a, const cfg::Block* b) {
  return a->id() < b->id();
}

// The blocks of the region one split takes, in id order, each listed once. Id
// order is not control-flow order: `blocks().front()` is the lowest-id block,
// not necessarily the region head. The head is the closure's `target`.
class RegionMembers {
 public:
  // One region's blocks, sorted here by id.
  explicit RegionMembers(std::vector<cfg::Block*> blocks);

  const std::vector<cfg::Block*>& blocks() const { return m_blocks; }
  const UnorderedSet<cfg::BlockId>& ids() const { return m_ids; }
  bool contains(cfg::BlockId id) const { return m_ids.contains(id); }

 private:
  std::vector<cfg::Block*> m_blocks;
  UnorderedSet<cfg::BlockId> m_ids;
};

// Where control leaves a region. A single-exit region goes back to the host at
// one block that every path out of the region passes through. That block is a
// real block, never the synthetic exit block.
struct SingleExit {
  cfg::Block* rejoin;
};

// Per-region metadata attached to a `Closure` when the closure was
// produced by region discovery rather than suffix discovery.
// Suffix closures have `closure.region == std::nullopt`.
struct RegionInfo {
  SingleExit exits;
  RegionMembers members;

  cfg::Block* rejoin_block() const { return exits.rejoin; }
};

// Whether control leaving a region may land on `b`. A block that starts with
// `move-result*` or `move-exception` reads the result of the instruction that
// ends its predecessor: an invoke, another result-producing opcode, or a throw.
// The two must stay together. If a region ended in that producer, the producer
// would move into the split while the host still runs the `move-result*` or
// `move-exception`, with nothing left in front of it to read from.
inline bool can_be_region_boundary(const cfg::Block* b) {
  return !b->starts_with_move_result() && !b->starts_with_move_exception();
}

// Whether `b` is the synthetic exit `calculate_exit_block` creates for a method
// with several returns, wired to each of them by `EDGE_GHOST`. It holds no code
// and does not survive a cfg rebuild, so it is never part of a region. A
// single-return method's `exit_block()` is its real return block.
inline bool is_ghost_exit_block(const cfg::ControlFlowGraph& cfg,
                                const cfg::Block* b) {
  return b == cfg.exit_block() &&
         cfg.get_pred_edge_of_type(b, cfg::EDGE_GHOST) != nullptr;
}

// How emission edits the host's switch. `None` makes no switch edit: the
// split takes one block's predecessors. `DeleteGrouped` serves a split that
// takes several cases: it deletes the grouped case keys and, when the default
// edge is grouped too, points that edge at the launchpad.
enum class HostSwitchEdit : uint8_t { None, DeleteGrouped };

// What a host switch edit does to one of the switch's edges.
enum class SwitchEdgeEdit : uint8_t { Keep, Delete, ToLaunchpad };

// What `edit` does to one edge of the host switch. `into_taken_head` says
// whether the edge enters a head the split takes, and `is_default` whether it
// is the switch's default edge. The net saving and emission both ask this.
inline SwitchEdgeEdit host_switch_edge_edit(HostSwitchEdit edit,
                                            bool into_taken_head,
                                            bool is_default) {
  if (!into_taken_head) {
    return SwitchEdgeEdit::Keep;
  }
  switch (edit) {
  case HostSwitchEdit::None:
    return SwitchEdgeEdit::Keep;
  case HostSwitchEdit::DeleteGrouped:
    // A deleted case key falls through to the default edge.
    return is_default ? SwitchEdgeEdit::ToLaunchpad : SwitchEdgeEdit::Delete;
  }
  not_reached();
}

// A split candidate: for a suffix, every block reachable from a reduced block;
// for a region, the blocks `region->members` lists.
struct Closure {
  const ReducedBlock* reduced_block;
  UnorderedSet<const ReducedBlock*> reduced_components;
  UnorderedSet<cfg::Block*> srcs;
  cfg::Block* target;
  // Set for region closures; nullopt for suffix closures.
  std::optional<RegionInfo> region;
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

// Discovers cold regions of a single block that return no value. Returns one
// `Closure` per eligible cold block. Eligibility includes these checks:
// - it is a node of the reduced CFG on its own;
// - it leaves only by a goto to another block (the continuation, where the host
//   resumes) that control may land on;
// - it defines nothing live at the continuation;
// - no throw edge crosses its boundary;
// - it is entered with no monitor held;
// - it is not in the final-field-put exclusion set.
class RegionStrategy : public ClosureDiscoveryStrategy {
 public:
  // `stats` receives the outcome of every head discovery refuses and a
  // candidate count for every head it considers.
  explicit RegionStrategy(Stats& stats) : m_stats(stats) {}
  std::vector<Closure> discover(
      DexMethod* method, const ReducedControlFlowGraph& rcfg) const override;

 private:
  Stats& m_stats;
};

// Find potentially relevant closures for a method. Thin dispatcher
// over `SuffixStrategy` retained for callers that don't yet have a
// strategy registry; new code should construct a strategy directly.
std::shared_ptr<MethodClosures> discover_closures(
    DexMethod* method, std::shared_ptr<const ReducedControlFlowGraph> rcfg);

} // namespace method_splitting_impl
