/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <atomic>
#include <memory>
#include <optional>
#include <vector>

#include "ConcurrentContainers.h"
#include "DexStore.h"
#include "MethodClosures.h"
#include "MethodSplittingConfig.h"
#include "MethodSplittingStats.h"
#include "RefChecker.h"

namespace api {
class AndroidSDK;
} // namespace api

namespace method_splitting_impl {

// One `RefChecker` per store, created up front and shared for the whole run:
// `RefChecker` memoizes `check_type` in concurrent maps and takes the store
// index as its only per-method input, so a per-method instance would throw the
// memo away on every method of every splitting iteration.
class StoreRefCheckers {
 public:
  // A null `min_sdk_api` makes every EXTERNAL type fail the check, so a missing
  // api file leaves the checkers maximally conservative rather than permissive.
  StoreRefCheckers(const DexStoresVector& stores,
                   bool normal_primary_dex,
                   const api::AndroidSDK* min_sdk_api);

  const RefChecker& get(const DexType* type) const {
    return *m_ref_checkers[m_xstores.get_store_idx(type)];
  }

 private:
  XStoreRefs m_xstores;
  std::vector<std::unique_ptr<RefChecker>> m_ref_checkers;
};

// Represents a single argument to a method closure. It must either have a type,
// to pass the register value through a parameter, or a simple definition, which
// must be const opcode.
struct ClosureArgument {
  reg_t reg;
  const DexType* type;
  IRInstruction* def;
};

// This data structure either represents the code following a single block, or a
// set of cases of a switch. It is "splittable" as it has been ensured that this
// part of the given method can in fact be split into a separate method.
struct SplittableClosure {
  std::shared_ptr<MethodClosures> method_closures;
  cfg::Block* switch_block;
  std::vector<const Closure*> closures;
  // The ids of the closures' head blocks. A split that takes several cases of
  // `switch_block` takes the switch's edges into these blocks.
  UnorderedSet<cfg::BlockId> grouped_heads;
  std::vector<ClosureArgument> args;
  double rank;
  size_t added_code_size;
  std::optional<HotSplitKind> hot_split_kind;
  bool is_large_packed_switch{false};
  bool creates_large_sparse_switch{false};
  bool destroys_large_packed_switch{false};
  // The net saving of a net-gated candidate, carried to emission, where the
  // candidate's fate is recorded with it.
  std::optional<ClosureNetTerms> net_terms;
  // The code units of the closures' blocks. The candidate's fate counts these
  // code units.
  size_t covered_code_units{0};
  // Whether only a net gate's lowered size floors admit the candidate.
  bool below_legacy_floors{false};

  int is_switch() const { return switch_block != nullptr ? 1 : 0; }

  // id is unique among all splittable closures where is_switch() is the same.
  size_t id() const {
    if (switch_block != nullptr) {
      return switch_block->id();
    }
    always_assert(closures.size() == 1);
    return closures.front()->target->id();
  }

  // Head-block ids in `closures` order.
  std::vector<cfg::BlockId> head_ids() const { return head_ids(closures); }

  // The head-block ids of `closures`, in order, also for a candidate that is
  // not a `SplittableClosure` yet.
  static std::vector<cfg::BlockId> head_ids(
      const std::vector<const Closure*>& closures) {
    std::vector<cfg::BlockId> ids;
    ids.reserve(closures.size());
    for (const auto* c : closures) {
      ids.push_back(c->target->id());
    }
    return ids;
  }

  std::vector<const DexType*> get_arg_types() const;
};

// Selects splittable closures for a given set of methods based of configured
// costs. `stats` receives the fate of every candidate dropped on the way.
ConcurrentMap<DexType*, std::vector<SplittableClosure>>
select_splittable_closures_based_on_costs(
    const ConcurrentSet<DexMethod*>& methods,
    const Config& config,
    const StoreRefCheckers& store_ref_checkers,
    InsertOnlyConcurrentSet<const DexMethod*>* concurrent_hot_methods,
    InsertOnlyConcurrentMap<DexMethod*, size_t>*
        concurrent_splittable_no_optimizations_methods,
    Stats& stats);

// Selects splittable closures for a given set of methods from all contained
// top-level switch cases.
InsertOnlyConcurrentMap<DexMethod*, std::vector<SplittableClosure>>
select_splittable_closures_from_top_level_switch_cases(
    const std::vector<DexMethod*>& methods, size_t max_live_in);

} // namespace method_splitting_impl
