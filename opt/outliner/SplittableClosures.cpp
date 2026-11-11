/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "SplittableClosures.h"

#include <cinttypes>
#include <deque>
#include <functional>
#include <optional>
#include <vector>

#include <sparta/PatriciaTreeSet.h>

#include "BaselineProfile.h"
#include "ClosureAggregator.h"
#include "ConcurrentContainers.h"
#include "Debug.h"
#include "InstructionLowering.h"
#include "Lazy.h"
#include "Liveness.h"
#include "MethodUtil.h"
#include "OutlinerTypeAnalysis.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "SplitNetSaving.h"
#include "Timer.h"
#include "Trace.h"
#include "UninitializedObjects.h"
#include "WorkQueue.h"

namespace {

using namespace method_splitting_impl;
using namespace outliner_impl;
using namespace uninitialized_objects;

// The ids of `closures`' head blocks.
UnorderedSet<cfg::BlockId> collect_head_ids(
    const std::vector<const Closure*>& closures) {
  UnorderedSet<cfg::BlockId> ids;
  for (const auto* c : closures) {
    ids.insert(c->target->id());
  }
  return ids;
}

// What a candidate's net saving is read for: nothing, or deciding whether it is
// split.
enum class NetSavingUse : uint8_t { None, Gate };

struct ScoredClosure {
  cfg::Block* switch_block{nullptr};
  std::vector<const Closure*> closures;
  // The heads of `closures` (`collect_head_ids`). A split that takes several
  // cases of `switch_block` takes the switch's edges into these heads.
  UnorderedSet<cfg::BlockId> grouped_heads;
  UnorderedSet<const ReducedBlock*> reduced_components;
  size_t split_size{};
  size_t remaining_size{};
  // The code units of the closures' blocks. The split copies these blocks, and
  // the candidate's fate counts these code units.
  size_t covered_code_units{0};
  // The code units the split takes out of the host: its blocks the host no
  // longer reaches once the split's edit is applied. A block the host can
  // still enter stays there too, so the split duplicates it rather than taking
  // it out. Set in `score()`; read by `net_saving_input`.
  size_t evicted_size{};
  // The part of `evicted_size` in hot blocks. This hot code leaves compiled
  // code too, but a split that is not hot is not compiled, so the hot code then
  // runs interpreted. The net saving therefore counts only cold code as saved.
  size_t evicted_hot_size{0};
  // The duplicated members' dex code units (`dex_code_units`).
  size_t duplicated_dex_code_units{0};
  // Whether only a net gate's lowered size floors admit the candidate.
  bool below_legacy_floors{false};
  std::optional<HotSplitKind> hot_split_kind{std::nullopt};
  bool is_large_packed_switch{false};
  bool creates_large_sparse_switch{false};
  bool destroys_large_packed_switch{false};
  std::vector<ClosureArgument> args;
  // Whether the net saving is read, and what for; decided in `score`.
  NetSavingUse net_saving_use{NetSavingUse::None};
  // The net saving of a candidate its net gate reads (`split_net_saving`).
  std::optional<ClosureNetTerms> net_terms{std::nullopt};
  // The compiled copies of the host its net saving counts (`split_net_saving`).
  size_t compiled_copies{1};
  // The partition of `switch_block`'s edges by `grouped_heads`; set for a
  // candidate taking several cases of a switch.
  std::optional<SwitchPartition> dispatch{std::nullopt};

  int is_switch() const { return switch_block != nullptr ? 1 : 0; }

  // id is unique among all splittable closures where is_switch() is the same.
  size_t id() const {
    if (switch_block != nullptr) {
      return switch_block->id();
    }
    always_assert(closures.size() == 1);
    return closures.front()->target->id();
  }
};

// For a given switch-block/closures, find all incoming preds which will be
// eliminated by splitting them out.
UnorderedSet<const ReducedEdge*> get_except_preds(
    cfg::Block* switch_block,
    const std::vector<const Closure*>& closures,
    const UnorderedSet<const ReducedBlock*>& reduced_components,
    UnorderedSet<int32_t>* except_case_keys) {
  UnorderedSet<const ReducedEdge*> except_preds;
  for (const auto* c : closures) {
    insert_unordered_iterable(except_preds, c->reduced_block->preds);
  }
  if (switch_block != nullptr) {
    for (const auto* c : closures) {
      for (const auto* pred : UnorderedIterable(c->reduced_block->preds)) {
        if (reduced_components.count(pred->src) != 0u) {
          continue;
        }
        // Decide first, then collect. The two questions are independent, and
        // interleaving them made the answer depend on hash order: the old loop
        // broke out on the first non-switch edge, so a pred that was going to
        // be erased anyway still contributed the case keys of whichever of its
        // edges happened to be visited before that one.
        //
        // An erased pred contributes no keys. It keeps a way into the host that
        // does not come from the switch, so its cases are not eliminated by
        // splitting and must not be counted as if they were.
        if (unordered_any_of(pred->edges, [switch_block](const cfg::Edge* e) {
              return e->src() != switch_block;
            })) {
          except_preds.erase(pred);
          continue;
        }
        for (const auto* e : UnorderedIterable(pred->edges)) {
          if (e->type() == cfg::EDGE_BRANCH) {
            except_case_keys->insert(*e->case_key());
          }
        }
      }
    }
  }
  return except_preds;
}

// The blocks reachable from `roots` along the edges `cut` keeps.
UnorderedSet<cfg::Block*> reachable_blocks(
    const std::vector<cfg::Block*>& roots,
    const std::function<bool(const cfg::Edge*)>& cut) {
  UnorderedSet<cfg::Block*> reached;
  std::deque<cfg::Block*> work;
  for (auto* r : roots) {
    if (reached.insert(r).second) {
      work.push_back(r);
    }
  }
  while (!work.empty()) {
    auto* b = work.front();
    work.pop_front();
    for (const auto* e : b->succs()) {
      if (!cut(e) && reached.insert(e->target()).second) {
        work.push_back(e->target());
      }
    }
  }
  return reached;
}

bool is_large(const Config& config,
              cfg::Block* switch_block,
              const UnorderedSet<int32_t>* except_case_keys = nullptr) {
  // ">" and not ">=" because the succs include the default edge.
  return switch_block->succs().size() -
             (except_case_keys != nullptr ? except_case_keys->size() : 0) >
         config.min_large_switch_size;
}

bool is_packed(cfg::Block* switch_block,
               const UnorderedSet<int32_t>* except_case_keys = nullptr) {
  instruction_lowering::CaseKeysExtentBuilder ckeb;
  for (auto* e : switch_block->succs()) {
    if (e->type() != cfg::EDGE_BRANCH) {
      continue;
    }
    auto case_key = *e->case_key();
    if ((except_case_keys != nullptr) &&
        (except_case_keys->count(case_key) != 0u)) {
      continue;
    }
    ckeb.insert(case_key);
  }
  return !ckeb->sufficiently_sparse();
}

// The two size floors of a candidate: what it must take and what the host
// must keep.
struct SizeFloors {
  uint64_t split;
  uint64_t remaining;
};

// The size floors of a candidate of `kind`. They are the floors of its kind,
// except that the host of a hot-cold suffix must keep the hot floor. A net gate
// that applies to the candidate (`gate`) lowers both floors to
// `min_suffix_sub_floor_split_size` where that is lower, so that its net saving
// can admit a candidate below its kind's floors.
SizeFloors floors_for(const Config& config, HotSplitKind kind, bool gate) {
  SizeFloors floors{};
  switch (kind) {
  case HotSplitKind::Hot:
    floors = {config.min_hot_split_size, config.min_hot_split_size};
    break;
  case HotSplitKind::HotCold:
    floors = {config.min_hot_cold_split_size, config.min_hot_split_size};
    break;
  case HotSplitKind::Cold:
    floors = {config.min_cold_split_size, config.min_cold_split_size};
    break;
  }
  if (gate) {
    always_assert(kind != HotSplitKind::Hot);
    floors.split =
        std::min(floors.split, config.min_suffix_sub_floor_split_size);
    floors.remaining =
        std::min(floors.remaining, config.min_suffix_sub_floor_split_size);
  }
  return floors;
}

// What the host keeps, block by block, once a split of `sc` is applied.
// Emission sends to the launchpad the switch's edges into the grouped heads
// (for a group), or every edge into the head (for one closure). It leaves every
// other edge in place. That includes an edge from a closure block the host
// still reaches, so the block that edge enters stays in the host too.
UnorderedSet<cfg::Block*> host_blocks_kept(cfg::ControlFlowGraph& cfg,
                                           const ScoredClosure& sc) {
  always_assert(!sc.closures.empty());
  const auto* head = sc.closures.front()->target;
  return reachable_blocks({cfg.entry_block()}, [&](const cfg::Edge* e) {
    return sc.switch_block != nullptr
               ? e->src() == sc.switch_block &&
                     sc.grouped_heads.contains(e->target()->id())
               : e->target() == head;
  });
}

// Sizes what a split of `sc` evicts from the host and what it duplicates,
// given the blocks the host keeps (`host_blocks_kept`).
void size_eviction(const UnorderedSet<cfg::Block*>& remaining_cfg_blocks,
                   ScoredClosure* sc) {
  // A block of the split that the host still reaches exists in both methods;
  // every other block leaves the host.
  size_t duplicated_size = 0;
  for (const auto* rb : UnorderedIterable(sc->reduced_components)) {
    for (const auto* b : UnorderedIterable(rb->blocks)) {
      const auto units = b->estimate_code_units();
      if (remaining_cfg_blocks.contains(const_cast<cfg::Block*>(b))) {
        duplicated_size += units;
        sc->duplicated_dex_code_units += dex_code_units(b);
      } else if (is_hot(b)) {
        sc->evicted_hot_size += units;
      }
    }
  }
  sc->evicted_size = sc->covered_code_units - duplicated_size;
}

std::optional<ScoredClosure> score(
    const Config& config,
    const MethodClosures& mcs,
    bool host_compiled,
    float max_overhead_ratio,
    cfg::Block* switch_block,
    bool is_large_packed_switch,
    const std::vector<const Closure*>& closures) {
  ScoredClosure sc{
      .switch_block = switch_block,
      .closures = closures,
      .grouped_heads = collect_head_ids(closures),
      .reduced_components = {},
      .args = {},
  };
  for (const auto* c : closures) {
    insert_unordered_iterable(sc.reduced_components, c->reduced_components);
  }
  auto reduced_components_code_size = code_size(sc.reduced_components);
  sc.covered_code_units = reduced_components_code_size;
  sc.split_size = config.cost_split_method + reduced_components_code_size;
  if (closures.size() > 1) {
    sc.split_size += config.cost_split_switch +
                     config.cost_split_switch_case * closures.size();
  }
  const auto kind = classify_hot_split_kind(closures);
  sc.hot_split_kind = kind;
  // A net gate applies to the suffixes of its kind on a compiled host, the
  // only host whose evicted cold code leaves compiled code.
  const bool gate =
      host_compiled &&
      ((kind == HotSplitKind::HotCold && config.suffix_net_gate) ||
       (kind == HotSplitKind::Cold && config.suffix_net_gate_cold));
  const auto floors = floors_for(config, kind, gate);
  if (sc.split_size < floors.split) {
    return std::nullopt;
  }
  always_assert(reduced_components_code_size <= mcs.original_size);
  auto remaining_size_reduction =
      closures.size() > 1
          ? config.cost_split_switch_case * (closures.size() - 1)
          : 0;

  UnorderedSet<int32_t> except_case_keys;
  get_except_preds(switch_block, closures, sc.reduced_components,
                   &except_case_keys);
  if (is_large_packed_switch) {
    sc.is_large_packed_switch = true;
    sc.destroys_large_packed_switch =
        is_large(config, switch_block, &except_case_keys) &&
        !is_packed(switch_block, &except_case_keys);
    if (except_case_keys.size() >= config.min_large_switch_size) {
      instruction_lowering::CaseKeysExtentBuilder ckeb;
      for (auto case_key : UnorderedIterable(except_case_keys)) {
        ckeb.insert(case_key);
      }
      sc.creates_large_sparse_switch = ckeb->sufficiently_sparse();
    }
  }

  const auto remaining_cfg_blocks =
      host_blocks_kept(mcs.method->get_code()->cfg(), sc);
  size_t raw_remaining = 0;
  for (const auto* b : UnorderedIterable(remaining_cfg_blocks)) {
    raw_remaining += b->estimate_code_units();
  }
  // `always_assert`, not `redex_assert`: what stays reachable must be part of
  // the input method, which this function does not establish, so the check
  // must survive an opt build, like the one on `reduced_components_code_size`
  // above. Without it, a violation would wrap the subtraction below into a
  // huge `evicted_size`, which the net saving would count as saved.
  always_assert_log(raw_remaining <= mcs.original_size,
                    "remaining %zu exceeds original %zu in %s", raw_remaining,
                    mcs.original_size, SHOW(mcs.method));
  sc.remaining_size = raw_remaining < remaining_size_reduction
                          ? 0
                          : raw_remaining - remaining_size_reduction;
  // The host's floor counts what the host keeps, including a block the split
  // copies that the host still reaches.
  if (sc.remaining_size < floors.remaining) {
    return std::nullopt;
  }
  if (gate) {
    const auto legacy = floors_for(config, kind, /*gate=*/false);
    sc.below_legacy_floors =
        sc.split_size < legacy.split || sc.remaining_size < legacy.remaining;
  }
  // The net saving decides whether a suffix is split where its net gate
  // applies, on a compiled host: every hot-cold suffix under `suffix_net_gate`,
  // and a cold tail that only the cold gate's lowered floors admit. On an
  // uncompiled host no suffix split saves compiled code, so none is evaluated.
  if (sc.below_legacy_floors ||
      (host_compiled && kind == HotSplitKind::HotCold &&
       config.suffix_net_gate)) {
    sc.net_saving_use = NetSavingUse::Gate;
  }
  if (switch_block != nullptr) {
    sc.dispatch = partition_switch(switch_block, sc.grouped_heads);
  }
  // `size_eviction` sizes from `covered_code_units`, which is this size.
  always_assert(sc.covered_code_units == reduced_components_code_size);
  size_eviction(remaining_cfg_blocks, &sc);
  auto overhead_ratio = static_cast<double>(sc.split_size + sc.remaining_size) /
                            static_cast<double>(mcs.original_size) -
                        1.0;
  if (overhead_ratio > max_overhead_ratio) {
    return std::nullopt;
  }
  return std::optional<ScoredClosure>(std::move(sc));
};

UnorderedSet<const ReducedBlock*> get_critical_components(
    const std::vector<std::pair<int32_t, const Closure*>>& keyed,
    const Closure* fallthrough) {
  UnorderedMap<const ReducedBlock*, size_t> counts;
  auto add_to_counts = [&counts](const Closure* c) {
    for (const auto* component : UnorderedIterable(c->reduced_components)) {
      counts[component]++;
    }
  };
  for (auto [_, c] : keyed) {
    add_to_counts(c);
  }
  UnorderedSet<const ReducedBlock*> critical_components;
  for (auto [c, count] : UnorderedIterable(counts)) {
    if (count < keyed.size() &&
        (fallthrough->reduced_components.count(c) == 0u)) {
      critical_components.insert(c);
    }
  }
  return critical_components;
};

std::optional<ScoredClosure> select_prefix(
    const Config& config,
    const MethodClosures& mcs,
    bool host_compiled,
    float max_overhead_ratio,
    cfg::Block* switch_block,
    bool is_large_packed_switch,
    std::vector<const Closure*> aggregated) {
  while (aggregated.size() > 1) {
    auto opt_sc = score(config, mcs, host_compiled, max_overhead_ratio,
                        switch_block, is_large_packed_switch, aggregated);
    if (opt_sc) {
      return opt_sc;
    }
    aggregated.pop_back();
  }
  return std::nullopt;
}

std::vector<const Closure*> aggregate_half_packed(
    const Closure* fallthrough,
    const std::vector<std::pair<int32_t, const Closure*>>& keyed,
    size_t switched_size) {
  std::vector<const Closure*> aggregated{fallthrough};
  size_t i = 0;
  // Add up to half of all cases
  while (i < keyed.size() && aggregated.size() * 2 <= switched_size) {
    aggregated.push_back(keyed.at(i++).second);
  }
  return aggregated;
}

std::vector<const Closure*> aggregate_half_sparse(
    const Closure* fallthrough,
    const std::vector<std::pair<int32_t, const Closure*>>& keyed,
    size_t switched_size) {
  ClosureAggregator aggregator(get_critical_components(keyed, fallthrough));
  for (auto [_, c] : keyed) {
    aggregator.insert(c);
  }
  std::vector<const Closure*> aggregated{fallthrough};
  // Select the seed case, which will influence all following cases.
  // We start with the largest key, preferring aggregating a suffix.
  const auto* seed = keyed.front().second;
  aggregator.erase(seed);
  aggregated.push_back(seed);

  // Add up to half of all cases
  while (!aggregator.empty() && aggregated.size() * 2 <= switched_size) {
    const auto* c = aggregator.front();
    aggregator.erase(c);
    aggregated.push_back(c);
  }
  return aggregated;
}

// Find a set of switch cases that are worthwhile to split off
std::optional<ScoredClosure> aggregate(
    const Config& config,
    const MethodClosures& mcs,
    bool host_compiled,
    float max_overhead_ratio,
    cfg::Block* switch_block,
    bool is_large_packed_switch,
    const std::vector<const Closure*>& switched,
    const std::function<bool(const Closure*)>& predicate) {
  always_assert(!switched.empty());
  if (switched.size() == 1) {
    return std::nullopt;
  }
  std::vector<std::pair<int32_t, const Closure*>> keyed; // only considering
                                                         // min-case-key
                                                         // except fallthrough
  const Closure* fallthrough = nullptr; // may include case-keys
  for (const auto* c : switched) {
    auto expanded_preds = c->reduced_block->expand_preds(switch_block);
    always_assert(!expanded_preds.empty());
    // Any minimum will do: ties compare equal on `case_key()`, which is the
    // only thing read off the winner.
    const auto* min_edge =
        *unordered_min_element(expanded_preds, [](auto* e, auto* f) {
          return e->case_key() < f->case_key();
        });
    if (min_edge->case_key()) {
      if (predicate(c)) {
        keyed.emplace_back(*min_edge->case_key(), c);
      }
    } else {
      fallthrough = c;
    }
  }
  if (keyed.empty() || (fallthrough == nullptr)) {
    return std::nullopt;
  }
  // Sort to have smallest case keys last, to prefer aggregating a suffix
  // of the (sorted) case keys.
  std::sort(keyed.begin(), keyed.end(),
            [&](auto& p, auto& q) { return p.first > q.first; });
  if (is_large_packed_switch) {
    auto aggregate_half_packed_and_select_prefix = [&]() {
      auto aggregated =
          aggregate_half_packed(fallthrough, keyed, switched.size());
      return select_prefix(config, mcs, host_compiled, max_overhead_ratio,
                           switch_block, is_large_packed_switch,
                           std::move(aggregated));
    };

    // First, consider suffix. Note that smallest keys are already last.
    auto sc_opt = aggregate_half_packed_and_select_prefix();
    if (sc_opt) {
      return sc_opt;
    }

    // Second, consider prefix. For this, we reserve the order to put smallest
    // case keys first.
    std::reverse(keyed.begin(), keyed.end());
    sc_opt = aggregate_half_packed_and_select_prefix();
    if (sc_opt) {
      return sc_opt;
    }

    // Otherwise, fall back to aggregation of arbitrarily switch cases
    // Restore original order (smallest case keys last).
    std::reverse(keyed.begin(), keyed.end());
  }

  auto aggregated = aggregate_half_sparse(fallthrough, keyed, switched.size());
  return select_prefix(config, mcs, host_compiled, max_overhead_ratio,
                       switch_block, is_large_packed_switch,
                       std::move(aggregated));
};

// Select closures that meet the configured size thresholds, and score them.
std::vector<ScoredClosure> get_scored_closures(const Config& config,
                                               const MethodClosures& mcs,
                                               bool host_compiled,
                                               float max_overhead_ratio) {
  // For all possible closures, do some quick filtering, and score the
  // surviving ones
  std::vector<ScoredClosure> scored_closures;
  UnorderedMap<cfg::Block*, std::vector<const Closure*>>
      remaining_switch_case_closures;
  for (const auto& c : mcs.closures) {
    auto opt_sc = score(config, mcs, host_compiled, max_overhead_ratio,
                        /* switch_block */ nullptr,
                        /* is_large_packed_switch */ false, {&c});
    if (opt_sc) {
      scored_closures.push_back(std::move(*opt_sc));
    }
    for (auto* src : UnorderedIterable(c.srcs)) {
      if (src->branchingness() == opcode::BRANCH_SWITCH) {
        remaining_switch_case_closures[src].push_back(&c);
      }
    }
  }

  // Next, try to aggregate switch case closures. We prefer splitting off cases
  // that are all cold, or all hot. Only when we don't find such a set of switch
  // cases, then we'll take anything.
  static std::array<std::function<bool(const Closure*)>, 3> predicates = {
      [](const auto* c) { return !c->reduced_block->is_hot; },
      [](const auto* c) { return c->reduced_block->is_hot; },
      [](const auto*) { return true; }};
  // Visit switch blocks in id order. Each iteration can append to
  // `scored_closures`, and that vector's order survives into emission, so
  // iterating the map in hash order would let the addresses of the switch
  // blocks decide the order candidates are considered in.
  for (auto* switch_block : unordered_to_ordered_keys(
           remaining_switch_case_closures,
           [](cfg::Block* a, cfg::Block* b) { return a->id() < b->id(); })) {
    const auto& switched = remaining_switch_case_closures.at(switch_block);
    auto is_large_packed_switch =
        is_large(config, switch_block) && is_packed(switch_block);
    for (const auto& predicate : predicates) {
      auto opt_sc =
          aggregate(config, mcs, host_compiled, max_overhead_ratio,
                    switch_block, is_large_packed_switch, switched, predicate);
      if (opt_sc) {
        scored_closures.push_back(std::move(*opt_sc));
        break;
      }
    }
  }
  return scored_closures;
};

// What `split_net_saving` needs to know about `sc`, once `evaluate_candidate`
// has resolved its arguments.
//
// A split takes its blocks out of the host except those the host still
// reaches, which it duplicates (`score()`): emission redirects only the edges
// into the heads and copies every block, so a block the host can still enter
// exists in both methods. Hot code taken out earns nothing: the saving is in
// compiled cold code, and a net-gated split is never hot, so it is not compiled
// and the hot code it takes runs interpreted.
NetSavingInput net_saving_input(const ScoredClosure& sc,
                                const DexMethod* method,
                                const LivenessFixpointIterator& liveness) {
  // The launchpad passes the typed arguments; the split recreates each
  // constant argument at its entry.
  size_t passed_args = 0;
  size_t passed_arg_registers = 0;
  size_t recreated_defs = 0;
  for (const auto& a : sc.args) {
    if (a.type != nullptr) {
      passed_args++;
      passed_arg_registers += type::is_wide_type(a.type) ? 2 : 1;
    } else {
      recreated_defs += dex_code_units(a.def);
    }
  }
  std::optional<NetSavingInput::Dispatch> dispatch;
  if (sc.dispatch) {
    // In the split, the copied switch leads only to the members.
    std::vector<cfg::Block*> heads;
    heads.reserve(sc.closures.size());
    for (const auto* c : sc.closures) {
      heads.push_back(c->target);
    }
    UnorderedSet<const cfg::Block*> blocks;
    for (const auto* rb : UnorderedIterable(sc.reduced_components)) {
      insert_unordered_iterable(blocks, rb->blocks);
    }
    const auto selector = sc.switch_block->get_last_insn()->insn->src(0);
    // In the host, the edited switch keeps its edges into blocks the split
    // does not take. When the split takes the default edge, the switch sends
    // it to the launchpad, which reads the selector if it passes it.
    std::vector<cfg::Block*> targets;
    std::vector<cfg::Block*> kept_targets;
    bool to_launchpad = false;
    for (const auto* e : sc.switch_block->succs()) {
      if (e->type() == cfg::EDGE_THROW) {
        continue;
      }
      targets.push_back(e->target());
      switch (
          host_switch_edge_edit(HostSwitchEdit::DeleteGrouped,
                                sc.grouped_heads.contains(e->target()->id()),
                                e->type() == cfg::EDGE_GOTO)) {
      case SwitchEdgeEdit::Keep:
        kept_targets.push_back(e->target());
        break;
      case SwitchEdgeEdit::ToLaunchpad:
        to_launchpad = true;
        break;
      case SwitchEdgeEdit::Delete:
        break;
      }
    }
    const bool passes_selector =
        std::any_of(sc.args.begin(), sc.args.end(), [&](const auto& a) {
          return a.reg == selector && a.type != nullptr;
        });
    const auto live_at_any = [&liveness,
                              selector](const std::vector<cfg::Block*>& bs) {
      return std::any_of(bs.begin(), bs.end(), [&](cfg::Block* b) {
        return liveness.get_live_in_vars_at(b).contains(selector);
      });
    };
    const bool live_before = live_at_any(targets);
    const bool live_after =
        (to_launchpad && passes_selector) || live_at_any(kept_targets);
    // Asked of the host's liveness, which is exact for a suffix's split: a
    // suffix takes everything its heads reach.
    dispatch.emplace(
        NetSavingInput::Dispatch{.partition = *sc.dispatch,
                                 .selector_live_in_split = live_at_any(heads),
                                 .selector_live_in_host_before = live_before,
                                 .selector_live_in_host_after = live_after});
  }
  return NetSavingInput{
      .split = NetSavingInput::Suffix{.returns_value = !type::is_void(
                                          method->get_proto()->get_rtype())},
      .dispatch = dispatch,
      // A Hot split is compiled, so its hot code counts like the rest of what
      // it evicts.
      .evicted = sc.hot_split_kind == HotSplitKind::Hot
                     ? sc.evicted_size
                     : sc.evicted_size - sc.evicted_hot_size,
      .duplicated = sc.duplicated_dex_code_units,
      .passed_args = passed_args,
      .passed_arg_registers = passed_arg_registers,
      .recreated_defs = recreated_defs,
      .compiled_copies = sc.compiled_copies,
      .split_compiled = sc.hot_split_kind == HotSplitKind::Hot,
  };
}

// The inputs of `evaluate_candidate`: the per-method Lazy analyses, built once
// in `to_splittable_closures`, and that function's other per-method inputs.
// They are bundled so that the `std::erase_if` predicate that calls
// `evaluate_candidate` captures one reference.
struct CandidateEvalContext {
  Lazy<OutlinerTypeAnalysis>& ota;
  Lazy<LivenessFixpointIterator>& liveness_fp_iter;
  Lazy<UninitializedObjectEnvironments>& uninitialized_objects;
  Lazy<UnorderedMap<IRInstruction*, const ReducedBlock*>>& insns;
  Lazy<std::optional<reg_t>>& receiver;
  const RefChecker* ref_checker;
  const Config& config;
  bool host_compiled;
  DexMethod* method;
};

// Evaluates one candidate on its own: resolves its live-in arguments into
// `sc.args` and checks every rule a candidate must pass by itself. Returns the
// fate of a candidate that must be dropped, nullopt for one that stays.
// Overlap between candidates is resolved by the caller, not here.
std::optional<CandidateFate> evaluate_candidate(ScoredClosure& sc,
                                                CandidateEvalContext& ctx) {
  sparta::PatriciaTreeSet<reg_t> live_in;
  for (const auto* c : sc.closures) {
    live_in.union_with(
        ctx.liveness_fp_iter->get_live_in_vars_at(c->target).elements());
  }
  IRInstruction* first_insn;
  if (sc.switch_block != nullptr) {
    always_assert(sc.closures.size() > 1);
    first_insn = sc.switch_block->get_last_insn()->insn;
    live_in.insert(first_insn->src(0));
  } else {
    always_assert(sc.closures.size() == 1);
    const auto* c = sc.closures.front();
    auto it = c->target->get_first_insn();
    if (it == c->target->end()) {
      return CandidateFate::Evaluation_EmptyHead;
    }
    first_insn = it->insn;
  }
  // The launchpad returns where the closure started. In a constructor whose
  // receiver may not be initialized there yet, that is a return ART's
  // verifier rejects, e.g. when a check that throws runs before the call of
  // the superclass constructor.
  if (method::is_init(ctx.method)) {
    if (!ctx.receiver->has_value()) {
      return CandidateFate::Evaluation_ReceiverUninitialized;
    }
    auto opt_uninitialized = ctx.uninitialized_objects->at(first_insn)
                                 .get(**ctx.receiver)
                                 .get_constant();
    if (!opt_uninitialized || *opt_uninitialized) {
      return CandidateFate::Evaluation_ReceiverUninitialized;
    }
  }
  std::vector<reg_t> ordered_live_in(live_in.begin(), live_in.end());
  if (ordered_live_in.size() > static_cast<size_t>(ctx.config.max_live_in)) {
    return CandidateFate::Evaluation_TooManyLiveIns;
  }
  std::sort(ordered_live_in.begin(), ordered_live_in.end());

  auto in_cover = [&ctx, &sc](IRInstruction* insn) {
    return sc.reduced_components.count(ctx.insns->at(insn)) != 0u;
  };
  // A suffix whose head is a loop is entered at the loop header, so a
  // definition of a live-in inside the loop reaches the entry too, through the
  // back edge. The launchpad passes only the definitions from outside the
  // closure. Typing the parameter by the uses of an in-loop definition could
  // declare it narrower than the value the host passes.
  auto passed_defs = [&](reg_t reg) {
    auto defs = ctx.ota->immediate_defs_at(first_insn, reg);
    defs.filter([&](IRInstruction* def) { return !in_cover(def); });
    return defs;
  };
  for (auto reg : ordered_live_in) {
    auto defs = ctx.ota->defs_at(first_insn, reg);
    if (defs.size() == 1 && opcode::is_a_const((*defs.begin())->opcode())) {
      sc.args.push_back((ClosureArgument){reg, nullptr, *defs.begin()});
      continue;
    }
    const auto* type = art::declare_parameter(
        ctx.ota->demand_of_uses(passed_defs(reg), in_cover),
        [&]() { return ctx.ota->value_at(first_insn, reg); });
    if (type == nullptr) {
      return CandidateFate::Evaluation_LiveInUntypable;
    }
    // The type demand is a meet over the uses, so it can name a type that no
    // individual use named -- possibly an external one above the min-sdk
    // floor, which type-checks at build time and fails to resolve on an old
    // device.
    if (ctx.ref_checker != nullptr && !ctx.ref_checker->check_type(type)) {
      return CandidateFate::Evaluation_ArgTypeIllegal;
    }
    sc.args.push_back((ClosureArgument){reg, type, nullptr});
    if (type::is_object(type)) {
      const auto& uninitialized_env = ctx.uninitialized_objects->at(first_insn);
      auto opt_uninitialized = uninitialized_env.get(reg).get_constant();
      if (!opt_uninitialized || *opt_uninitialized) {
        return CandidateFate::Evaluation_LiveInUninitialized;
      }
    }
  }

  // Without a net gate, a suffix is decided by the size floors and the
  // overhead ratio alone. A candidate its gate covers (see `score()`) is kept
  // only when its net saving (`split_net_saving`, weighted by
  // `net_oat_weight`) is positive, so a tail that only the gate's lowered
  // floors admit is split only when it pays. The cold gate is additive: a Cold
  // split the legacy floors admit is not evaluated, because
  // `min_cold_split_size` guards constraints the net saving does not model.
  if (sc.net_saving_use == NetSavingUse::None) {
    return std::nullopt;
  }
  // `score` evaluates no candidate on an uncompiled host: every suffix net
  // saving it reads needs a compiled host.
  redex_assert(ctx.host_compiled);
  const auto& terms = sc.net_terms.emplace(
      split_net_saving(net_saving_input(sc, ctx.method, *ctx.liveness_fp_iter),
                       ctx.config, ctx.host_compiled));
  if (terms.net <= 0) {
    TRACE(MS, 3,
          "net refused suffix %s at B%zu: saved %" PRId64 " added_ccuc %" PRId64
          " dex_added %" PRId64 " net %f",
          SHOW(ctx.method), (size_t)sc.closures.front()->target->id(),
          terms.saved, terms.added_ccuc, terms.dex_added, terms.net);
    return CandidateFate::Evaluation_NetNotPositive;
  }
  return std::nullopt;
}

// Filter out overlapping closures, unsplittable closures (when we cannot
// determine what type we can use as parameter type of a split method), and
// filter out closures which don't meet the configured liveness threshold.
std::vector<SplittableClosure> to_splittable_closures(
    const std::shared_ptr<MethodClosures>& mcs,
    std::vector<ScoredClosure> scored_closures,
    const Config& config,
    Stats& stats,
    bool host_compiled,
    // Null on the top-level-switch path, which has no store context.
    const RefChecker* ref_checker) {
  std::vector<SplittableClosure> splittable_closures;
  // We sort closures in a way that allows us to quickly prune contained
  // closures if we found a viable containing closure.
  std::sort(
      scored_closures.begin(), scored_closures.end(), [](auto& a, auto& b) {
        if (a.reduced_components.size() != b.reduced_components.size()) {
          return a.reduced_components.size() > b.reduced_components.size();
        }
        if (a.is_switch() != b.is_switch()) {
          return a.is_switch() < b.is_switch();
        }
        return a.id() < b.id();
      });

  // Now we do the expensive analysis of the remaining scored closures.
  auto* method = mcs->method;
  Lazy<OutlinerTypeAnalysis> ota(
      [method] { return std::make_unique<OutlinerTypeAnalysis>(method); });
  const auto& rcfg = *mcs->rcfg;
  auto& cfg = method->get_code()->cfg();
  Lazy<LivenessFixpointIterator> liveness_fp_iter([&cfg] {
    auto res = std::make_unique<LivenessFixpointIterator>(cfg);
    res->run({});
    return res;
  });
  Lazy<UninitializedObjectEnvironments> uninitialized_objects([method] {
    return std::make_unique<UninitializedObjectEnvironments>(
        get_uninitialized_object_environments(method));
  });
  Lazy<UnorderedMap<IRInstruction*, const ReducedBlock*>> insns([&rcfg] {
    auto res =
        std::make_unique<UnorderedMap<IRInstruction*, const ReducedBlock*>>();
    for (const auto* reduced_block : rcfg.blocks()) {
      for (const auto* block : UnorderedIterable(reduced_block->blocks)) {
        for (const auto& mie : InstructionIterable(block)) {
          res->emplace(mie.insn, reduced_block);
        }
      }
    }
    return res;
  });
  // A constructor's receiver register, or none if the constructor redefines
  // it, in which case its initialization cannot be tracked.
  Lazy<std::optional<reg_t>> receiver([&cfg]() {
    // Read only in an instance constructor, whose first parameter is its
    // receiver.
    auto params = cfg.get_param_instructions();
    always_assert(params.begin() != params.end());
    auto receiver_reg = params.begin()->insn->dest();
    for (const auto& mie : cfg::ConstInstructionIterable(cfg)) {
      if (!opcode::is_a_load_param(mie.insn->opcode()) &&
          mie.insn->has_dest() && mie.insn->dest() == receiver_reg) {
        return std::make_unique<std::optional<reg_t>>(std::nullopt);
      }
    }
    return std::make_unique<std::optional<reg_t>>(receiver_reg);
  });
  UnorderedSet<const ReducedBlock*> covered;

  // Every scored suffix is a candidate from here on.
  stats.suffix_fates.candidates += scored_closures.size();
  auto record = [&stats](const ScoredClosure& sc, CandidateFate fate) {
    stats.record(
        SplitKind::Suffix,
        [&sc] { return SplittableClosure::head_ids(sc.closures); },
        sc.net_terms, fate, sc.covered_code_units);
  };

  CandidateEvalContext ctx{ota,    liveness_fp_iter, uninitialized_objects,
                           insns,  receiver,         ref_checker,
                           config, host_compiled,    method};
  std::erase_if(scored_closures, [&covered, &ctx, &record](auto& sc) {
    for (auto* c : sc.closures) {
      if (covered.count(c->reduced_block)) {
        // We already have this contained closure covered by a valid
        // containing closure
        record(sc, CandidateFate::Selection_Displaced);
        return true;
      }
    }
    if (auto fate = evaluate_candidate(sc, ctx)) {
      record(sc, *fate);
      return true;
    }
    insert_unordered_iterable(covered, sc.reduced_components);
    return false;
  });
  // remaining scored closures should be all non-overlapping now
  for (auto& sc : scored_closures) {
    if (traceEnabled(MS, 2)) {
      std::ostringstream oss;
      oss << "=== selected " << show(method) << ": " << sc.split_size << " + "
          << sc.remaining_size << " >= " << mcs->original_size << ", "
          << describe(sc.hot_split_kind) << "\n";
      oss << "   args: ";
      for (auto [reg, type, def] : sc.args) {
        oss << "v" << reg << ":"
            << (type == nullptr ? show(def->opcode()) : show(type)) << ", ";
      }
      oss << "\n";
      oss << "   - ";
      std::vector<const cfg::Block*> blocks;
      UnorderedSet<const ReducedBlock*> reachable;
      for (const auto* c : sc.closures) {
        insert_unordered_iterable(blocks, blocks.end(),
                                  c->reduced_block->blocks);
        oss << "R" << c->reduced_block->id << ",";
        auto c_reachable = rcfg.reachable(c->reduced_block);
        insert_unordered_iterable(reachable, c_reachable);
      }
      oss << ": ";
      std::sort(blocks.begin(), blocks.end(),
                [](auto* b, auto* c) { return b->id() < c->id(); });
      for (const auto* b : blocks) {
        oss << "B" << b->id() << ", ";
      }
      oss << "reaches ";
      for (const auto* other : unordered_to_ordered(
               reachable, [](const ReducedBlock* x, const ReducedBlock* y) {
                 return x->id < y->id;
               })) {
        oss << "R" << other->id << ", ";
      }
      oss << "\n";
      oss << ::show(method->get_code()->cfg());
      TRACE(MS, 2, "%s", oss.str().c_str());
    }
    auto rank = static_cast<double>(sc.split_size) *
                static_cast<double>(mcs->original_size) /
                static_cast<double>(sc.split_size + sc.remaining_size);
    auto added_code_size =
        sc.split_size + sc.remaining_size - mcs->original_size;
    splittable_closures.push_back((SplittableClosure){
        .method_closures = mcs,
        .switch_block = sc.switch_block,
        .closures = std::move(sc.closures),
        .grouped_heads = std::move(sc.grouped_heads),
        .args = std::move(sc.args),
        .rank = rank,
        .added_code_size = added_code_size,
        .hot_split_kind = sc.hot_split_kind,
        .is_large_packed_switch = sc.is_large_packed_switch,
        .creates_large_sparse_switch = sc.creates_large_sparse_switch,
        .destroys_large_packed_switch = sc.destroys_large_packed_switch,
        .net_terms = sc.net_terms,
        .covered_code_units = sc.covered_code_units,
        .below_legacy_floors = sc.below_legacy_floors});
  }
  return splittable_closures;
};
} // namespace

namespace method_splitting_impl {

HotSplitKind classify_hot_split_kind(
    const std::vector<const Closure*>& closures) {
  bool any_src_hot{false};
  bool any_target_hot{false};
  for (const auto* c : closures) {
    for (const auto* pred : UnorderedIterable(c->reduced_block->preds)) {
      any_src_hot |= pred->src->is_hot;
    }
    any_target_hot |= c->reduced_block->is_hot;
  }
  if (!any_src_hot) {
    return HotSplitKind::Cold;
  }
  return any_target_hot ? HotSplitKind::Hot : HotSplitKind::HotCold;
}

StoreRefCheckers::StoreRefCheckers(const DexStoresVector& stores,
                                   bool normal_primary_dex,
                                   const api::AndroidSDK* min_sdk_api)
    : m_xstores(stores, normal_primary_dex) {
  m_ref_checkers.reserve(m_xstores.store_count());
  for (size_t store_idx = 0; store_idx < m_xstores.store_count(); store_idx++) {
    m_ref_checkers.push_back(
        std::make_unique<RefChecker>(&m_xstores, store_idx, min_sdk_api));
  }
}

std::vector<const DexType*> SplittableClosure::get_arg_types() const {
  std::vector<const DexType*> arg_types;
  for (auto arg : args) {
    if (arg.type != nullptr) {
      arg_types.push_back(arg.type);
    }
  }
  return arg_types;
}

ConcurrentMap<DexType*, std::vector<SplittableClosure>>
select_splittable_closures_based_on_costs(
    const ConcurrentSet<DexMethod*>& methods,
    const Config& config,
    const StoreRefCheckers& store_ref_checkers,
    InsertOnlyConcurrentSet<const DexMethod*>* concurrent_hot_methods,
    InsertOnlyConcurrentMap<DexMethod*, size_t>*
        concurrent_splittable_no_optimizations_methods,
    Stats& stats) {
  Timer t("select_splittable_closures_based_on_costs");
  ConcurrentMap<DexType*, std::vector<SplittableClosure>>
      concurrent_splittable_closures;
  auto concurrent_process_method = [&](DexMethod* method) {
    if (method->rstate.should_not_outline()) {
      return;
    }
    normalize_cfg_for_splitting(method, config.split_block_size);
    auto rcfg = reduce_cfg(method);
    // One probe of the shared hot set per method: nothing inserts into it
    // during selection, so all three uses below see the same answer.
    const bool baseline_hot = (concurrent_hot_methods != nullptr) &&
                              (concurrent_hot_methods->count(method) != 0u);
    auto is_sufficiently_large = [&]() {
      if (rcfg->code_size() >= config.min_original_size) {
        return true;
      }
      if (baseline_hot &&
          rcfg->code_size() >= config.min_original_size_hot_method) {
        return true;
      }
      if (method->rstate.too_large_for_inlining_into() &&
          rcfg->code_size() >=
              config.min_original_size_too_large_for_inlining) {
        return true;
      }
      return false;
    };
    if (!is_sufficiently_large()) {
      return;
    }

    auto mcs = discover_closures(method, std::move(rcfg));
    if (!mcs) {
      return;
    }
    auto& cfg = method->get_code()->cfg();

    std::vector<ScoredClosure> scored_closures;
    auto adjustment = cfg.get_size_adjustment(
        /* assume_no_unreachable_blocks */ true);
    bool is_hot = baseline_hot &&
                  mcs->original_size >= config.min_original_size_hot_method;
    bool is_huge =
        mcs->original_size + adjustment > config.huge_threshold ||
        (method->rstate.too_large_for_inlining_into() &&
         mcs->original_size >= config.min_original_size_too_large_for_inlining);
    auto begin = config.max_overhead_ratio;
    auto end = is_huge  ? config.max_huge_overhead_ratio
               : is_hot ? config.max_hot_overhead_ratio
                        : config.max_overhead_ratio;
    for (auto r = begin; scored_closures.empty() && r <= end; r *= 2) {
      scored_closures = get_scored_closures(config, *mcs, baseline_hot, r);
    }
    if (scored_closures.empty()) {
      return;
    }
    if (method->rstate.no_optimizations()) {
      if (concurrent_splittable_no_optimizations_methods != nullptr) {
        concurrent_splittable_no_optimizations_methods->emplace(
            method, mcs->original_size + adjustment);
      }
      return;
    }
    // A host compiled from the baseline profile is the only one whose cold
    // code a split takes out of compiled code: only there does the net saving
    // count anything as saved.
    auto splittable_closures =
        to_splittable_closures(mcs, std::move(scored_closures), config, stats,
                               /*host_compiled=*/baseline_hot,
                               &store_ref_checkers.get(method->get_class()));
    concurrent_splittable_closures.update(
        method->get_class(), [&](auto, auto& v, bool) {
          v.insert(v.end(),
                   std::make_move_iterator(splittable_closures.begin()),
                   std::make_move_iterator(splittable_closures.end()));
        });
  };
  workqueue_run<DexMethod*>(concurrent_process_method, methods);
  return concurrent_splittable_closures;
}

InsertOnlyConcurrentMap<DexMethod*, std::vector<SplittableClosure>>
select_splittable_closures_from_top_level_switch_cases(
    const std::vector<DexMethod*>& methods, size_t max_live_in) {
  Timer t("select_splittable_closures_from_top_level_switch_cases");
  InsertOnlyConcurrentMap<DexMethod*, std::vector<SplittableClosure>>
      concurrent_splittable_closures;
  // Unscored suffix candidates: no size floor, no net saving, no region.
  Config config;
  config.max_live_in = static_cast<int64_t>(max_live_in);
  // The fates of these unscored candidates are not reported.
  Stats stats;
  auto concurrent_process_method = [&](DexMethod* method) {
    if (method->rstate.no_optimizations() ||
        method->rstate.should_not_outline()) {
      TRACE(SWOL, 2, "%s is marked as do-not-optimize or no-outlining",
            SHOW(method));
      return;
    }

    auto& cfg = method->get_code()->cfg();
    normalize_cfg_for_splitting(method);
    auto rcfg = reduce_cfg(method);

    auto mcs = discover_closures(method, std::move(rcfg));
    if (!mcs) {
      TRACE(SWOL, 2, "%s doesn't have closures:\n%s", SHOW(method), SHOW(cfg));
      return;
    }

    auto* entry_block = cfg.entry_block();
    if (entry_block->branchingness() != opcode::BRANCH_SWITCH) {
      TRACE(SWOL, 2, "%s doesn't have top-level switch:\n%s", SHOW(method),
            SHOW(cfg));
      return;
    }
    auto* default_block = entry_block->goes_to();

    std::vector<ScoredClosure> scored_closures;
    for (auto& c : mcs->closures) {
      if (c.srcs.size() != 1 || *unordered_any(c.srcs) != entry_block) {
        continue;
      }
      if (c.reduced_block->blocks.count(default_block) != 0u) {
        // We don't bother with the fall-through case that typically throws an
        // exception.
        continue;
      }
      ScoredClosure sc{
          .switch_block = nullptr,
          .closures = {&c},
          .grouped_heads = collect_head_ids({&c}),
          .reduced_components = {},
          .args = {},
      };
      insert_unordered_iterable(sc.reduced_components, c.reduced_components);
      scored_closures.emplace_back(std::move(sc));
    }
    auto splittable_closures =
        to_splittable_closures(mcs, std::move(scored_closures), config, stats,
                               /*host_compiled=*/false,
                               /*ref_checker=*/nullptr);
    if (!splittable_closures.empty()) {
      concurrent_splittable_closures.emplace(method,
                                             std::move(splittable_closures));
    }
  };
  workqueue_run<DexMethod*>(concurrent_process_method, methods);
  return concurrent_splittable_closures;
}

// Exclude methods containing loadLibrary/loadLibraryUnsafe calls from
// splitting. Splitting these methods separates the const-string (library
// name) from the invoke, which causes ReachableNativesPass to crash.
bool has_load_library_call(const DexMethod* method) {
  const auto* code = method->get_code();
  if (code == nullptr || !code->cfg_built()) {
    return false;
  }
  for (auto* block : code->cfg().blocks()) {
    for (auto& mie : *block) {
      if (mie.type != MFLOW_OPCODE) {
        continue;
      }
      auto* insn = mie.insn;
      if (!insn->has_method() || !opcode::is_invoke_static(insn->opcode())) {
        continue;
      }
      auto callee_name = insn->get_method()->get_name()->str();
      if (callee_name != "loadLibrary" && callee_name != "loadLibraryUnsafe") {
        continue;
      }
      auto cls_name = insn->get_method()->get_class()->str();
      if (cls_name == "Lcom/facebook/soloader/SoLoader;" ||
          cls_name == "Lcom/facebook/soloader/nativeloader/NativeLoader;") {
        return true;
      }
    }
  }
  return false;
}

namespace {

// Instructions that compile to a call out of the method: invokes, allocations
// (runtime entry points) and `unreachable`, which is lowered to a call of
// `UnreachableException.createAndThrow`.
bool is_runtime_call(IROpcode op) {
  return opcode::is_an_invoke(op) || op == OPCODE_NEW_INSTANCE ||
         op == OPCODE_NEW_ARRAY || op == OPCODE_FILLED_NEW_ARRAY ||
         op == IOPCODE_UNREACHABLE;
}

} // namespace

void RareSuffixSelection::finish(const ConcurrentSet<DexMethod*>& split) && {
  for (auto&& [method, code] : UnorderedIterable(m_original_code)) {
    if (split.count(method) == 0) {
      method->set_code(std::move(code));
    }
  }
  m_original_code.clear();
  m_splittable_closures.clear();
}

RareSuffixSelection::~RareSuffixSelection() {
  std::move(*this).finish(/* split */ {});
}

namespace {

// The largest count the first source block of `b` carries over all
// interactions, or none if it carries none.
std::optional<float> block_count(const cfg::Block* b) {
  const auto* sb = source_blocks::get_first_source_block(b);
  if (sb == nullptr) {
    return std::nullopt;
  }
  std::optional<float> count;
  sb->foreach_val([&count](const auto& v) {
    if (v) {
      count = std::max(count.value_or(0.0f), v->val);
    }
  });
  return count;
}

} // namespace

RareSuffixSelection::RareSuffixSelection(
    const std::vector<DexMethod*>& methods,
    const Config& config,
    size_t min_suffix_runtime_calls,
    std::optional<float> max_returning_suffix_ratio,
    const std::function<size_t(const DexMethod*)>& compiled_copies,
    const StoreRefCheckers& store_ref_checkers,
    Stats& stats,
    RareSuffixSelectionStats& selection_stats) {
  Timer t("RareSuffixSelection");
  const size_t lowered_unreachable_extra =
      baseline_profiles::lowered_unreachable_extra_code_units();
  workqueue_run<DexMethod*>(
      [&](DexMethod* method) {
        if (method->rstate.no_optimizations() ||
            method->rstate.should_not_outline() ||
            has_load_library_call(method)) {
          selection_stats.unsplittable++;
          return;
        }
        always_assert_log(!method->get_code()->has_try_blocks(),
                          "%s has try blocks", SHOW(method));
        // How often the method runs, for a suffix that returns; read before
        // anything changes. Set only when the method ran: in a method that
        // never ran, every count is zero, which says nothing about which of
        // its suffixes run rarely.
        std::optional<float> entry_count;
        if (max_returning_suffix_ratio) {
          entry_count = block_count(method->get_code()->cfg().entry_block());
          if (!entry_count) {
            selection_stats.no_block_counts++;
          } else if (*entry_count <= 0.0f) {
            selection_stats.method_never_ran++;
            entry_count = std::nullopt;
          }
        }
        auto original_code = method->release_code();
        method->set_code(std::make_unique<IRCode>(*original_code));
        normalize_cfg_for_splitting(method);
        auto mcs = discover_closures(method, reduce_cfg(method));
        bool any_rare_suffix = false;
        std::vector<ScoredClosure> scored_closures;
        if (mcs != nullptr) {
          auto& cfg = method->get_code()->cfg();
          auto reaching_return = cfg.blocks_reaching_return();
          auto copies = compiled_copies(method);
          for (const auto& c : mcs->closures) {
            if (reaching_return.count(c.target) != 0u) {
              // A suffix that returns qualifies when it runs rarely: at most
              // `max_returning_suffix_ratio` times as often as the method.
              if (!entry_count) {
                continue;
              }
              auto suffix_count = block_count(c.target);
              if (!suffix_count ||
                  *suffix_count > *max_returning_suffix_ratio * *entry_count) {
                continue;
              }
              selection_stats.returning_suffixes++;
              // A suffix takes every block its head reaches, a return among
              // them, so its split returns too; the pass's per-reason reports
              // rely on that.
              always_assert_log(
                  unordered_any_of(c.reduced_components,
                                   [](const ReducedBlock* rb) {
                                     return unordered_any_of(
                                         rb->blocks, [](const cfg::Block* b) {
                                           return b->branchingness() ==
                                                  opcode::BRANCH_RETURN;
                                         });
                                   }),
                  "returning suffix without a return in %s", SHOW(method));
            }
            any_rare_suffix = true;
            size_t runtime_calls = 0;
            for (const auto* rb : UnorderedIterable(c.reduced_components)) {
              for (const auto* b : UnorderedIterable(rb->blocks)) {
                for (const auto& mie : InstructionIterable(b)) {
                  runtime_calls += is_runtime_call(mie.insn->opcode()) ? 1 : 0;
                }
              }
            }
            if (runtime_calls < min_suffix_runtime_calls) {
              continue;
            }
            // Sized and evaluated the way `score` sizes and evaluates a
            // suffix of a compiled host, with a compiled copy per inlined
            // copy.
            ScoredClosure sc{
                .switch_block = nullptr,
                .closures = {&c},
                .grouped_heads = collect_head_ids({&c}),
                .reduced_components = c.reduced_components,
                .args = {},
            };
            sc.covered_code_units = code_size(sc.reduced_components);
            sc.split_size = config.cost_split_method + sc.covered_code_units;
            sc.hot_split_kind = classify_hot_split_kind({&c});
            const auto kept = host_blocks_kept(cfg, sc);
            for (const auto* b : UnorderedIterable(kept)) {
              sc.remaining_size += b->estimate_code_units();
            }
            size_eviction(kept, &sc);
            // Each `unreachable` is lowered to a call and its move-result,
            // which every compiled copy of the method carries.
            for (const auto* rb : UnorderedIterable(sc.reduced_components)) {
              for (const auto* b : UnorderedIterable(rb->blocks)) {
                const size_t extra =
                    lowered_unreachable_extra *
                    method::count_opcode_of_types(*b, {IOPCODE_UNREACHABLE});
                if (kept.contains(const_cast<cfg::Block*>(b))) {
                  sc.duplicated_dex_code_units += extra;
                  continue;
                }
                sc.evicted_size += extra;
                if (is_hot(b)) {
                  sc.evicted_hot_size += extra;
                }
              }
            }
            sc.net_saving_use = NetSavingUse::Gate;
            sc.compiled_copies = copies;
            scored_closures.emplace_back(std::move(sc));
          }
        }
        std::vector<SplittableClosure> splittable_closures;
        if (!any_rare_suffix) {
          selection_stats.no_rare_suffix++;
        } else if (scored_closures.empty()) {
          selection_stats.too_few_runtime_calls++;
        } else {
          splittable_closures = to_splittable_closures(
              mcs, std::move(scored_closures), config, stats,
              /* host_compiled */ true,
              &store_ref_checkers.get(method->get_class()));
          if (splittable_closures.empty()) {
            selection_stats.not_splittable++;
          }
        }
        if (splittable_closures.empty()) {
          method->set_code(std::move(original_code));
          return;
        }
        m_original_code.emplace(method, std::move(original_code));
        m_splittable_closures.update(
            method->get_class(), [&](auto, auto& vec, bool) {
              vec.insert(vec.end(),
                         std::make_move_iterator(splittable_closures.begin()),
                         std::make_move_iterator(splittable_closures.end()));
            });
      },
      methods);
}

} // namespace method_splitting_impl
