/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "SplittableClosures.h"

#include <optional>
#include <vector>

#include <sparta/PatriciaTreeSet.h>

#include "ClosureAggregator.h"
#include "ConcurrentContainers.h"
#include "Debug.h"
#include "InstructionLowering.h"
#include "Lazy.h"
#include "Liveness.h"
#include "OutlinerTypeAnalysis.h"
#include "ReducedCFGClosureAdapter.h"
#include "Show.h"
#include "Timer.h"
#include "Trace.h"
#include "UninitializedObjects.h"
#include "WorkQueue.h"

namespace {

using namespace method_splitting_impl;
using namespace outliner_impl;
using namespace uninitialized_objects;

struct ScoredClosure {
  cfg::Block* switch_block{nullptr};
  std::vector<const Closure*> closures;
  UnorderedSet<const ReducedBlock*> reduced_components;
  size_t split_size{};
  size_t remaining_size{};
  std::optional<HotSplitKind> hot_split_kind{std::nullopt};
  bool is_large_packed_switch{false};
  bool creates_large_sparse_switch{false};
  bool destroys_large_packed_switch{false};
  std::vector<ClosureArgument> args;

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
        for (const auto* e : UnorderedIterable(pred->edges)) {
          if (e->src() != switch_block) {
            except_preds.erase(pred);
            break;
          } else if (e->type() == cfg::EDGE_BRANCH) {
            except_case_keys->insert(*e->case_key());
          }
        }
      }
    }
  }
  return except_preds;
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

std::optional<ScoredClosure> score(
    const Config& config,
    const MethodClosures& mcs,
    float max_overhead_ratio,
    cfg::Block* switch_block,
    bool is_large_packed_switch,
    const std::vector<const Closure*>& closures) {
  ScoredClosure sc{
      .switch_block = switch_block,
      .closures = closures,
      .reduced_components = {},
      .args = {},
  };
  for (const auto* c : closures) {
    insert_unordered_iterable(sc.reduced_components, c->reduced_components);
  }
  auto reduced_components_code_size = code_size(sc.reduced_components);
  sc.split_size = config.cost_split_method + reduced_components_code_size;
  if (closures.size() > 1) {
    sc.split_size += config.cost_split_switch +
                     config.cost_split_switch_case * closures.size();
  }
  bool any_src_hot{false};
  bool any_target_hot{false};
  for (const auto* c : closures) {
    for (const auto* pred : UnorderedIterable(c->reduced_block->preds)) {
      any_src_hot |= pred->src->is_hot;
    }
    any_target_hot |= c->reduced_block->is_hot;
  }
  if (any_src_hot) {
    if (any_target_hot) {
      if (sc.split_size < config.min_hot_split_size) {
        return std::nullopt;
      }
      sc.hot_split_kind = HotSplitKind::Hot;
    } else {
      if (sc.split_size < config.min_hot_cold_split_size) {
        return std::nullopt;
      }
      sc.hot_split_kind = HotSplitKind::HotCold;
    }
  } else {
    if (sc.split_size < config.min_cold_split_size) {
      return std::nullopt;
    }
    sc.hot_split_kind = HotSplitKind::Cold;
  }
  always_assert(reduced_components_code_size <= mcs.original_size);
  auto remaining_size_reduction =
      closures.size() > 1
          ? config.cost_split_switch_case * (closures.size() - 1)
          : 0;
  auto estimated_remaining_size =
      mcs.original_size - reduced_components_code_size;
  estimated_remaining_size =
      estimated_remaining_size < remaining_size_reduction
          ? 0
          : estimated_remaining_size - remaining_size_reduction;

  switch (sc.hot_split_kind.value()) {
  case HotSplitKind::Hot:
  case HotSplitKind::HotCold:
    if (estimated_remaining_size < config.min_hot_split_size) {
      return std::nullopt;
    }
    break;
  case HotSplitKind::Cold:
    if (estimated_remaining_size < config.min_cold_split_size) {
      return std::nullopt;
    }
    break;
  default:
    not_reached();
  }

  UnorderedSet<int32_t> except_case_keys;
  auto except_preds = get_except_preds(
      switch_block, closures, sc.reduced_components, &except_case_keys);
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

  const auto& rcfg = *mcs.rcfg;
  auto remaining_blocks = rcfg.reachable(rcfg.entry_block(), except_preds);
  sc.remaining_size = code_size(remaining_blocks);
  sc.remaining_size = sc.remaining_size < remaining_size_reduction
                          ? 0
                          : sc.remaining_size - remaining_size_reduction;
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
    float max_overhead_ratio,
    cfg::Block* switch_block,
    bool is_large_packed_switch,
    std::vector<const Closure*> aggregated) {
  while (aggregated.size() > 1) {
    auto opt_sc = score(config, mcs, max_overhead_ratio, switch_block,
                        is_large_packed_switch, aggregated);
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
    const auto* min_edge = *std::min_element(
        expanded_preds.begin(), expanded_preds.end(),
        [](auto* e, auto* f) { return e->case_key() < f->case_key(); });
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
      return select_prefix(config, mcs, max_overhead_ratio, switch_block,
                           is_large_packed_switch, std::move(aggregated));
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
  return select_prefix(config, mcs, max_overhead_ratio, switch_block,
                       is_large_packed_switch, std::move(aggregated));
};

// Select closures that meet the configured size thresholds, and score them.
std::vector<ScoredClosure> get_scored_closures(const Config& config,
                                               const MethodClosures& mcs,
                                               float max_overhead_ratio) {
  // For all possible closures, do some quick filtering, and score the
  // surviving ones
  std::vector<ScoredClosure> scored_closures;
  UnorderedMap<cfg::Block*, std::vector<const Closure*>>
      remaining_switch_case_closures;
  for (const auto& c : mcs.closures) {
    auto opt_sc = score(config, mcs, max_overhead_ratio,
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
  for (auto&& [switch_block, switched] :
       UnorderedIterable(remaining_switch_case_closures)) {
    auto is_large_packed_switch =
        is_large(config, switch_block) && is_packed(switch_block);
    for (const auto& predicate : predicates) {
      auto opt_sc = aggregate(config, mcs, max_overhead_ratio, switch_block,
                              is_large_packed_switch, switched, predicate);
      if (opt_sc) {
        scored_closures.push_back(std::move(*opt_sc));
        break;
      }
    }
  }
  return scored_closures;
};

// Filter out overlapping closures, unsplittable closures (when we cannot
// determine what type we can use as parameter type of a split method), and
// filter out closures which don't meet the configured liveness threshold.
std::vector<SplittableClosure> to_splittable_closures(
    size_t max_live_in,
    const std::shared_ptr<MethodClosures>& mcs,
    std::vector<ScoredClosure> scored_closures,
    // Both null on the top-level-switch path, which has no store context.
    const RefChecker* ref_checker,
    std::atomic<size_t>* arg_type_illegal) {
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
  Lazy<live_range::DefUseChains> def_uses([&cfg]() {
    return std::make_unique<live_range::DefUseChains>(
        live_range::Chains(cfg).get_def_use_chains());
  });
  UnorderedSet<const ReducedBlock*> covered;
  std::erase_if(scored_closures, [&covered, &ota, &liveness_fp_iter,
                                  &uninitialized_objects, &insns, &def_uses,
                                  max_live_in, ref_checker,
                                  arg_type_illegal](auto& sc) {
    for (auto* c : sc.closures) {
      if (covered.count(c->reduced_block)) {
        // We already have this contained closure covered by a valid
        // containing closure
        return true;
      }
    }

    sparta::PatriciaTreeSet<reg_t> live_in;
    for (auto* c : sc.closures) {
      live_in.union_with(
          liveness_fp_iter->get_live_in_vars_at(c->target).elements());
    }
    IRInstruction* first_insn;
    if (sc.switch_block) {
      always_assert(sc.closures.size() > 1);
      first_insn = sc.switch_block->get_last_insn()->insn;
      live_in.insert(first_insn->src(0));
    } else {
      always_assert(sc.closures.size() == 1);
      auto* c = sc.closures.front();
      auto it = c->target->get_first_insn();
      if (it == c->target->end()) {
        return true;
      }
      first_insn = it->insn;
    }
    std::vector<reg_t> ordered_live_in(live_in.begin(), live_in.end());
    if (ordered_live_in.size() > max_live_in) {
      return true;
    }
    std::sort(ordered_live_in.begin(), ordered_live_in.end());

    ReducedCFGClosureAdapter rcfgca(*ota, first_insn, insns,
                                    sc.reduced_components, def_uses);
    for (auto reg : ordered_live_in) {
      auto defs = rcfgca.get_defs(reg);
      if (defs.size() == 1 && opcode::is_a_const((*defs.begin())->opcode())) {
        sc.args.push_back((ClosureArgument){reg, nullptr, *defs.begin()});
        continue;
      }
      const auto* type = ota->get_type_demand(rcfgca, reg);
      if (!type) {
        return true;
      }
      // The type demand is a meet over the uses, so it can name a type that no
      // individual use named -- possibly an external one above the min-sdk
      // floor, which type-checks at build time and fails to resolve on an old
      // device.
      if (ref_checker != nullptr && !ref_checker->check_type(type)) {
        ++*arg_type_illegal;
        return true;
      }
      sc.args.push_back((ClosureArgument){reg, type, nullptr});
      if (type::is_object(type)) {
        const auto& uninitialized_env = uninitialized_objects->at(first_insn);
        auto opt_uninitialized = uninitialized_env.get(reg).get_constant();
        if (!opt_uninitialized || *opt_uninitialized) {
          return true;
        }
      }
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
      for (const auto* other : UnorderedIterable(reachable)) {
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
        mcs, sc.switch_block, std::move(sc.closures), std::move(sc.args), rank,
        added_code_size, sc.hot_split_kind, sc.is_large_packed_switch,
        sc.creates_large_sparse_switch, sc.destroys_large_packed_switch});
  }
  return splittable_closures;
};
} // namespace

namespace method_splitting_impl {

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
    std::atomic<size_t>* arg_type_illegal) {
  Timer t("select_splittable_closures_based_on_costs");
  ConcurrentMap<DexType*, std::vector<SplittableClosure>>
      concurrent_splittable_closures;
  auto concurrent_process_method = [&](DexMethod* method) {
    auto rcfg = reduce_cfg(method, config.split_block_size);
    auto is_sufficiently_large = [&]() {
      if (rcfg->code_size() >= config.min_original_size) {
        return true;
      }
      if ((concurrent_hot_methods != nullptr) &&
          (concurrent_hot_methods->count(method) != 0u) &&
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
    bool is_hot = (concurrent_hot_methods != nullptr) &&
                  (concurrent_hot_methods->count(method) != 0u) &&
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
      scored_closures = get_scored_closures(config, *mcs, r);
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
    auto splittable_closures = to_splittable_closures(
        config.max_live_in, mcs, std::move(scored_closures),
        &store_ref_checkers.get(method->get_class()), arg_type_illegal);
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
  auto concurrent_process_method = [&](DexMethod* method) {
    if (method->rstate.no_optimizations()) {
      TRACE(SWOL, 2, "%s is marked as do-not-optimize", SHOW(method));
      return;
    }

    auto& cfg = method->get_code()->cfg();
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
          .reduced_components = {},
          .args = {},
      };
      insert_unordered_iterable(sc.reduced_components, c.reduced_components);
      scored_closures.emplace_back(std::move(sc));
    }
    auto splittable_closures =
        to_splittable_closures(max_live_in, mcs, std::move(scored_closures),
                               /* ref_checker */ nullptr,
                               /* arg_type_illegal */ nullptr);
    if (!splittable_closures.empty()) {
      concurrent_splittable_closures.emplace(method,
                                             std::move(splittable_closures));
    }
  };
  workqueue_run<DexMethod*>(concurrent_process_method, methods);
  return concurrent_splittable_closures;
}

} // namespace method_splitting_impl
