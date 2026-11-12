/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

/*
 * This pass identifies traceable object allocations that don't escape, and then
 * attempts to inline all code interacting with the local object, turning all
 * instance fields into registers. The changes are only applied when the
 * estimated savings are not negative. This helps reduce...
 * - object allocations at runtime, and
 * - code size by eliminating many of the involved classes, fields and
 *   methods.
 *
 * At the core is an interprocedural escape analysis with method-level summaries
 * that...
 * - may include results of method invocations as allocations, and
 * - follows arguments to non-true-virtual method invocations.
 *
 * This pass is conservative: Any use of an object allocation that isn't fully
 * understood, e.g. an external method invocation, causes that allocation to
 * become ineligible for optimization. In any case, this pass will not transform
 * a root method with the no_optimizations annotation.
 *
 * The pass computes...
 * - method summaries, indicating whether a method allocates and returns an
 *   object that doesn't otherwise escape, and which method arguments don't
 *   escape
 * - "inline anchors", which are particular instructions (in particular methods)
 *   which produce a new unescaped object, either by directly allocating it or
 *   invoking a method that directly or indirectly allocates and returns an
 * object that doesn't otherwise escape, and then possibly use that object in
 * ways where it doesn't escape
 * - "root methods", which are all the methods which contain "inline anchors" of
 *   types whose allocation instructions are all ultimately inlinably anchored.
 * - "reduced methods", which are root methods where all inlinable anchors got
 *   fully inlined, and the fields of allocated objects got turned into
 *   registers (and the transformation does not produce estimated negative net
 *   savings)
 */

#include "ObjectEscapeAnalysis.h"

#include <optional>

#include "AtomicStatCounter.h"
#include "CFGMutation.h"
#include "ClassHierarchy.h"
#include "ConfigFiles.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexClass.h"
#include "ExpandableMethodParams.h"
#include "GlobalConfig.h"
#include "IRInstruction.h"
#include "Inliner.h"
#include "LinearScan.h"
#include "Liveness.h"
#include "MutablePriorityQueue.h"
#include "ObjectEscapeAnalysisImpl.h"
#include "ObjectEscapeAnalysisPlugin.h"
#include "PassManager.h"
#include "ReachingDefinitions.h"
#include "RedexContext.h"
#include "Show.h"
#include "Thread.h"
#include "Trace.h"
#include "Walkers.h"

using namespace sparta;
using namespace object_escape_analysis_impl;
namespace mog = method_override_graph;

namespace {

// How deep callee chains will be considered.
constexpr int MAX_INLINE_INVOKES_ITERATIONS = 8;

constexpr size_t MAX_INLINE_SIZE = 48;

// Don't even try to inline an incompletely inlinable type if a very rough
// estimate predicts an increase exceeding this threshold in code units.
constexpr int64_t INCOMPLETE_ESTIMATED_DELTA_THRESHOLD = 0;

// Overhead of having a method and its metadata.
constexpr size_t COST_METHOD = 16;

// Overhead of having a class and its metadata.
constexpr size_t COST_CLASS = 48;

// Overhead of having a field and its metadata.
constexpr size_t COST_FIELD = 8;

// Typical overhead of calling a method, without move-result overhead, times 10.
constexpr int64_t COST_INVOKE = 47;

// Typical overhead of having move-result instruction, times 10.
constexpr int64_t COST_MOVE_RESULT = 30;

// Overhead of a new-instance instruction, times 10.
constexpr int64_t COST_NEW_INSTANCE = 20;

// Minimum savings required to select a reduced method variant.
constexpr int64_t SAVINGS_THRESHOLD = 0;

using InlineAnchorsOfType =
    UnorderedMap<DexMethod*, UnorderedSet<IRInstruction*>>;
ConcurrentMap<const DexType*, InlineAnchorsOfType> compute_inline_anchors(
    const Scope& scope,
    const method_override_graph::Graph& method_override_graph,
    const MethodSummaries& method_summaries,
    const UnorderedSet<DexClass*>& excluded_classes,
    CalleesCache* callees_cache,
    MethodSummaryCache* method_summary_cache) {
  Timer t("compute_inline_anchors");
  ConcurrentMap<const DexType*, InlineAnchorsOfType> inline_anchors;
  walk::parallel::code(scope, [&](DexMethod* method, IRCode& /*code*/) {
    Analyzer analyzer(method_override_graph, excluded_classes, method_summaries,
                      /* incomplete_marker_method */ nullptr, method,
                      callees_cache, method_summary_cache);
    auto inlinables = analyzer.get_inlinables();
    for (auto* insn : UnorderedIterable(inlinables)) {
      auto [callee, type] = resolve_inlinable(method_summaries, method, insn);
      TRACE(OEA, 3, "[object escape analysis] inline anchor [%s] %s",
            SHOW(method), SHOW(insn));
      inline_anchors.update(type, [&](auto*, auto& map, bool) {
        // NOLINTNEXTLINE(bugprone-pointer-arithmetic-on-polymorphic-object)
        map[method].insert(insn);
      });
    }
  });
  return inline_anchors;
}

// Whether a `check-cast` to `cast_type`, applied to a tracked object of
// `anchor_type`, is guaranteed to succeed.
//
// `get_augmented_du_chains` below needs this answer in two places, and they
// MUST agree. One tracks a cast that can succeed as another def of the object;
// the other treats a cast that cannot succeed as unconditionally throwing and
// gives up on the whole reduced variant. Should they ever disagree, a cast can
// be kept by one and untracked by the other: `stackify` rewrites the cast to
// write a register it created, while the uses of the original destination were
// never followed, so that destination is left read but never written. Ask the
// question here, once, so the two cannot drift apart.
bool check_cast_always_succeeds(const DexType* anchor_type,
                                const DexType* cast_type) {
  return type::is_subclass(cast_type, anchor_type);
}

live_range::DefUseChains get_augmented_du_chains(
    const method_override_graph::Graph& method_override_graph,
    DexMethod* method,
    const std::vector<const DexType*>& inline_anchor_types,
    const MethodSummaries& method_summaries,
    CalleesCache* callees_cache,
    MethodSummaryCache* method_summary_cache,
    std::function<const DexType*(const IRInstruction*)> selector,
    bool* throwing_check_cast = nullptr) {
  auto is_inlinable_check_cast = [&](const auto* insn) {
    if (insn->opcode() == OPCODE_CHECK_CAST) {
      for (const auto* t : inline_anchor_types) {
        if (check_cast_always_succeeds(t, insn->get_type())) {
          return true;
        }
      }
    }
    return false;
  };

  auto is_inlinable_invoke = [&](const auto* insn,
                                 std::optional<src_index_t> src_index =
                                     std::nullopt) {
    if (!opcode::is_an_invoke(insn->opcode())) {
      return false;
    }

    const auto* ms = resolve_invoke_method_summary(
        method_override_graph, method_summaries, insn, method, callees_cache,
        method_summary_cache);
    if (!ms->returned_param_index()) {
      return false;
    }
    return !src_index || *ms->returned_param_index() == *src_index;
  };

  auto& cfg = method->get_code()->cfg();
  live_range::MoveAwareChains chains(
      cfg, /* ignore_unreachable */ false, [&](const auto* insn) {
        return selector(insn) != nullptr || is_inlinable_check_cast(insn) ||
               is_inlinable_invoke(insn);
      });
  const auto du_chains = chains.get_def_use_chains();
  live_range::DefUseChains res;
  for (auto&& [def, def_uses] : UnorderedIterable(du_chains)) {
    const auto* inline_anchor_type = selector(def);
    if (inline_anchor_type == nullptr) {
      continue;
    }
    auto& augmented_uses = res[def];
    std::stack<live_range::Use> stack;
    auto process_uses = [&](auto& uses) {
      for (auto& use : UnorderedIterable(uses)) {
        if (opcode::is_check_cast(use.insn->opcode())) {
          if (throwing_check_cast &&
              !check_cast_always_succeeds(inline_anchor_type,
                                          use.insn->get_type())) {
            *throwing_check_cast = true;
          }
          stack.push(use);
        } else if (is_inlinable_invoke(use.insn, use.src_index)) {
          stack.push(use);
        } else {
          augmented_uses.insert(use);
        }
      }
    };
    process_uses(def_uses);
    while (!stack.empty()) {
      auto use = stack.top();
      stack.pop();
      if (augmented_uses.insert(use).second) {
        auto it = du_chains.find(use.insn);
        if (it != du_chains.end()) {
          process_uses(it->second);
        }
      }
    }
  }
  return res;
}

class InlinedEstimator {
 private:
  const method_override_graph::Graph& m_method_override_graph;
  const DexType* m_inline_anchor_type;
  const MethodSummaries& m_method_summaries;
  CalleesCache* m_callees_cache;
  using Key = std::pair<DexMethod*, const IRInstruction*>;
  LazyUnorderedMap<DexMethod*, uint32_t> m_inlined_code_sizes;
  LazyUnorderedMap<Key, live_range::Uses, boost::hash<Key>> m_uses;
  LazyUnorderedMap<Key, int64_t, boost::hash<Key>> m_deltas;

  void gather_inlinable_methods(
      DexMethod* method,
      const IRInstruction* allocation_insn,
      bool* recursive,
      UnorderedMap<Key, bool, boost::hash<Key>>* visiting) {
    auto [it, emplaced] =
        visiting->emplace((Key){method, allocation_insn}, false);
    auto& visited = it->second;
    if (!emplaced) {
      if (!visited) {
        *recursive = true;
      }
      return;
    }
    always_assert(opcode::is_new_instance(allocation_insn->opcode()) ||
                  opcode::is_an_invoke(allocation_insn->opcode()) ||
                  opcode::is_load_param_object(allocation_insn->opcode()));
    if (opcode::is_an_invoke(allocation_insn->opcode())) {
      auto* callee = resolve_invoke_method_deprecated(allocation_insn, method);
      always_assert(callee);
      const auto* callee_allocation_insn =
          m_method_summaries.at(callee).allocation_insn();
      always_assert(callee_allocation_insn);
      gather_inlinable_methods(callee, callee_allocation_insn, recursive,
                               visiting);
    }
    for (const auto& use :
         UnorderedIterable(m_uses[{method, allocation_insn}])) {
      if (opcode::is_an_invoke(use.insn->opcode())) {
        if (is_benign(use.insn->get_method())) {
          continue;
        }
        auto* callee = resolve_invoke_inlinable_callee(
            m_method_override_graph, use.insn, method, m_callees_cache,
            [this, src_index = use.src_index]() {
              always_assert(src_index == 0);
              return m_inline_anchor_type;
            });
        always_assert(callee);
        auto load_param_insns = InstructionIterable(
            callee->get_code()->cfg().get_param_instructions());
        auto* load_param_insn =
            std::next(load_param_insns.begin(), use.src_index)->insn;
        always_assert(load_param_insn);
        always_assert(opcode::is_load_param_object(load_param_insn->opcode()));
        gather_inlinable_methods(callee, load_param_insn, recursive, visiting);
      }
    }
    visited = true;
  }

 public:
  InlinedEstimator(const ObjectEscapeConfig& config,
                   const method_override_graph::Graph& method_override_graph,
                   const DexType* inline_anchor_type,
                   const MethodSummaries& method_summaries,
                   CalleesCache* callees_cache,
                   MethodSummaryCache* method_summary_cache)
      : m_method_override_graph(method_override_graph),
        m_inline_anchor_type(inline_anchor_type),
        m_method_summaries(method_summaries),
        m_callees_cache(callees_cache),
        m_inlined_code_sizes([](DexMethod* method) {
          uint32_t code_size{0};
          auto& cfg = method->get_code()->cfg();
          for (auto& mie : InstructionIterable(cfg)) {
            auto* insn = mie.insn;
            // We do the cost estimation before shrinking, so we discount moves.
            // Returns will go away after inlining.
            if (opcode::is_a_move(insn->opcode()) ||
                opcode::is_a_return(insn->opcode())) {
              continue;
            }
            code_size += mie.insn->size();
          }
          return code_size;
        }),
        m_uses([this, method_summary_cache](Key key) {
          auto* allocation_insn = const_cast<IRInstruction*>(key.second);
          auto du_chains = get_augmented_du_chains(
              m_method_override_graph, key.first, {m_inline_anchor_type},
              m_method_summaries, m_callees_cache, method_summary_cache,
              [&](const auto* insn) {
                return insn == allocation_insn ? m_inline_anchor_type : nullptr;
              });
          return std::move(du_chains[allocation_insn]);
        }),
        m_deltas([&config, this](Key key) {
          auto [method, allocation_insn] = key;
          always_assert(
              opcode::is_new_instance(allocation_insn->opcode()) ||
              opcode::is_an_invoke(allocation_insn->opcode()) ||
              opcode::is_load_param_object(allocation_insn->opcode()));
          int64_t delta = 0;
          if (opcode::is_an_invoke(allocation_insn->opcode())) {
            auto* callee =
                resolve_invoke_method_deprecated(allocation_insn, method);
            always_assert(callee);
            const auto* callee_allocation_insn =
                m_method_summaries.at(callee).allocation_insn();
            always_assert(callee_allocation_insn);
            auto callee_delta = get_delta(callee, callee_allocation_insn);
            delta += 10 * (int64_t)m_inlined_code_sizes[callee] + callee_delta -
                     config.cost_invoke - config.cost_move_result;
          } else if (allocation_insn->opcode() == OPCODE_NEW_INSTANCE) {
            delta -= config.cost_new_instance;
          }
          for (const auto& use : UnorderedIterable(m_uses[key])) {
            if (opcode::is_an_invoke(use.insn->opcode())) {
              delta -= config.cost_invoke;
              if (is_benign(use.insn->get_method())) {
                continue;
              }
              auto* callee = resolve_invoke_inlinable_callee(
                  m_method_override_graph, use.insn, method, m_callees_cache,
                  [this, src_index = use.src_index]() {
                    always_assert(src_index == 0);
                    return m_inline_anchor_type;
                  });
              always_assert(callee);
              auto load_param_insns = InstructionIterable(
                  callee->get_code()->cfg().get_param_instructions());
              auto* load_param_insn =
                  std::next(load_param_insns.begin(), use.src_index)->insn;
              always_assert(load_param_insn);
              always_assert(
                  opcode::is_load_param_object(load_param_insn->opcode()));
              auto callee_delta = get_delta(callee, load_param_insn);
              delta +=
                  10 * (int64_t)m_inlined_code_sizes[callee] + callee_delta;
              if (!callee->get_proto()->is_void()) {
                delta -= config.cost_move_result;
              }
            } else if (opcode::is_an_iget(use.insn->opcode()) ||
                       opcode::is_an_iput(use.insn->opcode()) ||
                       opcode::is_instance_of(use.insn->opcode()) ||
                       opcode::is_a_monitor(use.insn->opcode()) ||
                       opcode::is_check_cast(use.insn->opcode())) {
              delta -= 10 * (int64_t)use.insn->size();
            }
          }
          return delta;
        }) {}

  // Gets estimated delta size in terms of code units, times 10.
  int64_t get_delta(DexMethod* method, const IRInstruction* allocation_insn) {
    return m_deltas[std::make_pair(method, allocation_insn)];
  }

  UnorderedSet<DexMethod*> get_inlinable_methods(
      DexMethod* method,
      const UnorderedSet<IRInstruction*>& allocation_insns,
      bool* recursive) {
    UnorderedMap<Key, bool, boost::hash<Key>> visiting;
    for (auto* allocation_insn : UnorderedIterable(allocation_insns)) {
      gather_inlinable_methods(method, allocation_insn, recursive, &visiting);
    }
    UnorderedSet<DexMethod*> inlinable_methods;
    for (auto&& [key, _0] : UnorderedIterable(visiting)) {
      auto [inlinable_method, _1] = key;
      inlinable_methods.insert(inlinable_method);
    }
    inlinable_methods.erase(method);
    return inlinable_methods;
  }
};

enum class InlinableTypeKind {
  // All uses of this type have inline anchors in identified root methods. It is
  // safe to inline all resolved inlinables.
  CompleteSingleRoot,
  // Same as CompleteSingleRoot, except that inlinable anchors are spread over
  // multiple root methods.
  CompleteMultipleRoots,
  // Not all uses of this type have inlinable anchors. Only attempt to inline
  // anchors present in original identified root methods.
  Incomplete,

  Last = Incomplete
};
struct InlinableInfo {
  InlinableTypeKind kind;
  UnorderedSet<DexMethod*> inlinable_methods;
};

using InlinableTypes = UnorderedMap<const DexType*, InlinableInfo>;

class CodeSizeCache {
 private:
  mutable InsertOnlyConcurrentMap<DexMethod*, size_t> m_cache;

 public:
  size_t operator[](DexMethod* method) const {
    return *m_cache
                .get_or_create_and_assert_equal(
                    method,
                    [&](auto* m) {
                      static AccumulatingTimer s_timer("get_code_size");
                      auto t = s_timer.scope();
                      return m->get_code()->estimate_code_units();
                    })
                .first;
  }
};

UnorderedMap<DexMethod*, InlinableTypes> compute_root_methods(
    const ObjectEscapeConfig& config,
    PassManager& mgr,
    const method_override_graph::Graph& method_override_graph,
    const ConcurrentMap<const DexType*, Locations>& new_instances,
    const ConcurrentMap<DexMethod*, Locations>& single_callee_invokes,
    const InsertOnlyConcurrentSet<DexMethod*>& multi_callee_invokes,
    const MethodSummaries& method_summaries,
    const ConcurrentMap<const DexType*, InlineAnchorsOfType>& inline_anchors,
    UnorderedSet<DexMethod*>* inlinable_methods_kept,
    CalleesCache* callees_cache,
    MethodSummaryCache* method_summary_cache) {
  Timer t("compute_root_methods");
  std::array<size_t, (size_t)(InlinableTypeKind::Last) + 1> candidate_types{
      0, 0, 0};
  UnorderedMap<DexMethod*, InlinableTypes> root_methods;
  UnorderedSet<const DexType*> inline_anchor_types;

  std::mutex mutex; // protects candidate_types and root_methods
  std::atomic<size_t> num_incomplete_estimated_delta_threshold_exceeded{0};
  std::atomic<size_t> num_recursive{0};
  std::atomic<size_t> num_no_optimizations{0};
  std::atomic<size_t> num_returning{0};

  InsertOnlyConcurrentSet<DexMethod*> concurrent_inlinable_methods_kept;
  auto concurrent_add_root_methods = [&](const DexType* type, bool complete) {
    const auto& inline_anchors_of_type = inline_anchors.at_unsafe(type);
    InlinedEstimator inlined_estimator(config, method_override_graph, type,
                                       method_summaries, callees_cache,
                                       method_summary_cache);
    auto keep = [&](const auto& inlinable_methods) {
      for (auto* inlinable_method : UnorderedIterable(inlinable_methods)) {
        concurrent_inlinable_methods_kept.insert(inlinable_method);
      }
      complete = false;
    };
    UnorderedMap<DexMethod*, UnorderedSet<DexMethod*>> methods;
    for (auto&& [method, allocation_insns] :
         UnorderedIterable(inline_anchors_of_type)) {
      bool recursive{false};
      auto inlinable_methods = inlined_estimator.get_inlinable_methods(
          method, allocation_insns, &recursive);
      if (recursive) {
        num_recursive++;
        keep(inlinable_methods);
        continue;
      }
      if (method->rstate.no_optimizations()) {
        num_no_optimizations++;
        keep(inlinable_methods);
        continue;
      }
      auto it2 = method_summaries.find(method);
      if (it2 != method_summaries.end() &&
          (it2->second.allocation_insn() != nullptr) &&
          resolve_inlinable(method_summaries, method,
                            it2->second.allocation_insn())
                  .second == type) {
        num_returning++;
        keep(inlinable_methods);
        continue;
      }
      methods.emplace(method, std::move(inlinable_methods));
    }
    if (!complete) {
      unordered_erase_if(methods, [&](const auto& p) {
        auto [method, inlinable_methods] = p;
        int64_t delta = 0;
        const auto& allocation_insns = inline_anchors_of_type.at(method);
        for (auto allocation_insn : UnorderedIterable(allocation_insns)) {
          delta += inlined_estimator.get_delta(method, allocation_insn);
        }
        if (delta > config.incomplete_estimated_delta_threshold) {
          // Skipping, as it's highly unlikely to result in an overall size
          // win, while taking a very long time to compute exactly.
          num_incomplete_estimated_delta_threshold_exceeded++;
          keep(inlinable_methods);
          return true;
        }
        return false;
      });
    }
    if (methods.empty()) {
      return;
    }
    bool multiple_roots = methods.size() > 1;
    auto kind = complete ? multiple_roots
                               ? InlinableTypeKind::CompleteMultipleRoots
                               : InlinableTypeKind::CompleteSingleRoot
                         : InlinableTypeKind::Incomplete;

    std::lock_guard<std::mutex> lock_guard(mutex);
    candidate_types[(size_t)kind]++;
    for (auto&& [method, inlinable_methods] : UnorderedIterable(methods)) {
      TRACE(OEA, 3, "[object escape analysis] root method %s with %s%s",
            SHOW(method), SHOW(type),
            kind == InlinableTypeKind::CompleteMultipleRoots
                ? " complete multiple-roots"
            : kind == InlinableTypeKind::CompleteSingleRoot
                ? " complete single-root"
                : " incomplete");
      root_methods[method].emplace(
          type, (InlinableInfo){kind, std::move(inlinable_methods)});
    }
  };

  for (const auto& [type, method_insn_pairs] :
       UnorderedIterable(new_instances)) {
    auto it = inline_anchors.find(type);
    if (it == inline_anchors.end()) {
      continue;
    }
    inline_anchor_types.insert(type);
  }
  workqueue_run<const DexType*>(
      [&](const DexType* type) {
        const auto& method_insn_pairs = new_instances.at_unsafe(type);
        const auto& inline_anchors_of_type = inline_anchors.at_unsafe(type);

        std::function<bool(const std::pair<DexMethod*, const IRInstruction*>&)>
            is_anchored;
        is_anchored = [&](const auto& p) {
          auto [method, insn] = p;
          auto it2 = inline_anchors_of_type.find(method);
          if (it2 != inline_anchors_of_type.end() &&
              it2->second.count(const_cast<IRInstruction*>(insn))) {
            return true;
          }
          auto it3 = method_summaries.find(method);
          if (it3 == method_summaries.end() ||
              it3->second.allocation_insn() != insn) {
            return false;
          }
          if (multi_callee_invokes.count_unsafe(method) || root(method)) {
            return false;
          }
          auto it4 = single_callee_invokes.find(method);
          if (it4 != single_callee_invokes.end()) {
            for (auto q : it4->second) {
              if (!is_anchored(q)) {
                return false;
              }
            }
          }
          return true;
        };

        // Check whether all uses of this type have inline anchors optimizable
        // root methods.
        bool complete = std::all_of(method_insn_pairs.begin(),
                                    method_insn_pairs.end(), is_anchored) &&
                        unordered_all_of(inline_anchors_of_type, [](auto& p) {
                          return !p.first->rstate.no_optimizations();
                        });

        concurrent_add_root_methods(type, complete);
      },
      inline_anchor_types);

  insert_unordered_iterable(*inlinable_methods_kept,
                            concurrent_inlinable_methods_kept);
  TRACE(OEA,
        1,
        "[object escape analysis] candidate types: %zu complete-single-root, "
        "%zu complete-multiple-roots, %zu incomplete",
        candidate_types[(size_t)InlinableTypeKind::CompleteSingleRoot],
        candidate_types[(size_t)InlinableTypeKind::CompleteMultipleRoots],
        candidate_types[(size_t)InlinableTypeKind::Incomplete]);
  mgr.incr_metric(
      "candidate types CompleteSingleRoot",
      candidate_types[(size_t)InlinableTypeKind::CompleteSingleRoot]);
  mgr.incr_metric(
      "candidate types CompleteMultipleRoots",
      candidate_types[(size_t)InlinableTypeKind::CompleteMultipleRoots]);
  mgr.incr_metric("candidate types Incomplete",
                  candidate_types[(size_t)InlinableTypeKind::Incomplete]);
  mgr.incr_metric("root_methods_incomplete_estimated_delta_threshold_exceeded",
                  (size_t)num_incomplete_estimated_delta_threshold_exceeded);
  mgr.incr_metric("root_methods_recursive", (size_t)num_recursive);
  mgr.incr_metric("root_methods_returning", (size_t)num_returning);
  mgr.incr_metric("root_methods_no_optimizations",
                  (size_t)num_no_optimizations);
  return root_methods;
}

size_t shrink_root_methods(
    const std::function<void(DexMethod*)>& apply_shrinking_plugins,
    MultiMethodInliner& inliner,
    const ConcurrentMap<DexMethod*, UnorderedSet<DexMethod*>>& dependencies,
    const UnorderedMap<DexMethod*, InlinableTypes>& root_methods,
    MethodSummaries* method_summaries,
    MethodSummaryCache* method_summary_cache) {
  InsertOnlyConcurrentSet<DexMethod*> methods_that_lost_allocation_insns;
  std::function<void(DexMethod*)> lose;
  lose = [&](DexMethod* method) {
    if (!methods_that_lost_allocation_insns.insert(method).second) {
      return;
    }
    auto it = dependencies.find(method);
    if (it == dependencies.end()) {
      return;
    }
    for (auto* caller : UnorderedIterable(it->second)) {
      auto it2 = method_summaries->find(caller);
      if (it2 == method_summaries->end()) {
        continue;
      }
      const auto* allocation_insn = it2->second.allocation_insn();
      if ((allocation_insn != nullptr) &&
          opcode::is_an_invoke(allocation_insn->opcode())) {
        auto* callee =
            resolve_invoke_method_deprecated(allocation_insn, caller);
        always_assert(callee);
        if (callee == method) {
          lose(caller);
        }
      }
    }
  };
  workqueue_run<std::pair<DexMethod*, InlinableTypes>>(
      [&](const std::pair<DexMethod*, InlinableTypes>& p) {
        const auto& [method, types] = p;
        inliner.get_shrinker().shrink_method(method);
        apply_shrinking_plugins(method);
        auto it = method_summaries->find(method);
        if (it != method_summaries->end() &&
            (it->second.allocation_insn() != nullptr)) {
          auto ii = InstructionIterable(method->get_code()->cfg());
          if (std::none_of(
                  ii.begin(), ii.end(), [&](const MethodItemEntry& mie) {
                    return opcode::is_return_object(mie.insn->opcode());
                  })) {
            lose(method);
          }
        }
      },
      root_methods);
  for (auto* method : UnorderedIterable(methods_that_lost_allocation_insns)) {
    auto& ms = method_summaries->at(method);
    always_assert(ms.allocation_insn() != nullptr);
    ms.returns = std::monostate();
    always_assert(ms.allocation_insn() == nullptr);
    if (ms.empty()) {
      method_summaries->erase(method);
    }
  }
  if (!methods_that_lost_allocation_insns.empty()) {
    method_summary_cache->clear();
  }
  return methods_that_lost_allocation_insns.size();
}

struct Stats {
  alignas(CACHE_LINE_SIZE) std::atomic<size_t> total_savings{0};
  size_t reduced_methods{0};
  alignas(CACHE_LINE_SIZE) std::atomic<size_t> reduced_methods_variants{0};
  size_t selected_reduced_methods{0};
  size_t reprioritizations{0};
  alignas(CACHE_LINE_SIZE)
      std::atomic<size_t> invokes_not_inlinable_callee_unexpandable{0};
  alignas(CACHE_LINE_SIZE)
      std::atomic<size_t> invokes_not_inlinable_callee_inconcrete{0};
  alignas(CACHE_LINE_SIZE) std::atomic<
      size_t> invokes_not_inlinable_callee_too_many_params_to_expand{0};
  alignas(CACHE_LINE_SIZE) alignas(CACHE_LINE_SIZE) std::atomic<
      size_t> invokes_not_inlinable_callee_expansion_needs_receiver_cast{0};
  alignas(CACHE_LINE_SIZE) std::atomic<size_t> throwing_check_cast{0};
  alignas(CACHE_LINE_SIZE) std::atomic<size_t> invokes_not_inlinable_inlining{
      0};
  alignas(CACHE_LINE_SIZE)
      std::atomic<size_t> invokes_not_inlinable_too_many_iterations{0};
  alignas(CACHE_LINE_SIZE) std::atomic<size_t> anchors_not_inlinable_inlining{
      0};
  alignas(CACHE_LINE_SIZE) std::atomic<size_t> invoke_supers{0};
  alignas(CACHE_LINE_SIZE) std::atomic<size_t> stackify_returns_objects{0};
  alignas(CACHE_LINE_SIZE)
      AtomicStatCounter<size_t> stackify_overlapping_lifetimes{0};
  alignas(CACHE_LINE_SIZE) AtomicStatCounter<size_t> stackify_lifetime_analyses{
      0};
  alignas(CACHE_LINE_SIZE) std::atomic<size_t> too_costly_globally{0};
  alignas(CACHE_LINE_SIZE) std::atomic<size_t> expanded_methods{0};
  alignas(CACHE_LINE_SIZE) std::atomic<size_t> calls_inlined{0};
  alignas(CACHE_LINE_SIZE) std::atomic<size_t> new_instances_eliminated{0};
  size_t inlined_methods_removed{0};
  size_t inlinable_methods_kept{0};
  alignas(CACHE_LINE_SIZE) std::atomic<size_t> reg_allocs{0};
};

struct ReducedMethodVariant {
  DexMethod* root_method;
  size_t variant_index;

  bool operator==(const ReducedMethodVariant& other) const {
    return root_method == other.root_method &&
           variant_index == other.variant_index;
  }

  bool operator<(const ReducedMethodVariant& other) const {
    if (variant_index != other.variant_index) {
      return variant_index < other.variant_index;
    }
    return compare_dexmethods(root_method, other.root_method);
  }
};

using Ref = std::variant<DexMethod*, const DexType*, ReducedMethodVariant>;

} // namespace

namespace std {

template <>
struct hash<ReducedMethodVariant> {
  size_t operator()(const ReducedMethodVariant& rmv) const {
    return reinterpret_cast<size_t>(rmv.root_method) ^ rmv.variant_index;
  }
};

} // namespace std

namespace {

// Data structure that represents a (cloned) reduced method, together with some
// auxiliary information that allows to derive net savings.
struct ReducedMethod {
  DexMethod* method;
  UnorderedMap<DexMethod*, UnorderedSet<const DexType*>> inlined_methods;
  InlinableTypes types;
  size_t calls_inlined;
  size_t new_instances_eliminated;

  void gather_references(const ObjectEscapeConfig& config,
                         const CodeSizeCache& code_size_cache,
                         const UnorderedSet<const DexType*>& irreducible_types,
                         const UnorderedSet<DexMethod*>& methods_kept,
                         UnorderedSet<Ref>* refs,
                         InsertOnlyConcurrentMap<Ref, int>* ref_sizes) const {
    code_size_cache[method];
    auto is_type_kept = [&](auto* type) {
      auto* cls = type_class(type);
      always_assert(cls);
      return root(cls) ||
             types.at(type).kind == InlinableTypeKind::Incomplete ||
             irreducible_types.count(type);
    };
    for (const auto& [inlined_method, inlined_types] :
         UnorderedIterable(inlined_methods)) {
      if (unordered_any_of(inlined_types, is_type_kept)) {
        continue;
      }
      if (root(inlined_method) || method::is_argless_init(inlined_method) ||
          (methods_kept.count(inlined_method) != 0u)) {
        continue;
      }
      refs->insert(Ref(inlined_method));
      ref_sizes->get_or_create_and_assert_equal(
          Ref(inlined_method), [&](auto ref) {
            return (int)(config.cost_method +
                         code_size_cache[std::get<DexMethod*>(ref)]);
          });
    }

    for (const auto& [inlined_type, kind] : UnorderedIterable(types)) {
      if (is_type_kept(inlined_type)) {
        continue;
      }
      refs->insert(Ref(inlined_type));
      ref_sizes->get_or_create_and_assert_equal(
          Ref(inlined_type), [&](auto ref) {
            int size = 0;
            auto cls = type_class(std::get<const DexType*>(ref));
            always_assert(cls);
            bool any_root_field{false};
            for (auto field : cls->get_ifields()) {
              if (root(field)) {
                any_root_field = true;
                continue;
              }
              size += (int)config.cost_field;
            }
            if (!any_root_field && cls->get_sfields().empty() &&
                !cls->get_clinit()) {
              size += (int)config.cost_class;
            }
            return size;
          });
    }
  }
};

class RootMethodReducer {
 private:
  const ObjectEscapeConfig& m_config;
  const std::function<void(DexMethod*)>& m_apply_shrinking_plugins;
  const CodeSizeCache& m_code_size_cache;
  const method_override_graph::Graph& m_method_override_graph;
  const ExpandableMethodParams& m_expandable_method_params;
  DexMethodRef* m_incomplete_marker_method;
  MultiMethodInliner& m_inliner;
  const MethodSummaries& m_method_summaries;
  const UnorderedSet<DexClass*>& m_excluded_classes;
  Stats* m_stats;
  bool m_is_init_or_clinit;
  DexMethod* m_method;
  const InlinableTypes& m_types;
  std::vector<const DexType*> m_types_vec;
  size_t m_calls_inlined{0};
  size_t m_new_instances_eliminated{0};
  CalleesCache* m_callees_cache;
  MethodSummaryCache* m_method_summary_cache;

 public:
  RootMethodReducer(
      const ObjectEscapeConfig& config,
      const std::function<void(DexMethod*)>& apply_shrinking_plugins,
      const CodeSizeCache& code_size_cache,
      const method_override_graph::Graph& method_override_graph,
      const ExpandableMethodParams& expandable_method_params,
      DexMethodRef* incomplete_marker_method,
      MultiMethodInliner& inliner,
      const MethodSummaries& method_summaries,
      const UnorderedSet<DexClass*>& excluded_classes,
      Stats* stats,
      bool is_init_or_clinit,
      DexMethod* method,
      const InlinableTypes& types,
      CalleesCache* callees_cache,
      MethodSummaryCache* method_summary_cache)
      : m_config(config),
        m_apply_shrinking_plugins(apply_shrinking_plugins),
        m_code_size_cache(code_size_cache),
        m_method_override_graph(method_override_graph),
        m_expandable_method_params(expandable_method_params),
        m_incomplete_marker_method(incomplete_marker_method),
        m_inliner(inliner),
        m_method_summaries(method_summaries),
        m_excluded_classes(excluded_classes),
        m_stats(stats),
        m_is_init_or_clinit(is_init_or_clinit),
        m_method(method),
        m_types(types),
        m_callees_cache(callees_cache),
        m_method_summary_cache(method_summary_cache) {
    m_types_vec.reserve(m_types.size());
    for (auto&& [type, _] : UnorderedIterable(m_types)) {
      m_types_vec.push_back(type);
    }
  }

  std::optional<ReducedMethod> reduce() {
    if (!inline_anchors() || !expand_or_inline_invokes()) {
      return std::nullopt;
    }

    auto* insn = find_rewritten_invoke_supers();
    if (insn != nullptr) {
      m_stats->invoke_supers++;
      return std::nullopt;
    }

    {
      // Possibly reduce complexity of CFG for DU chain computation.
      m_method->get_code()->cfg().recompute_registers_size();
      auto num_regs = m_method->get_code()->cfg().get_registers_size();
      constexpr size_t kRegAllocThreshold = 256;
      if (num_regs >= kRegAllocThreshold) {
        fastregalloc::LinearScanAllocator allocator(m_method);
        allocator.allocate();
        m_stats->reg_allocs.fetch_add(1, std::memory_order_relaxed);
      }
    }

    if (has_overlapping_lifetimes()) {
      m_stats->stackify_overlapping_lifetimes++;
      return std::nullopt;
    }
    while (auto opt_p = find_inlinable_new_instance()) {
      if (!stackify(opt_p->first, opt_p->second)) {
        return std::nullopt;
      }
    }

    insn = find_incomplete_marker_methods();
    auto describe = [&]() {
      std::ostringstream oss;
      for (const auto& [type, inlinable_info] : UnorderedIterable(m_types)) {
        oss << show(type) << ":"
            << (inlinable_info.kind == InlinableTypeKind::Incomplete
                    ? "incomplete"
                    : "")
            << ", ";
      }
      return oss.str();
    };
    always_assert_log(
        !insn,
        "Incomplete marker {%s} present in {%s} after reduction of %s in\n%s",
        SHOW(insn), SHOW(m_method), describe().c_str(),
        SHOW(m_method->get_code()->cfg()));

    shrink();
    return (ReducedMethod){m_method, std::move(m_inlined_methods), m_types,
                           m_calls_inlined, m_new_instances_eliminated};
  }

 private:
  void shrink() {
    m_inliner.get_shrinker().shrink_code(m_method->get_code(),
                                         is_static(m_method),
                                         m_is_init_or_clinit,
                                         m_method->get_class(),
                                         m_method->get_proto(),
                                         [this]() { return show(m_method); });
    m_apply_shrinking_plugins(m_method);
  }

  bool inline_insns(const UnorderedMap<IRInstruction*, DexMethod*>& insns) {
    auto inlined = m_inliner.inline_callees(m_method, insns);
    m_calls_inlined += inlined;
    return inlined == insns.size();
  }

  // Given a method invocation, replace a particular argument with the
  // sequence of the argument's field values to flow into an expanded
  // method.
  DexMethodRef* expand_invoke(cfg::CFGMutation& mutation,
                              const cfg::InstructionIterator& it,
                              param_index_t param_index,
                              const DexType* inlinable_type) {
    auto* insn = it->insn;
    auto* callee = resolve_invoke_inlinable_callee(
        m_method_override_graph, insn, m_method, m_callees_cache, [&]() {
          always_assert(param_index == 0);
          return inlinable_type;
        });
    always_assert(callee);
    always_assert(callee->is_concrete());
    std::vector<DexField*> const* fields;
    auto* expanded_method_ref =
        m_expandable_method_params.get_expanded_method_ref(callee, param_index,
                                                           &fields);
    if (expanded_method_ref == nullptr) {
      return nullptr;
    }

    insn->set_method(expanded_method_ref);
    if (!method::is_init(expanded_method_ref)) {
      insn->set_opcode(OPCODE_INVOKE_STATIC);
    }
    auto obj_reg = insn->src(param_index);
    std::vector<reg_t> srcs_copy = insn->srcs_copy();
    insn->set_srcs_size(srcs_copy.size() - 1 + fields->size());
    for (param_index_t i = param_index; i < srcs_copy.size() - 1; i++) {
      insn->set_src(i + fields->size(), srcs_copy.at(i + 1));
    }
    std::vector<IRInstruction*> instructions_to_insert;
    auto& cfg = m_method->get_code()->cfg();
    for (auto* field : *fields) {
      auto reg = type::is_wide_type(field->get_type())
                     ? cfg.allocate_wide_temp()
                     : cfg.allocate_temp();
      insn->set_src(param_index++, reg);
      auto iget_opcode = opcode::iget_opcode_for_field(field);
      instructions_to_insert.push_back((new IRInstruction(iget_opcode))
                                           ->set_src(0, obj_reg)
                                           ->set_field(field));
      auto move_result_pseudo_opcode =
          opcode::move_result_pseudo_for_iget(iget_opcode);
      instructions_to_insert.push_back(
          (new IRInstruction(move_result_pseudo_opcode))->set_dest(reg));
    }
    mutation.insert_before(it, std::move(instructions_to_insert));
    return expanded_method_ref;
  }

  bool expand_invokes(
      const UnorderedMap<IRInstruction*,
                         std::pair<param_index_t, const DexType*>>&
          invokes_to_expand,
      UnorderedSet<DexMethodRef*>* expanded_method_refs) {
    if (invokes_to_expand.empty()) {
      return true;
    }
    auto& cfg = m_method->get_code()->cfg();
    cfg::CFGMutation mutation(cfg);
    auto ii = InstructionIterable(cfg);
    for (auto it = ii.begin(); it != ii.end(); it++) {
      auto* insn = it->insn;
      auto it2 = invokes_to_expand.find(insn);
      if (it2 == invokes_to_expand.end()) {
        continue;
      }
      auto [param_index, inlinable_type] = it2->second;
      auto* expanded_method_ref =
          expand_invoke(mutation, it, param_index, inlinable_type);
      if (expanded_method_ref == nullptr) {
        mutation.clear();
        return false;
      }
      expanded_method_refs->insert(expanded_method_ref);
    }
    mutation.flush();
    return true;
  }

  // Inline all "anchors" until all relevant allocations are new-instance
  // instructions in the (root) method.
  bool inline_anchors() {
    for (int iteration = 0; true; iteration++) {
      Analyzer analyzer(m_method_override_graph, m_excluded_classes,
                        m_method_summaries, m_incomplete_marker_method,
                        m_method, m_callees_cache, m_method_summary_cache);
      using Inlinable =
          std::tuple<DexMethod*, const DexType*, const InlinableInfo*>;
      UnorderedMap<IRInstruction*, Inlinable> inlinables;
      auto inlinable_insns = analyzer.get_inlinables();
      for (auto* insn : UnorderedIterable(inlinable_insns)) {
        auto [callee, type] =
            resolve_inlinable(m_method_summaries, m_method, insn);
        auto it = m_types.find(type);
        if (it != m_types.end()) {
          inlinables.emplace(insn, Inlinable(callee, type, &it->second));
        }
      }
      if (inlinables.empty()) {
        // Can happen if pre-shrinking removes all references to inlinable
        // types.
        return true;
      }
      auto du_chains = get_augmented_du_chains(
          m_method_override_graph, m_method, m_types_vec, m_method_summaries,
          m_callees_cache, m_method_summary_cache, [&](const auto* insn) {
            auto it = inlinables.find(const_cast<IRInstruction*>(insn));
            return it != inlinables.end() ? std::get<1>(it->second) : nullptr;
          });
      UnorderedMap<IRInstruction*, DexMethod*> invokes_to_inline;
      auto& cfg = m_method->get_code()->cfg();
      cfg::CFGMutation mutation(cfg);
      for (auto&& [insn, inlinable] : UnorderedIterable(inlinables)) {
        auto [callee, type, inlinable_info] = inlinable;
        if (inlinable_info->kind == InlinableTypeKind::Incomplete) {
          // We are only going to consider incompletely inlinable types when we
          // find them in the first iteration, i.e. in the original method,
          // and not coming from any inlined method. We are then going insert
          // a special marker invocation instruction so that we can later find
          // the originally matched anchors again. This instruction will get
          // removed later.
          if (!has_incomplete_marker(du_chains[insn])) {
            if (iteration > 0) {
              continue;
            }
            auto insn_it = cfg.find_insn(insn);
            always_assert(!insn_it.is_end());
            auto move_result_it = cfg.move_result_of(insn_it);
            if (move_result_it.is_end()) {
              continue;
            }
            auto* invoke_insn = (new IRInstruction(OPCODE_INVOKE_STATIC))
                                    ->set_method(m_incomplete_marker_method)
                                    ->set_srcs_size(1)
                                    ->set_src(0, move_result_it->insn->dest());
            mutation.insert_after(move_result_it, {invoke_insn});
          }
        }
        if (callee == nullptr) {
          continue;
        }
        invokes_to_inline.emplace(insn, callee);
        m_inlined_methods[callee].insert(type);
      }
      mutation.flush();
      if (invokes_to_inline.empty()) {
        return true;
      }
      if (!inline_insns(invokes_to_inline)) {
        m_stats->anchors_not_inlinable_inlining++;
        return false;
      }
      // simplify to prune now unreachable code, e.g. from removed exception
      // handlers
      cfg.simplify();
    }
  }

  bool is_inlinable_new_instance(const IRInstruction* insn) const {
    return insn->opcode() == OPCODE_NEW_INSTANCE &&
           (m_types.count(insn->get_type()) != 0u);
  }

  bool is_incomplete_marker(const IRInstruction* insn) const {
    return insn->opcode() == OPCODE_INVOKE_STATIC &&
           insn->get_method() == m_incomplete_marker_method;
  }

  bool has_incomplete_marker(const live_range::Uses& uses) const {
    return unordered_any_of(
        uses, [&](auto& use) { return is_incomplete_marker(use.insn); });
  }

  IRInstruction* find_incomplete_marker_methods() const {
    auto& cfg = m_method->get_code()->cfg();
    for (auto& mie : InstructionIterable(cfg)) {
      if (is_incomplete_marker(mie.insn)) {
        return mie.insn;
      }
    }
    return nullptr;
  }

  IRInstruction* find_rewritten_invoke_supers() const {
    auto& cfg = m_method->get_code()->cfg();
    for (auto& mie : InstructionIterable(cfg)) {
      if (opcode::is_invoke_direct(mie.insn->opcode())) {
        auto* method = mie.insn->get_method()->as_def();
        ;
        if (method != nullptr && method->is_virtual()) {
          return mie.insn;
        }
      }
    }
    return nullptr;
  }

  std::optional<std::pair<IRInstruction*, live_range::Uses>>
  find_inlinable_new_instance() const {
    bool throwing_check_cast = false;
    auto du_chains = get_augmented_du_chains_for_inlinable_new_instances(
        &throwing_check_cast);
    always_assert(!throwing_check_cast);
    auto& cfg = m_method->get_code()->cfg();
    for (auto& mie : InstructionIterable(cfg)) {
      auto* insn = mie.insn;
      if (!is_inlinable_new_instance(insn)) {
        continue;
      }
      const auto* type = insn->get_type();
      auto& uses = du_chains[insn];
      auto kind = m_types.at(type).kind;
      if (kind == InlinableTypeKind::Incomplete &&
          !has_incomplete_marker(uses)) {
        continue;
      }
      return std::make_optional(std::make_pair(insn, std::move(uses)));
    }
    return std::nullopt;
  }

  bool should_expand(
      DexMethod* callee,
      const UnorderedMap<src_index_t, const DexType*>& src_indices) {
    always_assert(!src_indices.empty());
    if (method::is_init(callee) && (src_indices.count(0) == 0u)) {
      return true;
    }
    if (src_indices.size() > 1) {
      return false;
    }
    auto [param_index, type] = *unordered_any(src_indices);
    auto kind = m_types.at(type).kind;
    bool multiples = kind == InlinableTypeKind::CompleteMultipleRoots;
    return multiples && m_code_size_cache[callee] > m_config.max_inline_size &&
           (m_expandable_method_params.get_expanded_method_ref(
                callee, param_index) != nullptr);
  }

  live_range::DefUseChains get_augmented_du_chains_for_inlinable_new_instances(
      bool* throwing_check_cast) const {
    return get_augmented_du_chains(
        m_method_override_graph, m_method, m_types_vec, m_method_summaries,
        m_callees_cache, m_method_summary_cache,
        [&](const auto* insn) {
          return is_inlinable_new_instance(insn) ? insn->get_type() : nullptr;
        },
        throwing_check_cast);
  }

  // Expand or inline all uses of all relevant new-instance instructions that
  // involve invoke- instructions, until there are no more such uses.
  bool expand_or_inline_invokes() {
    UnorderedSet<DexMethodRef*> expanded_method_refs;
    for (int iteration = 0; iteration < m_config.max_inline_invokes_iterations;
         iteration++) {
      UnorderedMap<IRInstruction*, DexMethod*> invokes_to_inline;
      UnorderedMap<IRInstruction*, std::pair<param_index_t, const DexType*>>
          invokes_to_expand;

      bool throwing_check_cast = false;
      auto du_chains = get_augmented_du_chains_for_inlinable_new_instances(
          &throwing_check_cast);
      if (throwing_check_cast) {
        // Hm, unlikely that the program would unconditionally crash. It's
        // probably in dead code. We'll try to shrink (unless we are in a state
        // where rewritten invoke-supers are present).
        if (find_rewritten_invoke_supers() == nullptr) {
          shrink();
          throwing_check_cast = false;
          du_chains = get_augmented_du_chains_for_inlinable_new_instances(
              &throwing_check_cast);
        }
        if (throwing_check_cast) {
          m_stats->throwing_check_cast++;
          return false;
        }
      }
      UnorderedMap<IRInstruction*, UnorderedMap<src_index_t, const DexType*>>
          aggregated_uses;
      for (auto& [insn, uses] : UnorderedIterable(du_chains)) {
        always_assert(is_inlinable_new_instance(insn));
        const auto* type = insn->get_type();
        auto kind = m_types.at(type).kind;
        if (kind == InlinableTypeKind::Incomplete &&
            !has_incomplete_marker(uses)) {
          continue;
        }
        for (const auto& use : UnorderedIterable(uses)) {
          auto emplaced =
              aggregated_uses[use.insn].emplace(use.src_index, type).second;
          always_assert(emplaced);
        }
      }
      for (auto&& [uses_insn, src_indices] :
           UnorderedIterable(aggregated_uses)) {
        if (!opcode::is_an_invoke(uses_insn->opcode()) ||
            is_benign(uses_insn->get_method()) ||
            is_incomplete_marker(uses_insn)) {
          continue;
        }
        if (expanded_method_refs.count(uses_insn->get_method()) != 0u) {
          m_stats->invokes_not_inlinable_callee_inconcrete++;
          return false;
        }
        auto* callee = resolve_invoke_inlinable_callee(
            m_method_override_graph, uses_insn, m_method, m_callees_cache,
            [&_src_indices = src_indices]() {
              const auto& src_index_and_type = only(_src_indices);
              always_assert(src_index_and_type.first == 0);
              return src_index_and_type.second;
            });
        always_assert(callee);
        always_assert(callee->is_concrete());
        if (should_expand(callee, src_indices)) {
          if (src_indices.size() > 1) {
            m_stats->invokes_not_inlinable_callee_too_many_params_to_expand++;
            return false;
          }
          if (!is_static(callee) &&
              uses_insn->get_method()->get_class() != callee->get_class()) {
            // TODO: Support inserting check-casts as needed here, similar to
            // what the inliner does.
            m_stats
                ->invokes_not_inlinable_callee_expansion_needs_receiver_cast++;
            return false;
          }
          invokes_to_expand.emplace(uses_insn, only(src_indices));
          continue;
        }

        invokes_to_inline.emplace(uses_insn, callee);
        for (auto [src_index, type] : UnorderedIterable(src_indices)) {
          m_inlined_methods[callee].insert(type);
        }
      }

      if (!expand_invokes(invokes_to_expand, &expanded_method_refs)) {
        m_stats->invokes_not_inlinable_callee_unexpandable++;
        return false;
      }

      if (invokes_to_inline.empty()) {
        // Nothing else to do
        return true;
      }
      if (!inline_insns(invokes_to_inline)) {
        m_stats->invokes_not_inlinable_inlining++;
        return false;
      }
      // simplify to prune now unreachable code, e.g. from removed exception
      // handlers
      m_method->get_code()->cfg().simplify();
    }

    m_stats->invokes_not_inlinable_too_many_iterations++;
    return false;
  }

  // Before an allocation executes, a live reference with that allocation among
  // its possible origins (including casts) can still hold an older object.
  // Reusing its field registers could overwrite an object that is still needed.
  bool has_overlapping_lifetimes() {
    bool throwing_check_cast = false;
    auto du_chains = get_augmented_du_chains_for_inlinable_new_instances(
        &throwing_check_cast);
    always_assert_log(!throwing_check_cast,
                      "Throwing check-cast after invoke expansion in %s",
                      SHOW(m_method));
    auto& cfg = m_method->get_code()->cfg();
    UnorderedMap<IRInstruction*, UnorderedSet<const IRInstruction*>>
        allocation_defs;
    UnorderedSet<const IRInstruction*> tracked_defs;
    for (const auto& mie : InstructionIterable(cfg)) {
      auto* insn = mie.insn;
      if (!is_inlinable_new_instance(insn)) {
        continue;
      }
      const auto& uses = du_chains[insn];
      if (m_types.at(insn->get_type()).kind == InlinableTypeKind::Incomplete &&
          !has_incomplete_marker(uses)) {
        continue;
      }
      auto& defs = allocation_defs[insn];
      defs.insert(insn);
      tracked_defs.insert(insn);
      for (const auto& use : UnorderedIterable(uses)) {
        if (opcode::is_check_cast(use.insn->opcode())) {
          defs.insert(use.insn);
          tracked_defs.insert(use.insn);
        }
      }
    }
    if (allocation_defs.empty()) {
      return false;
    }

    // Check every candidate on the same CFG, before stackification removes
    // definitions or rewrites object registers into scalar registers.
    cfg.calculate_exit_block();
    reaching_defs::MoveAwareFixpointIterator rdefs(
        cfg, [&](const auto* insn) { return tracked_defs.count(insn) != 0u; });
    rdefs.run(reaching_defs::Environment());
    LivenessFixpointIterator liveness(cfg);
    liveness.run(LivenessDomain());
    m_stats->stackify_lifetime_analyses++;
    for (auto* block : cfg.blocks()) {
      UnorderedMap<IRInstruction*, LivenessDomain> live_at_allocations;
      auto live = liveness.get_live_out_vars_at(block);
      for (auto it = block->rbegin(); it != block->rend(); ++it) {
        if (it->type != MFLOW_OPCODE) {
          continue;
        }
        liveness.analyze_instruction(it->insn, &live);
        if (allocation_defs.count(it->insn) != 0u) {
          live_at_allocations.emplace(it->insn, live);
        }
      }
      auto env = rdefs.get_entry_state_at(block);
      for (const auto& mie : InstructionIterable(block)) {
        auto it = live_at_allocations.find(mie.insn);
        if (it != live_at_allocations.end()) {
          const auto& live_at_allocation = it->second;
          if (live_at_allocation.is_top()) {
            return true;
          }
          if (live_at_allocation.is_value()) {
            const auto& alloc_defs = allocation_defs.at(mie.insn);
            for (auto reg : live_at_allocation.elements()) {
              const auto& defs = env.get(reg);
              if (defs.is_top()) {
                return true;
              }
              if (defs.is_value()) {
                const auto& reaching = defs.elements();
                if (std::any_of(reaching.begin(), reaching.end(),
                                [&](const auto* def) {
                                  return alloc_defs.count(def) != 0u;
                                })) {
                  return true;
                }
              }
            }
          }
        }
        rdefs.analyze_instruction(mie.insn, &env);
      }
    }
    return false;
  }

  // Given a new-instance instruction whose (main) uses are as the receiver in
  // iget- and iput- instruction, transform all such field accesses into
  // accesses to registers, one per field.
  bool stackify(IRInstruction* new_instance_insn,
                const live_range::Uses& new_instance_insn_uses) {
    auto& cfg = m_method->get_code()->cfg();
    UnorderedMap<DexField*, reg_t> field_regs;
    UnorderedMap<reg_t, reg_t> created_regs;
    auto get_created_reg = [&](auto reg_t) {
      auto it = created_regs.find(reg_t);
      if (it == created_regs.end()) {
        it = created_regs.emplace(reg_t, cfg.allocate_temp()).first;
      }
      return it->second;
    };
    std::vector<DexField*> ordered_fields;
    auto get_field_reg = [&](DexFieldRef* ref) {
      always_assert(ref->is_def());
      auto* field = ref->as_def();
      auto it = field_regs.find(field);
      if (it == field_regs.end()) {
        auto wide = type::is_wide_type(field->get_type());
        auto reg = wide ? cfg.allocate_wide_temp() : cfg.allocate_temp();
        it = field_regs.emplace(field, reg).first;
        ordered_fields.push_back(field);
      }
      return it->second;
    };

    UnorderedSet<IRInstruction*> used_insns;
    for (const auto& use : UnorderedIterable(new_instance_insn_uses)) {
      auto opcode = use.insn->opcode();
      if (opcode::is_an_iput(opcode)) {
        always_assert(use.src_index == 1);
      } else if (opcode::is_an_invoke(opcode) || opcode::is_a_monitor(opcode) ||
                 opcode::is_check_cast(opcode) || opcode::is_an_iget(opcode) ||
                 opcode::is_instance_of(opcode) ||
                 opcode::is_move_object(opcode) || opcode == OPCODE_IF_EQZ ||
                 opcode == OPCODE_IF_NEZ) {
        always_assert(use.src_index == 0);
      } else if (opcode::is_return_object(opcode)) {
        // Can happen if the root method is also an allocator
        m_stats->stackify_returns_objects++;
        return false;
      } else {
        not_reached_log("Unexpected use: %s at %u", SHOW(use.insn),
                        use.src_index);
      }
      used_insns.insert(use.insn);
    }

    cfg::CFGMutation mutation(cfg);
    auto ii = InstructionIterable(cfg);
    auto new_instance_insn_it = ii.end();
    std::vector<std::pair<IRInstruction*, cfg::InstructionIterator>> zero_its;
    for (auto it = ii.begin(); it != ii.end(); it++) {
      auto* insn = it->insn;
      auto opcode = insn->opcode();
      if (used_insns.count(insn) == 0u) {
        if (insn == new_instance_insn) {
          new_instance_insn_it = it;
        } else if (opcode::is_const(opcode) || opcode::is_move_object(opcode)) {
          zero_its.emplace_back(insn, it);
        }
        continue;
      }
      if (opcode::is_move_object(opcode)) {
        auto* new_insn = (new IRInstruction(OPCODE_MOVE))
                             ->set_src(0, get_created_reg(insn->src(0)))
                             ->set_dest(get_created_reg(insn->dest()));
        mutation.replace(it, {new_insn});
      } else if (opcode::is_an_iget(opcode)) {
        auto move_result_it = cfg.move_result_of(it);
        auto* new_insn = (new IRInstruction(opcode::iget_to_move(opcode)))
                             ->set_src(0, get_field_reg(insn->get_field()))
                             ->set_dest(move_result_it->insn->dest());
        mutation.replace(it, {new_insn});
      } else if (opcode::is_an_iput(opcode)) {
        auto* new_insn = (new IRInstruction(opcode::iput_to_move(opcode)))
                             ->set_src(0, insn->src(0))
                             ->set_dest(get_field_reg(insn->get_field()));
        mutation.replace(it, {new_insn});
      } else if (opcode::is_an_invoke(opcode)) {
        always_assert(is_benign(insn->get_method()) ||
                      is_incomplete_marker(insn));
        mutation.remove(it);
      } else if (opcode::is_instance_of(opcode)) {
        auto move_result_it = cfg.move_result_of(it);
        // The allocated object's runtime type is exactly the new-instance
        // type, so the test reduces to whether that type is assignable to the
        // tested type. This must consider implemented interfaces, not just the
        // superclass chain.
        auto* new_insn =
            (type::check_cast(new_instance_insn->get_type(), insn->get_type())
                 ? (new IRInstruction(OPCODE_MOVE))
                       ->set_src(0, get_created_reg(insn->src(0)))
                 : (new IRInstruction(OPCODE_CONST))->set_literal(0))
                ->set_dest(move_result_it->insn->dest());
        mutation.replace(it, {new_insn});
      } else if (opcode::is_a_monitor(opcode)) {
        mutation.remove(it);
      } else if (opcode == OPCODE_IF_EQZ || opcode == OPCODE_IF_NEZ) {
        insn->set_src(0, get_created_reg(insn->src(0)));
      } else if (opcode::is_check_cast(opcode)) {
        auto move_result_it = cfg.move_result_of(it);
        auto dest = move_result_it->insn->dest();
        auto* new_insn = (new IRInstruction(OPCODE_MOVE))
                             ->set_src(0, get_created_reg(insn->src(0)))
                             ->set_dest(get_created_reg(dest));
        mutation.replace(it, {new_insn});
      } else {
        not_reached_log("Unexpected insn: %s", SHOW(insn));
      }
    }

    // Also handle (zero-)overrides of registers holding a reference to the
    // newly created object.
    for (auto& [insn, it] : zero_its) {
      auto created_regs_it = created_regs.find(insn->dest());
      if (created_regs_it != created_regs.end()) {
        auto* new_insn = (new IRInstruction(OPCODE_CONST))
                             ->set_literal(0)
                             ->set_dest(created_regs_it->second);
        mutation.insert_before(it, {new_insn});
      }
    }

    always_assert(!new_instance_insn_it.is_end());
    auto* init_class_insn =
        m_inliner.get_shrinker()
            .get_init_classes_with_side_effects()
            .create_init_class_insn(new_instance_insn->get_type());
    if (init_class_insn != nullptr) {
      mutation.insert_before(new_instance_insn_it, {init_class_insn});
    }
    mutation.remove(new_instance_insn_it);

    // Insert zero-initialization code for field registers.

    std::sort(ordered_fields.begin(), ordered_fields.end(), compare_dexfields);

    auto new_instance_move_result_it = cfg.move_result_of(new_instance_insn_it);
    always_assert(!new_instance_move_result_it.is_end());

    auto get_init_insns = [&](bool created) {
      std::vector<IRInstruction*> insns;
      insns.reserve(ordered_fields.size() + created_regs.size());
      for (auto* field : ordered_fields) {
        auto wide = type::is_wide_type(field->get_type());
        auto opcode = wide ? OPCODE_CONST_WIDE : OPCODE_CONST;
        auto reg = field_regs.at(field);
        auto* new_insn =
            (new IRInstruction(opcode))->set_literal(0)->set_dest(reg);
        insns.push_back(new_insn);
      }
      auto ordered_created_regs = unordered_to_ordered_keys(created_regs);
      for (auto reg : ordered_created_regs) {
        auto created_reg = created_regs.at(reg);
        auto* new_insn =
            (new IRInstruction(OPCODE_CONST))
                ->set_literal(static_cast<int64_t>(
                    created &&
                    reg == new_instance_move_result_it->insn->dest()))
                ->set_dest(created_reg);
        insns.push_back(new_insn);
      }
      return insns;
    };
    mutation.insert_before(new_instance_insn_it,
                           get_init_insns(/* created */ true));

    mutation.flush();

    auto* entry_block = cfg.entry_block();
    auto entry_it = entry_block->to_cfg_instruction_iterator(
        entry_block->get_first_non_param_loading_insn());
    cfg.insert_before(entry_it, get_init_insns(/* created */ false));

    // simplify to prune now unreachable code, e.g. from removed exception
    // handlers
    cfg.simplify();
    m_new_instances_eliminated++;
    return true;
  }

  UnorderedMap<DexMethod*, UnorderedSet<const DexType*>> m_inlined_methods;
};

// This order implies the sequence of inlinable type subsets
// we'll consider. We'll structure the sequence such that often occurring
// types with multiple uses will be chopped off the type set first.
std::vector<const DexType*> order_inlinable_types(
    const UnorderedMap<DexMethod*, InlinableTypes>& root_methods) {
  struct Occurrences {
    InlinableTypeKind kind;
    size_t count{0};
  };
  UnorderedMap<const DexType*, Occurrences> occurrences;
  std::vector<const DexType*> res;
  for (auto&& [method, types] : UnorderedIterable(root_methods)) {
    for (auto&& [type, inlinable_info] : UnorderedIterable(types)) {
      auto kind = inlinable_info.kind;
      auto [it, emplaced] = occurrences.emplace(type, (Occurrences){kind});
      it->second.count++;
      if (emplaced) {
        res.push_back(type);
      } else {
        always_assert(it->second.kind == kind);
      }
    }
  }

  std::sort(res.begin(), res.end(), [&occurrences](auto* a_type, auto* b_type) {
    const auto& a = occurrences.at(a_type);
    const auto& b = occurrences.at(b_type);
    // We sort types with incomplete anchors to the front.
    if (a.kind != b.kind) {
      return a.kind > b.kind;
    }
    // We sort types with more frequent occurrences to the front.
    if (a.count != b.count) {
      return a.count > b.count;
    }
    // Tie breaker.
    return compare_dextypes(a_type, b_type);
  });

  return res;
}

// Reduce all root methods to a set of variants. The reduced methods are ordered
// by how many types were inlined, with the largest number of inlined types
// going first.
UnorderedMap<DexMethod*, std::vector<ReducedMethod>> compute_reduced_methods(
    const ObjectEscapeConfig& config,
    const std::function<void(DexMethod*)>& apply_shrinking_plugins,
    const method_override_graph::Graph& method_override_graph,
    ExpandableMethodParams& expandable_method_params,
    MultiMethodInliner& inliner,
    const MethodSummaries& method_summaries,
    const UnorderedSet<DexClass*>& excluded_classes,
    const UnorderedMap<DexMethod*, InlinableTypes>& root_methods,
    const UnorderedMap<const DexType*, size_t>& inlinable_type_index,
    UnorderedSet<const DexType*>* irreducible_types,
    UnorderedSet<DexMethod*>* inlinable_methods_kept,
    Stats* stats,
    CalleesCache* callees_cache,
    MethodSummaryCache* method_summary_cache) {
  Timer t("compute_reduced_methods");

  // We'll now compute the set of variants we'll consider. For each root method
  // with N inlinable types, there will be N variants.
  std::vector<std::pair<DexMethod*, InlinableTypes>>
      ordered_root_methods_variants;
  {
    Timer sub_t{"ordered_root_methods_variants"};
    for (auto&& [method, types] : UnorderedIterable(root_methods)) {
      auto ordered_types = unordered_to_ordered(types, [&](auto& p, auto& q) {
        return inlinable_type_index.at(p.first) <
               inlinable_type_index.at(q.first);
      });
      for (auto it = ordered_types.begin(); it != ordered_types.end(); it++) {
        ordered_root_methods_variants.emplace_back(
            method, InlinableTypes(it, ordered_types.end()));
      }
    }
    // Order such that items with many types to process go first, which improves
    // workqueue efficiency.
    std::stable_sort(ordered_root_methods_variants.begin(),
                     ordered_root_methods_variants.end(), [](auto& a, auto& b) {
                       return a.second.size() > b.second.size();
                     });
  }

  // Special marker method, used to identify which newly created objects of only
  // incompletely inlinable types should get inlined.
  DexMethodRef* incomplete_marker_method = DexMethod::make_method(
      "Lredex/$ObjectEscapeAnalysis;.markIncomplete:(Ljava/lang/Object;)V");

  // We make a copy before we start reducing a root method, in case we run
  // into issues, or negative net savings.
  ConcurrentMap<DexMethod*, std::vector<ReducedMethod>>
      concurrent_reduced_methods;
  CodeSizeCache code_size_cache;
  // Computing root methods is very memory intensive, and "instrumented" builds
  // are doubly so. We limit parallelism to limit maximum memory usage.
  size_t num_threads = redex_parallel::default_num_threads();
  if (g_redex->instrument_mode && g_redex->slow_invariants_debug) {
    num_threads = std::min<size_t>(num_threads, 16u);
  }

  {
    Timer sub_t{"reduce"};
    workqueue_run<std::pair<DexMethod*, InlinableTypes>>(
        [&](const std::pair<DexMethod*, InlinableTypes>& p) {
          auto* method = p.first;
          const auto& types = p.second;
          auto copy_name_str = method->get_name()->str() + "$oea$internal$" +
                               std::to_string(types.size());
          auto* copy = DexMethod::make_method_from(
              method, method->get_class(),
              DexString::make_string(copy_name_str));
          RootMethodReducer root_method_reducer{config,
                                                apply_shrinking_plugins,
                                                code_size_cache,
                                                method_override_graph,
                                                expandable_method_params,
                                                incomplete_marker_method,
                                                inliner,
                                                method_summaries,
                                                excluded_classes,
                                                stats,
                                                method::is_init(method) ||
                                                    method::is_clinit(method),
                                                copy,
                                                types,
                                                callees_cache,
                                                method_summary_cache};
          auto reduced_method = root_method_reducer.reduce();
          if (reduced_method) {
            concurrent_reduced_methods.update(
                method, [&](auto*, auto& reduced_methods_variants, bool) {
                  reduced_methods_variants.emplace_back(
                      std::move(*reduced_method));
                });
            return;
          }
          DexMethod::delete_method_DO_NOT_USE(copy);
        },
        ordered_root_methods_variants, num_threads);
  }

  // For each root method, we order the reduced methods (if any) by how many
  // types were inlined, with the largest number of inlined types going first.
  UnorderedMap<DexMethod*, std::vector<ReducedMethod>> reduced_methods;
  {
    Timer sub_t{"reduced_methods"};
    for (auto& [method, reduced_methods_variants] :
         UnorderedIterable(concurrent_reduced_methods)) {
      std::sort(
          reduced_methods_variants.begin(), reduced_methods_variants.end(),
          [&](auto& a, auto& b) { return a.types.size() > b.types.size(); });
      reduced_methods.emplace(method, std::move(reduced_methods_variants));
    }
  }

  // All types which could not be accommodated by any reduced method variants
  // are marked as "irreducible", which is later used when doing a global cost
  // analysis.
  static const InlinableTypes no_types;
  {
    Timer sub_t{"irreducible"};
    for (auto&& [method, types] : UnorderedIterable(root_methods)) {
      auto it = reduced_methods.find(method);
      const auto& largest_types =
          it == reduced_methods.end() ? no_types : it->second.front().types;
      for (auto&& [type, inlinable_info] : UnorderedIterable(types)) {
        if (largest_types.count(type) == 0u) {
          for (auto* cls = type_class(type);
               (cls != nullptr) && !cls->is_external();
               cls = type_class(cls->get_super_class())) {
            irreducible_types->insert(cls->get_type());
          }
          insert_unordered_iterable(*inlinable_methods_kept,
                                    inlinable_info.inlinable_methods);
        }
      }
    }
  }
  return reduced_methods;
}

void gather_references(
    const UnorderedMap<DexMethod*, std::vector<ReducedMethod>>& reduced_methods,
    const ObjectEscapeConfig& config,
    const CodeSizeCache& code_size_cache,
    const UnorderedSet<const DexType*>& irreducible_types,
    const UnorderedSet<DexMethod*>& methods_kept,
    InsertOnlyConcurrentMap<ReducedMethodVariant, UnorderedSet<Ref>>* rmv_refs,
    InsertOnlyConcurrentMap<Ref, int>* ref_sizes) {
  workqueue_run<std::pair<DexMethod*, std::vector<ReducedMethod>>>(
      [&](const std::pair<DexMethod*, std::vector<ReducedMethod>>& p) {
        auto* method = p.first;
        const auto& reduced_methods_variants = p.second;
        UnorderedSet<Ref> dom_refs;
        for (size_t i = reduced_methods_variants.size(); i > 0; i--) {
          const auto& reduced_method = reduced_methods_variants.at(i - 1);
          UnorderedSet<Ref> refs;
          ReducedMethodVariant rmv{method, i - 1};
          refs.insert(rmv);
          ref_sizes->emplace(rmv, 0);
          reduced_method.gather_references(config, code_size_cache,
                                           irreducible_types, methods_kept,
                                           &refs, ref_sizes);
          unordered_erase_if(refs,
                             [&](auto ref) { return dom_refs.count(ref); });
          insert_unordered_iterable(dom_refs, refs);
          rmv_refs->emplace(rmv, std::move(refs));
        }
      },
      reduced_methods);
}

int get_savings(
    const CodeSizeCache& code_size_cache,
    const UnorderedMap<DexMethod*, std::vector<ReducedMethod>>& reduced_methods,
    const UnorderedMap<DexMethod*, size_t>& selected_reduced_methods,
    const InsertOnlyConcurrentMap<ReducedMethodVariant, UnorderedSet<Ref>>&
        rmv_refs,
    const UnorderedMap<Ref, UnorderedSet<ReducedMethodVariant>>& ref_rmvs,
    const InsertOnlyConcurrentMap<Ref, int>& ref_sizes,
    Ref seed_ref) {
  int savings = 0;

  UnorderedMap<Ref, size_t> ref_counts;
  for (const auto& rmv : UnorderedIterable(ref_rmvs.at(seed_ref))) {
    const auto& reduced_methods_variants = reduced_methods.at(rmv.root_method);
    auto it = selected_reduced_methods.find(rmv.root_method);
    size_t end;
    if (it == selected_reduced_methods.end()) {
      savings += (int)code_size_cache[rmv.root_method];
      end = reduced_methods_variants.size();
    } else {
      always_assert(rmv.variant_index < it->second);
      const auto& selected_reduced_method =
          reduced_methods_variants.at(it->second);
      savings += (int)code_size_cache[selected_reduced_method.method];
      end = it->second;
    }
    const auto& reduced_method = reduced_methods_variants.at(rmv.variant_index);
    savings -= (int)code_size_cache[reduced_method.method];
    for (size_t vi = rmv.variant_index; vi < end; vi++) {
      for (auto ref :
           UnorderedIterable(rmv_refs.at_unsafe({rmv.root_method, vi}))) {
        ref_counts[ref]++;
      }
    }
  }

  for (auto [ref, count] : UnorderedIterable(ref_counts)) {
    auto size = ref_rmvs.at(ref).size();
    always_assert(count <= size);
    if (count == size) {
      savings += ref_sizes.at(ref);
    }
  }

  return savings;
}

// Select all those reduced methods which will result in overall size savings;
// we consider savings for individual reduced methods, all reduced methods that
// will eliminate an inlined type, and savings achieved by eliminating any
// particular inlined method.
void select_reduced_methods(
    const ObjectEscapeConfig& config,
    const UnorderedMap<DexMethod*, std::vector<ReducedMethod>>& reduced_methods,
    UnorderedSet<const DexType*>* irreducible_types,
    UnorderedSet<DexMethod*>* inlinable_methods_kept,
    Stats* stats,
    UnorderedMap<DexMethod*, size_t>* selected_reduced_methods) {
  Timer t("select_reduced_methods");

  // Gather references

  CodeSizeCache code_size_cache;
  InsertOnlyConcurrentMap<ReducedMethodVariant, UnorderedSet<Ref>> rmv_refs;
  InsertOnlyConcurrentMap<Ref, int> ref_sizes;
  gather_references(reduced_methods, config, code_size_cache,
                    *irreducible_types, *inlinable_methods_kept, &rmv_refs,
                    &ref_sizes);

  UnorderedMap<Ref, UnorderedSet<ReducedMethodVariant>> ref_rmvs;
  for (auto&& [rmv, refs] : UnorderedIterable(rmv_refs)) {
    for (auto ref : UnorderedIterable(refs)) {
      ref_rmvs[ref].insert(rmv);
    }
  }

  // We'll identify the most profitable opportunities using a priority queue.
  // Each element of the priority represents either a reduced method variant, a
  // type that can get fully inlined, or a method that can be fully inlined. The
  // priority is simply the savings that would be achieved by selecting the
  // associated reduced method variants. For determinism, we incorporate a
  // deterministic reference order in the reference priorities.
  UnorderedMap<Ref, size_t> ref_indices;
  auto ordered_refs = unordered_to_ordered_keys(ref_sizes, [&](Ref a, Ref b) {
    if (a.index() != b.index()) {
      return a.index() < b.index();
    }
    if (std::holds_alternative<DexMethod*>(a)) {
      return compare_dexmethods(std::get<DexMethod*>(a),
                                std::get<DexMethod*>(b));
    }
    if (std::holds_alternative<const DexType*>(a)) {
      return compare_dextypes(std::get<const DexType*>(a),
                              std::get<const DexType*>(b));
    }
    return std::get<ReducedMethodVariant>(a) <
           std::get<ReducedMethodVariant>(b);
  });
  for (auto ref : ordered_refs) {
    ref_indices.emplace(ref, ref_indices.size());
  }

  auto get_priority = [&](Ref ref) {
    int64_t res =
        get_savings(code_size_cache, reduced_methods, *selected_reduced_methods,
                    rmv_refs, ref_rmvs, ref_sizes, ref);
    // Make priority unique per ref.
    res *= (int64_t)ref_indices.size();
    res += res >= 0 ? (int)ref_indices.at(ref) : -(int)ref_indices.at(ref);
    return res;
  };

  MutablePriorityQueue<Ref, int64_t> pq;
  for (auto [ref, _] : UnorderedIterable(ref_sizes)) {
    pq.insert(ref, get_priority(ref));
  }

  while (!pq.empty()) {
    auto seed_ref = pq.front();
    int savings = static_cast<int>(pq.get_priority(seed_ref) /
                                   static_cast<int64_t>(ref_indices.size()));
    if (savings < config.savings_threshold) {
      // All remaining references are less profitable than this one.
      break;
    }
    stats->total_savings += savings;

    // We now...
    // - record the choice of selected reduced method variants
    // - figure out how to mutate our state that maintains the refs and rmvs to
    //   reflect the eliminated references
    // - figure out which references are affected, in the sense that their
    //   priority (savings) might have changed
    UnorderedMap<Ref, UnorderedSet<ReducedMethodVariant>> delta_ref_rmvs;
    UnorderedSet<ReducedMethodVariant> affected_rmvs;
    for (const auto& rmv : UnorderedIterable(ref_rmvs.at(seed_ref))) {
      const auto& reduced_methods_variants =
          reduced_methods.at(rmv.root_method);
      size_t end;
      auto [it, emplaced] =
          selected_reduced_methods->emplace(rmv.root_method, rmv.variant_index);
      if (emplaced) {
        end = reduced_methods_variants.size();
      } else {
        always_assert(it->second > rmv.variant_index);
        end = it->second;
        it->second = rmv.variant_index;
      }

      for (size_t vi = rmv.variant_index; vi < end; vi++) {
        auto& refs = rmv_refs.at_unsafe({rmv.root_method, vi});
        for (auto ref : UnorderedIterable(refs)) {
          delta_ref_rmvs[ref].insert({rmv.root_method, vi});
          auto& rmvs = ref_rmvs.at(ref);
          insert_unordered_iterable(affected_rmvs, rmvs);
        }
      }
    }

    UnorderedSet<Ref> affected_refs;
    for (const auto& rmv : UnorderedIterable(affected_rmvs)) {
      for (size_t vi = 0; vi <= rmv.variant_index; vi++) {
        auto& refs = rmv_refs.at_unsafe({rmv.root_method, vi});
        insert_unordered_iterable(affected_refs, refs);
      }
    }

    // We apply the determined delta to our refs/rmvs state.
    for (auto&& [ref, delta_rmvs] : UnorderedIterable(delta_ref_rmvs)) {
      auto it = ref_rmvs.find(ref);
      for (const auto& rmv : UnorderedIterable(delta_rmvs)) {
        auto erased = it->second.erase(rmv);
        always_assert(erased);
        auto& refs = rmv_refs.at_unsafe(rmv);
        erased = refs.erase(ref);
        always_assert(erased);
        if (refs.empty()) {
          rmv_refs.erase_unsafe(rmv);
        }
      }

      if (it->second.empty()) {
        ref_rmvs.erase(it);
        if (std::holds_alternative<DexMethod*>(ref)) {
          stats->inlined_methods_removed++;
        }
      }
    }

    // Finally, we reprioritize as needed.
    for (auto ref : UnorderedIterable(affected_refs)) {
      auto it = ref_rmvs.find(ref);
      if (it != ref_rmvs.end()) {
        always_assert(!it->second.empty());
        pq.update_priority(ref, get_priority(ref));
        always_assert(pq.get_priority(ref) == get_priority(ref));
        stats->reprioritizations++;
      } else {
        pq.erase(ref);
      }
    }

    always_assert(!pq.contains(seed_ref));
  }

  stats->inlinable_methods_kept = inlinable_methods_kept->size();
  for (auto&& [ref, _] : UnorderedIterable(ref_rmvs)) {
    if (std::holds_alternative<DexMethod*>(ref)) {
      stats->inlinable_methods_kept++;
    }
  }

  for (auto&& [root_method, _] : UnorderedIterable(reduced_methods)) {
    if (selected_reduced_methods->count(root_method) == 0u) {
      stats->too_costly_globally++;
    }
  }
}

void reduce(const Scope& scope,
            const ObjectEscapeConfig& config,
            const std::function<void(DexMethod*)>& apply_shrinking_plugins,
            const method_override_graph::Graph& method_override_graph,
            MultiMethodInliner& inliner,
            const MethodSummaries& method_summaries,
            const UnorderedSet<DexClass*>& excluded_classes,
            const UnorderedMap<DexMethod*, InlinableTypes>& root_methods,
            Stats* stats,
            UnorderedSet<DexMethod*>* inlinable_methods_kept,
            CalleesCache* callees_cache,
            MethodSummaryCache* method_summary_cache,
            method_profiles::MethodProfiles* method_profiles) {
  Timer t("reduce");

  // First, we compute all reduced methods

  auto ordered_inlinable_types = order_inlinable_types(root_methods);
  // We are not exploring all possible subsets of types, but only single chain
  // of subsets, guided by the inlinable kind, and by how often
  // they appear as inlinable types in root methods.
  UnorderedMap<const DexType*, size_t> inlinable_type_index;
  for (const auto* type : ordered_inlinable_types) {
    inlinable_type_index.emplace(type, inlinable_type_index.size());
  }

  ExpandableMethodParams expandable_method_params(scope);
  UnorderedSet<const DexType*> irreducible_types;
  auto reduced_methods = compute_reduced_methods(
      config, apply_shrinking_plugins, method_override_graph,
      expandable_method_params, inliner, method_summaries, excluded_classes,
      root_methods, inlinable_type_index, &irreducible_types,
      inlinable_methods_kept, stats, callees_cache, method_summary_cache);
  stats->reduced_methods = reduced_methods.size();

  // Second, we select reduced methods that will result in net savings
  UnorderedMap<DexMethod*, size_t> selected_reduced_methods;
  select_reduced_methods(config, reduced_methods, &irreducible_types,
                         inlinable_methods_kept, stats,
                         &selected_reduced_methods);
  stats->selected_reduced_methods = selected_reduced_methods.size();

  // Finally, we are going to apply those selected methods, and clean up all
  // reduced method clones
  workqueue_run<std::pair<DexMethod*, std::vector<ReducedMethod>>>(
      [&](const std::pair<DexMethod*, std::vector<ReducedMethod>>& p) {
        const auto& [method, reduced_methods_variants] = p;
        auto it = selected_reduced_methods.find(method);
        if (it != selected_reduced_methods.end()) {
          const auto& reduced_method = reduced_methods_variants.at(it->second);
          method->set_code(reduced_method.method->release_code());
          stats->calls_inlined += reduced_method.calls_inlined;
          stats->new_instances_eliminated +=
              reduced_method.new_instances_eliminated;
        }
        stats->reduced_methods_variants += reduced_methods_variants.size();
        for (const auto& reduced_method : reduced_methods_variants) {
          DexMethod::delete_method_DO_NOT_USE(reduced_method.method);
        }
      },
      reduced_methods);

  size_t expanded_methods =
      expandable_method_params.flush(scope, method_profiles);
  stats->expanded_methods += expanded_methods;
}
} // namespace

ObjectEscapeAnalysisPass::ObjectEscapeAnalysisPass(bool register_plugins)
    : Pass(OBJECTESCAPEANALYSIS_PASS_NAME) {
  if (register_plugins) {
    std::unique_ptr<ObjectEscapeAnalysisRegistry> plugin =
        std::make_unique<ObjectEscapeAnalysisRegistry>();
    PluginRegistry::get().register_pass(OBJECTESCAPEANALYSIS_PASS_NAME,
                                        std::move(plugin));
  }
}

void ObjectEscapeAnalysisPass::bind_config() {
  bind("max_inline_size", MAX_INLINE_SIZE, m_config.max_inline_size);
  bind("max_inline_invokes_iterations", MAX_INLINE_INVOKES_ITERATIONS,
       m_config.max_inline_invokes_iterations);
  bind("incomplete_estimated_delta_threshold",
       INCOMPLETE_ESTIMATED_DELTA_THRESHOLD,
       m_config.incomplete_estimated_delta_threshold);
  bind("cost_method", COST_METHOD, m_config.cost_method);
  bind("cost_class", COST_CLASS, m_config.cost_class);
  bind("cost_field", COST_FIELD, m_config.cost_field);
  bind("cost_invoke", COST_INVOKE, m_config.cost_invoke);
  bind("cost_move_result", COST_MOVE_RESULT, m_config.cost_move_result);
  bind("cost_new_instance", COST_NEW_INSTANCE, m_config.cost_new_instance);
  bind("savings_threshold", SAVINGS_THRESHOLD, m_config.savings_threshold);
}

void ObjectEscapeAnalysisPass::run_pass(DexStoresVector& stores,
                                        ConfigFiles& conf,
                                        PassManager& mgr) {
  const auto scope = build_class_scope(stores);
  auto method_override_graph = mog::build_graph(scope);
  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, conf.create_init_class_insns(), method_override_graph.get());

  auto* registry = dynamic_cast<ObjectEscapeAnalysisRegistry*>(
      PluginRegistry::get().pass_registry(OBJECTESCAPEANALYSIS_PASS_NAME));
  std::vector<std::unique_ptr<ObjectEscapeAnalysisPlugin>> shrinking_plugins;
  if (registry != nullptr) {
    shrinking_plugins = registry->create_plugins();
  };
  auto apply_shrinking_plugins = [&](DexMethod* method) {
    for (auto& plugin : shrinking_plugins) {
      plugin->shrink_method(init_classes_with_side_effects, method);
    }
  };

  auto class_hierarchy = build_internal_type_hierarchy(scope);
  auto excluded_classes =
      method_override_graph::get_classes_with_overridden_finalize(
          *method_override_graph, class_hierarchy);

  ConcurrentMap<const DexType*, Locations> new_instances;
  ConcurrentMap<DexMethod*, Locations> single_callee_invokes;
  InsertOnlyConcurrentSet<DexMethod*> multi_callee_invokes;
  ConcurrentMap<DexMethod*, UnorderedSet<DexMethod*>> dependencies;
  CalleesCache callees_cache;
  analyze_scope(scope, *method_override_graph, &new_instances,
                &single_callee_invokes, &multi_callee_invokes, &dependencies,
                &callees_cache);

  size_t analysis_iterations;
  MethodSummaryCache method_summary_cache;
  auto method_summaries = compute_method_summaries(
      scope, dependencies, *method_override_graph, excluded_classes,
      &analysis_iterations, &callees_cache, &method_summary_cache);
  mgr.incr_metric("analysis_iterations", analysis_iterations);

  auto inline_anchors = compute_inline_anchors(
      scope, *method_override_graph, method_summaries, excluded_classes,
      &callees_cache, &method_summary_cache);

  UnorderedSet<DexMethod*> inlinable_methods_kept;
  auto root_methods = compute_root_methods(
      m_config, mgr, *method_override_graph, new_instances,
      single_callee_invokes, multi_callee_invokes, method_summaries,
      inline_anchors, &inlinable_methods_kept, &callees_cache,
      &method_summary_cache);

  ConcurrentMethodResolverDeprecated concurrent_method_resolver;
  UnorderedSet<DexMethod*> no_default_inlinables;
  // customize shrinking options
  auto inliner_config =
      *conf.get_global_config().get_config_by_name<InlinerConfig>("inliner");
  inliner_config.shrinker = shrinker::ShrinkerConfig();
  inliner_config.shrinker.run_const_prop = true;
  inliner_config.shrinker.run_cse = true;
  inliner_config.shrinker.run_copy_prop = true;
  inliner_config.shrinker.run_local_dce = true;
  inliner_config.shrinker.normalize_new_instances = false;
  inliner_config.shrinker.compute_pure_methods = false;
  inliner_config.rewrite_invoke_super = true;
  int min_sdk = 0;
  MultiMethodInliner inliner(
      scope, init_classes_with_side_effects, stores, conf,
      no_default_inlinables, std::ref(concurrent_method_resolver),
      inliner_config, min_sdk, MultiMethodInlinerMode::None);

  auto lost_returns_through_shrinking = shrink_root_methods(
      apply_shrinking_plugins, inliner, dependencies, root_methods,
      &method_summaries, &method_summary_cache);

  Stats stats;
  reduce(scope, m_config, apply_shrinking_plugins, *method_override_graph,
         inliner, method_summaries, excluded_classes, root_methods, &stats,
         &inlinable_methods_kept, &callees_cache, &method_summary_cache,
         &conf.get_method_profiles());

  inliner.flush();

  TRACE(OEA, 1, "[object escape analysis] total savings: %zu",
        (size_t)stats.total_savings);
  TRACE(
      OEA, 1,
      "[object escape analysis] %zu root methods lead to %zu reduced root "
      "methods with %zu variants of which %zu were selected involving %zu "
      "reprioritizations and %zu anchors not inlinable because "
      "inlining failed, %zu/%zu/%zu/%zu invokes not inlinable because callee "
      "is unexpandable/has too many params/expansion needs receiver cast/is "
      "inconcrete, %zu invokes not inlinable because inlining failed, %zu "
      "invokes not "
      "inlinable after too many iterations, %zu invoke-supers, %zu throwing "
      "check-casts, %zu stackify returned objects, "
      "%zu too costly globally; %zu expanded methods; %zu "
      "calls inlined; %zu new-instances eliminated; %zu/%zu inlinable "
      "methods removed/kept",
      root_methods.size(), stats.reduced_methods,
      (size_t)stats.reduced_methods_variants, stats.selected_reduced_methods,
      stats.reprioritizations, (size_t)stats.anchors_not_inlinable_inlining,
      (size_t)stats.invokes_not_inlinable_callee_unexpandable,
      (size_t)stats.invokes_not_inlinable_callee_too_many_params_to_expand,
      (size_t)stats.invokes_not_inlinable_callee_expansion_needs_receiver_cast,
      (size_t)stats.invokes_not_inlinable_callee_inconcrete,
      (size_t)stats.invokes_not_inlinable_inlining,
      (size_t)stats.invokes_not_inlinable_too_many_iterations,
      (size_t)stats.invoke_supers, (size_t)stats.throwing_check_cast,
      (size_t)stats.stackify_returns_objects, (size_t)stats.too_costly_globally,
      (size_t)stats.expanded_methods, (size_t)stats.calls_inlined,
      (size_t)stats.new_instances_eliminated, stats.inlined_methods_removed,
      stats.inlinable_methods_kept);

  mgr.incr_metric("total_savings", stats.total_savings);
  mgr.incr_metric("root_methods", root_methods.size());
  mgr.incr_metric("reduced_methods", stats.reduced_methods);
  mgr.incr_metric("reduced_methods_variants",
                  (size_t)stats.reduced_methods_variants);
  mgr.incr_metric("selected_reduced_methods", stats.selected_reduced_methods);
  mgr.incr_metric("reprioritizations", stats.reprioritizations);
  mgr.incr_metric("root_method_throwing_check_cast",
                  (size_t)stats.throwing_check_cast);
  mgr.incr_metric("root_method_anchors_not_inlinable_inlining",
                  (size_t)stats.anchors_not_inlinable_inlining);
  mgr.incr_metric("root_method_invokes_not_inlinable_callee_unexpandable",
                  (size_t)stats.invokes_not_inlinable_callee_unexpandable);
  mgr.incr_metric(
      "root_method_invokes_not_inlinable_callee_is_init_too_many_params_to_"
      "expand",
      (size_t)stats.invokes_not_inlinable_callee_too_many_params_to_expand);
  mgr.incr_metric(
      "invokes_not_inlinable_callee_expansion_needs_receiver_cast",
      (size_t)stats.invokes_not_inlinable_callee_expansion_needs_receiver_cast);
  mgr.incr_metric("root_method_invokes_not_inlinable_callee_inconcrete",
                  (size_t)stats.invokes_not_inlinable_callee_inconcrete);
  mgr.incr_metric("root_method_invokes_not_inlinable_inlining",
                  (size_t)stats.invokes_not_inlinable_inlining);
  mgr.incr_metric("root_method_invokes_not_inlinable_too_many_iterations",
                  (size_t)stats.invokes_not_inlinable_too_many_iterations);
  mgr.incr_metric("root_method_invoke_supers", (size_t)stats.invoke_supers);
  mgr.incr_metric("root_method_stackify_returns_objects",
                  (size_t)stats.stackify_returns_objects);
  mgr.incr_metric("root_method_stackify_overlapping_lifetimes",
                  stats.stackify_overlapping_lifetimes.load());
  mgr.incr_metric("root_method_stackify_lifetime_analyses",
                  stats.stackify_lifetime_analyses.load());
  mgr.incr_metric("root_method_too_costly_globally",
                  (size_t)stats.too_costly_globally);
  mgr.incr_metric("expanded_methods", (size_t)stats.expanded_methods);
  mgr.incr_metric("calls_inlined", (size_t)stats.calls_inlined);
  mgr.incr_metric("new_instances_eliminated",
                  (size_t)stats.new_instances_eliminated);
  mgr.incr_metric("inlined_methods_removed", stats.inlined_methods_removed);
  mgr.incr_metric("inlinable_methods_kept", stats.inlinable_methods_kept);
  mgr.incr_metric("lost_returns_through_shrinking",
                  lost_returns_through_shrinking);
  mgr.incr_metric("method_summaries", method_summaries.size());
  mgr.incr_metric("reg_allocs", stats.reg_allocs);
}

static ObjectEscapeAnalysisPass s_pass;
