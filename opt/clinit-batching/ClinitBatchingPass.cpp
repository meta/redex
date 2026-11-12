/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ClinitBatchingPass.h"

#include <algorithm>
#include <chrono>

#include <boost/regex.hpp> // NOLINT(facebook-unused-include-check)

#include "ApiLevelChecker.h"
#include "BaselineProfile.h"
#include "ConfigFiles.h"
#include "ControlFlow.h"
#include "DeterministicContainers.h"
#include "DexUtil.h"
#include "EarlyClassLoadsAnalysis.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "InitClassesWithSideEffects.h"
#include "MethodOverrideGraph.h"
#include "MethodProfiles.h"
#include "MethodUtil.h"
#include "PassManager.h"
#include "Resolver.h"
#include "Show.h"
#include "StaticFieldDependencyGraph.h"
#include "Trace.h"
#include "Walkers.h"

namespace {

// Batching-specific safety checks that go beyond what
// InitClassesWithSideEffects checks. The library handles general
// side-effects (SGET, static calls, constructors, NEW_INSTANCE,
// class hierarchy). These additional checks catch patterns that the
// library considers safe but are unsafe when running a clinit earlier
// at batch time.
enum class BatchingRejection {
  None,
  HasMonitorOp,
  HasThrow,
  HasVirtualCall,
  HasInterfaceCall,
  HasUnresolvedVirtualCall,
  HasTooManyOverrides,
  HasUnresolvedInterfaceCall,
  HasTooManyInterfaceOverrides,
  HasUnresolvedInternalCall,
  HasExternalCall,
  DepthExceeded,
};

constexpr size_t kMaxSafetyCheckDepth = 50;
constexpr size_t kMaxSafetyCheckVisited = 100;
constexpr size_t kMaxOverrideTargets = 5;

struct VirtualCallRejections {
  BatchingRejection no_graph;
  BatchingRejection unresolved;
  BatchingRejection too_many;
};

VirtualCallRejections get_virtual_call_rejections(bool is_iface) {
  if (is_iface) {
    return {BatchingRejection::HasInterfaceCall,
            BatchingRejection::HasUnresolvedInterfaceCall,
            BatchingRejection::HasTooManyInterfaceOverrides};
  }
  return {BatchingRejection::HasVirtualCall,
          BatchingRejection::HasUnresolvedVirtualCall,
          BatchingRejection::HasTooManyOverrides};
}

// Counters for benign virtual/interface calls and depth-exceeded events
// accumulated during a single check_batching_safety traversal.
struct BatchingSafetyStats {
  size_t benign_virtual_calls = 0;
  size_t depth_exceeded = 0;
};

// Result of a batching safety check. Carries both the rejection reason and
// whether the analysis short-circuited on a cycle-detection hit in `visited`.
// Cycle-dependent results must not be cached cross-traversal because they
// are context-dependent: the short-circuit returned None only because the
// method was already being analyzed in the current traversal. In a different
// traversal, that method would be fully analyzed and might be rejected.
struct SafetyResult {
  BatchingRejection rejection;
  bool cycle_dependent;

  static SafetyResult safe() { return {BatchingRejection::None, false}; }
  static SafetyResult cycle() { return {BatchingRejection::None, true}; }
  static SafetyResult reject(BatchingRejection r) { return {r, false}; }

  SafetyResult with_cycle(bool dep) const {
    return {rejection, cycle_dependent || dep};
  }
};

// Forward declaration for mutual recursion.
SafetyResult check_batching_safety_impl(
    const DexMethod* method,
    UnorderedSet<const DexMethod*>& visited,
    const method_override_graph::Graph* override_graph,
    bool skip_benign,
    size_t depth,
    UnorderedMap<const DexMethod*, BatchingRejection>* cache,
    BatchingSafetyStats& stats);

// Helper to recursively check a triggered clinit for batching safety.
// Walks the superclass chain, checking each class's own clinit.
SafetyResult check_clinit_safety(
    DexClass* cls,
    UnorderedSet<const DexMethod*>& visited,
    const method_override_graph::Graph* override_graph,
    bool skip_benign,
    size_t depth,
    UnorderedMap<const DexMethod*, BatchingRejection>* cache,
    BatchingSafetyStats& stats) {
  bool any_cycle = false;
  while (cls != nullptr && !cls->is_external()) {
    auto* clinit = cls->get_clinit();
    if (clinit != nullptr) {
      auto r = check_batching_safety_impl(clinit, visited, override_graph,
                                          skip_benign, depth, cache, stats);
      if (r.rejection != BatchingRejection::None) {
        return r;
      }
      any_cycle = any_cycle || r.cycle_dependent;
    }
    auto* super_type = cls->get_super_class();
    cls = super_type != nullptr ? type_class(super_type) : nullptr;
  }
  return {BatchingRejection::None, any_cycle};
}

// `visited` and `cache` serve different purposes and both are necessary:
//
// - `visited` is per-traversal cycle detection (a fresh UnorderedSet per
//   check_batching_safety call). It prevents infinite recursion. A method is
//   added when we *begin* processing it.
//
// - `cache` is cross-traversal memoization (persists across calls). It avoids
//   re-analyzing methods already fully evaluated. A method is added when we
//   *complete* processing it.
//
// A method currently being processed is in `visited` but NOT in `cache`.
// Results are not cached when:
// - DepthExceeded: a different call path might reach the method at a shallower
//   depth and succeed.
// - cycle_dependent: the result depended on a visited-set short-circuit that
//   is only valid in the current traversal's context.
SafetyResult check_batching_safety_impl(
    const DexMethod* method,
    UnorderedSet<const DexMethod*>& visited,
    const method_override_graph::Graph* override_graph,
    bool skip_benign,
    size_t depth,
    UnorderedMap<const DexMethod*, BatchingRejection>* cache,
    BatchingSafetyStats& stats) {
  if (method == nullptr) {
    return SafetyResult::safe();
  }
  if (method->get_code() == nullptr) {
    if (is_abstract(method)) {
      return SafetyResult::safe();
    }
    if (method->is_external()) {
      if (skip_benign && method::is_clinit_invoked_method_benign(method)) {
        return SafetyResult::safe();
      }
      return SafetyResult::reject(BatchingRejection::HasExternalCall);
    }
    return SafetyResult::reject(BatchingRejection::HasUnresolvedInternalCall);
  }
  if (visited.count(method) != 0) {
    return SafetyResult::cycle();
  }
  // Check memoization cache
  if (cache != nullptr) {
    auto it = cache->find(method);
    if (it != cache->end()) {
      return SafetyResult{it->second, false};
    }
  }
  if (depth >= kMaxSafetyCheckDepth) {
    stats.depth_exceeded++;
    return SafetyResult::reject(BatchingRejection::DepthExceeded);
  }
  if (visited.size() >= kMaxSafetyCheckVisited) {
    stats.depth_exceeded++;
    return SafetyResult::reject(BatchingRejection::DepthExceeded);
  }
  visited.insert(method);

  bool any_cycle = false;

  auto cache_and_return = [&](SafetyResult r) -> SafetyResult {
    r = r.with_cycle(any_cycle);
    if (cache != nullptr && r.rejection != BatchingRejection::DepthExceeded &&
        !r.cycle_dependent) {
      cache->emplace(method, r.rejection);
    }
    return r;
  };

  // Helper: merge a sub-result. Returns true if rejected (caller should
  // return immediately with the cached result).
  auto merge = [&](SafetyResult sub) -> bool {
    any_cycle = any_cycle || sub.cycle_dependent;
    return sub.rejection != BatchingRejection::None;
  };

  // Helper for invoke-static and invoke-direct: recurse into the resolved
  // callee and check the callee's declaring class clinit.
  auto check_resolved_callee = [&](const DexMethod* callee,
                                   DexMethodRef* method_ref) -> SafetyResult {
    if (callee != nullptr) {
      auto r = check_batching_safety_impl(callee, visited, override_graph,
                                          skip_benign, depth + 1, cache, stats);
      if (merge(r)) {
        return r;
      }
      auto r2 = check_clinit_safety(type_class(callee->get_class()), visited,
                                    override_graph, skip_benign, depth + 1,
                                    cache, stats);
      if (merge(r2)) {
        return r2;
      }
    } else {
      auto* ref_class = type_class(method_ref->get_class());
      if (ref_class != nullptr && !ref_class->is_external()) {
        return SafetyResult::reject(
            BatchingRejection::HasUnresolvedInternalCall);
      }
      if (skip_benign && method::is_clinit_invoked_method_benign(method_ref)) {
        return SafetyResult::safe();
      }
      return SafetyResult::reject(BatchingRejection::HasExternalCall);
    }
    return SafetyResult::safe();
  };

  // InstructionIterable requires non-const access for implementation reasons,
  // but we only read instructions. This const_cast is safe.
  auto* code = const_cast<IRCode*>(method->get_code());
  always_assert(code->cfg_built());
  for (auto& mie : InstructionIterable(code->cfg())) {
    auto* insn = mie.insn;
    auto op = insn->opcode();
    if (opcode::is_a_monitor(op)) {
      return cache_and_return(
          SafetyResult::reject(BatchingRejection::HasMonitorOp));
    }
    if (opcode::is_throw(op)) {
      return cache_and_return(
          SafetyResult::reject(BatchingRejection::HasThrow));
    }
    // invoke-super: resolve via manual superclass walk from the caller's class.
    // resolve_method(ref, Super) without a caller falls back to a Virtual
    // search from the ref's declaring class, which is incorrect (T132919742).
    if (opcode::is_invoke_super(op)) {
      auto* method_ref = insn->get_method();
      if (skip_benign && method::is_clinit_invoked_method_benign(method_ref)) {
        stats.benign_virtual_calls++;
        continue;
      }
      auto* caller_cls = type_class(method->get_class());
      const DexMethod* resolved = nullptr;
      if (caller_cls != nullptr) {
        auto* super_type = caller_cls->get_super_class();
        auto* current =
            (super_type != nullptr) ? type_class(super_type) : nullptr;
        while (current != nullptr && !current->is_external()) {
          for (auto* vm : current->get_vmethods()) {
            if (vm->get_name() == method_ref->get_name() &&
                vm->get_proto() == method_ref->get_proto()) {
              resolved = vm;
              current = nullptr;
              break;
            }
          }
          if (current != nullptr) {
            auto* next_super = current->get_super_class();
            current =
                (next_super != nullptr) ? type_class(next_super) : nullptr;
          }
        }
      }
      if (resolved == nullptr) {
        auto* ref_class = type_class(method_ref->get_class());
        if (ref_class != nullptr && !ref_class->is_external()) {
          return cache_and_return(SafetyResult::reject(
              BatchingRejection::HasUnresolvedInternalCall));
        }
        return cache_and_return(
            SafetyResult::reject(BatchingRejection::HasExternalCall));
      }
      if (skip_benign && method::is_clinit_invoked_method_benign(resolved)) {
        stats.benign_virtual_calls++;
        continue;
      }
      auto r = check_batching_safety_impl(resolved, visited, override_graph,
                                          skip_benign, depth + 1, cache, stats);
      if (merge(r)) {
        return cache_and_return(r);
      }
      auto r2 = check_clinit_safety(type_class(resolved->get_class()), visited,
                                    override_graph, skip_benign, depth + 1,
                                    cache, stats);
      if (merge(r2)) {
        return cache_and_return(r2);
      }
      continue;
    }
    // Virtual/interface calls: when override graph is available, resolve
    // targets and follow them. Otherwise reject.
    if (opcode::is_invoke_virtual(op) || opcode::is_invoke_interface(op)) {
      bool is_iface = opcode::is_invoke_interface(op);
      auto [reject_no_graph, reject_unresolved, reject_too_many] =
          get_virtual_call_rejections(is_iface);
      if (override_graph == nullptr) {
        return cache_and_return(SafetyResult::reject(reject_no_graph));
      }
      auto* method_ref = insn->get_method();
      if (skip_benign && method::is_clinit_invoked_method_benign(method_ref)) {
        stats.benign_virtual_calls++;
        continue;
      }
      auto* resolved = resolve_method(method_ref, opcode_to_search(insn));
      if (resolved == nullptr) {
        return cache_and_return(SafetyResult::reject(reject_unresolved));
      }
      if (skip_benign && method::is_clinit_invoked_method_benign(resolved)) {
        stats.benign_virtual_calls++;
        continue;
      }
      auto r = check_batching_safety_impl(resolved, visited, override_graph,
                                          skip_benign, depth + 1, cache, stats);
      if (merge(r)) {
        return cache_and_return(r);
      }
      auto overriders = method_override_graph::get_overriding_methods(
          *override_graph, resolved, /* include_interfaces */ true);
      if (overriders.size() > kMaxOverrideTargets) {
        return cache_and_return(SafetyResult::reject(reject_too_many));
      }
      for (const auto* overrider : UnorderedIterable(overriders)) {
        if (skip_benign && method::is_clinit_invoked_method_benign(overrider)) {
          stats.benign_virtual_calls++;
          continue;
        }
        r = check_batching_safety_impl(overrider, visited, override_graph,
                                       skip_benign, depth + 1, cache, stats);
        if (merge(r)) {
          return cache_and_return(r);
        }
      }
      auto r2 = check_clinit_safety(type_class(resolved->get_class()), visited,
                                    override_graph, skip_benign, depth + 1,
                                    cache, stats);
      if (merge(r2)) {
        return cache_and_return(r2);
      }
      continue;
    }

    // Static field access triggers the declaring class's clinit.
    if (opcode::is_an_sget(op) || opcode::is_an_sput(op)) {
      auto* field_ref = insn->get_field();
      always_assert(field_ref != nullptr);
      auto* resolved_field = resolve_field(field_ref, FieldSearch::Static);
      auto* dep_class = resolved_field != nullptr
                            ? type_class(resolved_field->get_class())
                            : type_class(field_ref->get_class());
      auto r = check_clinit_safety(dep_class, visited, override_graph,
                                   skip_benign, depth + 1, cache, stats);
      if (merge(r)) {
        return cache_and_return(r);
      }
      continue;
    }

    // invoke-static: recurse into callee and check the callee's class clinit.
    if (opcode::is_invoke_static(op)) {
      auto* method_ref = insn->get_method();
      auto* callee = resolve_method(method_ref, MethodSearch::Static);
      auto r = check_resolved_callee(callee, method_ref);
      if (r.rejection != BatchingRejection::None) {
        return cache_and_return(r);
      }
      continue;
    }

    // invoke-direct: recurse into callee and check the callee's class clinit.
    if (opcode::is_invoke_direct(op)) {
      auto* method_ref = insn->get_method();
      auto* callee = resolve_method(method_ref, MethodSearch::Direct);
      auto r = check_resolved_callee(callee, method_ref);
      if (r.rejection != BatchingRejection::None) {
        return cache_and_return(r);
      }
      continue;
    }

    // new-instance: triggers class initialization (clinit chain). The actual
    // constructor call is a separate invoke-direct instruction, which the
    // invoke-direct handler above will process.
    if (op == OPCODE_NEW_INSTANCE) {
      auto* inst_class = type_class(insn->get_type());
      if (inst_class != nullptr && !inst_class->is_external()) {
        auto r = check_clinit_safety(inst_class, visited, override_graph,
                                     skip_benign, depth + 1, cache, stats);
        if (merge(r)) {
          return cache_and_return(r);
        }
      }
    }
  }
  return cache_and_return(SafetyResult::safe());
}

BatchingRejection check_batching_safety(
    const DexMethod* clinit,
    const method_override_graph::Graph* override_graph,
    bool skip_benign,
    BatchingSafetyStats& stats,
    UnorderedMap<const DexMethod*, BatchingRejection>* cache = nullptr) {
  UnorderedSet<const DexMethod*> visited;
  return check_batching_safety_impl(clinit, visited, override_graph,
                                    skip_benign, 0, cache, stats)
      .rejection;
}

} // namespace

constexpr std::string_view kDefaultOrchestratorAnnotation =
    "Lcom/facebook/redex/annotations/GenerateStaticInitBatch;";

void ClinitBatchingPass::bind_config() {
  bind("interaction_pattern", "", m_interaction_pattern,
       "Regex pattern to filter baseline profile interactions (e.g., "
       "``ColdStart``). Only clinits hot in matching interactions are "
       "candidates for batching.");
  bind("skip_benign_virtual_calls", false, m_skip_benign_virtual_calls,
       "When true, skips known-benign virtual/interface calls (e.g., "
       "``Object.toString()``) during safety analysis instead of rejecting "
       "them.");
  bind("orchestrator_annotation",
       std::string(kDefaultOrchestratorAnnotation),
       m_orchestrator_annotation,
       "Dalvik descriptor of the annotation that marks the orchestrator "
       "method (e.g., ``Lcom/facebook/redex/annotations/"
       "GenerateStaticInitBatch;``).");
  trait(Traits::Pass::unique, true);
}

void ClinitBatchingPass::eval_pass(DexStoresVector& stores,
                                   ConfigFiles& /* conf */,
                                   PassManager& /* mgr */) {
  auto scope = build_class_scope(stores);

  // Get the annotation type for the orchestrator
  DexType* orchestrator_anno = DexType::get_type(m_orchestrator_annotation);

  always_assert_log(
      orchestrator_anno != nullptr,
      "ClinitBatchingPass: orchestrator annotation type %s not found in dex. "
      "Ensure the annotation class is included in the build.",
      m_orchestrator_annotation.c_str());

  // Walk all methods to find those annotated with the orchestrator annotation.
  // eval_pass runs before any optimization passes, so we can safely modify
  // rstate here to protect the orchestrator from premature removal by
  // MethodInlinePass (dont_inline) and LocalDce (no_optimizations).
  walk::methods(scope, [&](DexMethod* method) {
    if (m_orchestrator_method != nullptr) {
      return;
    }
    auto* anno_set = method->get_anno_set();
    if (anno_set == nullptr) {
      return;
    }

    auto& anno_list = anno_set->get_annotations();
    for (const auto& anno : anno_list) {
      if (anno->type() == orchestrator_anno) {
        m_orchestrator_method = method;
        // Mark the orchestrator method as dont_inline to prevent
        // MethodInlinePass from removing calls to this empty method
        // before we fill it in during run_pass(). This flag is
        // intentionally left set after run_pass() because the
        // orchestrator should never be inlined — it is called once at
        // startup and its purpose is to be a single AOT-compiled entry
        // point.
        method->rstate.set_dont_inline();
        // Also mark no_optimizations to prevent the purity analysis
        // (compute_no_side_effects_methods) from classifying this empty
        // method as side-effect-free, which would cause LocalDce to
        // remove its call sites. Cleared at the end of run_pass().
        method->rstate.set_no_optimizations();
        TRACE(CLINIT_BATCHING,
              1,
              "ClinitBatchingPass: found orchestrator method %s",
              SHOW(method));
        return;
      }
    }
  });

  always_assert_log(
      m_orchestrator_method != nullptr,
      "ClinitBatchingPass: no method annotated with %s found. "
      "Ensure that the orchestrator method exists and is annotated.",
      m_orchestrator_annotation.c_str());
}

InsertOnlyConcurrentMap<DexMethod*, DexClass*>
ClinitBatchingPass::identify_candidate_clinits(const Scope& scope,
                                               ConfigFiles& conf,
                                               PassManager& mgr) {
  // Load baseline profile config and filter by interaction pattern
  auto baseline_profile_config = conf.get_default_baseline_profile_config();
  if (!m_interaction_pattern.empty()) {
    boost::regex rx(m_interaction_pattern);
    unordered_erase_if(
        baseline_profile_config.interaction_configs,
        [&](auto& p) { return !boost::regex_match(p.first, rx); });
  }

  // Log interaction configs
  for (auto& [interaction_id, config] :
       UnorderedIterable(baseline_profile_config.interaction_configs)) {
    mgr.set_metric("interaction_" + interaction_id, config.threshold);
  }

  // Build baseline profile from method profiles using the filtered config
  baseline_profiles::BaselineProfileConfigMap bp_conf_map = {
      {baseline_profiles::DEFAULT_BASELINE_PROFILE_CONFIG_NAME,
       std::move(baseline_profile_config)}};
  auto baseline_profile = baseline_profiles::get_default_baseline_profile(
      scope, bp_conf_map, conf.get_method_profiles(),
      conf.get_coldstart_classes(),
      baseline_profiles::get_huge_method_max(conf));

  // Track statistics
  std::atomic<size_t> excluded_not_hot{0};
  std::atomic<size_t> excluded_no_optimizations{0};
  std::atomic<size_t> excluded_is_root{0};
  std::atomic<size_t> excluded_cannot_rename{0};
  std::atomic<size_t> excluded_is_enum{0};

  InsertOnlyConcurrentMap<DexMethod*, DexClass*> candidate_clinits;

  walk::parallel::classes(scope, [&](DexClass* cls) {
    DexMethod* method = cls->get_clinit();
    if (method == nullptr) {
      return;
    }

    // Skip methods marked as no_optimizations or should_not_outline
    if (method->rstate.no_optimizations() ||
        method->rstate.should_not_outline()) {
      excluded_no_optimizations.fetch_add(1);
      return;
    }

    // Check if clinit is hot in baseline profile
    auto it = baseline_profile.methods.find(method);
    if (it == baseline_profile.methods.end()) {
      excluded_not_hot.fetch_add(1);
      return;
    }
    if (!it->second.hot) {
      excluded_not_hot.fetch_add(1);
      return;
    }

    // Skip classes that are reachability roots (via ProGuard -keep,
    // @DoNotStrip, etc.). These classes may have semantic requirements on their
    // clinit behavior (e.g., JNI registration, security checks).
    if (!cls->rstate.can_delete()) {
      excluded_is_root.fetch_add(1);
      TRACE(CLINIT_BATCHING,
            4,
            "ClinitBatchingPass: excluding %s - class is a reachability root",
            SHOW(cls));
      return;
    }

    // Skip classes that cannot be renamed. If a class cannot be renamed, it's
    // likely being referenced externally (JNI, reflection, serialization) and
    // its clinit semantics may be important.
    if (!cls->rstate.can_rename()) {
      excluded_cannot_rename.fetch_add(1);
      TRACE(CLINIT_BATCHING,
            4,
            "ClinitBatchingPass: excluding %s - class cannot be renamed",
            SHOW(cls));
      return;
    }

    // Skip enum classes. Enums have a $VALUES static field that is initialized
    // in the clinit and accessed by the auto-generated values() method. The
    // runtime (via Class.getEnumConstants()) can call values() at any time
    // through reflection, before our batched initialization runs, causing NPE.
    //
    // TODO(jimmycleary): This enum exclusion was added by Claude to fix a
    // crash but the reasoning seems dubious — the concern about $VALUES being
    // accessed before batched init applies equally to all static fields, which
    // is what EarlyClassLoadsAnalysis handles. Verify whether enums actually
    // need special treatment before removing.
    if (is_enum(cls)) {
      excluded_is_enum.fetch_add(1);
      TRACE(CLINIT_BATCHING,
            4,
            "ClinitBatchingPass: excluding %s - class is an enum",
            SHOW(cls));
      return;
    }

    candidate_clinits.emplace(method, cls);
    auto* code = method->get_code();
    TRACE(CLINIT_BATCHING,
          3,
          "ClinitBatchingPass: candidate clinit %s (size=%u)",
          SHOW(method),
          code ? code->estimate_code_units() : 0);
  });

  // Report metrics
  mgr.set_metric("candidate_clinits_count", candidate_clinits.size());
  mgr.set_metric("excluded_not_hot", excluded_not_hot.load());
  mgr.set_metric("excluded_no_optimizations", excluded_no_optimizations.load());
  mgr.set_metric("excluded_is_root", excluded_is_root.load());
  mgr.set_metric("excluded_cannot_rename", excluded_cannot_rename.load());
  mgr.set_metric("excluded_is_enum", excluded_is_enum.load());

  TRACE(CLINIT_BATCHING,
        1,
        "ClinitBatchingPass: identified %zu candidate clinits "
        "(excluded: %zu not hot, %zu no_optimizations, "
        "%zu is_root, %zu cannot_rename, %zu is_enum)",
        candidate_clinits.size(),
        excluded_not_hot.load(),
        excluded_no_optimizations.load(),
        excluded_is_root.load(),
        excluded_cannot_rename.load(),
        excluded_is_enum.load());

  return candidate_clinits;
}

clinit_batching::TopologicalSortResult
ClinitBatchingPass::build_dependency_graph(
    const UnorderedMap<DexMethod*, DexClass*>& candidate_clinits,
    PassManager& mgr,
    const method_override_graph::Graph* override_graph,
    bool skip_benign) {
  clinit_batching::StaticFieldDependencyGraph graph;

  // Build the dependency graph from candidate clinits
  graph.build(candidate_clinits, override_graph, skip_benign);

  // Perform topological sort and report metrics
  auto sort_result = graph.topological_sort();

  mgr.set_metric("dependency_graph_nodes", graph.size());
  mgr.set_metric("ordered_classes_count", sort_result.ordered_classes.size());
  mgr.set_metric("cyclic_classes_count", sort_result.cyclic_classes.size());

  TRACE(CLINIT_BATCHING,
        1,
        "ClinitBatchingPass: dependency graph has %zu nodes, "
        "%zu in valid order, %zu in cycles",
        graph.size(),
        sort_result.ordered_classes.size(),
        sort_result.cyclic_classes.size());

  return sort_result;
}

UnorderedMap<DexClass*, DexMethod*> ClinitBatchingPass::transform_clinits(
    const std::vector<DexClass*>& ordered_classes,
    ConfigFiles& conf,
    PassManager& mgr) {
  auto& method_profiles = conf.get_method_profiles();

  size_t affected_final_fields = 0;
  UnorderedMap<DexClass*, DexMethod*> transformed_clinits;

  // Process each class in the ordered list
  for (DexClass* cls : ordered_classes) {
    DexMethod* clinit = cls->get_clinit();
    always_assert(clinit != nullptr);
    IRCode* code = clinit->get_code();
    always_assert(code != nullptr);
    always_assert(code->cfg_built());

    // Step 1: Remove ACC_FINAL from static fields being written
    UnorderedSet<DexField*> final_fields;
    for (auto& mie : InstructionIterable(code->cfg())) {
      auto* insn = mie.insn;
      if (opcode::is_an_sput(insn->opcode())) {
        auto* field = insn->get_field();
        auto* resolved_field = resolve_field(field, FieldSearch::Static);
        if (resolved_field == nullptr || !is_final(resolved_field)) {
          continue;
        }
        // Only remove ACC_FINAL from fields belonging to this class.
        // A clinit could theoretically write to a parent class's field.
        if (resolved_field->get_class() != clinit->get_class()) {
          continue;
        }
        if (final_fields.insert(resolved_field).second) {
          resolved_field->set_access(resolved_field->get_access() & ~ACC_FINAL);
        }
      }
    }
    affected_final_fields += final_fields.size();

    // Step 2: Create new __initStatics$<ClassName>() method with clinit body
    // Generate a unique method name based on the class name
    std::string class_name = show(cls->get_type());
    // Remove L prefix and ; suffix, replace / with _
    if (class_name.size() > 2 && class_name[0] == 'L' &&
        class_name.back() == ';') {
      class_name = class_name.substr(1, class_name.size() - 2);
    }
    std::replace(class_name.begin(), class_name.end(), '/', '_');
    std::string new_method_name = "__initStatics$" + class_name;

    const auto* method_name = DexMethod::get_unique_name(
        clinit->get_class(), DexString::make_string(new_method_name),
        clinit->get_proto());
    auto* init_statics =
        DexMethod::make_method(clinit->get_class(), method_name,
                               clinit->get_proto())
            ->make_concrete(ACC_STATIC | ACC_PUBLIC, clinit->release_code(),
                            /* is_virtual */ false);

    init_statics->rstate.set_generated();
    init_statics->rstate.set_dont_inline();
    int api_level = api::LevelChecker::get_method_level(clinit);
    init_statics->rstate.set_api_level(api_level);
    init_statics->set_deobfuscated_name(show_deobfuscated(init_statics));

    // Step 3: Add the new method to the class
    cls->add_method(init_statics);

    // Step 4: Derive stats for the new method from the original clinit
    method_profiles.derive_stats(init_statics, {clinit});

    // Step 5: Remove the original clinit, making the class trivially
    // initialized (a class with no clinit needs no initialization barrier).
    cls->remove_method(clinit);

    transformed_clinits.emplace(cls, init_statics);

    TRACE(CLINIT_BATCHING,
          3,
          "ClinitBatchingPass: transformed clinit %s -> %s",
          SHOW(cls),
          SHOW(init_statics));
  }

  // Report metrics
  mgr.set_metric("transformed_clinits_count", transformed_clinits.size());
  mgr.set_metric("affected_final_fields", affected_final_fields);

  TRACE(
      CLINIT_BATCHING,
      1,
      "ClinitBatchingPass: transformed %zu clinits, affected %zu final fields",
      transformed_clinits.size(),
      affected_final_fields);

  return transformed_clinits;
}

size_t ClinitBatchingPass::generate_orchestrator(
    DexMethod* orchestrator_method,
    const UnorderedMap<DexClass*, DexMethod*>& init_statics_methods,
    const std::vector<DexClass*>& ordered_classes,
    PassManager& mgr) {
  always_assert(orchestrator_method != nullptr);

  auto* code = orchestrator_method->get_code();
  always_assert(code != nullptr);
  always_assert(code->cfg_built());
  auto& cfg = code->cfg();

  // Find the RETURN_VOID instruction where we'll insert our calls
  auto ii = cfg::InstructionIterable(cfg);
  auto it = ii.begin();
  auto end = ii.end();

  // Skip any parameter loading instructions
  while (it != end && opcode::is_a_load_param(it->insn->opcode())) {
    ++it;
  }

  // The orchestrator should be empty (just RETURN_VOID). We set dont_inline
  // and no_optimizations in eval_pass to prevent other passes from modifying
  // it.
  always_assert_log(it != end && it->insn->opcode() == OPCODE_RETURN_VOID,
                    "ClinitBatchingPass: orchestrator method %s is not empty "
                    "(expected RETURN_VOID, found %s)",
                    SHOW(orchestrator_method),
                    it != end ? SHOW(it->insn) : "end");

  // Generate invoke-static instructions for each __initStatics$*() method
  // in dependency order
  std::vector<IRInstruction*> insns;
  insns.reserve(ordered_classes.size());

  for (DexClass* cls : ordered_classes) {
    auto it2 = init_statics_methods.find(cls);
    if (it2 == init_statics_methods.end()) {
      continue;
    }

    DexMethod* init_statics = it2->second;

    // Generate: invoke-static {}, <init_statics>
    auto* invoke = new IRInstruction(OPCODE_INVOKE_STATIC);
    invoke->set_method(init_statics);
    invoke->set_srcs_size(0);
    insns.push_back(invoke);

    TRACE(CLINIT_BATCHING,
          3,
          "ClinitBatchingPass: adding call to %s in orchestrator",
          SHOW(init_statics));
  }

  if (insns.empty()) {
    TRACE(CLINIT_BATCHING,
          1,
          "ClinitBatchingPass: no init calls to generate for orchestrator");
    return 0;
  }

  // Insert the generated instructions before the RETURN_VOID
  cfg.insert_before(it, insns);

  // Report metrics
  mgr.set_metric("num_init_calls_generated", insns.size());

  TRACE(CLINIT_BATCHING,
        1,
        "ClinitBatchingPass: generated %zu invoke-static calls in "
        "orchestrator method %s",
        insns.size(),
        SHOW(orchestrator_method));

  return insns.size();
}

void ClinitBatchingPass::run_pass(DexStoresVector& stores,
                                  ConfigFiles& conf,
                                  PassManager& mgr) {
  always_assert(m_orchestrator_method != nullptr);

  auto scope = build_class_scope(stores);

  // Build method override graph. EarlyClassLoadsAnalysis always needs it for
  // virtual call resolution; the safety analysis uses it conditionally.
  auto method_override_graph = method_override_graph::build_graph(scope);

  // Step 1: Run early class loads analysis to find classes loaded before
  // the orchestrator is called
  clinit_batching::EarlyClassLoadsAnalysis early_analysis(
      m_orchestrator_method, conf, method_override_graph.get());
  auto early_result = early_analysis.run();

  always_assert_log(!early_result.error_message.has_value(),
                    "ClinitBatchingPass: early class loads analysis failed: %s",
                    early_result.error_message.has_value()
                        ? early_result.error_message->c_str()
                        : "");

  always_assert_log(
      early_result.orchestrator_encountered,
      "ClinitBatchingPass: orchestrator method %s not encountered in "
      "callgraph from entry points. Ensure the orchestrator is reachable "
      "from an application entry point.",
      SHOW(m_orchestrator_method));

  mgr.set_metric("early_loaded_classes",
                 early_result.early_loaded_classes.size());
  mgr.set_metric("entry_points_count", early_result.entry_points.size());

  TRACE(CLINIT_BATCHING,
        1,
        "ClinitBatchingPass: found %zu early loaded classes from %zu entry "
        "points",
        early_result.early_loaded_classes.size(),
        early_result.entry_points.size());

  // Step 2: Identify candidate clinits based on baseline profile
  auto candidate_clinits = identify_candidate_clinits(scope, conf, mgr);

  // Step 3: Filter out early loaded classes from candidates
  size_t excluded_early = 0;
  UnorderedMap<DexMethod*, DexClass*> filtered_candidates;
  for (const auto& [clinit, cls] : UnorderedIterable(candidate_clinits)) {
    if (early_result.early_loaded_classes.count(cls) != 0) {
      TRACE(CLINIT_BATCHING,
            3,
            "ClinitBatchingPass: excluding %s - loaded before orchestrator",
            SHOW(clinit));
      excluded_early++;
    } else {
      filtered_candidates.emplace(clinit, cls);
    }
  }
  mgr.set_metric("excluded_early_loads", excluded_early);

  TRACE(CLINIT_BATCHING,
        1,
        "ClinitBatchingPass: excluded %zu candidates due to early class loads",
        excluded_early);

  // Step 4: Safety analysis using InitClassesWithSideEffects as the base
  // filter, plus batching-specific checks (monitors, throws, virtual/interface
  // calls with override graph support).
  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, /* create_init_class_insns */ false, method_override_graph.get());

  size_t rejected_side_effects = 0;
  size_t rejected_monitor = 0;
  size_t rejected_throw = 0;
  size_t rejected_virtual_call = 0;
  size_t rejected_interface_call = 0;
  size_t rejected_unresolved_virtual = 0;
  size_t rejected_too_many_overrides = 0;
  size_t rejected_unresolved_interface = 0;
  size_t rejected_too_many_interface_overrides = 0;
  size_t rejected_unresolved_internal = 0;
  size_t rejected_external_call = 0;
  size_t rejected_depth_exceeded = 0;
  size_t benign_virtual_calls = 0;
  size_t depth_exceeded_events = 0;
  UnorderedMap<const DexMethod*, BatchingRejection> safety_cache;

  UnorderedMap<DexMethod*, DexClass*> analysis_candidates;
  size_t candidate_idx = 0;
  for (const auto& [clinit, cls] : UnorderedIterable(filtered_candidates)) {
    candidate_idx++;

    // Two-stage filter: InitClassesWithSideEffects + batching-specific checks
    if (init_classes_with_side_effects.refine(cls->get_type()) != nullptr) {
      rejected_side_effects++;
      continue;
    }
    BatchingSafetyStats call_stats;
    auto pre_cache_size = safety_cache.size();
    auto start = std::chrono::steady_clock::now();
    auto batching_rejection = check_batching_safety(
        clinit, method_override_graph.get(), m_skip_benign_virtual_calls,
        call_stats, &safety_cache);
    auto elapsed_ms = std::chrono::duration_cast<std::chrono::milliseconds>(
                          std::chrono::steady_clock::now() - start)
                          .count();
    TRACE(CLINIT_BATCHING, 2,
          "check_batching_safety[%zu/%zu]: %s took %lldms -> %d "
          "(cache: %zu -> %zu, benign: %zu, depth_exceeded: %zu)",
          candidate_idx, candidate_clinits.size(), SHOW(clinit),
          (long long)elapsed_ms, static_cast<int>(batching_rejection),
          pre_cache_size, safety_cache.size(), call_stats.benign_virtual_calls,
          call_stats.depth_exceeded);
    benign_virtual_calls += call_stats.benign_virtual_calls;
    depth_exceeded_events += call_stats.depth_exceeded;
    switch (batching_rejection) {
    case BatchingRejection::HasMonitorOp:
      rejected_monitor++;
      break;
    case BatchingRejection::HasThrow:
      rejected_throw++;
      break;
    case BatchingRejection::HasVirtualCall:
      rejected_virtual_call++;
      break;
    case BatchingRejection::HasUnresolvedVirtualCall:
      rejected_virtual_call++;
      rejected_unresolved_virtual++;
      break;
    case BatchingRejection::HasTooManyOverrides:
      rejected_virtual_call++;
      rejected_too_many_overrides++;
      break;
    case BatchingRejection::HasInterfaceCall:
      rejected_interface_call++;
      break;
    case BatchingRejection::HasUnresolvedInterfaceCall:
      rejected_interface_call++;
      rejected_unresolved_interface++;
      break;
    case BatchingRejection::HasTooManyInterfaceOverrides:
      rejected_interface_call++;
      rejected_too_many_interface_overrides++;
      break;
    case BatchingRejection::HasUnresolvedInternalCall:
      rejected_unresolved_internal++;
      break;
    case BatchingRejection::HasExternalCall:
      rejected_external_call++;
      break;
    case BatchingRejection::DepthExceeded:
      rejected_depth_exceeded++;
      break;
    case BatchingRejection::None:
      analysis_candidates.emplace(clinit, cls);
      break;
    }
  }

  mgr.set_metric("analysis_candidates", analysis_candidates.size());
  mgr.set_metric("rejected_side_effects", rejected_side_effects);
  mgr.set_metric("rejected_monitor", rejected_monitor);
  mgr.set_metric("rejected_throw", rejected_throw);
  mgr.set_metric("rejected_virtual_call", rejected_virtual_call);
  mgr.set_metric("rejected_unresolved_virtual", rejected_unresolved_virtual);
  mgr.set_metric("rejected_too_many_overrides", rejected_too_many_overrides);
  mgr.set_metric("rejected_interface_call", rejected_interface_call);
  mgr.set_metric("rejected_unresolved_interface",
                 rejected_unresolved_interface);
  mgr.set_metric("rejected_too_many_interface_overrides",
                 rejected_too_many_interface_overrides);
  mgr.set_metric("rejected_unresolved_internal", rejected_unresolved_internal);
  mgr.set_metric("rejected_external_call", rejected_external_call);
  mgr.set_metric("benign_virtual_calls", benign_virtual_calls);
  mgr.set_metric("rejected_depth_exceeded", rejected_depth_exceeded);
  mgr.set_metric("depth_exceeded_events", depth_exceeded_events);

  TRACE(CLINIT_BATCHING, 1,
        "ClinitBatchingPass: safety analysis accepted %zu "
        "(rejected: side_effects=%zu, monitor=%zu, throw=%zu, "
        "virtual_call=%zu, interface_call=%zu)",
        analysis_candidates.size(), rejected_side_effects, rejected_monitor,
        rejected_throw, rejected_virtual_call, rejected_interface_call);

  // Verify invariant: every candidate must pass batching safety checks.
  // The dependency graph relies on the absence of virtual/interface calls,
  // monitor ops, and throw in the transitive call graph reachable through
  // invoke-static/invoke-direct chains.
  for (const auto& [clinit, cls] : UnorderedIterable(analysis_candidates)) {
    BatchingSafetyStats verify_stats;
    auto rejection = check_batching_safety(clinit, method_override_graph.get(),
                                           m_skip_benign_virtual_calls,
                                           verify_stats, &safety_cache);
    always_assert_log(
        rejection == BatchingRejection::None,
        "ClinitBatchingPass: candidate %s passed initial safety check but "
        "fails re-check before dep graph build (this is a bug)",
        SHOW(clinit));
  }

  // Step 5: Build dependency graph and topological sort
  auto sort_result = build_dependency_graph(analysis_candidates, mgr,
                                            method_override_graph.get(),
                                            m_skip_benign_virtual_calls);

  // Step 6: Transform clinits in dependency order
  auto transformed_clinits =
      transform_clinits(sort_result.ordered_classes, conf, mgr);

  // Step 7: Generate orchestrator method body with invoke-static calls
  auto num_init_calls =
      generate_orchestrator(m_orchestrator_method, transformed_clinits,
                            sort_result.ordered_classes, mgr);

  mgr.set_metric("batched_clinits", transformed_clinits.size());
  mgr.set_metric("skipped_cyclic_classes", sort_result.cyclic_classes.size());
  mgr.set_metric("orchestrator_generated", 1);
  mgr.set_metric("interaction_pattern_set",
                 m_interaction_pattern.empty() ? 0 : 1);
  mgr.set_metric("skip_benign_virtual_calls",
                 m_skip_benign_virtual_calls ? 1 : 0);
  TRACE(CLINIT_BATCHING,
        1,
        "ClinitBatchingPass: batched %zu clinits, skipped %zu cyclic classes, "
        "%zu orchestrator calls",
        transformed_clinits.size(),
        sort_result.cyclic_classes.size(),
        num_init_calls);

  // Clear no_optimizations so later passes can optimize the now-populated
  // orchestrator body.
  m_orchestrator_method->rstate.reset_no_optimizations();
}

static ClinitBatchingPass s_pass;
