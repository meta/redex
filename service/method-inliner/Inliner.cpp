/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "Inliner.h"

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <limits>
#include <optional>
#include <utility>
#include <vector>

#include "ApiLevelChecker.h"
#include "CFGInliner.h"
#include "ClassUtil.h"
#include "ConstantPropagationAnalysis.h"
#include "ConstructorAnalysis.h"
#include "Debug.h"
#include "DexInstruction.h"
#include "InlineForSpeed.h"
#include "InlinerConfig.h"
#include "LiveRange.h"
#include "LoopInfo.h"
#include "MonitorCount.h"
#include "Mutators.h"
#include "OptData.h"
#include "OutlinedMethods.h"
#include "PartialInliner.h"
#include "RecursionPruner.h"
#include "SourceBlocks.h"
#include "Timer.h"
#include "UnknownVirtuals.h"
#include "Walkers.h"
#include "WorkQueue.h"

using namespace opt_metadata;
using namespace outliner;

namespace {
/*
 * This is the maximum size of method that Dex bytecode can encode.
 * The table of instructions is indexed by a 32 bit unsigned integer.
 */
constexpr uint64_t HARD_MAX_INSTRUCTION_SIZE = UINT64_C(1) << 32;

// TODO: Make configurable.
const uint64_t MAX_HOT_COLD_CALLEE_SIZE = 27;

// A block's execution count: the max-over-interactions synthetic `val` of its
// first source block (0 when unprofiled / no source block).
float block_max_count(cfg::Block* block) {
  return source_blocks::max_val_over_interactions(
             source_blocks::get_first_source_block(block))
      .value_or(0.0f);
}

/*
 * Whether an invocation naming `callee` verifies at `insn` as far as the
 * receiver goes, which a static callee trivially does.
 */
bool has_receiver_of_callee_class(const IRInstruction* insn,
                                  const DexMethod* callee) {
  return is_static(callee) ||
         type::check_cast(insn->get_method()->get_class(), callee->get_class());
}

/*
 * The type the receiver of `insn` must be cast to for an invocation naming
 * `callee` to verify, or nullptr if no cast is needed.
 */
const DexType* get_needs_receiver_cast(const IRInstruction* insn,
                                       const DexMethod* callee) {
  return has_receiver_of_callee_class(insn, callee) ? nullptr
                                                    : callee->get_class();
}

/*
 * Given a method, gather all resolved init-class instruction types. This
 * gathering-logic mimics (the first part of) what
 * DexStructure::resolve_init_classes does.
 */
UnorderedSet<const DexType*> gather_resolved_init_class_types(
    const cfg::ControlFlowGraph& cfg,
    const init_classes::InitClassesWithSideEffects&
        init_classes_with_side_effects) {
  UnorderedSet<const DexType*> refined_init_class_types;

  for (const auto& mie : InstructionIterable(cfg)) {
    auto* insn = mie.insn;
    if (insn->opcode() != IOPCODE_INIT_CLASS) {
      continue;
    }
    const auto* refined_type =
        init_classes_with_side_effects.refine(insn->get_type());
    if (refined_type != nullptr) {
      refined_init_class_types.insert(const_cast<DexType*>(refined_type));
    }
  }

  return refined_init_class_types;
}

// Inlining methods into different classes might lead to worse cross-dex-ref
// minimization results. \returns the estimated cross dex penalty caused by
// inlining.
float estimate_cross_dex_penalty(const InlinedCost* inlined_cost,
                                 const InlinerCostConfig& inliner_cost_config,
                                 bool use_other_refs) {
  float cross_dex_penalty =
      inliner_cost_config.cross_dex_penalty_coe1 * inlined_cost->method_refs;
  if (use_other_refs &&
      (inlined_cost->method_refs + inlined_cost->other_refs) > 0) {
    cross_dex_penalty +=
        inliner_cost_config.cross_dex_penalty_coe2 * inlined_cost->other_refs +
        inliner_cost_config.cross_dex_penalty_const;
  }
  return cross_dex_penalty;
}

bool is_finalizable(const DexType* type) {
  for (const auto* cls = type_class(type);
       (cls != nullptr) && cls->get_type() != type::java_lang_Object();
       cls = type_class(cls->get_super_class())) {
    for (const auto* m : cls->get_vmethods()) {
      if (m->get_name()->str() != "finalize") {
        continue;
      }
      const auto* p = m->get_proto();
      if (!p->is_void() || !p->get_args()->empty()) {
        continue;
      }
      return true;
    }
  }
  return false;
}

} // namespace

MultiMethodInliner::MultiMethodInliner(
    const std::vector<DexClass*>& scope,
    const init_classes::InitClassesWithSideEffects&
        init_classes_with_side_effects,
    DexStoresVector& stores,
    const ConfigFiles& conf,
    const UnorderedSet<DexMethod*>& candidates,
    std::function<DexMethod*(DexMethodRef*, MethodSearch, const DexMethod*)>
        concurrent_resolve_fn,
    const inliner::InlinerConfig& config,
    int min_sdk,
    MultiMethodInlinerMode mode /* default is InterDex */,
    const CalleeCallerInsns& true_virtual_callers,
    InlineForSpeed* inline_for_speed,
    bool analyze_and_prune_inits,
    const UnorderedSet<DexMethodRef*>& configured_pure_methods,
    const api::AndroidSDK* min_sdk_api,
    bool cross_dex_penalty,
    const UnorderedSet<const DexString*>& configured_finalish_field_names,
    bool local_only,
    HotColdInliningBehavior hot_cold_inlining_behavior,
    std::optional<baseline_profiles::BaselineProfile> baseline_profile,
    InlinerCostConfig inliner_cost_config,
    const UnorderedSet<const DexMethod*>* unfinalized_init_methods,
    InsertOnlyConcurrentSet<DexMethod*>* methods_with_write_barrier,
    const method_override_graph::Graph* method_override_graph)
    : m_min_sdk_api(min_sdk_api),
      m_concurrent_resolver(std::move(concurrent_resolve_fn)),
      m_scheduler(
          [this](DexMethod* method) {
            auto it = m_caller_callee.find(method);
            if (it != m_caller_callee.end()) {
              always_assert(method->get_code()->cfg_built());
              UnorderedSet<DexMethod*> callees;
              callees.reserve(it->second.size());
              for (auto& p : UnorderedIterable(it->second)) {
                callees.insert(p.first);
              }
              inline_callees(method, callees,
                             /* filter_via_should_inline */ true);
              // We schedule the post-processing, to allow other unlocked
              // higher-priority tasks take precedence
              m_scheduler.augment(
                  method, [this, method] { postprocess_method(method); });
            } else {
              postprocess_method(method);
            }
          },
          0),
      m_scope(scope),
      m_config(config),
      m_mode(mode),
      m_inline_for_speed(inline_for_speed),
      m_analyze_and_prune_inits(analyze_and_prune_inits),
      m_cross_dex_penalty(cross_dex_penalty),
      m_shrinker(stores,
                 scope,
                 init_classes_with_side_effects,
                 conf,
                 config.shrinker,
                 min_sdk,
                 configured_pure_methods,
                 configured_finalish_field_names,
                 /* configured_finalish_fields */ {},
                 /* package_name */ std::nullopt,
                 /* package_name */ method_override_graph),
      m_local_only(local_only),
      m_hot_cold_inlining_behavior(hot_cold_inlining_behavior),
      m_baseline_profile(std::move(baseline_profile)),
      m_inliner_cost_config(inliner_cost_config),
      m_unfinalized_init_methods(unfinalized_init_methods),
      m_methods_with_write_barrier(methods_with_write_barrier) {
  Timer t("MultiMethodInliner construction");
  for (const auto& callee_callers : UnorderedIterable(true_virtual_callers)) {
    auto* callee = callee_callers.first;
    if (callee_callers.second.other_call_sites) {
      m_true_virtual_callees_with_other_call_sites.insert(callee);
    }
    for (const auto& caller_insns :
         UnorderedIterable(callee_callers.second.caller_insns)) {
      for (auto* insn : UnorderedIterable(caller_insns.second)) {
        auto emplaced = m_caller_virtual_callees[caller_insns.first]
                            .insns.emplace(insn, callee)
                            .second;
        always_assert(emplaced);
      }
    }
    insert_unordered_iterable(m_inlined_invokes_need_cast,
                              callee_callers.second.inlined_invokes_need_cast);
  }
  if (mode == IntraDex) {
    m_x_dex = std::make_unique<XDexMethodRefs>(stores);
  }
  // Walk every opcode in scope looking for calls to inlinable candidates and
  // build a map of callers to callees and the reverse callees to callers.
  if (min_sdk_api != nullptr) {
    m_ref_checkers =
        std::make_unique<InsertOnlyConcurrentMap<size_t, RefChecker>>();
  }

  walk::parallel::opcodes(
      scope, [](DexMethod*) { return true; },
      [&](DexMethod* caller, IRInstruction* insn) {
        if (!opcode::is_an_invoke(insn->opcode())) {
          return;
        }
        auto* callee = m_concurrent_resolver(insn->get_method(),
                                             opcode_to_search(insn), caller);
        if (callee == nullptr || !callee->is_concrete() ||
            (candidates.count(callee) == 0u)) {
          return;
        }
        m_callee_caller.update(callee,
                               [caller](const DexMethod*,
                                        UnorderedMap<DexMethod*, size_t>& v,
                                        bool) { ++v[caller]; });
        m_caller_callee.update(caller,
                               [callee](const DexMethod*,
                                        UnorderedMap<DexMethod*, size_t>& v,
                                        bool) { ++v[callee]; });
      });
  for (const auto& callee_callers : UnorderedIterable(true_virtual_callers)) {
    auto* callee = callee_callers.first;
    for (const auto& caller_insns :
         UnorderedIterable(callee_callers.second.caller_insns)) {
      auto* caller = const_cast<DexMethod*>(caller_insns.first);
      auto count = caller_insns.second.size();
      always_assert(count > 0);
      m_callee_caller.update_unsafe(callee,
                                    [&](const DexMethod*,
                                        UnorderedMap<DexMethod*, size_t>& v,
                                        bool) { v[caller] += count; });
      bool added_virtual_only = false;
      m_caller_callee.update_unsafe(
          caller,
          [&](const DexMethod*, UnorderedMap<DexMethod*, size_t>& v, bool) {
            added_virtual_only = (v[callee] += count) == count;
          });
      if (added_virtual_only) {
        // We added a new callee that is only valid via m_caller_virtual_callees
        m_caller_virtual_callees[caller].exclusive_callees.insert(callee);
      }
    }
  }

  if (m_hot_cold_inlining_behavior != HotColdInliningBehavior::None ||
      m_config.partial_hot_hot_inline) {
    std::vector<const DexMethod*> methods;
    for (auto&& [callee, _] : UnorderedIterable(m_callee_caller)) {
      methods.push_back(callee);
    }
    for (auto&& [caller, _] : UnorderedIterable(m_caller_callee)) {
      if (m_callee_caller.count_unsafe(caller) == 0u) {
        methods.push_back(caller);
      }
    }
    // Now try to get the hot blocks and exclude them too based on the
    // instrumented SourceBlock data.
    workqueue_run<const DexMethod*>(
        [&](const DexMethod* method) {
          const auto* code = method->get_code();
          if (code == nullptr || !code->cfg_built()) {
            return;
          }
          const auto& cfg = code->cfg();
          if (m_hot_cold_inlining_behavior != HotColdInliningBehavior::None) {
            auto blocks = cfg.blocks();
            if (std::any_of(blocks.begin(), blocks.end(),
                            source_blocks::is_not_cold)) {
              m_not_cold_methods.insert(method);
            }
            if (source_blocks::method_maybe_hot(method)) {
              m_maybe_hot_methods.insert(method);
            }
          }
          if (m_config.partial_hot_hot_inline &&
              source_blocks::is_hot(cfg.entry_block())) {
            m_hot_methods.insert(method);
          }
        },
        methods);
  }

  if (m_inliner_cost_config.inline_hot_callsite_count_percentile > 0) {
    build_hot_callsite_count_ramp();
  }
}

void MultiMethodInliner::inline_methods() {
  // The order in which we inline is such that once a callee is considered to
  // be inlined, its code will no longer change. So we can cache...
  // - its size
  // - its set of type refs
  // - its set of method refs
  // - whether all callers are in the same class, and are called from how many
  //   classes
  m_callee_partial_code = std::make_unique<
      InsertOnlyConcurrentMap<const DexMethod*, PartialCode>>();
  m_callee_insn_sizes =
      std::make_unique<InsertOnlyConcurrentMap<const DexMethod*, size_t>>();
  m_callee_type_refs = std::make_unique<InsertOnlyConcurrentMap<
      const DexMethod*, std::shared_ptr<UnorderedBag<const DexType*>>>>();
  if (m_ref_checkers) {
    m_callee_code_refs = std::make_unique<
        InsertOnlyConcurrentMap<const DexMethod*, std::shared_ptr<CodeRefs>>>();
  }
  if (m_x_dex) {
    m_callee_x_dex_refs = std::make_unique<InsertOnlyConcurrentMap<
        const DexMethod*, std::shared_ptr<XDexMethodRefs::Refs>>>();
  }
  m_callee_caller_refs = std::make_unique<
      InsertOnlyConcurrentMap<const DexMethod*, CalleeCallerRefs>>();

  // Instead of changing visibility as we inline, blocking other work on the
  // critical path, we do it all in parallel at the end.
  m_delayed_visibility_changes = std::make_unique<VisibilityChanges>();

  // we want to inline bottom up, so as a first step, for all callers, we
  // recurse into all inlinable callees until we hit a leaf and we start
  // inlining from there. First, we just gather data on
  // caller/non-recursive-callees pairs for each stack depth.
  {
    auto exclude_fn = [this](DexMethod* caller, DexMethod* callee) {
      return for_speed() &&
             !m_inline_for_speed->should_inline_generic(caller, callee);
    };
    inliner::RecursionPruner recursion_pruner(m_callee_caller, m_caller_callee,
                                              std::move(exclude_fn));
    recursion_pruner.run();
    info.recursive = recursion_pruner.recursive_call_sites();
    info.max_call_stack_depth = recursion_pruner.max_call_stack_depth();
    m_recursive_callees = std::move(recursion_pruner.recursive_callees());
    m_speed_excluded_callees = std::move(recursion_pruner.excluded_callees());
  }

  if (m_config.use_call_site_summaries) {
    m_call_site_summarizer = std::make_unique<inliner::CallSiteSummarizer>(
        m_shrinker, m_callee_caller, m_caller_callee,
        [this](DexMethod* caller, IRInstruction* insn) -> DexMethod* {
          auto callee_opt = this->get_callee(caller, insn);
          return callee_opt.value_or(nullptr);
        },
        [this](DexMethod* callee) -> bool {
          return (m_recursive_callees.count(callee) != 0u) || root(callee) ||
                 !can_rename(callee) ||
                 (m_true_virtual_callees_with_other_call_sites.count(callee) !=
                  0u) ||
                 (m_speed_excluded_callees.count(callee) != 0u);
        },
        /* filter_fn */ nullptr, &info.call_site_summary_stats);
    m_call_site_summarizer->summarize();
  }

  // Inlining and shrinking initiated from within this method will be done
  // in parallel.
  m_scheduler.get_thread_pool().set_num_threads(
      m_config.debug ? 1 : redex_parallel::default_num_threads());

  // Second, compute caller priorities --- the callers get a priority assigned
  // that reflects how many other callers will be waiting for them.
  UnorderedSet<DexMethod*> methods_to_schedule;
  for (auto& p : UnorderedIterable(m_caller_callee)) {
    const auto* caller = p.first;
    for (auto& q : UnorderedIterable(p.second)) {
      auto* callee = q.first;
      m_scheduler.add_dependency(const_cast<DexMethod*>(caller), callee);
    }
  }

  // Third, schedule and run tasks for all selected methods.
  if (m_shrinker.enabled() && m_config.shrink_other_methods) {
    walk::code(m_scope, [&](DexMethod* method, IRCode& /*code*/) {
      methods_to_schedule.insert(method);
    });
  } else {
    for (auto& p : UnorderedIterable(m_caller_callee)) {
      methods_to_schedule.insert(const_cast<DexMethod*>(p.first));
    }
    for (auto& p : UnorderedIterable(m_callee_caller)) {
      methods_to_schedule.insert(const_cast<DexMethod*>(p.first));
    }
  }

  info.critical_path_length = m_scheduler.run(std::move(methods_to_schedule));

  flush();
  info.waited_seconds = m_scheduler.get_thread_pool().get_waited_seconds();
}

std::optional<DexMethod*> MultiMethodInliner::get_callee(DexMethod* caller,
                                                         IRInstruction* insn) {
  if (!opcode::is_an_invoke(insn->opcode())) {
    return std::nullopt;
  }
  auto* callee =
      m_concurrent_resolver(insn->get_method(), opcode_to_search(insn), caller);
  auto it = m_caller_virtual_callees.find(caller);
  if (it == m_caller_virtual_callees.end()) {
    return callee;
  }
  const auto& cvc = it->second;
  auto it2 = cvc.insns.find(insn);
  if (it2 == cvc.insns.end()) {
    // We couldn't find a matching true virtual invocation; only allow callee if
    // it's not exclusive to matching true virtuals.
    return cvc.exclusive_callees.count(callee) != 0u
               ? std::nullopt
               : std::make_optional(callee);
  }
  return it2->second;
}

void MultiMethodInliner::inline_callees(DexMethod* caller,
                                        const UnorderedSet<DexMethod*>& callees,
                                        bool filter_via_should_inline) {
  TraceContext context{caller};
  std::vector<Inlinable> inlinables;
  {
    auto timer = m_inline_callees_timer.scope();

    always_assert(caller->get_code()->cfg_built());
    auto& cfg = caller->get_code()->cfg();
    for (auto* block : cfg.blocks()) {
      auto ii = InstructionIterable(block);
      // walk the caller opcodes collecting all candidates to inline
      // Build a callee to opcode map
      for (auto it = ii.begin(); it != ii.end(); ++it) {
        auto* insn = it->insn;
        auto callee_opt = get_callee(caller, insn);
        if (!callee_opt) {
          continue;
        }
        auto* callee = *callee_opt;
        if (callees.count(callee) == 0u) {
          continue;
        }
        std::shared_ptr<ReducedCode> reduced_code;
        bool no_return{false};
        bool partial{false};
        bool for_speed{false};
        size_t insn_size{0};
        PartialCode partial_code;
        if (filter_via_should_inline) {
          auto timer2 = m_inline_callees_should_inline_timer.scope();
          // Cost model is based on fully inlining callee everywhere; let's
          // see if we can get more detailed call-site specific information
          if (should_inline_at_call_site(caller, block, insn, callee,
                                         &no_return, &for_speed, &reduced_code,
                                         &insn_size, &partial_code)) {
            always_assert(!no_return);
            // Yes, we know might have dead_blocks and a refined insn_size
          } else if (should_inline_always(callee)) {
            // We'll fully inline the callee without any adjustments
            no_return = false;
            reduced_code = nullptr;
            insn_size = get_callee_insn_size(callee);
          } else if (should_partially_inline(block, insn, callee,
                                             &partial_code)) {
            partial = true;
            reduced_code = partial_code.reduced_code;
            insn_size = partial_code.insn_size;
          } else if (no_return) {
            always_assert(insn_size == 0);
            always_assert(!reduced_code);
          } else {
            continue;
          }
        } else {
          insn_size = get_callee_insn_size(callee);
        }
        always_assert(callee->is_concrete());
        if (m_analyze_and_prune_inits && method::is_init(callee) &&
            !no_return) {
          auto timer2 = m_inline_callees_init_timer.scope();
          if (!callee->get_code()->cfg_built()) {
            continue;
          }
          if (!can_inline_init(callee)) {
            if (!method::is_init(caller) ||
                caller->get_class() != callee->get_class() ||
                !caller->get_code()->cfg_built() ||
                !constructor_analysis::can_inline_inits_in_same_class(
                    caller, callee, insn)) {
              continue;
            }
          }
        }

        const auto* needs_receiver_cast = get_recorded_receiver_cast(insn);
        inlinables.push_back((Inlinable){callee, insn, no_return, partial,
                                         for_speed, std::move(reduced_code),
                                         insn_size, needs_receiver_cast});
      }
    }
  }
  if (!inlinables.empty()) {
    inline_inlinables(caller, inlinables);
  }
}

size_t MultiMethodInliner::inline_callees(
    DexMethod* caller, const UnorderedSet<IRInstruction*>& insns) {
  TraceContext context{caller};
  std::vector<Inlinable> inlinables;
  always_assert(caller->get_code()->cfg_built());
  for (auto& mie : InstructionIterable(caller->get_code()->cfg())) {
    auto* insn = mie.insn;
    if (insns.count(insn) != 0u) {
      auto callee_opt = get_callee(caller, insn);
      if (!callee_opt) {
        continue;
      }
      auto* callee = *callee_opt;
      always_assert(callee->is_concrete());
      const auto* needs_receiver_cast = get_recorded_receiver_cast(insn);
      inlinables.push_back((Inlinable){callee, insn, false, false, false,
                                       nullptr, get_callee_insn_size(callee),
                                       needs_receiver_cast});
    }
  }

  return inline_inlinables(caller, inlinables);
}

size_t MultiMethodInliner::inline_callees(
    DexMethod* caller, const UnorderedMap<IRInstruction*, DexMethod*>& insns) {
  TraceContext context{caller};
  std::vector<Inlinable> inlinables;
  always_assert(caller->get_code()->cfg_built());
  for (auto& mie : InstructionIterable(caller->get_code()->cfg())) {
    auto* insn = mie.insn;
    auto it = insns.find(insn);
    if (it == insns.end()) {
      continue;
    }
    auto* callee = it->second;
    always_assert(callee->is_concrete());
    always_assert(opcode::is_an_invoke(insn->opcode()));
    const auto* needs_receiver_cast = get_needs_receiver_cast(insn, callee);
    inlinables.push_back((Inlinable){callee, insn, false, false, false, nullptr,
                                     get_callee_insn_size(callee),
                                     needs_receiver_cast});
  }

  return inline_inlinables(caller, inlinables);
}

namespace {

// Helper method, as computing inline for a trace could be too expensive.
std::string create_inlining_trace_msg(const DexMethod* caller,
                                      const DexMethod* callee,
                                      IRInstruction* invoke_insn) {
  std::ostringstream oss;
  oss << "inline " << show(callee) << " into " << show(caller) << " ";
  auto features = [&oss](const DexMethod* m, IRInstruction* insn) {
    const auto* code = m->get_code();
    auto regs = code->cfg_built() ? code->cfg().get_registers_size()
                                  : code->get_registers_size();
    auto opcodes = code->count_opcodes();
    auto blocks = code->cfg_built() ? code->cfg().num_blocks() : (size_t)0;
    auto edges = code->cfg_built() ? code->cfg().num_edges() : (size_t)0;

    oss << regs << "!" << opcodes << "!" << blocks << "!" << edges;

    // Expensive...
    if (code->cfg_built()) {
      loop_impl::LoopInfo info(code->cfg());
      oss << "!" << info.num_loops();
      size_t max_depth{0};
      for (auto& loop : info) {
        max_depth = std::max(max_depth, (size_t)loop.get_loop_depth());
      }
      oss << "!" << max_depth;
      if (insn != nullptr) {
        auto it = code->cfg().find_insn(insn);
        loop_impl::Loop* loop{nullptr};
        if (!it.is_end()) {
          loop = info.get_loop_for(it.block());
        }
        if (loop != nullptr) {
          oss << "!" << loop->get_loop_depth();
        } else {
          oss << "!" << 0;
        }
      } else {
        oss << "!" << 0;
      }
    } else {
      oss << "!0!0!0";
    }
  };
  features(caller, invoke_insn);
  oss << "!";
  features(callee, nullptr);
  return oss.str();
}

} // namespace

void MultiMethodInliner::make_partial(const DexMethod* method,
                                      InlinedCost* inlined_cost) {
  if (m_config.partial_hot_hot_inline &&
      (m_hot_methods.count_unsafe(method) != 0u) &&
      inlined_cost->reduced_code) {
    inlined_cost->partial_code = inliner::get_partially_inlined_code(
        method, inlined_cost->reduced_code->cfg(),
        m_config.max_partially_inlined_code_units);
  }
  inlined_cost->reduced_code.reset();
  // `insn_size` was measured on the reduced cfg. Without that cfg the *full*
  // callee body is what gets copied into the caller, so keeping the reduced
  // number would make `inline_inlinables` under-charge `estimated_caller_size`
  // and under-state the size passed to `is_inlinable`.
  inlined_cost->insn_size = get_callee_insn_size(method);
}

const DexType* MultiMethodInliner::get_needs_init_class(
    DexMethod* callee) const {
  if (!is_static(callee) || assumenosideeffects(callee)) {
    return nullptr;
  }
  auto* insn =
      m_shrinker.get_init_classes_with_side_effects().create_init_class_insn(
          callee->get_class());
  if (insn == nullptr) {
    return nullptr;
  }
  const auto* type = insn->get_type();
  delete insn;
  return type;
}

bool MultiMethodInliner::get_needs_constructor_fence(
    const DexMethod* caller, const DexMethod* callee) const {
  if (!method::is_init(callee)) {
    return false;
  }
  if (caller != nullptr && method::is_init(caller) &&
      caller->get_class() == callee->get_class()) {
    return false;
  }
  if ((m_unfinalized_init_methods != nullptr) &&
      (m_unfinalized_init_methods->count(callee) != 0u)) {
    return true;
  }
  return m_unfinalized_overloads.count(callee) != 0u;
}

size_t MultiMethodInliner::inline_inlinables(
    DexMethod* caller_method, const std::vector<Inlinable>& inlinables) {
  auto timer = m_inline_inlinables_timer.scope();
  auto* caller = caller_method->get_code();
  always_assert(caller->cfg_built());

  // attempt to inline all inlinable candidates
  size_t estimated_caller_size = caller->cfg().estimate_code_units();

  // Prefer inlining smaller methods first, so that we are less likely to hit
  // overall size limit.
  std::vector<Inlinable> ordered_inlinables(inlinables.begin(),
                                            inlinables.end());

  const auto* preferred_methods = get_preferred_methods();
  if (preferred_methods != nullptr &&
      preferred_methods->count_unsafe(caller_method) != 0u) {
    preferred_methods = nullptr;
  }

  std::stable_sort(
      ordered_inlinables.begin(),
      ordered_inlinables.end(),
      [&](const Inlinable& a, const Inlinable& b) {
        // First, prefer no-return inlinable, as they cut off
        // control-flow and thus other inlinables.
        if (a.no_return != b.no_return) {
          return static_cast<int>(a.no_return) > static_cast<int>(b.no_return);
        }
        // Second, prefer inlining callees that preserve integrity of the global
        // cost function. Partial inlines and inlines for speed may not preserve
        // this.
        if (a.partial != b.partial) {
          return static_cast<int>(a.partial) < static_cast<int>(b.partial);
        }
        if (a.for_speed != b.for_speed) {
          return static_cast<int>(a.for_speed) < static_cast<int>(b.for_speed);
        }
        // Third, if appropriate, prefer inlining not-cold / maybe-hot callees
        if (preferred_methods != nullptr) {
          auto a_not_cold = preferred_methods->count_unsafe(a.callee);
          auto b_not_cold = preferred_methods->count_unsafe(b.callee);
          if (a_not_cold != b_not_cold) {
            return a_not_cold > b_not_cold;
          }
        }
        // Fourth, prefer smaller methods, to avoid hitting size
        // limits too soon
        return a.insn_size < b.insn_size;
      });

  std::vector<DexMethod*> inlined_callees;
  std::optional<reg_t> cfg_next_caller_reg;
  if (!m_config.unique_inlined_registers) {
    cfg_next_caller_reg = caller->cfg().get_registers_size();
  }
  size_t calls_not_inlinable{0}, calls_not_inlined{0}, no_returns{0},
      unreachable_insns{0}, caller_too_large{0},
      calls_not_inlined_with_perf_sensitive_constructors{0};

  size_t intermediate_shrinkings{0};
  size_t intermediate_remove_unreachable_blocks{0};
  // We only try intermediate remove-unreachable-blocks or shrinking when using
  // the cfg-inliner, as it will invalidate irlist iterators, which are used
  // with the legacy non-cfg-inliner.
  size_t last_intermediate_inlined_callees{0};

  // Once blocks might have been freed, which can happen via
  // remove_unreachable_blocks and shrinking, callsite pointers are no longer
  // valid.
  std::unique_ptr<UnorderedSet<const IRInstruction*>> remaining_callsites;
  auto recompute_remaining_callsites = [caller, &remaining_callsites,
                                        &ordered_inlinables]() {
    if (!remaining_callsites) {
      remaining_callsites =
          std::make_unique<UnorderedSet<const IRInstruction*>>();
      for (const auto& inlinable : ordered_inlinables) {
        remaining_callsites->insert(inlinable.insn);
      }
    }
    UnorderedSet<const IRInstruction*> new_remaining_callsites;
    for (auto& mie : InstructionIterable(caller->cfg())) {
      if (mie.insn->has_method() &&
          (remaining_callsites->count(mie.insn) != 0u)) {
        new_remaining_callsites.insert(mie.insn);
      }
    }
    always_assert(new_remaining_callsites.size() <=
                  remaining_callsites->size());
    *remaining_callsites = std::move(new_remaining_callsites);
  };

  VisibilityChanges visibility_changes;
  UnorderedSet<DexMethod*> visibility_changes_for;
  size_t init_classes = 0;
  size_t constructor_fences = 0;
  for (const auto& inlinable : ordered_inlinables) {
    auto* callee_method = inlinable.callee;
    const auto& reduced_code = inlinable.reduced_code;
    const auto* reduced_cfg = reduced_code ? &reduced_code->cfg() : nullptr;
    auto* callsite_insn = inlinable.insn;

    if (remaining_callsites &&
        (remaining_callsites->count(callsite_insn) == 0u)) {
      if (!inlinable.no_return) {
        calls_not_inlined++;
      }
      continue;
    }

    if (inlinable.no_return) {
      if (!m_config.throw_after_no_return ||
          caller_method->rstate.no_optimizations()) {
        continue;
      }
      // we are not actually inlining, but just cutting off control-flow
      // afterwards, inserting an (unreachable) "throw null" instruction
      // sequence.
      auto& caller_cfg = caller->cfg();
      auto callsite_it = caller_cfg.find_insn(callsite_insn);
      if (!callsite_it.is_end()) {
        if (m_config.unique_inlined_registers) {
          cfg_next_caller_reg = caller_cfg.get_registers_size();
        }
        auto temp_reg = *cfg_next_caller_reg;
        if (temp_reg >= caller_cfg.get_registers_size()) {
          caller_cfg.set_registers_size(temp_reg + 1);
        }
        // Copying to avoid cfg limitation
        auto* callsite_copy = new IRInstruction(*callsite_it->insn);
        auto* unreachable_insn =
            (new IRInstruction(IOPCODE_UNREACHABLE))->set_dest(temp_reg);
        auto* throw_insn =
            (new IRInstruction(OPCODE_THROW))->set_src(0, temp_reg);
        caller_cfg.replace_insns(callsite_it,
                                 {callsite_copy, unreachable_insn, throw_insn});
        auto p = caller_cfg.remove_unreachable_blocks();
        auto unreachable_insn_count = p.first;
        auto registers_size_possibly_reduced = p.second;
        if (registers_size_possibly_reduced &&
            m_config.unique_inlined_registers) {
          caller_cfg.recompute_registers_size();
          cfg_next_caller_reg = caller_cfg.get_registers_size();
        }
        if (unreachable_insn_count != 0u) {
          unreachable_insns += unreachable_insn_count;
          recompute_remaining_callsites();
        }
        estimated_caller_size = caller_cfg.estimate_code_units();
        no_returns++;
      }
      continue;
    }

    if (for_speed()) {
      // This is expensive, but with shrinking/non-cfg inlining prep there's no
      // better way. Needs an explicit check to see whether the instruction has
      // already been shrunk away.
      auto callsite_it = caller->cfg().find_insn(callsite_insn);
      if (!callsite_it.is_end()) {
        auto* block = callsite_it.block();
        if (!m_inline_for_speed->should_inline_callsite(caller_method,
                                                        callee_method, block)) {
          calls_not_inlinable++;
          continue;
        }
      }
    }

    bool caller_too_large_;
    auto not_inlinable = !is_inlinable(
        caller_method, callee_method, reduced_cfg, callsite_insn,
        estimated_caller_size, inlinable.insn_size, &caller_too_large_);
    if (not_inlinable && caller_too_large_ &&
        inlined_callees.size() > last_intermediate_inlined_callees) {
      intermediate_remove_unreachable_blocks++;
      last_intermediate_inlined_callees = inlined_callees.size();
      auto p = caller->cfg().remove_unreachable_blocks();
      unreachable_insns += p.first;
      auto registers_size_possibly_reduced = p.second;
      if (registers_size_possibly_reduced &&
          m_config.unique_inlined_registers) {
        caller->cfg().recompute_registers_size();
        cfg_next_caller_reg = caller->cfg().get_registers_size();
      }
      estimated_caller_size = caller->cfg().estimate_code_units();
      recompute_remaining_callsites();
      if (remaining_callsites->count(callsite_insn) == 0u) {
        calls_not_inlined++;
        continue;
      }
      not_inlinable = !is_inlinable(caller_method, callee_method, reduced_cfg,
                                    callsite_insn, estimated_caller_size,
                                    inlinable.insn_size, &caller_too_large_);
      if (!not_inlinable && m_config.intermediate_shrinking &&
          m_shrinker.enabled() && !caller_method->rstate.no_optimizations()) {
        intermediate_shrinkings++;
        m_shrinker.shrink_method(caller_method);
        cfg_next_caller_reg = caller->cfg().get_registers_size();
        estimated_caller_size = caller->cfg().estimate_code_units();
        recompute_remaining_callsites();
        if (remaining_callsites->count(callsite_insn) == 0u) {
          calls_not_inlined++;
          continue;
        }
        not_inlinable = !is_inlinable(caller_method, callee_method, reduced_cfg,
                                      callsite_insn, estimated_caller_size,
                                      inlinable.insn_size, &caller_too_large_);
      }
    }
    if (not_inlinable) {
      if (caller_too_large_) {
        caller_too_large++;
      } else {
        calls_not_inlinable++;
      }
      continue;
    }

    TRACE(MMINL, 4, "%s",
          create_inlining_trace_msg(caller_method, callee_method, callsite_insn)
              .c_str());

    if (m_config.unique_inlined_registers) {
      cfg_next_caller_reg = caller->cfg().get_registers_size();
    }
    auto timer2 = m_inline_with_cfg_timer.scope();
    const auto* needs_init_class = get_needs_init_class(callee_method);
    auto needs_constructor_fence =
        get_needs_constructor_fence(caller_method, callee_method);
    auto callee_has_constructor_fence =
        m_config.unfinalize_relaxed_init_inline &&
        (m_methods_with_write_barrier != nullptr) &&
        m_methods_with_write_barrier->count(callee_method) > 0;
    if (needs_constructor_fence || callee_has_constructor_fence) {
      if ((m_config.unfinalize_perf_mode ==
               inliner::UnfinalizePerfMode::NOT_COLD &&
           source_blocks::method_is_not_cold(caller_method)) ||
          (m_config.unfinalize_perf_mode ==
               inliner::UnfinalizePerfMode::MAYBE_HOT &&
           source_blocks::method_maybe_hot(caller_method)) ||
          (m_config.unfinalize_perf_mode == inliner::UnfinalizePerfMode::HOT &&
           source_blocks::method_is_hot(caller_method))) {
        calls_not_inlined_with_perf_sensitive_constructors++;
        continue;
      }
    }
    bool success = inliner::inline_with_cfg(
        caller_method, callee_method, callsite_insn,
        inlinable.needs_receiver_cast, needs_init_class, *cfg_next_caller_reg,
        reduced_cfg, m_config.rewrite_invoke_super ? callee_method : nullptr,
        needs_constructor_fence);
    if (!success) {
      calls_not_inlined++;
      continue;
    }
    TRACE(INL, 2, "caller: %s\tcallee: %s",
          caller->cfg_built() ? SHOW(caller->cfg()) : SHOW(caller),
          SHOW(reduced_cfg ? *reduced_cfg : callee_method->get_code()->cfg()));
    estimated_caller_size += inlinable.insn_size;
    if (reduced_cfg != nullptr) {
      visibility_changes.insert(get_visibility_changes(
          *reduced_cfg, caller_method->get_class(), callee_method));
    } else {
      visibility_changes_for.insert(callee_method);
    }
    if (needs_init_class != nullptr) {
      init_classes++;
    }
    if (needs_constructor_fence) {
      const DexMethod* m = callee_method;
      m_inlined_with_fence.insert(m);
      while (const auto* ptr = m_unfinalized_overloads.get(m)) {
        m = *ptr;
        m_inlined_with_fence.insert(m);
      }
      constructor_fences++;
      if (m_methods_with_write_barrier != nullptr) {
        m_methods_with_write_barrier->insert(caller_method);
      }
    } else {
      if (callee_has_constructor_fence) {
        m_methods_with_write_barrier->insert(caller_method);
      }
      if (get_needs_constructor_fence(/* caller */ nullptr, callee_method)) {
        // Inlining callee in any other context would need a constructor fence;
        // that means that final fields are involved, and we just didn't need a
        // constructor fence here because we inlined into an init overload.
        // Record this.
        always_assert(method::is_init(caller_method));
        always_assert(method::is_init(callee_method));
        always_assert(caller_method->get_class() == callee_method->get_class());
        m_unfinalized_overloads.emplace(caller_method, callee_method);
      }
    }

    inlined_callees.push_back(callee_method);
    if (type::is_kotlin_lambda(type_class(callee_method->get_class()))) {
      info.kotlin_lambda_inlined++;
    }
    if (inlinable.partial) {
      info.partially_inlined++;
      info.partially_inlined_callees.fetch_add(callee_method, 1);
    }
  }

  if (!inlined_callees.empty()) {
    for (auto* callee_method : UnorderedIterable(visibility_changes_for)) {
      visibility_changes.insert(
          get_visibility_changes(callee_method, caller_method->get_class()));
    }
    if (!visibility_changes.empty()) {
      std::lock_guard<std::mutex> guard(m_visibility_changes_mutex);
      if (m_delayed_visibility_changes) {
        m_delayed_visibility_changes->insert(visibility_changes);
      } else {
        visibility_changes_apply_and_record_make_static(visibility_changes);
      }
    }
    m_inlined.insert(inlined_callees.begin(), inlined_callees.end());
  }

  info.calls_inlined += inlined_callees.size();
  if (calls_not_inlinable != 0u) {
    info.calls_not_inlinable += calls_not_inlinable;
  }
  if (calls_not_inlined != 0u) {
    info.calls_not_inlined += calls_not_inlined;
  }
  if (calls_not_inlined_with_perf_sensitive_constructors != 0u) {
    info.calls_not_inlined_with_perf_sensitive_constructors +=
        calls_not_inlined_with_perf_sensitive_constructors;
  }
  if (no_returns != 0u) {
    info.no_returns += no_returns;
  }
  if (unreachable_insns != 0u) {
    info.unreachable_insns += unreachable_insns;
  }
  if (intermediate_shrinkings != 0u) {
    info.intermediate_shrinkings += intermediate_shrinkings;
  }
  if (intermediate_remove_unreachable_blocks != 0u) {
    info.intermediate_remove_unreachable_blocks +=
        intermediate_remove_unreachable_blocks;
  }
  if (caller_too_large != 0u) {
    info.caller_too_large += caller_too_large;
    caller_method->rstate.set_too_large_for_inlining_into();
  }
  if (init_classes != 0u) {
    info.init_classes += init_classes;
  }
  if (constructor_fences != 0u) {
    info.constructor_fences += constructor_fences;
  }
  return inlined_callees.size();
}

void MultiMethodInliner::postprocess_method(DexMethod* method) {
  TraceContext context(method);
  if (m_shrinker.enabled() && !method->rstate.no_optimizations()) {
    m_shrinker.shrink_method(method);
  }

  // Release some memory that is no longer needed as the method has been
  // processed as a caller
  {
    auto it = m_caller_virtual_callees.find(method);
    if (it != m_caller_virtual_callees.end()) {
      it->second = decltype(it->second)();
    }
  }
  {
    auto it = m_caller_callee.find(method);
    if (it != m_caller_callee.end()) {
      it->second = decltype(it->second)();
    }
  }

  bool is_callee = !(m_callee_caller.count_unsafe(method) == 0u);
  if (!is_callee) {
    // This method isn't the callee of another caller, so we can stop here.
    return;
  }

  compute_callee_costs(method);
}

void MultiMethodInliner::compute_callee_costs(DexMethod* method) {
  const auto* fully_inlined_cost = get_fully_inlined_cost(method);
  always_assert(fully_inlined_cost);

  const auto* callee_call_site_invokes =
      m_call_site_summarizer
          ? m_call_site_summarizer->get_callee_call_site_invokes(method)
          : nullptr;
  if (callee_call_site_invokes != nullptr) {
    UnorderedMap<const CallSiteSummary*, std::vector<const IRInstruction*>>
        invokes;
    for (const auto* invoke_insn : *callee_call_site_invokes) {
      const auto* call_site_summary =
          m_call_site_summarizer->get_instruction_call_site_summary(
              invoke_insn);
      always_assert(call_site_summary != nullptr);
      invokes[call_site_summary].push_back(invoke_insn);
    }
    for (auto& p : UnorderedIterable(invokes)) {
      m_scheduler.augment(method, [this, call_site_summary = p.first,
                                   insns = std::move(p.second), method]() {
        TraceContext context(method);
        // Populate caches
        auto timer = m_call_site_inlined_cost_timer.scope();
        bool keep_reduced_code = false;
        for (const auto* insn : insns) {
          if (should_inline_at_call_site(nullptr, nullptr, insn, method)) {
            keep_reduced_code = true;
          }
        }
        if (!keep_reduced_code) {
          CalleeCallSiteSummary key{method, call_site_summary};
          const auto* cached = m_call_site_inlined_costs.get(key);
          if (cached != nullptr) {
            make_partial(method, const_cast<InlinedCost*>(cached));
          }
        }
      });
    }
  }

  m_scheduler.augment(method, [this, method]() {
    // Populate caches
    get_callee_insn_size(method);
    get_callee_type_refs(method, /* reduced_cfg */ nullptr);
    if (m_ref_checkers) {
      get_callee_code_refs(method, /* reduced_cfg */ nullptr);
    }
    if (m_callee_x_dex_refs) {
      get_callee_x_dex_refs(method, /* reduced_cfg */ nullptr);
    }
  });

  // The should_inline_always caching depends on all other caches, so we augment
  // it as a "continuation".
  m_scheduler.augment(
      method,
      [this, method] {
        TraceContext context(method);
        // Populate cache
        should_inline_always(method);
      },
      /* continuation */ true);
}

std::string MultiMethodInliner::InlinableDecision::to_str() const {
  switch (decision) {
  case InlinableDecision::Decision::kInlinable:
    return "inlinable";
  case InlinableDecision::Decision::kCallerNoOpt:
    return "not-inlinable-caller-no-opt";
  case InlinableDecision::Decision::kCrossStore:
    return "not-inlinable-cross-store";
  case InlinableDecision::Decision::kCrossDexRef:
    return "not-inlinable-cross-dex-ref";
  case InlinableDecision::Decision::kHotCold:
    return "not-inlinable-hot-cold";
  case InlinableDecision::Decision::kBlocklisted:
    return "not-inlinable-blocklisted";
  case InlinableDecision::Decision::kExternalCatch:
    return "not-inlinable-external-catch";
  case InlinableDecision::Decision::kUninlinableOpcodes:
    return "not-inlinable-uninlinable-opcodes";
  case InlinableDecision::Decision::kApiMismatch:
    return "not-inlinable-api-mismatch";
  case InlinableDecision::Decision::kCalleeDontInline:
    return "not-inlinable-callee-dont-inline";
  case InlinableDecision::Decision::kCallerTooLarge:
    return "not-inlinable-caller-too-large";
  case InlinableDecision::Decision::kProblematicRefs:
    return "not-inlinable-problematic-refs";
  }
  not_reached();
}

/**
 * Defines the set of rules that determine whether a function is inlinable.
 */
MultiMethodInliner::InlinableDecision MultiMethodInliner::is_inlinable(
    const DexMethod* caller,
    const DexMethod* callee,
    const cfg::ControlFlowGraph* reduced_cfg,
    const IRInstruction* insn,
    uint64_t estimated_caller_size,
    uint64_t estimated_callee_size,
    bool* caller_too_large_) {
  TraceContext context{caller};
  if (caller_too_large_ != nullptr) {
    *caller_too_large_ = false;
  }
  if (caller->rstate.no_optimizations()) {
    return InlinableDecision(InlinableDecision::Decision::kCallerNoOpt);
  }
  // don't inline cross store references
  if (cross_store_reference(caller, callee, reduced_cfg)) {
    if (insn != nullptr) {
      log_nopt(INL_CROSS_STORE_REFS, caller, insn);
    }
    return InlinableDecision(InlinableDecision::Decision::kCrossStore);
  }
  if (cross_dex_reference(caller, callee, reduced_cfg)) {
    return InlinableDecision(InlinableDecision::Decision::kCrossDexRef);
  }
  if (cross_hot_cold(caller, callee, estimated_callee_size)) {
    return InlinableDecision(InlinableDecision::Decision::kHotCold);
  }
  if (is_blocklisted(callee)) {
    if (insn != nullptr) {
      log_nopt(INL_BLOCK_LISTED_CALLEE, callee);
    }
    return InlinableDecision(InlinableDecision::Decision::kBlocklisted);
  }
  if (caller_is_blocklisted(caller)) {
    if (insn != nullptr) {
      log_nopt(INL_BLOCK_LISTED_CALLER, caller);
    }
    return InlinableDecision(InlinableDecision::Decision::kBlocklisted);
  }
  if (has_external_catch(callee, reduced_cfg)) {
    if (insn != nullptr) {
      log_nopt(INL_EXTERN_CATCH, callee);
    }
    return InlinableDecision(InlinableDecision::Decision::kExternalCatch);
  }
  if (cannot_inline_opcodes(caller, callee, reduced_cfg, insn)) {
    return InlinableDecision(InlinableDecision::Decision::kUninlinableOpcodes);
  }
  auto caller_too_large_decision = [&]() {
    if (insn != nullptr) {
      log_nopt(INL_TOO_BIG, caller, insn);
    }
    if (caller_too_large_ != nullptr) {
      *caller_too_large_ = true;
    }
    return InlinableDecision(InlinableDecision::Decision::kCallerTooLarge);
  };

  if (m_config.is_over_armv7_hard_max_instruction_size(estimated_caller_size,
                                                       estimated_callee_size)) {
    return caller_too_large_decision();
  }

  if (!callee->rstate.force_inline()) {
    // Don't inline code into a method that doesn't have the same (or higher)
    // required API. We don't want to bring API specific code into a class
    // where it's not supported.
    int32_t callee_api = api::LevelChecker::get_method_level(callee);
    if (callee_api != api::LevelChecker::get_min_level() &&
        callee_api > api::LevelChecker::get_method_level(caller)) {
      // check callee_api against the minimum and short-circuit because most
      // methods don't have a required api and we want that to be fast.
      if (insn != nullptr) {
        log_nopt(INL_REQUIRES_API, caller, insn);
      }
      TRACE(MMINL, 4,
            "Refusing to inline %s"
            "              into %s\n because of API boundaries.",
            show_deobfuscated(callee).c_str(),
            show_deobfuscated(caller).c_str());
      info.api_level_mismatch++;
      return InlinableDecision(InlinableDecision::Decision::kApiMismatch);
    }

    if (callee->rstate.dont_inline()) {
      if (insn != nullptr) {
        log_nopt(INL_DO_NOT_INLINE, caller, insn);
      }
      return InlinableDecision(InlinableDecision::Decision::kCalleeDontInline);
    }

    if (caller_too_large(caller->get_class(), estimated_caller_size,
                         estimated_callee_size)) {
      return caller_too_large_decision();
    }

    if (caller->get_class() != callee->get_class() && m_ref_checkers &&
        problematic_refs(caller, callee, reduced_cfg)) {
      return InlinableDecision(InlinableDecision::Decision::kProblematicRefs);
    }
  }

  return InlinableDecision(InlinableDecision::Decision::kInlinable);
}

/**
 * Return whether the method or any of its ancestors are in the blocklist.
 * Typically used to prevent inlining / deletion of methods that are called
 * via reflection.
 */
bool MultiMethodInliner::is_blocklisted(const DexMethod* callee) {
  auto* cls = type_class(callee->get_class());
  // Enums' kept methods are all excluded.
  if (is_enum(cls) && root(callee)) {
    return true;
  }
  while (cls != nullptr) {
    if (m_config.get_blocklist().count(cls->get_type()) != 0u) {
      info.blocklisted++;
      return true;
    }
    cls = type_class(cls->get_super_class());
  }
  return false;
}

bool MultiMethodInliner::is_estimate_over_max(uint64_t estimated_caller_size,
                                              uint64_t estimated_callee_size,
                                              uint64_t max) {
  // INSTRUCTION_BUFFER is added because the final method size is often larger
  // than our estimate -- during the sync phase, we may have to pick larger
  // branch opcodes to encode large jumps.
  return estimated_caller_size + estimated_callee_size >
         max - std::min(m_config.instruction_size_buffer, max);
}

bool MultiMethodInliner::caller_too_large(DexType* /*caller_type*/,
                                          uint64_t estimated_caller_size,
                                          uint64_t estimated_callee_size) {
  if (is_estimate_over_max(estimated_caller_size, estimated_callee_size,
                           HARD_MAX_INSTRUCTION_SIZE)) {
    return true;
  }

  if (!m_config.enforce_method_size_limit) {
    return false;
  }

  if (is_estimate_over_max(estimated_caller_size, estimated_callee_size,
                           m_config.soft_max_instruction_size)) {
    return true;
  }

  return false;
}

bool MultiMethodInliner::should_inline_fast(const DexMethod* callee) {
  if (for_speed()) {
    // inline_for_speed::should_inline was used earlier to prune the static
    // call-graph
    return true;
  }

  if (callee->rstate.force_inline()) {
    return true;
  }

  // non-root methods that are only ever called once should always be inlined,
  // as the method can be removed afterwards
  const auto& callers = m_callee_caller.at_unsafe(callee);
  return callers.size() == 1 && unordered_any(callers)->second == 1 &&
         !root(callee) && !method::is_argless_init(callee) &&
         (m_recursive_callees.count(callee) == 0u) &&
         (m_true_virtual_callees_with_other_call_sites.count(callee) == 0u) &&
         !cross_hot_cold(unordered_any(callers)->first, callee);
}

bool MultiMethodInliner::should_inline_always(const DexMethod* callee) {
  if (m_local_only) {
    return false;
  }

  if (should_inline_fast(callee)) {
    return true;
  }

  return *m_should_inline
              .get_or_create_and_assert_equal(
                  callee,
                  [&](const auto&) {
                    always_assert(!for_speed());
                    always_assert(!callee->rstate.force_inline());
                    if (too_many_callers(callee)) {
                      log_nopt(INL_TOO_MANY_CALLERS, callee);
                      return false;
                    }
                    return true;
                  })
              .first;
}

PartialCode MultiMethodInliner::get_callee_partial_code(
    const DexMethod* callee) {
  if (!m_config.partial_hot_hot_inline) {
    return PartialCode();
  }
  if (!m_callee_partial_code) {
    return inliner::get_partially_inlined_code(
        callee, callee->get_code()->cfg(),
        m_config.max_partially_inlined_code_units);
  }
  return *m_callee_partial_code
              ->get_or_create_and_assert_equal(
                  callee,
                  [&](const auto&) {
                    return inliner::get_partially_inlined_code(
                        callee, callee->get_code()->cfg(),
                        m_config.max_partially_inlined_code_units);
                  })
              .first;
}

size_t MultiMethodInliner::get_callee_insn_size(const DexMethod* callee) {
  if (m_callee_insn_sizes) {
    const auto* res = m_callee_insn_sizes->get(callee);
    if (res != nullptr) {
      return *res;
    }
  }

  const IRCode* code = callee->get_code();
  auto size = code->estimate_code_units();
  if (m_callee_insn_sizes) {
    m_callee_insn_sizes->emplace(callee, size);
  }
  return size;
}

/*
 * Estimate additional costs if an instruction takes many source registers.
 */
static size_t get_inlined_regs_cost(size_t regs,
                                    const InlinerCostConfig& cost_config) {
  size_t cost{0};
  if (regs > cost_config.reg_threshold_1) {
    if (regs > cost_config.reg_threshold_1 + cost_config.reg_threshold_2) {
      // invoke with many args will likely need extra moves
      cost += regs;
    } else {
      cost += regs / 2;
    }
  }
  return cost;
}

static float get_invoke_cost(const InlinerCostConfig& cost_config,
                             const DexMethod* callee,
                             float result_used) {
  float invoke_cost =
      cost_config.cost_invoke + result_used * cost_config.cost_move_result;
  invoke_cost += static_cast<float>(get_inlined_regs_cost(
      callee->get_proto()->get_args()->size(), cost_config));
  return invoke_cost;
}

/*
 * Try to estimate number of code units (2 bytes each) of an instruction.
 * - Ignore internal opcodes because they do not take up any space in the
 * final dex file.
 * - Ignore move opcodes with the hope that RegAlloc will eliminate most of
 *   them.
 * - Remove return opcodes, as they will disappear when gluing things
 * together.
 */
static size_t get_inlined_cost(IRInstruction* insn,
                               const InlinerCostConfig& cost_config) {
  auto op = insn->opcode();
  size_t cost{0};
  if (opcode::is_an_internal(op) || opcode::is_a_move(op) ||
      opcode::is_a_return(op)) {
    if (op == IOPCODE_INIT_CLASS) {
      cost += cost_config.op_init_class_cost;
    } else if (op == IOPCODE_INJECTION_ID) {
      cost += cost_config.op_injection_id_cost;
    } else if (op == IOPCODE_UNREACHABLE) {
      cost += cost_config.op_unreachable_cost;
    } else if (op == IOPCODE_WRITE_BARRIER) {
      cost += static_cast<size_t>(cost_config.cost_invoke);
    } else if (op == IOPCODE_R_CONST) {
      // A resource ID is always in [0x01000000, 0x7FFFFFFF]
      cost += 1 + cost_config.insn_has_lit_cost_2;
    }
  } else {
    cost++;
    auto regs = insn->srcs_size() +
                ((insn->has_dest() || insn->has_move_result_pseudo()) ? 1 : 0);
    cost += get_inlined_regs_cost(regs, cost_config);
    if (op == OPCODE_MOVE_EXCEPTION) {
      cost += cost_config.op_move_exception_cost; // accounting for book-keeping
                                                  // overhead of throw-blocks
    } else if (insn->has_method() || insn->has_field() || insn->has_type() ||
               insn->has_string()) {
      cost += cost_config.insn_cost_1;
    } else if (insn->has_data()) {
      cost += cost_config.insn_has_data_cost + insn->get_data()->size();
    } else if (insn->has_literal()) {
      auto lit = insn->get_literal();
      if (lit < -2147483648 || lit > 2147483647) {
        cost += cost_config.insn_has_lit_cost_1;
      } else if (lit < -32768 || lit > 32767) {
        cost += cost_config.insn_has_lit_cost_2;
      } else if ((opcode::is_a_const(op) && (lit < -8 || lit > 7)) ||
                 (!opcode::is_a_const(op) && (lit < -128 || lit > 127))) {
        cost += cost_config.insn_has_lit_cost_3;
      }
    }
  }
  TRACE(INLINE, 5, "  %zu: %s", cost, SHOW(insn));
  return cost;
}

/*
 * Try to estimate number of code units (2 bytes each) overhead (instructions,
 * metadata) that exists for this block; this doesn't include the cost of
 * the instructions in the block, which are accounted for elsewhere.
 */
static size_t get_inlined_cost(const std::vector<cfg::Block*>& blocks,
                               size_t index,
                               const cfg::CompactEdgeVector& succs) {
  auto* block = blocks.at(index);
  switch (block->branchingness()) {
  case opcode::Branchingness::BRANCH_GOTO:
  case opcode::Branchingness::BRANCH_IF:
  case opcode::Branchingness::BRANCH_SWITCH: {
    if (succs.empty()) {
      return 0;
    }
    if (succs.size() > 2) {
      // a switch
      return 4 + 3 * succs.size();
    }
    // a (possibly conditional) branch; each feasible non-fallthrough edge has a
    // cost
    size_t cost{0};
    auto* next_block =
        index == blocks.size() - 1 ? nullptr : blocks.at(index + 1);
    for (auto* succ : succs) {
      always_assert(succ->target() != nullptr);
      if (next_block != succ->target()) {
        // we have a non-fallthrough edge
        cost++;
      }
    }
    return cost;
  }
  default:
    return 0;
  }
}

std::shared_ptr<ReducedCode> MultiMethodInliner::apply_call_site_summary(
    bool is_static,
    DexType* declaring_type,
    DexProto* proto,
    const cfg::ControlFlowGraph& original_cfg,
    const CallSiteSummary* call_site_summary) {
  if (call_site_summary == nullptr) {
    return nullptr;
  }

  if (call_site_summary->arguments.is_top()) {
    if (proto->is_void() || call_site_summary->result_used) {
      return nullptr;
    }
  }

  // Clone original cfg
  auto reduced_code = std::make_shared<ReducedCode>();
  original_cfg.deep_copy(&reduced_code->cfg());

  // If result is not used, change all return-* instructions to return-void (and
  // let local-dce remove the code that leads to it).
  if (!proto->is_void() && !call_site_summary->result_used) {
    proto = DexProto::make_proto(type::_void(), proto->get_args());
    for (auto& mie : InstructionIterable(reduced_code->cfg())) {
      if (opcode::is_a_return(mie.insn->opcode())) {
        mie.insn->set_opcode(OPCODE_RETURN_VOID);
        mie.insn->set_srcs_size(0);
      }
    }
  }

  // Run constant-propagation with call-site specific arguments, and then run
  // local-dce
  ConstantEnvironment initial_env =
      constant_propagation::interprocedural::env_with_params(
          is_static, &reduced_code->code(), call_site_summary->arguments);
  constant_propagation::Transform::Config config;
  // No need to add extra instructions to load constant params, we'll pass those
  // in anyway
  config.add_param_const = false;
  config.pure_methods = &m_shrinker.get_pure_methods();
  m_shrinker.constant_propagation(is_static, declaring_type, proto,
                                  &reduced_code->code(), initial_env, config);
  m_shrinker.local_dce(&reduced_code->code(),
                       /* normalize_new_instances */ false, declaring_type);

  // Re-build cfg once more to get linearized representation, good for
  // predicting fallthrough branches
  reduced_code->code().build_cfg();

  return reduced_code;
}

InlinedCost MultiMethodInliner::get_inlined_cost(
    bool is_static,
    DexType* declaring_type,
    DexProto* proto,
    const IRCode* code,
    const CallSiteSummary* call_site_summary) {
  size_t cost{0};
  std::shared_ptr<ReducedCode> reduced_code;
  size_t returns{0};
  UnorderedSet<DexMethodRef*> method_refs_set;
  UnorderedSet<const void*> other_refs_set;
  auto analyze_refs = [&](IRInstruction* insn) {
    if (insn->has_method()) {
      auto* cls = type_class(insn->get_method()->get_class());
      if ((cls != nullptr) && !cls->is_external()) {
        method_refs_set.insert(insn->get_method());
      }
    }
    if (insn->has_field()) {
      auto* cls = type_class(insn->get_field()->get_class());
      if ((cls != nullptr) && !cls->is_external()) {
        other_refs_set.insert(insn->get_field());
      }
    }
    if (insn->has_type()) {
      const auto* type = type::make_element_type_if_array(insn->get_type());
      auto* cls = type_class(type);
      if ((cls != nullptr) && !cls->is_external()) {
        other_refs_set.insert(type);
      }
    }
  };
  size_t insn_size;
  float unused_args{0};
  always_assert(code->cfg_built());
  reduced_code = apply_call_site_summary(is_static, declaring_type, proto,
                                         code->cfg(), call_site_summary);
  const auto* cfg = &(reduced_code ? &reduced_code->code() : code)->cfg();
  auto blocks = cfg->blocks();
  for (size_t i = 0; i < blocks.size(); ++i) {
    auto* block = blocks.at(i);
    for (auto& mie : InstructionIterable(block)) {
      auto* insn = mie.insn;
      cost += ::get_inlined_cost(insn, m_inliner_cost_config);
      analyze_refs(insn);
    }
    cost += ::get_inlined_cost(blocks, i, block->succs());
    if (block->branchingness() == opcode::Branchingness::BRANCH_RETURN) {
      returns++;
    }
  }
  live_range::MoveAwareChains chains(
      *cfg,
      /* ignore_unreachable */ !reduced_code,
      [&](auto* insn) { return opcode::is_a_load_param(insn->opcode()); });
  auto def_use_chains = chains.get_def_use_chains();
  size_t arg_idx = 0;
  for (auto& mie : cfg->get_param_instructions()) {
    auto it = def_use_chains.find(mie.insn);
    if (it == def_use_chains.end() || it->second.empty()) {
      float multiplier =
          1.0f; // all other multipliers are relative to this normative value
      if (call_site_summary != nullptr) {
        const auto& cv = call_site_summary->arguments.get(arg_idx);
        if (!cv.is_top()) {
          multiplier = get_unused_arg_multiplier(cv);
        }
      }
      unused_args += multiplier;
    }
    arg_idx++;
  }
  insn_size = cfg->estimate_code_units();
  if (returns > 1) {
    // if there's more than one return, gotos will get introduced to merge
    // control flow
    cost += returns - 1;
  }
  auto result_used = call_site_summary != nullptr
                         ? call_site_summary->result_used
                         : !proto->is_void();

  return (InlinedCost){cost,
                       (float)cost,
                       (float)method_refs_set.size(),
                       (float)other_refs_set.size(),
                       returns == 0u,
                       (float)result_used,
                       unused_args,
                       std::move(reduced_code),
                       insn_size};
}

float MultiMethodInliner::get_unused_arg_multiplier(
    const ConstantValue& cv) const {
  always_assert(!cv.is_top());
  always_assert(!cv.is_bottom());
  if (cv.is_zero()) {
    return m_inliner_cost_config.unused_arg_zero_multiplier;
  }
  if (auto scd = cv.maybe_get<SignedConstantDomain>()) {
    if (scd->get_constant()) {
      return m_inliner_cost_config.unused_arg_non_zero_constant_multiplier;
    }
    if (scd->is_nez()) {
      return m_inliner_cost_config.unused_arg_nez_multiplier;
    }
    return m_inliner_cost_config.unused_arg_interval_multiplier;
  }
  if (cv.is_object()) {
    if (cv.is_singleton_object()) {
      return m_inliner_cost_config.unused_arg_singleton_object_multiplier;
    }
    if (cv.is_object_with_immutable_attr()) {
      return m_inliner_cost_config
          .unused_arg_object_with_immutable_attr_multiplier;
    }
    if (cv.maybe_get<StringDomain>()) {
      return m_inliner_cost_config.unused_arg_string_multiplier;
    }
    if (cv.maybe_get<ConstantClassObjectDomain>()) {
      return m_inliner_cost_config.unused_arg_class_object_multiplier;
    }
    if (cv.maybe_get<NewObjectDomain>()) {
      return m_inliner_cost_config.unused_arg_new_object_multiplier;
    }
    return m_inliner_cost_config.unused_arg_other_object_multiplier;
  }
  return m_inliner_cost_config.unused_arg_not_top_multiplier;
}

const InlinedCost* MultiMethodInliner::get_fully_inlined_cost(
    const DexMethod* callee) {
  return m_fully_inlined_costs
      .get_or_create_and_assert_equal(
          callee,
          [&](const auto&) -> InlinedCost {
            InlinedCost inlined_cost(
                get_inlined_cost(is_static(callee), callee->get_class(),
                                 callee->get_proto(), callee->get_code()));
            TRACE(INLINE, 4,
                  "get_fully_inlined_cost(%s) = {%zu,%f,%f,%f,%s,%f,%d,%zu}",
                  SHOW(callee), inlined_cost.full_code, inlined_cost.code,
                  inlined_cost.method_refs, inlined_cost.other_refs,
                  inlined_cost.no_return ? "no_return" : "return",
                  inlined_cost.result_used, !!inlined_cost.reduced_code,
                  inlined_cost.insn_size);
            always_assert(inlined_cost.reduced_code == nullptr);
            always_assert(inlined_cost.partial_code.reduced_code == nullptr);
            return inlined_cost;
          })
      .first;
}

const InlinedCost* MultiMethodInliner::get_call_site_inlined_cost(
    const IRInstruction* invoke_insn, const DexMethod* callee) {
  return *m_invoke_call_site_inlined_costs
              .get_or_create_and_assert_equal(
                  invoke_insn,
                  [&](const auto&) {
                    const auto* call_site_summary =
                        m_call_site_summarizer
                            ? m_call_site_summarizer
                                  ->get_instruction_call_site_summary(
                                      invoke_insn)
                            : nullptr;
                    return call_site_summary == nullptr
                               ? nullptr
                               : get_call_site_inlined_cost(call_site_summary,
                                                            callee);
                  })
              .first;
}

const InlinedCost* MultiMethodInliner::get_call_site_inlined_cost(
    const CallSiteSummary* call_site_summary, const DexMethod* callee) {
  const auto* fully_inlined_cost = get_fully_inlined_cost(callee);
  always_assert(fully_inlined_cost);
  if (fully_inlined_cost->full_code >
      m_config.max_cost_for_constant_propagation) {
    return nullptr;
  }

  CalleeCallSiteSummary key{callee, call_site_summary};
  return m_call_site_inlined_costs
      .get_or_create_and_assert_equal(
          key,
          [&](const auto&) -> InlinedCost {
            auto inlined_cost = get_inlined_cost(
                is_static(callee), callee->get_class(), callee->get_proto(),
                callee->get_code(), call_site_summary);
            TRACE(
                INLINE, 4,
                "get_call_site_inlined_cost(%s) = {%zu,%f,%f,%f,%s,%f,%d,%zu}",
                call_site_summary->get_key().c_str(), inlined_cost.full_code,
                inlined_cost.code, inlined_cost.method_refs,
                inlined_cost.other_refs,
                inlined_cost.no_return ? "no_return" : "return",
                inlined_cost.result_used, !!inlined_cost.reduced_code,
                inlined_cost.insn_size);
            if (inlined_cost.insn_size >=
                std::min(fully_inlined_cost->insn_size,
                         m_config.max_reduced_size)) {
              make_partial(callee, &inlined_cost);
            }
            return inlined_cost;
          })
      .first;
}

const InlinedCost* MultiMethodInliner::get_average_inlined_cost(
    const DexMethod* callee) {
  const auto* cached = m_average_inlined_costs.get(callee);
  if (cached != nullptr) {
    return cached;
  }

  size_t callees_analyzed{0};
  size_t callees_unused_results{0};
  size_t callees_no_return{0};

  auto res = [&]() {
    const auto* fully_inlined_cost = get_fully_inlined_cost(callee);
    always_assert(fully_inlined_cost);

    if (fully_inlined_cost->full_code >
        m_config.max_cost_for_constant_propagation) {
      return *fully_inlined_cost;
    }
    const auto* callee_call_site_summary_occurrences =
        m_call_site_summarizer
            ? m_call_site_summarizer->get_callee_call_site_summary_occurrences(
                  callee)
            : nullptr;
    if (callee_call_site_summary_occurrences == nullptr) {
      return *fully_inlined_cost;
    }
    InlinedCost inlined_cost((InlinedCost){fully_inlined_cost->full_code,
                                           /* code */ 0.0f,
                                           /* method_refs */ 0.0f,
                                           /* other_refs */ 0.0f,
                                           /* no_return */ true,
                                           /* result_used */ 0.0f,
                                           /* unused_args */ 0.0f,
                                           /* reduced_cfg */ nullptr,
                                           /* insn_size */ 0});
    bool callee_has_result = !callee->get_proto()->is_void();
    for (const auto& p : *callee_call_site_summary_occurrences) {
      const auto* const call_site_summary = p.first;
      const auto count = p.second;
      const auto* call_site_inlined_cost =
          get_call_site_inlined_cost(call_site_summary, callee);
      always_assert(call_site_inlined_cost);
      if (callee_has_result && !call_site_summary->result_used) {
        callees_unused_results += count;
      }
      inlined_cost.code +=
          call_site_inlined_cost->code * static_cast<float>(count);
      inlined_cost.method_refs +=
          call_site_inlined_cost->method_refs * static_cast<float>(count);
      inlined_cost.other_refs +=
          call_site_inlined_cost->other_refs * static_cast<float>(count);
      inlined_cost.result_used +=
          call_site_inlined_cost->result_used * static_cast<float>(count);
      inlined_cost.unused_args +=
          call_site_inlined_cost->unused_args * static_cast<float>(count);
      if (call_site_inlined_cost->no_return) {
        callees_no_return++;
      } else {
        inlined_cost.no_return = false;
      }
      if (call_site_inlined_cost->insn_size > inlined_cost.insn_size) {
        inlined_cost.insn_size = call_site_inlined_cost->insn_size;
      }
      callees_analyzed += count;
    };

    always_assert(callees_analyzed > 0);
    // compute average costs
    inlined_cost.code /= static_cast<float>(callees_analyzed);
    inlined_cost.method_refs /= static_cast<float>(callees_analyzed);
    inlined_cost.other_refs /= static_cast<float>(callees_analyzed);
    inlined_cost.result_used /= static_cast<float>(callees_analyzed);
    inlined_cost.unused_args /= static_cast<float>(callees_analyzed);
    return inlined_cost;
  }();
  TRACE(INLINE, 4, "get_average_inlined_cost(%s) = {%zu,%f,%f,%f,%s,%f,%zu}",
        SHOW(callee), res.full_code, res.code, res.method_refs, res.other_refs,
        res.no_return ? "no_return" : "return", res.result_used, res.insn_size);
  auto [ptr, emplaced] =
      m_average_inlined_costs.get_or_emplace_and_assert_equal(callee,
                                                              std::move(res));
  if (emplaced && callees_analyzed >= 0) {
    info.constant_invoke_callees_analyzed += callees_analyzed;
    info.constant_invoke_callees_unused_results += callees_unused_results;
    info.constant_invoke_callees_no_return += callees_no_return;
  }
  return ptr;
}

bool MultiMethodInliner::can_inline_init(const DexMethod* init_method) {
  return *m_can_inline_init
              .get_or_create_and_assert_equal(
                  init_method,
                  [&](const auto&) {
                    const auto* finalizable_fields =
                        m_shrinker.get_finalizable_fields();
                    // When configured, we allow for relaxed constructor
                    // inlining starting with min-sdk 21: starting with that
                    // version, the Android verifier allows that any inherited
                    // constructor may be invoked.

                    // However, following JLS 17.4.5. Happens-before Order rules
                    // (see
                    // https://docs.oracle.com/javase/specs/jls/se21/html/jls-17.html),
                    // we want to make sure that a happens-before relationship
                    // is maintained between a proper constructor and a finalize
                    // method, if any.

                    // We also exclude possibly anonymous classes as those may
                    // regress the effectiveness of the class-merging passes.
                    // TODO T184662680: While this is not a correctness issue,
                    // we should fully support relaxed init methods in
                    // class-merging. Align with what happens in
                    // unfinalize_fields_if_beneficial.

                    // We also don't want to inline constructors of throwable
                    // (exception, error) classes, as they capture the current
                    // stack trace in a way that is sensitive to inlining.
                    bool relaxed =
                        m_config.relaxed_init_inline &&
                        !klass::maybe_anonymous_class(
                            type_class(init_method->get_class())) &&
                        !is_finalizable(init_method->get_class()) &&
                        (!m_config.strict_throwable_init_inline ||
                         !type::check_cast(init_method->get_class(),
                                           type::java_lang_Throwable()));
                    return constructor_analysis::can_inline_init(
                        init_method, finalizable_fields, relaxed);
                  })
              .first;
}

bool MultiMethodInliner::too_many_callers(const DexMethod* callee) {
  bool can_delete_callee = true;
  if (root(callee) || (m_recursive_callees.count(callee) != 0u) ||
      method::is_argless_init(callee) ||
      (m_true_virtual_callees_with_other_call_sites.count(callee) != 0u) ||
      !m_config.multiple_callers) {
    if (m_config.use_call_site_summaries) {
      return true;
    }
    can_delete_callee = false;
  }

  const auto& callers = m_callee_caller.at_unsafe(callee);

  // Can we inline the init-callee into all callers?
  // If not, then we can give up, as there's no point in making the case that
  // we can eliminate the callee method based on pervasive inlining.
  if (m_analyze_and_prune_inits && method::is_init(callee)) {
    always_assert(callee->get_code()->cfg_built());
    if (!can_inline_init(callee)) {
      for (const auto& p : UnorderedIterable(callers)) {
        auto* caller = p.first;
        always_assert(caller->get_code()->cfg_built());
        if (!method::is_init(caller) ||
            caller->get_class() != callee->get_class() ||
            !constructor_analysis::can_inline_inits_in_same_class(
                caller, callee,
                /* callsite_insn */ nullptr)) {
          return true;
        }
      }
    }
  }

  // 1. Determine costs of inlining

  const auto* inlined_cost = get_average_inlined_cost(callee);
  always_assert(inlined_cost);

  std::optional<CalleeCallerRefs> callee_caller_refs;
  float cross_dex_penalty{0};
  if (m_cross_dex_penalty && !is_private(callee)) {
    callee_caller_refs = get_callee_caller_refs(callee);
    if (callee_caller_refs->same_class) {
      callee_caller_refs = std::nullopt;
    } else {
      // Inlining methods into different classes might lead to worse
      // cross-dex-ref minimization results.
      cross_dex_penalty = estimate_cross_dex_penalty(
          inlined_cost, m_inliner_cost_config, callee_caller_refs->classes > 1);
    }
  }

  float cross_dex_bonus{0};
  if (can_delete_callee && m_cross_dex_penalty) {
    auto callee_code_refs =
        get_callee_code_refs(callee, /* reduced_cfg*/ nullptr);
    const auto& mrefs = callee_code_refs->methods;
    if (std::none_of(mrefs.begin(), mrefs.end(),
                     [callee](const auto* m) { return m != callee; })) {
      cross_dex_bonus = m_inliner_cost_config.cross_dex_bonus_const;
    }
  }

  // 2. Determine costs of keeping the invoke instruction

  size_t caller_count{0};
  size_t total_fence_cost{0};
  for (auto [caller, count] : UnorderedIterable(callers)) {
    caller_count += count;
    if (get_needs_constructor_fence(caller, callee)) {
      total_fence_cost += 3 * count;
    }
  }
  float average_fence_cost =
      static_cast<float>(total_fence_cost) / static_cast<float>(caller_count);
  float invoke_cost =
      get_invoke_cost(m_inliner_cost_config, callee, inlined_cost->result_used);
  TRACE(INLINE, 3,
        "[too_many_callers] %zu calls to %s; cost: inlined %f + %f - %f, "
        "invoke %f",
        caller_count, SHOW(callee), inlined_cost->code, cross_dex_penalty,
        cross_dex_bonus, invoke_cost);

  size_t classes = callee_caller_refs ? callee_caller_refs->classes : 1;

  size_t method_cost = 0;
  if (can_delete_callee) {
    // The cost of keeping a method amounts of somewhat fixed metadata overhead,
    // plus the method body, which we approximate with the inlined cost.
    method_cost = m_inliner_cost_config.cost_method + inlined_cost->full_code;
  }

  // If we inline invocations to this method everywhere, we could delete the
  // method. Is this worth it, given the number of callsites and costs
  // involved?
  if ((inlined_cost->code + average_fence_cost -
       inlined_cost->unused_args * m_inliner_cost_config.unused_args_discount) *
              static_cast<float>(caller_count) +
          static_cast<float>(classes) * (cross_dex_penalty - cross_dex_bonus) >
      invoke_cost * static_cast<float>(caller_count) +
          static_cast<float>(method_cost)) {
    return true;
  }

  if (can_delete_callee) {
    // We are going to call is_inlinable for all callers, and we are going to
    // short circuit as those calls are potentially expensive. However,
    // is_inlinable is recording some metrics around how often certain things
    // occur, so we are creating an ordered list of callers here to make sure we
    // always call is_inlinable in the same way.
    auto ordered_callers =
        unordered_to_ordered_keys(callers, compare_dexmethods);

    // We can't eliminate the method entirely if it's not inlinable
    for (auto* caller : ordered_callers) {
      // We can't account here in detail for the caller and callee size. We hope
      // for the best, and assume that the caller is empty, and we'll use the
      // (maximum) insn_size for all inlined-costs. We'll check later again at
      // each individual call-site whether the size limits hold.
      if (!is_inlinable(caller, callee, /* reduced_cfg */ nullptr,
                        /* insn */ nullptr,
                        /* estimated_caller_size */ 0,
                        /* estimated_callee_size */ inlined_cost->insn_size)) {
        return true;
      }
    }
  }

  return false;
}

bool MultiMethodInliner::should_inline_at_call_site(
    DexMethod* caller,
    cfg::Block* caller_block,
    const IRInstruction* invoke_insn,
    DexMethod* callee,
    bool* no_return,
    bool* for_speed,
    std::shared_ptr<ReducedCode>* reduced_code,
    size_t* insn_size,
    PartialCode* partial_code) {
  const auto* inlined_cost = get_call_site_inlined_cost(invoke_insn, callee);
  if (inlined_cost == nullptr) {
    return false;
  }

  float cross_dex_penalty{0};
  if (m_cross_dex_penalty && !is_private(callee) &&
      (caller == nullptr || caller->get_class() != callee->get_class())) {
    // Inlining methods into different classes might lead to worse
    // cross-dex-ref minimization results.
    cross_dex_penalty =
        estimate_cross_dex_penalty(inlined_cost, m_inliner_cost_config, true);
  }

  float invoke_cost =
      get_invoke_cost(m_inliner_cost_config, callee, inlined_cost->result_used);
  auto fence_cost = get_needs_constructor_fence(caller, callee) ? 3 : 0;
  float inline_cost =
      inlined_cost->code + static_cast<float>(fence_cost) -
      inlined_cost->unused_args * m_inliner_cost_config.unused_args_discount +
      cross_dex_penalty;
  bool size_increased = inline_cost > invoke_cost;

  float discount =
      compute_profile_guided_discount(caller, callee, inline_cost, caller_block,
                                      inlined_cost->reduced_code.get());

  if (discount * inline_cost > invoke_cost) {
    if (no_return != nullptr) {
      *no_return = inlined_cost->no_return;
    }
    if (partial_code != nullptr) {
      *partial_code = inlined_cost->partial_code;
    }
    return false;
  }

  if (reduced_code != nullptr) {
    *reduced_code = inlined_cost->reduced_code;
  }
  if (insn_size != nullptr) {
    *insn_size = inlined_cost->insn_size;
  }
  if (for_speed != nullptr) {
    *for_speed = size_increased;
  }
  return true;
}

const DexType* MultiMethodInliner::get_recorded_receiver_cast(
    IRInstruction* insn) const {
  auto it = m_inlined_invokes_need_cast.find(insn);
  return it == m_inlined_invokes_need_cast.end() ? nullptr : it->second;
}

bool MultiMethodInliner::can_invoke_callee_directly(
    IRInstruction* insn, const DexMethod* callee) const {
  auto op = insn->opcode();
  auto fallback_op = inliner::get_fallback_invoke_opcode(callee);
  if (fallback_op == OPCODE_INVOKE_STATIC) {
    return op == OPCODE_INVOKE_STATIC;
  }
  // A virtual fallback re-resolves the callee against the receiver's runtime
  // class. An invoke-interface original does the same, so devirtualizing it is
  // fine; an invoke-super or invoke-direct original deliberately does not.
  //
  // Invoke-super is excluded for cost, not for soundness. The peeled-off code
  // is spliced into the very caller the instruction sat in, and invoke-super is
  // interpreted relative to the enclosing class, so an invoke-super fallback
  // would reach the same target without any further analysis. Taking it needs a
  // second variant of the peeled-off code per callee, which means keying both
  // the `get_callee_partial_code` cache and `InlinedCost::partial_code` by
  // variant, and it leaves a live invoke-super in inlined code, where
  // `CFGInliner::rewrite_invoke_supers` is waiting to rewrite it.
  bool dispatches_alike =
      fallback_op == OPCODE_INVOKE_VIRTUAL
          ? (op == OPCODE_INVOKE_VIRTUAL || op == OPCODE_INVOKE_INTERFACE)
          : op == fallback_op;
  if (!dispatches_alike) {
    return false;
  }
  const auto* recorded_cast = get_recorded_receiver_cast(insn);
  if (recorded_cast != nullptr) {
    // The receiver gets cast ahead of the inlined code, so the fallback sees
    // the cast value rather than the original one.
    return type::check_cast(recorded_cast, callee->get_class());
  }
  return has_receiver_of_callee_class(insn, callee);
}

bool MultiMethodInliner::should_partially_inline(cfg::Block* block,
                                                 IRInstruction* insn,
                                                 DexMethod* callee,
                                                 PartialCode* partial_code) {
  always_assert(opcode::is_an_invoke(insn->opcode()));
  always_assert(insn->has_method());
  // Partial inlining peels off the callee's hot prefix and lets the peeled-off
  // code fall back to a plain invocation of the callee, which must be a valid
  // stand-in for the instruction it replaces.
  //
  // That the peeled-off prefix is the code that would actually run at this
  // callsite is not established here: everything `get_callee` hands out is the
  // implementation that the receiver dispatches to.
  if (!m_config.partial_hot_hot_inline || !source_blocks::is_hot(block) ||
      !can_invoke_callee_directly(insn, callee)) {
    return false;
  }
  // If we don't already have pre-computed partially inlined code for this
  // particular callsite, then we'll fetch the partially inlined derived from
  // the full callee.
  if (!partial_code->is_valid()) {
    *partial_code = get_callee_partial_code(callee);
  }
  return partial_code->is_valid();
}

bool MultiMethodInliner::caller_is_blocklisted(const DexMethod* caller) {
  auto* cls = caller->get_class();
  if (m_config.get_caller_blocklist().count(cls) != 0u) {
    info.blocklisted++;
    return true;
  }
  return false;
}

/**
 * Returns true if the callee has catch type which is external and not public,
 * in which case we cannot inline.
 */
bool MultiMethodInliner::has_external_catch(
    const DexMethod* callee, const cfg::ControlFlowGraph* reduced_cfg) {
  always_assert(callee->get_code()->cfg_built());
  const auto& callee_cfg =
      reduced_cfg != nullptr ? *reduced_cfg : callee->get_code()->cfg();
  std::vector<const DexType*> types;
  callee_cfg.gather_catch_types(types);
  for (const auto* type : types) {
    auto* cls = type_class(type);
    if (cls != nullptr && cls->is_external() && !is_public(cls)) {
      return true;
    }
  }
  return false;
}

/**
 * Analyze opcodes in the callee to see if they are problematic for inlining.
 */
bool MultiMethodInliner::cannot_inline_opcodes(
    const DexMethod* caller,
    const DexMethod* callee,
    const cfg::ControlFlowGraph* reduced_cfg,
    const IRInstruction* invk_insn) {
  bool can_inline = true;
  always_assert(callee->get_code()->cfg_built());
  const auto& callee_cfg =
      reduced_cfg != nullptr ? *reduced_cfg : callee->get_code()->cfg();
  for (const auto& mie : InstructionIterable(callee_cfg)) {
    auto* insn = mie.insn;
    if (create_vmethod(insn, callee, caller)) {
      if (invk_insn != nullptr) {
        log_nopt(INL_CREATE_VMETH, caller, invk_insn);
      }
      can_inline = false;
      break;
    }
    if (outlined_invoke_outlined(insn, caller)) {
      can_inline = false;
      break;
    }
    // if the caller and callee are in the same class, we don't have to
    // worry about invoke supers, or unknown virtuals -- private /
    // protected methods will remain accessible
    if (caller->get_class() != callee->get_class()) {
      if (nonrelocatable_invoke_super(insn, callee)) {
        if (invk_insn != nullptr) {
          log_nopt(INL_HAS_INVOKE_SUPER, caller, invk_insn);
        }
        can_inline = false;
        break;
      }
      if (unknown_virtual(insn, caller)) {
        if (invk_insn != nullptr) {
          log_nopt(INL_UNKNOWN_VIRTUAL, caller, invk_insn);
        }
        can_inline = false;
        break;
      }
      if (unknown_field(insn)) {
        if (invk_insn != nullptr) {
          log_nopt(INL_UNKNOWN_FIELD, caller, invk_insn);
        }
        can_inline = false;
        break;
      }
      if (check_android_os_version(insn)) {
        can_inline = false;
        break;
      }
    }
    if (!m_config.throws_inline && insn->opcode() == OPCODE_THROW) {
      info.throws++;
      can_inline = false;
      break;
    }
  }
  if (!can_inline) {
    return true;
  }
  if (m_config.respect_sketchy_methods) {
    auto timer = m_cannot_inline_sketchy_code_timer.scope();
    if (monitor_count::cannot_inline_sketchy_code(caller->get_code()->cfg(),
                                                  callee_cfg, invk_insn)) {
      return true;
    }
  }
  return false;
}

/**
 * Check if a visibility/accessibility change would turn a method referenced
 * in a callee to virtual methods as they are inlined into the caller.
 * That is, once a callee is inlined we need to ensure that everything that
 * was referenced by a callee is visible and accessible in the caller context.
 * This step would not be needed if we changed all private instance to static.
 */
bool MultiMethodInliner::create_vmethod(IRInstruction* insn,
                                        const DexMethod* callee,
                                        const DexMethod* caller) {
  auto opcode = insn->opcode();
  if (opcode == OPCODE_INVOKE_DIRECT) {
    auto* method =
        m_concurrent_resolver(insn->get_method(), MethodSearch::Direct, caller);
    if (method == nullptr) {
      info.need_vmethod++;
      return true;
    }
    always_assert(method->is_def());
    if (caller->get_class() == callee->get_class()) {
      // No need to give up here, or make it static. Visibility is just fine.
      return false;
    }
    if (method::is_init(method)) {
      if (!method->is_concrete() && !is_public(method)) {
        info.non_pub_ctor++;
        return true;
      }
      // concrete ctors we can handle because they stay invoke_direct
      return false;
    }
    if (!can_rename(method) || method->rstate.no_optimizations()) {
      info.need_vmethod++;
      return true;
    }
  }
  return false;
}

bool MultiMethodInliner::outlined_invoke_outlined(IRInstruction* insn,
                                                  const DexMethod* caller) {
  // TODO: Remove this limitation imposed by symbolication infrastructure.
  return !PositionPatternSwitchManager::
             CAN_OUTLINED_METHOD_INVOKE_OUTLINED_METHOD &&
         insn->opcode() == OPCODE_INVOKE_STATIC && is_outlined_method(caller) &&
         is_outlined_method(insn->get_method());
}

/**
 * Return true if a callee contains an invoke super to a different method
 * in the hierarchy.
 * Inlining an invoke_super off its class hierarchy would break the verifier.
 */
bool MultiMethodInliner::nonrelocatable_invoke_super(IRInstruction* insn,
                                                     const DexMethod* callee) {
  if (insn->opcode() == OPCODE_INVOKE_SUPER) {
    if (m_config.rewrite_invoke_super) {
      auto* resolved_method = resolve_invoke_method_deprecated(insn, callee);
      if ((resolved_method != nullptr) && resolved_method->is_def() &&
          (resolved_method->as_def()->get_code() != nullptr)) {
        return false;
      }
    }
    info.invoke_super++;
    return true;
  }
  return false;
}

/**
 * The callee contains an invoke to a virtual method we either do not know
 * or it's not public. Given the caller may not be in the same
 * hierarchy/package we cannot inline it unless we make the method public.
 * But we need to make all methods public across the hierarchy and for methods
 * we don't know we have no idea whether the method was public or not anyway.
 */
bool MultiMethodInliner::unknown_virtual(IRInstruction* insn,
                                         const DexMethod* caller) {
  if (insn->opcode() == OPCODE_INVOKE_VIRTUAL) {
    auto* method = insn->get_method();
    auto* res_method =
        m_concurrent_resolver(method, MethodSearch::Virtual, caller);
    if (res_method == nullptr) {
      info.unresolved_methods++;
      if (unknown_virtuals::is_method_known_to_be_public(method)) {
        info.known_public_methods++;
        return false;
      }

      info.escaped_virtual++;
      return true;
    }
    if (res_method->is_external() && !is_public(res_method)) {
      info.non_pub_virtual++;
      return true;
    }
  }
  return false;
}

/**
 * The callee contains a *get/put instruction to an unknown field.
 * Given the caller may not be in the same hierarchy/package we cannot inline
 * it unless we make the field public.
 * But we need to make all fields public across the hierarchy and for fields
 * we don't know we have no idea whether the field was public or not anyway.
 */
bool MultiMethodInliner::unknown_field(IRInstruction* insn) {
  if (opcode::is_an_ifield_op(insn->opcode()) ||
      opcode::is_an_sfield_op(insn->opcode())) {
    auto* ref = insn->get_field();
    DexField* field = resolve_field(ref, opcode::is_an_sfield_op(insn->opcode())
                                             ? FieldSearch::Static
                                             : FieldSearch::Instance);
    if (field == nullptr) {
      info.escaped_field++;
      return true;
    }
    if (!field->is_concrete() && !is_public(field)) {
      info.non_pub_field++;
      return true;
    }
  }
  return false;
}

/**
 * return true if `insn` is
 *   sget android.os.Build.VERSION.SDK_INT
 */
bool MultiMethodInliner::check_android_os_version(IRInstruction* insn) {
  // Referencing a method or field that doesn't exist on the OS version of the
  // current device causes a "soft error" for the entire class that the
  // reference resides in. Soft errors aren't worrisome from a correctness
  // perspective (though they may cause the class to run slower on some
  // devices) but there's a bug in Android 5 that triggers an erroneous "hard
  // error" after a "soft error".
  //
  // The exact conditions that trigger the Android 5 bug aren't currently
  // known. As a quick fix, we're refusing to inline methods that check the
  // OS's version. This generally works because the reference to the
  // non-existent field/method is usually guarded by checking that
  // `android.os.build.VERSION.SDK_INT` is larger than the required api level.
  auto op = insn->opcode();
  if (opcode::is_an_sget(op)) {
    auto* ref = insn->get_field();
    DexField* field = resolve_field(ref, FieldSearch::Static);
    if (field != nullptr && field == m_sdk_int_field) {
      return true;
    }
  }
  return false;
}

std::shared_ptr<CodeRefs> MultiMethodInliner::get_callee_code_refs(
    const DexMethod* callee, const cfg::ControlFlowGraph* reduced_cfg) {
  always_assert(m_ref_checkers);

  if (m_callee_code_refs && (reduced_cfg == nullptr)) {
    const auto* res = m_callee_code_refs->get(callee);
    if (res != nullptr) {
      return *res;
    }
  }

  auto code_refs = std::make_shared<CodeRefs>(callee, reduced_cfg);
  if (m_callee_code_refs && (reduced_cfg == nullptr)) {
    m_callee_code_refs->emplace(callee, code_refs);
  }
  return code_refs;
}

std::shared_ptr<XDexMethodRefs::Refs> MultiMethodInliner::get_callee_x_dex_refs(
    const DexMethod* callee, const cfg::ControlFlowGraph* reduced_cfg) {
  always_assert(m_x_dex);

  if (m_callee_x_dex_refs && (reduced_cfg == nullptr)) {
    const auto* res = m_callee_x_dex_refs->get(callee);
    if (res != nullptr) {
      return *res;
    }
  }

  const auto* callee_code = callee->get_code();
  always_assert(callee_code->cfg_built());
  const auto& callee_cfg =
      reduced_cfg != nullptr ? *reduced_cfg : callee_code->cfg();
  auto x_dex_refs =
      std::make_shared<XDexMethodRefs::Refs>(m_x_dex->get_for_callee(
          callee_cfg,
          gather_resolved_init_class_types(
              callee_cfg, m_shrinker.get_init_classes_with_side_effects())));

  if (m_callee_x_dex_refs && (reduced_cfg == nullptr)) {
    m_callee_x_dex_refs->emplace(callee, x_dex_refs);
  }
  return x_dex_refs;
}

std::shared_ptr<UnorderedBag<const DexType*>>
MultiMethodInliner::get_callee_type_refs(
    const DexMethod* callee, const cfg::ControlFlowGraph* reduced_cfg) {
  if (m_callee_type_refs && (reduced_cfg == nullptr)) {
    const auto* res = m_callee_type_refs->get(callee);
    if (res != nullptr) {
      return *res;
    }
  }

  UnorderedSet<const DexType*> type_refs_set;
  always_assert(callee->get_code()->cfg_built());
  const auto& callee_cfg =
      reduced_cfg != nullptr ? *reduced_cfg : callee->get_code()->cfg();
  for (const auto& mie : InstructionIterable(callee_cfg)) {
    auto* insn = mie.insn;
    if (insn->has_type()) {
      type_refs_set.insert(insn->get_type());
    } else if (insn->has_method()) {
      auto* meth = insn->get_method();
      type_refs_set.insert(meth->get_class());
      auto* proto = meth->get_proto();
      type_refs_set.insert(proto->get_rtype());
      auto* args = proto->get_args();
      if (args != nullptr) {
        for (const auto& arg : *args) {
          type_refs_set.insert(arg);
        }
      }
    } else if (insn->has_field()) {
      auto* field = insn->get_field();
      type_refs_set.insert(field->get_class());
      type_refs_set.insert(field->get_type());
    }
  }

  auto type_refs = std::make_shared<UnorderedBag<const DexType*>>();
  for (const auto* type : UnorderedIterable(type_refs_set)) {
    // filter out what xstores.illegal_ref(...) doesn't care about
    if (type_class_internal(type) == nullptr) {
      continue;
    }
    type_refs->insert(type);
  }

  if (m_callee_type_refs && (reduced_cfg == nullptr)) {
    m_callee_type_refs->emplace(callee, type_refs);
  }
  return type_refs;
}

CalleeCallerRefs MultiMethodInliner::get_callee_caller_refs(
    const DexMethod* callee) {
  if (m_callee_caller_refs) {
    const auto* res = m_callee_caller_refs->get(callee);
    if (res != nullptr) {
      return *res;
    }
  }

  const auto& callers = m_callee_caller.at_unsafe(callee);
  UnorderedSet<DexType*> caller_classes;
  for (const auto& p : UnorderedIterable(callers)) {
    auto* caller = p.first;
    caller_classes.insert(caller->get_class());
  }
  auto* callee_class = callee->get_class();
  CalleeCallerRefs callee_caller_refs{
      /* same_class */ caller_classes.size() == 1 &&
          *unordered_any(caller_classes) == callee_class,
      caller_classes.size()};

  if (m_callee_caller_refs) {
    m_callee_caller_refs->emplace(callee, callee_caller_refs);
  }
  return callee_caller_refs;
}

bool MultiMethodInliner::problematic_refs(
    const DexMethod* caller,
    const DexMethod* callee,
    const cfg::ControlFlowGraph* reduced_cfg) {
  always_assert(caller->get_class() != callee->get_class());
  always_assert(m_ref_checkers);
  auto callee_code_refs = get_callee_code_refs(callee, reduced_cfg);
  always_assert(callee_code_refs);
  size_t store_idx =
      m_shrinker.get_xstores().get_store_idx(caller->get_class());
  const auto* ref_checker =
      m_ref_checkers
          ->get_or_create_and_assert_equal(
              store_idx,
              [&](auto) {
                const auto& xstores = m_shrinker.get_xstores();
                return RefChecker(&xstores, store_idx, m_min_sdk_api);
              })
          .first;
  if (!ref_checker->check_code_refs(*callee_code_refs)) {
    info.problematic_refs++;
    return true;
  }
  return false;
}

bool MultiMethodInliner::cross_store_reference(
    const DexMethod* caller,
    const DexMethod* callee,
    const cfg::ControlFlowGraph* reduced_cfg) {
  auto callee_type_refs = get_callee_type_refs(callee, reduced_cfg);
  always_assert(callee_type_refs);
  const auto& xstores = m_shrinker.get_xstores();
  size_t store_idx = xstores.get_store_idx(caller->get_class());
  for (const auto* type : UnorderedIterable(*callee_type_refs)) {
    if (xstores.illegal_ref(store_idx, type)) {
      info.cross_store++;
      return true;
    }
  }
  if (method::is_init(callee)) {
    // Extra check for constructor inlining across stores; if callee is in
    // another store, but everything the callee references is in the same store
    // as the caller, a problem can still arise (verifier will not know that
    // methods called on the receiver are okay - it will see an unresolved
    // reference).
    if (xstores.illegal_ref(store_idx, callee->get_class())) {
      info.cross_store++;
      return true;
    }
  }
  return false;
}

bool MultiMethodInliner::cross_dex_reference(
    const DexMethod* caller,
    const DexMethod* callee,
    const cfg::ControlFlowGraph* reduced_cfg) {
  if (!m_x_dex) {
    return false;
  }

  auto callee_x_dex_refs = get_callee_x_dex_refs(callee, reduced_cfg);
  if (m_x_dex->has_cross_dex_refs(*callee_x_dex_refs, caller->get_class())) {
    info.cross_dex++;
    return true;
  }
  return false;
}

bool MultiMethodInliner::cross_hot_cold(const DexMethod* caller,
                                        const DexMethod* callee,
                                        uint64_t estimated_callee_size) {
  const auto* preferred_methods = get_preferred_methods();
  if (preferred_methods == nullptr) {
    return false;
  }

  if ((preferred_methods->count_unsafe(caller) == 0u) ||
      (preferred_methods->count_unsafe(callee) != 0u)) {
    return false;
  }

  if (estimated_callee_size == 0) {
    estimated_callee_size = get_callee_insn_size(callee);
  }

  // TODO: Make configurable as part of the cost options.
  return estimated_callee_size > MAX_HOT_COLD_CALLEE_SIZE;
}

void MultiMethodInliner::delayed_visibility_changes_apply() {
  if (!m_delayed_visibility_changes) {
    return;
  }
  visibility_changes_apply_and_record_make_static(
      *m_delayed_visibility_changes);
  m_delayed_visibility_changes->clear();
}

void MultiMethodInliner::visibility_changes_apply_and_record_make_static(
    const VisibilityChanges& visibility_changes) {
  visibility_changes.apply();
  // any method that was just made public and isn't virtual or a constructor or
  // static must be made static
  for (auto* method : UnorderedIterable(visibility_changes.methods)) {
    always_assert(is_public(method));
    if (!method->is_virtual() && !method::is_init(method) &&
        !is_static(method)) {
      always_assert(can_rename(method));
      always_assert(method->is_concrete());
      m_delayed_make_static.insert(method);
    }
  }
}

void MultiMethodInliner::delayed_invoke_direct_to_static() {
  if (m_delayed_make_static.empty()) {
    return;
  }
  // We sort the methods here because make_static renames methods on
  // collision, and which collisions occur is order-dependent. E.g. if we have
  // the following methods in m_delayed_make_static:
  //
  //   Foo Foo::bar()
  //   Foo Foo::bar(Foo f)
  //
  // making Foo::bar() static first would make it collide with Foo::bar(Foo
  // f), causing it to get renamed to bar$redex0(). But if Foo::bar(Foo f)
  // gets static-ified first, it becomes Foo::bar(Foo f, Foo f), so when bar()
  // gets made static later there is no collision. So in the interest of
  // having reproducible binaries, we sort the methods first.
  //
  // Also, we didn't use an std::set keyed by method signature here because
  // make_static is mutating the signatures. The tree that implements the set
  // would have to be rebalanced after the mutations.
  auto methods =
      unordered_to_ordered(m_delayed_make_static, compare_dexmethods);
  for (auto* method : methods) {
    TRACE(MMINL, 6, "making %s static", method->get_name()->c_str());
    mutators::make_static(method);
  }
  walk::parallel::opcodes(
      m_scope, [](DexMethod* /*meth*/) { return true; },
      [&](DexMethod*, IRInstruction* insn) {
        auto op = insn->opcode();
        if (op == OPCODE_INVOKE_DIRECT) {
          auto* m = insn->get_method()->as_def();
          if ((m != nullptr) && (m_delayed_make_static.count_unsafe(m) != 0u)) {
            insn->set_opcode(OPCODE_INVOKE_STATIC);
          }
        }
      });
  m_delayed_make_static.clear();
}

// 4096 buckets is ~0.024 percentile of resolution -- far finer than the ramp's
// curvature -- and keeps the table at 32KB no matter how large the app is.
constexpr size_t HOT_CALLSITE_QUANTILES = 4096;

void MultiMethodInliner::build_hot_callsite_count_ramp() {
  const auto& cc = m_inliner_cost_config;
  // The distribution is one entry per profiled, positive-count block that holds
  // a callsite (invoke). `gather_block_counts` reduces each block to its
  // source-block execution count; the filter keeps only invoke blocks.
  std::vector<float> counts = source_blocks::gather_block_counts(
      m_scope, [](DexMethod*, cfg::Block* block) {
        for (const auto& mie : InstructionIterable(block)) {
          if (opcode::is_an_invoke(mie.insn->opcode())) {
            return true;
          }
        }
        return false;
      });
  // Sorts `counts` in place, which the quantile table below relies on.
  m_hot_callsite_count_cutoff = source_blocks::rank_cutoff_for_percentile(
      counts, cc.inline_hot_callsite_count_percentile);

  const int p_start = cc.inline_hot_callsite_count_percentile;
  const int p_top = cc.inline_hot_callsite_count_top_percentile;
  const float d_start = cc.inline_hot_callsite_count_discount;
  const float d_top = cc.inline_hot_callsite_count_top_discount;
  always_assert_log(
      (p_top > 0) == (d_top > 0.0f),
      "inline_hot_callsite_count_top_percentile and _top_discount must be set "
      "together; got %d and %f",
      p_top, d_top);
  if (p_top <= 0) {
    // No ramp configured: flat step at d_start for everything above the cutoff.
    return;
  }
  always_assert_log(p_top > p_start && p_top <= 100,
                    "inline_hot_callsite_count_top_percentile must be in (%d, "
                    "100], got %d",
                    p_start, p_top);
  always_assert_log(d_top <= d_start && d_start <= 1.0f,
                    "need 0 < d_top <= d_start <= 1, got %f and %f", d_top,
                    d_start);
  if (counts.empty()) {
    return;
  }
  m_hot_callsite_count_quantiles.reserve(HOT_CALLSITE_QUANTILES);
  m_hot_callsite_count_discounts.reserve(HOT_CALLSITE_QUANTILES);
  const double span = HOT_CALLSITE_QUANTILES - 1;
  for (size_t i = 0; i != HOT_CALLSITE_QUANTILES; ++i) {
    auto idx = static_cast<size_t>((static_cast<double>(i) / span) *
                                   static_cast<double>(counts.size() - 1));
    m_hot_callsite_count_quantiles.push_back(counts[idx]);
    double p = 100.0 * static_cast<double>(i) / span;
    double x = std::clamp((p - p_start) / static_cast<double>(p_top - p_start),
                          0.0, 1.0);
    m_hot_callsite_count_discounts.push_back(
        static_cast<float>(d_start * std::pow(d_top / d_start, x)));
  }
}

float MultiMethodInliner::hot_callsite_count_discount(float count) const {
  // Require a positive count: an unprofiled/cold callsite (count 0) must never
  // qualify, even when the cutoff degenerates to -inf (percentile <= 0).
  if (count <= 0.0f || count < m_hot_callsite_count_cutoff) {
    return 1.0f;
  }
  if (m_hot_callsite_count_quantiles.empty()) {
    return m_inliner_cost_config.inline_hot_callsite_count_discount;
  }
  auto it = std::upper_bound(m_hot_callsite_count_quantiles.begin(),
                             m_hot_callsite_count_quantiles.end(), count);
  auto i = static_cast<size_t>(it - m_hot_callsite_count_quantiles.begin());
  return m_hot_callsite_count_discounts[std::min(
      i, m_hot_callsite_count_discounts.size() - 1)];
}

float MultiMethodInliner::compute_profile_guided_discount(
    DexMethod* caller,
    DexMethod* callee,
    float inline_cost,
    cfg::Block* caller_block,
    ReducedCode* reduced_callee) {
  float discount = 1.0f;

  // [experimental] Callsite-count-percentile lever, independent of the
  // baseline-profile discount below: the hotter a callsite is within the
  // profiled (positive-count) callsite distribution, the more its local inline
  // cost is scaled down, so a genuinely hot callsite inlines a callee the flat
  // cost model would otherwise reject. NFC when the lever is off -- the cutoff
  // stays +inf, so nothing qualifies.
  if (m_inliner_cost_config.inline_hot_callsite_count_percentile > 0 &&
      caller_block != nullptr) {
    discount *= hot_callsite_count_discount(block_max_count(caller_block));
  }

  if (!m_baseline_profile) {
    return discount;
  }

  // Discounts only given to calls found to be hot with a high enough appear
  // percentage and in the baseline profile
  if ((caller_block == nullptr) ||
      !source_blocks::is_hot(
          caller_block,
          m_inliner_cost_config.profile_guided_block_appear_threshold) ||
      m_baseline_profile->methods.count(caller) == 0 ||
      !m_baseline_profile->methods.at(caller).hot) {
    return discount;
  }

  const auto* full_cost = get_fully_inlined_cost(callee);
  // Methods smaller than a particular threshold will automatically already be
  // inlined by the ART compiler, so we do not try to bias Redex into inlining.
  constexpr size_t size_threshold = 32;
  if (full_cost->full_code <= size_threshold) {
    return discount;
  }

  // Bias toward inlining if the inlined code is smaller than the original.
  auto shrinkage =
      std::min(inline_cost / static_cast<float>(full_cost->full_code), 1.0f);
  auto shrink_discount =
      pow(shrinkage, m_inliner_cost_config.profile_guided_shrink_bias);

  uint32_t hot_units = 0;
  uint32_t cold_units = 0;
  // Try to get the best estimate of hotness of inlined callee. If available, we
  // check the reduced code, otherwise we will have to check the full callee.
  if (reduced_callee != nullptr) {
    source_blocks::get_hot_cold_units(reduced_callee->code().cfg(), hot_units,
                                      cold_units);
  } else {
    source_blocks::get_hot_cold_units(callee->get_code()->cfg(), hot_units,
                                      cold_units);
  }

  // Bias toward inlining if the inlined code is mainly made of hot code.
  float heat_discount = 1.0f;
  if ((hot_units != 0u) || (cold_units != 0u)) {
    // Heat threshold is the point at which percentage hotness yields a
    // neutral bias (1.0).
    // Heat discount is the discount given to a method that is 100% made of hot
    // units.
    // If we use a linear mapping from percentage hotness to discount, we would
    // need one that maps [threshold, 1.0] -> [1.0, discount].
    float percentage = float(hot_units) / float(hot_units + cold_units);
    const auto t = m_inliner_cost_config.profile_guided_heat_threshold;
    const auto d = m_inliner_cost_config.profile_guided_heat_discount;
    heat_discount = static_cast<float>((d - 1.0) / (1.0 - t));
    heat_discount *= (percentage - t);
    heat_discount += 1.0;
  }

  return static_cast<float>(discount * shrink_discount * heat_discount);
}

namespace inliner {

// return true on successful inlining, false otherwise
bool inline_with_cfg(DexMethod* caller_method,
                     DexMethod* callee_method,
                     IRInstruction* callsite,
                     const DexType* needs_receiver_cast,
                     const DexType* needs_init_class,
                     size_t next_caller_reg,
                     const cfg::ControlFlowGraph* reduced_cfg,
                     DexMethod* rewrite_invoke_super_callee,
                     bool needs_constructor_fence) {

  auto* caller_code = caller_method->get_code();
  always_assert(caller_code->cfg_built());
  auto& caller_cfg = caller_code->cfg();
  const cfg::InstructionIterator& callsite_it = caller_cfg.find_insn(callsite);
  if (callsite_it.is_end()) {
    // The callsite is not in the caller cfg. This is probably because the
    // callsite pointer is stale. Maybe the callsite's block was deleted since
    // the time the callsite was found.
    //
    // This could have happened if a previous inlining caused a block to be
    // unreachable, and that block was deleted when the CFG was simplified.
    return false;
  }

  auto* callee_code = callee_method->get_code();
  always_assert(callee_code->cfg_built());
  const auto& callee_cfg =
      reduced_cfg != nullptr ? *reduced_cfg : callee_code->cfg();

  bool is_trivial = true;
  for (const auto& mie : InstructionIterable(callee_cfg)) {
    if (mie.insn->opcode() != OPCODE_RETURN_VOID &&
        !opcode::is_load_param(mie.insn->opcode())) {
      is_trivial = false;
      break;
    }
  }
  if (is_trivial) {
    // no need to go through expensive general inlining, which would also add
    // unnecessary or even dubious positions
    caller_cfg.remove_insn(callsite_it);
    return true;
  }

  if (caller_code->get_debug_item() == nullptr) {
    // Create an empty item so that debug info of inlinee does not get lost.
    caller_code->set_debug_item(std::make_unique<DexDebugItem>());
    // Create a fake position.
    caller_cfg.insert_before(
        caller_cfg.entry_block(),
        caller_cfg.entry_block()->get_first_non_param_loading_insn(),
        DexPosition::make_synthetic_entry_position(caller_method));
  }

  // Logging before the call to inline_cfg to get the most relevant line
  // number near callsite before callsite gets replaced. Should be ok as
  // inline_cfg does not fail to inline.
  log_opt(INLINED, caller_method, callsite);

  cfg::CFGInliner::inline_cfg(&caller_cfg, callsite_it, needs_receiver_cast,
                              needs_init_class, callee_cfg, next_caller_reg,
                              rewrite_invoke_super_callee,
                              needs_constructor_fence);

  return true;
}

} // namespace inliner
