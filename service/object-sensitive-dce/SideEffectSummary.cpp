/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "SideEffectSummary.h"

#include "CallGraph.h"
#include "ConcurrentContainers.h"
#include "Debug.h"
#include "DexUtil.h"
#include "Show.h"
#include "Trace.h"
#include "Walkers.h"

using namespace side_effects;
using namespace sparta;

namespace ptrs = local_pointers;

namespace side_effects {

using SummaryConcurrentMap =
    InsertOnlyConcurrentMap<const DexMethodRef*, Summary>;

SummaryBuilder::SummaryBuilder(
    const init_classes::InitClassesWithSideEffects&
        init_classes_with_side_effects,
    const InvokeToSummaryMap& invoke_to_summary_cmap,
    const ptrs::FixpointIterator& ptrs_fp_iter,
    const IRCode* code,
    reaching_defs::MoveAwareFixpointIterator* reaching_defs_fixpoint_iter,
    bool analyze_external_reads)
    : m_init_classes_with_side_effects(init_classes_with_side_effects),
      m_invoke_to_summary_cmap(invoke_to_summary_cmap),
      m_ptrs_fp_iter(ptrs_fp_iter),
      m_code(code),
      m_analyze_external_reads(analyze_external_reads),
      m_reaching_defs_fixpoint_iter(reaching_defs_fixpoint_iter) {
  auto idx = 0;
  auto params = code->get_param_instructions();
  for (auto& mie : InstructionIterable(params)) {
    auto* insn = mie.insn;
    m_param_insn_map.emplace(insn, idx++);
  }
}

Summary SummaryBuilder::build() {
  Summary summary;

  // Aggregate the effects of each individual instruction in the code object.
  const auto& cfg = m_code->cfg();
  for (auto* block : cfg.blocks()) {
    auto env = m_ptrs_fp_iter.get_entry_state_at(block);
    reaching_defs::Environment reaching_def_env;
    if (env.is_bottom()) {
      continue;
    }
    if (m_analyze_external_reads) {
      reaching_def_env =
          m_reaching_defs_fixpoint_iter->get_entry_state_at(block);
    }
    for (auto& mie : InstructionIterable(block)) {
      auto* insn = mie.insn;
      analyze_instruction_effects(env, reaching_def_env, insn, &summary);
      m_ptrs_fp_iter.analyze_instruction(insn, &env);
      if (m_analyze_external_reads) {
        m_reaching_defs_fixpoint_iter->analyze_instruction(insn,
                                                           &reaching_def_env);
      }
    }
  }

  return summary;
}

void SummaryBuilder::analyze_instruction_effects(
    const ptrs::Environment& env,
    const reaching_defs::Environment& reaching_def_env,
    const IRInstruction* insn,
    Summary* summary) {
  auto init_class = !(m_init_classes_with_side_effects.refine(
                          get_init_class_type_demand(insn)) == nullptr);
  if (init_class) {
    summary->effects |= EFF_INIT_CLASS;
  }

  auto op = insn->opcode();
  switch (op) {
  case OPCODE_THROW: {
    summary->effects |= EFF_THROWS;
    break;
  }
  case OPCODE_MONITOR_ENTER:
  case OPCODE_MONITOR_EXIT: {
    summary->effects |= EFF_LOCKS;
    break;
  }

  case OPCODE_SGET:
  case OPCODE_SGET_WIDE:
  case OPCODE_SGET_BOOLEAN:
  case OPCODE_SGET_BYTE:
  case OPCODE_SGET_CHAR:
  case OPCODE_SGET_SHORT:
  case OPCODE_SGET_OBJECT: {
    summary->may_read_external = true;
    break;
  }

  case OPCODE_IGET:
  case OPCODE_IGET_WIDE:
  case OPCODE_IGET_BOOLEAN:
  case OPCODE_IGET_BYTE:
  case OPCODE_IGET_CHAR:
  case OPCODE_IGET_SHORT:
  case OPCODE_IGET_OBJECT:

  case OPCODE_AGET:
  case OPCODE_AGET_WIDE:
  case OPCODE_AGET_BOOLEAN:
  case OPCODE_AGET_BYTE:
  case OPCODE_AGET_CHAR:
  case OPCODE_AGET_SHORT:
  case OPCODE_AGET_OBJECT: {
    if (m_analyze_external_reads) {
      auto def = reaching_def_env.get(insn->src(0));
      if (def.is_top() ||
          std::any_of(def.elements().begin(), def.elements().end(),
                      [&](auto insn) {
                        return !opcode::is_a_load_param(insn->opcode());
                      })) {
        summary->may_read_external = true;
      }
    } else {
      summary->may_read_external = true;
    }
    break;
  }

  case OPCODE_SPUT:
  case OPCODE_SPUT_WIDE:
  case OPCODE_SPUT_BOOLEAN:
  case OPCODE_SPUT_BYTE:
  case OPCODE_SPUT_CHAR:
  case OPCODE_SPUT_SHORT:
  case OPCODE_SPUT_OBJECT: {
    summary->effects |= EFF_WRITE_MAY_ESCAPE;
    break;
  }
  case OPCODE_IPUT:
  case OPCODE_IPUT_WIDE:
  case OPCODE_IPUT_BOOLEAN:
  case OPCODE_IPUT_BYTE:
  case OPCODE_IPUT_CHAR:
  case OPCODE_IPUT_SHORT:
  case OPCODE_IPUT_OBJECT:

  case OPCODE_APUT:
  case OPCODE_APUT_WIDE:
  case OPCODE_APUT_BOOLEAN:
  case OPCODE_APUT_BYTE:
  case OPCODE_APUT_CHAR:
  case OPCODE_APUT_SHORT:
  case OPCODE_APUT_OBJECT: {
    classify_heap_write(env, insn->src(1), summary);
    break;
  }

  case OPCODE_FILL_ARRAY_DATA: {
    classify_heap_write(env, insn->src(0), summary);
    break;
  }
  case OPCODE_INVOKE_SUPER:
  case OPCODE_INVOKE_INTERFACE:
  case OPCODE_INVOKE_STATIC:
  case OPCODE_INVOKE_DIRECT:
  case OPCODE_INVOKE_VIRTUAL: {
    if (m_invoke_to_summary_cmap.count(insn) != 0u) {
      const auto& callee_summary = m_invoke_to_summary_cmap.at(insn);
      summary->effects |= callee_summary.effects;
      summary->may_read_external |= callee_summary.may_read_external;
      for (auto idx : UnorderedIterable(callee_summary.modified_params)) {
        classify_heap_write(env, insn->src(idx), summary);
      }
    } else {
      TRACE(OSDCE, 3, "Unknown invoke: %s", SHOW(insn));
      summary->effects |= EFF_UNKNOWN_INVOKE;
    }
    break;
  }
  case OPCODE_INVOKE_POLYMORPHIC:
  case OPCODE_INVOKE_CUSTOM: {
    // Neither names the method that runs.
    summary->effects |= EFF_UNKNOWN_INVOKE;
    break;
  }
  default: {
    break;
  }
  }
}
/*
 * Given a write to the heap, classify it as one of the following:
 *   - Write to a locally-allocated non-escaping object
 *   - Write to an object passed in as a parameter
 *   - Write to an escaping and/or unknown object
 */
void SummaryBuilder::classify_heap_write(const ptrs::Environment& env,
                                         reg_t modified_ptr_reg,
                                         Summary* summary) {
  const auto& pointers = env.get_pointers(modified_ptr_reg);
  if (!pointers.is_value()) {
    summary->effects |= EFF_WRITE_MAY_ESCAPE;
    return;
  }
  for (const auto* insn : pointers.elements()) {
    if (!env.may_have_escaped(insn)) {
      if (insn->opcode() == IOPCODE_LOAD_PARAM_OBJECT) {
        summary->modified_params.emplace(m_param_insn_map.at(insn));
      }
    } else {
      TRACE(OSDCE, 3, "Escaping write to value allocated by %s", SHOW(insn));
      summary->effects |= EFF_WRITE_MAY_ESCAPE;
    }
  }
}

InvokeToSummaryMap build_summary_map(const SummaryMap& summary_map,
                                     const call_graph::Graph& call_graph,
                                     const DexMethod* method) {
  InvokeToSummaryMap invoke_to_summary_map;
  if (call_graph.has_node(method)) {
    const auto& callee_edges = call_graph.node(method)->callees();
    for (const auto& edge : callee_edges) {
      if (edge->callee() == call_graph.exit()) {
        continue;
      }
      auto* invoke_insn = edge->invoke_insn();
      auto& callee_summary = invoke_to_summary_map[invoke_insn];
      const auto* callee = edge->callee()->method();
      auto it = summary_map.find(callee);
      if (it != summary_map.end()) {
        callee_summary.join_with(it->second);
      } else if (callee == nullptr &&
                 ptrs::is_array_clone(invoke_insn->get_method())) {
        // The array clone method doesn't have any effects, and doesn't modify
        // any parameters; but may read heap locations (the elements of the
        // array it clones).
        callee_summary.join_with(
            Summary(EFF_NONE, {}, /* may_read_external */ true));
      }
    }
  }
  return invoke_to_summary_map;
}

/*
 * Analyze :method.
 */
Summary analyze_method(const init_classes::InitClassesWithSideEffects&
                           init_classes_with_side_effects,
                       const DexMethod* method,
                       const call_graph::Graph& call_graph,
                       const ptrs::FixpointIteratorMap& ptrs_fp_iter_map,
                       const SummaryMap& summary_map) {
  auto invoke_to_summary_map =
      build_summary_map(summary_map, call_graph, method);

  const auto& ptrs_fp_iter = *ptrs_fp_iter_map.at_unsafe(method);
  auto summary =
      SummaryBuilder(init_classes_with_side_effects, invoke_to_summary_map,
                     ptrs_fp_iter, method->get_code())
          .build();
  if (method->rstate.no_optimizations()) {
    summary.effects |= EFF_NO_OPTIMIZE;
  }

  if (traceEnabled(OSDCE, 3)) {
    TRACE(OSDCE, 3, "%s %s unknown side effects (%zu)", SHOW(method),
          summary.effects != EFF_NONE ? "has" : "does not have",
          summary.effects);
    if (!summary.modified_params.empty()) {
      TRACE_NO_LINE(OSDCE, 3, "Modified params: ");
      for (auto idx : UnorderedIterable(summary.modified_params)) {
        TRACE_NO_LINE(OSDCE, 3, "%u ", idx);
      }
      TRACE(OSDCE, 3, "");
    }
  }

  return summary;
}

Summary analyze_code(const init_classes::InitClassesWithSideEffects&
                         init_classes_with_side_effects,
                     const InvokeToSummaryMap& invoke_to_summary_cmap,
                     const ptrs::FixpointIterator& ptrs_fp_iter,
                     const IRCode* code) {
  return SummaryBuilder(init_classes_with_side_effects, invoke_to_summary_cmap,
                        ptrs_fp_iter, code)
      .build();
}

void analyze_scope(const init_classes::InitClassesWithSideEffects&
                       init_classes_with_side_effects,
                   const Scope& scope,
                   const call_graph::Graph& call_graph,
                   const ptrs::FixpointIteratorMap& ptrs_fp_iter_map,
                   SummaryMap* effect_summaries) {
  // This method is special: the bytecode verifier requires that this method
  // be called before a newly-allocated object gets used in any way. We can
  // model this by treating the method as modifying its `this` parameter --
  // changing it from uninitialized to initialized.
  (*effect_summaries)[method::java_lang_Object_ctor()] = Summary({0});

  auto affected_methods = std::make_unique<ConcurrentSet<const DexMethod*>>();
  walk::parallel::code(scope, [&](const DexMethod* method, IRCode&) {
    affected_methods->insert(method);
  });

  while (!affected_methods->empty()) {
    SummaryConcurrentMap changed_effect_summaries;
    auto next_affected_methods =
        std::make_unique<ConcurrentSet<const DexMethod*>>();
    workqueue_run<const DexMethod*>(
        [&](const DexMethod* method) {
          auto new_summary =
              analyze_method(init_classes_with_side_effects, method, call_graph,
                             ptrs_fp_iter_map, *effect_summaries);
          new_summary.normalize();
          auto it = effect_summaries->find(method);
          if (it != effect_summaries->end() && it->second == new_summary) {
            return;
          }
          changed_effect_summaries.emplace(method, std::move(new_summary));
          const auto& callers = call_graph.get_callers(method);
          insert_unordered_iterable(*next_affected_methods, callers);
        },
        *affected_methods);
    for (auto&& [method, summary] :
         UnorderedIterable(changed_effect_summaries)) {
      (*effect_summaries)[method] = std::move(summary);
    }
    std::swap(next_affected_methods, affected_methods);
  }
}

s_expr to_s_expr(const Summary& summary) {
  std::vector<s_expr> s_exprs;
  s_exprs.emplace_back(std::to_string(summary.effects));
  std::vector<s_expr> mod_param_s_exprs;
  mod_param_s_exprs.reserve(summary.modified_params.size());
  for (auto idx : UnorderedIterable(summary.modified_params)) {
    mod_param_s_exprs.emplace_back(idx);
  }
  s_exprs.emplace_back(mod_param_s_exprs);
  return s_expr(s_exprs);
}

std::ostream& operator<<(std::ostream& o, const Summary& summary) {
  o << "Effects: " << summary.effects << ", ";
  o << "Modified parameters: ";
  auto modified_params = unordered_to_ordered(summary.modified_params);
  bool first{true};
  for (auto p_idx : UnorderedIterable(modified_params)) {
    if (!first) {
      o << ", ";
    }
    o << p_idx;
    first = false;
  }
  o << "May-read-external: " << summary.may_read_external << ", ";
  return o;
}

Summary Summary::from_s_expr(const s_expr& expr) {
  Summary summary;
  always_assert(expr.size() == 2);
  always_assert(expr[0].is_string());
  summary.effects = std::stoi(expr[0].str());
  always_assert(expr[1].is_list());
  for (size_t i = 0; i < expr[1].size(); ++i) {
    summary.modified_params.emplace(expr[1][i].get_int32());
  }
  return summary;
}

void Summary::join_with(const Summary& other) {
  effects |= other.effects;
  insert_unordered_iterable(modified_params, other.modified_params);
  if (other.may_read_external) {
    may_read_external = true;
  }
}
} // namespace side_effects
