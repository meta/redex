/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "TypeAnalysisCallGraphGenerationPass.h"
#include "ConfigFiles.h"

#include "Debug.h"
#include "DexUtil.h"
#include "MethodOverrideGraph.h"
#include "PassManager.h"
#include "Show.h"
#include "Trace.h"
#include "Walkers.h"

using namespace call_graph;
using namespace type_analyzer;

namespace mog = method_override_graph;

namespace {

void report_stats(const Graph& graph, PassManager& mgr) {
  auto stats = get_num_nodes_edges(graph);
  mgr.incr_metric("callgraph_nodes", stats.num_nodes);
  mgr.incr_metric("callgraph_edges", stats.num_edges);
  mgr.incr_metric("callgraph_callsites", stats.num_callsites);
  TRACE(TYPE, 2, "TypeAnalysisCallGraphGenerationPass Stats:");
  TRACE(TYPE, 2, " callgraph nodes = %u", stats.num_nodes);
  TRACE(TYPE, 2, " callgraph edges = %u", stats.num_edges);
  TRACE(TYPE, 2, " callgraph callsites = %u", stats.num_callsites);
}

/*
 * We can resolve the class of an invoke-interface target. In that case, we want
 * to adjust the MethodSearch type to be Virtual.
 */
MethodSearch get_method_search(const DexClass* analysis_cls,
                               IRInstruction* insn) {
  auto ms = opcode_to_search(insn);
  if (ms == MethodSearch::Interface && !is_interface(analysis_cls)) {
    ms = MethodSearch::Virtual;
  }
  return ms;
}

class TypeAnalysisBasedStrategy : public MultipleCalleeBaseStrategy {
 public:
  explicit TypeAnalysisBasedStrategy(
      const mog::Graph& method_override_graph,
      const Scope& scope,
      std::shared_ptr<type_analyzer::global::GlobalTypeAnalyzer> gta)
      : MultipleCalleeBaseStrategy(method_override_graph, scope),
        m_gta(std::move(gta)) {
    walk::parallel::code(scope, [](DexMethod*, IRCode& code) {
      always_assert(code.cfg_built());
      code.cfg().calculate_exit_block();
    });
  }

  CallSites get_callsites(const DexMethod* method) const override {
    CallSites callsites;
    auto* code = const_cast<IRCode*>(method->get_code());
    if (code == nullptr) {
      return callsites;
    }
    auto lta = m_gta->get_replayable_local_analysis(method);
    for (const auto& block : code->cfg().blocks()) {
      auto env = lta->get_entry_state_at(block);
      if (env.is_bottom()) {
        // Unreachable
        continue;
      }
      for (auto& mie : InstructionIterable(block)) {
        auto* insn = mie.insn;
        // Replay analysis for individual instruction
        lta->analyze_instruction(insn, &env);
        if (!opcode::is_a_method_invoke(insn->opcode())) {
          continue;
        }
        auto* resolved_callee = resolve_invoke_method_deprecated(insn, method);
        if (resolved_callee == nullptr) {
          continue;
        }
        if (!is_definitely_virtual(resolved_callee) ||
            opcode::is_invoke_super(insn->opcode())) {
          // Not true virtual call
          if (resolved_callee->is_concrete()) {
            callsites.emplace_back(resolved_callee, insn);
          }
        } else {
          get_callsites_for_true_virtual_call(resolved_callee, env, mie,
                                              callsites);
        }
      }
    }
    return callsites;
  }

 protected:
  void get_callsites_for_true_virtual_call(DexMethod* resolved_callee,
                                           const DexTypeEnvironment& env,
                                           MethodItemEntry& invoke,
                                           CallSites& callsites) const {
    auto* insn = invoke.insn;
    auto* callee_ref = insn->get_method();
    auto domain = env.get(insn->src(0));
    auto analysis_cls = domain.get_dex_cls();
    DexMethod* analysis_resolved_callee = nullptr;
    if (analysis_cls) {
      auto method_search = get_method_search(*analysis_cls, insn);
      analysis_resolved_callee =
          resolve_method_deprecated(*analysis_cls, callee_ref->get_name(),
                                    callee_ref->get_proto(), method_search);
      if (analysis_resolved_callee != nullptr) {
        resolved_callee = analysis_resolved_callee;
      } else {
        // If the analysis type is too generic and we cannot resolve a concrete
        // callee based on that type, we fall back to the method reference at
        // the call site.
        TRACE(TYPE, 5, "Unresolved callee at %s for analysis cls %s",
              SHOW(insn), SHOW(*analysis_cls));
      }
    }

    // Add callees to callsites
    if (resolved_callee->is_concrete()) {
      callsites.emplace_back(resolved_callee, insn);
    }
    always_assert(!opcode::is_invoke_super(insn->opcode()));
    const auto& overriding_methods =
        mog::get_overriding_methods(m_method_override_graph, resolved_callee);
    for (const auto* overriding_method :
         UnorderedIterable(overriding_methods)) {
      callsites.emplace_back(overriding_method, insn);
    }
  }

  std::shared_ptr<type_analyzer::global::GlobalTypeAnalyzer> m_gta;
};

} // namespace

void TypeAnalysisCallGraphGenerationPass::run_pass(DexStoresVector& stores,
                                                   ConfigFiles& /*config*/,
                                                   PassManager& mgr) {
  auto* analysis = mgr.get_preserved_analysis<GlobalTypeAnalysisPass>();
  always_assert(analysis);
  auto gta = analysis->get_result();
  always_assert(gta);

  Scope scope = build_class_scope(stores);
  m_result = std::make_shared<call_graph::Graph>(
      TypeAnalysisBasedStrategy(*mog::build_graph(scope), scope, gta));
  always_assert(m_result);
  report_stats(*m_result, mgr);
}

static TypeAnalysisCallGraphGenerationPass s_pass;
