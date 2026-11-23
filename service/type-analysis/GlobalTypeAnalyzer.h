/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <sparta/HashedAbstractPartition.h>

#include "CallGraph.h"
#include "DexTypeEnvironment.h"
#include "LocalTypeAnalyzer.h"
#include "MethodOverrideGraph.h"
#include "WholeProgramState.h"

namespace type_analyzer {

namespace global {

/*
 * ArgumentTypeEnvironment describes the DexType of arguments for a given
 * callsite. The n'th argument will be represented by a binding of n
 * to a DexTypeDomain instance.
 *
 * Note that while this is structurally identical to the
 * DexTypeEnvironment, they should be treated as semantically
 * distinct types: Here, the environment variables denote param index, whereas
 * in a DexTypeEnvironment, they denote registers.
 */

using ArgumentTypeEnvironment =
    sparta::PatriciaTreeMapAbstractEnvironment<param_index_t, DexTypeDomain>;

/*
 * This map is an abstraction of the execution paths starting from the entry
 * point of a method and ending at an invoke instruction, hence the use of an
 * abstract partitioning.
 *
 * At method entry, this map contains a single item, a binding of the null
 * pointer to an ArgumentTypeEnvironment representing the input arguments. At
 * method exit, this map will have bindings from all the invoke-* instructions
 * contained in the method to the ArgumentTypeEnvironments representing the
 * arguments passed to the callee.
 */
using ArgumentTypePartition =
    sparta::HashedAbstractPartition<const IRInstruction*,
                                    ArgumentTypeEnvironment>;

constexpr const IRInstruction* CURRENT_PARTITION_LABEL = nullptr;

/*
 * Initializing the local DexTypeEnvironment with the ArgumentTypeEnvironment
 * passed into the code. The env of the registers holding the params are
 * populated after calling this.
 */
DexTypeEnvironment env_with_params(const IRCode* code,
                                   const ArgumentTypeEnvironment& args);

/*
 * Performs interprocedural DexType analysis of stack / register values.
 * The intraprocedural propagation logic is delegated to the LocalTypeAnalyzer.
 */
class GlobalTypeAnalyzer : public sparta::ParallelMonotonicFixpointIterator<
                               call_graph::GraphInterface,
                               ArgumentTypePartition> {
 public:
  explicit GlobalTypeAnalyzer(
      std::shared_ptr<const call_graph::Graph> call_graph)
      : ParallelMonotonicFixpointIterator(*call_graph),
        m_call_graph(std::move(call_graph)) {
    auto* wps = new WholeProgramState();
    wps->set_to_top();
    m_wps.reset(wps);
  }

  void analyze_node(const call_graph::NodeId& node,
                    ArgumentTypePartition* current_partition) const override;

  ArgumentTypePartition analyze_edge(
      const call_graph::EdgeId& edge,
      const ArgumentTypePartition& exit_state_at_source) const override;

  /*
   * Run local analysis for the given method and return the LocalAnalyzer with
   * the end state.
   */
  std::unique_ptr<local::LocalTypeAnalyzer> get_replayable_local_analysis(
      const DexMethod*) const;

  const WholeProgramState& get_whole_program_state() const { return *m_wps; }

  void set_whole_program_state(std::unique_ptr<WholeProgramState> wps) {
    m_wps = std::move(wps);
  }

  const call_graph::Graph& get_call_graph() { return *m_call_graph; }

  bool is_reachable(const DexMethod* method) const;

 private:
  // What the analysis of `method` knows about how it uses its own fields.
  local::CtorFields get_ctor_fields(const DexMethod* method) const;

  std::unique_ptr<const WholeProgramState> m_wps;
  std::shared_ptr<const call_graph::Graph> m_call_graph;

  /*
   * An unsafe variant that runs the local analysis on the given method, and
   * returns the LocalAnalyzer with the end state. This is only used for
   * collecting global states. This is not meant to be used to replay analysis
   * after the global type analysis. It doesn't always fall back to the
   * WholeProgramState.
   */
  std::unique_ptr<local::LocalTypeAnalyzer> get_internal_local_analysis(
      const DexMethod*) const;

  std::unique_ptr<local::LocalTypeAnalyzer> analyze_method(
      const DexMethod* method,
      const WholeProgramState& wps,
      ArgumentTypeEnvironment args,
      const bool is_replayable = false) const;

  friend class type_analyzer::WholeProgramState;
};

class GlobalTypeAnalysis {

 public:
  explicit GlobalTypeAnalysis(
      size_t max_global_analysis_iteration = 10,
      bool use_multiple_callee_callgraph = false,
      bool only_aggregate_safely_inferrable_fields = true,
      bool enforce_iteration_refinement = true)
      : m_max_global_analysis_iteration(max_global_analysis_iteration),
        m_use_multiple_callee_callgraph(use_multiple_callee_callgraph),
        m_only_aggregate_safely_inferrable_fields(
            only_aggregate_safely_inferrable_fields),
        m_enforce_iteration_refinement(enforce_iteration_refinement) {}

  void run(const Scope& scope) { analyze(scope); }

  std::unique_ptr<GlobalTypeAnalyzer> analyze(const Scope&);

  size_t get_global_analysis_iterations() const {
    return global_analysis_iterations;
  }

 private:
  const size_t m_max_global_analysis_iteration;
  size_t global_analysis_iterations{0};

  bool m_use_multiple_callee_callgraph;
  bool m_only_aggregate_safely_inferrable_fields;
  bool m_enforce_iteration_refinement;
  // Methods reachable from clinit that read static fields and reachable from
  // ctors that read instance fields.
  ConcurrentSet<const DexMethod*> m_any_init_reachables;

  struct Stats {
    size_t resolved_fields{0};
    size_t resolved_methods{0};
  } m_stats;

  void find_any_init_reachables(
      const method_override_graph::Graph& method_override_graph,
      const Scope&,
      std::shared_ptr<const call_graph::Graph>);

  void trace_stats(WholeProgramState& wps);
};

} // namespace global

} // namespace type_analyzer
