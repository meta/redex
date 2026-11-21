/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <sparta/HashedAbstractPartition.h>

#include <utility>

#include "AtomicStatCounter.h"
#include "CallGraph.h"
#include "ConstantEnvironment.h"
#include "ConstantPropagationAnalysis.h"
#include "ConstantPropagationWholeProgramState.h"
#include "DeterministicContainers.h"

namespace constant_propagation {

namespace interprocedural {

/*
 * ArgumentDomain describes the constant-valued arguments (if any) for a given
 * method or callsite. The n'th argument will be represented by a binding of n
 * to a ConstantDomain instance.
 *
 * Note that while this is structurally identical to the
 * ConstantRegisterEnvironment, they should be treated as semantically
 * distinct types: Here, the environment variables denote param index, whereas
 * in a ConstantRegisterEnvironment, they denote registers.
 */

using ArgumentDomain =
    sparta::PatriciaTreeMapAbstractEnvironment<param_index_t, ConstantValue>;

/*
 * This map is an abstraction of the execution paths starting from the entry
 * point of a method and ending at an invoke instruction, hence the use of an
 * abstract partitioning.
 *
 * At method entry, this map contains a single item, a binding of the null
 * pointer to an ArgumentDomain representing the input arguments. At method
 * exit, this map will have bindings from all the invoke-* instructions
 * contained in the method to the ArgumentDomains representing the arguments
 * passed to the callee.
 */
using Domain =
    sparta::HashedAbstractPartition<const IRInstruction*, ArgumentDomain>;

constexpr IRInstruction* CURRENT_PARTITION_LABEL = nullptr;

/*
 * Return an environment populated with parameter values.
 */
ConstantEnvironment env_with_params(bool is_static,
                                    const IRCode* code,
                                    const ArgumentDomain& args);

// Runs the intraprocedural fixpoint of one method. It records every
// whole-program value it reads, from construction until
// take_wps_accessor_record(), so that FixpointIterator can tell when a cached
// result of the method is stale.
struct IntraproceduralAnalysis {
  std::unique_ptr<WholeProgramStateAccessor> wps_accessor;
  intraprocedural::FixpointIterator fp_iter;
  IntraproceduralAnalysis(
      const NullCheckMethods* null_check_methods,
      std::unique_ptr<WholeProgramStateAccessor> wps_accessor,
      const cfg::ControlFlowGraph& cfg,
      InstructionAnalyzer<ConstantEnvironment> insn_analyzer,
      const ConstantEnvironment& env);

  /*
   * Stops recording and returns the whole-program values read since
   * construction: by the fixpoint iteration, including its edge transfer
   * functions, and by any later walk over the instructions.
   */
  WholeProgramStateAccessorRecord take_wps_accessor_record();
};

using IntraproceduralAnalysisFactory =
    std::function<std::unique_ptr<IntraproceduralAnalysis>(
        const DexMethod*, const WholeProgramState&, ArgumentDomain)>;

/*
 * Performs interprocedural constant propagation of stack / register values.
 *
 * The intraprocedural propagation logic is delegated to the
 * ProcedureAnalysisFactory.
 */
class FixpointIterator : public sparta::ParallelMonotonicFixpointIterator<
                             call_graph::GraphInterface,
                             Domain> {
 public:
  struct Stats {
    AtomicStatCounter<size_t> method_cache_hits{0};
    AtomicStatCounter<size_t> method_cache_misses{0};
  };
  FixpointIterator(
      std::shared_ptr<const call_graph::Graph> call_graph,
      IntraproceduralAnalysisFactory proc_analysis_factory,
      std::shared_ptr<const call_graph::Graph> call_graph_for_wps = nullptr)
      : ParallelMonotonicFixpointIterator(*call_graph),
        m_proc_analysis_factory(std::move(proc_analysis_factory)),
        m_call_graph(std::move(call_graph)) {
    auto* wps = new WholeProgramState(std::move(call_graph_for_wps));
    wps->set_to_top();
    m_wps.reset(wps);
  }

  // NOLINTNEXTLINE(bugprone-exception-escape)
  virtual ~FixpointIterator();

  void analyze_node(const call_graph::NodeId& node,
                    Domain* current_state) const override;

  Domain analyze_edge(const call_graph::EdgeId& edge,
                      const Domain& exit_state_at_source) const override;

  std::unique_ptr<IntraproceduralAnalysis> get_intraprocedural_analysis(
      const DexMethod*) const;

  const WholeProgramState& get_whole_program_state() const { return *m_wps; }

  void set_whole_program_state(std::unique_ptr<WholeProgramState> wps) {
    m_wps = std::move(wps);
  }

  const call_graph::Graph& get_call_graph() { return *m_call_graph; }

  const Stats& get_stats() const { return m_stats; }

 private:
  const ArgumentDomain& get_entry_args(const DexMethod* method) const;

  std::unique_ptr<const WholeProgramState> m_wps;
  IntraproceduralAnalysisFactory m_proc_analysis_factory;
  std::shared_ptr<const call_graph::Graph> m_call_graph;
  struct MethodCacheEntry {
    ArgumentDomain args;
    WholeProgramStateAccessorRecord wps_accessor_record;
    UnorderedMap<const IRInstruction*, ArgumentDomain> result;
  };
  using MethodCache = std::list<std::shared_ptr<const MethodCacheEntry>>;
  mutable ConcurrentMap<const DexMethod*, MethodCache> m_cache;

  MethodCache& get_method_cache(const DexMethod* method) const;

  bool method_cache_entry_matches(const MethodCacheEntry& mce,
                                  const ArgumentDomain& args) const;

  const MethodCacheEntry* find_matching_method_cache_entry(
      MethodCache& method_cache, const ArgumentDomain& args) const;

  mutable Stats m_stats;
};

} // namespace interprocedural

/*
 * For each static field in :cls, bind its encoded value in :env.
 */
void set_encoded_values(const DexClass* cls, ConstantEnvironment* env);

/**
 * Bind all eligible fields to SignedConstantDomain(0) in :env, since all
 * fields are initialized to zero by default at runtime.
 */
void set_ifield_values(const DexClass* cls,
                       const EligibleIfields& eligible_ifields,
                       ConstantEnvironment* env);

} // namespace constant_propagation
