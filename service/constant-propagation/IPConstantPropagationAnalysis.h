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
      std::unique_ptr<WholeProgramStateAccessor> wps_accessor,
      const cfg::ControlFlowGraph& cfg,
      InstructionAnalyzer<ConstantEnvironment> insn_analyzer,
      InstructionAnalyzer<ConstantEnvironment> no_throw_analyzer,
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

  /*
   * Makes every later analysis of a method record what the method writes to
   * instance fields, which collect_field_writes() and rerun_incrementally()
   * read. Drops the cached results, which lack those writes. The methods of
   * `scope` that no call graph node represents count as well, analyzed with
   * unknown arguments.
   */
  void start_recording_field_writes(const Scope& scope);

  // Stops recording; the cached results keep the writes they have.
  void stop_recording_field_writes();

  /*
   * Returns what the methods write to instance fields under their current
   * entry arguments and the current whole-program state, analyzing the methods
   * that no cache entry matches; the methods without a call graph node are
   * analyzed with unknown arguments. Leaves the entry and exit states alone:
   * a method whose exit state is out of date stays stale for
   * rerun_incrementally().
   */
  ConstantFieldPartition collect_field_writes() const;

  /*
   * Joins `writes` into the field values of the whole-program state; see
   * WholeProgramState::grow_field_values.
   */
  WholeProgramState::FieldGrowth grow_field_values(
      const ConstantFieldPartition& writes, size_t widening_delay);

  /*
   * Brings the analysis up to date after the whole-program state grew (see
   * grow_field_values), without visiting every method again. Starting from
   * the current entry arguments, re-analyzes the methods whose cached result
   * read a whole-program value that has since changed, then every method whose
   * entry arguments grew as a result, and updates the entry and exit states.
   * Returns what the re-analyzed methods write to instance fields; the writes
   * of the others are unchanged. The entry arguments of a method that its
   * recursive calls have grown in more than `max_growing_sweeps` passes over
   * the call graph are set to Top, so the result can be less precise than a
   * full run's, but it stays sound.
   */
  ConstantFieldPartition rerun_incrementally(size_t max_growing_sweeps);

  const call_graph::Graph& get_call_graph() { return *m_call_graph; }

  const Stats& get_stats() const { return m_stats; }

 private:
  const ArgumentDomain& get_entry_args(const DexMethod* method) const;

  // Non-const for grow_field_values(), the only change to the state between
  // replacements by set_whole_program_state(). It only grows field values,
  // which rerun_incrementally() and prune_stale_cache_entries() rely on.
  std::unique_ptr<WholeProgramState> m_wps;
  IntraproceduralAnalysisFactory m_proc_analysis_factory;
  std::shared_ptr<const call_graph::Graph> m_call_graph;
  struct MethodCacheEntry {
    ArgumentDomain args;
    WholeProgramStateAccessorRecord wps_accessor_record;
    UnorderedMap<const IRInstruction*, ArgumentDomain> result;
    // What the method writes to instance fields, recorded only after
    // start_recording_field_writes(). Every write is kept, not only those to
    // fields the current state tracks, because the entry can be reused under
    // another state.
    ConstantFieldPartition field_writes;
  };
  // Most recently used first. For a method that the call graph represents,
  // the front entry produced the node's current exit state.
  using MethodCache = std::list<std::shared_ptr<const MethodCacheEntry>>;
  mutable ConcurrentMap<const DexMethod*, MethodCache> m_cache;
  bool m_record_field_writes{false};
  std::vector<const DexMethod*> m_methods_without_node;

  // The order in which rerun_incrementally() visits the call graph. `nodes`
  // are in reverse postorder from the entry; an edge from a lower to a higher
  // index there is a forward edge, and any other edge is a recursive call. A
  // node's level is its longest distance from the entry along forward edges,
  // so a node's callers outside recursion have lower levels.
  struct CallGraphLevels {
    std::vector<call_graph::NodeId> nodes;
    UnorderedMap<call_graph::NodeId, uint32_t> index;
    std::vector<uint32_t> level;
    uint32_t num_levels{0};
  };
  std::unique_ptr<CallGraphLevels> m_call_graph_levels;

  // A re-analyzed node's cache entry, or null for a node without analyzable
  // code, and the arguments its calls pass to callees, by callee index, where
  // they are not already below the callee's entry arguments.
  struct Reanalysis {
    const MethodCacheEntry* entry{nullptr};
    std::vector<std::pair<uint32_t, ArgumentDomain>> calls;
  };

  // Analyzes `method` under `args`, or reuses a matching cache entry, and sets
  // the arguments of its calls that the call graph represents in
  // `current_state`. Returns the cache entry, or null for a method without
  // analyzable code.
  const MethodCacheEntry* analyze_method(const DexMethod* method,
                                         const ArgumentDomain& args,
                                         Domain* current_state) const;

  // Analyzes `method`, which has analyzable code, under `args`, without
  // consulting or changing the cache.
  std::shared_ptr<const MethodCacheEntry> compute_method_cache_entry(
      const DexMethod* method, const ArgumentDomain& args) const;

  // Returns a cache entry of `method` that matches `args`, analyzing the
  // method and appending the result to the back of its cache if none does,
  // or null for a method without analyzable code. Unlike analyze_method(),
  // keeps the front entry in front.
  const MethodCacheEntry* find_or_append_method_cache_entry(
      const DexMethod* method, const ArgumentDomain& args) const;

  // Returns what the methods without a call graph node write to instance
  // fields, analyzing them with unknown arguments where no cache entry
  // matches. Drops their stale cache entries first.
  ConstantFieldPartition collect_writes_of_methods_without_node() const;

  // Drops the cache entries of `method` that read a whole-program value that
  // has changed since. With `entry_args`, the method's current entry arguments,
  // also drops the entries for other arguments, so pass them only where entry
  // arguments only grow, as in rerun_incrementally(); an entry dropped that is
  // needed again is recomputed.
  void prune_stale_cache_entries(
      const DexMethod* method,
      const ArgumentDomain* entry_args = nullptr) const;

  // Returns, by callee index, the arguments that the calls of `node` pass
  // under `exit_state`, where they are not already below the callee's entry
  // arguments.
  std::vector<std::pair<uint32_t, ArgumentDomain>> get_grown_callee_args(
      const CallGraphLevels& levels,
      call_graph::NodeId node,
      const Domain& exit_state) const;

  const CallGraphLevels& get_call_graph_levels();

  // Returns, in increasing order, the nodes with code whose latest cache entry
  // no longer matches their entry arguments and the whole-program state.
  std::vector<uint32_t> find_stale_nodes(const CallGraphLevels& levels) const;

  // Analyzes the nodes of `batch`, all of one level, again: each first joins
  // the arguments waiting for it in `incoming` into its entry arguments.
  // Updates their exit states, and returns their results in the order of
  // `batch`.
  std::vector<Reanalysis> reanalyze(
      const CallGraphLevels& levels,
      const std::vector<uint32_t>& batch,
      std::vector<std::vector<ArgumentDomain>>* incoming);

  MethodCache& get_method_cache(const DexMethod* method) const;

  bool method_cache_entry_matches(const MethodCacheEntry& mce,
                                  const ArgumentDomain& args) const;

  bool wps_dependencies_match(const MethodCacheEntry& mce) const;

  const MethodCacheEntry* find_matching_method_cache_entry(
      MethodCache& method_cache, const ArgumentDomain& args) const;

  // The cache entry that the latest analysis of `method` used, if it still
  // matches `args` and the current whole-program state.
  const MethodCacheEntry* latest_matching_method_cache_entry(
      const DexMethod* method, const ArgumentDomain& args) const;

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
