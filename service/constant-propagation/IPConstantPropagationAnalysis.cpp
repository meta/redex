/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "IPConstantPropagationAnalysis.h"

#include <algorithm>
#include <set>

#include "Debug.h"
#include "DexAnnotation.h"
#include "GraphUtil.h"
#include "Walkers.h"
#include "WorkQueue.h"

namespace constant_propagation {

namespace interprocedural {

/*
 * Return an environment populated with parameter values.
 */
ConstantEnvironment env_with_params(bool is_static,
                                    const IRCode* code,
                                    const ArgumentDomain& args) {
  boost::sub_range<IRList> param_instruction = code->get_param_instructions();
  size_t idx{0};
  ConstantEnvironment env;
  for (auto& mie : InstructionIterable(param_instruction)) {
    auto value = args.get(idx);
    if (idx == 0 && !is_static) {
      value.meet_with(SignedConstantDomain(sign_domain::Interval::NEZ));
    }
    env.set(mie.insn->dest(), value);
    idx++;
  }
  return env;
}

// NOLINTNEXTLINE(bugprone-exception-escape)
FixpointIterator::~FixpointIterator() {
  // We are going to destroy a lot of patricia trees, which can be expensive. To
  // speed this up, we are going to do it in parallel.
  auto wq = workqueue_foreach<const DexMethod*>(
      [&](const DexMethod* method) { m_cache.at_unsafe(method).clear(); });
  for (auto&& [method, method_cache] : UnorderedIterable(m_cache)) {
    wq.add_item(method);
  }
  wq.run_all();
}

namespace {

bool has_analyzable_code(const DexMethod* method) {
  // The entry node has no associated method.
  if (method == nullptr) {
    return false;
  }
  const auto* code = method->get_code();
  if (code == nullptr) {
    return false;
  }
  if (!code->cfg_built()) {
    // This can happen when there are dangling references to methods that can
    // never run.
    return false;
  }
  return true;
}

} // namespace

void FixpointIterator::analyze_node(call_graph::NodeId const& node,
                                    Domain* current_state) const {
  auto args = current_state->get(CURRENT_PARTITION_LABEL); // intentional copy
  current_state->set(CURRENT_PARTITION_LABEL, ArgumentDomain::bottom());
  always_assert(current_state->is_bottom());
  analyze_method(node->method(), args, current_state);
}

const FixpointIterator::MethodCacheEntry* FixpointIterator::analyze_method(
    const DexMethod* method,
    const ArgumentDomain& args,
    Domain* current_state) const {
  if (!has_analyzable_code(method)) {
    return nullptr;
  }
  auto& method_cache = get_method_cache(method);
  const auto* method_cache_entry =
      find_matching_method_cache_entry(method_cache, args);
  if (method_cache_entry != nullptr) {
    ++m_stats.method_cache_hits;
  } else {
    method_cache.push_front(compute_method_cache_entry(method, args));
    ++m_stats.method_cache_misses;
    method_cache_entry = method_cache.front().get();
  }
  for (const auto& [insn, out_args] :
       UnorderedIterable(method_cache_entry->result)) {
    current_state->set(insn, out_args);
  }
  return method_cache_entry;
}

std::shared_ptr<const FixpointIterator::MethodCacheEntry>
FixpointIterator::compute_method_cache_entry(const DexMethod* method,
                                             const ArgumentDomain& args) const {
  const auto& cfg = method->get_code()->cfg();
  auto ipa =
      m_proc_analysis_factory(method, this->get_whole_program_state(), args);
  auto& intra_cp = ipa->fp_iter;
  UnorderedSet<IRInstruction*> outgoing_insns;
  if (m_call_graph->has_node(method)) {
    const auto outgoing_edges = call_graph::GraphInterface::successors(
        *m_call_graph, m_call_graph->node(method));
    for (const auto& edge : outgoing_edges) {
      if (edge->callee() == m_call_graph->exit()) {
        continue; // ghost edge to the ghost exit node
      }
      outgoing_insns.emplace(edge->invoke_insn());
    }
  }
  UnorderedMap<const IRInstruction*, ArgumentDomain> result;
  ConstantFieldPartition field_writes;
  for (auto* block : cfg.blocks()) {
    auto state = intra_cp.get_entry_state_at(block);
    auto last_insn = block->get_last_insn();
    for (auto& mie : InstructionIterable(block)) {
      auto* insn = mie.insn;
      if (insn->has_method()) {
        if (outgoing_insns.count(insn) != 0u) {
          ArgumentDomain out_args;
          for (size_t i = 0; i < insn->srcs_size(); ++i) {
            out_args.set(i, state.get(insn->src(i)));
          }
          result.emplace(insn, std::move(out_args));
        }
      }
      if (m_record_field_writes && opcode::is_an_iput(insn->opcode())) {
        if (auto write = WholeProgramState::get_field_write(insn, state)) {
          field_writes.update(write->first, [&](auto* value) {
            value->join_with(write->second);
          });
        }
      }
      intra_cp.analyze_instruction(insn, &state, insn == last_insn->insn);
    }
  }
  return std::make_shared<MethodCacheEntry>(
      (MethodCacheEntry){args, ipa->take_wps_accessor_record(),
                         std::move(result), std::move(field_writes)});
}

const FixpointIterator::MethodCacheEntry*
FixpointIterator::find_or_append_method_cache_entry(
    const DexMethod* method, const ArgumentDomain& args) const {
  if (!has_analyzable_code(method)) {
    return nullptr;
  }
  auto& method_cache = get_method_cache(method);
  for (const auto& mce : method_cache) {
    if (method_cache_entry_matches(*mce, args)) {
      ++m_stats.method_cache_hits;
      return mce.get();
    }
  }
  // At the back, so that the front entry still produced the node's exit
  // state: a node whose exit state is out of date stays stale until
  // rerun_incrementally() analyzes it again and passes its grown arguments to
  // its callees.
  method_cache.push_back(compute_method_cache_entry(method, args));
  ++m_stats.method_cache_misses;
  return method_cache.back().get();
}

void FixpointIterator::start_recording_field_writes(const Scope& scope) {
  m_record_field_writes = true;
  m_cache.clear();
  // Methods that no call graph node represents can still run (the call graph
  // misses some calls, such as those through method handles), so their writes
  // count too, as they do in WholeProgramState::collect.
  InsertOnlyConcurrentSet<const DexMethod*> methods_without_node;
  walk::parallel::code(scope, [&](const DexMethod* method, IRCode&) {
    if (has_analyzable_code(method) && !m_call_graph->has_node(method)) {
      methods_without_node.insert(method);
    }
  });
  m_methods_without_node =
      unordered_to_ordered(methods_without_node, compare_dexmethods);
}

ConstantFieldPartition
FixpointIterator::collect_writes_of_methods_without_node() const {
  const auto& methods = m_methods_without_node;
  std::vector<const MethodCacheEntry*> entries(methods.size(), nullptr);
  workqueue_run_for<size_t>(0, methods.size(), [&](size_t k) {
    // No exit state rests on the front entry of a method without a node, so
    // its stale entries can go now; nothing else would ever drop them.
    prune_stale_cache_entries(methods[k]);
    entries[k] = find_or_append_method_cache_entry(methods[k],
                                                   get_entry_args(methods[k]));
  });
  ConstantFieldPartition writes;
  for (const auto* entry : entries) {
    if (entry != nullptr) {
      writes.join_with(entry->field_writes);
    }
  }
  return writes;
}

ConstantFieldPartition FixpointIterator::collect_field_writes() const {
  always_assert(m_record_field_writes);
  auto methods = unordered_to_ordered_keys(m_cache, compare_dexmethods);
  std::vector<const MethodCacheEntry*> entries(methods.size(), nullptr);
  workqueue_run_for<size_t>(0, methods.size(), [&](size_t k) {
    const auto* method = methods[k];
    if (m_call_graph->has_node(method)) {
      entries[k] =
          find_or_append_method_cache_entry(method, get_entry_args(method));
    }
  });
  auto writes = collect_writes_of_methods_without_node();
  for (const auto* entry : entries) {
    if (entry != nullptr) {
      writes.join_with(entry->field_writes);
    }
  }
  return writes;
}

WholeProgramState::FieldGrowth FixpointIterator::grow_field_values(
    const ConstantFieldPartition& writes, size_t widening_delay) {
  return m_wps->grow_field_values(writes, widening_delay);
}

const FixpointIterator::CallGraphLevels&
FixpointIterator::get_call_graph_levels() {
  if (m_call_graph_levels != nullptr) {
    return *m_call_graph_levels;
  }
  auto levels = std::make_unique<CallGraphLevels>();
  levels->nodes =
      graph::postorder_sort<call_graph::GraphInterface>(*m_call_graph);
  std::reverse(levels->nodes.begin(), levels->nodes.end());
  for (uint32_t i = 0; i < levels->nodes.size(); ++i) {
    levels->index.emplace(levels->nodes[i], i);
  }
  std::vector<uint32_t> depth(levels->nodes.size(), 0);
  for (uint32_t i = 0; i < levels->nodes.size(); ++i) {
    for (const auto* edge : levels->nodes[i]->callees()) {
      auto j = levels->index.at(edge->callee());
      if (j > i) {
        depth[j] = std::max(depth[j], depth[i] + 1);
      }
    }
  }
  // rerun_incrementally() analyzes the nodes of a level in parallel, which is
  // safe because no node calls another node of its level: in reverse
  // postorder, an edge to a lower index goes to an ancestor on the depth-first
  // path, which has a lower level.
  for (uint32_t i = 0; i < levels->nodes.size(); ++i) {
    for (const auto* edge : levels->nodes[i]->callees()) {
      auto j = levels->index.at(edge->callee());
      always_assert_log(j == i || depth[j] != depth[i],
                        "a call between two nodes of the same level");
    }
  }
  levels->num_levels =
      depth.empty() ? 0 : *std::max_element(depth.begin(), depth.end()) + 1;
  levels->level = std::move(depth);
  m_call_graph_levels = std::move(levels);
  return *m_call_graph_levels;
}

std::vector<uint32_t> FixpointIterator::find_stale_nodes(
    const CallGraphLevels& levels) const {
  const auto& nodes = levels.nodes;
  auto stale = std::make_unique<bool[]>(nodes.size());
  workqueue_run_for<size_t>(0, nodes.size(), [&](size_t i) {
    always_assert_log(this->m_entry_states.count(nodes[i]) != 0,
                      "rerun_incrementally() follows a full run");
    const auto* method = nodes[i]->method();
    stale[i] = has_analyzable_code(method) &&
               latest_matching_method_cache_entry(
                   method, get_entry_args(method)) == nullptr;
  });
  std::vector<uint32_t> result;
  for (uint32_t i = 0; i < nodes.size(); ++i) {
    if (stale[i]) {
      result.push_back(i);
    }
  }
  return result;
}

void FixpointIterator::prune_stale_cache_entries(
    const DexMethod* method, const ArgumentDomain* entry_args) const {
  if (!has_analyzable_code(method)) {
    return;
  }
  // Values only grow, so an entry that read a value that has changed can never
  // match again. With `entry_args`, entries for other arguments go too: the
  // incremental reanalysis only joins into entry arguments, so an entry it made
  // for earlier arguments cannot match again. One left from the full run can,
  // and is then recomputed.
  get_method_cache(method).remove_if([&](const auto& mce) {
    return !wps_dependencies_match(*mce) ||
           (entry_args != nullptr && !mce->args.equals(*entry_args));
  });
}

std::vector<std::pair<uint32_t, ArgumentDomain>>
FixpointIterator::get_grown_callee_args(const CallGraphLevels& levels,
                                        call_graph::NodeId node,
                                        const Domain& exit_state) const {
  std::vector<std::pair<uint32_t, ArgumentDomain>> calls;
  for (const auto* edge : node->callees()) {
    if (edge->callee() == m_call_graph->exit()) {
      continue;
    }
    auto args = analyze_edge(edge, exit_state).get(CURRENT_PARTITION_LABEL);
    const auto& callee_args =
        this->m_entry_states.at(edge->callee()).get(CURRENT_PARTITION_LABEL);
    if (!args.leq(callee_args)) {
      calls.emplace_back(levels.index.at(edge->callee()), std::move(args));
    }
  }
  return calls;
}

std::vector<FixpointIterator::Reanalysis> FixpointIterator::reanalyze(
    const CallGraphLevels& levels,
    const std::vector<uint32_t>& batch,
    std::vector<std::vector<ArgumentDomain>>* incoming) {
  std::vector<Reanalysis> results(batch.size());
  workqueue_run_for<size_t>(0, batch.size(), [&](size_t k) {
    const auto* node = levels.nodes[batch[k]];
    // No other node of this level calls this one (see
    // get_call_graph_levels()), so only this task touches its entry state.
    auto& entry_state = this->m_entry_states.at(node);
    auto args = entry_state.get(CURRENT_PARTITION_LABEL);
    for (const auto& more : (*incoming)[batch[k]]) {
      args.join_with(more);
    }
    (*incoming)[batch[k]].clear();
    entry_state.set(CURRENT_PARTITION_LABEL, args);
    prune_stale_cache_entries(node->method(), &args);
    Domain state;
    results[k].entry = analyze_method(node->method(), args, &state);
    results[k].calls = get_grown_callee_args(levels, node, state);
    this->m_exit_states.at(node) = std::move(state);
  });
  return results;
}

ConstantFieldPartition FixpointIterator::rerun_incrementally(
    size_t max_growing_sweeps) {
  always_assert(m_record_field_writes);
  const auto& levels = get_call_graph_levels();
  const auto num_nodes = levels.nodes.size();
  std::vector<std::vector<uint32_t>> pending(levels.num_levels);
  std::vector<bool> is_pending(num_nodes, false);
  size_t num_pending = 0;
  auto schedule = [&](uint32_t i) {
    if (!is_pending[i]) {
      is_pending[i] = true;
      pending[levels.level[i]].push_back(i);
      ++num_pending;
    }
  };
  for (auto i : find_stale_nodes(levels)) {
    schedule(i);
  }

  ConstantFieldPartition writes;
  // Per node: the arguments that calls analyzed since its last analysis pass
  // to it, in the order in which their callers were analyzed. The node's next
  // analysis joins them into its entry arguments.
  std::vector<std::vector<ArgumentDomain>> incoming(num_nodes);
  // Per node: the number of sweeps in which recursive calls grew its entry
  // arguments.
  std::vector<size_t> growing_sweeps(num_nodes, 0);
  while (num_pending > 0) {
    // One sweep goes through the levels in increasing order, so a node's
    // callers outside recursion are analyzed before it. A recursive call goes
    // to the same or a lower level; the node it grows waits for the next
    // sweep.
    std::set<uint32_t> grown_by_recursion;
    for (uint32_t level = 0; level < levels.num_levels; ++level) {
      if (pending[level].empty()) {
        continue;
      }
      auto batch = std::move(pending[level]);
      pending[level].clear();
      num_pending -= batch.size();
      for (auto i : batch) {
        is_pending[i] = false;
      }
      for (auto& result : reanalyze(levels, batch, &incoming)) {
        if (result.entry != nullptr) {
          writes.join_with(result.entry->field_writes);
        }
        for (auto& [j, args] : result.calls) {
          incoming[j].push_back(std::move(args));
          if (levels.level[j] <= level) {
            grown_by_recursion.insert(j);
          }
          schedule(j);
        }
      }
    }
    // Each sweep carries growth along recursive calls only one call further,
    // so growth around a recursion can keep the sweeps going for long.
    for (auto j : grown_by_recursion) {
      if (++growing_sweeps[j] > max_growing_sweeps) {
        this->m_entry_states.at(levels.nodes[j])
            .set(CURRENT_PARTITION_LABEL, ArgumentDomain::top());
        incoming[j].clear();
      }
    }
  }
  writes.join_with(collect_writes_of_methods_without_node());
  return writes;
}

Domain FixpointIterator::analyze_edge(
    const call_graph::EdgeId& edge, const Domain& exit_state_at_source) const {
  Domain entry_state_at_dest;
  auto* insn = edge->invoke_insn();
  if (insn == nullptr) {
    entry_state_at_dest.set(CURRENT_PARTITION_LABEL, ArgumentDomain::top());
  } else {
    entry_state_at_dest.set(CURRENT_PARTITION_LABEL,
                            exit_state_at_source.get(insn));
  }
  return entry_state_at_dest;
}

std::unique_ptr<IntraproceduralAnalysis>
FixpointIterator::get_intraprocedural_analysis(const DexMethod* method) const {
  return m_proc_analysis_factory(
      method, this->get_whole_program_state(), get_entry_args(method));
}

IntraproceduralAnalysis::IntraproceduralAnalysis(
    std::unique_ptr<WholeProgramStateAccessor> wps_accessor,
    const cfg::ControlFlowGraph& cfg,
    InstructionAnalyzer<ConstantEnvironment> insn_analyzer,
    InstructionAnalyzer<ConstantEnvironment> no_throw_analyzer,
    const ConstantEnvironment& env)
    : wps_accessor(std::move(wps_accessor)),
      fp_iter(cfg, std::move(insn_analyzer), std::move(no_throw_analyzer)) {
  if (this->wps_accessor) {
    this->wps_accessor->start_recording();
  }
  fp_iter.run(env);
}

WholeProgramStateAccessorRecord
IntraproceduralAnalysis::take_wps_accessor_record() {
  if (wps_accessor == nullptr) {
    return {};
  }
  return wps_accessor->stop_recording();
}

const ArgumentDomain& FixpointIterator::get_entry_args(
    const DexMethod* method) const {
  if (m_call_graph->has_node(method)) {
    return this->get_entry_state_at(m_call_graph->node(method))
        .get(CURRENT_PARTITION_LABEL);
  }
  static const ArgumentDomain bottom = ArgumentDomain::bottom();
  return bottom;
}

FixpointIterator::MethodCache& FixpointIterator::get_method_cache(
    const DexMethod* method) const {
  MethodCache* method_cache;
  m_cache.update(method,
                 [&](auto*, auto& value, auto) { method_cache = &value; });
  return *method_cache;
}

bool FixpointIterator::method_cache_entry_matches(
    const MethodCacheEntry& mce, const ArgumentDomain& args) const {
  return mce.args.equals(args) && wps_dependencies_match(mce);
}

bool FixpointIterator::wps_dependencies_match(
    const MethodCacheEntry& mce) const {
  // Each value is compared the way WholeProgramStateAccessor read it: with a
  // call graph, a callee's return value and parameter summary come straight
  // from the partitions, also for methods that are not known.
  if (m_wps->has_call_graph()) {
    for (auto&& [method, val] :
         UnorderedIterable(mce.wps_accessor_record.method_dependencies)) {
      if (!m_wps->get_method_partition().get(method).equals(val)) {
        return false;
      }
    }
    for (auto&& [method, val] : UnorderedIterable(
             mce.wps_accessor_record.method_param_env_dependencies)) {
      if (!m_wps->get_method_param_partition().get(method).equals(val)) {
        return false;
      }
    }
  } else {
    for (auto&& [method, val] :
         UnorderedIterable(mce.wps_accessor_record.method_dependencies)) {
      if (!m_wps->get_return_value(method).equals(val)) {
        return false;
      }
    }
    for (auto&& [method, val] : UnorderedIterable(
             mce.wps_accessor_record.method_param_env_dependencies)) {
      if (!m_wps->get_method_param_env(method).equals(val)) {
        return false;
      }
    }
  }
  for (auto&& [field, val] :
       UnorderedIterable(mce.wps_accessor_record.field_dependencies)) {
    if (!m_wps->get_field_value(field).equals(val)) {
      return false;
    }
  }
  return true;
}

const FixpointIterator::MethodCacheEntry*
FixpointIterator::latest_matching_method_cache_entry(
    const DexMethod* method, const ArgumentDomain& args) const {
  const auto& method_cache = get_method_cache(method);
  if (method_cache.empty() ||
      !method_cache_entry_matches(*method_cache.front(), args)) {
    return nullptr;
  }
  return method_cache.front().get();
}

const FixpointIterator::MethodCacheEntry*
FixpointIterator::find_matching_method_cache_entry(
    MethodCache& method_cache, const ArgumentDomain& args) const {
  for (auto it = method_cache.begin(); it != method_cache.end(); it++) {
    if (method_cache_entry_matches(**it, args)) {
      auto copy = *it;
      if (it != method_cache.begin()) {
        method_cache.erase(it);
        method_cache.push_front(std::move(copy));
        copy = *method_cache.begin();
      }
      return copy.get();
    }
  }
  return nullptr;
}

} // namespace interprocedural

void set_encoded_values(const DexClass* cls, ConstantEnvironment* env) {
  always_assert(!cls->is_external());
  for (auto* sfield : cls->get_sfields()) {
    always_assert(!sfield->is_external());
    auto* value = sfield->get_static_value();
    if (value == nullptr || value->evtype() == DEVT_NULL) {
      env->set(sfield, SignedConstantDomain(0));
    } else if (type::is_primitive(sfield->get_type())) {
      env->set(sfield, SignedConstantDomain(value->value()));
    } else if (sfield->get_type() == type::java_lang_String() &&
               value->evtype() == DEVT_STRING) {
      env->set(
          sfield,
          StringDomain(dynamic_cast<DexEncodedValueString*>(value)->string()));
    } else if (sfield->get_type() == type::java_lang_Class() &&
               value->evtype() == DEVT_TYPE) {
      env->set(sfield,
               ConstantClassObjectDomain(
                   dynamic_cast<DexEncodedValueType*>(value)->type()));
    } else {
      env->set(sfield, ConstantValue::top());
    }
  }
}

/**
 * This function is much simpler than set_ifield_values since there are no
 * DexEncodedValues to handle.
 */
void set_ifield_values(const DexClass* cls,
                       const EligibleIfields& eligible_ifields,
                       ConstantEnvironment* env) {
  always_assert(!cls->is_external());
  for (auto* ifield : cls->get_ifields()) {
    always_assert(!ifield->is_external());
    if (eligible_ifields.count(ifield) == 0u) {
      // If the field is not a eligible ifield, move on.
      continue;
    }
    env->set(ifield, SignedConstantDomain(0));
  }
}

} // namespace constant_propagation
