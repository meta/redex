/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "IPConstantPropagationAnalysis.h"

#include "Debug.h"
#include "DexAnnotation.h"
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

void FixpointIterator::analyze_node(call_graph::NodeId const& node,
                                    Domain* current_state) const {
  auto args = current_state->get(CURRENT_PARTITION_LABEL); // intentional copy
  current_state->set(CURRENT_PARTITION_LABEL, ArgumentDomain::bottom());
  always_assert(current_state->is_bottom());

  const DexMethod* method = node->method();
  // The entry node has no associated method.
  if (method == nullptr) {
    return;
  }
  const auto* code = method->get_code();
  if (code == nullptr) {
    return;
  }
  if (!code->cfg_built()) {
    // This can happen when there are dangling references to methods that can
    // never run.
    return;
  }
  auto& method_cache = get_method_cache(method);
  const auto* method_cache_entry =
      find_matching_method_cache_entry(method_cache, args);
  if (method_cache_entry != nullptr) {
    for (const auto& [insn, out_args] :
         UnorderedIterable(method_cache_entry->result)) {
      current_state->set(insn, out_args);
    }
    ++m_stats.method_cache_hits;
    return;
  }

  const auto& cfg = code->cfg();
  auto ipa =
      m_proc_analysis_factory(method, this->get_whole_program_state(), args);
  auto& intra_cp = ipa->fp_iter;
  const auto outgoing_edges =
      call_graph::GraphInterface::successors(*m_call_graph, node);
  UnorderedSet<IRInstruction*> outgoing_insns;
  for (const auto& edge : outgoing_edges) {
    if (edge->callee() == m_call_graph->exit()) {
      continue; // ghost edge to the ghost exit node
    }
    outgoing_insns.emplace(edge->invoke_insn());
  }
  UnorderedMap<const IRInstruction*, ArgumentDomain> result;
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
      intra_cp.analyze_instruction(insn, &state, insn == last_insn->insn);
    }
  }
  for (auto& [insn, out_args] : UnorderedIterable(result)) {
    current_state->set(insn, out_args);
  }
  method_cache.push_front(std::make_shared<MethodCacheEntry>((MethodCacheEntry){
      std::move(args), ipa->take_wps_accessor_record(), std::move(result)}));
  ++m_stats.method_cache_misses;
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
  if (!mce.args.equals(args)) {
    return false;
  }
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
