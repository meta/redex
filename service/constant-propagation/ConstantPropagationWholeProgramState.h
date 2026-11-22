/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <optional>

#include <sparta/HashedAbstractPartition.h>
#include <sparta/PatriciaTreeMapAbstractEnvironment.h>

#include "CallGraph.h"
#include "ConstantEnvironment.h"
#include "ConstantPropagationAnalysis.h"
#include "DeterministicContainers.h"
#include "IRInstruction.h"
#include "InstructionAnalyzer.h"

namespace constant_propagation {

enum class FieldType { INSTANCE, STATIC };

using EligibleIfields = UnorderedSet<DexField*>;

namespace interprocedural {

class FixpointIterator;

} // namespace interprocedural

using ConstantFieldPartition =
    sparta::HashedAbstractPartition<const DexField*, ConstantValue>;

using ConstantMethodPartition =
    sparta::HashedAbstractPartition<const DexMethod*, ConstantValue>;

// Per-parameter abstract value summarizing what holds across every
// non-throwing exit of a method's body. Computed by joining
// env.get(param_reg) over all reachable RETURNs, restricted to params whose
// register is never reassigned inside the body (otherwise the exit value
// does not reflect the entry value the caller passed).
//
// The default value for an unbound key is ConstantValue::top(), matching
// PatriciaTreeMapAbstractEnvironment semantics.
using MethodParamEnv =
    sparta::PatriciaTreeMapAbstractEnvironment<param_index_t, ConstantValue>;

using MethodParamPartition =
    sparta::HashedAbstractPartition<const DexMethod*, MethodParamEnv>;

/*
 * This class contains flow-insensitive information about fields and method
 * return values, i.e. it can tells us if a field or a return value is constant
 * throughout the entire program.
 *
 * It should never be written to as part of the inter/intra-procedural fixpoint
 * iteration process. Instead, it takes the results of a completed fixpoint
 * iteration and extracts the constant values.
 */
class WholeProgramState {
 public:
  // By default, the field and method partitions are initialized to Bottom.
  WholeProgramState() = default;

  // By default, the field and method partitions are initialized to Bottom.
  explicit WholeProgramState(
      const UnorderedSet<const DexType*>& field_blocklist)
      : m_field_blocklist(field_blocklist) {}

  // By default, the field and method partitions are initialized to Bottom.
  explicit WholeProgramState(
      std::shared_ptr<const call_graph::Graph> call_graph)
      : m_call_graph(std::move(call_graph)) {}

  WholeProgramState(const Scope&,
                    const interprocedural::FixpointIterator&,
                    const InsertOnlyConcurrentSet<DexMethod*>&,
                    const UnorderedSet<const DexType*>&,
                    const UnorderedSet<const DexField*>&,
                    std::shared_ptr<const call_graph::Graph> call_graph);

  /*
   * If we only have knowledge of the constant values in a single class --
   * instead of a view of the constants in the whole program -- we can still
   * determine that the values of final fields are constant throughout
   * the entire program. This method records the values of those fields in the
   * WholeProgramState.
   */
  void collect_static_finals(const DexClass*, FieldEnvironment);

  void collect_instance_finals(const DexClass*,
                               const EligibleIfields&,
                               FieldEnvironment);

  void set_to_top() {
    m_field_partition.set_to_top();
    m_method_partition.set_to_top();
    m_method_param_partition.set_to_top();
  }

  bool leq(const WholeProgramState& other) const {
    return m_field_partition.leq(other.m_field_partition) &&
           m_method_partition.leq(other.m_method_partition) &&
           m_method_param_partition.leq(other.m_method_param_partition);
  }

  /*
   * Returns our best approximation of the field value.
   *
   * Bottom means that the field holds no value once initialized. For an
   * instance field, no reachable code writes it, and every constructor writes
   * it before any read, so no read of it completes normally. A static field's
   * value, Bottom included, describes it only after its class initializer
   * completes; code that the initializer runs can read it earlier (see
   * analyze_clinits).
   */
  ConstantValue get_field_value(const DexField* field) const {
    if (m_known_fields.count(field) == 0u) {
      return ConstantValue::top();
    }
    return m_field_partition.get(field);
  }

  /*
   * Returns our best static approximation of the return value.
   *
   * This may return Bottom to indicate that a method never returns (i.e. it
   * throws or loops indefinitely).
   */
  ConstantValue get_return_value(const DexMethod* method) const {
    if (m_known_methods.count(method) == 0u) {
      return ConstantValue::top();
    }
    return m_method_partition.get(method);
  }

  /*
   * Returns the per-parameter abstract value summary for `method`: the join
   * of `env.get(param_reg)` over every reachable non-throwing exit of the
   * method's body, restricted to params whose register is never reassigned.
   * Unknown methods return the top environment; a method with no reachable
   * non-throwing exit returns bottom.
   */
  MethodParamEnv get_method_param_env(const DexMethod* method) const {
    if (m_known_methods.count(method) == 0u) {
      return MethodParamEnv::top();
    }
    return m_method_param_partition.get(method);
  }

  const ConstantFieldPartition& get_field_partition() const {
    return m_field_partition;
  }

  const ConstantMethodPartition& get_method_partition() const {
    return m_method_partition;
  }

  const MethodParamPartition& get_method_param_partition() const {
    return m_method_param_partition;
  }

  bool has_call_graph() const { return !!m_call_graph; }

  const call_graph::Graph* call_graph() const { return m_call_graph.get(); }

  bool invoke_is_dynamic(const IRInstruction* insn) const {
    return call_graph::invoke_is_dynamic(*m_call_graph, insn);
  }

 private:
  void collect(
      const Scope& scope,
      const interprocedural::FixpointIterator& fp_iter,
      const UnorderedSet<const DexField*>& definitely_assigned_ifields);

  void collect_field_values(
      const IRInstruction* insn,
      const ConstantEnvironment& env,
      const DexType* clinit_cls,
      ConcurrentMap<const DexField*, ConstantValue>* fields_value_tmp);

  void collect_return_values(
      const IRInstruction* insn,
      const ConstantEnvironment& env,
      const DexMethod* method,
      ConcurrentMap<const DexMethod*, ConstantValue>* methods_value_tmp);

  // At each reachable normal-exit point of :method, build a per-param
  // env from `env.get(param_reg)` (restricted to stable param registers)
  // and join it into the running per-method binding in :methods_param_env_tmp.
  void collect_param_exit_values(
      const IRInstruction* insn,
      const ConstantEnvironment& env,
      const DexMethod* method,
      const std::vector<reg_t>& param_regs,
      const UnorderedSet<reg_t>& stable_param_regs,
      ConcurrentMap<const DexMethod*, MethodParamEnv>* methods_param_env_tmp);

  std::shared_ptr<const call_graph::Graph> m_call_graph;

  // Unknown fields and methods will be treated as containing / returning Top.
  UnorderedSet<const DexField*> m_known_fields;
  UnorderedSet<const DexMethod*> m_known_methods;

  UnorderedSet<const DexType*> m_field_blocklist;

  // A partition represents a set of execution paths that reach certain control
  // points (like invoke/return statements). The abstract information
  // associated to these terminal control points denotes the union of all
  // possible concrete states over the corresponding execution paths. In
  // contrast, an abstract environment represents the intersection of a
  // collection of abstract data over some execution paths. See proposition 12
  // of the following paper for more detail on partitions:
  // https://cs.nyu.edu/~pcousot/publications.www/CousotCousot-JLP-v2-n4-p511--547-1992.pdf
  //
  // One can think of the bindings in these DexMember-labeled Partitions as
  // modeling the state of the result register after the execution of any sget
  // or invoke instruction that references the DexMember. Since each label
  // represents a subset of control points, we should use a Partition rather
  // than an Environment here.
  //
  // This is particularly relevant for method return values -- a method can
  // "return" Bottom by throwing or never terminating, in which case we want to
  // bind it to Bottom here, but doing so in an Environment would set the whole
  // Environment to Bottom.
  ConstantFieldPartition m_field_partition;
  ConstantMethodPartition m_method_partition;
  MethodParamPartition m_method_param_partition;
};

struct WholeProgramStateAccessorRecord {
  UnorderedMap<const DexField*, ConstantValue> field_dependencies;
  UnorderedMap<const DexMethod*, ConstantValue> method_dependencies;
  UnorderedMap<const DexMethod*, MethodParamEnv> method_param_env_dependencies;
};

class WholeProgramStateAccessor {
 public:
  explicit WholeProgramStateAccessor(const WholeProgramState& wps)
      : m_wps(wps) {}

  bool has_call_graph() const { return m_wps.has_call_graph(); }

  bool invoke_is_dynamic(const IRInstruction* insn) const {
    return m_wps.invoke_is_dynamic(insn);
  }

  ConstantValue get_field_value(const DexField* field) const {
    auto val = m_wps.get_field_value(field);
    if (m_record) {
      m_record->field_dependencies.emplace(field, val);
    }
    return val;
  }

  ConstantValue get_return_value_from_cg(const IRInstruction* insn) const {
    const auto& callees =
        call_graph::resolve_callees_in_graph(*m_wps.call_graph(), insn);
    if (callees.empty()) {
      return ConstantValue::top();
    }
    for (const DexMethod* callee : UnorderedIterable(callees)) {
      if (callee->get_code() == nullptr) {
        always_assert(is_abstract(callee) || is_native(callee));
        return ConstantValue::top();
      }
    }
    ConstantValue ret = ConstantValue::bottom();
    for (const DexMethod* callee : UnorderedIterable(callees)) {
      const auto& val = m_wps.get_method_partition().get(callee);
      if (m_record) {
        m_record->method_dependencies.emplace(callee, val);
      }
      ret.join_with(val);
    }
    if (ret == ConstantValue::bottom()) {
      return ConstantValue::top();
    }
    return ret;
  }

  ConstantValue get_return_value(const DexMethod* method) const {
    auto val = m_wps.get_return_value(method);
    if (m_record) {
      m_record->method_dependencies.emplace(method, val);
    }
    return val;
  }

  MethodParamEnv get_method_param_env(const DexMethod* method) const {
    auto val = m_wps.get_method_param_env(method);
    if (m_record) {
      m_record->method_param_env_dependencies.emplace(method, val);
    }
    return val;
  }

  // Like get_return_value_from_cg, but does not fold a bottom result up to top:
  // a never-returning callee must collapse the caller's no-throw edge.
  MethodParamEnv get_method_param_env_from_cg(const IRInstruction* insn) const {
    const auto& callees =
        call_graph::resolve_callees_in_graph(*m_wps.call_graph(), insn);
    if (callees.empty()) {
      return MethodParamEnv::top();
    }
    for (const DexMethod* callee : UnorderedIterable(callees)) {
      if (callee->get_code() == nullptr) {
        always_assert(is_abstract(callee) || is_native(callee));
        return MethodParamEnv::top();
      }
    }
    MethodParamEnv ret = MethodParamEnv::bottom();
    for (const DexMethod* callee : UnorderedIterable(callees)) {
      const auto& val = m_wps.get_method_param_partition().get(callee);
      if (m_record) {
        m_record->method_param_env_dependencies.emplace(callee, val);
      }
      ret.join_with(val);
    }
    return ret;
  }

  // Starts recording every whole-program value that the getters above return.
  void start_recording() { m_record.emplace(); }

  // Stops recording and returns the values read since start_recording().
  WholeProgramStateAccessorRecord stop_recording() {
    redex_assert(m_record);
    auto record = std::move(*m_record);
    m_record.reset();
    return record;
  }

 private:
  const WholeProgramState& m_wps;
  mutable std::optional<WholeProgramStateAccessorRecord> m_record;
};

/*
 * Incorporate information about the values of static fields and the return
 * values of other methods in the local analysis of a given method.
 */
class WholeProgramAwareAnalyzer final
    : public InstructionAnalyzerBase<WholeProgramAwareAnalyzer,
                                     ConstantEnvironment,
                                     const WholeProgramStateAccessor*> {
 public:
  static bool analyze_sget(const WholeProgramStateAccessor* whole_program_state,
                           const IRInstruction* insn,
                           ConstantEnvironment* env);

  static bool analyze_iget(const WholeProgramStateAccessor* whole_program_state,
                           const IRInstruction* insn,
                           ConstantEnvironment* env);

  static bool analyze_invoke(
      const WholeProgramStateAccessor* whole_program_state,
      const IRInstruction* insn,
      ConstantEnvironment* env);
};

/*
 * Returns a no-throw analyzer that additionally consults the IPCP-derived
 * per-(method, param) exit-value summary in WholeProgramState. At an invoke
 * whose callee is statically known -- a statically-dispatched call, a
 * non-overridden virtual, or (with a call graph) any non-dynamic dispatch --
 * it meets each source register with the summarized value for the
 * corresponding parameter, then delegates to the default no-throw analyzer.
 * If `wps_accessor` is null it behaves exactly like the default.
 *
 * Why a no-throw analyzer: the summary is the join of a parameter's value over
 * the callee's normal exits, so it describes the argument only when the call
 * returns normally -- e.g. a callee that dereferences a parameter throws on
 * null, so a normal return proves that argument was non-null.
 *
 * It also makes the no-throw edge unreachable after an instance field read or
 * a call whose whole-program value is Bottom: such an instruction cannot
 * complete normally, but its exception edges stay reachable. Static field
 * reads keep their no-throw edge (see get_field_value).
 */
InstructionAnalyzer<ConstantEnvironment> make_wps_aware_no_throw_analyzer(
    const NullCheckMethods* null_check_methods,
    const WholeProgramStateAccessor* wps_accessor);

} // namespace constant_propagation
