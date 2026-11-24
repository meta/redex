/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <iosfwd>
#include <utility>

#include <sparta/PatriciaTreeMapAbstractEnvironment.h>
#include <sparta/PatriciaTreeSetAbstractDomain.h>
#include <sparta/ReducedProductAbstractDomain.h>
#include <sparta/S_Expression.h>

#include "BaseIRAnalyzer.h"
#include "CallGraph.h"
#include "ConcurrentContainers.h"
#include "ControlFlow.h"
#include "DexClass.h"

/*
 * This analysis identifies heap values that are allocated within a given
 * method and have not escaped it. Specifically, it determines all the pointers
 * that a given register may contain, and figures out which of these pointers
 * must not have escaped on any path from the method entry to the current
 * program point.
 *
 * Note that we do not model instance fields or array elements, so any values
 * written to them will be treated as escaping, even if the containing object
 * does not escape the method.
 */

namespace local_pointers {

using PointerSet = sparta::PatriciaTreeSetAbstractDomain<const IRInstruction*>;

using PointerEnvironment =
    sparta::PatriciaTreeMapAbstractEnvironment<reg_t, PointerSet>;

inline bool may_alloc(IROpcode op) {
  return op == OPCODE_NEW_INSTANCE || op == OPCODE_NEW_ARRAY ||
         op == OPCODE_FILLED_NEW_ARRAY || opcode::is_a_method_invoke(op);
}

// Whether `insn` is a `const 0`, the only instruction that puts null in a
// register.
inline bool is_null_constant(const IRInstruction* insn) {
  return insn->opcode() == OPCODE_CONST && insn->get_literal() == 0;
}

/*
 * A model of pointer values on the stack and the heap values they point to in
 * the store. This acts as an interface over EnvironmentWithStoreImpl<Store>,
 * allowing us to write generic algorithms that are indifferent to the specific
 * type of Store used.
 */
class EnvironmentWithStore {
 public:
  virtual ~EnvironmentWithStore() = default;

  // Explicitly defaulting copy/move semantics for implicit copy constructor
  // is deprecated warning.
  EnvironmentWithStore() = default;
  EnvironmentWithStore(const EnvironmentWithStore&) = default;
  EnvironmentWithStore& operator=(const EnvironmentWithStore&) = default;
  EnvironmentWithStore(EnvironmentWithStore&&) = default;
  EnvironmentWithStore& operator=(EnvironmentWithStore&&) = default;

  virtual const PointerEnvironment& get_pointer_environment() const = 0;

  virtual bool may_have_escaped(const IRInstruction* ptr) const = 0;

  const PointerSet& get_pointers(reg_t reg) const {
    return get_pointer_environment().get(reg);
  }

  virtual void set_pointers(reg_t reg, PointerSet pset) = 0;

  virtual void set_fresh_pointer(reg_t reg, const IRInstruction* pointer) = 0;

  /*
   * Indicate that the blamed instruction may cause the pointer which is held
   * in the given register to escape.
   */
  virtual void set_may_escape_pointer(reg_t reg,
                                      const IRInstruction* pointer,
                                      const IRInstruction* blame) = 0;

  /*
   * Consider all pointers that may be contained in this register to have been
   * escaped by the blamed instruction.
   */
  virtual void set_may_escape(reg_t reg, const IRInstruction* blame) = 0;
};

template <class Store>
class EnvironmentWithStoreImpl final
    : public sparta::ReducedProductAbstractDomain<
          EnvironmentWithStoreImpl<Store>,
          PointerEnvironment,
          typename Store::Domain>,
      public EnvironmentWithStore {
 public:
  using StoreDomain = typename Store::Domain;
  using Base =
      sparta::ReducedProductAbstractDomain<EnvironmentWithStoreImpl<Store>,
                                           PointerEnvironment,
                                           StoreDomain>;

  EnvironmentWithStoreImpl() = default;
  EnvironmentWithStoreImpl(PointerEnvironment pe, StoreDomain sd)
      : Base(std::make_tuple(std::move(pe), std::move(sd))) {}

  static void reduce_product(
      const std::tuple<PointerEnvironment, StoreDomain>&) {}

  const PointerEnvironment& get_pointer_environment() const override {
    return Base::template get<0>();
  }

  const StoreDomain& get_store() const { return Base::template get<1>(); }

  bool may_have_escaped(const IRInstruction* ptr) const override {
    if (is_always_escaping(ptr)) {
      return true;
    }
    return Store::may_have_escaped(Base::template get<1>(), ptr);
  }

  void set_pointers(reg_t reg, PointerSet pset) override {
    Base::template apply<0>(
        [&](PointerEnvironment* penv) { penv->set(reg, std::move(pset)); });
  }

  void set_fresh_pointer(reg_t reg, const IRInstruction* pointer) override {
    set_pointers(reg, PointerSet(pointer));
    Base::template apply<1>(
        [&](StoreDomain* store) { Store::set_fresh(pointer, store); });
  }

  void set_may_escape_pointer(reg_t reg,
                              const IRInstruction* pointer,
                              const IRInstruction* blame) override {
    set_pointers(reg, PointerSet(pointer));
    if (!is_always_escaping(pointer)) {
      Base::template apply<1>([&](StoreDomain* store) {
        Store::set_may_escape(pointer, blame, store);
      });
    }
  }

  template <class F>
  void update_store(reg_t reg, F updater) {
    const auto& pointers = get_pointers(reg);
    if (!pointers.is_value()) {
      return;
    }
    Base::template apply<1>([&](StoreDomain* store) {
      for (const auto* pointer : pointers.elements()) {
        updater(pointer, store);
      }
    });
  }

  void set_may_escape(reg_t reg, const IRInstruction* blame) override {
    update_store(reg,
                 [blame](const IRInstruction* pointer, StoreDomain* store) {
                   if (!is_always_escaping(pointer)) {
                     Store::set_may_escape(pointer, blame, store);
                   }
                 });
  }

 private:
  /*
   * This method tells us whether we should always treat as may-escapes all the
   * non-null pointers written by the given instruction to its dest register.
   * This is a small performance optimization -- it means we don't have to
   * populate our may_escape set with as many pointers.
   *
   * For instructions that don't write any non-null pointer values to their
   * dests, this method will be vacuously true.
   */
  static bool is_always_escaping(const IRInstruction* ptr) {
    auto op = ptr->opcode();
    return !may_alloc(op) && op != IOPCODE_LOAD_PARAM_OBJECT;
  }
};

using ParamSet = UnorderedSet<uint16_t>;

// For denoting that a returned value is freshly allocated in the summarized
// method and only escaped at the return opcode(s).
constexpr uint16_t FRESH_RETURN = std::numeric_limits<uint16_t>::max();

// For denoting a returned value that escaped.
constexpr uint16_t ESCAPED_FRESH_RETURN = FRESH_RETURN - 1;

// For denoting a returned null. A caller treats it like ESCAPED_FRESH_RETURN;
// it is kept apart for readers of a summary that ask whether a method may
// return an object other than its parameters.
constexpr uint16_t NULL_RETURN = FRESH_RETURN - 2;

struct EscapeSummary {
  // The elements of this set represent the indexes of the src registers that
  // escape.
  ParamSet escaping_parameters;

  // The indices of the src registers that may be returned. This is useful for
  // modeling methods that return `this`, though it is also able to model the
  // general case. It is a set instead of a single value since a method may
  // return different values depending on its inputs.
  // We only track returned parameters that may pass "pointers". Other returned
  // values are not tracked. We do not model whether a method returns at all,
  // and thus the empty set is not special. See UsedVarsTest_noReturn for more
  // background on that. A returned value that is not a parameter is denoted
  // by FRESH_RETURN, ESCAPED_FRESH_RETURN or NULL_RETURN.
  ParamSet returned_parameters;

  EscapeSummary() = default;

  // TODO: Tidy complains about an unnecessary copy when using a value type.
  //       This indicates that a move constructor may be missing for ParamSet.
  EscapeSummary(ParamSet ps, std::initializer_list<uint16_t> l)
      : escaping_parameters(l), returned_parameters(std::move(ps)) {}

  static EscapeSummary from_s_expr(const sparta::s_expr&);

  bool operator==(const EscapeSummary& other) const {
    return escaping_parameters == other.escaping_parameters &&
           returned_parameters == other.returned_parameters;
  }

  bool operator<=(const EscapeSummary& other) const;

  void join_with(const EscapeSummary& other);
};

std::ostream& operator<<(std::ostream& o, const EscapeSummary& summary);

sparta::s_expr to_s_expr(const EscapeSummary&);

using InvokeToSummaryMap = UnorderedMap<const IRInstruction*, EscapeSummary>;

/*
 * A basic model of the heap, only tracking whether an object has escaped.
 */
class MayEscapeStore {
 public:
  using Domain = PointerSet;

  static void set_may_escape(const IRInstruction* ptr,
                             const IRInstruction* /* blame */,
                             Domain* dom) {
    dom->add(ptr);
  }

  static void set_fresh(const IRInstruction* ptr, Domain* dom) {
    dom->remove(ptr);
  }

  static bool may_have_escaped(const Domain& dom, const IRInstruction* ptr) {
    return dom.contains(ptr);
  }
};

using Environment = EnvironmentWithStoreImpl<MayEscapeStore>;

/*
 * Analyze the given method to determine which pointers escape. Note that we do
 * not mark returned or thrown pointers as escaping here. This makes it easier
 * to use as part of an interprocedural analysis -- the analysis of the caller
 * can choose whether to track these pointers or treat them as having escaped.
 * Check-casts would not let source value escape in normal cases. But for
 * OptimizeEnumsPass which replaces enum object with boxed integer, check-casts
 * may result in cast error. So we add the option `escape_check_cast` to make
 * OptimizeEnumsPass able to treat check-cast as an escaping instruction.
 */
class FixpointIterator final : public ir_analyzer::BaseIRAnalyzer<Environment> {
 public:
  explicit FixpointIterator(
      const cfg::ControlFlowGraph& cfg,
      InvokeToSummaryMap invoke_to_summary_map = InvokeToSummaryMap(),
      bool escape_check_cast = false,
      const UnorderedSet<DexClass*>* excluded_classes = nullptr)
      : ir_analyzer::BaseIRAnalyzer<Environment>(cfg),
        m_invoke_to_summary_map(std::move(invoke_to_summary_map)),
        m_escape_check_cast(escape_check_cast),
        m_excluded_classes(excluded_classes) {}

  void analyze_instruction(const IRInstruction* insn,
                           Environment* env) const override;

 private:
  // A map of the invoke instructions in the analyzed method to their respective
  // summaries. If an invoke instruction is not present in the method, we treat
  // it as an unknown method which could do anything (so all arguments may
  // escape).
  //
  // By taking this map as a parameter -- instead of trying to resolve callsites
  // ourselves -- we are able to switch easily between different call graph
  // construction strategies.
  InvokeToSummaryMap m_invoke_to_summary_map;
  const bool m_escape_check_cast;
  const UnorderedSet<DexClass*>* m_excluded_classes;
};

/*
 * If `insn` creates a pointer, mark it as escaped, otherwise clear the contents
 * of `dest`.  `dest` is assumed to be the destination for `insn` -- either the
 * result register, or the instruction's own register field.
 */
void escape_dest(const IRInstruction* insn,
                 reg_t dest,
                 EnvironmentWithStore* env);

void escape_heap_referenced_objects(const IRInstruction* insn,
                                    EnvironmentWithStore* env);

void escape_invoke_params(const IRInstruction* insn, EnvironmentWithStore* env);

void default_instruction_handler(const IRInstruction* insn,
                                 EnvironmentWithStore* env);

using FixpointIteratorMap =
    ConcurrentMap<const DexMethod*, std::unique_ptr<FixpointIterator>>;

using SummaryMap = UnorderedMap<const DexMethodRef*, EscapeSummary>;

struct AnalyzeScopeResult {
  FixpointIteratorMap data;
  size_t iterations;
};

/*
 * A call graph that lets `analyze_scope` summarize every method with code: each
 * such method is a root, and a call gets edges only when they reach every
 * method that can run for it. A call that may reach a native method, a method
 * of a class created at runtime, an overridable or unsummarized external
 * method, an abstract method, or one of more than `big_override_threshold`
 * overrides gets none, so `analyze_scope` treats it as a call to unknown code.
 */
class EscapeCallGraphStrategy : public call_graph::MultipleCalleeStrategy {
 public:
  static constexpr uint32_t DEFAULT_BIG_OVERRIDE_THRESHOLD = 5;

  EscapeCallGraphStrategy(
      const method_override_graph::Graph& method_override_graph,
      const Scope& scope,
      uint32_t big_override_threshold = DEFAULT_BIG_OVERRIDE_THRESHOLD);

  call_graph::CallSites get_callsites(const DexMethod* method) const override;

  call_graph::RootAndDynamic get_roots() const override;

 protected:
  // Whether the external method `callee`, which cannot be overridden, has a
  // summary that `analyze_scope` can use. `analyze_scope` itself provides only
  // the one of `Object.<init>`.
  virtual bool has_external_summary(const DexMethod* callee) const;

  // Whether `insn`, a call to `callee`, neither lets an object escape nor
  // returns one, so that it needs no summary.
  virtual bool is_object_free_call(const IRInstruction* /* insn */,
                                   const DexMethod* /* callee */) const {
    return false;
  }

 private:
  call_graph::RootAndDynamic m_root_and_dynamic;
};

/*
 * Analyze all methods in scope, making sure to analyze the callees before
 * their callers.
 *
 * If a non-null SummaryMap pointer is passed in, it will get populated
 * with the escape summaries of the methods in scope.
 */
AnalyzeScopeResult analyze_scope(
    const Scope&,
    const call_graph::Graph&,
    SummaryMap* = nullptr,
    const UnorderedSet<DexClass*>* excluded_classes = nullptr);

/*
 * Join over all possible returned and thrown values.
 */
void collect_exiting_pointers(const FixpointIterator& fp_iter,
                              const IRCode& code,
                              PointerSet* returned_ptrs,
                              PointerSet* thrown_ptrs);

/*
 * Summarize the effect a method has on its input parameters -- e.g. whether
 * they may have escaped, and whether they are being returned. Note that we
 * don't have a way to represent thrown pointers in our summary, so any such
 * pointers are treated as escaping.
 */
EscapeSummary get_escape_summary(const FixpointIterator& fp_iter,
                                 const IRCode& code,
                                 bool result_may_be_pointer);

/* Whether a method is virtual but not final, or in a final class. */
bool may_be_overridden(const DexMethod*);

// Whether a given method ref is a method called "clone" defined on an array.
bool is_array_clone(const DexMethodRef*);

} // namespace local_pointers
