/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <limits>
#include <optional>
#include <sparta/MonotonicFixpointIterator.h>
#include <utility>

#include "BaseIRAnalyzer.h"
#include "ConcurrentContainers.h"
#include "ConstantEnvironment.h"
#include "ConstantPropagationState.h"
#include "DeterministicContainers.h"
#include "IRCode.h"
#include "InstructionAnalyzer.h"
#include "KotlinNullCheckMethods.h"
#include "MethodUtil.h"

class DexMethodRef;

namespace constant_propagation {

std::optional<size_t> get_null_check_object_index(
    const IRInstruction* insn, const NullCheckMethods& null_check_methods);

// The exact runtime type of an object constant -- String for a const-string,
// Class for a const-class -- or nullptr when the value is not such a constant.
const DexType* get_object_constant_type(const ConstantValue& value);

namespace intraprocedural {

// The default no-throw analyzer's logic, as a composable analyzer class:
// along an instruction's no-throw successor edge, refine a dereferenced or
// null-checked source register to non-null.
class DefaultNoThrowAnalyzer final
    : public InstructionAnalyzerBase<DefaultNoThrowAnalyzer,
                                     ConstantEnvironment,
                                     const NullCheckMethods*> {
 public:
  static bool analyze_default(const NullCheckMethods* null_check_methods,
                              const IRInstruction* insn,
                              ConstantEnvironment* env);
};

/*
 * Returns the default no-throw analyzer, which refines source-register values
 * along an instruction's no-throw successor edge. The optional `state` is
 * forwarded to the returned analyzer.
 */
InstructionAnalyzer<ConstantEnvironment> make_default_no_throw_analyzer(
    const NullCheckMethods* null_check_methods = nullptr);

class FixpointIterator final
    : public ir_analyzer::BaseEdgeAwareIRAnalyzer<ConstantEnvironment> {
 public:
  FixpointIterator(const cfg::ControlFlowGraph& cfg,
                   InstructionAnalyzer<ConstantEnvironment> insn_analyzer,
                   InstructionAnalyzer<ConstantEnvironment> no_throw_analyzer =
                       make_default_no_throw_analyzer(),
                   bool imprecise_switches = false);

  void clear_switch_succ_cache() const { m_switch_succs.clear(); }

 protected:
  void analyze_instruction_normal(const IRInstruction* insn,
                                  ConstantEnvironment* env) const override;

  void analyze_if(const IRInstruction* insn,
                  cfg::Edge* const& edge,
                  ConstantEnvironment* env) const override;

  void analyze_switch(const IRInstruction* insn,
                      cfg::Edge* const& edge,
                      ConstantEnvironment* env) const override;

  void analyze_no_throw(const IRInstruction* insn,
                        ConstantEnvironment* env) const override;

 private:
  using SwitchSuccs = UnorderedMap<int32_t, uint32_t>;
  mutable UnorderedMap<cfg::Block*, SwitchSuccs> m_switch_succs;
  InstructionAnalyzer<ConstantEnvironment> m_insn_analyzer;
  InstructionAnalyzer<ConstantEnvironment> m_no_throw_analyzer;
  const bool m_imprecise_switches;

  const SwitchSuccs& find_switch_succs(cfg::Block* block) const {
    auto it = m_switch_succs.find(block);
    if (it == m_switch_succs.end()) {
      std::vector<int32_t> keys;
      for (auto* succ : block->succs()) {
        if (succ->type() == cfg::EDGE_BRANCH) {
          keys.push_back(*succ->case_key());
        }
      }
      std::sort(keys.begin(), keys.end());
      SwitchSuccs switch_succs;
      for (auto key : keys) {
        switch_succs.emplace(key, switch_succs.size());
      }
      it = m_switch_succs.emplace(block, std::move(switch_succs)).first;
    }
    return it->second;
  }

  bool has_switch_consecutive_case_keys(cfg::Block* block,
                                        int32_t min_case_key,
                                        int32_t max_case_key) const {
    always_assert(min_case_key <= max_case_key);
    const auto& succs = find_switch_succs(block);
    auto min_it = succs.find(min_case_key);
    if (min_it == succs.end()) {
      return false;
    }
    auto max_it = succs.find(max_case_key);
    if (max_it == succs.end()) {
      return false;
    }
    always_assert(min_it->second <= max_it->second);
    uint32_t cases_keys = max_it->second - min_it->second;
    int64_t n = (int64_t)max_case_key - min_case_key;
    always_assert(n >= 0 && n < std::numeric_limits<uint32_t>::max());
    return cases_keys == (uint32_t)n;
  }
};

} // namespace intraprocedural

/*
 * Propagates primitive constants and handles simple arithmetic. Also defines
 * an analyze_default implementation that simply sets any modified registers
 * to Top. This sub-analyzer should typically be the last one in any list of
 * combined sub-analyzers.
 */
class PrimitiveAnalyzer final
    : public InstructionAnalyzerBase<PrimitiveAnalyzer, ConstantEnvironment> {
 public:
  static bool analyze_default(const IRInstruction* insn,
                              ConstantEnvironment* env);

  static bool analyze_const(const IRInstruction* insn,
                            ConstantEnvironment* env);

  static bool analyze_move(const IRInstruction* insn, ConstantEnvironment* env);

  static bool analyze_move_result(const IRInstruction* insn,
                                  ConstantEnvironment* env);

  static bool analyze_cmp(const IRInstruction* insn, ConstantEnvironment* env);

  static bool analyze_unop(const IRInstruction* insn, ConstantEnvironment* env);

  static bool analyze_binop_lit(const IRInstruction* insn,
                                ConstantEnvironment* env);

  static bool analyze_binop(const IRInstruction* insn,
                            ConstantEnvironment* env);

  static bool analyze_check_cast(const IRInstruction* insn,
                                 ConstantEnvironment* env);

  static bool analyze_instance_of(const IRInstruction* insn,
                                  ConstantEnvironment* env);
};

class InjectionIdAnalyzer final
    : public InstructionAnalyzerBase<InjectionIdAnalyzer, ConstantEnvironment> {
 public:
  static bool analyze_injection_id(const IRInstruction* insn,
                                   ConstantEnvironment* env);
};

// This is the most common use of constant propagation, so we define this alias
// for our convenience.
using ConstantPrimitiveAnalyzer =
    InstructionAnalyzerCombiner<PrimitiveAnalyzer>;

class ResourceIdAnalyzer final
    : public InstructionAnalyzerBase<ResourceIdAnalyzer, ConstantEnvironment> {
 public:
  static bool analyze_r_const(const IRInstruction* insn,
                              ConstantEnvironment* env);
  static bool analyze_cmp(const IRInstruction* insn, ConstantEnvironment* env);

  static bool analyze_unop(const IRInstruction* insn, ConstantEnvironment* env);

  static bool analyze_binop_lit(const IRInstruction* insn,
                                ConstantEnvironment* env);

  static bool analyze_binop(const IRInstruction* insn,
                            ConstantEnvironment* env);

 private:
  static bool is_src_known(const IRInstruction* insn,
                           ConstantEnvironment* env,
                           src_index_t i);
};

/*
 * Defines default analyses of opcodes that have the potential to let
 * heap-allocated values escape. It sets the escaped values to Top.
 *
 * This Analyzer should typically be used in sequence with other Analyzers
 * that allocate values on the abstract heap.
 */
class HeapEscapeAnalyzer final
    : public InstructionAnalyzerBase<HeapEscapeAnalyzer, ConstantEnvironment> {
 public:
  static bool analyze_sput(const IRInstruction* insn, ConstantEnvironment* env);
  static bool analyze_iput(const IRInstruction* insn, ConstantEnvironment* env);
  static bool analyze_aput(const IRInstruction* insn, ConstantEnvironment* env);
  static bool analyze_invoke(const IRInstruction* insn,
                             ConstantEnvironment* env);
  static bool analyze_filled_new_array(const IRInstruction* insn,
                                       ConstantEnvironment* env);
};

/*
 * Handle non-escaping arrays.
 *
 * This Analyzer should typically be used followed by the
 * HeapEscapeAnalyzer in a combined analysis -- LocalArrayAnalyzer
 * only handles the creation and mutation of array values, but does not account
 * for how they may escape.
 */
class LocalArrayAnalyzer final
    : public InstructionAnalyzerBase<LocalArrayAnalyzer, ConstantEnvironment> {
 public:
  static bool analyze_new_array(const IRInstruction* insn,
                                ConstantEnvironment* env);

  static bool analyze_aget(const IRInstruction* insn, ConstantEnvironment* env);

  static bool analyze_aput(const IRInstruction* insn, ConstantEnvironment* env);

  static bool analyze_fill_array_data(const IRInstruction* insn,
                                      ConstantEnvironment* env);

  static bool analyze_filled_new_array(const IRInstruction* insn,
                                       ConstantEnvironment* env);
};

// State for tracking a class's static fields during its <clinit>.
struct ClinitFieldAnalyzerState {
  const DexType* class_under_init;
  // If this is nullptr, calls invalidate all tracked fields.
  const UnorderedSet<const DexField*>* clinit_only_fields;

  explicit ClinitFieldAnalyzerState(
      const DexType* type = nullptr,
      const UnorderedSet<const DexField*>* fields = nullptr)
      : class_under_init(type), clinit_only_fields(fields) {}
};

// Returns the static fields that no code other than their declaring class's
// <clinit> writes, excluding volatile, external and kept fields. The returned
// set must outlive any analyzer state that refers to it.
UnorderedSet<const DexField*> get_clinit_only_written_fields(
    const Scope& scope);

class ClinitFieldAnalyzer final
    : public InstructionAnalyzerBase<ClinitFieldAnalyzer,
                                     ConstantEnvironment,
                                     ClinitFieldAnalyzerState> {
 public:
  static bool analyze_sget(const ClinitFieldAnalyzerState& state,
                           const IRInstruction* insn,
                           ConstantEnvironment* env);

  static bool analyze_sput(const ClinitFieldAnalyzerState& state,
                           const IRInstruction* insn,
                           ConstantEnvironment* env);

  static bool analyze_invoke(const ClinitFieldAnalyzerState& state,
                             const IRInstruction* insn,
                             ConstantEnvironment* env);
};

/*
 * Models the effects of the sget instructions on static final fields
 */
class StaticFinalFieldAnalyzer final
    : public InstructionAnalyzerBase<StaticFinalFieldAnalyzer,
                                     ConstantEnvironment> {
 public:
  static bool analyze_sget(const IRInstruction* insn, ConstantEnvironment* env);
};

/*
 * Handle instance fields in <init> methods.
 */
class InitFieldAnalyzer final
    : public InstructionAnalyzerBase<InitFieldAnalyzer,
                                     ConstantEnvironment,
                                     DexType* /* class_under_init */> {
 public:
  static bool analyze_iget(const DexType* class_under_init,
                           const IRInstruction* insn,
                           ConstantEnvironment* env);

  static bool analyze_iput(const DexType* class_under_init,
                           const IRInstruction* insn,
                           ConstantEnvironment* env);

  static bool analyze_invoke(const DexType* class_under_init,
                             const IRInstruction* insn,
                             ConstantEnvironment* env);
};

// Construction of this object is expensive because get_method acquires a
// global lock. Make sure to cache it!
struct EnumFieldAnalyzerState {
  const DexMethod* enum_equals;

  EnumFieldAnalyzerState()
      : enum_equals(dynamic_cast<DexMethod*>(DexMethod::get_method(
            "Ljava/lang/Enum;.equals:(Ljava/lang/Object;)Z"))) {}
};

/*
 * EnumFieldAnalyzer::analyze_sget assumes that when it is called to analyze
 * some `sget-object LFoo;.X:LFoo` instruction, the sget instruction is not
 * contained within Foo's class initializer. This means that most users of this
 * analyzer should put it after the ClinitFieldAnalyzer when building the
 * combined analyzer.
 */
class EnumFieldAnalyzer final
    : public InstructionAnalyzerBase<EnumFieldAnalyzer,
                                     ConstantEnvironment,
                                     EnumFieldAnalyzerState> {
 public:
  static bool analyze_sget(const EnumFieldAnalyzerState&,
                           const IRInstruction*,
                           ConstantEnvironment*);
  static bool analyze_invoke(const EnumFieldAnalyzerState&,
                             const IRInstruction*,
                             ConstantEnvironment*);
};

/**
 * Specify how an immutatble field is initialized through function call.
 * For instance, a boxed integer is usually constructed through
 * `Integer.valueOf(I)` invocation with a primitive value, the primitive value
 * can be retrieved through `Integer.intValue()`.
 */
struct ImmutableAttributeAnalyzerState {
  struct Initializer {
    ImmutableAttr::Attr attr;
    size_t insn_src_id_of_attr;
    // The object is passed in as a source register of the method invocation,
    // like `this` pointer of constructor.
    std::optional<size_t> insn_src_id_of_obj = std::nullopt;
    // The object is the return value of the method. Example, Integer.valueOf(I)
    bool obj_is_dest() const { return insn_src_id_of_obj == std::nullopt; }

    explicit Initializer(DexMethod* method_attr) : attr(method_attr) {}
    explicit Initializer(DexField* field_attr) : attr(field_attr) {}

    Initializer& set_src_id_of_attr(size_t id) {
      insn_src_id_of_attr = id;
      return *this;
    }
    Initializer& set_obj_to_dest() {
      insn_src_id_of_obj = std::nullopt;
      return *this;
    }
    Initializer& set_src_id_of_obj(size_t id) {
      insn_src_id_of_obj = id;
      return *this;
    }
  };

  struct CachedBoxedObjects {
    long begin;
    long end;
  };

  ConcurrentMap<DexMethod*, std::vector<std::unique_ptr<Initializer>>>
      method_initializers;
  ConcurrentSet<DexMethod*> attribute_methods;
  ConcurrentSet<DexField*> attribute_fields;
  UnorderedMap<DexMethod*, CachedBoxedObjects> cached_boxed_objects;
  ConcurrentSet<const DexType*> initialized_types;
  mutable InsertOnlyConcurrentMap<const DexType*, bool>
      may_be_initialized_types;

  ImmutableAttributeAnalyzerState();

  // Immutable state should not be updated in parallel with analysis!

  Initializer& add_initializer(DexMethod* initialize_method, DexMethod* attr);
  Initializer& add_initializer(DexMethod* initialize_method, DexField* attr);
  Initializer& add_initializer(DexMethod* initialize_method,
                               const ImmutableAttr::Attr& attr);
  void add_cached_boxed_objects(DexMethod* initialize_method,
                                long begin,
                                long end);
  bool is_jvm_cached_object(DexMethod* initialize_method, long value) const;

  static const DexType* initialized_type(const DexMethod* initialize_method);

  bool may_be_initialized_type(const DexType* type) const;

 private:
  bool compute_may_be_initialized_type(const DexType* type) const;
};

class ImmutableAttributeAnalyzer final
    : public InstructionAnalyzerBase<ImmutableAttributeAnalyzer,
                                     ConstantEnvironment,
                                     ImmutableAttributeAnalyzerState*> {
  static bool analyze_method_initialization(
      const ImmutableAttributeAnalyzerState*,
      const IRInstruction*,
      ConstantEnvironment*,
      DexMethod* method);
  static bool analyze_method_attr(const ImmutableAttributeAnalyzerState*,
                                  const IRInstruction*,
                                  ConstantEnvironment*,
                                  DexMethod* method);

 public:
  static bool analyze_invoke(const ImmutableAttributeAnalyzerState*,
                             const IRInstruction*,
                             ConstantEnvironment*);
  static bool analyze_iget(const ImmutableAttributeAnalyzerState*,
                           const IRInstruction* insn,
                           ConstantEnvironment* env);
};

// Construction of this object is expensive because get_type/field/method
// acquires a global lock. Make sure to cache it.
struct BoxedBooleanAnalyzerState {
  const DexType* boolean_class{DexType::get_type("Ljava/lang/Boolean;")};
  const DexField* boolean_true{dynamic_cast<DexField*>(
      DexField::get_field("Ljava/lang/Boolean;.TRUE:Ljava/lang/Boolean;"))};
  const DexField* boolean_false{dynamic_cast<DexField*>(
      DexField::get_field("Ljava/lang/Boolean;.FALSE:Ljava/lang/Boolean;"))};
  const DexMethod* boolean_valueof{
      dynamic_cast<DexMethod*>(DexMethod::get_method(
          "Ljava/lang/Boolean;.valueOf:(Z)Ljava/lang/Boolean;"))};
  const DexMethod* boolean_booleanvalue{dynamic_cast<DexMethod*>(
      DexMethod::get_method("Ljava/lang/Boolean;.booleanValue:()Z"))};
};

class BoxedBooleanAnalyzer final
    : public InstructionAnalyzerBase<BoxedBooleanAnalyzer,
                                     ConstantEnvironment,
                                     BoxedBooleanAnalyzerState> {
 public:
  static bool analyze_sget(const BoxedBooleanAnalyzerState&,
                           const IRInstruction*,
                           ConstantEnvironment*);
  static bool analyze_invoke(const BoxedBooleanAnalyzerState&,
                             const IRInstruction*,
                             ConstantEnvironment*);
};

struct StringAnalyzerState {
  explicit StringAnalyzerState(const UnorderedSet<DexMethod*>& methods)
      : string_equality_methods(methods) {}

  static StringAnalyzerState make_default();

  void set_methods_as_root();
  UnorderedSet<DexMethod*> string_equality_methods;
};

class StringAnalyzer : public InstructionAnalyzerBase<StringAnalyzer,
                                                      ConstantEnvironment,
                                                      StringAnalyzerState*> {
 public:
  static bool analyze_const_string(const StringAnalyzerState* /*state*/,
                                   const IRInstruction* insn,
                                   ConstantEnvironment* env) {
    env->set(RESULT_REGISTER, StringDomain(insn->get_string()));
    return true;
  }

  static bool analyze_invoke(const StringAnalyzerState* state,
                             const IRInstruction*,
                             ConstantEnvironment*);
};

class ConstantClassObjectAnalyzer
    : public InstructionAnalyzerBase<ConstantClassObjectAnalyzer,
                                     ConstantEnvironment> {
 public:
  static bool analyze_const_class(const IRInstruction* insn,
                                  ConstantEnvironment* env) {
    env->set(RESULT_REGISTER, ConstantClassObjectDomain(insn->get_type()));
    return true;
  }
};

// TODO(T275196808): Remove this once the per-parameter exit-value summary is
// fully rolled out.
extern bool enable_param_exit_value_summary;

// TODO(T279417132): Remove this once the behavior is fully rolled out.
extern bool enable_check_cast_value_preservation;

/*
 * Marks return values of well-known external methods as non-null (NEZ).
 * This enables elimination of redundant Kotlin null-check intrinsics
 * (e.g. checkNotNullExpressionValue) after calls to these methods.
 */
class KnownNonNullReturnsAnalyzer
    : public InstructionAnalyzerBase<KnownNonNullReturnsAnalyzer,
                                     ConstantEnvironment> {
 public:
  static bool analyze_invoke(const IRInstruction* insn,
                             ConstantEnvironment* env);
};

// Construction of this object is expensive because get_method acquires a
// global lock. Make sure to cache it!
struct ApiLevelAnalyzerState {
  explicit ApiLevelAnalyzerState(int32_t min_sdk);

  const DexFieldRef* sdk_int_field;
  int32_t min_sdk;
};

class ApiLevelAnalyzer final
    : public InstructionAnalyzerBase<ApiLevelAnalyzer,
                                     ConstantEnvironment,
                                     ApiLevelAnalyzerState> {
 public:
  static bool analyze_sget(const ApiLevelAnalyzerState& state,
                           const IRInstruction* insn,
                           ConstantEnvironment* env);
};

struct PackageNameState {
  const UnorderedSet<DexMethodRef*> getter_methods;
  const DexString* package_name;

  static PackageNameState make(const std::optional<std::string>& package_name);
};

class PackageNameAnalyzer final
    : public InstructionAnalyzerBase<PackageNameAnalyzer,
                                     ConstantEnvironment,
                                     PackageNameState*> {
 public:
  static bool analyze_invoke(const PackageNameState* state,
                             const IRInstruction* insn,
                             ConstantEnvironment* env);
};

class NewObjectAnalyzer
    : public InstructionAnalyzerBase<NewObjectAnalyzer,
                                     ConstantEnvironment,
                                     ImmutableAttributeAnalyzerState*> {
  static bool ignore_type(const ImmutableAttributeAnalyzerState* state,
                          const DexType* type);

 public:
  static bool analyze_new_instance(const ImmutableAttributeAnalyzerState* state,
                                   const IRInstruction* insn,
                                   ConstantEnvironment* env);
  static bool analyze_filled_new_array(
      const ImmutableAttributeAnalyzerState* state,
      const IRInstruction* insn,
      ConstantEnvironment* env);
  static bool analyze_new_array(const ImmutableAttributeAnalyzerState* state,
                                const IRInstruction* insn,
                                ConstantEnvironment* env);
  static bool analyze_instance_of(const ImmutableAttributeAnalyzerState*,
                                  const IRInstruction* insn,
                                  ConstantEnvironment* env);
  static bool analyze_array_length(const ImmutableAttributeAnalyzerState*,
                                   const IRInstruction* insn,
                                   ConstantEnvironment* env);
};

/*
 * Utility methods.
 */

/*
 * runtime_equals_visitor and runtime_leq_visitor are handling different
 * notions of equality / order than AbstractDomain::equals() and
 * AbstractDomain::leq(). The former return true if they can prove that their
 * respective relations hold for a runtime comparison (e.g. from an if-eq or
 * packed-switch instruction). In contrast, AbstractDomain::equals() will
 * return true for two domains representing integers > 0, even though their
 * corresponding runtime values may be different integers.
 */
class runtime_equals_visitor : public boost::static_visitor<bool> {
 public:
  bool operator()(const SignedConstantDomain& scd_left,
                  const SignedConstantDomain& scd_right) const {
    auto cst_left = scd_left.get_constant();
    auto cst_right = scd_right.get_constant();
    if (!(cst_left && cst_right)) {
      return false;
    }
    return *cst_left == *cst_right;
  }

  // SingletonObjectDomain and StringDomains are equal iff their respective
  // constants are equal.
  template <typename Constant,
            typename = typename std::enable_if_t<
                template_util::contains<Constant,
                                        const DexField*,
                                        const DexString*,
                                        const DexType*>::value>>
  bool operator()(const sparta::ConstantAbstractDomain<Constant>& d1,
                  const sparta::ConstantAbstractDomain<Constant>& d2) const {
    if (!(d1.is_value() && d2.is_value())) {
      return false;
    }
    return *d1.get_constant() == *d2.get_constant();
  }

  bool operator()(const ObjectWithImmutAttrDomain& d1,
                  const ObjectWithImmutAttrDomain& d2) const {
    if (!(d1.is_value() && d2.is_value())) {
      return false;
    }
    return d1.get_constant()->runtime_equals(*d2.get_constant()) ==
           TriState::True;
  }

  template <typename Domain, typename OtherDomain>
  bool operator()(const Domain& /*d1*/, const OtherDomain& /*d2*/) const {
    return false;
  }
};

class runtime_leq_visitor : public boost::static_visitor<bool> {
 public:
  bool operator()(const SignedConstantDomain& scd_left,
                  const SignedConstantDomain& scd_right) const {
    return scd_left.max_element() <= scd_right.min_element();
  }

  template <typename Domain, typename OtherDomain>
  bool operator()(const Domain& /*d1*/, const OtherDomain& /*d2*/) const {
    return false;
  }
};

/*
 * Note: We cannot replace the runtime_lt_visitor by combining the
 * runtime_leq_visitor and the negation of the runtime_equals_visitor. Suppose
 * the runtime_leq_visitor returns true and the runtime_equals_visitor returns
 * false. That means that the LHS must be less than or equal to the RHS, and
 * that they *might* not be equal. Since they may still be equal, we cannot
 * conclude that the LHS must be less than the RHS.
 */
class runtime_lt_visitor : public boost::static_visitor<bool> {
 public:
  bool operator()(const SignedConstantDomain& scd_left,
                  const SignedConstantDomain& scd_right) const {
    return scd_left.max_element() < scd_right.min_element();
  }

  template <typename Domain, typename OtherDomain>
  bool operator()(const Domain& /*d1*/, const OtherDomain& /*d2*/) const {
    return false;
  }
};

/*
 * Analyze the invoke instruction given by :insn by running an abstract
 * interpreter on the :callee_code with the provided arguments. By analyzing the
 * callee with the exact arguments at this callsite -- instead of the join of
 * the arguments at every possible callsites -- we can get more precision in the
 * return value / final heap state of the invoke.
 *
 * :env should represent the ConstantEnvironment at the point before the invoke
 * instruction gets executed. semantically_inline_method will update :env to
 * reflect the ConstantEnvironment at the point after the invoke instruction
 * has finished executing.
 *
 * Note that this method will not recursively inline invocations within
 * :callee_code. We can extend it to support that in the future.
 */
void semantically_inline_method(
    IRCode* callee_code,
    const IRInstruction* insn,
    const InstructionAnalyzer<ConstantEnvironment>& analyzer,
    ConstantEnvironment* env);

/*
 * Do a join over the states at each return opcode in a method.
 */
ReturnState collect_return_state(IRCode* code,
                                 const intraprocedural::FixpointIterator&);

/*
 * Get source argument index, if any, which is getting dereferenced by an
 * instruction. A null object would cause an exception to be thrown.
 */
std::optional<size_t> get_dereferenced_object_src_index(const IRInstruction*);

/*
 * Handle reading of static fields fXXX in $EnumUtils class.
 */
class EnumUtilsFieldAnalyzer final
    : public InstructionAnalyzerBase<EnumUtilsFieldAnalyzer,
                                     ConstantEnvironment,
                                     ImmutableAttributeAnalyzerState*> {
 public:
  static bool analyze_sget(ImmutableAttributeAnalyzerState* state,
                           const IRInstruction* insn,
                           ConstantEnvironment* env);
};

using ConstantPrimitiveAndBoxedAnalyzer =
    InstructionAnalyzerCombiner<EnumUtilsFieldAnalyzer,
                                ImmutableAttributeAnalyzer,
                                EnumFieldAnalyzer,
                                BoxedBooleanAnalyzer,
                                StringAnalyzer,
                                ApiLevelAnalyzer,
                                PackageNameAnalyzer,
                                ConstantClassObjectAnalyzer,
                                NewObjectAnalyzer,
                                KnownNonNullReturnsAnalyzer,
                                PrimitiveAnalyzer>;

} // namespace constant_propagation
