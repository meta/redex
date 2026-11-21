/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <functional>
#include <optional>

#include "ConstantUses.h"
#include "DeterministicContainers.h"
#include "IRInstruction.h"
#include "Lazy.h"
#include "LiveRange.h"
#include "PartialCandidates.h"
#include "ReachingDefinitions.h"
#include "TypeInference.h"

namespace outliner_impl {

using TypeEnvironments =
    UnorderedMap<const IRInstruction*, type_inference::TypeEnvironment>;

using ReachingDefsEnvironments =
    UnorderedMap<const IRInstruction*, reaching_defs::Environment>;

// The type ART's verifier gives an integral register.
//
// ART types each value by its definition: a constant by its value, any other
// producer by its result type. Where several values reach a point, ART merges
// their types pairwise, in whatever order it visits the paths
// (`RegType::Merge`). The merge is not associative. `boolean` and 65 merge into
// `byte`, which 40000 then takes to `int`. But 65 and 40000 first merge into a
// constant, which `boolean` then takes to `char`.
//
// So an `IntegralType` keeps what each value contributes, as a set of ART types
// of single values. `type()` answers the least type above the merge of that set
// in EVERY order. `exact_type()` answers the type all orders end at, if they
// agree. `join` is the union of the sets, so the type of a union never depends
// on how its parts were grouped.
//
// A constant is kept as the set of integral types that hold it, because that
// is all ART's merge looks at. To the merge, 65 and 74 are the same constant:
// each merges with a `byte` into a `byte` and with a `char` into a `char`.
class IntegralType {
 public:
  // The type of a value of the integral type `t`.
  static IntegralType of(const DexType* t);
  // The type of the constant `value`.
  static IntegralType constant(int64_t value);

  // The value of a register that may hold a value of `a` or of `b`.
  static IntegralType join(const IntegralType& a, const IntegralType& b);
  // `b` when nothing has accumulated in `a` yet, else their join.
  static IntegralType join(const std::optional<IntegralType>& a,
                           const IntegralType& b) {
    return a ? join(*a, b) : b;
  }

  // Whether only constants contribute: ART types the register by their values,
  // and no single type stands for them.
  bool is_constant() const { return m_types == 0; }
  // The least integral type above every merge order; nullptr for a constant.
  const DexType* type() const;
  // The type every merge order ends at, or nullptr when the order decides the
  // type (a `boolean`, a `char` and 2 end at `char` or `int`) or for a
  // constant.
  const DexType* exact_type() const;
  // Whether ART accepts this value wherever it accepts `bound`. Against a
  // typed `bound`, this value's `type()` must be at or below `bound`'s type;
  // when this value is a constant, `bound`'s type must hold it instead.
  // Against a constant `bound`, this value must be a constant that every type
  // holding `bound` also holds.
  bool leq(const IntegralType& bound) const;
  // Whether `t` holds every value: ART accepts this value where `t` is
  // demanded.
  bool held_by(const DexType* t) const { return leq(of(t)); }

  bool operator==(const IntegralType& o) const {
    return m_types == o.m_types && m_constants == o.m_constants;
  }

 private:
  IntegralType(uint8_t types, uint16_t constants)
      : m_types(types), m_constants(constants) {}
  // Bit `k` of `m_types` stands for a value of the k-th of Z, B, S, C, I. Bit
  // `m` of `m_constants` stands for a constant held by exactly the types in the
  // mask `m` over Z, B, S, C (`int` holds every constant).
  uint8_t m_types;
  uint16_t m_constants;
};

// Outlined code declares a type for every value that crosses its boundary.
// That type must be at or above what reaches the register and at or below
// what its uses accept. `art::Value` models what reaches the register, a join
// over its definitions. `art::Demand` models what its uses accept, a meet over
// its uses. `OutlinerTypeAnalysis` computes both, and the role policies below
// pick the declared type.
namespace art {

// What ART's verifier may hold in a register: the type of every producer and
// every constant that reaches it, each one register wide or a wide pair.
// `join` keeps each contribution; `upper()` resolves them into one type.
class Value {
 public:
  // No value reaches the register.
  Value() = default;
  static Value unknown();
  // A value of type `t`, the result type of its producer; unknown for nullptr.
  static Value of_type(const DexType* t);
  // The value of a `const` or `const-wide`.
  static Value constant(const IRInstruction* insn);
  // This value, to which only constants contribute, given the type `t` that the
  // uses of those constants need. The constants keep their widths.
  Value typed_by_uses(const DexType* t) const;

  void join_with(const Value& other);

  // The integral types and constants that contribute, when nothing else does:
  // no unknown, wide, reference or floating-point value.
  std::optional<IntegralType> integral() const;

  // Whether constants contribute and nothing else does: no producer gives
  // the register a type.
  bool is_constant() const;
  // The type of the register, at or above every contribution; nullptr when
  // a contribution is unknown, no type holds them all, or only constants
  // contribute. No type holds a one-register value beside a wide pair, such
  // as a `const 0` beside a `long`.
  const DexType* upper() const;
  // `upper()` when every order in which ART may merge the contributions ends
  // at that type, else nullptr (`IntegralType::exact_type`).
  const DexType* exact() const;

 private:
  friend bool accepts_argument(const DexType* parameter, const Value& passed);

  bool m_unknown{false};
  // The integral producers.
  std::optional<IntegralType> m_integral;
  // Bit k: a value of the k-th of `float`, `long`, `double`.
  uint8_t m_primitives{0};
  // The other types contributing: classes and arrays.
  UnorderedSet<const DexType*> m_references;
  std::optional<IntegralType> m_constants;
  bool m_wide_constant{false};
  bool m_narrow_constant{false};
};

// What the uses of a register require of it: the type each use demands.
// `meet_with` keeps each demand; `widest()` resolves them into one type.
class Demand {
 public:
  // No use demands anything.
  Demand() = default;
  static Demand unknown();
  // A use requiring `t`; unknown for nullptr.
  static Demand of_use(const DexType* t);

  void meet_with(const Demand& other);
  // Given this demand on the result of an `and`, `or` or `xor`, the demand it
  // places on each operand. ART types such an operation as boolean when every
  // operand is boolean, and as int otherwise. Of those two types, only
  // boolean is assignable to a `boolean`, `byte`, `short` or `char` demand.
  // So a narrow demand on the result is met only by boolean operands, while
  // an `int` demand is met by any integral operand.
  Demand through_bitwise() const;

  bool is_none() const;
  // The widest type every use accepts; nullptr when a demand is unknown, there
  // is no use, or no one type is accepted by every use: two classes or
  // categories, or `char` beside `byte` or `short`.
  const DexType* widest() const;
  // Whether every use accepts the integral value `value`: every integral type a
  // use needs holds it, so with no use any value is accepted. A use that needs
  // any other type accepts no integral value. ART would take a constant at a
  // `float` use, and 0 at a reference use, but this answers no for those too.
  // When the type a use needs is unknown, nothing is accepted.
  bool accepts(const IntegralType& value) const;

 private:
  bool m_unknown{false};
  uint8_t m_integral{0};
  uint8_t m_primitives{0};
  UnorderedSet<const DexType*> m_references;
};

// The type of a value passed into outlined code: the widest type every use
// accepts, so that the signature does not depend on what one caller holds.
// When the uses do not determine a type, the type of the value `supply` gives.
const DexType* declare_parameter(const Demand& uses,
                                 const std::function<Value()>& supply);

// Whether a parameter declared `parameter` holds `passed`, every value its
// call passes, in every order in which ART may merge them. The call may pass
// fewer values than the uses were verified with: when the entry is a loop
// header whose back edge moves into the split, the call passes only the
// values that reach the header from before the loop. Each is still at or
// below the merge the uses were verified with. Only for an integral parameter
// and for an array of interfaces does merge order change the answer; any
// other parameter accepts a value of its kind (a reference for a reference,
// a `float` for a `float`) in any order. A parameter that is an array of an
// interface, or of a class Redex cannot see, is taken to hold only values of
// exactly its type, or null; an unknown value is refused only there and at an
// integral parameter. `passed` must list each value, not a join of them.
[[nodiscard]] bool accepts_argument(const DexType* parameter,
                                    const Value& passed);

// The type to declare for a value passed into outlined code, or nullopt to
// refuse the value; never nullptr. For an integral value it is never wider than
// the type the caller holds, so a value the outlined code passes on keeps the
// integral type ART gave it in the caller. `declare_parameter`, by contrast,
// may widen a `char` to the `int` its uses accept.
//
//  - No use needs a type (the value is only passed on): the type of the value.
//    A value defined only by constants has no single type, and `int` holds any
//    of them. A value whose type cannot be told (an unknown contribution, or
//    several without a common type), or that the type does not hold
//    (`accepts_argument`), is refused.
//  - The uses have a widest type: refuse a value it does not hold
//    (`accepts_argument`). Otherwise declare the type of an integral value that
//    is not only constants, and else that widest type. The type of the value is
//    the least type above every order in which ART may merge its definitions,
//    because outlined code need not keep the order ART verified the caller
//    with.
//  - The uses have no widest type, or the type a use needs is unknown: refuse.
//    No declared type satisfies the uses.
//
// `supply` gives the value that reaches the register at the call, as the caller
// holds it; it is called only when the uses do not refuse the value.
std::optional<const DexType*> declare_parameter_preferring_supply(
    const Demand& uses, const std::function<Value()>& supply);

// The type of a value outlined code gives back. The caller's code after the
// call was verified against the one type ART gave the register, so only a
// type that every merge order ends at may be declared.
const DexType* declare_result(const Value& returned);

} // namespace art

// Instructions of a method that a candidate covers.
using Membership = std::function<bool(IRInstruction*)>;

class OutlinerTypeAnalysis {
 public:
  OutlinerTypeAnalysis() = delete;
  OutlinerTypeAnalysis(const OutlinerTypeAnalysis&) = delete;
  OutlinerTypeAnalysis& operator=(const OutlinerTypeAnalysis&) = delete;
  explicit OutlinerTypeAnalysis(DexMethod* method);

  // The value of a register that `assignments` write, joined with
  // `incoming`, the value it holds on a path through none of them. A move or
  // move-result stands for the definitions of what it copies; when those are
  // unknown, the value is `incoming` alone. A register that only constants
  // define is typed by the uses of the constants outside `candidate`.
  art::Value value_of_assignments(
      const UnorderedSet<const IRInstruction*>& assignments,
      const std::optional<art::Value>& incoming,
      const Membership& candidate = {});

  // The value of `reg` where `anchor` reads it, typed for a declaration: its
  // `supply_at`, except that a declared type is one type, not a set of values.
  // So a reference takes the type that type inference gives the register, and
  // a register only constants define takes a type from how the constants are
  // used.
  art::Value value_at(const IRInstruction* anchor, reg_t reg);

  // What reaches `reg` where `anchor` reads it, with constants kept as
  // constants: the join of its definitions as ART types them
  // (`value_of_producers`). A reference keeps the value of each producer too,
  // where its producers are known: ART merges arrays whose elements share an
  // interface to `Object[]`, wider than type inference's join of them, and
  // `art::accepts_argument` must see each value. Floating-point and wide
  // values take the type that type inference gives the register. A register
  // that only constants define keeps those constants where their uses take
  // them as integral values; a literal used as a float, a wide value or null
  // takes that type, and a literal whose uses have no common type is unknown.
  art::Value supply_at(const IRInstruction* anchor, reg_t reg);

  // What reaches a register that `defs` define, with constants kept as
  // constants: the join of the value of each producer as ART types it. A move
  // or move-result stands for the producers of what it copies; the value is
  // unknown when those are not known. ART types a constant by its value, an
  // `and`, `or` or `xor` as `boolean` when every operand is boolean and as
  // `int` otherwise, and any other producer by its result type.
  art::Value value_of_producers(const UnorderedSet<const IRInstruction*>& defs);

  // What the instructions of `pc` require of the value `reg` holds on entry.
  // `result` is the register the candidate gives back, with its declared type.
  art::Demand demand_in_candidate(
      const PartialCandidate& pc,
      reg_t reg,
      const std::optional<std::pair<reg_t, const DexType*>>& result);

  // What the uses within `scope` require of the values `seeds` define, through
  // moves and the bitwise operations that can keep a boolean.
  art::Demand demand_of_uses(
      const sparta::PatriciaTreeSet<IRInstruction*>& seeds,
      const Membership& scope);

  // The definitions of `reg` that reach `anchor`, through moves.
  sparta::PatriciaTreeSet<IRInstruction*> defs_at(const IRInstruction* anchor,
                                                  reg_t reg);
  // The definitions of `reg` that reach `anchor`; a move is a definition.
  sparta::PatriciaTreeSet<IRInstruction*> immediate_defs_at(
      const IRInstruction* anchor, reg_t reg);

 private:
  DexMethod* m_method;
  Lazy<ReachingDefsEnvironments> m_reaching_defs_environments;
  Lazy<live_range::Chains> m_immediate_chains;
  Lazy<ReachingDefsEnvironments> m_immediate_reaching_defs_environments;
  Lazy<live_range::DefUseChains> m_immediate_def_uses;
  Lazy<TypeEnvironments> m_type_environments;
  Lazy<constant_uses::ConstantUses> m_constant_uses;
  // Whether each `and`, `or` and `xor` analysed so far is boolean (true) or
  // int (false); nullopt when the type of an operand is unknown.
  UnorderedMap<const IRInstruction*, std::optional<bool>> m_bitwise_booleanness;

  art::Demand demand_of_use(IRInstruction* use, src_index_t src_index);

  // Whether ART types `reg` as null where `insn` reads it: every definition
  // that reaches it is null to ART.
  bool is_null_to_art(const IRInstruction* insn, reg_t reg);

  size_t get_load_param_index(const IRInstruction* load_param_insn);

  const DexType* get_result_type_helper(const IRInstruction* insn);

  const DexType* get_if_insn_type_demand(IRInstruction* insn);

  const DexType* get_type_demand(IRInstruction* insn, size_t src_index);

  std::optional<UnorderedSet<const IRInstruction*>> get_defs(
      const UnorderedSet<const IRInstruction*>& insns);

  // The definitions of `reg` that reach `anchor`; nullopt when they are not
  // known (bottom or top).
  std::optional<UnorderedSet<const IRInstruction*>> known_defs_at(
      const IRInstruction* anchor, reg_t reg);

  const DexType* get_const_insns_type_demand(
      const Membership& candidate,
      const UnorderedSet<const IRInstruction*>& const_insns);

  // The value of the producer `def`, after moves and move-results have been
  // traced back to it. A constant gives its own value, an `and`, `or` or `xor`
  // the type `get_bitwise_booleanness` gives it, and any other producer its
  // result type.
  art::Value value_of_def(const IRInstruction* def);
  std::optional<bool> get_bitwise_booleanness(const IRInstruction* bitwise);

  art::Value value_of_defs(const UnorderedSet<const IRInstruction*>& defs,
                           art::Value value,
                           const Membership& candidate);
}; // class OutlinerTypeAnalysis

} // namespace outliner_impl
