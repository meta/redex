/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include <array>
#include <bit>
#include <functional>
#include <set>
#include <string>
#include <vector>

#include "Creators.h"
#include "Debug.h"
#include "IRAssembler.h"
#include "Lazy.h"
#include "OutlinerTypeAnalysis.h"
#include "RedexTest.h"
#include "ReducedControlFlow.h"
#include "Show.h"

class OutlinerTypeAnalysisTest : public RedexTest {};

using method_splitting_impl::ReducedBlock;
using method_splitting_impl::ReducedControlFlowGraph;

using outliner_impl::OutlinerTypeAnalysis;
namespace art = outliner_impl::art;

// The result type the outliner declares for a register that `insns` assign,
// with `optional_extra_type` its type on a path through none of them.
static const DexType* get_result_type(
    OutlinerTypeAnalysis& ota,
    const UnorderedSet<const IRInstruction*>& insns,
    const DexType* optional_extra_type) {
  std::optional<art::Value> incoming;
  if (optional_extra_type != nullptr) {
    incoming = art::Value::of_type(optional_extra_type);
  }
  return art::declare_result(ota.value_of_assignments(insns, incoming));
}

namespace {

struct Candidate {
  OutlinerTypeAnalysis& ota;
  outliner_impl::PartialCandidate pc;
  std::optional<std::pair<reg_t, const DexType*>> result;

  void set_result(reg_t reg, const DexType* type) { result.emplace(reg, type); }
};

} // namespace

// The type of `reg` on entry to `candidate`, declared as a parameter or, when
// `as_result`, as a result.
static const DexType* get_inferred_type(const Candidate& candidate,
                                        reg_t reg,
                                        bool as_result = false) {
  auto value = candidate.ota.value_at(candidate.pc.root.insns.front(), reg);
  return as_result ? art::declare_result(value) : value.upper();
}

// The parameter type the outliner declares for `reg` in `candidate`.
static const DexType* get_type_demand(const Candidate& candidate, reg_t reg) {
  return art::declare_parameter(
      candidate.ota.demand_in_candidate(candidate.pc, reg, candidate.result),
      [&]() {
        return candidate.ota.value_at(candidate.pc.root.insns.front(), reg);
      });
}

static IRInstruction* find_insn(
    DexMethod* method,
    const std::function<bool(IRInstruction*)>& predicate,
    size_t occurrence = 1) {
  always_assert(occurrence > 0);
  for (const auto& mie : InstructionIterable(method->get_code()->cfg())) {
    if (predicate(mie.insn) && --occurrence == 0) {
      return mie.insn;
    }
  }
  not_reached();
}

static IRInstruction* find_insn(DexMethod* method,
                                IROpcode opcode,
                                size_t occurrence = 1) {
  return find_insn(
      method,
      [opcode](IRInstruction* insn) { return insn->opcode() == opcode; },
      occurrence);
}

TEST_F(OutlinerTypeAnalysisTest, get_result_type_primitive) {
  auto* foo_method = assembler::method_from_string(R"(
      (method (public static) "LFoo;.foo:(IZ)V" (
        (load-param v1)
        (load-param v2)
        (add-int v1 v1 v1)
        (move v1 v1)
        (or-int v1 v1 v1)
        (xor-int v2 v2 v2)
        (return-void)
      )))");
  foo_method->get_code()->build_cfg();
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  {
    // result type of 'add-int' is int
    auto* insn = find_insn(foo_method, OPCODE_ADD_INT);
    const auto* result_type =
        get_result_type(ota, {insn}, /* optional_extra_type */ nullptr);
    EXPECT_EQ(result_type, type::_int());
  }

  {
    // result type of 'move' of 'add-int' is int
    auto* insn = find_insn(foo_method, OPCODE_MOVE);
    const auto* result_type =
        get_result_type(ota, {insn}, /* optional_extra_type */ nullptr);
    EXPECT_EQ(result_type, type::_int());
  }

  {
    // result type of 'or-int' of 'move' of 'add-int' is int
    auto* insn = find_insn(foo_method, OPCODE_OR_INT);
    const auto* result_type =
        get_result_type(ota, {insn}, /* optional_extra_type */ nullptr);
    EXPECT_EQ(result_type, type::_int());
  }

  {
    // result type of first 'load-param' is int due to method signature
    auto* insn = find_insn(foo_method, IOPCODE_LOAD_PARAM);
    const auto* result_type =
        get_result_type(ota, {insn}, /* optional_extra_type */ nullptr);
    EXPECT_EQ(result_type, type::_int());
  }

  {
    // result type of second 'load-param' is boolean due to method signature
    auto* insn = find_insn(foo_method, IOPCODE_LOAD_PARAM, 2);
    const auto* result_type =
        get_result_type(ota, {insn}, /* optional_extra_type */ nullptr);
    EXPECT_EQ(result_type, type::_boolean());
  }

  {
    // result type of 'xor-int' of boolean 'load-param' is boolean
    auto* insn = find_insn(foo_method, OPCODE_XOR_INT);
    const auto* result_type =
        get_result_type(ota, {insn}, /* optional_extra_type */ nullptr);
    EXPECT_EQ(result_type, type::_boolean());
  }

  {
    // the combined result type of int and boolean is int
    auto* insn1 = find_insn(foo_method, IOPCODE_LOAD_PARAM);
    auto* insn2 = find_insn(foo_method, IOPCODE_LOAD_PARAM, 2);
    const auto* result_type =
        get_result_type(ota, {insn1, insn2},
                        /* optional_extra_type */ nullptr);
    EXPECT_EQ(result_type, type::_int());
  }

  {
    // the combined result type of boolean and the optional_extra_type int is
    // int
    auto* insn = find_insn(foo_method, IOPCODE_LOAD_PARAM);
    const auto* result_type =
        get_result_type(ota, {insn}, /* optional_extra_type */ type::_int());
    EXPECT_EQ(result_type, type::_int());
  }
}

// ART's verifier types `and`, `or` and `xor` as boolean only when every operand
// is boolean, that is, a boolean value or the literal 0 or 1. Otherwise it
// types them as int. Any other answer for a mixed bitwise operation is a type
// that no consumer of the result can rely on. For example, claiming `char` for
// an `and-int` of a `char` and a `boolean` makes an outlined method return, or
// pass on, a value that ART types as int where `char` is declared.
TEST_F(OutlinerTypeAnalysisTest, get_result_type_bitwise) {
  auto* foo_method = assembler::method_from_string(R"(
      (method (public static) "LFoo;.foo:(CZ)V" (
        (load-param v0)
        (load-param v1)
        (and-int v2 v0 v1)
        (or-int v3 v1 v1)
        (and-int/lit v4 v0 1)
        (xor-int/lit v5 v1 1)
        (const v6 5)
        (const v7 1)
        (xor-int v8 v1 v6)
        (or-int v9 v1 v7)
        (and-int v10 v2 v1)
        (or-int v11 v3 v5)
        (return-void)
      )))");
  foo_method->get_code()->build_cfg();
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  auto result_type = [&](IROpcode op, size_t occurrence) {
    auto* insn = find_insn(foo_method, op, occurrence);
    return get_result_type(ota, {insn},
                           /* optional_extra_type */ nullptr);
  };
  // `char` & `boolean`
  EXPECT_EQ(result_type(OPCODE_AND_INT, 1), type::_int());
  // `boolean` | `boolean`
  EXPECT_EQ(result_type(OPCODE_OR_INT, 1), type::_boolean());
  // `char` & 1
  EXPECT_EQ(result_type(OPCODE_AND_INT_LIT, 1), type::_int());
  // `boolean` ^ 1
  EXPECT_EQ(result_type(OPCODE_XOR_INT_LIT, 1), type::_boolean());
  // `boolean` ^ 5
  EXPECT_EQ(result_type(OPCODE_XOR_INT, 1), type::_int());
  // `boolean` | 1
  EXPECT_EQ(result_type(OPCODE_OR_INT, 2), type::_boolean());
  // (`char` & `boolean`) & `boolean`
  EXPECT_EQ(result_type(OPCODE_AND_INT, 2), type::_int());
  // (`boolean` | `boolean`) | (`boolean` ^ 1)
  EXPECT_EQ(result_type(OPCODE_OR_INT, 3), type::_boolean());
}

// ART types a constant by its value, however the constant is used, and merges
// it with the register's typed definitions.
TEST_F(OutlinerTypeAnalysisTest, get_result_type_types_constants_by_value) {
  auto* foo_method = assembler::method_from_string(R"(
      (method (public static) "LFoo;.foo:(ZC)V" (
        (load-param v0)
        (load-param v1)
        (const v2 65)
        (const v3 74)
        (const v4 1)
        (const v8 40000)
        (invoke-static (v2) "LFoo;.takeChar:(C)V")
        (add-int v5 v3 v3)
        (and-int v6 v0 v4)
        (and-int v7 v1 v4)
        (return-void)
      )))");
  foo_method->get_code()->build_cfg();
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);
  auto type = [&](std::initializer_list<std::pair<IROpcode, size_t>> defs) {
    UnorderedSet<const IRInstruction*> set;
    for (const auto& [op, occurrence] : defs) {
      set.insert(find_insn(foo_method, op, occurrence));
    }
    return get_result_type(ota, set, nullptr);
  };
  // 65 is used as a `char`, 74 as an `int`; `char` holds both.
  EXPECT_EQ(type({{OPCODE_CONST, 1}, {IOPCODE_LOAD_PARAM, 2}}), type::_char());
  EXPECT_EQ(type({{OPCODE_CONST, 2}, {IOPCODE_LOAD_PARAM, 2}}), type::_char());
  EXPECT_EQ(type({{OPCODE_CONST, 3}, {IOPCODE_LOAD_PARAM, 1}}),
            type::_boolean());
  // A `boolean` and 65 merge into `byte`.
  EXPECT_EQ(type({{OPCODE_CONST, 1}, {IOPCODE_LOAD_PARAM, 1}}), type::_byte());
  // `boolean` & 1 is boolean, `char` & 1 is int.
  EXPECT_EQ(type({{OPCODE_AND_INT, 1}}), type::_boolean());
  EXPECT_EQ(type({{OPCODE_AND_INT, 2}}), type::_int());
}

TEST_F(OutlinerTypeAnalysisTest, integral_type_join_and_order) {
  using IT = outliner_impl::IntegralType;
  auto k = [](int64_t v) { return IT::constant(v); };
  auto t = [](const DexType* type) { return IT::of(type); };
  auto join = [](std::initializer_list<IT> values) {
    std::optional<IT> joined;
    for (const auto& v : values) {
      joined = IT::join(joined, v);
    }
    return *joined;
  };
  EXPECT_TRUE(join({k(65), k(-3)}).is_constant());
  EXPECT_EQ(join({k(65), t(type::_char())}).type(), type::_char());
  EXPECT_EQ(join({k(65), t(type::_byte())}).type(), type::_byte());
  EXPECT_EQ(join({k(200), t(type::_byte())}).type(), type::_short());
  EXPECT_EQ(join({k(40000), t(type::_boolean())}).type(), type::_char());
  EXPECT_EQ(join({k(65), t(type::_boolean())}).type(), type::_byte());
  EXPECT_EQ(join({k(-1), t(type::_char())}).type(), type::_int());
  EXPECT_EQ(join({k(40000), t(type::_short())}).type(), type::_int());
  // ART merges 65 with a `boolean` into `byte`, which a `char` takes to `int`;
  // in the other orders the result is `char`. Only `int` holds in all.
  EXPECT_EQ(join({k(65), t(type::_boolean()), t(type::_char())}).type(),
            type::_int());
  EXPECT_EQ(join({k(65), t(type::_boolean()), t(type::_char())}).exact_type(),
            nullptr);
  EXPECT_EQ(join({k(65), k(40000), t(type::_boolean())}).type(), type::_int());
  EXPECT_EQ(join({k(65), k(40000), t(type::_boolean())}).exact_type(), nullptr);
  // Every order merges a `boolean` and 2 into `byte`, and a `byte` and 200
  // into `short`.
  EXPECT_EQ(join({k(2), t(type::_boolean())}).exact_type(), type::_byte());
  EXPECT_EQ(join({k(200), t(type::_byte())}).exact_type(), type::_short());
  EXPECT_EQ(join({k(65), k(74)}).exact_type(), nullptr);
  EXPECT_EQ(join({t(type::_short()), t(type::_char())}).type(), type::_int());
  EXPECT_EQ(join({t(type::_boolean()), t(type::_char())}).type(),
            type::_char());
  // The join is a union: grouping does not change the type.
  EXPECT_EQ(IT::join(join({k(65), t(type::_char())}), t(type::_boolean())),
            join({k(65), t(type::_char()), t(type::_boolean())}));

  EXPECT_TRUE(join({k(65), k(74)}).held_by(type::_char()));
  EXPECT_TRUE(join({k(65), k(74)}).held_by(type::_byte()));
  EXPECT_FALSE(join({k(-1), k(74)}).held_by(type::_char()));
  EXPECT_FALSE(t(type::_char()).leq(join({k(0), k(65535)})));
  EXPECT_TRUE(join({k(1), k(2)}).leq(join({k(0), k(65535)})));
  EXPECT_FALSE(join({k(1), k(40000)}).leq(join({k(0), k(65)})));
  EXPECT_TRUE(t(type::_byte()).leq(t(type::_short())));
  EXPECT_FALSE(t(type::_byte()).leq(t(type::_char())));

  art::Demand demand;
  EXPECT_EQ(demand.widest(), nullptr);
  demand.meet_with(art::Demand::of_use(type::_int()));
  EXPECT_EQ(demand.widest(), type::_int());
  demand.meet_with(art::Demand::of_use(type::_short()));
  EXPECT_EQ(demand.widest(), type::_short());
  demand.meet_with(art::Demand::of_use(type::_char()));
  EXPECT_EQ(demand.widest(), nullptr);
}

// Which integral types hold a constant, at every edge of their ranges: `int`
// holds each value, and `boolean`, `byte`, `short` and `char` exactly those in
// [0, 1], [-128, 127], [-32768, 32767] and [0, 65535].
TEST_F(OutlinerTypeAnalysisTest, integral_constant_held_by_type_ranges) {
  using IT = outliner_impl::IntegralType;
  struct Row {
    int64_t value;
    bool z, b, s, c;
  };
  const std::vector<Row> rows = {
      {-32769, false, false, false, false}, {-32768, false, false, true, false},
      {-129, false, false, true, false},    {-128, false, true, true, false},
      {-1, false, true, true, false},       {0, true, true, true, true},
      {1, true, true, true, true},          {2, false, true, true, true},
      {127, false, true, true, true},       {128, false, false, true, true},
      {32767, false, false, true, true},    {32768, false, false, false, true},
      {65535, false, false, false, true},   {65536, false, false, false, false},
  };
  for (const auto& r : rows) {
    const auto k = IT::constant(r.value);
    EXPECT_EQ(k.held_by(type::_boolean()), r.z) << r.value;
    EXPECT_EQ(k.held_by(type::_byte()), r.b) << r.value;
    EXPECT_EQ(k.held_by(type::_short()), r.s) << r.value;
    EXPECT_EQ(k.held_by(type::_char()), r.c) << r.value;
    EXPECT_TRUE(k.held_by(type::_int())) << r.value;
  }
}

namespace art_oracle {

// The integral part of ART's `RegType::Merge`
// (art/runtime/verifier/reg_type.cc), over ART's own representation. A
// constant is held as one value. Merging two constants of opposite signs gives
// the least of ART's byte, short and int constants that holds both, and each
// of those is held as the most negative value of its type.
struct Reg {
  enum Kind { Boolean, Byte, Short, Char, Integer, Constant } kind;
  int64_t value{0};

  bool is_constant() const { return kind == Constant; }
  bool in(int64_t lo, int64_t hi) const {
    return is_constant() && value >= lo && value <= hi;
  }
  bool constant_boolean() const { return in(0, 1); }
  bool constant_byte() const { return in(-128, 127); }
  bool constant_short() const { return in(-32768, 32767); }
  bool constant_char() const { return in(0, 65535); }
  bool boolean_types() const { return kind == Boolean || constant_boolean(); }
  bool byte_types() const {
    return constant_byte() || kind == Byte || boolean_types();
  }
  bool short_types() const {
    return kind == Short || byte_types() || constant_short();
  }
  bool char_types() const {
    return kind == Char || boolean_types() || constant_char();
  }
};

Reg merge(const Reg& a, const Reg& b) {
  if (a.kind == b.kind && (!a.is_constant() || a.value == b.value)) {
    return a;
  }
  if (a.is_constant() && b.is_constant()) {
    if (a.value >= 0 && b.value >= 0) {
      return {Reg::Constant, std::max(a.value, b.value)};
    }
    if (a.value < 0 && b.value < 0) {
      return {Reg::Constant, std::min(a.value, b.value)};
    }
    const Reg byte_constant{Reg::Constant, -128};
    const Reg short_constant{Reg::Constant, -32768};
    const Reg int_constant{Reg::Constant, std::numeric_limits<int32_t>::min()};
    if (a.constant_byte()) {
      return b.constant_byte()    ? byte_constant
             : b.constant_short() ? short_constant
                                  : int_constant;
    }
    if (a.constant_short()) {
      return b.constant_short() ? short_constant : int_constant;
    }
    return int_constant;
  }
  if (a.boolean_types() && b.boolean_types()) {
    return {Reg::Boolean};
  }
  if (a.byte_types() && b.byte_types()) {
    return {Reg::Byte};
  }
  if (a.short_types() && b.short_types()) {
    return {Reg::Short};
  }
  if (a.char_types() && b.char_types()) {
    return {Reg::Char};
  }
  return {Reg::Integer};
}

outliner_impl::IntegralType to_integral_type(const Reg& r) {
  using IT = outliner_impl::IntegralType;
  switch (r.kind) {
  case Reg::Boolean:
    return IT::of(type::_boolean());
  case Reg::Byte:
    return IT::of(type::_byte());
  case Reg::Short:
    return IT::of(type::_short());
  case Reg::Char:
    return IT::of(type::_char());
  case Reg::Integer:
    return IT::of(type::_int());
  case Reg::Constant:
    return IT::constant(r.value);
  }
  not_reached();
}

// Every result ART's merge can reach for `values`, over every order and
// grouping in which it merges them.
std::vector<Reg> every_merge(const std::vector<Reg>& values) {
  if (values.size() == 1) {
    return values;
  }
  std::vector<Reg> out;
  // Split into two non-empty groups in every way; each group merges first.
  const size_t n = values.size();
  for (size_t mask = 1; mask + 1 < (size_t{1} << n); ++mask) {
    std::vector<Reg> left;
    std::vector<Reg> right;
    for (size_t i = 0; i < n; ++i) {
      ((mask >> i) & 1u) != 0 ? left.push_back(values[i])
                              : right.push_back(values[i]);
    }
    for (const auto& l : every_merge(left)) {
      for (const auto& r : every_merge(right)) {
        out.push_back(merge(l, r));
      }
    }
  }
  return out;
}

} // namespace art_oracle

// Checks `IntegralType` against ART's merge. The values are every multiset of
// up to four drawn from the five integral types and ten constants, which cover
// every way the types hold a constant. The merge runs in every order and
// grouping. ART never reaches a type above the join, some order reaches the
// join, and `exact_type()` answers exactly when every order reaches the same
// type.
TEST_F(OutlinerTypeAnalysisTest, integral_type_join_covers_every_art_merge) {
  using art_oracle::Reg;
  using IT = outliner_impl::IntegralType;
  std::vector<Reg> leaves{
      {Reg::Boolean}, {Reg::Byte}, {Reg::Short}, {Reg::Char}, {Reg::Integer}};
  for (int64_t v : {-40000, -129, -1, 0, 1, 65, 200, 32767, 40000, 65536}) {
    leaves.push_back({Reg::Constant, v});
  }
  size_t multisets = 0;
  size_t typed = 0;
  size_t exact = 0;
  std::function<void(std::vector<Reg>&, size_t)> each;
  each = [&](std::vector<Reg>& values, size_t from) {
    if (!values.empty()) {
      ++multisets;
      std::optional<IT> accumulated;
      for (const auto& v : values) {
        accumulated = IT::join(accumulated, art_oracle::to_integral_type(v));
      }
      const auto joined = *accumulated;
      bool reached = false;
      std::optional<const DexType*> every_order;
      bool orders_agree = true;
      for (const auto& r : art_oracle::every_merge(values)) {
        const auto art = art_oracle::to_integral_type(r);
        EXPECT_TRUE(art.leq(joined));
        reached =
            reached || (joined.is_constant() ? art.is_constant()
                                             : art.type() == joined.type());
        if (!joined.is_constant()) {
          if (every_order && *every_order != art.type()) {
            orders_agree = false;
          }
          every_order = art.type();
        }
      }
      EXPECT_TRUE(reached);
      if (joined.is_constant()) {
        EXPECT_EQ(joined.exact_type(), nullptr);
      } else {
        ++typed;
        if (orders_agree) {
          ++exact;
          EXPECT_EQ(joined.exact_type(), *every_order);
        } else {
          EXPECT_EQ(joined.exact_type(), nullptr);
        }
      }
    }
    if (values.size() == 4) {
      return;
    }
    for (size_t i = from; i < leaves.size(); ++i) {
      values.push_back(leaves[i]);
      each(values, i);
      values.pop_back();
    }
  };
  std::vector<Reg> values;
  each(values, 0);
  EXPECT_EQ(multisets, 3875u);
  EXPECT_EQ(typed, 2875u);
  EXPECT_EQ(exact, 2830u);
}

namespace art16 {

// The integral register kinds of android-16.0.0_r1
// `runtime/verifier/reg_type.h`, each group of constants in the enumerator
// order the merge relies on.
enum Kind : uint8_t {
  kBoolean,
  kByte,
  kChar,
  kShort,
  kInteger,
  kZero,
  kBooleanConstant,
  kPositiveByteConstant,
  kPositiveShortConstant,
  kCharConstant,
  kByteConstant,
  kShortConstant,
  kIntegerConstant,
  kNumKinds,
};

constexpr bool is_constant(uint8_t k) { return k >= kZero; }
constexpr bool is_boolean_types(uint8_t k) {
  return k == kBoolean || k == kZero || k == kBooleanConstant;
}
constexpr bool is_byte_types(uint8_t k) {
  return k == kByte || k == kPositiveByteConstant || k == kByteConstant ||
         is_boolean_types(k);
}
constexpr bool is_short_types(uint8_t k) {
  return k == kShort || k == kPositiveShortConstant || k == kShortConstant ||
         is_byte_types(k);
}
constexpr bool is_char_types(uint8_t k) {
  return k == kChar || k == kCharConstant || k == kPositiveShortConstant ||
         k == kPositiveByteConstant || is_boolean_types(k);
}

// `RegTypeMergeImpl::MergeKind` (`runtime/verifier/reg_type.cc`) on two
// integral kinds.
constexpr uint8_t merge(uint8_t a, uint8_t b) {
  if (is_constant(a) && is_constant(b)) {
    auto is_non_negative = [](uint8_t k) {
      return k == kZero || k == kBooleanConstant ||
             k == kPositiveByteConstant || k == kPositiveShortConstant ||
             k == kCharConstant;
    };
    if (is_non_negative(a) == is_non_negative(b)) {
      return a >= b ? a : b;
    }
    const uint8_t non_negative = is_non_negative(a) ? a : b;
    const uint8_t can_be_negative = is_non_negative(a) ? b : a;
    if (can_be_negative == kByteConstant &&
        non_negative <= kPositiveByteConstant) {
      return kByteConstant;
    }
    if (can_be_negative <= kShortConstant &&
        non_negative <= kPositiveShortConstant) {
      return kShortConstant;
    }
    return kIntegerConstant;
  }
  if (is_boolean_types(a) && is_boolean_types(b)) {
    return kBoolean;
  }
  if (is_byte_types(a) && is_byte_types(b)) {
    return kByte;
  }
  if (is_short_types(a) && is_short_types(b)) {
    return kShort;
  }
  if (is_char_types(a) && is_char_types(b)) {
    return kChar;
  }
  return kInteger;
}

outliner_impl::IntegralType to_integral_type(uint8_t k) {
  using IT = outliner_impl::IntegralType;
  switch (k) {
  case kBoolean:
    return IT::of(type::_boolean());
  case kByte:
    return IT::of(type::_byte());
  case kChar:
    return IT::of(type::_char());
  case kShort:
    return IT::of(type::_short());
  case kInteger:
    return IT::of(type::_int());
  default: {
    // A value of each constant kind's range.
    static const int64_t kValues[] = {0, 1, 2, 128, 32768, -1, -129, 65536};
    return IT::constant(kValues[k - kZero]);
  }
  }
}

const DexType* to_dex_type(uint8_t k) {
  switch (k) {
  case kBoolean:
    return type::_boolean();
  case kByte:
    return type::_byte();
  case kChar:
    return type::_char();
  case kShort:
    return type::_short();
  default:
    always_assert(k == kInteger);
    return type::_int();
  }
}

// For every non-empty set of kinds, given as a mask: the kinds at which some
// merge tree whose leaves are exactly that set ends.
std::vector<uint16_t> ends_of_every_merge_tree() {
  constexpr uint16_t kAll = (1u << kNumKinds) - 1;
  std::vector<uint16_t> ends(kAll + 1, 0);
  // `with[m][k]`: the merges of each kind in `m` with `k`.
  std::vector<std::array<uint16_t, kNumKinds>> with(kAll + 1);
  for (uint32_t m = 1; m <= kAll; ++m) {
    for (uint8_t k = 0; k < kNumKinds; ++k) {
      uint16_t r = 0;
      for (uint8_t j = 0; j < kNumKinds; ++j) {
        if ((m & (1u << j)) != 0) {
          r |= 1u << merge(j, k);
        }
      }
      with[m][k] = r;
    }
  }
  // Visit sets in increasing order, so both halves of a split are already
  // computed.
  for (uint32_t set = 1; set <= kAll; ++set) {
    if (std::popcount(set) == 1) {
      ends[set] = set;
      continue;
    }
    uint16_t r = 0;
    for (uint32_t left = (set - 1) & set; left != 0; left = (left - 1) & set) {
      const uint32_t right = set & ~left;
      if (left < right) {
        continue;
      }
      for (uint8_t k = 0; k < kNumKinds; ++k) {
        if ((ends[right] & (1u << k)) != 0) {
          r |= with[ends[left]][k];
        }
      }
    }
    ends[set] = r;
  }
  return ends;
}

} // namespace art16

// Checks `IntegralType` against android-16's merge of every set of the 13
// integral register kinds, over every merge tree. `type()` is the least type
// above every end, and `exact_type()` is the end when all trees agree. A merge
// tree whose leaves repeat a kind reaches no other end; the test checks that
// for every multiset of up to four kinds.
TEST_F(OutlinerTypeAnalysisTest,
       integral_type_matches_art16_merge_of_every_kind_set) {
  using IT = outliner_impl::IntegralType;
  const auto ends = art16::ends_of_every_merge_tree();
  size_t typed = 0;
  size_t order_dependent = 0;
  for (uint32_t set = 1; set < ends.size(); ++set) {
    std::optional<IT> joined;
    for (uint8_t k = 0; k < art16::kNumKinds; ++k) {
      if ((set & (1u << k)) != 0) {
        joined = IT::join(joined, art16::to_integral_type(k));
      }
    }
    const bool constants_only = (set & ((1u << art16::kZero) - 1)) == 0;
    EXPECT_EQ(joined->is_constant(), constants_only);
    if (constants_only) {
      continue;
    }
    ++typed;
    std::optional<IT> upper;
    for (uint8_t k = 0; k < art16::kNumKinds; ++k) {
      if ((ends[set] & (1u << k)) != 0) {
        ASSERT_FALSE(art16::is_constant(k));
        upper = IT::join(upper, IT::of(art16::to_dex_type(k)));
      }
    }
    EXPECT_EQ(joined->type(), upper->type()) << "kind set " << set;
    if (std::popcount(ends[set]) == 1) {
      EXPECT_EQ(joined->exact_type(),
                art16::to_dex_type(std::countr_zero(ends[set])))
          << "kind set " << set;
    } else {
      ++order_dependent;
      EXPECT_EQ(ends[set], (1u << art16::kChar) | (1u << art16::kInteger));
      EXPECT_EQ(joined->exact_type(), nullptr) << "kind set " << set;
    }
  }
  EXPECT_EQ(typed, 8191u - 255u);
  EXPECT_EQ(order_dependent, 36u);

  // Every merge tree over a multiset ends where the trees over its distinct
  // kinds do.
  std::function<std::set<uint8_t>(const std::vector<uint8_t>&)> every_end;
  every_end = [&](const std::vector<uint8_t>& leaves) {
    if (leaves.size() == 1) {
      return std::set<uint8_t>{leaves[0]};
    }
    std::set<uint8_t> result;
    const uint32_t n = leaves.size();
    for (uint32_t left = 1; left + 1 < (1u << n); ++left) {
      std::vector<uint8_t> l;
      std::vector<uint8_t> r;
      for (uint32_t i = 0; i < n; ++i) {
        ((left & (1u << i)) != 0 ? l : r).push_back(leaves[i]);
      }
      for (auto a : every_end(l)) {
        for (auto b : every_end(r)) {
          result.insert(art16::merge(a, b));
        }
      }
    }
    return result;
  };
  size_t multisets = 0;
  std::vector<uint8_t> leaves;
  std::function<void(uint8_t)> each = [&](uint8_t from) {
    if (!leaves.empty()) {
      ++multisets;
      uint16_t set = 0;
      for (auto k : leaves) {
        set |= 1u << k;
      }
      uint16_t mask = 0;
      for (auto k : every_end(leaves)) {
        mask |= 1u << k;
      }
      EXPECT_EQ(mask, ends[set]);
    }
    if (leaves.size() == 4) {
      return;
    }
    for (uint8_t k = from; k < art16::kNumKinds; ++k) {
      leaves.push_back(k);
      each(k);
      leaves.pop_back();
    }
  };
  each(0);
  EXPECT_EQ(multisets, 2379u);
}

namespace {

// A method that defines a parameter of each integral type and a constant for
// each of the oracle's constant leaves, with the ART register each definition
// stands for. `for_each` visits every set of up to four of those definitions
// that includes at least one parameter.
struct TypedDefsCorpus {
  DexMethod* method{nullptr};
  std::vector<art_oracle::Reg> leaves;
  std::vector<const IRInstruction*> defs;

  TypedDefsCorpus() {
    using art_oracle::Reg;
    std::string body =
        "(load-param v0)\n(load-param v1)\n(load-param v2)\n"
        "(load-param v3)\n(load-param v4)\n";
    leaves = {
        {Reg::Boolean}, {Reg::Byte}, {Reg::Short}, {Reg::Char}, {Reg::Integer}};
    const std::vector<int64_t> constants{-40000, -129, -1,    0,     1,
                                         65,     200,  32767, 40000, 65536};
    for (size_t i = 0; i < constants.size(); ++i) {
      body += "(const v" + std::to_string(5 + i) + " " +
              std::to_string(constants[i]) + ")\n";
      leaves.push_back({Reg::Constant, constants[i]});
    }
    body += "(return-void)\n";
    method = assembler::method_from_string(
        R"((method (public static) "LCorpus;.foo:(ZBSCI)V" ()" + body + "))");
    method->get_code()->build_cfg();
    for (const auto& mie : InstructionIterable(method->get_code()->cfg())) {
      if (mie.insn->has_dest()) {
        defs.push_back(mie.insn);
      }
    }
    always_assert(defs.size() == leaves.size());
  }

  // Calls `f(values, defs)` for every set.
  void for_each(
      const std::function<void(const std::vector<art_oracle::Reg>&,
                               const UnorderedSet<const IRInstruction*>&)>& f)
      const {
    std::vector<size_t> chosen;
    std::function<void(size_t)> each;
    each = [&](size_t from) {
      if (!chosen.empty() && chosen.front() < 5) {
        std::vector<art_oracle::Reg> values;
        UnorderedSet<const IRInstruction*> set;
        for (auto i : chosen) {
          values.push_back(leaves[i]);
          set.insert(defs[i]);
        }
        f(values, set);
      }
      if (chosen.size() == 4) {
        return;
      }
      for (size_t i = from; i < leaves.size(); ++i) {
        chosen.push_back(i);
        each(i + 1);
        chosen.pop_back();
      }
    };
    each(0);
  }
};

// The type every order and grouping of ART's merge of `values` ends at, or
// nullptr when they end at different types.
const DexType* type_of_every_merge(const std::vector<art_oracle::Reg>& values) {
  std::optional<const DexType*> type;
  for (const auto& r : art_oracle::every_merge(values)) {
    const auto* t = art_oracle::to_integral_type(r).type();
    if (type && *type != t) {
      return nullptr;
    }
    type = t;
  }
  return *type;
}

} // namespace

// Checks `get_result_type` against ART's merge. The definitions are every set
// of up to four drawn from a parameter of each integral type and the oracle's
// constants, with at least one parameter. The answer is the type that every
// order and grouping of ART's merge ends at, and there is none when the order
// decides the type.
TEST_F(OutlinerTypeAnalysisTest, get_result_type_is_never_narrower_than_art) {
  TypedDefsCorpus corpus;
  outliner_impl::OutlinerTypeAnalysis ota(corpus.method);
  size_t sets = 0;
  size_t typed = 0;
  corpus.for_each([&](const auto& values, const auto& defs) {
    ++sets;
    const auto* t = get_result_type(ota, defs, nullptr);
    const auto* art = type_of_every_merge(values);
    if (art != nullptr) {
      ++typed;
      EXPECT_EQ(t, art) << SHOW(t);
    } else {
      EXPECT_EQ(t, nullptr) << SHOW(t);
    }
  });
  EXPECT_EQ(sets, 1555u);
  EXPECT_EQ(typed, 1528u);
}

// A `boolean` and a constant in [2, 32767] can merge first into `byte` or
// `short`, which a `char` then takes to `int`. In the other orders they end at
// `char`. So the set cannot be declared as a result: the code after the call
// was verified against whichever of `char` and `int` ART computed.
TEST_F(OutlinerTypeAnalysisTest, get_result_type_of_boolean_char_and_constant) {
  auto* foo_method = assembler::method_from_string(R"(
      (method (public static) "LFoo;.foo:(ZC)V" (
        (load-param v0)
        (load-param v1)
        (const v2 2)
        (return-void)
      )))");
  foo_method->get_code()->build_cfg();
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);
  const auto* z = find_insn(foo_method, IOPCODE_LOAD_PARAM, 1);
  const auto* c = find_insn(foo_method, IOPCODE_LOAD_PARAM, 2);
  const auto* two = find_insn(foo_method, OPCODE_CONST);
  EXPECT_EQ(get_result_type(ota, {z, c, two}, nullptr), nullptr);
  EXPECT_EQ(get_result_type(ota, {z, two}, type::_char()), nullptr);
}

// A long chain of `and-int`s, each reading the previous result twice. A walk
// that re-visits a shared operand once per path to it takes 2^64 steps; the
// fixpoint takes one per operation.
TEST_F(OutlinerTypeAnalysisTest,
       integral_value_of_shared_bitwise_dag_is_linear) {
  std::string body = "(load-param v0)\n(load-param v1)\n";
  for (int i = 0; i < 64; ++i) {
    body += "(and-int v0 v0 v0)\n(xor-int v1 v1 v1)\n(or-int v1 v1 v0)\n";
  }
  body += "(return-void)\n";
  auto* foo_method = assembler::method_from_string(
      R"((method (public static) "LFoo;.foo:(ZC)V" ()" + body + "))");
  foo_method->get_code()->build_cfg();
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);
  auto last = [&](IROpcode op) {
    const IRInstruction* found = nullptr;
    for (const auto& mie : InstructionIterable(foo_method->get_code()->cfg())) {
      if (mie.insn->opcode() == op) {
        found = mie.insn;
      }
    }
    return found;
  };
  EXPECT_EQ(get_result_type(ota, {last(OPCODE_AND_INT)}, nullptr),
            type::_boolean());
  EXPECT_EQ(get_result_type(ota, {last(OPCODE_OR_INT)}, nullptr), type::_int());
}

// A bitwise operation in a loop reads its own result. It stays boolean while
// nothing else feeding it is wider, as in ART.
TEST_F(OutlinerTypeAnalysisTest, integral_value_of_bitwise_cycle) {
  auto* foo_method = assembler::method_from_string(R"(
      (method (public static) "LFoo;.foo:(ZZC)V" (
        (load-param v0)
        (load-param v1)
        (load-param v2)
        (move v3 v2)
        (:loop)
        (and-int v0 v0 v1)
        (or-int v3 v3 v0)
        (if-nez v1 :loop)
        (return-void)
      )))");
  foo_method->get_code()->build_cfg();
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);
  EXPECT_EQ(
      get_result_type(ota, {find_insn(foo_method, OPCODE_AND_INT)}, nullptr),
      type::_boolean());
  EXPECT_EQ(
      get_result_type(ota, {find_insn(foo_method, OPCODE_OR_INT)}, nullptr),
      type::_int());
}

// A register that a typed definition and constants outside its type define
// has the type ART merges them into, not none.
TEST_F(OutlinerTypeAnalysisTest, get_result_type_merges_constants_by_value) {
  auto* foo_method = assembler::method_from_string(R"(
      (method (public static) "LFoo;.foo:(ZBSCI)V" (
        (load-param v0)
        (load-param v1)
        (load-param v2)
        (load-param v3)
        (load-param v4)
        (const v5 200)
        (const v6 -1)
        (const v7 40000)
        (const v8 65)
        (return-void)
      )))");
  foo_method->get_code()->build_cfg();
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);
  auto type_of = [&](size_t param, int64_t literal) {
    UnorderedSet<const IRInstruction*> defs{
        find_insn(foo_method, IOPCODE_LOAD_PARAM, param),
        find_insn(foo_method, [literal](IRInstruction* insn) {
          return insn->opcode() == OPCODE_CONST &&
                 insn->get_literal() == literal;
        })};
    return get_result_type(ota, defs, nullptr);
  };
  EXPECT_EQ(type_of(2, 200), type::_short());
  EXPECT_EQ(type_of(4, -1), type::_int());
  EXPECT_EQ(type_of(3, 40000), type::_int());
  EXPECT_EQ(type_of(1, 65), type::_byte());
  EXPECT_EQ(type_of(1, 200), type::_short());
  EXPECT_EQ(type_of(4, 65), type::_char());
}

// A register whose only definitions are undefined values, or that has none,
// takes its incoming type.
TEST_F(OutlinerTypeAnalysisTest, get_result_type_of_incoming_type_alone) {
  auto* foo_method = assembler::method_from_string(R"(
      (method (public static) "LFoo;.foo:()V" (
        (unreachable v0)
        (throw v0)
      )))");
  foo_method->get_code()->build_cfg();
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);
  EXPECT_EQ(get_result_type(ota, {}, type::_char()), type::_char());
  EXPECT_EQ(get_result_type(ota, {find_insn(foo_method, IOPCODE_UNREACHABLE)},
                            type::_char()),
            type::_char());
}

// The same chain as `integral_value_of_shared_bitwise_dag_is_linear`, typed
// through `get_result_type`.
TEST_F(OutlinerTypeAnalysisTest,
       get_result_type_of_shared_bitwise_dag_is_linear) {
  std::string body = "(load-param v0)\n(load-param v1)\n";
  for (int i = 0; i < 64; ++i) {
    body += "(and-int v0 v0 v0)\n(xor-int v1 v1 v1)\n(or-int v1 v1 v0)\n";
  }
  body += "(const v2 7)\n(return-void)\n";
  auto* foo_method = assembler::method_from_string(
      R"((method (public static) "LFoo;.foo:(ZC)V" ()" + body + "))");
  foo_method->get_code()->build_cfg();
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);
  UnorderedSet<const IRInstruction*> ands;
  const IRInstruction* last_or = nullptr;
  for (const auto& mie : InstructionIterable(foo_method->get_code()->cfg())) {
    if (mie.insn->opcode() == OPCODE_AND_INT) {
      ands.insert(mie.insn);
    } else if (mie.insn->opcode() == OPCODE_OR_INT) {
      last_or = mie.insn;
    }
  }
  EXPECT_EQ(get_result_type(ota, ands, nullptr), type::_boolean());
  EXPECT_EQ(get_result_type(ota, {last_or}, nullptr), type::_int());
  EXPECT_EQ(get_result_type(ota, ands, type::_char()), type::_char());
  ands.insert(find_insn(foo_method, OPCODE_CONST));
  EXPECT_EQ(get_result_type(ota, ands, nullptr), type::_byte());
}

TEST_F(OutlinerTypeAnalysisTest, get_result_type_unreachable) {
  // Regression: a def fed by IOPCODE_UNREACHABLE (a synthetic undefined value
  // that the type analysis groups with consts) must not crash
  // get_const_insns_type_demand -- the constant-uses analysis only handles
  // OPCODE_CONST/OPCODE_CONST_WIDE. Its type is undeterminable -> nullptr.
  auto* foo_method = assembler::method_from_string(R"(
      (method (public static) "LFoo;.foo:()V" (
        (const v0 0)
        (return-void)
      )))");
  foo_method->get_code()->build_cfg();
  auto& cfg = foo_method->get_code()->cfg();
  auto* unreachable = new IRInstruction(IOPCODE_UNREACHABLE);
  unreachable->set_dest(0);
  auto ii = InstructionIterable(cfg);
  cfg.insert_before(ii.begin(), unreachable);
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  const auto* result_type =
      get_result_type(ota, {unreachable}, /* optional_extra_type */
                      nullptr);
  EXPECT_EQ(result_type, nullptr);
}

TEST_F(OutlinerTypeAnalysisTest, get_result_type_unsupported_dest_bearing) {
  // `const-method-type` and `const-method-handle` write a result the type
  // analysis does not model. They are legal input dex. `value_of_def` hands
  // every definition that is neither a constant nor a bitwise operation to
  // `get_result_type_helper`, so it must type such a definition as nullptr
  // and must not throw. nullptr means "undeterminable", and every caller then
  // drops the candidate.
  auto* foo_method = assembler::method_from_string(R"(
      (method (public static) "LFoo;.foo:()V" (
        (const v0 0)
        (return-void)
      )))");
  foo_method->get_code()->build_cfg();
  auto& cfg = foo_method->get_code()->cfg();

  // `const-method-type` carries no dest of its own: like the other
  // result-producing opcodes it writes through a following
  // `move-result-pseudo-object`. Setting a dest on it directly trips
  // `has_dest()`.
  auto* const_method_type = new IRInstruction(OPCODE_CONST_METHOD_TYPE);
  const_method_type->set_proto(
      DexProto::make_proto(type::_void(), DexTypeList::make_type_list({})));
  auto* move_result = new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT);
  move_result->set_dest(0);
  auto ii = InstructionIterable(cfg);
  cfg.insert_before(ii.begin(), {const_method_type, move_result});
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  // The test hands the analysis the dest-bearing `move-result-pseudo-object`,
  // because that is what a reaching-defs query yields. `get_defs` resolves it
  // to the PRIMARY instruction, where `get_result_type_helper` meets the
  // unsupported opcode. Passing the primary directly would trip an unrelated
  // `has_dest()` assertion in `get_defs` instead, and would not exercise the
  // refusal path.
  const DexType* result_type = nullptr;
  EXPECT_NO_THROW({
    result_type = get_result_type(ota, {move_result},
                                  /* optional_extra_type */ nullptr);
  });
  EXPECT_EQ(result_type, nullptr);
}

TEST_F(OutlinerTypeAnalysisTest, get_result_type_object) {
  ClassCreator object_creator(type::java_lang_Object());
  ClassCreator foo_creator(DexType::make_type("LFoo;"));
  foo_creator.set_super(type::java_lang_Object());
  ClassCreator bar_creator(DexType::make_type("LBar;"));
  bar_creator.set_super(type::java_lang_Object());

  auto* foo_method = assembler::method_from_string(R"(
      (method (public) "LFoo;.foo:(Ljava/lang/Object;LBar;)V" (
        (load-param-object v1)
        (load-param-object v2)
        (load-param-object v3)
      )))");
  foo_method->get_code()->build_cfg();
  foo_creator.add_method(foo_method);
  object_creator.create();
  auto* foo_type = foo_creator.create()->get_type();
  auto* bar_type = bar_creator.create()->get_type();

  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  {
    // result type of first 'load-param-object' is Foo
    auto* insn = find_insn(foo_method, IOPCODE_LOAD_PARAM_OBJECT);
    const auto* result_type =
        get_result_type(ota, {insn},
                        /* optional_extra_type */ nullptr);
    EXPECT_EQ(result_type, foo_type);
  }

  {
    // result type of second 'load-param-object' is Object
    auto* insn = find_insn(foo_method, IOPCODE_LOAD_PARAM_OBJECT, 2);
    const auto* result_type =
        get_result_type(ota, {insn}, /* optional_extra_type */ nullptr);
    EXPECT_EQ(result_type, type::java_lang_Object());
  }

  {
    // result type of third 'load-param-object' is Bar
    auto* insn = find_insn(foo_method, IOPCODE_LOAD_PARAM_OBJECT, 3);
    const auto* result_type =
        get_result_type(ota, {insn}, /* optional_extra_type */ nullptr);
    EXPECT_EQ(result_type, bar_type);
  }

  {
    // the combined result type of Foo and Object is Object
    auto* insn1 = find_insn(foo_method, IOPCODE_LOAD_PARAM_OBJECT);
    auto* insn2 = find_insn(foo_method, IOPCODE_LOAD_PARAM_OBJECT, 2);
    const auto* result_type =
        get_result_type(ota, {insn1, insn2},
                        /* optional_extra_type */ nullptr);
    EXPECT_EQ(result_type, type::java_lang_Object());
  }

  {
    // the combined result type of Foo and Bar is Object
    auto* insn1 = find_insn(foo_method, IOPCODE_LOAD_PARAM_OBJECT, 1);
    auto* insn2 = find_insn(foo_method, IOPCODE_LOAD_PARAM_OBJECT, 3);
    const auto* result_type =
        get_result_type(ota, {insn1, insn2},
                        /* optional_extra_type */ nullptr);
    EXPECT_EQ(result_type, type::java_lang_Object());
  }
}

TEST_F(OutlinerTypeAnalysisTest, get_result_type_object_with_interfaces) {
  ClassCreator i_creator(DexType::make_type("LI;"));
  i_creator.set_access(ACC_INTERFACE | ACC_ABSTRACT);
  i_creator.set_super(type::java_lang_Object());
  auto* i_type = i_creator.create()->get_type();
  ClassCreator j_creator(DexType::make_type("LJ;"));
  j_creator.set_access(ACC_INTERFACE | ACC_ABSTRACT);
  j_creator.set_super(type::java_lang_Object());
  auto* j_type = j_creator.create()->get_type();
  ClassCreator object_creator(type::java_lang_Object());
  ClassCreator foo_creator(DexType::make_type("LFoo;"));
  foo_creator.set_super(type::java_lang_Object());
  foo_creator.add_interface(i_type);
  foo_creator.add_interface(j_type);
  ClassCreator bar_creator(DexType::make_type("LBar;"));
  bar_creator.set_super(type::java_lang_Object());
  bar_creator.add_interface(i_type);
  bar_creator.add_interface(j_type);

  auto* foo_method = assembler::method_from_string(R"(
      (method (public) "LFoo;.foo:(LBar;)V" (
        (load-param-object v1)
        (load-param-object v2)
        (return-void)
      )))");
  foo_method->get_code()->build_cfg();
  foo_creator.add_method(foo_method);
  object_creator.create();
  auto* foo_type = foo_creator.create()->get_type();
  auto* bar_type = bar_creator.create()->get_type();

  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  {
    // result type of first 'load-param-object' is Foo
    auto* insn = find_insn(foo_method, IOPCODE_LOAD_PARAM_OBJECT, 1);
    const auto* result_type =
        get_result_type(ota, {insn}, /* optional_extra_type */ nullptr);
    EXPECT_EQ(result_type, foo_type);
  }

  {
    // result type of second 'load-param-object' is Bar
    auto* insn = find_insn(foo_method, IOPCODE_LOAD_PARAM_OBJECT, 2);
    const auto* result_type =
        get_result_type(ota, {insn}, /* optional_extra_type */ nullptr);
    EXPECT_EQ(result_type, bar_type);
  }

  {
    // the combined result type of Foo and Bar is nullptr, as the common base
    // type Object does not implement the common interfaces I and J
    auto* insn1 = find_insn(foo_method, IOPCODE_LOAD_PARAM_OBJECT, 1);
    auto* insn2 = find_insn(foo_method, IOPCODE_LOAD_PARAM_OBJECT, 2);
    const auto* result_type =
        get_result_type(ota, {insn1, insn2},
                        /* optional_extra_type */ nullptr);
    EXPECT_EQ(result_type, nullptr);
  }
}

static std::shared_ptr<outliner_impl::PartialCandidateNode> create_node(
    std::vector<IRInstruction*> insns,
    std::vector<std::pair<cfg::Edge*,
                          std::shared_ptr<outliner_impl::PartialCandidateNode>>>
        succs = {}) {
  return std::make_shared<outliner_impl::PartialCandidateNode>(
      (outliner_impl::PartialCandidateNode){
          std::move(insns), {}, std::move(succs)});
}

static Candidate create_candidate(
    outliner_impl::OutlinerTypeAnalysis& ota,
    const std::shared_ptr<outliner_impl::PartialCandidateNode>& root) {
  outliner_impl::PartialCandidate pc{{}, *root};
  return Candidate{ota, std::move(pc), std::nullopt};
}

TEST_F(OutlinerTypeAnalysisTest, get_type_demand_primitive) {
  auto* foo_method = assembler::method_from_string(R"(
      (method (public) "LFoo;.foo:(IZ)Z" (
        (load-param v1)
        (load-param v2)
        (move v1 v1)
        (add-int v1 v1 v1)
        (or-int v1 v1 v1)
        (sub-int v1 v1 v1)
        (xor-int v2 v2 v2)
        (return v2)
      )))");
  foo_method->get_code()->build_cfg();
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  {
    // type demand of src(0) of 'add-int' is int
    auto* insn = find_insn(foo_method, OPCODE_ADD_INT);
    auto root = create_node({insn});
    auto candidate = create_candidate(ota, root);
    const auto* result_type = get_type_demand(candidate, insn->src(0));
    EXPECT_EQ(result_type, type::_int());
  }

  {
    // type demand of src(0) of 'return' of foo is boolean
    auto* insn = find_insn(foo_method, OPCODE_RETURN);
    auto root = create_node({insn});
    auto candidate = create_candidate(ota, root);
    const auto* result_type = get_type_demand(candidate, insn->src(0));
    EXPECT_EQ(result_type, type::_boolean());
  }

  {
    // type demand of src(0) of 'xor' with boolean out is boolean
    auto* insn = find_insn(foo_method, OPCODE_XOR_INT);
    auto root = create_node({insn});
    auto candidate = create_candidate(ota, root);
    candidate.set_result(insn->dest(), type::_boolean());
    const auto* result_type = get_type_demand(candidate, insn->src(0));
    EXPECT_EQ(result_type, type::_boolean());
  }

  {
    // type demand of src(0) of 'or' follows by 'sub' is int
    auto* insn1 = find_insn(foo_method, OPCODE_OR_INT);
    auto* insn2 = find_insn(foo_method, OPCODE_SUB_INT);
    auto root = create_node({insn1, insn2});
    auto candidate = create_candidate(ota, root);
    const auto* result_type = get_type_demand(candidate, insn1->src(0));
    EXPECT_EQ(result_type, type::_int());
  }
}

TEST_F(OutlinerTypeAnalysisTest, get_type_demand_unsupported_invoke) {
  // `invoke-polymorphic` and `invoke-custom` are legal input dex, and a
  // candidate can read a register through one. Their argument demand is not
  // modelled, so it must come back undeterminable (nullptr), and
  // `get_type_demand` then falls back to the inferred type instead of aborting
  // the build.
  auto* foo_method = assembler::method_from_string(R"(
      (method (public static) "LFoo;.foo:(Ljava/lang/invoke/MethodHandle;I)V" (
        (load-param-object v0)
        (load-param v1)
        (return-void)
      )))");
  foo_method->get_code()->build_cfg();
  auto& cfg = foo_method->get_code()->cfg();

  auto* invoke = new IRInstruction(OPCODE_INVOKE_POLYMORPHIC);
  invoke->set_method(DexMethod::make_method(
      "Ljava/lang/invoke/MethodHandle;.invoke:([Ljava/lang/Object;)"
      "Ljava/lang/Object;"));
  invoke->set_srcs_size(2);
  invoke->set_src(0, 0);
  invoke->set_src(1, 1);
  auto* ret = find_insn(foo_method, OPCODE_RETURN_VOID);
  cfg.insert_before(cfg.find_insn(ret), invoke);
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  auto root = create_node({invoke});
  auto candidate = create_candidate(ota, root);
  const DexType* result_type = nullptr;
  EXPECT_NO_THROW(
      { result_type = get_type_demand(candidate, invoke->src(1)); });
  EXPECT_EQ(result_type, type::_int());
}

TEST_F(OutlinerTypeAnalysisTest, get_type_demand_sputs_of_zero) {
  auto* foo_method = assembler::method_from_string(R"(
      (method (public static) "LFoo;.foo:()V" (
        (const v0 0)
        (sput-object v0 "LFoo;.s1:LBar1;")
        (sput-object v0 "LFoo;.s2:LBar2;")
        (return-void)
      )))");
  foo_method->get_code()->build_cfg();
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  {
    // there's no type that would fit untyped zero (null)
    auto* insn1 = find_insn(foo_method, OPCODE_SPUT_OBJECT, 1);
    auto* insn2 = find_insn(foo_method, OPCODE_SPUT_OBJECT, 2);
    auto root = create_node({insn1, insn2});
    auto candidate = create_candidate(ota, root);
    const auto* result_type = get_type_demand(candidate, insn1->src(0));
    EXPECT_EQ(result_type, nullptr);
  }
}

TEST_F(OutlinerTypeAnalysisTest, get_type_demand_if_of_zero) {
  std::string src = R"(
      (
        (const v1 0)
        (const v2 0)
        (if-eq v1 v2 :L1)
        (:L1)
        (return-void)
      ))";
  auto code = assembler::ircode_from_string(src);
  code->build_cfg();
  auto* foo_method =
      DexMethod::make_method("LFoo;.foo:()V")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, std::move(code),
                          /*is_virtual=*/false);
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  {
    // type demand of if-eq src(0) is not something we can determine
    // with zero (could be object or int)
    auto* insn = find_insn(foo_method, OPCODE_IF_EQ);
    auto root = create_node({insn});
    auto candidate = create_candidate(ota, root);
    const auto* result_type = get_type_demand(candidate, insn->src(0));
    EXPECT_EQ(result_type, nullptr);
  }
}

TEST_F(OutlinerTypeAnalysisTest, get_type_demand_if_of_nonzero) {
  std::string src = R"(
      (
        (const v1 23)
        (const v2 42)
        (if-eq v1 v2 :L1)
        (:L1)
        (return-void)
      ))";
  auto code = assembler::ircode_from_string(src);
  code->build_cfg();
  auto* foo_method =
      DexMethod::make_method("LFoo;.foo:()V")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, std::move(code),
                          /*is_virtual=*/false);
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  {
    auto* insn = find_insn(foo_method, OPCODE_IF_EQ);
    auto root = create_node({insn});
    auto candidate = create_candidate(ota, root);
    const auto* result_type = get_type_demand(candidate, insn->src(0));
    EXPECT_EQ(result_type, type::_int());
  }
}

TEST_F(OutlinerTypeAnalysisTest, get_type_demand_if_of_large_constants) {
  std::string src = R"(
      (
        (const v1 -30000)
        (const v2 40000)
        (if-eq v1 v2 :L1)
        (:L1)
        (return-void)
      ))";
  auto code = assembler::ircode_from_string(src);
  code->build_cfg();
  auto* foo_method =
      DexMethod::make_method("LFoo;.foo:()V")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, std::move(code),
                          /*is_virtual=*/false);
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  {
    // the non-zero constants flowing into the if must be some kind of integer
    // type. The particular values here allow us to pick specific types.
    auto* insn = find_insn(foo_method, OPCODE_IF_EQ);
    auto root = create_node({insn});
    auto candidate = create_candidate(ota, root);
    const auto* result_type0 = get_type_demand(candidate, insn->src(0));
    EXPECT_EQ(result_type0, type::_short());
    const auto* result_type1 = get_type_demand(candidate, insn->src(1));
    EXPECT_EQ(result_type1, type::_char());
  }
}

TEST_F(OutlinerTypeAnalysisTest, get_type_demand_primitive_narrow) {
  std::string src = R"(
      (
        (const v0 42)
        (load-param-object v1)
        (iput-short v0 v1 "LFoo;.f:S")
        (iput-byte v0 v1 "LFoo;.g:B")
        (iput v0 v1 "LFoo;.h:I")
        (return-void)
      ))";
  auto code = assembler::ircode_from_string(src);
  code->build_cfg();
  auto* foo_method = DexMethod::make_method("LFoo;.foo:()V")
                         ->make_concrete(ACC_PUBLIC, std::move(code),
                                         /*is_virtual=*/false);
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  {
    // a primitive put accepts any integral value, whatever the field's type,
    // so the narrowed type demand on the value across all the iputs is int
    auto* insn1 = find_insn(foo_method, OPCODE_IPUT_SHORT);
    auto* insn2 = find_insn(foo_method, OPCODE_IPUT_BYTE);
    auto* insn3 = find_insn(foo_method, OPCODE_IPUT);
    auto root = create_node({insn1, insn2, insn3});
    auto candidate = create_candidate(ota, root);
    const auto* result_type = get_type_demand(candidate, insn1->src(0));
    EXPECT_EQ(result_type, type::_int());
  }
}

// ART checks a primitive field or array put by category only, so a value that
// only reaches narrow puts is demanded as `int`. Taking the slot type as the
// demand would type an outlined parameter `boolean` (say) while the caller
// passes an `int`, which ART rejects for an invocation argument.
TEST_F(OutlinerTypeAnalysisTest, get_type_demand_narrow_puts_demand_int) {
  auto* foo_method = assembler::method_from_string(R"(
      (method (public static) "LFoo;.foo:(I[C[I[Z[B[SLFoo;)V" (
        (load-param v0)
        (load-param-object v1)
        (load-param-object v2)
        (load-param-object v5)
        (load-param-object v6)
        (load-param-object v7)
        (load-param-object v8)
        (add-int v3 v0 v0)
        (sput-boolean v3 "LFoo;.z:Z")
        (sput-byte v3 "LFoo;.b:B")
        (sput-char v3 "LFoo;.c:C")
        (sput-short v3 "LFoo;.s:S")
        (aput-boolean v3 v5 v0)
        (aput-byte v3 v6 v0)
        (aput-char v3 v1 v0)
        (aput-short v3 v7 v0)
        (aput v3 v2 v0)
        (iput-boolean v3 v8 "LFoo;.iz:Z")
        (iput-byte v3 v8 "LFoo;.ib:B")
        (iput-char v3 v8 "LFoo;.ic:C")
        (iput-short v3 v8 "LFoo;.is:S")
        (int-to-float v4 v0)
        (sput v4 "LFoo;.f:F")
        (return-void)
      )))");
  foo_method->get_code()->build_cfg();
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  for (auto op :
       {OPCODE_SPUT_BOOLEAN, OPCODE_SPUT_BYTE, OPCODE_SPUT_CHAR,
        OPCODE_SPUT_SHORT, OPCODE_APUT_BOOLEAN, OPCODE_APUT_BYTE,
        OPCODE_APUT_CHAR, OPCODE_APUT_SHORT, OPCODE_APUT, OPCODE_IPUT_BOOLEAN,
        OPCODE_IPUT_BYTE, OPCODE_IPUT_CHAR, OPCODE_IPUT_SHORT}) {
    auto* insn = find_insn(foo_method, op);
    auto root = create_node({insn});
    auto candidate = create_candidate(ota, root);
    EXPECT_EQ(get_type_demand(candidate, insn->src(0)), type::_int())
        << SHOW(insn);
  }

  {
    // a non-integral slot still demands its own type
    auto* insn = find_insn(foo_method, OPCODE_SPUT);
    auto root = create_node({insn});
    auto candidate = create_candidate(ota, root);
    EXPECT_EQ(get_type_demand(candidate, insn->src(0)), type::_float());
  }
}

// ART checks the value of a narrow array put by category only when it types
// the array operand as an array. A null array is a register that only a
// `const 0` defines. Through a null array, ART 6.0 and later check the value
// strictly against the instruction's own type (`VerifyAPut` in
// `method_verifier.cc`), so that type is the demand. A null merged with an
// array is the array to ART.
TEST_F(OutlinerTypeAnalysisTest, get_type_demand_narrow_aput_into_null_array) {
  auto* foo_method = assembler::method_from_string(R"(
      (method (public static) "LFoo;.foo:(I[C)V" (
        (load-param v0)
        (load-param-object v5)
        (add-int v3 v0 v0)
        (const v1 0)
        (aput-boolean v3 v1 v0)
        (aput-byte v3 v1 v0)
        (aput-char v3 v1 v0)
        (aput-short v3 v1 v0)
        (if-eqz v0 :merged)
        (move-object v5 v1)
        (:merged)
        (aput-char v3 v5 v0)
        (return-void)
      )))");
  foo_method->get_code()->build_cfg();
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  auto demand = [&](IROpcode op, size_t occurrence = 1) {
    auto* insn = find_insn(foo_method, op, occurrence);
    auto root = create_node({insn});
    auto candidate = create_candidate(ota, root);
    return get_type_demand(candidate, insn->src(0));
  };
  EXPECT_EQ(demand(OPCODE_APUT_BOOLEAN), type::_boolean());
  EXPECT_EQ(demand(OPCODE_APUT_BYTE), type::_byte());
  EXPECT_EQ(demand(OPCODE_APUT_CHAR), type::_char());
  EXPECT_EQ(demand(OPCODE_APUT_SHORT), type::_short());
  EXPECT_EQ(demand(OPCODE_APUT_CHAR, 2), type::_int());
}

// ART types an `aget-object` from a null array as null too, so a put into it
// is checked strictly. An array that only ART knows, after an `instance-of`
// test, is checked by category: the put places no demand of its own, and the
// value keeps its inferred `int`.
TEST_F(OutlinerTypeAnalysisTest,
       get_type_demand_narrow_aput_beyond_const_null) {
  auto* foo_method = assembler::method_from_string(R"(
      (method (public static) "LFoo;.foo:(ILjava/lang/Object;)V" (
        (load-param v0)
        (load-param-object v1)
        (add-int v3 v0 v0)
        (const v4 0)
        (aget-object v4 v0)
        (move-result-pseudo-object v5)
        (aput-byte v3 v5 v0)
        (instance-of v1 "[C")
        (move-result-pseudo v6)
        (if-eqz v6 :end)
        (aput-char v3 v1 v0)
        (:end)
        (return-void)
      )))");
  foo_method->get_code()->build_cfg();
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  auto demand = [&](IROpcode op) {
    auto* insn = find_insn(foo_method, op);
    auto root = create_node({insn});
    auto candidate = create_candidate(ota, root);
    return get_type_demand(candidate, insn->src(0));
  };
  EXPECT_EQ(demand(OPCODE_APUT_BYTE), type::_byte());
  EXPECT_EQ(demand(OPCODE_APUT_CHAR), type::_int());
}

// A `byte` demand and a `char` demand do not accept each other's type, and
// neither do `short` and `char`. ART accepts a value for both only if it is a
// boolean or a constant in their common range, and an `int` is neither. So the
// two demands have no common type, and `get_type_demand` falls back to the
// value's own type.
TEST_F(OutlinerTypeAnalysisTest, get_type_demand_byte_and_char_have_no_meet) {
  auto* foo_method = assembler::method_from_string(R"(
      (method (public static) "LFoo;.foo:(Z)V" (
        (load-param v0)
        (invoke-static (v0) "LFoo;.takeByte:(B)V")
        (invoke-static (v0) "LFoo;.takeChar:(C)V")
        (const v1 5)
        (invoke-static (v1) "LFoo;.takeShort:(S)V")
        (invoke-static (v1) "LFoo;.takeChar:(C)V")
        (return-void)
      )))");
  foo_method->get_code()->build_cfg();
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  {
    // the boolean that flows in satisfies both demands
    auto* insn1 = find_insn(foo_method, OPCODE_INVOKE_STATIC, 1);
    auto* insn2 = find_insn(foo_method, OPCODE_INVOKE_STATIC, 2);
    auto root = create_node({insn1, insn2});
    auto candidate = create_candidate(ota, root);
    EXPECT_EQ(get_type_demand(candidate, insn1->src(0)), type::_boolean());
  }

  {
    // the constant 5 satisfies both demands, but no parameter type does
    auto* insn1 = find_insn(foo_method, OPCODE_INVOKE_STATIC, 3);
    auto* insn2 = find_insn(foo_method, OPCODE_INVOKE_STATIC, 4);
    auto root = create_node({insn1, insn2});
    auto candidate = create_candidate(ota, root);
    EXPECT_EQ(get_type_demand(candidate, insn1->src(0)), nullptr);
  }
}

// ART types `and-int`, `or-int` and `xor-int` as boolean only when every
// operand is boolean, and as int otherwise, and of the integral types only a
// boolean is assignable to a `boolean`, `byte`, `short` or `char` demand. So a
// narrow demand on the result of a bitwise operation demands `boolean` of its
// operands; an `int` demand on the result demands `int`.
TEST_F(OutlinerTypeAnalysisTest, get_type_demand_through_bitwise) {
  auto* foo_method = assembler::method_from_string(R"(
      (method (public static) "LFoo;.foo:(CZ)V" (
        (load-param v0)
        (load-param v1)
        (and-int v2 v0 v1)
        (invoke-static (v2) "LFoo;.takeChar:(C)V")
        (or-int v3 v0 v1)
        (invoke-static (v3) "LFoo;.takeByte:(B)V")
        (xor-int/lit v4 v0 1)
        (invoke-static (v4) "LFoo;.takeShort:(S)V")
        (and-int v5 v0 v1)
        (invoke-static (v5) "LFoo;.takeBoolean:(Z)V")
        (and-int v6 v0 v1)
        (invoke-static (v6) "LFoo;.takeInt:(I)V")
        (invoke-static (v0) "LFoo;.takeChar:(C)V")
        (return-void)
      )))");
  foo_method->get_code()->build_cfg();
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  auto demand_through = [&](size_t occurrence,
                            std::vector<IRInstruction*> extra = {}) {
    auto* bitwise = find_insn(
        foo_method,
        [](IRInstruction* insn) {
          switch (insn->opcode()) {
          case OPCODE_AND_INT:
          case OPCODE_OR_INT:
          case OPCODE_XOR_INT_LIT:
            return true;
          default:
            return false;
          }
        },
        occurrence);
    auto* use = find_insn(foo_method, OPCODE_INVOKE_STATIC, occurrence);
    std::vector<IRInstruction*> insns{bitwise, use};
    insns.insert(insns.end(), extra.begin(), extra.end());
    auto root = create_node(insns);
    auto candidate = create_candidate(ota, root);
    return get_type_demand(candidate, bitwise->src(0));
  };

  EXPECT_EQ(demand_through(1), type::_boolean()) << "char demand on the result";
  EXPECT_EQ(demand_through(2), type::_boolean()) << "byte demand on the result";
  EXPECT_EQ(demand_through(3), type::_boolean())
      << "short demand on the result of a literal form";
  EXPECT_EQ(demand_through(4), type::_boolean())
      << "boolean demand on the result";
  EXPECT_EQ(demand_through(5), type::_int()) << "int demand on the result";
  // A direct `char` use beside a bitwise operation whose result is demanded
  // as `int` still demands `char`.
  EXPECT_EQ(demand_through(5, {find_insn(foo_method, OPCODE_INVOKE_STATIC, 6)}),
            type::_char());
}

TEST_F(OutlinerTypeAnalysisTest, get_type_demand_aput_object) {
  std::string src = R"(
      (
        (load-param-object v0)
        (load-param-object v1)
        (const v2 42)
        (aput-object v0 v1 v2)
        (return-void)
      ))";
  auto code = assembler::ircode_from_string(src);
  code->build_cfg();
  auto* foo_method = DexMethod::make_method(
                         "LFoo;.foo:(Ljava/lang/String;[Ljava/lang/String;)V")
                         ->make_concrete(ACC_PUBLIC, std::move(code),
                                         /*is_virtual=*/false);
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  {
    auto* insn = find_insn(foo_method, OPCODE_APUT_OBJECT);
    auto root = create_node({insn});
    auto candidate = create_candidate(ota, root);
    const auto* type0 = get_type_demand(candidate, insn->src(0));
    const auto* type1 = get_type_demand(candidate, insn->src(1));
    EXPECT_EQ(type0, type::java_lang_Object());
    EXPECT_EQ(type1, DexType::make_type("[Ljava/lang/Object;"));
  }
}

TEST_F(OutlinerTypeAnalysisTest, get_type_demand_inference) {
  ClassCreator i_creator(DexType::make_type("LI;"));
  i_creator.set_access(ACC_INTERFACE | ACC_ABSTRACT);
  i_creator.set_super(type::java_lang_Object());
  auto* i_type = i_creator.create()->get_type();
  ClassCreator j_creator(DexType::make_type("LJ;"));
  j_creator.set_access(ACC_INTERFACE | ACC_ABSTRACT);
  j_creator.set_super(type::java_lang_Object());
  auto* j_type = j_creator.create()->get_type();
  ClassCreator object_creator(type::java_lang_Object());
  ClassCreator bar_creator(DexType::make_type("LBar;"));
  bar_creator.set_super(type::java_lang_Object());
  bar_creator.add_interface(i_type);
  bar_creator.add_interface(j_type);
  auto* bar_type = bar_creator.create()->get_type();

  std::string src = R"(
      (
        (load-param-object v1)
        (load-param-object v2)
        (iput-object v2 v1 "LFoo;.i:LI;")
        (iput-object v2 v1 "LFoo;.j:LJ;")
        (return-void)
      ))";
  auto code = assembler::ircode_from_string(src);
  code->build_cfg();
  auto* foo_method = DexMethod::make_method("LFoo;.foo:(LBar;)V")
                         ->make_concrete(ACC_PUBLIC, std::move(code),
                                         /*is_virtual=*/false);
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);

  {
    // it's not clear what the narrowed type of {I, J} is; then type inference
    // will be used, which will determine that the incoming value is if type Bar
    // (which happens to implement the two interfaces)
    auto* insn1 = find_insn(foo_method, OPCODE_IPUT_OBJECT, 1);
    auto* insn2 = find_insn(foo_method, OPCODE_IPUT_OBJECT, 2);
    auto root = create_node({insn1, insn2});
    auto candidate = create_candidate(ota, root);
    const auto* result_type = get_type_demand(candidate, insn1->src(0));
    EXPECT_EQ(result_type, bar_type);
  }
}

namespace {

IRInstruction* find_invoke_of(DexMethod* method, std::string_view name) {
  for (const auto& mie : InstructionIterable(method->get_code()->cfg())) {
    if (mie.insn->has_method() && mie.insn->get_method()->str() == name) {
      return mie.insn;
    }
  }
  not_reached();
}

cfg::Block* block_of(cfg::ControlFlowGraph& cfg, const IRInstruction* insn) {
  for (auto* block : cfg.blocks()) {
    for (const auto& mie : InstructionIterable(block)) {
      if (mie.insn == insn) {
        return block;
      }
    }
  }
  not_reached();
}

// `LB;` extends `LA;`. `foo` receives an `LA;`. Inside a loop, it uses the
// value as an `LA;` and then overwrites it with an `LB;`. That overwrite is a
// definition INSIDE the loop body that still reaches the loop header, along the
// back edge. So a closure rooted at the header covers one of the definitions
// that reach its own entry. Excluding in-cover seed definitions guards against
// exactly this case.
DexMethod* create_back_edge_method() {
  ClassCreator object_creator(type::java_lang_Object());
  object_creator.create();
  ClassCreator a_creator(DexType::make_type("LA;"));
  a_creator.set_super(type::java_lang_Object());
  auto* a_type = a_creator.create()->get_type();
  ClassCreator b_creator(DexType::make_type("LB;"));
  b_creator.set_super(a_type);
  b_creator.create();

  auto* foo_method = assembler::method_from_string(R"(
      (method (public static) "LFoo;.foo:(LA;Z)V" (
        (load-param-object v0)
        (load-param v1)
        (:loop)
        (invoke-static (v0) "LFoo;.inspect:(LA;)V")
        (invoke-static () "LFoo;.makeB:()LB;")
        (move-result-object v0)
        (invoke-static (v0) "LFoo;.useB:(LB;)V")
        (if-nez v1 :loop)
        (return-void)
      )))");
  foo_method->get_code()->build_cfg();
  ClassCreator foo_creator(DexType::make_type("LFoo;"));
  foo_creator.set_super(type::java_lang_Object());
  foo_creator.add_method(foo_method);
  foo_creator.create();
  return foo_method;
}

} // namespace

// A split's parameter type is the MEET of its live-in's use demands. It must
// never be narrower than the type the caller actually passes. Seeding the walk
// from every reaching definition breaks that: a definition inside the cover
// adds the demands of its own uses. Here `useB` demands `LB;`, a strict subtype
// of the `LA;` the caller passes. The test asserts both seedings, so it fails
// if the in-cover exclusion stops making a difference in either direction.
TEST_F(OutlinerTypeAnalysisTest, in_cover_seed_defs_do_not_narrow_live_in) {
  auto* foo_method = create_back_edge_method();
  auto& cfg = foo_method->get_code()->cfg();
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);
  ReducedControlFlowGraph rcfg(cfg);

  Lazy<UnorderedMap<IRInstruction*, const ReducedBlock*>> insns([&rcfg] {
    auto res =
        std::make_unique<UnorderedMap<IRInstruction*, const ReducedBlock*>>();
    for (const auto* reduced_block : rcfg.blocks()) {
      for (const auto* block : UnorderedIterable(reduced_block->blocks)) {
        for (const auto& mie : InstructionIterable(block)) {
          res->emplace(mie.insn, reduced_block);
        }
      }
    }
    return res;
  });
  auto* first_insn = find_invoke_of(foo_method, "inspect");
  auto reg = first_insn->src(0);
  // The loop is a strongly-connected component, so it collapses to a single
  // reduced block, and that block alone is the closure's cover.
  UnorderedSet<const ReducedBlock*> cover{
      rcfg.get_reduced_block(block_of(cfg, first_insn))};

  const auto* a_type = DexType::get_type("LA;");
  const auto* b_type = DexType::get_type("LB;");
  ASSERT_NE(a_type, nullptr);
  ASSERT_NE(b_type, nullptr);

  auto in_cover = [&insns, &cover](IRInstruction* insn) {
    auto it = insns->find(insn);
    return it != insns->end() && cover.count(it->second) != 0u;
  };
  auto parameter_type =
      [&](const sparta::PatriciaTreeSet<IRInstruction*>& seeds) {
        return art::declare_parameter(
            ota.demand_of_uses(seeds, in_cover),
            [&]() { return ota.value_at(first_insn, reg); });
      };

  {
    // Seeding from every reaching def: `move-result-object` lies inside the
    // cover, so `useB`'s `LB;` demand joins the meet and wins. The split would
    // be typed against a subtype its caller never passes, and the host fails
    // verification handing it an `LA;`.
    EXPECT_EQ(parameter_type(ota.immediate_defs_at(first_insn, reg)), b_type);
  }

  {
    // With in-cover seed defs excluded, only the caller's `load-param-object`
    // seeds the walk, and the meet stays at the incoming `LA;`.
    auto seeds = ota.immediate_defs_at(first_insn, reg);
    seeds.filter([&](IRInstruction* def) { return !in_cover(def); });
    EXPECT_EQ(parameter_type(seeds), a_type);
  }
}

// A narrow demand on the result of a bitwise operation is met only by boolean
// operands, because ART types `and-int` as int as soon as one operand is not
// boolean. So the demand found through the `and-int` must not count as a
// demand on the operand itself. Here the boolean `v0` also has a direct `char`
// use. Counting both as `v0`'s own demands would type `v0` `char`, and the
// `and-int` inside the closure would then hand an int to `takeChar`.
TEST_F(OutlinerTypeAnalysisTest, narrow_demand_through_bitwise_is_boolean) {
  auto* foo_method = assembler::method_from_string(R"(
      (method (public static) "LFoo;.foo:(ZZ)V" (
        (load-param v0)
        (load-param v1)
        (invoke-static (v0) "LFoo;.takeChar:(C)V")
        (and-int v2 v0 v1)
        (invoke-static (v2) "LFoo;.takeChar:(C)V")
        (return-void)
      )))");
  foo_method->get_code()->build_cfg();
  auto& cfg = foo_method->get_code()->cfg();
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);
  ReducedControlFlowGraph rcfg(cfg);

  Lazy<UnorderedMap<IRInstruction*, const ReducedBlock*>> insns([&rcfg] {
    auto res =
        std::make_unique<UnorderedMap<IRInstruction*, const ReducedBlock*>>();
    for (const auto* reduced_block : rcfg.blocks()) {
      for (const auto* block : UnorderedIterable(reduced_block->blocks)) {
        for (const auto& mie : InstructionIterable(block)) {
          res->emplace(mie.insn, reduced_block);
        }
      }
    }
    return res;
  });

  IRInstruction* and_insn = nullptr;
  for (const auto& mie : InstructionIterable(cfg)) {
    if (mie.insn->opcode() == OPCODE_AND_INT) {
      and_insn = mie.insn;
    }
  }
  ASSERT_NE(and_insn, nullptr);
  UnorderedSet<const ReducedBlock*> cover{
      rcfg.get_reduced_block(block_of(cfg, and_insn))};
  auto* first_insn = find_invoke_of(foo_method, "takeChar");
  auto reg = and_insn->src(0);
  EXPECT_EQ(art::declare_parameter(
                ota.demand_of_uses(ota.immediate_defs_at(first_insn, reg),
                                   [&](IRInstruction* insn) {
                                     return cover.count(insns->at(insn)) != 0u;
                                   }),
                [&]() { return ota.value_at(first_insn, reg); }),
            type::_boolean());
}

// The same register as in `get_result_type_of_boolean_char_and_constant`,
// here as a value that reaches the outlined code. Declared as a parameter, it
// is `int`. Passed through as the result, it has no type.
TEST_F(OutlinerTypeAnalysisTest,
       get_inferred_type_of_boolean_char_and_constant) {
  auto* foo_method = assembler::method_from_string(R"(
      (method (public static) "LFoo;.foo:(ZCI)V" (
        (load-param v0)
        (load-param v1)
        (load-param v4)
        (const v2 2)
        (move v3 v0)
        (if-eqz v4 :char)
        (move v3 v1)
        (:char)
        (if-nez v4 :two)
        (move v3 v2)
        (:two)
        (sput v3 "LFoo;.i:I")
        (return-void)
      )))");
  foo_method->get_code()->build_cfg();
  outliner_impl::OutlinerTypeAnalysis ota(foo_method);
  auto* sput = find_insn(foo_method, OPCODE_SPUT);
  auto root = create_node({sput});
  auto candidate = create_candidate(ota, root);
  EXPECT_EQ(get_inferred_type(candidate, sput->src(0)), type::_int());
  EXPECT_EQ(get_inferred_type(candidate, sput->src(0),
                              /* as_result */ true),
            nullptr);
}
