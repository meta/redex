/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

// A test-only model of ART's verifier, as far as the kinds of values a method
// holds, uses, passes and returns: integral, float, long, double and reference.
//
// `IRTypeChecker` treats boolean, byte, short, char and int as one integer
// type. So it accepts a method that ART rejects whenever a boolean, byte,
// short or char value reaches a place declared with an integral type that does
// not hold it. Production code decides such types with
// `outliner_impl::IntegralType`; this model does not use it, so a test can
// catch that type being wrong.
//
// What it models:
// - A register holds one of ART's register kinds: the integral kinds and the
//   merge of android-16 `runtime/verifier/reg_type.cc` (`art16`, transcribed
//   below), float, the halves of a long, a double and a wide constant, a
//   reference, an uninitialized object, undefined or conflict.
// - ART merges the kinds that reach a point in the order it visits the paths,
//   and checks an instruction each time it reaches it. So a register here
//   holds every kind some order can give it: each kind that reaches it, and
//   each merge of those. A use is accepted only if ART accepts every one.
// - Before android-16, ART held a constant by its value rather than by a kind.
//   `pre16_merge_reaches_the_same_kinds` in OutlinerTypeAnalysisTest checks
//   that its merge reaches the same kinds, so the model applies to it too.
// - Each instruction's operands are judged as ART's `RegType::AssignableFrom`
//   judges them, and a field or array access must match the type it accesses.
//   A primitive put accepts any integral value. A `return` also accepts an int
//   where a narrower type is declared, and a byte where a boolean is.
// - An object is uninitialized from its `new-instance` until a constructor is
//   invoked on it, and so is `this` in a constructor until it calls another
//   one. As in ART, each register remembers which allocation it holds, and
//   the constructor call initializes every register holding the same one. A
//   register that holds the object uninitialized on one path and anything else
//   on another is a conflict. An uninitialized object may only be copied,
//   compared, locked or given its constructor, and a constructor may access
//   its own class's fields through `this`. Any other use rejects it, such as
//   passing it to a method or returning it.
// - An exception handler sees the registers as they were before the
//   instruction that threw, so an object whose constructor threw is still
//   uninitialized there.
// - A reference is otherwise judged only as a reference: its class is left to
//   `IRTypeChecker`. Only an array access reads the reference's type, to find
//   the element type.
//
// `describeArtTypeViolations` describes each use ART would reject on those
// grounds. An empty string means there is none. The shared splitter test
// harnesses run it on what every split kind emits, through
// `ArtTypeCheckOfOutput`.

#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <functional>
#include <map>
#include <optional>
#include <set>
#include <sstream>
#include <string>
#include <vector>

#include "ControlFlow.h"
#include "Debug.h"
#include "DexClass.h"
#include "IRInstruction.h"
#include "MethodUtil.h"
#include "ScopedCFG.h"
#include "Show.h"
#include "TypeUtil.h"

// The integral register kinds of android-16.0.0_r1
// `runtime/verifier/reg_type.h`, each group of constants in the enumerator
// order the merge relies on.
namespace art16 {

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

// The kind ART gives the 32-bit constant `value`.
constexpr uint8_t constant_kind(int64_t value) {
  if (value == 0) {
    return kZero;
  }
  if (value == 1) {
    return kBooleanConstant;
  }
  if (value > 0) {
    return value <= 127     ? kPositiveByteConstant
           : value <= 32767 ? kPositiveShortConstant
           : value <= 65535 ? kCharConstant
                            : kIntegerConstant;
  }
  return value >= -128     ? kByteConstant
         : value >= -32768 ? kShortConstant
                           : kIntegerConstant;
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

} // namespace art16

namespace method_splitting_test {

namespace art_types {

// The integral kinds are `art16`'s; the rest follow them.
enum Kind : uint8_t {
  kFloat = art16::kNumKinds,
  kLongLo,
  kLongHi,
  kDoubleLo,
  kDoubleHi,
  kConstantLo,
  kConstantHi,
  kReference,
  kUninitialized,
  kUndefined,
  kConflict,
  kNumKinds,
};
static_assert(kNumKinds <= 32);

constexpr bool is_integral(uint8_t k) { return k < art16::kNumKinds; }

// `art16::is_constant` is defined on the integral kinds only.
constexpr bool is_integral_constant(uint8_t k) {
  return is_integral(k) && art16::is_constant(k);
}

// `RegType::Merge` on two kinds. The integral merge is android-16's; the
// others are the same in every ART version. An uninitialized object merged
// with anything else is a conflict; `join` handles two different ones.
constexpr uint8_t merge(uint8_t a, uint8_t b) {
  if (a == b) {
    return a;
  }
  if (a == kUndefined || b == kUndefined) {
    return kUndefined;
  }
  if (a == kConflict || b == kConflict) {
    return kConflict;
  }
  if (is_integral(a) && is_integral(b)) {
    return art16::merge(a, b);
  }
  auto either_with = [&](uint8_t k, uint8_t other) {
    return (a == k && b == other) || (b == k && a == other);
  };
  // A float, long or double merged with a constant of its width keeps its
  // type, and a reference merged with zero stays a reference.
  for (uint8_t k : {kLongLo, kDoubleLo}) {
    if (either_with(k, kConstantLo)) {
      return k;
    }
  }
  for (uint8_t k : {kLongHi, kDoubleHi}) {
    if (either_with(k, kConstantHi)) {
      return k;
    }
  }
  if ((a == kFloat && is_integral_constant(b)) ||
      (b == kFloat && is_integral_constant(a))) {
    return kFloat;
  }
  if (either_with(kReference, art16::kZero)) {
    return kReference;
  }
  return kConflict;
}

// A set of kinds, one bit each.
using Kinds = uint32_t;

constexpr Kinds bit(uint8_t k) { return Kinds{1} << k; }

// `merge` on every pair of kinds.
constexpr auto kMerged = [] {
  std::array<std::array<uint8_t, kNumKinds>, kNumKinds> t{};
  for (uint8_t a = 0; a < kNumKinds; ++a) {
    for (uint8_t b = 0; b < kNumKinds; ++b) {
      t[a][b] = merge(a, b);
    }
  }
  return t;
}();

// `s` with every merge of its members added, until nothing new appears.
inline Kinds close_under_merge(Kinds s) {
  for (Kinds before = 0; before != s;) {
    before = s;
    for (Kinds as = before; as != 0; as &= as - 1) {
      const auto a = static_cast<uint8_t>(std::countr_zero(as));
      for (Kinds bs = before & (as - 1); bs != 0; bs &= bs - 1) {
        s |= bit(kMerged[a][std::countr_zero(bs)]);
      }
    }
  }
  return s;
}

// What a register may hold: its kinds, every type an instruction gives a
// reference, and, for `kUninitialized`, the instruction that allocated each
// uninitialized object it may hold: a `new-instance`, or the `load-param` of
// `this` in a constructor. ART tells uninitialized objects apart the same way,
// by where they were allocated.
struct Value {
  Kinds kinds{0};
  std::set<const DexType*, dextypes_comparator> types;
  std::set<const IRInstruction*> allocations;

  bool operator==(const Value& o) const = default;
};

// Joins `b` into `*a`: what a register holds where a path on which it holds
// `*a` meets one on which it holds `b`.
inline void join_into(Value* a, const Value& b) {
  a->types.insert(b.types.begin(), b.types.end());
  a->allocations.insert(b.allocations.begin(), b.allocations.end());
  Kinds kinds = a->kinds | b.kinds;
  // Two different uninitialized objects merge into a conflict.
  if (a->allocations.size() > 1) {
    kinds |= bit(kConflict);
  }
  a->kinds = close_under_merge(kinds);
}

inline Value join(const Value& a, const Value& b) {
  Value v = a;
  join_into(&v, b);
  return v;
}

inline Value single(uint8_t k, const DexType* type = nullptr) {
  Value v{bit(k), {}, {}};
  if (type != nullptr) {
    v.types.insert(type);
  }
  return v;
}

// The value of a register of type `t`, and of the register after it if `t` is
// wide.
inline std::pair<Value, Value> of_type(const DexType* t) {
  switch (type::to_datatype(t)) {
  case DataType::Boolean:
    return {single(art16::kBoolean), {}};
  case DataType::Byte:
    return {single(art16::kByte), {}};
  case DataType::Char:
    return {single(art16::kChar), {}};
  case DataType::Short:
    return {single(art16::kShort), {}};
  case DataType::Int:
    return {single(art16::kInteger), {}};
  case DataType::Float:
    return {single(kFloat), {}};
  case DataType::Long:
    return {single(kLongLo), single(kLongHi)};
  case DataType::Double:
    return {single(kDoubleLo), single(kDoubleHi)};
  case DataType::Object:
  case DataType::Array:
    return {single(kReference, t), {}};
  case DataType::Void:
    break;
  }
  not_reached_log("no value of type %s", SHOW(t));
}

// What a use requires of a register.
enum class Need : uint8_t {
  Boolean,
  Byte,
  Short,
  Char,
  Integral,
  Float,
  LongLo,
  LongHi,
  DoubleLo,
  DoubleHi,
  WideLo,
  WideHi,
  Category1,
  Reference,
  ReferenceOrUninitialized,
  IntegralOrReference,
};

inline std::string_view show_need(Need n) {
  static constexpr std::string_view kNames[] = {
      "boolean",
      "byte",
      "short",
      "char",
      "int",
      "float",
      "long",
      "long (high half)",
      "double",
      "double (high half)",
      "a wide value",
      "a wide value (high half)",
      "an int or a float",
      "a reference",
      "a reference or an uninitialized object",
      "an int or a reference",
  };
  return kNames[static_cast<size_t>(n)];
}

// `RegType::AssignableFrom(lhs, k)` for the `lhs` that `n` stands for, and
// the category checks of ART's moves.
constexpr bool assignable(Need n, uint8_t k) {
  switch (n) {
  case Need::Boolean:
    return is_integral(k) && art16::is_boolean_types(k);
  case Need::Byte:
    return is_integral(k) && art16::is_byte_types(k);
  case Need::Short:
    return is_integral(k) && art16::is_short_types(k);
  case Need::Char:
    return is_integral(k) && art16::is_char_types(k);
  case Need::Integral:
    return is_integral(k);
  case Need::Float:
    return k == kFloat || is_integral_constant(k);
  case Need::LongLo:
    return k == kLongLo || k == kConstantLo;
  case Need::LongHi:
    return k == kLongHi || k == kConstantHi;
  case Need::DoubleLo:
    return k == kDoubleLo || k == kConstantLo;
  case Need::DoubleHi:
    return k == kDoubleHi || k == kConstantHi;
  case Need::WideLo:
    return k == kLongLo || k == kDoubleLo || k == kConstantLo;
  case Need::WideHi:
    return k == kLongHi || k == kDoubleHi || k == kConstantHi;
  case Need::Category1:
    return is_integral(k) || k == kFloat;
  case Need::Reference:
    return k == kReference || k == art16::kZero;
  case Need::ReferenceOrUninitialized:
    return k == kReference || k == art16::kZero || k == kUninitialized;
  case Need::IntegralOrReference:
    return is_integral(k) || k == kReference || k == kUninitialized;
  }
  return false;
}

// The needs of a value declared `t`, the second one for the register after it
// if `t` is wide. A put accepts any integral value where `t` is integral.
inline std::vector<Need> needs_of(const DexType* t, bool put = false) {
  switch (type::to_datatype(t)) {
  case DataType::Boolean:
    return {put ? Need::Integral : Need::Boolean};
  case DataType::Byte:
    return {put ? Need::Integral : Need::Byte};
  case DataType::Char:
    return {put ? Need::Integral : Need::Char};
  case DataType::Short:
    return {put ? Need::Integral : Need::Short};
  case DataType::Int:
    return {Need::Integral};
  case DataType::Float:
    return {Need::Float};
  case DataType::Long:
    return {Need::LongLo, Need::LongHi};
  case DataType::Double:
    return {Need::DoubleLo, Need::DoubleHi};
  case DataType::Object:
  case DataType::Array:
    return {Need::Reference};
  case DataType::Void:
    break;
  }
  not_reached_log("no value of type %s", SHOW(t));
}

inline std::string show_kinds(Kinds s) {
  static constexpr std::string_view kNames[] = {
      "boolean",
      "byte",
      "char",
      "short",
      "int",
      "zero",
      "const 1",
      "const 2..127",
      "const 128..32767",
      "const 32768..65535",
      "const -128..-1",
      "const -32768..-129",
      "const int",
      "float",
      "long",
      "long (high half)",
      "double",
      "double (high half)",
      "wide const",
      "wide const (high half)",
      "a reference",
      "an uninitialized object",
      "undefined",
      "conflict",
  };
  static_assert(std::size(kNames) == kNumKinds);
  std::string out;
  for (uint8_t k = 0; k < kNumKinds; ++k) {
    if ((s & bit(k)) != 0) {
      out += out.empty() ? "" : " | ";
      out += kNames[k];
    }
  }
  return out.empty() ? "nothing" : out;
}

// Whether a field or array access by `op` may access a value of type `t`. A
// 32-bit access also serves `float`, and a wide one `double`.
inline bool access_matches(IROpcode op, const DexType* t) {
  switch (op) {
  case OPCODE_AGET:
  case OPCODE_APUT:
  case OPCODE_IGET:
  case OPCODE_IPUT:
  case OPCODE_SGET:
  case OPCODE_SPUT:
    return t == type::_int() || t == type::_float();
  case OPCODE_AGET_WIDE:
  case OPCODE_APUT_WIDE:
  case OPCODE_IGET_WIDE:
  case OPCODE_IPUT_WIDE:
  case OPCODE_SGET_WIDE:
  case OPCODE_SPUT_WIDE:
    return type::is_wide_type(t);
  case OPCODE_AGET_OBJECT:
  case OPCODE_APUT_OBJECT:
  case OPCODE_IGET_OBJECT:
  case OPCODE_IPUT_OBJECT:
  case OPCODE_SGET_OBJECT:
  case OPCODE_SPUT_OBJECT:
    return type::is_object(t);
  case OPCODE_AGET_BOOLEAN:
  case OPCODE_APUT_BOOLEAN:
  case OPCODE_IGET_BOOLEAN:
  case OPCODE_IPUT_BOOLEAN:
  case OPCODE_SGET_BOOLEAN:
  case OPCODE_SPUT_BOOLEAN:
    return t == type::_boolean();
  case OPCODE_AGET_BYTE:
  case OPCODE_APUT_BYTE:
  case OPCODE_IGET_BYTE:
  case OPCODE_IPUT_BYTE:
  case OPCODE_SGET_BYTE:
  case OPCODE_SPUT_BYTE:
    return t == type::_byte();
  case OPCODE_AGET_CHAR:
  case OPCODE_APUT_CHAR:
  case OPCODE_IGET_CHAR:
  case OPCODE_IPUT_CHAR:
  case OPCODE_SGET_CHAR:
  case OPCODE_SPUT_CHAR:
    return t == type::_char();
  default:
    return t == type::_short();
  }
}

// The element types of the arrays `v` may hold.
inline std::vector<const DexType*> elements_of(const Value& v) {
  std::vector<const DexType*> out;
  for (const auto* t : v.types) {
    if (type::is_array(t)) {
      out.push_back(type::get_array_component_type(t));
    }
  }
  return out;
}

// The type an access by `op` reads when the model does not know the array's.
inline const DexType* default_element(IROpcode op) {
  switch (op) {
  case OPCODE_AGET:
    return type::_int();
  case OPCODE_AGET_WIDE:
    return type::_long();
  case OPCODE_AGET_OBJECT:
    return type::java_lang_Object();
  case OPCODE_AGET_BOOLEAN:
    return type::_boolean();
  case OPCODE_AGET_BYTE:
    return type::_byte();
  case OPCODE_AGET_CHAR:
    return type::_char();
  default:
    return type::_short();
  }
}

using State = std::map<reg_t, Value>;

inline const Value& value_in(const State& st, reg_t r) {
  static const Value undefined = single(kUndefined);
  auto it = st.find(r);
  return it == st.end() ? undefined : it->second;
}

// One use: `reg` must meet `need`; `what` names it in a report. A `malformed`
// use is rejected whatever the register holds, and `what` says why. A `copy`
// also accepts a conflict: ART lets `move` and `move-object` copy one, and
// rejects it only where it is used.
struct Use {
  reg_t reg;
  Need need;
  std::string what;
  bool malformed{false};
  bool copy{false};
};

// What `insn` requires of its registers, in state `st`.
inline std::vector<Use> uses_of(const DexMethod* m,
                                const IRInstruction* insn,
                                const State& st) {
  std::vector<Use> uses;
  auto use_reg = [&](reg_t r, Need n, std::string what) {
    uses.push_back({r, n, std::move(what), /* malformed */ false,
                    /* copy */ false});
  };
  auto use = [&](size_t i, Need n, std::string what = "") {
    use_reg(insn->src(i), n,
            what.empty() ? "v" + std::to_string(insn->src(i))
                         : std::move(what));
  };
  auto use_declared = [&](size_t i, const DexType* t, bool put,
                          const std::string& what) {
    auto needs = needs_of(t, put);
    use(i, needs[0], what);
    if (needs.size() == 2) {
      use_reg(insn->src(i) + 1, needs[1], what + " (high half)");
    }
  };
  auto malformed = [&](std::string why) {
    uses.push_back({0, Need::Reference, std::move(why), /* malformed */ true,
                    /* copy */ false});
  };
  auto op = insn->opcode();
  const auto* rtype = m->get_proto()->get_rtype();
  switch (op) {
  case OPCODE_RETURN_VOID:
    if (rtype != type::_void()) {
      malformed("returns nothing from a method declared " + show(rtype));
    }
    return uses;
  case OPCODE_RETURN:
  case OPCODE_RETURN_WIDE:
  case OPCODE_RETURN_OBJECT: {
    const bool fits =
        rtype != type::_void() &&
        (op == OPCODE_RETURN_OBJECT
             ? type::is_object(rtype)
             : !type::is_object(rtype) &&
                   type::is_wide_type(rtype) == (op == OPCODE_RETURN_WIDE));
    if (!fits) {
      malformed("is the wrong return for a method declared " + show(rtype));
    } else {
      use_declared(0, rtype, /* put */ false, "return");
    }
    return uses;
  }
  case OPCODE_MOVE:
    use(0, Need::Category1);
    uses.back().copy = true;
    return uses;
  case OPCODE_MOVE_OBJECT:
    use(0, Need::ReferenceOrUninitialized);
    uses.back().copy = true;
    return uses;
  case OPCODE_MOVE_WIDE:
    use(0, Need::WideLo);
    use_reg(insn->src(0) + 1, Need::WideHi,
            "v" + std::to_string(insn->src(0)) + " (high half)");
    return uses;
  case OPCODE_MOVE_RESULT:
  case IOPCODE_MOVE_RESULT_PSEUDO:
    use_reg(RESULT_REGISTER, Need::Category1, "the result");
    return uses;
  case OPCODE_MOVE_RESULT_OBJECT:
  case IOPCODE_MOVE_RESULT_PSEUDO_OBJECT:
    use_reg(RESULT_REGISTER, Need::ReferenceOrUninitialized, "the result");
    return uses;
  case OPCODE_MOVE_RESULT_WIDE:
  case IOPCODE_MOVE_RESULT_PSEUDO_WIDE:
    use_reg(RESULT_REGISTER, Need::WideLo, "the result");
    use_reg(RESULT_REGISTER + 1, Need::WideHi, "the result (high half)");
    return uses;
  case OPCODE_MONITOR_ENTER:
  case OPCODE_MONITOR_EXIT:
    use(0, Need::ReferenceOrUninitialized);
    return uses;
  case OPCODE_THROW:
  case OPCODE_CHECK_CAST:
  case OPCODE_INSTANCE_OF:
  case OPCODE_ARRAY_LENGTH:
  case OPCODE_FILL_ARRAY_DATA:
    use(0, Need::Reference);
    return uses;
  case OPCODE_NEW_ARRAY:
    use(0, Need::Integral);
    return uses;
  case OPCODE_FILLED_NEW_ARRAY:
    for (size_t i = 0; i < insn->srcs_size(); ++i) {
      use_declared(i, type::get_array_component_type(insn->get_type()),
                   /* put */ true, "element " + std::to_string(i));
    }
    return uses;
  case OPCODE_SWITCH:
  case OPCODE_IF_LT:
  case OPCODE_IF_GE:
  case OPCODE_IF_GT:
  case OPCODE_IF_LE:
  case OPCODE_IF_LTZ:
  case OPCODE_IF_GEZ:
  case OPCODE_IF_GTZ:
  case OPCODE_IF_LEZ:
    for (size_t i = 0; i < insn->srcs_size(); ++i) {
      use(i, Need::Integral);
    }
    return uses;
  case OPCODE_IF_EQZ:
  case OPCODE_IF_NEZ:
    use(0, Need::IntegralOrReference);
    return uses;
  default:
    break;
  }
  if (opcode::is_an_aget(op) || opcode::is_an_aput(op)) {
    const size_t array = opcode::is_an_aget(op) ? 0 : 1;
    use(array, Need::Reference, "the array");
    use(array + 1, Need::Integral, "the index");
    std::vector<Need> value_needs;
    for (const auto* element : elements_of(value_in(st, insn->src(array)))) {
      if (!access_matches(op, element)) {
        malformed("accesses an element of type " + show(element));
        continue;
      }
      if (opcode::is_an_aput(op)) {
        for (auto n : needs_of(element, /* put */ true)) {
          if (std::find(value_needs.begin(), value_needs.end(), n) ==
              value_needs.end()) {
            value_needs.push_back(n);
          }
        }
      }
    }
    for (auto n : value_needs) {
      const bool high = n == Need::LongHi || n == Need::DoubleHi;
      use_reg(insn->src(0) + (high ? 1 : 0), n,
              high ? "the value (high half)" : "the value");
    }
    return uses;
  }
  if (opcode::is_an_ifield_op(op) || opcode::is_an_sfield_op(op)) {
    const auto* field_type = insn->get_field()->get_type();
    if (!access_matches(op, field_type)) {
      malformed("accesses a field of type " + show(field_type));
      return uses;
    }
    const bool put = opcode::is_an_iput(op) || opcode::is_an_sput(op);
    if (opcode::is_an_ifield_op(op)) {
      const size_t object = put ? 1 : 0;
      // A constructor may access its own class's fields through `this`
      // before `this` is initialized.
      const auto& allocations = value_in(st, insn->src(object)).allocations;
      const bool own_field_of_this =
          method::is_init(m) &&
          insn->get_field()->get_class() == m->get_class() &&
          std::all_of(allocations.begin(), allocations.end(),
                      [](const IRInstruction* a) {
                        return opcode::is_a_load_param(a->opcode());
                      });
      use(object,
          own_field_of_this ? Need::ReferenceOrUninitialized : Need::Reference,
          "the object");
    }
    if (put) {
      use_declared(0, field_type, /* put */ true, "the value");
    }
    return uses;
  }
  if (opcode::is_a_method_invoke(op)) {
    const auto* args = insn->get_method()->get_proto()->get_args();
    const size_t first = op == OPCODE_INVOKE_STATIC ? 0 : 1;
    if (insn->srcs_size() != args->size() + first) {
      malformed("passes " + std::to_string(insn->srcs_size()) +
                " values where " + std::to_string(args->size() + first) +
                " are expected");
      return uses;
    }
    if (first == 1) {
      // A constructor is what initializes its receiver.
      const bool init =
          op == OPCODE_INVOKE_DIRECT && method::is_init(insn->get_method());
      use(0, init ? Need::ReferenceOrUninitialized : Need::Reference,
          "the receiver");
    }
    for (size_t i = first; i < insn->srcs_size(); ++i) {
      use_declared(i, args->at(i - first), /* put */ false,
                   "argument " + std::to_string(i));
    }
    return uses;
  }
  // Arithmetic and conversions: each source by the operand type of `op`.
  auto operands = [&](Need lo, bool wide, size_t from, size_t to) {
    for (size_t i = from; i < to; ++i) {
      use(i, lo);
      if (wide) {
        use_reg(insn->src(i) + 1,
                lo == Need::LongLo ? Need::LongHi : Need::DoubleHi,
                "v" + std::to_string(insn->src(i)) + " (high half)");
      }
    }
  };
  switch (op) {
  case OPCODE_NEG_INT:
  case OPCODE_NOT_INT:
  case OPCODE_INT_TO_LONG:
  case OPCODE_INT_TO_FLOAT:
  case OPCODE_INT_TO_DOUBLE:
  case OPCODE_INT_TO_BYTE:
  case OPCODE_INT_TO_CHAR:
  case OPCODE_INT_TO_SHORT:
  case OPCODE_ADD_INT:
  case OPCODE_SUB_INT:
  case OPCODE_MUL_INT:
  case OPCODE_DIV_INT:
  case OPCODE_REM_INT:
  case OPCODE_AND_INT:
  case OPCODE_OR_INT:
  case OPCODE_XOR_INT:
  case OPCODE_SHL_INT:
  case OPCODE_SHR_INT:
  case OPCODE_USHR_INT:
    operands(Need::Integral, false, 0, insn->srcs_size());
    break;
  case OPCODE_NEG_LONG:
  case OPCODE_NOT_LONG:
  case OPCODE_LONG_TO_INT:
  case OPCODE_LONG_TO_FLOAT:
  case OPCODE_LONG_TO_DOUBLE:
  case OPCODE_ADD_LONG:
  case OPCODE_SUB_LONG:
  case OPCODE_MUL_LONG:
  case OPCODE_DIV_LONG:
  case OPCODE_REM_LONG:
  case OPCODE_AND_LONG:
  case OPCODE_OR_LONG:
  case OPCODE_XOR_LONG:
  case OPCODE_CMP_LONG:
    operands(Need::LongLo, true, 0, insn->srcs_size());
    break;
  case OPCODE_SHL_LONG:
  case OPCODE_SHR_LONG:
  case OPCODE_USHR_LONG:
    operands(Need::LongLo, true, 0, 1);
    operands(Need::Integral, false, 1, 2);
    break;
  case OPCODE_NEG_FLOAT:
  case OPCODE_FLOAT_TO_INT:
  case OPCODE_FLOAT_TO_LONG:
  case OPCODE_FLOAT_TO_DOUBLE:
  case OPCODE_ADD_FLOAT:
  case OPCODE_SUB_FLOAT:
  case OPCODE_MUL_FLOAT:
  case OPCODE_DIV_FLOAT:
  case OPCODE_REM_FLOAT:
  case OPCODE_CMPL_FLOAT:
  case OPCODE_CMPG_FLOAT:
    operands(Need::Float, false, 0, insn->srcs_size());
    break;
  case OPCODE_NEG_DOUBLE:
  case OPCODE_DOUBLE_TO_INT:
  case OPCODE_DOUBLE_TO_LONG:
  case OPCODE_DOUBLE_TO_FLOAT:
  case OPCODE_ADD_DOUBLE:
  case OPCODE_SUB_DOUBLE:
  case OPCODE_MUL_DOUBLE:
  case OPCODE_DIV_DOUBLE:
  case OPCODE_REM_DOUBLE:
  case OPCODE_CMPL_DOUBLE:
  case OPCODE_CMPG_DOUBLE:
    operands(Need::DoubleLo, true, 0, insn->srcs_size());
    break;
  default:
    if (opcode::is_an_int_lit(op)) {
      operands(Need::Integral, false, 0, 1);
    }
    break;
  }
  return uses;
}

// Whether ART's `if-eq` or `if-ne` accepts comparing kinds `a` and `b`: two
// integral values or two references, initialized or not.
constexpr bool comparable(uint8_t a, uint8_t b) {
  auto reference = [](uint8_t k) {
    return k == kReference || k == art16::kZero || k == kUninitialized;
  };
  return (is_integral(a) && is_integral(b)) || (reference(a) && reference(b));
}

// Whether ART's `return` accepts kind `k` where `rtype` is declared: it also
// takes an int for any narrower integral type, and a byte for a boolean.
inline bool return_accepts(const DexType* rtype, uint8_t k) {
  if (k == art16::kInteger && type::is_integral(rtype) &&
      rtype != type::_int()) {
    return true;
  }
  return k == art16::kByte && rtype == type::_boolean();
}

// The result type of arithmetic or a conversion `op`.
inline const DexType* arithmetic_result(IROpcode op) {
  switch (op) {
  case OPCODE_NEG_FLOAT:
  case OPCODE_INT_TO_FLOAT:
  case OPCODE_LONG_TO_FLOAT:
  case OPCODE_DOUBLE_TO_FLOAT:
  case OPCODE_ADD_FLOAT:
  case OPCODE_SUB_FLOAT:
  case OPCODE_MUL_FLOAT:
  case OPCODE_DIV_FLOAT:
  case OPCODE_REM_FLOAT:
    return type::_float();
  case OPCODE_NEG_DOUBLE:
  case OPCODE_INT_TO_DOUBLE:
  case OPCODE_LONG_TO_DOUBLE:
  case OPCODE_FLOAT_TO_DOUBLE:
  case OPCODE_ADD_DOUBLE:
  case OPCODE_SUB_DOUBLE:
  case OPCODE_MUL_DOUBLE:
  case OPCODE_DIV_DOUBLE:
  case OPCODE_REM_DOUBLE:
    return type::_double();
  case OPCODE_NEG_LONG:
  case OPCODE_NOT_LONG:
  case OPCODE_INT_TO_LONG:
  case OPCODE_FLOAT_TO_LONG:
  case OPCODE_DOUBLE_TO_LONG:
  case OPCODE_ADD_LONG:
  case OPCODE_SUB_LONG:
  case OPCODE_MUL_LONG:
  case OPCODE_DIV_LONG:
  case OPCODE_REM_LONG:
  case OPCODE_AND_LONG:
  case OPCODE_OR_LONG:
  case OPCODE_XOR_LONG:
  case OPCODE_SHL_LONG:
  case OPCODE_SHR_LONG:
  case OPCODE_USHR_LONG:
    return type::_long();
  case OPCODE_INT_TO_BYTE:
    return type::_byte();
  case OPCODE_INT_TO_CHAR:
    return type::_char();
  case OPCODE_INT_TO_SHORT:
    return type::_short();
  default:
    return type::_int();
  }
}

// The type of the object `allocation` creates: a `new-instance`, or the
// `load-param` of `this` in a constructor of `m`.
inline const DexType* allocated_type(const DexMethod* m,
                                     const IRInstruction* allocation) {
  return opcode::is_a_load_param(allocation->opcode()) ? m->get_class()
                                                       : allocation->get_type();
}

// Rewrites every register that may hold the uninitialized object `allocation`
// creates: it holds `kind` instead.
inline void replace_allocation(const DexMethod* m,
                               const IRInstruction* allocation,
                               uint8_t kind,
                               State* st) {
  for (auto& [r, v] : *st) {
    if (v.allocations.erase(allocation) == 0) {
      continue;
    }
    if (v.allocations.empty()) {
      v.kinds &= ~bit(kUninitialized);
    }
    v.kinds = close_under_merge(v.kinds | bit(kind));
    if (kind == kReference) {
      v.types.insert(allocated_type(m, allocation));
    }
  }
}

// Applies what `insn` defines to `st`.
inline void transfer(DexMethod* m,
                     IRInstruction* insn,
                     size_t* param_idx,
                     State* st) {
  auto get = [&](reg_t r) { return value_in(*st, r); };
  using Pair = std::pair<Value, Value>;
  auto set = [&](reg_t r, const Pair& v, bool wide) {
    (*st)[r] = v.first;
    if (wide) {
      (*st)[r + 1] = v.second;
    }
  };
  auto set_dest = [&](const Pair& v) {
    set(insn->dest(), v, insn->dest_is_wide());
  };
  auto set_result = [&](const Pair& v) { set(RESULT_REGISTER, v, true); };
  auto of_kind = [](uint8_t k) { return Pair{single(k), {}}; };
  auto op = insn->opcode();
  switch (op) {
  case IOPCODE_LOAD_PARAM:
  case IOPCODE_LOAD_PARAM_OBJECT:
  case IOPCODE_LOAD_PARAM_WIDE: {
    size_t idx = (*param_idx)++;
    if (!is_static(m)) {
      if (idx == 0) {
        // In a constructor, `this` is uninitialized until it calls another
        // constructor, except in `Object`'s, which has none to call.
        if (method::is_init(m) && m->get_class() != type::java_lang_Object()) {
          set_dest({Value{bit(kUninitialized), {}, {insn}}, {}});
        } else {
          set_dest({single(kReference, m->get_class()), {}});
        }
        return;
      }
      --idx;
    }
    set_dest(of_type(m->get_proto()->get_args()->at(idx)));
    return;
  }
  case OPCODE_CONST:
  case IOPCODE_R_CONST:
    set_dest(of_kind(art16::constant_kind(insn->get_literal())));
    return;
  case OPCODE_CONST_WIDE:
    set_dest({single(kConstantLo), single(kConstantHi)});
    return;
  case IOPCODE_INJECTION_ID:
    set_dest(of_kind(art16::kInteger));
    return;
  case IOPCODE_UNREACHABLE:
    set_dest(of_kind(art16::kZero));
    return;
  case OPCODE_MOVE:
  case OPCODE_MOVE_OBJECT:
    set_dest({get(insn->src(0)), {}});
    return;
  case OPCODE_MOVE_WIDE:
    set_dest({get(insn->src(0)), get(insn->src(0) + 1)});
    return;
  case OPCODE_MOVE_RESULT:
  case OPCODE_MOVE_RESULT_OBJECT:
  case OPCODE_MOVE_RESULT_WIDE:
  case IOPCODE_MOVE_RESULT_PSEUDO:
  case IOPCODE_MOVE_RESULT_PSEUDO_OBJECT:
  case IOPCODE_MOVE_RESULT_PSEUDO_WIDE:
    set_dest({get(RESULT_REGISTER), get(RESULT_REGISTER + 1)});
    return;
  case OPCODE_MOVE_EXCEPTION:
    set_dest(of_kind(kReference));
    return;
  case OPCODE_CONST_STRING:
    set_result({single(kReference, type::java_lang_String()), {}});
    return;
  case OPCODE_CONST_CLASS:
    set_result({single(kReference, type::java_lang_Class()), {}});
    return;
  case OPCODE_CONST_METHOD_HANDLE:
  case OPCODE_CONST_METHOD_TYPE:
    set_result(of_kind(kReference));
    return;
  case OPCODE_NEW_INSTANCE:
    // An object this instruction allocated earlier and that is still
    // uninitialized can no longer be used: ART could not tell it from the
    // new one.
    replace_allocation(m, insn, kConflict, st);
    set_result({Value{bit(kUninitialized), {}, {insn}}, {}});
    return;
  case OPCODE_NEW_ARRAY:
  case OPCODE_FILLED_NEW_ARRAY:
  case OPCODE_CHECK_CAST:
    set_result({single(kReference, insn->get_type()), {}});
    return;
  case OPCODE_INSTANCE_OF:
    set_result(of_kind(art16::kBoolean));
    return;
  case OPCODE_ARRAY_LENGTH:
    set_result(of_kind(art16::kInteger));
    return;
  case OPCODE_CMPL_FLOAT:
  case OPCODE_CMPG_FLOAT:
  case OPCODE_CMPL_DOUBLE:
  case OPCODE_CMPG_DOUBLE:
  case OPCODE_CMP_LONG:
    set_dest(of_kind(art16::kInteger));
    return;
  case OPCODE_AND_INT:
  case OPCODE_OR_INT:
  case OPCODE_XOR_INT:
  case OPCODE_AND_INT_LIT:
  case OPCODE_OR_INT_LIT:
  case OPCODE_XOR_INT_LIT: {
    // Boolean when every operand is, in each order's combination of kinds.
    const bool lit = opcode::is_an_int_lit(op);
    const bool boolean_lit =
        lit && insn->get_literal() >= 0 && insn->get_literal() <= 1;
    auto boolean = [](uint8_t k) {
      return is_integral(k) && art16::is_boolean_types(k);
    };
    const Kinds a = get(insn->src(0)).kinds;
    const Kinds b =
        lit ? bit(boolean_lit ? art16::kBooleanConstant : art16::kInteger)
            : get(insn->src(1)).kinds;
    Kinds out = 0;
    for (uint8_t x = 0; x < kNumKinds; ++x) {
      for (uint8_t y = 0; y < kNumKinds; ++y) {
        if ((a & bit(x)) != 0 && (b & bit(y)) != 0) {
          out |=
              bit(boolean(x) && boolean(y) ? art16::kBoolean : art16::kInteger);
        }
      }
    }
    set_dest({{out, {}, {}}, {}});
    return;
  }
  default:
    break;
  }
  if (opcode::is_an_aget(op)) {
    // Each array the register may hold gives its element type. An access to
    // an array whose type the model does not know reads the opcode's type.
    auto elements = elements_of(get(insn->src(0)));
    Pair out;
    bool known = false;
    for (const auto* element : elements) {
      if (access_matches(op, element)) {
        auto v = of_type(element);
        out = {join(out.first, v.first), join(out.second, v.second)};
        known = true;
      }
    }
    set_result(known ? out : of_type(default_element(op)));
    return;
  }
  if (op == OPCODE_INVOKE_DIRECT && method::is_init(insn->get_method())) {
    // The constructor initializes the object in every register that holds it.
    const auto allocations = get(insn->src(0)).allocations;
    for (const auto* allocation : allocations) {
      replace_allocation(m, allocation, kReference, st);
    }
    return;
  }
  if (opcode::is_a_method_invoke(op)) {
    const auto* rtype = insn->get_method()->get_proto()->get_rtype();
    if (rtype != type::_void()) {
      set_result(of_type(rtype));
    }
    return;
  }
  if (opcode::is_an_sget(op) || opcode::is_an_iget(op)) {
    set_result(of_type(insn->get_field()->get_type()));
    return;
  }
  // What is left is arithmetic or a conversion. A division or a remainder
  // delivers its result through a `move-result-pseudo`.
  if (insn->has_dest()) {
    always_assert_log(!insn->dest_is_object(), "unmodeled %s", SHOW(insn));
    set_dest(of_type(arithmetic_result(op)));
  } else if (insn->has_move_result_pseudo()) {
    set_result(of_type(arithmetic_result(op)));
  }
}

// Joins state `b` into `*a`: the state where paths in states `*a` and `b`
// meet. A register that one of them does not define is undefined on that path.
inline void join_states_into(State* a, const State& b) {
  for (auto& [r, v] : *a) {
    join_into(&v, value_in(b, r));
  }
  for (const auto& [r, v] : b) {
    if (!a->contains(r)) {
      a->emplace(r, join(single(kUndefined), v));
    }
  }
}

// The join of the states that some slots hold, kept current as single slots
// change: a change joins a logarithmic number of states, where joining every
// slot again would join them all. A slot holds nothing until it is set. The
// join does not depend on the order or grouping of the states it joins, so it
// is what joining the slots one after another gives.
class SlotJoin {
 public:
  explicit SlotJoin(size_t slots)
      : m_leaves(std::bit_ceil(std::max<size_t>(slots, 1))),
        m_nodes(2 * m_leaves) {}

  // Sets `slot` to hold `*state`, or nothing if `state` is null.
  void set(size_t slot, const State* state) {
    size_t i = m_leaves + slot;
    if (state != nullptr) {
      m_nodes[i] = *state;
    } else {
      m_nodes[i].reset();
    }
    for (i /= 2; i > 0; i /= 2) {
      const auto& left = m_nodes[2 * i];
      const auto& right = m_nodes[2 * i + 1];
      m_nodes[i] = left ? left : right;
      if (left && right) {
        join_states_into(&*m_nodes[i], *right);
      }
    }
  }

  // The join of every slot, or nothing if no slot holds a state.
  const std::optional<State>& joined() const { return m_nodes[1]; }

 private:
  // The tree is complete: node `i` joins nodes `2i` and `2i + 1`, and slot `s`
  // is node `m_leaves + s`.
  size_t m_leaves;
  std::vector<std::optional<State>> m_nodes;
};

// What a block passes on: the state at its exit to its successors, and to its
// exception handlers the states before each instruction in it that may throw.
// A block with no such instruction passes nothing to a handler.
struct BlockOut {
  State exit;
  std::optional<State> at_throw;

  bool operator==(const BlockOut& o) const = default;
};

// Runs the model over `m` and appends a line per rejected use to `out`. A call
// to one of `checked`, the methods judged together with `m`, crosses the
// boundary of a split, and a report on it says so.
inline void check_method(
    DexMethod* m,
    const std::set<const DexMethodRef*, dexmethods_comparator>& checked,
    std::ostringstream* out) {
  cfg::ScopedCFG scoped_cfg(m->get_code());
  auto& cfg = *scoped_cfg;
  // What each block a path from the entry has reached passes on. ART visits
  // only such blocks.
  std::map<cfg::BlockId, BlockOut> block_outs;
  // For each block, the join of what its predecessors in `block_outs` pass
  // along its incoming edges, one slot per edge in `preds()` order.
  std::map<cfg::BlockId, SlotJoin> entry_joins;
  std::map<const cfg::Edge*, size_t> slot_of;
  for (auto* b : cfg.blocks()) {
    for (size_t i = 0; i < b->preds().size(); ++i) {
      slot_of.emplace(b->preds()[i], i);
    }
  }
  auto entry_state = [&](cfg::Block* b) {
    auto it = entry_joins.find(b->id());
    if (it == entry_joins.end() || !it->second.joined()) {
      return State{};
    }
    return *it->second.joined();
  };
  using Visit = std::function<void(IRInstruction*, const State&)>;
  auto run_block = [&](cfg::Block* b, const Visit& visit) {
    BlockOut o{entry_state(b), std::nullopt};
    size_t param_idx = 0;
    for (auto& mie : InstructionIterable(b)) {
      visit(mie.insn, o.exit);
      if (opcode::can_throw(mie.insn->opcode())) {
        if (o.at_throw) {
          join_states_into(&*o.at_throw, o.exit);
        } else {
          o.at_throw = o.exit;
        }
      }
      transfer(m, mie.insn, &param_idx, &o.exit);
    }
    return o;
  };
  // States only grow, and there are finitely many, so the worklist empties.
  std::vector<cfg::Block*> work{cfg.entry_block()};
  while (!work.empty()) {
    auto* b = work.back();
    work.pop_back();
    BlockOut o = run_block(b, [](IRInstruction*, const State&) {});
    auto it = block_outs.find(b->id());
    if (it != block_outs.end() && it->second == o) {
      continue;
    }
    const auto& stored = block_outs[b->id()] = std::move(o);
    for (auto* e : b->succs()) {
      auto* target = e->target();
      auto& entry_join =
          entry_joins.try_emplace(target->id(), target->preds().size())
              .first->second;
      const State* passed = &stored.exit;
      if (e->type() == cfg::EDGE_THROW) {
        passed = stored.at_throw ? &*stored.at_throw : nullptr;
      }
      entry_join.set(slot_of.at(e), passed);
      work.push_back(target);
    }
  }
  const auto* rtype = m->get_proto()->get_rtype();
  for (auto* b : cfg.blocks()) {
    if (!block_outs.contains(b->id())) {
      continue;
    }
    run_block(b, [&](IRInstruction* insn, const State& st) {
      auto report = [&](const std::string& what) {
        *out << show(m) << ": " << show(insn) << ": " << what << "\n";
      };
      if (insn->opcode() == OPCODE_IF_EQ || insn->opcode() == OPCODE_IF_NE) {
        const Kinds a = value_in(st, insn->src(0)).kinds;
        const Kinds c = value_in(st, insn->src(1)).kinds;
        for (uint8_t x = 0; x < kNumKinds; ++x) {
          for (uint8_t y = 0; y < kNumKinds; ++y) {
            if ((a & bit(x)) != 0 && (c & bit(y)) != 0 && !comparable(x, y)) {
              report("compares " + show_kinds(a) + " with " + show_kinds(c));
              return;
            }
          }
        }
        return;
      }
      for (const auto& u : uses_of(m, insn, st)) {
        if (u.malformed) {
          report(u.what);
          continue;
        }
        const Kinds kinds = value_in(st, u.reg).kinds;
        Kinds rejected = 0;
        for (uint8_t k = 0; k < kNumKinds; ++k) {
          if ((kinds & bit(k)) != 0 && !assignable(u.need, k) &&
              (!u.copy || k != kConflict) &&
              (insn->opcode() != OPCODE_RETURN || !return_accepts(rtype, k))) {
            rejected |= bit(k);
          }
        }
        if (rejected == bit(kUninitialized)) {
          const bool into_split = opcode::is_a_method_invoke(insn->opcode()) &&
                                  checked.contains(insn->get_method());
          report(u.what + " may be an uninitialized object" +
                 (into_split ? ", which crosses the boundary of the split " +
                                   show(insn->get_method())
                             : ""));
        } else if (rejected != 0) {
          report(u.what + " may be " + show_kinds(kinds) + ", needs " +
                 std::string(show_need(u.need)));
        }
      }
    });
  }
}

// Whether ART accepts a value of type `value` where `declared` is declared.
inline bool accepts(const DexType* declared, const DexType* value) {
  const auto need = needs_of(declared).front();
  const Kinds kinds = of_type(value).first.kinds;
  for (uint8_t k = 0; k < kNumKinds; ++k) {
    if ((kinds & bit(k)) != 0 && !assignable(need, k)) {
      return false;
    }
  }
  return true;
}

} // namespace art_types

// Describes each use in `methods` that ART would reject; empty if none.
inline std::string describeArtTypeViolations(
    const std::vector<DexMethod*>& methods) {
  const std::set<const DexMethodRef*, dexmethods_comparator> checked(
      methods.begin(), methods.end());
  std::ostringstream out;
  for (auto* m : methods) {
    if (m->get_code() != nullptr) {
      art_types::check_method(m, checked, &out);
    }
  }
  return out.str();
}

// For a test harness: the violations in what a transformation emitted, judged
// only if the model accepted everything it was given. A transformation must
// keep valid code valid; it owes nothing to input that is already invalid, and
// such input can reach its output unchanged. Some tests feed deliberately
// invalid input, and the model, which judges every order in which ART may
// visit the paths, can also reject input that ART accepts in the order the
// layout gives.
class ArtTypeCheckOfOutput {
 public:
  explicit ArtTypeCheckOfOutput(const std::vector<DexMethod*>& input)
      : m_judged(describeArtTypeViolations(input).empty()) {}

  std::string violations(const std::vector<DexMethod*>& output) const {
    return m_judged ? describeArtTypeViolations(output) : std::string();
  }

 private:
  bool m_judged;
};

} // namespace method_splitting_test
