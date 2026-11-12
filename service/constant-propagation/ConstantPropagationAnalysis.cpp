/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ConstantPropagationAnalysis.h"

#include <boost/container_hash/hash.hpp>
#include <cinttypes>
#include <cstring>
#include <limits>
#include <type_traits>

#include "ControlFlow.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "RedexContext.h"

#include <bit>

// Note: MSVC STL doesn't implement std::isnan(Integral arg). We need to provide
// an override of fpclassify for integral types.
#ifdef _MSC_VER
#include <type_traits>
template <typename T>
std::enable_if_t<std::is_integral<T>::value, int> fpclassify(T x) {
  return x == 0 ? FP_ZERO : FP_NORMAL;
}
#endif

#include "DexAccess.h"
#include "DexAnnotation.h"
#include "DexInstruction.h"
#include "Resolver.h"
#include "Trace.h"
#include "Walkers.h"

// Signed integer overflow is undefined behavior in C++20, but the two's
// complement wrapping matches the required Java semantics. So silence ubsan.
#if defined(__clang__)
#define NO_UBSAN_ARITH __attribute__((no_sanitize("signed-integer-overflow")))
#else
#define NO_UBSAN_ARITH
#endif

namespace {

/*
 * Helpers for basic block analysis
 */

// reinterpret the long's bits as a double
template <typename Out, typename In>
static Out reinterpret_bits(In in) {
  static_assert(sizeof(Out) == sizeof(In), "Size mismatch");
  static_assert(std::is_trivially_copyable_v<In> &&
                    std::is_trivially_copyable_v<Out>,
                "Not trivially copyable, can't safely memcpy");

  if constexpr (std::is_same_v<In, Out>) {
    return in;
  }
  Out res;
  std::memcpy(&res, &in, sizeof(In));
  return res;
}

bool is_compare_floating(IROpcode op) {
  return op == OPCODE_CMPG_DOUBLE || op == OPCODE_CMPL_DOUBLE ||
         op == OPCODE_CMPG_FLOAT || op == OPCODE_CMPL_FLOAT;
}

bool is_less_than_bias(IROpcode op) {
  return op == OPCODE_CMPL_DOUBLE || op == OPCODE_CMPL_FLOAT;
}

// Propagate the result of a compare if the operands are known constants.
// If we know enough, put -1, 0, or 1 into the destination register.
//
// Stored is how the data is stored in the register (the size).
//   Should be int32_t or int64_t
// Operand is how the data is used.
//   Should be float, double, or int64_t
template <typename Operand, typename Stored>
void analyze_compare(const IRInstruction* insn, ConstantEnvironment* env) {
  static_assert(std::is_same_v<Stored, int32_t> ||
                std::is_same_v<Stored, int64_t>);
  static_assert(std::is_floating_point_v<Operand> ||
                std::is_same_v<Operand, int64_t>);
  static_assert(sizeof(Operand) == sizeof(Stored),
                "Operand and Stored must have the same size.");

  IROpcode op = insn->opcode();
  auto scd_left = env->get<SignedConstantDomain>(insn->src(0));
  const auto scd_right = env->get<SignedConstantDomain>(insn->src(1));
  const auto left = scd_left.get_constant();
  const auto right = scd_right.get_constant();

  if (left && right) {
    int32_t result;
    auto l_val = reinterpret_bits<Operand, Stored>(*left);
    auto r_val = reinterpret_bits<Operand, Stored>(*right);
    if (is_compare_floating(op) && (std::isnan(l_val) || std::isnan(r_val))) {
      if (is_less_than_bias(op)) {
        result = -1;
      } else {
        result = 1;
      }
    } else if (l_val > r_val) {
      result = 1;
    } else if (l_val == r_val) {
      result = 0;
    } else { // l_val < r_val
      result = -1;
    }
    TRACE(CONSTP, 5,
          "Propagated constant in branch instruction %s, "
          "Operands [%d] [%d] -> Result: [%d]",
          SHOW(insn), (int)l_val, (int)r_val, result);
    env->set(insn->dest(), SignedConstantDomain(result));
    return;
  }

  if (op == OPCODE_CMP_LONG) {
    scd_left.meet_with(scd_right);
    if (scd_left.is_bottom()) {
      // No overlap, such as bitset or nez/zero mismatch.
      env->set(insn->dest(), SignedConstantDomain::nez());
      return;
    }
  }

  env->set(insn->dest(), SignedConstantDomain::top());
}

// https://cs.android.com/android/platform/superproject/main/+/main:art/runtime/entrypoints/entrypoint_utils-inl.h;l=702;drc=d5137445c0d4067406cb3e38aade5507ff2fcd16
template <typename INT_TYPE, typename FLOAT_TYPE>
inline INT_TYPE art_float_to_integral(FLOAT_TYPE f) {
  static_assert(std::is_integral_v<INT_TYPE>, "INT_TYPE must be integral");
  static_assert(std::is_floating_point_v<FLOAT_TYPE>,
                "FLOAT_TYPE must be floating-point");

  const INT_TYPE kMaxInt =
      static_cast<INT_TYPE>(std::numeric_limits<INT_TYPE>::max());
  const INT_TYPE kMinInt =
      static_cast<INT_TYPE>(std::numeric_limits<INT_TYPE>::min());
  const FLOAT_TYPE kMaxIntAsFloat = static_cast<FLOAT_TYPE>(kMaxInt);
  const FLOAT_TYPE kMinIntAsFloat = static_cast<FLOAT_TYPE>(kMinInt);
  if (f > kMinIntAsFloat) {
    if (f < kMaxIntAsFloat) {
      return static_cast<INT_TYPE>(f);
    } else {
      return kMaxInt;
    }
  } else {
    return (f != f) ? 0 : kMinInt; // f != f implies NaN
  }
}

} // namespace

namespace constant_propagation {

std::optional<size_t> get_null_check_object_index(
    const IRInstruction* insn, const NullCheckMethods& null_check_methods) {
  switch (insn->opcode()) {
  case OPCODE_INVOKE_STATIC: {
    auto* method = insn->get_method();
    if (null_check_methods.kotlin_null_check_assertions().count(method) != 0u) {
      // Note: We are not assuming here that the first argument is the checked
      // argument of type object, as it might not be. For example,
      // RemoveUnusedArgs may have removed or otherwise reordered the arguments.
      // TODO: Don't mattern match at all, but make this a deep semantic
      // analysis, as even this remaining pattern matching is brittle once we
      // might start doing argument type weakening / strengthening
      // optimizations.
      auto& args = *method->get_proto()->get_args();
      for (size_t i = 0; i < args.size(); i++) {
        if (args.at(i) == type::java_lang_Object()) {
          return i;
        }
      }
    }
    break;
  }
  default:
    break;
  }
  return std::nullopt;
}

std::optional<size_t> get_dereferenced_object_src_index(
    const IRInstruction* insn) {
  switch (insn->opcode()) {
  case OPCODE_MONITOR_ENTER:
  case OPCODE_MONITOR_EXIT:
  case OPCODE_AGET:
  case OPCODE_AGET_BYTE:
  case OPCODE_AGET_CHAR:
  case OPCODE_AGET_WIDE:
  case OPCODE_AGET_SHORT:
  case OPCODE_AGET_OBJECT:
  case OPCODE_AGET_BOOLEAN:
  case OPCODE_IGET:
  case OPCODE_IGET_BYTE:
  case OPCODE_IGET_CHAR:
  case OPCODE_IGET_WIDE:
  case OPCODE_IGET_SHORT:
  case OPCODE_IGET_OBJECT:
  case OPCODE_IGET_BOOLEAN:
  case OPCODE_ARRAY_LENGTH:
  case OPCODE_FILL_ARRAY_DATA:
  case OPCODE_INVOKE_SUPER:
  case OPCODE_INVOKE_INTERFACE:
  case OPCODE_INVOKE_VIRTUAL:
  case OPCODE_INVOKE_DIRECT:
    return 0;
  case OPCODE_APUT:
  case OPCODE_APUT_BYTE:
  case OPCODE_APUT_CHAR:
  case OPCODE_APUT_WIDE:
  case OPCODE_APUT_SHORT:
  case OPCODE_APUT_OBJECT:
  case OPCODE_APUT_BOOLEAN:
  case OPCODE_IPUT:
  case OPCODE_IPUT_BYTE:
  case OPCODE_IPUT_CHAR:
  case OPCODE_IPUT_WIDE:
  case OPCODE_IPUT_SHORT:
  case OPCODE_IPUT_OBJECT:
  case OPCODE_IPUT_BOOLEAN:
    return 1;
  default:
    return std::nullopt;
  }
}

static void set_escaped(reg_t reg, ConstantEnvironment* env) {
  if (auto ptr_opt = env->get(reg).maybe_get<AbstractHeapPointer>()) {
    if (auto ptr_value = ptr_opt->get_constant()) {
      env->mutate_heap(
          [&](ConstantHeap* heap) { heap->set(*ptr_value, HeapValue::top()); });
    }
  }
}

bool HeapEscapeAnalyzer::analyze_aput(const IRInstruction* insn,
                                      ConstantEnvironment* env) {
  if (insn->opcode() == OPCODE_APUT_OBJECT) {
    set_escaped(insn->src(0), env);
  }
  return true;
}

bool HeapEscapeAnalyzer::analyze_sput(const IRInstruction* insn,
                                      ConstantEnvironment* env) {
  if (insn->opcode() == OPCODE_SPUT_OBJECT) {
    set_escaped(insn->src(0), env);
  }
  return true;
}

bool HeapEscapeAnalyzer::analyze_iput(const IRInstruction* insn,
                                      ConstantEnvironment* env) {
  if (insn->opcode() == OPCODE_IPUT_OBJECT) {
    set_escaped(insn->src(0), env);
  }
  return true;
}

bool HeapEscapeAnalyzer::analyze_invoke(const IRInstruction* insn,
                                        ConstantEnvironment* env) {
  for (size_t i = 0; i < insn->srcs_size(); ++i) {
    set_escaped(insn->src(i), env);
  }
  // Practical use cases of this analyzer is followed by PrimitiveAnalyzer which
  // will handle setting result register. Return false to let it run.
  return false;
}

bool HeapEscapeAnalyzer::analyze_filled_new_array(const IRInstruction* insn,
                                                  ConstantEnvironment* env) {
  for (size_t i = 0; i < insn->srcs_size(); ++i) {
    set_escaped(insn->src(i), env);
  }
  // Practical use cases of this analyzer is followed by PrimitiveAnalyzer which
  // will handle setting result register. Return false to let it run.
  return false;
}

bool LocalArrayAnalyzer::analyze_new_array(const IRInstruction* insn,
                                           ConstantEnvironment* env) {
  auto length = env->get<SignedConstantDomain>(insn->src(0));
  auto length_value_opt = length.get_constant();
  if (!length_value_opt) {
    return false;
  }
  env->new_heap_value(RESULT_REGISTER, insn,
                      ConstantValueArrayDomain(*length_value_opt));
  return true;
}

bool LocalArrayAnalyzer::analyze_aget(const IRInstruction* insn,
                                      ConstantEnvironment* env) {
  if (insn->opcode() == OPCODE_AGET_OBJECT) {
    return false;
  }
  auto idx_opt = env->get<SignedConstantDomain>(insn->src(1)).get_constant();
  if (!idx_opt) {
    return false;
  }
  auto heap_ptr = env->get(insn->src(0)).maybe_get<AbstractHeapPointer>();
  if (!heap_ptr) {
    return false;
  }
  auto arr = env->get_pointee<ConstantValueArrayDomain>(insn->src(0));
  env->set(RESULT_REGISTER, arr.get(*idx_opt));
  return true;
}

bool LocalArrayAnalyzer::analyze_aput(const IRInstruction* insn,
                                      ConstantEnvironment* env) {
  if (insn->opcode() == OPCODE_APUT_OBJECT) {
    return false;
  }
  auto subscript = env->get(insn->src(2)).maybe_get<SignedConstantDomain>();
  if (!subscript || subscript->is_top() || subscript->is_bottom()) {
    set_escaped(insn->src(1), env);
    return false;
  }
  auto val = env->get(insn->src(0));
  // Check if insn->src(1) is actually known as an array
  auto heap_ptr = env->get(insn->src(1)).maybe_get<AbstractHeapPointer>();
  if (!heap_ptr) {
    return false;
  }
  env->set_array_binding(insn->src(1), *subscript->get_constant(), val);
  return true;
}

namespace {
template <typename IntType>
void populate_array_bindings_for_payload(reg_t array_reg,
                                         const std::vector<IntType>& elements,
                                         ConstantEnvironment* env) {
  static_assert(
      std::is_integral<IntType>::value,
      "fill-array-data-payload only implemented for integral values.");
  for (size_t i = 0; i < elements.size(); i++) {
    auto constant = elements[i];
    env->set_array_binding(array_reg, i, SignedConstantDomain(constant));
  }
}
} // namespace

bool LocalArrayAnalyzer::analyze_fill_array_data(const IRInstruction* insn,
                                                 ConstantEnvironment* env) {
  // Unpacks the fill-array-data-payload and call env->set_array_binding()
  // N times with the appropriate SignedConstantDomain. The bytecode format says
  // the size of the array is allowed to be larger than the payload of items;
  // under such a contition the elements beyond what are contained in
  // fill-array-data-payload should be unmodified.
  // If an too small array is encountered, mark it as escaped to avoid making
  // any assumptions.
  auto reg = insn->src(0);
  auto* op_data = insn->get_data();
  auto heap_ptr = env->get(reg).maybe_get<AbstractHeapPointer>();
  if (heap_ptr) {
    auto array_domain = env->get_pointee<ConstantValueArrayDomain>(*heap_ptr);
    if (array_domain.is_value()) {
      auto len = array_domain.length();
      auto ewidth = fill_array_data_payload_width(op_data);
      auto element_count = fill_array_data_payload_element_count(op_data);
      if (len >= element_count) {
        if (ewidth == 1) {
          auto elements = get_fill_array_data_payload<int8_t>(op_data);
          populate_array_bindings_for_payload(reg, elements, env);
        } else if (ewidth == 2) {
          auto elements = get_fill_array_data_payload<int16_t>(op_data);
          populate_array_bindings_for_payload(reg, elements, env);
        } else if (ewidth == 4) {
          auto elements = get_fill_array_data_payload<int32_t>(op_data);
          populate_array_bindings_for_payload(reg, elements, env);
        } else {
          always_assert_log(ewidth == 8, "Invalid element width: %d", ewidth);
          auto elements = get_fill_array_data_payload<int64_t>(op_data);
          populate_array_bindings_for_payload(reg, elements, env);
        }
        return true;
      } else {
        TRACE(
            CONSTP, 3,
            "Array length does not match size of fill-array-data-payload @ %s\n"
            "  => marking as escaped",
            SHOW(insn));
      }
    }
  }
  // Fallthrough behavior is as before; mark the array it modifies as unknown.
  set_escaped(reg, env);
  return false;
}

namespace {

template <typename T>
bool try_constant_type(ConstantEnvironment* env,
                       const ConstantValue& val,
                       size_t idx) {
  auto t_val = val.maybe_get<T>();
  if (!t_val) {
    return false;
  }
  if (t_val->is_top() || t_val->is_bottom()) {
    env->set_array_binding(RESULT_REGISTER, idx, SignedConstantDomain());
    return true;
  }

  env->set_array_binding(RESULT_REGISTER, idx, val);
  return true;
}

template <typename... T>
bool try_constant_types(ConstantEnvironment* env,
                        const ConstantValue& val,
                        size_t idx) {
  return (try_constant_type<T>(env, val, idx) || ...);
}

} // namespace

bool LocalArrayAnalyzer::analyze_filled_new_array(const IRInstruction* insn,
                                                  ConstantEnvironment* env) {
  auto array_size = insn->srcs_size();
  const DexType* element_type =
      type::make_array_component_type(insn->get_type());
  if (type::is_integral(element_type)) {
    env->new_heap_value(RESULT_REGISTER, insn,
                        ConstantValueArrayDomain(array_size));
    for (src_index_t i = 0; i < array_size; i++) {
      if (!try_constant_types<SignedConstantDomain, ConstantInjectionIdDomain,
                              ConstantResourceIdDomain>(
              env, env->get(insn->src(i)), i)) {
        env->set_array_binding(RESULT_REGISTER, i, SignedConstantDomain());
      }
    }
    return true;
  } else {
    // Subsequent analyzers should mark all srcs as escaped.
    return false;
  }
}

bool ResourceIdAnalyzer::is_src_known(const IRInstruction* insn,
                                      ConstantEnvironment* env,
                                      src_index_t i) {
  const auto& register_env = env->get_register_environment();
  const auto& value = register_env.get(insn->src(i));
  auto r_domain = value.maybe_get<ConstantResourceIdDomain>();
  return r_domain != std::nullopt && r_domain->is_value();
}

bool ResourceIdAnalyzer::analyze_r_const(const IRInstruction* insn,
                                         ConstantEnvironment* env) {
  auto id = static_cast<uint32_t>(insn->get_literal());
  TRACE(CONSTP, 5, "Discovered new resource id for reg: %u value: %u",
        insn->dest(), id);
  env->set(insn->dest(), ConstantResourceIdDomain({.id = id}));
  return true;
}

bool ResourceIdAnalyzer::analyze_cmp(const IRInstruction* insn,
                                     ConstantEnvironment* env) {
  if (ResourceIdAnalyzer::is_src_known(insn, env, 0) ||
      ResourceIdAnalyzer::is_src_known(insn, env, 1)) {
    env->set(insn->dest(), ConstantValue::top());
    return true;
  }
  return false;
}

bool ResourceIdAnalyzer::analyze_binop(const IRInstruction* insn,
                                       ConstantEnvironment* env) {
  if (ResourceIdAnalyzer::is_src_known(insn, env, 0) ||
      ResourceIdAnalyzer::is_src_known(insn, env, 1)) {
    env->set(insn->dest(), ConstantValue::top());
    return true;
  }
  return false;
}

bool ResourceIdAnalyzer::analyze_unop(const IRInstruction* insn,
                                      ConstantEnvironment* env) {
  if (ResourceIdAnalyzer::is_src_known(insn, env, 0)) {
    env->set(insn->dest(), ConstantValue::top());
    return true;
  }
  return false;
}

bool ResourceIdAnalyzer::analyze_binop_lit(const IRInstruction* insn,
                                           ConstantEnvironment* env) {
  if (ResourceIdAnalyzer::is_src_known(insn, env, 0)) {
    env->set(insn->dest(), ConstantValue::top());
    return true;
  }
  return false;
}

bool PrimitiveAnalyzer::analyze_default(const IRInstruction* insn,
                                        ConstantEnvironment* env) {
  if (opcode::is_a_load_param(insn->opcode())) {
    return true;
  }
  switch (insn->opcode()) {
  case OPCODE_NEW_ARRAY:
  case OPCODE_FILLED_NEW_ARRAY:
  case OPCODE_NEW_INSTANCE:
  case OPCODE_CONST_STRING:
  case OPCODE_CONST_CLASS: {
    env->set(RESULT_REGISTER, SignedConstantDomain(sign_domain::Interval::NEZ));
    return true;
  }
  case OPCODE_MOVE_EXCEPTION: {
    env->set(insn->dest(), SignedConstantDomain(sign_domain::Interval::NEZ));
    return true;
  }
  case OPCODE_ARRAY_LENGTH: {
    env->set(RESULT_REGISTER, SignedConstantDomain(sign_domain::Interval::GEZ));
    return true;
  }
  default:
    break;
  }
  if (insn->has_dest()) {
    TRACE(CONSTP, 5, "Marking value unknown [Reg: %u] %s", insn->dest(),
          SHOW(insn));
    env->set(insn->dest(), ConstantValue::top());
  } else if (insn->has_move_result_any()) {
    TRACE(CONSTP, 5, "Clearing result register %s", SHOW(insn));
    env->set(RESULT_REGISTER, ConstantValue::top());
  }
  return true;
}

bool PrimitiveAnalyzer::analyze_const(const IRInstruction* insn,
                                      ConstantEnvironment* env) {
  TRACE(CONSTP, 5, "Discovered new constant for reg: %u value: %" PRId64,
        insn->dest(), insn->get_literal());
  env->set(insn->dest(), SignedConstantDomain(insn->get_literal()));
  return true;
}

// TODO(T279417132): Remove this once the behavior is fully rolled out.
bool enable_check_cast_value_preservation = false;

bool PrimitiveAnalyzer::analyze_check_cast(const IRInstruction* insn,
                                           ConstantEnvironment* env) {
  auto src = env->get(insn->src(0));
  if (!enable_check_cast_value_preservation) {
    // Carry a null operand through as null; leave everything else unknown.
    if (src.is_zero()) {
      env->set(RESULT_REGISTER, SignedConstantDomain(0));
      return true;
    }
    return analyze_default(insn, env);
  }
  // A successful check-cast returns its operand unchanged, so the result holds
  // the operand's value.
  env->set(RESULT_REGISTER, src);
  return true;
}

bool PrimitiveAnalyzer::analyze_instance_of(const IRInstruction* insn,
                                            ConstantEnvironment* env) {
  auto src = env->get(insn->src(0));
  if (src.is_zero()) {
    env->set(RESULT_REGISTER, SignedConstantDomain(0));
    return true;
  }
  if (const DexType* src_type = get_object_constant_type(src)) {
    if (auto res = type::evaluate_type_check(src_type, insn->get_type())) {
      env->set(RESULT_REGISTER, SignedConstantDomain(*res));
      return true;
    }
  }
  return analyze_default(insn, env);
}

bool PrimitiveAnalyzer::analyze_move(const IRInstruction* insn,
                                     ConstantEnvironment* env) {
  env->set(insn->dest(), env->get(insn->src(0)));
  return true;
}

bool PrimitiveAnalyzer::analyze_move_result(const IRInstruction* insn,
                                            ConstantEnvironment* env) {
  env->set(insn->dest(), env->get(RESULT_REGISTER));
  return true;
}

bool PrimitiveAnalyzer::analyze_cmp(const IRInstruction* insn,
                                    ConstantEnvironment* env) {
  auto op = insn->opcode();
  switch (op) {
  case OPCODE_CMPL_FLOAT:
  case OPCODE_CMPG_FLOAT: {
    analyze_compare<float, int32_t>(insn, env);
    break;
  }

  case OPCODE_CMPL_DOUBLE:
  case OPCODE_CMPG_DOUBLE: {
    analyze_compare<double, int64_t>(insn, env);
    break;
  }

  case OPCODE_CMP_LONG: {
    analyze_compare<int64_t, int64_t>(insn, env);
    break;
  }
  default: {
    not_reached_log("Unexpected opcode: %s\n", SHOW(op));
  }
  }
  return true;
}

bool PrimitiveAnalyzer::analyze_unop(const IRInstruction* insn,
                                     ConstantEnvironment* env) NO_UBSAN_ARITH {
  auto op = insn->opcode();

  auto apply = [&](auto val) {
    SignedConstantDomain result;
    if constexpr (sizeof(val) == 4) {
      result = SignedConstantDomain(
          (int32_t)((std::bit_cast<int32_t>(val)) & 0xFFFFFFFF));
    } else if constexpr (sizeof(val) == 8) {
      result = SignedConstantDomain(std::bit_cast<int64_t>(val));
    } else {
      // floating point number is either 32 bit or 64 bit
      // so we must have intergral value here
      result = SignedConstantDomain(val);
    }
    env->set(insn->dest(), result);
    return true;
  };

  auto scd = env->get<SignedConstantDomain>(insn->src(0));
  const auto cst = scd.get_constant();

  if (cst) {
    TRACE(CONSTP, 5, "Attempting to fold %s", SHOW(insn));
    int64_t val = *cst;
    switch (op) {
    case OPCODE_NOT_INT:
      return apply(~((int32_t)val));
    case OPCODE_NOT_LONG:
      return apply(~val);
    case OPCODE_NEG_INT:
      return apply(-((int32_t)val));
    case OPCODE_NEG_LONG:
      return apply(-val);
    case OPCODE_NEG_FLOAT:
      return apply(-std::bit_cast<float>((int32_t)val));
    case OPCODE_NEG_DOUBLE:
      return apply(-std::bit_cast<double>(val));
    case OPCODE_LONG_TO_INT:
      return apply((int32_t)val);
    case OPCODE_INT_TO_LONG:
      return apply(val);
    case OPCODE_INT_TO_BYTE:
      return apply((int8_t)val);
    case OPCODE_INT_TO_CHAR:
      return apply((uint16_t)val);
    case OPCODE_INT_TO_SHORT:
      return apply((int16_t)val);
    case OPCODE_INT_TO_FLOAT:
      return apply((float)(val));
    case OPCODE_DOUBLE_TO_FLOAT:
      return apply((float)(std::bit_cast<double>(val)));
    case OPCODE_LONG_TO_FLOAT:
      return apply((float)val);
    case OPCODE_INT_TO_DOUBLE:
      return apply((double)((int32_t)val));
    case OPCODE_LONG_TO_DOUBLE:
      return apply((double)val);
    case OPCODE_FLOAT_TO_DOUBLE:
      return apply((double)(std::bit_cast<float>((int32_t)val)));
    case OPCODE_FLOAT_TO_INT:
      return apply(art_float_to_integral<int32_t, float>(
          std::bit_cast<float>((int32_t)val)));
    case OPCODE_DOUBLE_TO_INT:
      return apply(
          art_float_to_integral<int32_t, double>(std::bit_cast<double>(val)));
    case OPCODE_FLOAT_TO_LONG:
      return apply(art_float_to_integral<int64_t, float>(
          std::bit_cast<float>((int32_t)val)));
    case OPCODE_DOUBLE_TO_LONG:
      return apply(
          art_float_to_integral<int64_t, double>(std::bit_cast<double>(val)));
    default:
      break;
    }
  }

  if (op == OPCODE_NOT_INT || op == OPCODE_NOT_LONG) {
    uint64_t new_determined_zeros = scd.get_determined_one_bits();
    uint64_t new_determined_ones = scd.get_determined_zero_bits();
    if (op == OPCODE_NOT_INT) {
      new_determined_zeros |=
          ~static_cast<uint64_t>(std::numeric_limits<uint32_t>::max());
      new_determined_ones &= std::numeric_limits<uint32_t>::max();
    }
    scd.set_determined_bits_erasing_bounds(
        new_determined_zeros, new_determined_ones, op == OPCODE_NOT_INT);
    env->set(insn->dest(), scd);
    return true;
  }

  return analyze_default(insn, env);
}

bool PrimitiveAnalyzer::analyze_binop_lit(
    const IRInstruction* insn, ConstantEnvironment* env) NO_UBSAN_ARITH {
  auto op = insn->opcode();
  int32_t lit = static_cast<int32_t>(insn->get_literal());
  auto scd = env->get<SignedConstantDomain>(insn->src(0));
  const auto cst = scd.get_constant();
  std::optional<int64_t> result = std::nullopt;
  if (cst) {
    TRACE(CONSTP, 5, "Attempting to fold %s with literal %d", SHOW(insn), lit);
    bool use_result_reg = false;
    switch (op) {
    case OPCODE_ADD_INT_LIT: {
      // add-int/lit is the most common arithmetic instruction: about .29% of
      // all instructions. All other arithmetic instructions are less than
      // .05%
      result = (*cst) + lit;
      break;
    }
    case OPCODE_RSUB_INT_LIT: {
      result = lit - (*cst);
      break;
    }
    case OPCODE_MUL_INT_LIT: {
      result = (*cst) * lit;
      break;
    }
    case OPCODE_DIV_INT_LIT: {
      if (lit != 0) {
        result = (*cst) / lit;
      }
      use_result_reg = true;
      break;
    }
    case OPCODE_REM_INT_LIT: {
      if (lit != 0) {
        result = (*cst) % lit;
      }
      use_result_reg = true;
      break;
    }
    case OPCODE_AND_INT_LIT: {
      result = (*cst) & lit;
      break;
    }
    case OPCODE_OR_INT_LIT: {
      result = (*cst) | lit;
      break;
    }
    case OPCODE_XOR_INT_LIT: {
      result = (*cst) ^ lit;
      break;
    }
    // as in https://source.android.com/devices/tech/dalvik/dalvik-bytecode
    // the following operations have the second operand masked.
    case OPCODE_SHL_INT_LIT: {
      uint32_t ucst = static_cast<uint32_t>(*cst);
      uint32_t uresult = ucst << (lit & 0x1f);
      result = static_cast<int32_t>(uresult);
      break;
    }
    case OPCODE_SHR_INT_LIT: {
      result = (*cst) >> (lit & 0x1f);
      break;
    }
    case OPCODE_USHR_INT_LIT: {
      uint32_t ucst = static_cast<uint32_t>(*cst);
      // defined in dalvik spec
      result = ucst >> (lit & 0x1f);
      break;
    }
    default:
      break;
    }
    auto res_const_dom = SignedConstantDomain::top();
    if (result != std::nullopt) {
      int32_t result32 = (int32_t)(*result & 0xFFFFFFFF);
      res_const_dom = SignedConstantDomain(result32);
    }
    env->set(use_result_reg ? RESULT_REGISTER : insn->dest(), res_const_dom);
    return true;
  }

  if (op == OPCODE_AND_INT_LIT || op == OPCODE_OR_INT_LIT ||
      op == OPCODE_XOR_INT_LIT || op == OPCODE_USHR_INT_LIT ||
      op == OPCODE_SHR_INT_LIT || op == OPCODE_SHL_INT_LIT) {
    TRACE(CONSTP, 5, "Attempting to set bits in %s with literal %d", SHOW(insn),
          lit);
    switch (op) {
    case OPCODE_AND_INT_LIT: {
      scd.set_determined_bits_erasing_bounds(scd.get_determined_zero_bits() |
                                                 ~static_cast<uint64_t>(lit),
                                             std::nullopt, /*bit32=*/true);
      break;
    }
    case OPCODE_OR_INT_LIT: {
      scd.set_determined_bits_erasing_bounds(std::nullopt,
                                             scd.get_determined_one_bits() |
                                                 static_cast<uint64_t>(lit),
                                             /*bit32=*/true);
      break;
    }
    case OPCODE_XOR_INT_LIT: {
      const auto determined_zeros = scd.get_determined_zero_bits();
      const auto determined_ones = scd.get_determined_one_bits();
      const auto new_determined_zeros =
          determined_ones & static_cast<uint64_t>(lit);
      const auto new_determined_ones =
          determined_zeros & static_cast<uint64_t>(lit);
      scd.set_determined_bits_erasing_bounds(
          (determined_zeros | new_determined_zeros) & ~new_determined_ones,
          (determined_ones | new_determined_ones) & ~new_determined_zeros,
          /*bit32=*/true);
      break;
    }
    case OPCODE_SHL_INT_LIT: {
      scd.left_shift_bits_int(lit);
      break;
    }
    case OPCODE_USHR_INT_LIT: {
      scd.unsigned_right_shift_bits_int(lit);
      break;
    }
    case OPCODE_SHR_INT_LIT: {
      scd.signed_right_shift_bits_int(lit);
      break;
    }
    default:
      not_reached();
    }

    env->set(insn->dest(), scd);
    return true;
  }
  return analyze_default(insn, env);
}

bool PrimitiveAnalyzer::analyze_binop(const IRInstruction* insn,
                                      ConstantEnvironment* env) NO_UBSAN_ARITH {
  auto op = insn->opcode();
  const auto scd_left = env->get<SignedConstantDomain>(insn->src(0));
  const auto cst_left = scd_left.get_constant();
  const auto scd_right = env->get<SignedConstantDomain>(insn->src(1));
  const auto cst_right = scd_right.get_constant();
  std::optional<int64_t> result = std::nullopt;
  if (cst_left && cst_right) {
    TRACE(CONSTP, 5, "Attempting to fold %s", SHOW(insn));
    bool use_result_reg = false;
    switch (op) {
    case OPCODE_ADD_INT:
    case OPCODE_ADD_LONG: {
      result = (*cst_left) + (*cst_right);
      break;
    }
    case OPCODE_SUB_INT:
    case OPCODE_SUB_LONG: {
      result = (*cst_left) - (*cst_right);
      break;
    }
    case OPCODE_MUL_INT:
    case OPCODE_MUL_LONG: {
      result = (*cst_left) * (*cst_right);
      break;
    }
    case OPCODE_DIV_INT:
    case OPCODE_DIV_LONG: {
      if ((*cst_right) != 0) {
        result = (*cst_left) / (*cst_right);
      }
      use_result_reg = true;
      break;
    }
    case OPCODE_REM_INT:
    case OPCODE_REM_LONG: {
      if ((*cst_right) != 0) {
        result = (*cst_left) % (*cst_right);
      }
      use_result_reg = true;
      break;
    }
    case OPCODE_AND_INT:
    case OPCODE_AND_LONG: {
      result = (*cst_left) & (*cst_right);
      break;
    }
    case OPCODE_OR_INT:
    case OPCODE_OR_LONG: {
      result = (*cst_left) | (*cst_right);
      break;
    }
    case OPCODE_XOR_INT:
    case OPCODE_XOR_LONG: {
      result = (*cst_left) ^ (*cst_right);
      break;
    }
    default:
      return analyze_default(insn, env);
    }
    auto res_const_dom = SignedConstantDomain::top();
    if (result != std::nullopt) {
      if (opcode::is_binop64(op)) {
        res_const_dom = SignedConstantDomain(*result);
      } else {
        int32_t result32 = (int32_t)(*result & 0xFFFFFFFF);
        res_const_dom = SignedConstantDomain(result32);
      }
    }
    env->set(use_result_reg ? RESULT_REGISTER : insn->dest(), res_const_dom);
    return true;
  }

  switch (op) {
  case OPCODE_AND_INT:
  case OPCODE_AND_LONG: {
    SignedConstantDomain dest_scd;
    dest_scd.set_determined_bits_erasing_bounds(
        scd_left.get_determined_zero_bits() |
            scd_right.get_determined_zero_bits(),
        scd_left.get_determined_one_bits() &
            scd_right.get_determined_one_bits(),
        /*bit32=*/op == OPCODE_AND_INT);
    env->set(insn->dest(), dest_scd);
    return true;
  }
  case OPCODE_OR_INT:
  case OPCODE_OR_LONG: {
    SignedConstantDomain dest_scd;
    dest_scd.set_determined_bits_erasing_bounds(
        scd_left.get_determined_zero_bits() &
            scd_right.get_determined_zero_bits(),
        scd_left.get_determined_one_bits() |
            scd_right.get_determined_one_bits(),
        /*bit32=*/op == OPCODE_OR_INT);
    env->set(insn->dest(), dest_scd);
    return true;
  }
  case OPCODE_XOR_INT:
  case OPCODE_XOR_LONG: {
    SignedConstantDomain dest_scd;
    dest_scd.set_determined_bits_erasing_bounds(
        (scd_left.get_determined_zero_bits() &
         scd_right.get_determined_zero_bits()) |
            (scd_left.get_determined_one_bits() &
             scd_right.get_determined_one_bits()),
        (scd_left.get_determined_zero_bits() &
         scd_right.get_determined_one_bits()) |
            (scd_left.get_determined_one_bits() &
             scd_right.get_determined_zero_bits()),
        /*bit32=*/op == OPCODE_XOR_INT);
    env->set(insn->dest(), dest_scd);
    return true;
  }
  case OPCODE_SHL_INT: {
    if (!cst_right) {
      break;
    }

    SignedConstantDomain dest_scd(scd_left);
    dest_scd.left_shift_bits_int(static_cast<int32_t>(*cst_right));
    env->set(insn->dest(), dest_scd);
    return true;
  }
  case OPCODE_SHL_LONG: {
    if (!cst_right) {
      break;
    }

    SignedConstantDomain dest_scd(scd_left);
    dest_scd.left_shift_bits_long(static_cast<int32_t>(*cst_right));
    env->set(insn->dest(), dest_scd);
    return true;
  }
  case OPCODE_USHR_INT: {
    if (!cst_right) {
      break;
    }

    SignedConstantDomain dest_scd(scd_left);
    dest_scd.unsigned_right_shift_bits_int(static_cast<int32_t>(*cst_right));
    env->set(insn->dest(), dest_scd);
    return true;
  }
  case OPCODE_USHR_LONG: {
    if (!cst_right) {
      break;
    }

    SignedConstantDomain dest_scd(scd_left);
    dest_scd.unsigned_right_shift_bits_long(static_cast<int32_t>(*cst_right));
    env->set(insn->dest(), dest_scd);
    return true;
  }
  case OPCODE_SHR_INT: {
    if (!cst_right) {
      break;
    }

    SignedConstantDomain dest_scd(scd_left);
    dest_scd.signed_right_shift_bits_int(static_cast<int32_t>(*cst_right));
    env->set(insn->dest(), dest_scd);
    return true;
  }
  case OPCODE_SHR_LONG: {
    if (!cst_right) {
      break;
    }

    SignedConstantDomain dest_scd(scd_left);
    dest_scd.signed_right_shift_bits_long(static_cast<int32_t>(*cst_right));
    env->set(insn->dest(), dest_scd);
    return true;
  }
  default:
    break;
  }
  return analyze_default(insn, env);
}

bool InjectionIdAnalyzer::analyze_injection_id(const IRInstruction* insn,
                                               ConstantEnvironment* env) {
  auto id = static_cast<int32_t>(insn->get_literal());
  TRACE(CONSTP, 5, "Discovered new injection id for reg: %u value: %d",
        insn->dest(), id);
  env->set(insn->dest(), ConstantInjectionIdDomain(id));
  return true;
}

UnorderedSet<const DexField*> get_clinit_only_written_fields(
    const Scope& scope) {
  InsertOnlyConcurrentSet<const DexField*> written_outside_clinit;
  walk::parallel::opcodes(scope, [&](DexMethod* method, IRInstruction* insn) {
    if (!opcode::is_an_sput(insn->opcode())) {
      return;
    }
    auto* field = resolve_field(insn->get_field(), FieldSearch::Static);
    if (field != nullptr && (!method::is_clinit(method) ||
                             field->get_class() != method->get_class())) {
      written_outside_clinit.insert(field);
    }
  });
  UnorderedSet<const DexField*> fields;
  for (const auto* cls : scope) {
    for (const auto* field : cls->get_sfields()) {
      if (!is_volatile(field) && field->rstate.can_delete() &&
          !field->is_external() && written_outside_clinit.count(field) == 0) {
        fields.emplace(field);
      }
    }
  }
  return fields;
}

bool ClinitFieldAnalyzer::analyze_sget(const ClinitFieldAnalyzerState& state,
                                       const IRInstruction* insn,
                                       ConstantEnvironment* env) {
  auto* field = resolve_field(insn->get_field());
  if (field == nullptr) {
    return false;
  }
  if (field->get_class() == state.class_under_init) {
    env->set(RESULT_REGISTER, env->get(field));
    return true;
  }
  return false;
}

bool ClinitFieldAnalyzer::analyze_sput(const ClinitFieldAnalyzerState& state,
                                       const IRInstruction* insn,
                                       ConstantEnvironment* env) {
  auto* field = resolve_field(insn->get_field());
  if (field == nullptr) {
    return false;
  }
  if (field->get_class() == state.class_under_init) {
    env->set(field, env->get(insn->src(0)));
    return true;
  }
  return false;
}

bool ClinitFieldAnalyzer::analyze_invoke(const ClinitFieldAnalyzerState& state,
                                         const IRInstruction* insn,
                                         ConstantEnvironment* env) {
  if (state.class_under_init == nullptr) {
    return false;
  }
  if (insn->opcode() == OPCODE_INVOKE_CUSTOM ||
      insn->opcode() == OPCODE_INVOKE_POLYMORPHIC) {
    // The target of a dynamic invoke cannot be resolved here.
    env->clear_field_environment();
    return false;
  }
  // As in StaticFieldReadAnalysis, external and unresolved cross-class
  // calls are assumed not to modify the tracked fields.
  if (state.class_under_init != insn->get_method()->get_class()) {
    auto* callee = resolve_method(insn->get_method(), opcode_to_search(insn));
    if (callee == nullptr || callee->is_external()) {
      return false;
    }
  }
  if (state.clinit_only_fields == nullptr) {
    env->clear_field_environment();
  } else {
    env->mutate_field_environment([&](FieldEnvironment* fields) {
      auto retained = *fields;
      fields->visit([&](const auto& binding) {
        if (state.clinit_only_fields->count(binding.first) == 0) {
          retained.set(binding.first, ConstantValue::top());
        }
      });
      *fields = std::move(retained);
    });
  }
  return false;
}

/*
 * An analyzer for sget for when we have a static final field
 */
bool StaticFinalFieldAnalyzer::analyze_sget(const IRInstruction* insn,
                                            ConstantEnvironment* env) {
  auto opcode = insn->opcode();
  if (opcode != OPCODE_SGET && opcode != OPCODE_SGET_WIDE) {
    return false;
  }

  auto* field = insn->get_field();
  const auto* dex_field = dynamic_cast<const DexField*>(field);
  // Only want to set the environment of the variable has a static value
  // and is certainly final and will not be modified
  if ((field != nullptr) && field->is_def() &&
      (dex_field->get_static_value() != nullptr) && is_final(dex_field)) {
    const auto constant = SignedConstantDomain(
        static_cast<int64_t>(dex_field->get_static_value()->value()));
    env->set(RESULT_REGISTER, constant);
    return true;
  }
  return false;
}

bool InitFieldAnalyzer::analyze_iget(const DexType* class_under_init,
                                     const IRInstruction* insn,
                                     ConstantEnvironment* env) {
  auto* field = resolve_field(insn->get_field());
  if (field == nullptr) {
    return false;
  }
  if (field->get_class() == class_under_init) {
    env->set(RESULT_REGISTER, env->get(field));
    return true;
  }
  return false;
}

bool InitFieldAnalyzer::analyze_iput(const DexType* class_under_init,
                                     const IRInstruction* insn,
                                     ConstantEnvironment* env) {
  auto* field = resolve_field(insn->get_field());
  if (field == nullptr) {
    return false;
  }
  if (field->get_class() == class_under_init) {
    env->set(field, env->get(insn->src(0)));
    return true;
  }
  return false;
}

bool InitFieldAnalyzer::analyze_invoke(const DexType* class_under_init,
                                       const IRInstruction* insn,
                                       ConstantEnvironment* env) {
  // If the class initializer invokes a method on its own class, that
  // method can modify the class' fields. We would have to inspect the
  // method to find out. Here we take the conservative approach of
  // marking all fields as unknown after the invoke.
  auto opcode = insn->opcode();
  if ((opcode == OPCODE_INVOKE_VIRTUAL || opcode == OPCODE_INVOKE_DIRECT) &&
      class_under_init == insn->get_method()->get_class()) {
    env->clear_field_environment();
  }
  return false;
}

bool EnumFieldAnalyzer::analyze_sget(const EnumFieldAnalyzerState&,
                                     const IRInstruction* insn,
                                     ConstantEnvironment* env) {
  if (insn->opcode() != OPCODE_SGET_OBJECT) {
    return false;
  }
  auto* field = resolve_field(insn->get_field());
  if (field == nullptr) {
    return false;
  }
  if (!is_enum(field)) {
    return false;
  }
  // An enum value is compiled into a static final field of the enum class.
  // Each of these fields contain a unique object, so we can represent them
  // with a SingletonObjectDomain.
  // Note that EnumFieldAnalyzer assumes that it is the only one in a
  // combined chain of Analyzers that creates SingletonObjectDomains of Enum
  // types.
  env->set(RESULT_REGISTER, SingletonObjectDomain(field));
  return true;
}

bool EnumFieldAnalyzer::analyze_invoke(const EnumFieldAnalyzerState& state,
                                       const IRInstruction* insn,
                                       ConstantEnvironment* env) {
  auto op = insn->opcode();
  if (op == OPCODE_INVOKE_VIRTUAL) {
    auto* method =
        resolve_method_deprecated(insn->get_method(), MethodSearch::Virtual);
    if (method == nullptr) {
      return false;
    }
    if (method == state.enum_equals) {
      auto left = env->get(insn->src(0)).maybe_get<SingletonObjectDomain>();
      auto right = env->get(insn->src(1)).maybe_get<SingletonObjectDomain>();
      if (!left || !right) {
        return false;
      }
      auto left_field = left->get_constant();
      auto right_field = right->get_constant();
      if (!left_field || !right_field) {
        return false;
      }
      env->set(RESULT_REGISTER,
               SignedConstantDomain(
                   static_cast<int64_t>(left_field == right_field)));
      return true;
    }
  }
  return false;
}

bool BoxedBooleanAnalyzer::analyze_sget(const BoxedBooleanAnalyzerState& state,
                                        const IRInstruction* insn,
                                        ConstantEnvironment* env) {
  if (insn->opcode() != OPCODE_SGET_OBJECT) {
    return false;
  }
  auto* field = resolve_field(insn->get_field());
  if (field == nullptr) {
    return false;
  }
  // Boolean.TRUE and Boolean.FALSE each contain a unique object, so we can
  // represent them with a SingletonObjectDomain.
  // Note that BoxedBooleanAnalyzer assumes that it is the only one in a
  // combined chain of Analyzers that creates SingletonObjectDomains of
  // Boolean type.
  if (field != state.boolean_true && field != state.boolean_false) {
    return false;
  }
  env->set(RESULT_REGISTER, SingletonObjectDomain(field));
  return true;
}

bool BoxedBooleanAnalyzer::analyze_invoke(
    const BoxedBooleanAnalyzerState& state,
    const IRInstruction* insn,
    ConstantEnvironment* env) {
  auto* method = insn->get_method();
  if (method == nullptr || method->get_class() != state.boolean_class) {
    return false;
  }
  if (method == state.boolean_valueof) {
    auto cst = env->get<SignedConstantDomain>(insn->src(0)).get_constant();
    if (!cst) {
      return false;
    }
    if (*cst == 0) {
      env->set(RESULT_REGISTER, SingletonObjectDomain(state.boolean_false));
    } else {
      env->set(RESULT_REGISTER, SingletonObjectDomain(state.boolean_true));
    }
    return true;
  } else if (method == state.boolean_booleanvalue) {
    auto value = env->get(insn->src(0)).maybe_get<SingletonObjectDomain>();
    if (!value) {
      return false;
    }
    auto cst = value->get_constant();
    if (!cst) {
      return false;
    }
    if (cst == state.boolean_false) {
      env->set(RESULT_REGISTER, SignedConstantDomain(0));
      return true;
    } else if (cst == state.boolean_true) {
      env->set(RESULT_REGISTER, SignedConstantDomain(1));
      return true;
    } else {
      return false;
    }
  } else {
    return false;
  }
}

StringAnalyzerState StringAnalyzerState::make_default() {
  UnorderedSet<DexMethod*> methods;
  auto* kotlin_are_equal = method::kotlin_jvm_internal_Intrinsics_areEqual();
  if (kotlin_are_equal != nullptr) {
    methods.emplace(kotlin_are_equal);
  }
  return StringAnalyzerState(methods);
}

void StringAnalyzerState::set_methods_as_root() {
  for (const auto& method : UnorderedIterable(string_equality_methods)) {
    if (!method->is_external()) {
      method->rstate.set_root();
    }
  }
}

bool StringAnalyzer::analyze_invoke(const StringAnalyzerState* state,
                                    const IRInstruction* insn,
                                    ConstantEnvironment* env) {
  DexMethod* method =
      resolve_method_deprecated(insn->get_method(), opcode_to_search(insn));
  if (method == nullptr) {
    return false;
  }

  auto maybe_string = [&](int arg_idx) -> const DexString* {
    auto value = env->get(insn->src(arg_idx));
    if (value.is_top() || value.is_bottom()) {
      return nullptr;
    }
    if (const auto& string_value_opt = value.maybe_get<StringDomain>()) {
      return *string_value_opt->get_constant();
    }
    return nullptr;
  };

  if (method == method::java_lang_String_equals() ||
      (state != nullptr && state->string_equality_methods.find(method) !=
                               state->string_equality_methods.end())) {
    always_assert(insn->srcs_size() == 2);
    if (const auto* arg0 = maybe_string(0)) {
      if (const auto* arg1 = maybe_string(1)) {
        // pointer comparison is okay, DexStrings are internalized
        int64_t res = static_cast<int64_t>(arg0 == arg1);
        env->set(RESULT_REGISTER, SignedConstantDomain(res));
        return true;
      }
    }
  } else if (method == method::java_lang_String_hashCode()) {
    always_assert(insn->srcs_size() == 1);
    if (const auto* arg0 = maybe_string(0)) {
      int64_t res = arg0->java_hashcode();
      env->set(RESULT_REGISTER, SignedConstantDomain(res));
      return true;
    }
  } else if (method == method::java_lang_String_length()) {
    always_assert(insn->srcs_size() == 1);
    if (const auto* arg0 = maybe_string(0)) {
      int64_t res = arg0->length();
      env->set(RESULT_REGISTER, SignedConstantDomain(res));
      return true;
    }
  } else if (method == method::java_lang_String_isEmpty()) {
    always_assert(insn->srcs_size() == 1);
    if (const auto* arg0 = maybe_string(0)) {
      int64_t res = arg0->length() == 0 ? 1 : 0;
      env->set(RESULT_REGISTER, SignedConstantDomain(res));
      return true;
    }
  } else if (method == method::java_lang_String_charAt()) {
    always_assert(insn->srcs_size() == 2);
    if (const auto* arg0 = maybe_string(0)) {
      auto idx_const =
          env->get<SignedConstantDomain>(insn->src(1)).get_constant();
      if (idx_const) {
        int64_t i = *idx_const;
        // Only fold for ASCII-only strings where MUTF-8 byte index
        // equals UTF-16 code unit index.
        if (arg0->is_simple() && i >= 0 &&
            i < static_cast<int64_t>(arg0->length())) {
          int64_t ch = static_cast<uint8_t>(arg0->c_str()[i]);
          env->set(RESULT_REGISTER, SignedConstantDomain(ch));
          return true;
        }
      }
    }
  }

  return false;
}

bool NewObjectAnalyzer::ignore_type(
    const ImmutableAttributeAnalyzerState* state, const DexType* type) {
  // Avoid types that may interact other more specialized object domains.
  if (state->may_be_initialized_type(type) ||
      type == type::java_lang_String() || type == type::java_lang_Boolean()) {
    return true;
  }
  auto* cls = type_class(type);
  return (cls != nullptr) && is_enum(cls);
}

bool NewObjectAnalyzer::analyze_new_instance(
    const ImmutableAttributeAnalyzerState* state,
    const IRInstruction* insn,
    ConstantEnvironment* env) {
  if (ignore_type(state, insn->get_type())) {
    return false;
  }
  env->set(RESULT_REGISTER, NewObjectDomain(insn));
  return true;
}

bool NewObjectAnalyzer::analyze_filled_new_array(
    const ImmutableAttributeAnalyzerState* state,
    const IRInstruction* insn,
    ConstantEnvironment* env) {
  if (ignore_type(state, insn->get_type())) {
    return false;
  }
  auto array_length =
      SignedConstantDomain(static_cast<int64_t>(insn->srcs_size()));
  env->set(RESULT_REGISTER, NewObjectDomain(insn, array_length));
  return true;
}

bool NewObjectAnalyzer::analyze_new_array(
    const ImmutableAttributeAnalyzerState* state,
    const IRInstruction* insn,
    ConstantEnvironment* env) {
  if (ignore_type(state, insn->get_type())) {
    return false;
  }
  SignedConstantDomain array_length =
      env->get<SignedConstantDomain>(insn->src(0));
  array_length.meet_with(SignedConstantDomain(sign_domain::Interval::GEZ));
  env->set(RESULT_REGISTER, NewObjectDomain(insn, array_length));
  return true;
}

bool NewObjectAnalyzer::analyze_instance_of(
    const ImmutableAttributeAnalyzerState*,
    const IRInstruction* insn,
    ConstantEnvironment* env) {
  auto new_obj_opt = env->get(insn->src(0)).maybe_get<NewObjectDomain>();
  if (!new_obj_opt) {
    return false;
  }
  const auto* obj_type = new_obj_opt->get_type();
  if (obj_type == nullptr) {
    return false;
  }
  auto* cls = type_class(type::make_element_type_if_array(obj_type));
  if ((cls == nullptr) ||
      (cls->is_external() && obj_type != insn->get_type())) {
    return false;
  }
  auto res = type::check_cast(obj_type, insn->get_type());
  env->set(RESULT_REGISTER, SignedConstantDomain(res ? 1 : 0));
  return true;
}

bool NewObjectAnalyzer::analyze_array_length(
    const ImmutableAttributeAnalyzerState*,
    const IRInstruction* insn,
    ConstantEnvironment* env) {
  auto new_obj_opt = env->get(insn->src(0)).maybe_get<NewObjectDomain>();
  if (!new_obj_opt) {
    return false;
  }
  auto array_length = new_obj_opt->get_array_length();
  env->set(RESULT_REGISTER, SignedConstantDomain(array_length));
  return true;
}

ImmutableAttributeAnalyzerState::Initializer&
ImmutableAttributeAnalyzerState::add_initializer(DexMethod* initialize_method,
                                                 DexMethod* attr) {
  attribute_methods.insert(attr);
  ImmutableAttributeAnalyzerState::Initializer* new_initializer = nullptr;
  method_initializers.update(
      initialize_method,
      [&](DexMethod*, std::vector<std::unique_ptr<Initializer>>& initializers,
          bool) {
        initializers.emplace_back(
            std::make_unique<Initializer>(Initializer(attr)));
        new_initializer = initializers.back().get();
        // Need to keep this sorted for fast join and runtime_equals.
        std::sort(initializers.begin(), initializers.end(),
                  [](const auto& lhs, const auto& rhs) {
                    return lhs->attr < rhs->attr;
                  });
      });
  redex_assert(new_initializer);
  initialized_types.insert(initialized_type(initialize_method));
  return *new_initializer;
}

ImmutableAttributeAnalyzerState::Initializer&
ImmutableAttributeAnalyzerState::add_initializer(DexMethod* initialize_method,
                                                 DexField* attr) {
  attribute_fields.insert(attr);
  ImmutableAttributeAnalyzerState::Initializer* new_initializer = nullptr;
  method_initializers.update(
      initialize_method,
      [&](DexMethod*, std::vector<std::unique_ptr<Initializer>>& initializers,
          bool) {
        initializers.emplace_back(
            std::make_unique<Initializer>(Initializer(attr)));
        new_initializer = initializers.back().get();
        // Need to keep this sorted for fast join and runtime_equals.
        std::sort(initializers.begin(), initializers.end(),
                  [](const auto& lhs, const auto& rhs) {
                    return lhs->attr < rhs->attr;
                  });
      });
  redex_assert(new_initializer);
  initialized_types.insert(initialized_type(initialize_method));
  return *new_initializer;
}

ImmutableAttributeAnalyzerState::Initializer&
ImmutableAttributeAnalyzerState::add_initializer(
    DexMethod* initialize_method, const ImmutableAttr::Attr& attr) {
  return attr.is_field() ? add_initializer(initialize_method, attr.val.field)
                         : add_initializer(initialize_method, attr.val.method);
}

ImmutableAttributeAnalyzerState::ImmutableAttributeAnalyzerState() {
  // clang-format off
  // Integer can be initialized throuth
  //  invoke-static v0 Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;
  // clang-format on
  // Other boxed types are similar.
  struct BoxedTypeInfo {
    DexType* type;
    long begin;
    long end;
  };
  // See e.g.
  // https://cs.android.com/android/platform/superproject/+/master:libcore/ojluni/src/main/java/java/lang/Integer.java
  // for what is actually cached on Android. Note:
  // - We don't handle java.lang.Boolean here, as that's more appropriate
  // handled by the
  //   BoxedBooleanAnalyzer, which also knows about the FALSE and TRUE fields.
  // - The actual upper bound of cached Integers is actually configurable. We
  //   just use the minimum value here.
  std::array<BoxedTypeInfo, 7> boxed_type_infos = {
      BoxedTypeInfo{type::java_lang_Byte(), -128, 128},
      BoxedTypeInfo{type::java_lang_Short(), -128, 128},
      BoxedTypeInfo{type::java_lang_Character(), 0, 128},
      BoxedTypeInfo{type::java_lang_Integer(), -128, 128},
      BoxedTypeInfo{type::java_lang_Long(), -128, 128},
      BoxedTypeInfo{type::java_lang_Float(), 0, 0},
      BoxedTypeInfo{type::java_lang_Double(), 0, 0}};
  for (auto& bti : boxed_type_infos) {
    auto* valueOf = type::make_value_of_method_for_type(bti.type);
    auto* getter_method = type::make_unboxing_method_for_type(bti.type);
    if ((valueOf != nullptr) && (getter_method != nullptr) &&
        valueOf->is_def() && getter_method->is_def()) {
      add_initializer(valueOf->as_def(), getter_method->as_def())
          .set_src_id_of_attr(0)
          .set_obj_to_dest();
      if (bti.end > bti.begin) {
        add_cached_boxed_objects(valueOf->as_def(), bti.begin, bti.end);
      }
    }
  }
}

void ImmutableAttributeAnalyzerState::add_cached_boxed_objects(
    DexMethod* initialize_method, long begin, long end) {
  always_assert(begin < end);
  cached_boxed_objects.emplace(initialize_method,
                               CachedBoxedObjects{begin, end});
}

bool ImmutableAttributeAnalyzerState::is_jvm_cached_object(
    DexMethod* initialize_method, long value) const {
  auto it = cached_boxed_objects.find(initialize_method);
  if (it == cached_boxed_objects.end()) {
    return false;
  }
  const auto& cached_objects = it->second;
  return value >= cached_objects.begin && value < cached_objects.end;
}

const DexType* ImmutableAttributeAnalyzerState::initialized_type(
    const DexMethod* initialize_method) {
  auto* res = method::is_init(initialize_method)
                  ? initialize_method->get_class()
                  : initialize_method->get_proto()->get_rtype();
  always_assert(!type::is_primitive(res));
  always_assert(res != type::java_lang_Object());
  always_assert(!type::is_array(res));
  return res;
}

bool ImmutableAttributeAnalyzerState::may_be_initialized_type(
    const DexType* type) const {
  if (type == nullptr || type::is_array(type)) {
    return false;
  }
  always_assert(!type::is_primitive(type));
  return *may_be_initialized_types
              .get_or_create_and_assert_equal(
                  type,
                  [&](const DexType*) {
                    return compute_may_be_initialized_type(type);
                  })
              .first;
}

bool ImmutableAttributeAnalyzerState::compute_may_be_initialized_type(
    const DexType* type) const {
  // Here we effectively check if check_cast(type, x) for any x in
  // initialized_types.
  always_assert(type != nullptr);
  if (initialized_types.count_unsafe(type) != 0u) {
    return true;
  }
  auto* cls = type_class(type);
  if (cls == nullptr) {
    return false;
  }
  if (may_be_initialized_type(cls->get_super_class())) {
    return true;
  }
  auto* intfs = cls->get_interfaces();
  for (auto* intf : *intfs) {
    if (may_be_initialized_type(intf)) {
      return true;
    }
  }
  return false;
}

bool ImmutableAttributeAnalyzer::analyze_iget(
    const ImmutableAttributeAnalyzerState* state,
    const IRInstruction* insn,
    ConstantEnvironment* env) {
  auto* field_ref = insn->get_field();
  DexField* field = resolve_field(field_ref, FieldSearch::Instance);
  if (field == nullptr) {
    field = dynamic_cast<DexField*>(field_ref);
  }

  // Immutable state should not be updated in parallel with analysis.

  if (state->attribute_fields.count_unsafe(field) == 0u) {
    return false;
  }
  auto this_domain = env->get(insn->src(0));
  if (this_domain.is_top() || this_domain.is_bottom()) {
    return false;
  }
  if (const auto& obj_or_none =
          this_domain.maybe_get<ObjectWithImmutAttrDomain>()) {
    auto object = obj_or_none->get_constant();
    auto value = object->get_value(field);
    if (value && !value->is_top()) {
      if (const auto& string_value = value->maybe_get<StringDomain>()) {
        env->set(RESULT_REGISTER, *string_value);
        return true;
      } else if (const auto& signed_value =
                     value->maybe_get<SignedConstantDomain>()) {
        env->set(RESULT_REGISTER, *signed_value);
        return true;
      }
    }
    return false;
  } else {
    return false;
  }
}

bool ImmutableAttributeAnalyzer::analyze_invoke(
    const ImmutableAttributeAnalyzerState* state,
    const IRInstruction* insn,
    ConstantEnvironment* env) {
  auto* method_ref = insn->get_method();
  DexMethod* method =
      resolve_method_deprecated(method_ref, opcode_to_search(insn));
  if (method == nullptr) {
    // Redex may run without sdk as input, so the method resolving may fail.
    // Example: Integer.valueOf(I) is an external method.
    method = dynamic_cast<DexMethod*>(method_ref);
  }

  // Immutable state should not be updated in parallel with analysis.

  if (state->method_initializers.count_unsafe(method) != 0u) {
    return analyze_method_initialization(state, insn, env, method);
  } else if (state->attribute_methods.count_unsafe(method) != 0u) {
    return analyze_method_attr(state, insn, env, method);
  }
  return false;
}

/**
 * Propagate method return value if this method is a getter method of an
 * immutable field of an object. `Integer.intValue()` is a such method.
 */
bool ImmutableAttributeAnalyzer::analyze_method_attr(
    const ImmutableAttributeAnalyzerState* /* unused */,
    const IRInstruction* insn,
    ConstantEnvironment* env,
    DexMethod* method) {
  if (insn->srcs_size() != 1) {
    return false;
  }
  auto this_domain = env->get(insn->src(0));
  if (this_domain.is_top() || this_domain.is_bottom()) {
    return false;
  }
  if (const auto& obj_or_none =
          this_domain.maybe_get<ObjectWithImmutAttrDomain>()) {
    auto object = obj_or_none->get_constant();
    auto value = object->get_value(method);
    if (value && !value->is_top()) {
      if (const auto& string_value = value->maybe_get<StringDomain>()) {
        env->set(RESULT_REGISTER, *string_value);
        return true;
      } else if (const auto& signed_value =
                     value->maybe_get<SignedConstantDomain>()) {
        env->set(RESULT_REGISTER, *signed_value);
        return true;
      }
    }
    return false;
  } else {
    return false;
  }
}

bool ImmutableAttributeAnalyzer::analyze_method_initialization(
    const ImmutableAttributeAnalyzerState* state,
    const IRInstruction* insn,
    ConstantEnvironment* env,
    DexMethod* method) {
  auto it = state->method_initializers.find(method);
  if (it == state->method_initializers.end()) {
    return false;
  }
  ObjectWithImmutAttr object(
      ImmutableAttributeAnalyzerState::initialized_type(method),
      static_cast<uint32_t>(it->second.size()));
  // Only support one register for the object, can be easily extended. For
  // example, virtual method may return `this` pointer, so two registers are
  // holding the same heap object.
  reg_t obj_reg;
  bool has_value = false;
  for (const auto& initializer : it->second) {
    obj_reg = initializer->obj_is_dest()
                  ? RESULT_REGISTER
                  : insn->src(*initializer->insn_src_id_of_obj);
    const auto& domain = env->get(insn->src(initializer->insn_src_id_of_attr));
    if (const auto& signed_value = domain.maybe_get<SignedConstantDomain>()) {
      auto constant = signed_value->get_constant();
      if (!constant) {
        object.write_value(initializer->attr, SignedConstantDomain::top());
        continue;
      }
      object.jvm_cached_singleton =
          state->is_jvm_cached_object(method, *constant);
      object.write_value(initializer->attr, *signed_value);
      has_value = true;
    } else if (const auto& string_value = domain.maybe_get<StringDomain>()) {
      if (!string_value->is_value()) {
        object.write_value(initializer->attr, StringDomain::top());
        continue;
      }
      object.write_value(initializer->attr, *string_value);
      has_value = true;
    } else if (const auto& type_value =
                   domain.maybe_get<ConstantClassObjectDomain>()) {
      if (!type_value->is_value()) {
        object.write_value(initializer->attr, ConstantClassObjectDomain::top());
        continue;
      }
      object.write_value(initializer->attr, *type_value);
      has_value = true;
    }
  }
  if (!has_value || object.empty()) {
    return false;
  }
  env->set(obj_reg, ObjectWithImmutAttrDomain(std::move(object)));
  return true;
}

void semantically_inline_method(
    IRCode* callee_code,
    const IRInstruction* insn,
    const InstructionAnalyzer<ConstantEnvironment>& analyzer,
    ConstantEnvironment* env) {
  always_assert(callee_code->cfg_built());
  auto& cfg = callee_code->cfg();

  // Set up the environment at entry into the callee.
  ConstantEnvironment call_entry_env;
  auto load_params = cfg.get_param_instructions();
  auto load_params_it = InstructionIterable(load_params).begin();
  for (size_t i = 0; i < insn->srcs_size(); ++i) {
    call_entry_env.set(load_params_it->insn->dest(), env->get(insn->src(i)));
    ++load_params_it;
  }
  call_entry_env.mutate_heap(
      [env](ConstantHeap* heap) { *heap = env->get_heap(); });

  // Analyze the callee.
  auto fp_iter =
      std::make_unique<intraprocedural::FixpointIterator>(cfg, analyzer);
  fp_iter->run(call_entry_env);

  // Update the caller's environment with the callee's return states.
  auto return_state = collect_return_state(callee_code, *fp_iter);
  env->set(RESULT_REGISTER, return_state.get_value());
  env->mutate_heap(
      [&return_state](ConstantHeap* heap) { *heap = return_state.get_heap(); });
}

ReturnState collect_return_state(
    IRCode* code, const intraprocedural::FixpointIterator& fp_iter) {
  always_assert(code->cfg_built());
  auto& cfg = code->cfg();
  auto return_state = ReturnState::bottom();
  for (cfg::Block* b : cfg.blocks()) {
    auto env = fp_iter.get_entry_state_at(b);
    auto last_insn = b->get_last_insn();
    for (auto& mie : InstructionIterable(b)) {
      auto* insn = mie.insn;
      fp_iter.analyze_instruction(insn, &env, insn == last_insn->insn);
      if (opcode::is_a_return(insn->opcode())) {
        if (insn->opcode() != OPCODE_RETURN_VOID) {
          return_state.join_with(
              ReturnState(env.get(insn->dest()), env.get_heap()));
        } else {
          return_state.join_with(
              ReturnState(ConstantValue::top(), env.get_heap()));
        }
      }
    }
  }
  return return_state;
}

bool EnumUtilsFieldAnalyzer::analyze_sget(
    ImmutableAttributeAnalyzerState* state,
    const IRInstruction* insn,
    ConstantEnvironment* env) {
  // The $EnumUtils class contains fields named fXXX, where XXX encodes a 32-bit
  // number whose boxed value is stored as a java.lang.Integer instance in that
  // field. These fields are initialized through Integer.valueOf(...).
  auto* integer_type = type::java_lang_Integer();
  auto* field = resolve_field(insn->get_field());
  if (field == nullptr || !is_final(field) ||
      field->get_type() != integer_type || field->str().empty() ||
      field->str()[0] != 'f' ||
      field->get_class() != DexType::make_type("Lredex/$EnumUtils;")) {
    return false;
  }
  auto* valueOf = method::java_lang_Integer_valueOf();
  auto it = state->method_initializers.find(valueOf);
  if (it == state->method_initializers.end()) {
    return false;
  }
  const auto& initializers = it->second;
  const auto& initializer = only(initializers);
  always_assert(initializer->insn_src_id_of_attr == 0);

  const auto name = field->str();
  auto value = std::stoi(str_copy(name.substr(1)));
  ObjectWithImmutAttr object(integer_type, 1);
  object.write_value(initializer->attr, SignedConstantDomain(value));
  object.jvm_cached_singleton = state->is_jvm_cached_object(valueOf, value);
  env->set(RESULT_REGISTER, ObjectWithImmutAttrDomain(std::move(object)));
  return true;
}

ApiLevelAnalyzerState::ApiLevelAnalyzerState(int32_t min_sdk)
    : min_sdk(min_sdk) {
  sdk_int_field = DexField::get_field("Landroid/os/Build$VERSION;.SDK_INT:I");
}

bool ApiLevelAnalyzer::analyze_sget(const ApiLevelAnalyzerState& state,
                                    const IRInstruction* insn,
                                    ConstantEnvironment* env) {
  auto* field = insn->get_field();
  if ((field != nullptr) && field == state.sdk_int_field) {
    // possible range is [min_sdk, max_int]
    env->set(RESULT_REGISTER,
             SignedConstantDomain(state.min_sdk,
                                  std::numeric_limits<int32_t>::max()));
    return true;
  }
  return false;
}

PackageNameState PackageNameState::make(
    const std::optional<std::string>& package_name) {
  UnorderedSet<DexMethodRef*> refs{
      DexMethod::get_method(
          "Landroid/content/Context;.getPackageName:()Ljava/lang/String;"),
      DexMethod::get_method(
          "Landroid/content/ContextWrapper;.getPackageName:()Ljava/lang/"
          "String;")};
  const DexString* dex_string = package_name != std::nullopt
                                    ? DexString::make_string(*package_name)
                                    : nullptr;
  return {std::move(refs), dex_string};
}

bool PackageNameAnalyzer::analyze_invoke(const PackageNameState* state,
                                         const IRInstruction* insn,
                                         ConstantEnvironment* env) {
  auto* method = insn->get_method();
  if ((method != nullptr) && (state != nullptr) &&
      (state->package_name != nullptr) &&
      state->getter_methods.count(method) > 0) {
    env->set(RESULT_REGISTER, StringDomain(state->package_name));
    return true;
  }
  return false;
}

const DexType* get_object_constant_type(const ConstantValue& value) {
  if (auto s = value.maybe_get<StringDomain>(); s && s->get_constant()) {
    return type::java_lang_String();
  }
  if (auto c = value.maybe_get<ConstantClassObjectDomain>();
      c && c->get_constant()) {
    return type::java_lang_Class();
  }
  return nullptr;
}

namespace intraprocedural {

FixpointIterator::FixpointIterator(
    const cfg::ControlFlowGraph& cfg,
    InstructionAnalyzer<ConstantEnvironment> insn_analyzer,
    InstructionAnalyzer<ConstantEnvironment> no_throw_analyzer,
    bool imprecise_switches)
    : BaseEdgeAwareIRAnalyzer(cfg),
      m_insn_analyzer(std::move(insn_analyzer)),
      m_no_throw_analyzer(std::move(no_throw_analyzer)),
      m_imprecise_switches(imprecise_switches) {}

void FixpointIterator::analyze_instruction_normal(
    const IRInstruction* insn, ConstantEnvironment* env) const {
  m_insn_analyzer(insn, env);
}

bool DefaultNoThrowAnalyzer::analyze_default(
    const NullCheckMethods* null_check_methods,
    const IRInstruction* insn,
    ConstantEnvironment* env) {
  // This case is an unconditional throw, so the no-throw successor is dead.
  // Pruning it stops the constant from reaching a downstream pass that would
  // materialize it into a target-typed slot it cannot hold -- ill-typed code.
  // External targets are skipped: their class hierarchy may be incomplete to
  // decide castability.
  if (enable_check_cast_value_preservation &&
      insn->opcode() == OPCODE_CHECK_CAST) {
    const DexType* const_type =
        get_object_constant_type(env->get(insn->src(0)));
    if (const_type != nullptr) {
      auto* target_cls = type_class(insn->get_type());
      if (target_cls != nullptr && !target_cls->is_external() &&
          !type::check_cast(const_type, insn->get_type())) {
        env->set_to_bottom();
      }
    }
    return false;
  }
  auto src_index = get_dereferenced_object_src_index(insn);
  if (!src_index && null_check_methods != nullptr) {
    src_index = get_null_check_object_index(insn, *null_check_methods);
  }
  if (!src_index) {
    if (null_check_methods == nullptr ||
        insn->opcode() != OPCODE_INVOKE_STATIC ||
        insn->get_method() !=
            null_check_methods->redex_null_check_assertion()) {
      return false;
    }
    src_index = 0;
  }
  if (insn->has_dest()) {
    auto dest = insn->dest();
    if ((dest == *src_index) ||
        (insn->dest_is_wide() && dest + 1 == *src_index)) {
      return false;
    }
  }
  auto src = insn->src(*src_index);
  auto value = env->get(src);
  value.meet_with(SignedConstantDomain(sign_domain::Interval::NEZ));
  env->set(src, value);
  return false;
}

InstructionAnalyzer<ConstantEnvironment> make_default_no_throw_analyzer(
    const NullCheckMethods* null_check_methods) {
  return InstructionAnalyzerCombiner<DefaultNoThrowAnalyzer>(
      null_check_methods);
}

void FixpointIterator::analyze_no_throw(const IRInstruction* insn,
                                        ConstantEnvironment* env) const {
  if (m_no_throw_analyzer) {
    m_no_throw_analyzer(insn, env);
  }
}

/*
 * Helpers for CFG edge analysis
 */
namespace {
struct IfZeroMeetWith {
  sign_domain::Interval right_zero_meet_interval;
  std::optional<sign_domain::Interval> left_zero_meet_interval{std::nullopt};
};
} // namespace

static const UnorderedMap<IROpcode, IfZeroMeetWith, boost::hash<IROpcode>>
    if_zero_meet_with{
        {OPCODE_IF_EQZ, {sign_domain::Interval::EQZ}},
        {OPCODE_IF_NEZ, {sign_domain::Interval::NEZ}},
        {OPCODE_IF_LTZ, {sign_domain::Interval::LTZ}},
        {OPCODE_IF_GTZ, {sign_domain::Interval::GTZ}},
        {OPCODE_IF_LEZ, {sign_domain::Interval::LEZ}},
        {OPCODE_IF_GEZ, {sign_domain::Interval::GEZ}},

        {OPCODE_IF_EQ,
         {sign_domain::Interval::EQZ, sign_domain::Interval::EQZ}},
        {OPCODE_IF_NE,
         {sign_domain::Interval::NEZ, sign_domain::Interval::NEZ}},
        {OPCODE_IF_LT,
         {sign_domain::Interval::LTZ, sign_domain::Interval::GTZ}},
        {OPCODE_IF_GT,
         {sign_domain::Interval::GTZ, sign_domain::Interval::LTZ}},
        {OPCODE_IF_LE,
         {sign_domain::Interval::LEZ, sign_domain::Interval::GEZ}},
        {OPCODE_IF_GE,
         {sign_domain::Interval::GEZ, sign_domain::Interval::LEZ}},
    };

static std::pair<SignedConstantDomain, SignedConstantDomain> refine_lt(
    const SignedConstantDomain& left, const SignedConstantDomain& right) {
  if (right.max_element_int() == std::numeric_limits<int32_t>::min() ||
      left.min_element_int() == std::numeric_limits<int32_t>::max()) {
    return {SignedConstantDomain::bottom(), SignedConstantDomain::bottom()};
  }
  return {
      left.meet(SignedConstantDomain(std::numeric_limits<int32_t>::min(),
                                     right.max_element_int() - 1)),
      right.meet(SignedConstantDomain(left.min_element_int() + 1,
                                      std::numeric_limits<int32_t>::max()))};
}

static std::pair<SignedConstantDomain, SignedConstantDomain> refine_le(
    const SignedConstantDomain& left, const SignedConstantDomain& right) {
  return {left.meet(SignedConstantDomain(std::numeric_limits<int32_t>::min(),
                                         right.max_element_int())),
          right.meet(SignedConstantDomain(
              left.min_element_int(), std::numeric_limits<int32_t>::max()))};
}

static SignedConstantDomain refine_ne_left(const SignedConstantDomain& left,
                                           const SignedConstantDomain& right) {
  auto c = right.clamp_int().get_constant();
  if (c) {
    always_assert(*c >= std::numeric_limits<int32_t>::min());
    always_assert(*c <= std::numeric_limits<int32_t>::max());
    if (*c == left.min_element_int()) {
      if (*c >= left.max_element_int()) {
        return SignedConstantDomain::bottom();
      }
      return left.meet(SignedConstantDomain(*c + 1, left.max_element_int()));
    }
    if (*c == left.max_element_int()) {
      if (*c <= left.min_element_int()) {
        return SignedConstantDomain::bottom();
      }
      return left.meet(SignedConstantDomain(left.min_element_int(), *c - 1));
    }
  }
  return left;
}

/*
 * If we can determine that a branch is not taken based on the constants in
 * the environment, set the environment to bottom upon entry into the
 * unreachable block.
 */
void FixpointIterator::analyze_if(const IRInstruction* insn,
                                  cfg::Edge* const& edge,
                                  ConstantEnvironment* env) const {
  if (env->is_bottom()) {
    return;
  }
  bool is_true_branch = edge->type() == cfg::EDGE_BRANCH;
  // Inverting the conditional here means that we only need to consider the
  // "true" case of the if-* opcode
  auto op = !is_true_branch ? opcode::invert_conditional_branch(insn->opcode())
                            : insn->opcode();
  auto left = env->get(insn->src(0));
  auto right =
      insn->srcs_size() > 1 ? env->get(insn->src(1)) : SignedConstantDomain(0);
  const IfZeroMeetWith& izmw = if_zero_meet_with.at(op);
  if (right.is_zero()) {
    env->set(insn->src(0),
             left.meet(SignedConstantDomain(izmw.right_zero_meet_interval)));
    return;
  }
  if (left.is_zero()) {
    env->set(insn->src(1),
             right.meet(SignedConstantDomain(*izmw.left_zero_meet_interval)));
    return;
  }

  switch (op) {
  case OPCODE_IF_EQ: {
    auto refined_value = left.meet(right);
    env->set(insn->src(0), refined_value);
    env->set(insn->src(1), refined_value);
    break;
  }
  case OPCODE_IF_NE: {
    if (ConstantValue::apply_visitor(runtime_equals_visitor(), left, right)) {
      env->set_to_bottom();
    } else {
      auto scd_left = left.maybe_get<SignedConstantDomain>();
      auto scd_right = right.maybe_get<SignedConstantDomain>();
      if (scd_left && scd_right) {
        env->set(insn->src(0), refine_ne_left(*scd_left, *scd_right));
        if (insn->srcs_size() > 1) {
          env->set(insn->src(1), refine_ne_left(*scd_right, *scd_left));
        }
      }
    }
    break;
  }
  case OPCODE_IF_LT: {
    if (ConstantValue::apply_visitor(runtime_leq_visitor(), right, left)) {
      env->set_to_bottom();
    } else {
      auto scd_left = left.maybe_get<SignedConstantDomain>();
      auto scd_right = right.maybe_get<SignedConstantDomain>();
      if (scd_left && scd_right) {
        auto p = refine_lt(*scd_left, *scd_right);
        env->set(insn->src(0), p.first);
        if (insn->srcs_size() > 1) {
          env->set(insn->src(1), p.second);
        }
      }
    }
    break;
  }
  case OPCODE_IF_GT: {
    if (ConstantValue::apply_visitor(runtime_leq_visitor(), left, right)) {
      env->set_to_bottom();
    } else {
      auto scd_left = left.maybe_get<SignedConstantDomain>();
      auto scd_right = right.maybe_get<SignedConstantDomain>();
      if (scd_left && scd_right) {
        auto p = refine_lt(*scd_right, *scd_left);
        env->set(insn->src(0), p.second);
        if (insn->srcs_size() > 1) {
          env->set(insn->src(1), p.first);
        }
      }
    }
    break;
  }
  case OPCODE_IF_LE: {
    if (ConstantValue::apply_visitor(runtime_lt_visitor(), right, left)) {
      env->set_to_bottom();
    } else {
      auto scd_left = left.maybe_get<SignedConstantDomain>();
      auto scd_right = right.maybe_get<SignedConstantDomain>();
      if (scd_left && scd_right) {
        auto p = refine_le(*scd_left, *scd_right);
        env->set(insn->src(0), p.first);
        if (insn->srcs_size() > 1) {
          env->set(insn->src(1), p.second);
        }
      }
    }
    break;
  }
  case OPCODE_IF_GE: {
    if (ConstantValue::apply_visitor(runtime_lt_visitor(), left, right)) {
      env->set_to_bottom();
    } else {
      auto scd_left = left.maybe_get<SignedConstantDomain>();
      auto scd_right = right.maybe_get<SignedConstantDomain>();
      if (scd_left && scd_right) {
        auto p = refine_le(*scd_right, *scd_left);
        env->set(insn->src(0), p.second);
        if (insn->srcs_size() > 1) {
          env->set(insn->src(1), p.first);
        }
      }
    }
    break;
  }
  default: {
    not_reached_log("expected if-* opcode, got %s", SHOW(insn));
  }
  }
}

void FixpointIterator::analyze_switch(const IRInstruction* insn,
                                      cfg::Edge* const& edge,
                                      ConstantEnvironment* env) const {
  auto selector_val = env->get(insn->src(0));
  const auto& case_key = edge->case_key();
  if (case_key) {
    always_assert(edge->type() == cfg::EDGE_BRANCH);
    selector_val.meet_with(SignedConstantDomain(*case_key));
    if (m_imprecise_switches) {
      // We could refine the selector value itself, for maximum knowledge.
      // However, in practice, this can cause following blocks to be refined
      // with the constant, which then degrades subsequent block deduping.
      if (selector_val.is_bottom()) {
        env->set_to_bottom();
        return;
      }
    } else {
      env->set(insn->src(0), selector_val);
    }
  } else {
    always_assert(edge->type() == cfg::EDGE_GOTO);
    // We are looking at the fallthrough case. Set env to bottom in case there
    // is a non-fallthrough edge with a case-key that is equal to the actual
    // selector value.
    auto scd = selector_val.maybe_get<SignedConstantDomain>();
    if (!scd) {
      return;
    }
    auto selector_const = scd->get_constant();
    if (selector_const &&
        has_switch_consecutive_case_keys(
            edge->src(), static_cast<int32_t>(*selector_const),
            static_cast<int32_t>(*selector_const))) {
      env->set_to_bottom();
      return;
    }
    auto numeric_interval_domain = scd->numeric_interval_domain();
    if (numeric_interval_domain.is_bottom()) {
      return;
    }
    auto lb = numeric_interval_domain.lower_bound();
    auto ub = numeric_interval_domain.upper_bound();
    if (lb > NumericIntervalDomain::MIN && ub < NumericIntervalDomain::MAX &&
        has_switch_consecutive_case_keys(edge->src(), static_cast<int32_t>(lb),
                                         static_cast<int32_t>(ub))) {
      env->set_to_bottom();
      return;
    }
  }
}

} // namespace intraprocedural

} // namespace constant_propagation
