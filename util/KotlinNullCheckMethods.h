/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "ControlFlow.h"
#include "DeterministicContainers.h"
#include "DexClass.h"
#include "MethodUtil.h"

namespace kotlin_nullcheck_wrapper {
enum NullErrSrc {
  UNKNOWN_SRC = 0,
  LOAD_PARAM,
  CONST,
  INSTANCE_FIELD,
  STATIC_FIELD,
  ARRAY_ELEMENT,
  INVOKE_RETURN,
  CHECK_CAST
};

constexpr std::initializer_list<NullErrSrc> all_NullErrSrc = {
    UNKNOWN_SRC,  LOAD_PARAM,    CONST,         INSTANCE_FIELD,
    STATIC_FIELD, ARRAY_ELEMENT, INVOKE_RETURN, CHECK_CAST};

inline std::string get_err_msg(NullErrSrc err) {
  switch (err) {
  case NullErrSrc::UNKNOWN_SRC:
    return "UNKNOWN";
  case NullErrSrc::LOAD_PARAM:
    return "LOAD_PARAM";
  case NullErrSrc::CONST:
    return "CONST";
  case NullErrSrc::INSTANCE_FIELD:
    return "INSTANCE_FIELD";
  case NullErrSrc::STATIC_FIELD:
    return "STATIC_FIELD";
  case NullErrSrc::ARRAY_ELEMENT:
    return "ARRAY_ELEMENT";
  case NullErrSrc::INVOKE_RETURN:
    return "INVOKE_RETURN";
  case NullErrSrc::CHECK_CAST:
    return "CHECK_CAST";
  default:
    return "";
  }
}

constexpr const char* WRAPPER_CHECK_PARAM_NULL_METHOD_V1_3 =
    "$WrCheckParameter_V1_3";
constexpr const char* WRAPPER_CHECK_PARAM_NULL_METHOD_V1_4 =
    "$WrCheckParameter_V1_4";
constexpr const char* WRAPPER_CHECK_EXPR_NULL_METHOD_V1_3_PRE =
    "$WrCheckExpression_V1_3_";
constexpr const char* WRAPPER_CHECK_EXPR_NULL_METHOD_V1_4_PRE =
    "$WrCheckExpression_V1_4_";

constexpr const char* CHECK_PARAM_NULL_SIGNATURE_V1_3 =
    "Lkotlin/jvm/internal/Intrinsics;.checkParameterIsNotNull:(Ljava/lang/"
    "Object;Ljava/lang/String;)V";
constexpr const char* CHECK_PARAM_NULL_SIGNATURE_V1_4 =
    "Lkotlin/jvm/internal/Intrinsics;.checkNotNullParameter:(Ljava/lang/"
    "Object;Ljava/lang/String;)V";
constexpr const char* CHECK_EXPR_NULL_SIGNATURE_V1_3 =
    "Lkotlin/jvm/internal/Intrinsics;.checkExpressionValueIsNotNull:(Ljava/"
    "lang/Object;Ljava/lang/String;)V";
constexpr const char* CHECK_EXPR_NULL_SIGNATURE_V1_4 =
    "Lkotlin/jvm/internal/Intrinsics;.checkNotNullExpressionValue:(Ljava/"
    "lang/Object;Ljava/lang/String;)V";

constexpr const char* NEW_CHECK_PARAM_NULL_SIGNATURE_V1_3 =
    "Lkotlin/jvm/internal/Intrinsics;.$WrCheckParameter_V1_3:(Ljava/lang/"
    "Object;I)V";

constexpr const char* NEW_CHECK_PARAM_NULL_SIGNATURE_V1_4 =
    "Lkotlin/jvm/internal/Intrinsics;.$WrCheckParameter_V1_4:(Ljava/lang/"
    "Object;I)V";

constexpr const char* NEW_CHECK_EXPR_NULL_SIGNATURE_V1_3_PRE =
    "Lkotlin/jvm/internal/Intrinsics;.$WrCheckExpression_V1_3_";
constexpr const char* NEW_CHECK_EXPR_NULL_SIGNATURE_V1_4_PRE =
    "Lkotlin/jvm/internal/Intrinsics;.$WrCheckExpression_V1_4_";

constexpr const char* NEW_CHECK_EXPR_NULL_SIGNATURE_POST =
    ":(Ljava/lang/Object;)V";

// Wrapper for Kotlin null safety check
// Lkotlin/jvm/internal/Intrinsics;.checkParameterIsNotNull which does not
// require name of the parameter.
inline DexMethod* kotlin_jvm_internal_Intrinsics_WrCheckParameter_V1_3() {
  return dynamic_cast<DexMethod*>(
      DexMethod::get_method(NEW_CHECK_PARAM_NULL_SIGNATURE_V1_3));
}

inline DexMethod* kotlin_jvm_internal_Intrinsics_WrCheckParameter_V1_4() {
  return dynamic_cast<DexMethod*>(
      DexMethod::get_method(NEW_CHECK_PARAM_NULL_SIGNATURE_V1_4));
}

// Wrapper for Kotlin null safety check
// Lkotlin/jvm/internal/Intrinsics;.checkExpressionValueIsNotNull which does not
// require name of the expression.
inline DexMethod* kotlin_jvm_internal_Intrinsics_WrCheckExpression_V1_3(
    const std::string& msg) {
  std::string wrapper_signature;
  wrapper_signature.append(NEW_CHECK_EXPR_NULL_SIGNATURE_V1_3_PRE);
  wrapper_signature.append(msg);
  wrapper_signature.append(NEW_CHECK_EXPR_NULL_SIGNATURE_POST);
  return dynamic_cast<DexMethod*>(DexMethod::get_method(wrapper_signature));
}

inline DexMethod* kotlin_jvm_internal_Intrinsics_WrCheckExpression_V1_4(
    const std::string& msg) {
  std::string wrapper_signature;
  wrapper_signature.append(NEW_CHECK_EXPR_NULL_SIGNATURE_V1_4_PRE);
  wrapper_signature.append(msg);
  wrapper_signature.append(NEW_CHECK_EXPR_NULL_SIGNATURE_POST);
  return dynamic_cast<DexMethod*>(DexMethod::get_method(wrapper_signature));
}

// Inserts methods used in Kotlin parameter null assertions
// (checkParameterIsNotNull, checkNotNullParameter, and their wrappers).
inline void get_kotlin_param_null_assertions(UnorderedSet<DexMethodRef*>& out) {
  if (auto* m =
          method::kotlin_jvm_internal_Intrinsics_checkParameterIsNotNull()) {
    out.emplace(m);
  }
  if (auto* m =
          method::kotlin_jvm_internal_Intrinsics_checkNotNullParameter()) {
    out.emplace(m);
  }
  if (auto* m = kotlin_nullcheck_wrapper::
          kotlin_jvm_internal_Intrinsics_WrCheckParameter_V1_3()) {
    out.emplace(m);
  }
  if (auto* m = kotlin_nullcheck_wrapper::
          kotlin_jvm_internal_Intrinsics_WrCheckParameter_V1_4()) {
    out.emplace(m);
  }
}

// Inserts methods used in Kotlin expression null assertions
// (checkExpressionValueIsNotNull, checkNotNullExpressionValue, and their
// wrappers).
inline void get_kotlin_expr_null_assertions(UnorderedSet<DexMethodRef*>& out) {
  if (auto* m = method::
          kotlin_jvm_internal_Intrinsics_checExpressionValueIsNotNull()) {
    out.emplace(m);
  }
  if (auto* m = method::
          kotlin_jvm_internal_Intrinsics_checkNotNullExpressionValue()) {
    out.emplace(m);
  }
  for (auto err : all_NullErrSrc) {
    if (auto* m = kotlin_nullcheck_wrapper::
            kotlin_jvm_internal_Intrinsics_WrCheckExpression_V1_3(
                get_err_msg(err))) {
      out.emplace(m);
    }
    if (auto* m = kotlin_nullcheck_wrapper::
            kotlin_jvm_internal_Intrinsics_WrCheckExpression_V1_4(
                get_err_msg(err))) {
      out.emplace(m);
    }
  }
}

// Inserts methods used in Kotlin not-null assertions
// (Intrinsics.checkNotNull). The Kotlin compiler emits these for:
// - !! operator:
// https://github.com/JetBrains/kotlin/blob/340be3a860a7/compiler/ir/backend.jvm/codegen/src/org/jetbrains/kotlin/backend/jvm/intrinsics/IrIntrinsicMethods.kt#L69
// https://github.com/JetBrains/kotlin/blob/340be3a860a7/compiler/ir/backend.jvm/codegen/src/org/jetbrains/kotlin/backend/jvm/intrinsics/IrCheckNotNull.kt#L35
// - as cast to non-null type:
// https://github.com/JetBrains/kotlin/blob/340be3a860a7/compiler/ir/backend.jvm/lower/src/org/jetbrains/kotlin/backend/jvm/lower/TypeOperatorLowering.kt#L170
// https://github.com/JetBrains/kotlin/blob/340be3a860a7/compiler/ir/backend.jvm/lower/src/org/jetbrains/kotlin/backend/jvm/lower/TypeOperatorLowering.kt#L95
// - IMPLICIT_NOTNULL fallback (seems like a fallback that kotlinc enforces when
// it can't safely invoke checkExpressionValueIsNotNull, should be rare):
// https://github.com/JetBrains/kotlin/blob/340be3a860a7/compiler/ir/backend.jvm/lower/src/org/jetbrains/kotlin/backend/jvm/lower/TypeOperatorLowering.kt#L203
// https://github.com/JetBrains/kotlin/blob/340be3a860a7/compiler/ir/backend.jvm/lower/src/org/jetbrains/kotlin/backend/jvm/lower/TypeOperatorLowering.kt#L214
inline void get_kotlin_notnull_assertions(UnorderedSet<DexMethodRef*>& out) {
  if (auto* m =
          DexMethod::get_method("Lkotlin/jvm/internal/Intrinsics;.checkNotNull:"
                                "(Ljava/lang/Object;)V")) {
    out.emplace(m);
  }
  if (auto* m =
          DexMethod::get_method("Lkotlin/jvm/internal/Intrinsics;.checkNotNull:"
                                "(Ljava/lang/Object;Ljava/lang/String;)V")) {
    out.emplace(m);
  }
}

// This returns methods that are used in Kotlin null assertion.
// These null assertions will take the object that they are checking for
// nullness as first argument and returns void. The value of the object will
// not be null beyond this program point in the execution path.
inline UnorderedSet<DexMethodRef*> get_kotlin_null_assertions() {
  UnorderedSet<DexMethodRef*> methods;
  get_kotlin_param_null_assertions(methods);
  get_kotlin_expr_null_assertions(methods);
  get_kotlin_notnull_assertions(methods);
  return methods;
}

/**
 * Whether the code of `ref` may not be what runs, or may do more than check
 * its first argument: a copy marked `no_optimizations`, an instance method
 * (the summaries below take the checked value to be the first argument), or a
 * wrapper that calls such a copy.
 */
inline bool is_untrusted_null_assertion(
    const DexMethodRef* ref, const UnorderedSet<DexMethodRef*>& assertions) {
  auto is_untrusted_copy = [](const DexMethodRef* method) {
    const auto* def = method->as_def();
    return def != nullptr &&
           (def->rstate.no_optimizations() || !is_static(def));
  };
  if (is_untrusted_copy(ref)) {
    return true;
  }
  const auto* def = ref->as_def();
  const auto* code = def == nullptr ? nullptr : def->get_code();
  if (code == nullptr) {
    return false;
  }
  // A wrapper that RemoveNullcheckStringArg made does what the null check it
  // calls does, so it is no more trusted than that one.
  auto ii = cfg::ConstInstructionIterable(code->cfg());
  return std::any_of(ii.begin(), ii.end(), [&](const auto& mie) {
    return opcode::is_a_method_invoke(mie.insn->opcode()) &&
           assertions.count(mie.insn->get_method()) != 0u &&
           is_untrusted_copy(mie.insn->get_method());
  });
}

/**
 * The null assertions of `get_kotlin_null_assertions` whose code can be
 * trusted to only check the nullity of their first argument.
 */
inline UnorderedSet<DexMethodRef*> get_trusted_kotlin_null_assertions() {
  const auto assertions = get_kotlin_null_assertions();
  UnorderedSet<DexMethodRef*> trusted;
  for (auto* ref : UnorderedIterable(assertions)) {
    if (!is_untrusted_null_assertion(ref, assertions)) {
      trusted.insert(ref);
    }
  }
  return trusted;
}

inline NullErrSrc get_wrapper_code(IROpcode opcode) {
  switch (opcode) {
  case IOPCODE_LOAD_PARAM_OBJECT:
    return NullErrSrc::LOAD_PARAM;
  case OPCODE_AGET_OBJECT:
    return NullErrSrc::ARRAY_ELEMENT;
  case OPCODE_CONST:
  case OPCODE_CONST_STRING:
  case OPCODE_CONST_CLASS:
    return NullErrSrc::CONST;
  case OPCODE_IGET_OBJECT:
    return NullErrSrc::INSTANCE_FIELD;
  case OPCODE_SGET_OBJECT:
    return NullErrSrc::STATIC_FIELD;
  case OPCODE_INVOKE_VIRTUAL:
  case OPCODE_INVOKE_SUPER:
  case OPCODE_INVOKE_DIRECT:
  case OPCODE_INVOKE_STATIC:
  case OPCODE_INVOKE_POLYMORPHIC:
  case OPCODE_INVOKE_CUSTOM:
  case OPCODE_INVOKE_INTERFACE:
    return NullErrSrc::INVOKE_RETURN;
  case OPCODE_CHECK_CAST:
    return NullErrSrc::CHECK_CAST;
  default:
    return NullErrSrc::UNKNOWN_SRC;
  }
}

} // namespace kotlin_nullcheck_wrapper
