/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "KotlinNullCheckMethods.h"
#include "Pass.h"

namespace cfg {
class ControlFlowGraph;
} // namespace cfg

/**
 * Kotlin has null safety checks which adds runtime assertions. These assertions
 * takes the object and the identifier name which is holding the object
 * (parameter or field) as parameters.
 *
 * This pass modifies calls to these assertions (checkParameterIsNotNull and
 * checkExpressionValueIsNotNull) to a generated wrapper method calls such that
 * it reduces the string usage and code size. For example,
 * checkParameterIsNotNull like below will change from:
 *
 * (invoke-static (v0 v1)
 * "Lkotlin/jvm/internal/Intrinsics;.checkParameterIsNotNull:(Ljava/lang/Object;Ljava/lang/String;)V")
 * to:
 * (invoke-static (v0, v1)
 * "Lkotlin/jvm/internal/Intrinsics;.$WrCheckParameter(Ljava/lang/Object;I)V")
 *
 * And, this pass will generate wrapper function called $WrCheckParameter and
 * $WrCheckExpression in the host class. $WrcheckParameter will in turn call
 * checkParameterIsNotNull with a string converted from index or
 * $WrCheckExpression will call checkExpressionValueIsNotNull with an empty
 * string. Inliner will inline checkParameterIsNotNull into the wrapper
 * function.
 *
 */
class RemoveNullcheckStringArg : public Pass {
 public:
  // Records the wrapper method for assertions if the
  // wrapper method takes the index of the parameter as an argument. In this
  // case, we will construct a string from the index with additional information
  // as part of the wrapper method and print that as part of the trace.
  using TransferMapForParam = UnorderedMap<DexMethodRef*, DexMethod*>;

  // Records the wrapper method for assertions with a simple message to indicate
  // where the error comes from. In this case, we will construct a string based
  // on error src as part of the wrapper method and print that as part of the
  // trace.
  using TransferMapForExpr =
      UnorderedMap<DexMethodRef*,
                   UnorderedMap<const kotlin_nullcheck_wrapper::NullErrSrc,
                                DexMethod*,
                                std::hash<int>>>;
  using NewMethodSet = UnorderedSet<DexMethod*>;
  struct Stats {
    // The number of null-check which are optmized by this pass.
    size_t null_check_insns_changed{0};
    // The number of null-check which are not optmized by this pass.
    size_t null_check_insns_unchanged{0};
    // The number of null-check which are opitmized, but the object src is not
    // analyzed.
    size_t null_check_src_unknown{0};
    Stats& operator+=(const Stats& that) {
      null_check_insns_changed += that.null_check_insns_changed;
      null_check_insns_unchanged += that.null_check_insns_unchanged;
      null_check_src_unknown += that.null_check_src_unknown;
      return *this;
    }
    /// Updates metrics tracked by \p mgr corresponding to these statistics.
    /// Simultaneously prints the statistics via TRACE.
    void report(PassManager& mgr) const;
  };

  RemoveNullcheckStringArg() : Pass("RemoveNullcheckStringArgPass") {}

  redex_properties::PropertyInteractions get_property_interactions()
      const override {
    using namespace redex_properties::interactions;
    using namespace redex_properties::names;
    return {
        {NoResolvablePureRefs, Preserves},
        {UltralightCodePatterns, Preserves},
    };
  }

  bool setup(TransferMapForParam& transfer_map_param,
             TransferMapForExpr& transfer_map_expr,
             NewMethodSet& new_methods);
  void run_pass(DexStoresVector&, ConfigFiles&, PassManager&) override;
  RemoveNullcheckStringArg::Stats change_in_cfg(
      cfg::ControlFlowGraph& cfg,
      const TransferMapForParam& transfer_map_param,
      const TransferMapForExpr& transfer_map_expr,
      bool is_static);

 private:
  /* If the \p wrapper_signature is already present or if the function being
   * wrapped does not exist or if creation of new method fails, return nullptr.
   * Otherwise create a method in the same class as in \p
   * builtin_signature with a new name \p wrapper_name. In this method, \p
   * builtin methoded is called with the given throw exception message \p msg.*/
  DexMethod* get_wrapper_method_with_msg(const char* signature,
                                         const char* name,
                                         const std::string& msg,
                                         DexMethodRef* builtin);
  /* If the \p wrapper_signature, that also takes int index, is already present
   * or if the function being wrapped does not exist or if creation of new
   * method fails, return nullptr. Otherwise create a method in the same class
   * as in \p builtin_signature with a new name \p wrapper_name. */
  DexMethod* get_wrapper_method_with_int_index(const char* wrapper_signature,
                                               const char* wrapper_name,
                                               DexMethodRef* builtin);
};
