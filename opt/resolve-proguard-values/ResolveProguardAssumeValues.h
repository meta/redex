/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once
#include "ControlFlow.h"
#include "Pass.h"
#include "PassManager.h"

class ResolveProguardAssumeValuesPass : public Pass {
  struct Stats {
    size_t method_return_values_changed{0};
    size_t field_values_changed{0};

    Stats& operator+=(const Stats& that) {
      method_return_values_changed += that.method_return_values_changed;
      field_values_changed += that.field_values_changed;
      return *this;
    }
    void report(PassManager& mgr) const {
      mgr.incr_metric("method_return_values_changed",
                      method_return_values_changed);
      mgr.incr_metric("field_values_changed", field_values_changed);
    }
  };

 public:
  // This pass changes the methods that has -assumenosideeffects with values
  // into that returns specified values - as in the proguard rule.
  //
  // We consider static methods and methods that are not external.
  //
  // Example:
  // If we have a proguard rule that specifies getASSERTIONS_ENABLED() does not
  // have side-effects and always return false (for example in release build).
  // -assumenosideeffects class kotlinx.coroutines.DebugKt {
  //     boolean getASSERTIONS_ENABLED() return false;
  //  }
  //  This pass will convert call to getASSERTIONS_ENABLED() as follows:
  //    INVOKE_STATIC Lkotlinx/coroutines/DebugKt;.getASSERTIONS_ENABLED:()Z
  //    MOVE_RESULT v0
  //  Into:
  //    CONST v0, 0
  //
  // TODO: Extend this (with Proguard parsing) to support the following:
  //  We currently support boolean return values only.  This could be extended.
  //  We also does not support setting field values like
  //  -assumenosideeffects class
  //  kotlinx.coroutines.internal.MainDispatcherLoader {
  //      boolean FAST_SERVICE_LOADER_ENABLED return false;
  //  }
  //
  ResolveProguardAssumeValuesPass() : Pass("ResolveProguardAssumeValuesPass") {}

  redex_properties::PropertyInteractions get_property_interactions()
      const override {
    using namespace redex_properties::interactions;
    using namespace redex_properties::names;
    return {
        {NoResolvablePureRefs, Preserves},
    };
  }

  static ResolveProguardAssumeValuesPass::Stats process_for_code(
      cfg::ControlFlowGraph& cfg);
  void run_pass(DexStoresVector& stores,
                ConfigFiles&,
                PassManager& mgr) override;
};
