/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "DexClass.h"
#include "Pass.h"
#include "PassManager.h"
#include "Trace.h"

class MaterializeNullChecksPass : public Pass {
 public:
  struct Stats {
    size_t num_of_obj_getClass{0};
    size_t num_of_null_check{0};
    Stats& operator+=(const Stats& that) {
      num_of_obj_getClass += that.num_of_obj_getClass;
      num_of_null_check += that.num_of_null_check;
      return *this;
    }
    /// Updates metrics tracked by \p mgr corresponding to these statistics.
    void report(PassManager& mgr) const {
      mgr.incr_metric("num_of_obj_getClass", num_of_obj_getClass);
      mgr.incr_metric("num_of_null_check", num_of_null_check);
      TRACE(NCI, 1, "Number of object getClass = %zu\n", num_of_obj_getClass);
      TRACE(NCI, 1, "Number of rewriten null_check = %zu\n", num_of_null_check);
    }
  };

  explicit MaterializeNullChecksPass() : Pass("MaterializeNullChecksPass") {}

  redex_properties::PropertyInteractions get_property_interactions()
      const override {
    using namespace redex_properties::interactions;
    using namespace redex_properties::names;
    return {
        {DexLimitsObeyed, Preserves},
        {InitialRenameClass, Preserves},
        {NoInitClassInstructions, Preserves},
        {NoResolvablePureRefs, Preserves},
        {NoUnreachableInstructions, Preserves},
        {RenameClass, Preserves},
        {SpuriousGetClassCallsInterned, Requires},
    };
  }

  std::string get_config_doc() override {
    return trim(R"(
Convert `Lredex/$NullCheck;.null_check:(Ljava/lang/Object;)V` to
`java/lang/Object.getClass:()Ljava/lang/Class;`. Check `IntrinsifyNullChecksPass`
for details.
    )");
  }

  void run_pass(DexStoresVector&, ConfigFiles&, PassManager&) override;
  Stats rewrite_null_check(DexMethod* method);

 private:
  Stats m_stats;
  DexMethodRef* m_getClass_ref;
  DexMethod* m_null_check_ref;
};
