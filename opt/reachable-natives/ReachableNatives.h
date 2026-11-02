/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <vector>

#include "DeterministicContainers.h"
#include "IRList.h"
#include "Pass.h"

/*
   This pass will identify native methods which are (un)reachable, ignoring
   "blanket native" proguard rules which keep all native methods and classes
   with native methods, e.g.

   -keepclasseswithmembers class * {
      native <methods>;
    }

    It just runs reachability analysis in the same way as RMU does, but does
    not mark "blanket native" classes/methods as roots.  Classes and methods
    which are kept only due to a "blanket native" rule have been identified
    during proguard processing and stored in RedexContext.

    Results are written to a file, named "redex-reachable-natives.txt" by
    default, and stats on the number of (un)reachable native methods are
    logged.

    Optionally, the pass can also track which libraries are loaded by name.

    Optionally, the pass can also remove classes/fields/methods (except actual
    native methods) only kept because of blanket native keep rules.
*/

class ReachableNativesPass : public Pass {
 public:
  ReachableNativesPass() : Pass("ReachableNativesPass") {}

  redex_properties::PropertyInteractions get_property_interactions()
      const override {
    using namespace redex_properties::interactions;
    using namespace redex_properties::names;
    return {
        {DexLimitsObeyed, Preserves},
        {NoResolvablePureRefs, Preserves},
        {UltralightCodePatterns, Preserves},
        {InitialRenameClass, Preserves},
    };
  }

  void bind_config() override;

  void eval_pass(DexStoresVector&, ConfigFiles&, PassManager&) override;

  void run_pass(DexStoresVector&, ConfigFiles&, PassManager&) override;

 private:
  // Adds the constant library names `caller` passes to load-library entry
  // points to `names`, and returns the instructions that define any library
  // name that is not a constant string.
  std::vector<const IRInstruction*> gather_load_library(
      DexMethod* caller, InsertOnlyConcurrentSet<const DexString*>* names);

  void analyze_final_load_library(
      const DexClasses&,
      ConfigFiles&,
      PassManager&,
      const std::function<bool(DexMethod*)>& reachable_fn);

  std::string m_output_file_name;
  size_t m_run_number = 0;
  size_t m_eval_number = 0;
  bool m_analyze_load_library = false;
  std::string m_live_load_library_file_name;
  std::string m_dead_load_library_file_name;
  std::vector<std::string> m_additional_load_library_names;
  UnorderedSet<DexMethod*> m_load_library_unsafe_methods;
  UnorderedSet<DexMethod*> m_load_library_methods;
  size_t m_pinned_load_library_entry_points = 0;
  bool m_sweep;
  bool m_sweep_native_methods;
};
