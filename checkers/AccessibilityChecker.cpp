/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "AccessibilityChecker.h"

#include "Debug.h"
#include "DexClass.h"
#include "DexUtil.h"
#include "IRInstruction.h"
#include "Show.h"
#include "TypeUtil.h"
#include "Walkers.h"

namespace redex_properties {

void AccessibilityChecker::run_checker(DexStoresVector& stores,
                                       ConfigFiles& /* conf */,
                                       PassManager& /*mgr*/,
                                       bool established) {
  if (established) {
    return;
  }
  const auto& scope = build_class_scope(stores);
  walk::parallel::opcodes(scope, [&](DexMethod* method, IRInstruction* insn) {
    std::optional<std::string> fail_str;
    if (insn->has_field()) {
      auto* f = insn->get_field();
      if (!f->is_external() && f->is_def() &&
          !type::can_access(method, f->as_def())) {
        fail_str = vshow(method) + " -> " + vshow(f->as_def());
      }
    }

    if (insn->has_method()) {
      auto* m = insn->get_method();
      if (!m->is_external() && m->is_def() &&
          !type::can_access(method, m->as_def())) {
        fail_str = vshow(method) + " -> " + vshow(m->as_def());
      }
    }

    if (insn->has_type()) {
      // The device checks access to an array's element class.
      auto* t = type_class(type::get_element_type_if_array(insn->get_type()));
      if (t != nullptr && !t->is_external() && !type::can_access(method, t)) {
        fail_str = vshow(method) + " -> " + vshow(t);
      }
    }

    always_assert_log(
        !fail_str, "%s\n%s", fail_str->c_str(), SHOW(method->get_code()));
  });
}

} // namespace redex_properties

namespace {
static redex_properties::AccessibilityChecker s_checker;
} // namespace
