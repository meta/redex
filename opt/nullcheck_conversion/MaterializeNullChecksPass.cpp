/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "MaterializeNullChecksPass.h"
#include "ConfigFiles.h"

#include "Debug.h"
#include "DexClass.h"
#include "DexUtil.h"
#include "IRCode.h"
#include "MethodUtil.h"
#include "Walkers.h"

void MaterializeNullChecksPass::run_pass(DexStoresVector& stores,
                                         ConfigFiles&,
                                         PassManager& mgr) {
  const auto& scope = build_class_scope(stores);
  m_getClass_ref =
      DexMethod::get_method("Ljava/lang/Object;.getClass:()Ljava/lang/Class;");

  m_null_check_ref = method::redex_internal_checkObjectNotNull();
  if (m_null_check_ref == nullptr) {
    // Could not find Lredex/$NullCheck;.null_check
    // return.
    return;
  }
  m_stats = walk::parallel::methods<Stats>(
      scope, [&](DexMethod* method) { return rewrite_null_check(method); });
  m_stats.report(mgr);
  mgr.record_materialize_nullchecks();
}

MaterializeNullChecksPass::Stats MaterializeNullChecksPass::rewrite_null_check(
    DexMethod* method) {
  Stats stats;
  IRCode* code = method->get_code();
  if (code == nullptr) {
    return stats;
  }
  always_assert(code->cfg_built());
  auto& cfg = code->cfg();
  for (auto* block : cfg.blocks()) {
    for (auto& mie : InstructionIterable(block)) {
      auto* insn = mie.insn;
      if (!opcode::is_invoke_static(insn->opcode())) {
        continue;
      }
      // Only calls of the intrinsic itself: other static methods of
      // `Lredex/$NullCheck;`, such as one another pass split out of it, keep
      // their own calls.
      if (insn->get_method() != m_null_check_ref) {
        continue;
      }
      // Found invoke-static
      // Lredex/$NullCheck;.null_check:(Ljava/lang/Object;)V.
      stats.num_of_null_check++;
      // Rewrite to invoke-virtual Object;.getClass();

      insn->set_opcode(OPCODE_INVOKE_VIRTUAL);
      insn->set_method(m_getClass_ref);
    }
  }
  return stats;
}

static MaterializeNullChecksPass s_pass;
