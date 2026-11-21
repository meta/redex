/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ResolveMethodRefs.h"

#include "CFGMutation.h"
#include "KotlinLambdaAnalyzer.h"
#include "ScopedCFG.h"
#include "Show.h"
#include "Trace.h"
#include "Walkers.h"

ResolveMethodRefs::ResolveMethodRefs(
    const Scope& scope,
    const type_analyzer::global::GlobalTypeAnalyzer& gta,
    const XStoreRefs& xstores) {
  Timer t("ResolveMethodRefs");
  walk::parallel::methods(scope, [&](DexMethod* method) {
    auto* code = method->get_code();
    if (code == nullptr) {
      return;
    }
    cfg::ScopedCFG cfg(code);
    auto lta = gta.get_replayable_local_analysis(method);
    // Using the result of GTA, check if an interface can be resolved to its
    // implementor at certain callsite.
    analyze_method(method, *lta, xstores);
  });
}

void ResolveMethodRefs::analyze_method(
    DexMethod* method,
    const type_analyzer::local::LocalTypeAnalyzer& lta,
    const XStoreRefs& xstores) {
  IRCode* code = method->get_code();
  auto& cfg = code->cfg();

  cfg::CFGMutation mutation(cfg);
  for (const auto& block : cfg.blocks()) {
    auto env = lta.get_entry_state_at(block);
    if (env.is_bottom()) {
      continue;
    }

    auto ii = InstructionIterable(block);
    for (auto it = ii.begin(); it != ii.end(); it++) {
      auto* insn = it->insn;
      lta.analyze_instruction(insn, &env);
      // Since we only consider kotlin non capturing lambda, which originally
      // derived from an interface.
      if (insn->opcode() != OPCODE_INVOKE_INTERFACE) {
        continue;
      }
      auto* insn_method = insn->get_method();
      auto* intf = resolve_method_deprecated(insn_method,
                                             opcode_to_search(insn), method);
      if (intf == nullptr) {
        continue;
      }
      // Step1. Use GTA result to resolve the interface(i.e. the first param of
      // invoke-interface),  to its implementation which is actually called at
      // this callsite.
      auto type_domain = env.get(insn->src(0));
      auto analysis_cls = type_domain.get_dex_cls();
      if (!analysis_cls) {
        continue;
      }

      auto ms = opcode_to_search(insn);
      if (ms == MethodSearch::Interface && !is_interface(*analysis_cls)) {
        ms = MethodSearch::Virtual;
      }
      DexMethod* impl = resolve_method_deprecated(
          *analysis_cls, intf->get_name(), intf->get_proto(), ms);
      // Step2.  if this calle can be resolved, replace invoke-interface to
      // invoke-virtual.
      if ((impl == nullptr) || xstores.cross_store_ref(method, impl)) {
        continue;
      }

      // We first focus on Kotlin lambda code.
      if (auto analyzer = KotlinLambdaAnalyzer::for_class(*analysis_cls);
          !analyzer || !analyzer->is_non_capturing()) {
        continue;
      }

      TRACE(TYPE, 5, "Intf %s is resolved to: %s \n", SHOW(intf), SHOW(impl));

      // resolve the interface to its implementor.
      auto cfg_it = block->to_cfg_instruction_iterator(it);
      mutation.insert_before(cfg_it,
                             make_check_cast(impl->get_class(), insn->src(0)));

      // rewrite invoke-interface to invoke-virtual
      insn->set_method(impl);
      insn->set_opcode(OPCODE_INVOKE_VIRTUAL);

      m_num_resolved_kt_non_capturing_lambda_calls++;
    }
  }
  mutation.flush();
  cfg.recompute_registers_size();
}

void ResolveMethodRefs::report(PassManager& mgr) const {
  mgr.incr_metric("m_num_resolved_kt_non_capturing_lambda_calls",
                  m_num_resolved_kt_non_capturing_lambda_calls);

  TRACE(TYPE, 5, "num of kotlin non capturing lambda is %zu \n",
        m_num_resolved_kt_non_capturing_lambda_calls);
}
