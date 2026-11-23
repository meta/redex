/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "GlobalTypeAnalysisPass.h"

#include "ConfigFiles.h"
#include "DexUtil.h"
#include "GlobalTypeAnalyzer.h"
#include "KotlinNullCheckMethods.h"
#include "OptionalIO.h"
#include "PassManager.h"
#include "ResolveMethodRefs.h"
#include "Show.h"
#include "Trace.h"
#include "TypeAnalysisTransform.h"
#include "TypeInference.h"
#include "Walkers.h"

using namespace type_analyzer;

namespace {

bool are_different(const std::optional<const DexType*>& gtype,
                   const std::optional<const DexType*>& ltype) {
  if (!gtype) {
    return false;
  }
  return !ltype || *gtype != *ltype;
}

bool trace_results_if_different(const std::string& prefix,
                                const DexTypeDomain& gdomain,
                                const std::optional<const DexType*>& ltype,
                                std::ostringstream& out) {
  if (gdomain.is_top() || gdomain.is_bottom()) {
    return false;
  }
  const auto& gtype = gdomain.get_single_domain().get_dex_type();
  if (!are_different(gtype, ltype)) {
    return false;
  }
  out << prefix << " global:" << gtype;
  out << " local:" << ltype << '\n';
  return true;
}

void trace_analysis_diff(DexMethod* method,
                         const type_analyzer::local::LocalTypeAnalyzer& lta) {
  IRCode* code = method->get_code();
  auto& cfg = code->cfg();
  type_inference::TypeInference type_inference(cfg);
  type_inference.run(method);
  auto lenvs = type_inference.get_type_environments();
  std::ostringstream out;
  size_t param_idx = 0;
  bool found_improvement = false;
  UnorderedSet<DexMethodRef*> callees;
  UnorderedSet<DexFieldRef*> fields;

  for (const auto& block : cfg.blocks()) {
    auto genv = lta.get_entry_state_at(block);
    if (genv.is_bottom()) {
      continue;
    }
    for (auto& mie : InstructionIterable(block)) {
      auto* insn = mie.insn;
      lta.analyze_instruction(insn, &genv);

      if (insn->opcode() == IOPCODE_LOAD_PARAM_OBJECT) {
        auto gparam = genv.get(insn->dest());
        auto lparam = lenvs.at(insn).get_dex_type(insn->dest());
        auto prefix = "param " + std::to_string(param_idx++);
        found_improvement =
            trace_results_if_different(prefix, gparam, lparam, out);
      } else if (insn->opcode() == OPCODE_IGET_OBJECT ||
                 insn->opcode() == OPCODE_SGET_OBJECT) {
        auto gparam = genv.get(RESULT_REGISTER);
        auto it = block->to_cfg_instruction_iterator(mie);
        auto move_res = cfg.move_result_of(it);
        auto* field = insn->get_field();
        if (fields.count(field) != 0u) {
          continue;
        }
        fields.insert(field);
        auto lparam = lenvs.at(move_res->insn).get_dex_type(RESULT_REGISTER);
        auto prefix = "field " + show(insn);
        found_improvement =
            trace_results_if_different(prefix, gparam, lparam, out);
      } else if (opcode::is_a_method_invoke(insn->opcode())) {
        auto gparam = genv.get(RESULT_REGISTER);
        auto it = block->to_cfg_instruction_iterator(mie);
        auto* callee = insn->get_method();
        it.move_next_in_block();
        if ((lenvs.count(it->insn) == 0u) || (callees.count(callee) != 0u)) {
          continue;
        }
        callees.insert(callee);
        auto lparam = lenvs.at(it->insn).get_dex_type(RESULT_REGISTER);
        auto prefix = "return " + show(insn);
        found_improvement =
            trace_results_if_different(prefix, gparam, lparam, out);
      }
    }
  }

  if (found_improvement) {
    TRACE(TYPE_TRANSFORM,
          5,
          "%s%s\n%s",
          out.str().c_str(),
          SHOW(method),
          SHOW(cfg));
  }
}

} // namespace

void GlobalTypeAnalysisPass::run_pass(DexStoresVector& stores,
                                      ConfigFiles& config,
                                      PassManager& mgr) {
  if (m_config.insert_runtime_asserts) {
    m_config.runtime_assert =
        RuntimeAssertTransform::Config(config.get_proguard_map());
  }

  type_analyzer::Transform::NullAssertionSet null_assertion_set =
      kotlin_nullcheck_wrapper::get_kotlin_null_assertions();
  null_assertion_set.insert(method::redex_internal_checkObjectNotNull());
  Scope scope = build_class_scope(stores);
  XStoreRefs xstores(stores, config.normal_primary_dex());
  global::GlobalTypeAnalysis analysis(m_config.max_global_analysis_iteration,
                                      m_config.use_multiple_callee_callgraph);
  auto gta = analysis.analyze(scope);
  optimize(scope, xstores, *gta, null_assertion_set, mgr);
  m_result = std::move(gta);

  mgr.set_metric("global_analysis_iterations",
                 analysis.get_global_analysis_iterations());
}

void GlobalTypeAnalysisPass::optimize(
    const Scope& scope,
    const XStoreRefs& xstores,
    const type_analyzer::global::GlobalTypeAnalyzer& gta,
    const type_analyzer::Transform::NullAssertionSet& null_assertion_set,
    PassManager& mgr) {
  auto stats = walk::parallel::methods<Stats>(scope, [&](DexMethod* method) {
    if (method->get_code() == nullptr) {
      return Stats();
    }
    auto lta = gta.get_replayable_local_analysis(method);

    if (m_config.trace_global_local_diff) {
      trace_analysis_diff(method, *lta);
    }

    if (m_config.insert_runtime_asserts) {
      RuntimeAssertTransform rat(m_config.runtime_assert);
      Stats ra_stats;
      ra_stats.assert_stats =
          rat.apply(*lta, gta.get_whole_program_state(), method);
      return ra_stats;
    }

    Transform tf(m_config.transform);
    Stats tr_stats;
    tr_stats.transform_stats = tf.apply(*lta, gta.get_whole_program_state(),
                                        method, null_assertion_set);
    if (!tr_stats.transform_stats.is_empty()) {
      TRACE(TYPE,
            9,
            "changes applied to %s\n%s",
            SHOW(method),
            SHOW(method->get_code()->cfg()));
    }
    return tr_stats;
  });

  stats.report(mgr);

  if (m_config.resolve_method_refs) {
    ResolveMethodRefs intf_trans(scope, gta, xstores);
    intf_trans.report(mgr);
  }
}

static GlobalTypeAnalysisPass s_pass;
