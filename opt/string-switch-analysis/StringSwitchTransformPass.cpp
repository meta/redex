/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "StringSwitchTransformPass.h"

#include <algorithm>
#include <fstream>
#include <iomanip>
#include <sstream>
#include <string>
#include <vector>

#include "ConfigFiles.h"
#include "ConstantEnvironment.h"
#include "ConstantPropagationAnalysis.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "DexClass.h"
#include "DexStructure.h"
#include "DexUtil.h"
#include "Histogram.h"
#include "IRCode.h"
#include "InitClassesWithSideEffects.h"
#include "MethodUtil.h"
#include "PassManager.h"
#include "Purity.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "StringSwitchFinder.h"
#include "StringSwitchTransform.h"
#include "StringTreeMapTransform.h"
#include "Trace.h"
#include "Walkers.h"

namespace {

namespace cp = constant_propagation;

// The string switches found in one method. PassManager keeps the editable CFGs
// built for the whole pass, so the block pointers in
// StringSwitchInfo stay valid until the pass returns -- and these are the real
// details future transforms will act on, not just rendered text.
struct MethodResult {
  DexMethod* method;
  std::vector<StringSwitchInfo> switches;
};

struct CombineMethodResults {
  void operator()(const std::vector<MethodResult>& addend,
                  std::vector<MethodResult>* accumulator) const {
    accumulator->insert(accumulator->end(), addend.begin(), addend.end());
  }
};

const char* form_name(StringSwitchInfo::Form form) {
  switch (form) {
  case StringSwitchInfo::Form::HASH_SWITCH:
    return "HASH_SWITCH";
  case StringSwitchInfo::Form::HASH_SWITCH_DIRECT:
    return "HASH_SWITCH_DIRECT";
  case StringSwitchInfo::Form::EQUALS_CHAIN:
    return "EQUALS_CHAIN";
  }
  not_reached();
}

void write_block(std::ostream& os, cfg::Block* block) {
  if (block == nullptr) {
    return;
  }
  for (auto& mie : InstructionIterable(block)) {
    os << "  OPCODE: " << show(mie.insn) << "\n";
  }
}

void render_switch(std::ostream& os, const StringSwitchInfo& info) {
  // A recovered switch always has both an origin instruction and block.
  always_assert(info.origin_insn != nullptr && info.origin_block != nullptr);
  // Hotness summary. When the origin is cold there is nothing to reorder, so
  // report N/A. Otherwise report the ratio of hot case destinations to total
  // cases (the default case is counted in both); if exactly one case is hot,
  // flag it as a SINGLE CASE (a dominant-case dispatch).
  if (!source_blocks::is_hot(info.origin_block)) {
    os << "HOTNESS: N/A\n";
  } else {
    size_t total_cases = info.key_to_case.size();
    size_t hot_cases = 0;
    for (const auto& [key, block] : info.key_to_case) {
      if (block != nullptr && source_blocks::is_hot(block)) {
        ++hot_cases;
      }
    }
    double ratio =
        static_cast<double>(hot_cases) / static_cast<double>(total_cases);
    std::ostringstream ratio_ss;
    ratio_ss << std::fixed << std::setprecision(1) << ratio;
    os << "HOTNESS: " << hot_cases << "/" << total_cases << " ("
       << ratio_ss.str() << ")";
    if (hot_cases == 1) {
      os << " SINGLE CASE";
    }
    os << "\n";
  }
  os << "FORM: " << form_name(info.form) << "\n";
  os << "ORIGIN: " << show(info.origin_insn) << "\n";
  os << "CASES: " << info.key_to_case.size() << "\n";
  os << "=== BEGIN ===\n";

  auto default_block = info.default_case();
  bool default_hot = default_block && *default_block != nullptr &&
                     source_blocks::is_hot(*default_block);
  os << "DEFAULT HOT: " << (default_hot ? "true" : "false") << "\n";
  if (default_block) {
    write_block(os, *default_block);
  }

  for (const auto& [key, block] : info.key_to_case) {
    if (std::holds_alternative<StringSwitchInfo::DefaultCase>(key)) {
      continue;
    }
    const auto* str = std::get<const DexString*>(key);
    bool block_hot = block != nullptr && source_blocks::is_hot(block);
    os << "STRING \"" << str->str()
       << "\" HOT: " << (block_hot ? "true" : "false") << "\n";
    write_block(os, block);
  }
  os << "=== END ===\n";
}

} // namespace

void StringSwitchTransformPass::bind_config() {
  bind("emit_analysis", m_emit_analysis, m_emit_analysis,
       "Prints out a metafile showing all string switches found.");
  bind("min_cases", m_min_cases, m_min_cases,
       "For use in StringTreeMapTransform, number of case keys which are "
       "eligible for transformation.");
  bind("string_tree_lookup_method", m_string_tree_lookup_method,
       m_string_tree_lookup_method,
       "For use in StringTreeMapTransform, search method to invoke on encoded "
       "data.");
  bind("const_string_max_size", m_const_string_max_size,
       m_const_string_max_size,
       "For use in StringTreeMapTransform, a maximum size for encoded data to "
       "obey (beyond this size will be considered ineligible).");
}

std::vector<std::unique_ptr<StringSwitchTransform>>
StringSwitchTransformPass::build_transforms() const {
  std::vector<std::unique_ptr<StringSwitchTransform>> transforms;
  // Registered in priority order; each transform self-gates in evaluate(). When
  // none are configured the pass performs analysis only.
  //
  // StringTreeMap re-encoding (SIZE tier): enabled only when a lookup method is
  // configured AND resolves in the app -- otherwise switches are left as-is.
  if (!m_string_tree_lookup_method.empty()) {
    auto* lookup = DexMethod::get_method(m_string_tree_lookup_method);
    if (lookup != nullptr) {
      transforms.push_back(std::make_unique<StringTreeMapTransform>(
          lookup, m_min_cases, m_const_string_max_size));
    }
  }
  return transforms;
}

void StringSwitchTransformPass::eval_pass(DexStoresVector&,
                                          ConfigFiles&,
                                          PassManager& mgr) {
  // Reserve the dex refs the configured transforms may introduce, so earlier
  // passes leave room. Released at the start of run_pass.
  RefBudget budget;
  for (const auto& transform : build_transforms()) {
    auto refs = transform->reserve_refs();
    budget.frefs += refs.frefs;
    budget.mrefs += refs.mrefs;
    budget.trefs += refs.trefs;
  }
  if (budget.frefs != 0 || budget.mrefs != 0 || budget.trefs != 0) {
    m_reserved_refs_handle = mgr.reserve_refs(
        name(), ReserveRefsInfo(budget.frefs, budget.trefs, budget.mrefs));
  }
}

void StringSwitchTransformPass::run_pass(DexStoresVector& stores,
                                         ConfigFiles& conf,
                                         PassManager& mgr) {
  if (m_reserved_refs_handle) {
    mgr.release_reserved_refs(*m_reserved_refs_handle);
    m_reserved_refs_handle = std::nullopt;
  }

  auto scope = build_class_scope(stores);

  // Phase A: recover string switches and emit the analysis report + histogram.
  // Read-only and entirely gated on `emit_analysis` -- when disabled we skip
  // the (redundant) recovery scan altogether. Runs to completion before any
  // rewrite, so the recovered block pointers stay valid through rendering.
  if (m_emit_analysis) {
    auto all_results = walk::parallel::methods<std::vector<MethodResult>,
                                               CombineMethodResults>(
        scope, [&](DexMethod* method, std::vector<MethodResult>* acc) {
          auto* code = method->get_code();
          if (code == nullptr) {
            return;
          }
          auto& cfg = code->cfg();
          // Cheap linear pre-filter: a string switch needs both a
          // String.hashCode() and a String.equals() call. Skip the expensive
          // fixpoint iterator and finder for the vast majority of methods that
          // have neither pair.
          if (!may_contain_string_switch(cfg)) {
            TRACE(STRSW, 9,
                  "[StringSwitchTransformPass] not a candidate %s\n%s",
                  SHOW(method), SHOW(cfg));
            return;
          }
          TRACE(STRSW, 5, "[StringSwitchTransformPass] candidate %s\n%s",
                SHOW(method), SHOW(cfg));
          auto fixpoint =
              std::make_shared<cp::intraprocedural::FixpointIterator>(
                  cfg, StringSwitchFinder::Analyzer());
          fixpoint->run(ConstantEnvironment());

          auto switches = find_string_switches(cfg, fixpoint);
          if (!switches.empty()) {
            acc->push_back({method, std::move(switches)});
          }
        });

    std::sort(all_results.begin(), all_results.end(),
              [](const MethodResult& a, const MethodResult& b) {
                return compare_dexmethods(a.method, b.method);
              });

    // The case count of each switch (including its default), for the histogram.
    std::vector<size_t> case_counts;
    std::ofstream ofs(conf.metafile("string_switch_analysis.txt"));
    for (const auto& result : all_results) {
      ofs << "Method " << show(result.method) << "\n";
      for (const auto& info : result.switches) {
        case_counts.push_back(info.key_to_case.size());
        render_switch(ofs, info);
      }
    }

    mgr.set_metric("num_string_switches", case_counts.size());
    TRACE(STRSW, 1,
          "[StringSwitchTransformPass] found %zu string switch(es) in %zu "
          "method(s)\n%s",
          case_counts.size(), all_results.size(),
          histogram::render_histogram(
              case_counts, "Case-count distribution across string switches", 30)
              .c_str());
  }

  // Phase B: apply transforms (mutates CFGs). No-op when none are registered.
  auto transforms = build_transforms();
  if (transforms.empty()) {
    return;
  }
  // The inputs LocalDce needs are method-independent, so build them once and
  // share them across every method's driver run: the side-effect-free method
  // set (notably String.hashCode/equals) and the (empty-scope) init-class info.
  auto pure_methods = get_pure_methods();
  init_classes::InitClassesWithSideEffects init_classes(
      /*scope=*/{}, /*create_init_class_insns=*/false);
  auto stats = walk::parallel::methods<DriverStats, CombineDriverStats>(
      scope, [&](DexMethod* method, DriverStats* acc) {
        if (!method::is_optimizable(method)) {
          return;
        }
        auto* code = method->get_code();
        auto& cfg = code->cfg();
        if (!may_contain_string_switch(cfg)) {
          return;
        }
        run_string_switch_transforms(method, cfg, transforms, pure_methods,
                                     init_classes, acc);
      });
  for (const auto& [transform_name, count] : stats.applied) {
    mgr.set_metric("applied." + transform_name, count);
  }
}

static StringSwitchTransformPass s_pass;
