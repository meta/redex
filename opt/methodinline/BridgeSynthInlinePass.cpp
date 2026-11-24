/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "BridgeSynthInlinePass.h"

#include <atomic>

#include "BridgeSynthInlineInternal.h"
#include "CFGMutation.h"
#include "ConfigFiles.h"
#include "ControlFlow.h"
#include "DexClass.h"
#include "DexUtil.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "MethodInliner.h"
#include "MethodUtil.h"
#include "PassManager.h"
#include "Resolver.h"
#include "Show.h"
#include "Trace.h"
#include "Walkers.h"

namespace {

bool is_bridgelike_synthetic(const DexMethod* method) {
  return method->is_virtual() &&
         (is_bridge(method) ||
          (is_synthetic(method) && !method::is_constructor(method)));
}

DexMethodRef* invoke_super_abstract_target(const IRInstruction* insn,
                                           const DexMethod* caller) {
  if (insn->opcode() != OPCODE_INVOKE_SUPER) {
    return nullptr;
  }
  auto* resolved =
      resolve_method(insn->get_method(), MethodSearch::Super, caller);
  if (resolved == nullptr || !is_abstract(resolved)) {
    return nullptr;
  }
  return insn->get_method();
}

} // namespace

namespace bridge_synth_inline_internal {

bool rewrite_bridge_with_abstract_super_target(DexMethod* method) {
  if (!is_bridgelike_synthetic(method)) {
    return false;
  }
  if (!method::is_optimizable(method)) {
    return false;
  }
  auto* code = method->get_code();

  auto& cfg = code->cfg();
  cfg::CFGMutation mutation(cfg);
  bool rewrote_any = false;
  auto iterable = cfg::InstructionIterable(cfg);
  for (auto it = iterable.begin(); it != iterable.end(); ++it) {
    auto* offending_ref = invoke_super_abstract_target(it->insn, method);
    if (offending_ref == nullptr) {
      continue;
    }
    auto exception_reg = cfg.allocate_temp();
    auto message_reg = cfg.allocate_temp();
    std::vector<IRInstruction*> throw_insns;
    create_abstract_method_error_block(
        DexString::make_string("redex-synthesized: " + show(offending_ref)),
        throw_insns,
        exception_reg,
        message_reg);
    mutation.replace(it, std::move(throw_insns));
    rewrote_any = true;
    TRACE(BRIDGE, 2,
          "[BridgeSynthInline] rewrote invoke-super in %s; abstract target %s",
          SHOW(method), SHOW(offending_ref));
  }
  mutation.flush();
  return rewrote_any;
}

} // namespace bridge_synth_inline_internal

namespace {

size_t rewrite_bridges_with_abstract_super_targets(const Scope& scope,
                                                   PassManager& mgr) {
  TRACE(BRIDGE, 1,
        "[BridgeSynthInline] scanning %zu classes for synthetic bridges "
        "containing invoke-super to abstract...",
        scope.size());
  std::atomic<size_t> rewritten{0};
  walk::parallel::methods(scope, [&](DexMethod* method) {
    if (bridge_synth_inline_internal::rewrite_bridge_with_abstract_super_target(
            method)) {
      rewritten.fetch_add(1, std::memory_order_relaxed);
    }
  });
  auto total = rewritten.load();
  TRACE(BRIDGE, 1,
        "[BridgeSynthInline] done; rewrote %zu bridges to throw "
        "AbstractMethodError",
        total);
  mgr.set_metric("num_bridges_with_abstract_super_rewritten", total);
  return total;
}

} // namespace

void BridgeSynthInlinePass::run_pass(DexStoresVector& stores,
                                     ConfigFiles& conf,
                                     PassManager& mgr) {
  Scope scope = build_class_scope(stores);
  rewrite_bridges_with_abstract_super_targets(scope, mgr);

  inliner::run_inliner(stores,
                       mgr,
                       conf,
                       DEFAULT_COST_CONFIG,
                       HotColdInliningBehavior::None,
                       /* partial_hot_hot */ false,
                       /* intra_dex */ false,
                       /* baseline_profile_guided */ false,
                       /* inline_for_speed */ nullptr,
                       /* inline_bridge_synth_only */ true);
}

static BridgeSynthInlinePass s_pass;
