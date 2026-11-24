/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "InsertRemarksForTracing.h"

#include <atomic>

#include "ControlFlow.h"
#include "DexClass.h"
#include "DexStore.h"
#include "DexUtil.h"
#include "IRCode.h"
#include "IRList.h"
#include "MethodUtil.h"
#include "PassManager.h"
#include "RedexContext.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "Walkers.h"

void InsertRemarksForTracingPass::run_pass(DexStoresVector& stores,
                                           ConfigFiles& /* conf */,
                                           PassManager& mgr) {
  // Gated on the global insert_remarks flag: remarks are only created (and, in
  // turn, counted per pass) when this validation flag is set.
  if (!g_redex->insert_remarks) {
    return;
  }

  auto scope = build_class_scope(stores);

  // Interned once; every remark this pass stamps records it as the producer.
  const auto* producer = DexString::make_string("InsertRemarksForTracingPass");

  std::atomic<size_t> inserted{0};
  walk::parallel::methods(scope, [&](DexMethod* method) {
    auto* code = method->get_code();
    // Respect the no-optimizations blocklist (build-time bytecode may not match
    // runtime for such methods).
    if (!method::is_optimizable(method)) {
      return;
    }
    // val_str = the deobfuscated, fully-qualified method name (interned). It
    // rides with the code, so after inlining a remark still names its origin
    // method.
    const auto* method_name = DexString::make_string(show_deobfuscated(method));
    // PassManager guarantees the CFG is built for every method in scope.
    auto& cfg = code->cfg();
    size_t local = 0;
    for (auto* block : cfg.blocks()) {
      auto insert_point = source_blocks::find_first_block_insert_point(block);
      // val_int = the block id: deterministic (reproducible builds) and
      // distinct per block, so tests can verify deep_copy carries the exact
      // payload.
      block->insert_before(
          insert_point,
          std::make_unique<Remark>(producer, method_name,
                                   static_cast<int64_t>(block->id())));
      ++local;
    }
    inserted.fetch_add(local, std::memory_order_relaxed);
  });

  mgr.set_metric("inserted_remarks", inserted.load());
}

static InsertRemarksForTracingPass s_pass;
