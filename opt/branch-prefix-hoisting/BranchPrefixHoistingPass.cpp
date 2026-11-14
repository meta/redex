/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "BranchPrefixHoistingPass.h"

#include "AtomicStatCounter.h"

#include "BranchPrefixHoisting.h"
#include "DexUtil.h"
#include "PassManager.h"
#include "Show.h"
#include "Trace.h"
#include "Walkers.h"

/**
 * This pass eliminates sibling branches that begin with identical instructions,
 * (aka prefix hoisting).
 * example code pattern
 * if (condition) {
 *   insn_1;
 *   insn_2;
 *   insn_3;
 * } else {
 *   insn_1;
 *   insn_2;
 *   insn_4;
 * }
 * will be optimized into
 * insn_1;
 * insn_2;
 * if (condition) {
 *   insn_3;
 * } else {
 *   insn_4;
 * }
 * given that the hoisted instructions doesn't have a side effect on the branch
 * condition.
 *
 * We leave debug and position info in the original block. This is required for
 * correctness of the suffix.
 *
 * We hoist source blocks. The reasoning for that is tracking of exceptional
 * flow.
 *
 * Note: if an instruction gets hoisted may throw, the line numbers in stack
 * trace may be pointing to before the branch. The hoisted copy records that its
 * retained line no longer identifies a unique source.
 */

namespace {
constexpr const char* METRIC_INSTRUCTIONS_HOISTED = "num_instructions_hoisted";
} // namespace

void BranchPrefixHoistingPass::run_pass(DexStoresVector& stores,
                                        ConfigFiles& /* unused */,
                                        PassManager& mgr) {
  auto scope = build_class_scope(stores);

  bool can_allocate_regs = !mgr.regalloc_has_run();
  // Each method accumulates into a plain local and merges once, rather than
  // touching a shared counter per join.
  AtomicStatCounter<size_t> positions_marked_unreliable{0};
  AtomicStatCounter<size_t> merges_not_recorded{0};
  size_t total_insns_hoisted = walk::parallel::methods<size_t>(
      scope,
      [can_allocate_regs, &positions_marked_unreliable, &merges_not_recorded](
          DexMethod* method) -> size_t {
        auto* const code = method->get_code();
        if ((code == nullptr) || method->rstate.no_optimizations()) {
          return 0;
        }
        TraceContext context{method};

        positions::JoinStats join_stats;
        size_t insns_hoisted = branch_prefix_hoisting_impl::process_code(
            code, method, can_allocate_regs, &join_stats);
        positions_marked_unreliable += join_stats.marked_unreliable;
        merges_not_recorded += join_stats.not_recorded;
        if (insns_hoisted != 0) {
          TRACE(BPH, 3,
                "[branch prefix hoisting] Moved %zu insns in method {%s}",
                insns_hoisted, SHOW(method));
        }
        if (join_stats.marked_unreliable != 0 || join_stats.not_recorded != 0) {
          TRACE(BPH, 3,
                "[branch prefix hoisting] %zu positions became unreliable and "
                "%zu could not be recorded in method {%s}",
                join_stats.marked_unreliable, join_stats.not_recorded,
                SHOW(method));
        }
        return insns_hoisted;
      });

  mgr.incr_metric(METRIC_INSTRUCTIONS_HOISTED, total_insns_hoisted);
  mgr.incr_metric(positions::metrics::kMarkedUnreliable,
                  positions_marked_unreliable);
  mgr.incr_metric(positions::metrics::kNotRecorded, merges_not_recorded);
}

static BranchPrefixHoistingPass s_pass;
