/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "RedundantCheckCastRemover.h"

#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexClass.h"
#include "IRCode.h"
#include "Match.h"
#include "PassManager.h"
#include "Show.h"
#include "Trace.h"
#include "TypeUtil.h"
#include "Walkers.h"

RedundantCheckCastRemover::RedundantCheckCastRemover(
    PassManager& mgr, const std::vector<DexClass*>& scope)
    : m_mgr(mgr), m_scope(scope) {}

void RedundantCheckCastRemover::run() {
  auto match = std::make_tuple(m::a_method_invoke(),
                               m::move_result_object_(),
                               m::check_cast_(),
                               m::move_result_pseudo_object_());

  UnorderedMap<DexMethod*, std::vector<IRInstruction*>> to_remove;

  std::atomic<uint32_t> num_check_casts_removed(0);
  walk::parallel::matching_opcodes_in_block(
      m_scope,
      match,
      [&num_check_casts_removed](DexMethod* method,
                                 cfg::Block*,
                                 const std::vector<IRInstruction*>& insns) {
        if (RedundantCheckCastRemover::can_remove_check_cast(insns)) {
          IRInstruction* check_cast = insns[2];
          auto& cfg = method->get_code()->cfg();
          auto pos_it = cfg.find_insn(check_cast);
          cfg.remove_insn(pos_it);
          num_check_casts_removed++;

          TRACE(PEEPHOLE, 8, "redundant check cast in %s", SHOW(method));
          for (IRInstruction* insn : insns) {
            TRACE(PEEPHOLE, 8, "  %s", SHOW(insn));
          }
        }
      });

  m_mgr.incr_metric("redundant_check_casts_removed", num_check_casts_removed);
}

bool RedundantCheckCastRemover::can_remove_check_cast(
    const std::vector<IRInstruction*>& insns) {
  always_assert(insns.size() == 4);
  IRInstruction* invoke_op = insns[0];
  IRInstruction* move_result_op = insns[1];
  IRInstruction* check_cast_op = insns[2];
  IRInstruction* move_result_pseudo = insns[3];

  auto* invoke_return = invoke_op->get_method()->get_proto()->get_rtype();
  auto* check_type = check_cast_op->get_type();
  return move_result_op->dest() == check_cast_op->src(0) &&
         move_result_pseudo->dest() == check_cast_op->src(0) &&
         type::check_cast(invoke_return, check_type);
}
