/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "CheckRecursion.h"

#include <atomic>

#include "ControlFlow.h"
#include "Debug.h"
#include "DexAsm.h"
#include "DexClass.h"
#include "DexUtil.h"
#include "PassManager.h"
#include "Resolver.h"
#include "Show.h"
#include "Trace.h"
#include "Walkers.h"

namespace {

constexpr const char* METRIC_METHODS_DETECTED = "methods_detected";
constexpr const char* METRIC_METHODS_PATCHED = "methods_patched";

enum class CheckRecursionResult { NotFound, SafeRecursion, Patched };

// Check bad recursion and apply fix for the method. CFG should be built before
// calling this function.
static CheckRecursionResult do_check_recursion(DexMethod* method,
                                               IRCode& code,
                                               int bad_recursion_count) {
  int self_recursion_count = 0;
  std::unique_ptr<cfg::InstructionIterator> last_call_insn;
  auto iterable = cfg::InstructionIterable(code.cfg());
  for (auto it = iterable.begin(); it != iterable.end(); ++it) {
    auto* insn = it->insn;
    if (!opcode::is_a_method_invoke(insn->opcode())) {
      continue;
    }

    auto* callee_method_ref = insn->get_method();
    auto* callee_method = resolve_method_deprecated(
        callee_method_ref, opcode_to_search(insn), method);
    if (callee_method == nullptr) {
      continue;
    }

    if (method == callee_method) {
      self_recursion_count++;
      last_call_insn.reset(new cfg::InstructionIterator(it));
    }
  }

  if (self_recursion_count < bad_recursion_count) {
    return CheckRecursionResult::NotFound;
  }

  for (auto* it : code.cfg().blocks()) {
    if (it->is_catch()) {
      // Catch handlers disables inlining, so if the method already has
      // catch handlers there is nothing to do.
      TRACE(CHECKRECURSION, 2, "Skip method %s with catches, recursion %d",
            SHOW(method), self_recursion_count);
      return CheckRecursionResult::SafeRecursion;
    }
  }

  TRACE(CHECKRECURSION, 1, "Bad self recursion %d times in %s",
        self_recursion_count, SHOW(method));

  cfg::InstructionIterator call_insn = *last_call_insn;
  always_assert(!call_insn.is_end());

  cfg::Block* block = call_insn.block();
  // Split block just before and just after last self recursive call if
  // call instruction is not the first instruction in the block.
  auto split_insn = call_insn.unwrap();
  while (split_insn != block->begin()) {
    if ((--split_insn)->type == MFLOW_OPCODE) {
      break;
    }
  }
  if (split_insn != block->begin()) {
    always_assert(split_insn->type == MFLOW_OPCODE);
    block =
        code.cfg().split_block(block->to_cfg_instruction_iterator(split_insn));
    call_insn = block->to_cfg_instruction_iterator(block->get_first_insn());
  }
  // Also have to split block after the call because otherwise, if the
  // block has return, it cannot have exception edge.
  code.cfg().split_block(call_insn);

  cfg::Block* catch_block = code.cfg().create_block();
  code.cfg().add_edge(block, catch_block, /* catch_type */ nullptr,
                      /* index */ 0);

  using namespace dex_asm;
  Operand exception_reg{VREG, code.cfg().allocate_temp()};
  catch_block->push_back({dasm(OPCODE_MOVE_EXCEPTION, {exception_reg}),
                          dasm(OPCODE_THROW, {exception_reg})});

  return CheckRecursionResult::Patched;
}

} // namespace

/**
 * This isn't a real optimisation pass. This pass tests for self recursion that
 * might cause problems on the device due to massive dex2oat memory usage for
 * self-recursive function, see https://r8-review.googlesource.com/c/r8/+/25743/
 * for more details. The workaround is to inserts try/catch to prevent inlining.
 */
void CheckRecursionPass::run_pass(DexStoresVector& stores,
                                  ConfigFiles& /* unused */,
                                  PassManager& mgr) {
  auto min_sdk = mgr.get_redex_options().min_sdk;
  constexpr int32_t kAndroidN = 24;
  if (min_sdk >= kAndroidN) {
    mgr.set_metric("skipped_for_min_sdk_version", 1);
    return;
  }

  std::atomic_int num_methods_detected{0};
  std::atomic_int num_methods_patched{0};

  const auto scope = build_class_scope(stores);
  walk::parallel::code(
      scope,
      [this, &num_methods_detected, &num_methods_patched](DexMethod* method,
                                                          IRCode& code) {
        switch (do_check_recursion(method, code, bad_recursion_count)) {
        case CheckRecursionResult::SafeRecursion:
          ++num_methods_detected;
          break;

        case CheckRecursionResult::Patched:
          ++num_methods_detected;
          ++num_methods_patched;
          break;

        case CheckRecursionResult::NotFound:
          break;
        }
      });

  mgr.incr_metric(METRIC_METHODS_DETECTED, num_methods_detected);
  mgr.incr_metric(METRIC_METHODS_PATCHED, num_methods_patched);
}

static CheckRecursionPass s_pass;
