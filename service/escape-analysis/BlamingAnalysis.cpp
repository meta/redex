/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "BlamingAnalysis.h"

#include "Debug.h"
using namespace ir_analyzer;

namespace {

/*
 * Returns the register that `insn` puts its result into, assuming it has one.
 * (This function will fail if the instruction has no destination).
 */
reg_t dest(const IRInstruction* insn) {
  return insn->has_move_result_any() ? RESULT_REGISTER : insn->dest();
}

} // namespace

namespace local_pointers {
namespace blaming {

FixpointIterator::FixpointIterator(
    const cfg::ControlFlowGraph& cfg,
    UnorderedSet<const IRInstruction*> allocators,
    UnorderedSet<DexMethodRef*> safe_method_refs,
    UnorderedSet<const DexString*> safe_method_names)
    : ir_analyzer::BaseIRAnalyzer<Environment>(cfg),
      m_allocators(std::move(allocators)),
      m_safe_method_refs(std::move(safe_method_refs)),
      m_safe_method_names(std::move(safe_method_names)) {}

void FixpointIterator::analyze_instruction(const IRInstruction* insn,
                                           Environment* env) const {
  escape_heap_referenced_objects(insn, env);

  auto op = insn->opcode();
  if (op == OPCODE_RETURN_OBJECT) {
    env->set_may_escape(insn->src(0), insn);
  } else if (opcode::is_a_method_invoke(op)) {
    if (!is_safe_method(insn->get_method())) {
      escape_invoke_params(insn, env);
    }

    if (is_allocator(insn)) {
      env->set_fresh_pointer(dest(insn), insn);
    } else {
      escape_dest(insn, RESULT_REGISTER, env);
    }
  } else if (is_allocator(insn)) {
    env->set_fresh_pointer(dest(insn), insn);
  } else {
    default_instruction_handler(insn, env);
  }
}

BlameMap analyze_escapes(cfg::ControlFlowGraph& cfg,
                         UnorderedSet<const IRInstruction*> allocators,
                         std::initializer_list<SafeMethod> safe_methods) {

  UnorderedSet<DexMethodRef*> safe_method_refs;
  UnorderedSet<const DexString*> safe_method_names;
  for (const auto& safe : safe_methods) {
    switch (safe.type) {
    case SafeMethod::ByRef:
      safe_method_refs.insert(safe.method_ref);
      break;
    case SafeMethod::ByName:
      safe_method_names.insert(safe.method_name);
      break;
    default:
      not_reached_log("Safe: unknown type");
    }
  }

  if (cfg.exit_block() == nullptr) {
    cfg.calculate_exit_block();
  }

  BlameStore::Domain store;
  for (const auto* alloc : UnorderedIterable(allocators)) {
    store.set(alloc, BlameStore::unallocated());
  }

  blaming::FixpointIterator fp{cfg, std::move(allocators),
                               std::move(safe_method_refs),
                               std::move(safe_method_names)};

  fp.run({{}, std::move(store)});

  return BlameMap{fp.get_exit_state_at(cfg.exit_block()).get_store()};
}

} // namespace blaming
} // namespace local_pointers
