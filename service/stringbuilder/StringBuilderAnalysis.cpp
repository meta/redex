/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "StringBuilderAnalysis.h"

#include "Debug.h"
#include "DexClass.h"
#include "DexUtil.h"
#include "IROpcode.h"
#include "Show.h"
#include "Trace.h"
#include "TypeUtil.h"

namespace stringbuilder_analysis {

namespace ptrs = local_pointers;

FixpointIterator::FixpointIterator(const cfg::ControlFlowGraph& cfg)
    : ir_analyzer::BaseIRAnalyzer<Environment>(cfg),
      m_stringbuilder(DexType::get_type("Ljava/lang/StringBuilder;")),
      m_stringbuilder_no_param_init(
          DexMethod::get_method("Ljava/lang/StringBuilder;.<init>:()V")),
      m_stringbuilder_init_with_string(DexMethod::get_method(
          "Ljava/lang/StringBuilder;.<init>:(Ljava/lang/String;)V")),
      m_append_str(DexString::get_string("append")) {
  always_assert(m_stringbuilder != nullptr);
  always_assert(m_stringbuilder_init_with_string != nullptr);
  always_assert(m_append_str != nullptr);

  m_immutable_types.emplace(type::_boolean());
  m_immutable_types.emplace(type::_char());
  m_immutable_types.emplace(type::_double());
  m_immutable_types.emplace(type::_float());
  m_immutable_types.emplace(type::_int());
  m_immutable_types.emplace(type::_long());
  m_immutable_types.emplace(type::java_lang_String());
}

/*
 * Only include constructors that we know are safe for our outlining scheme. In
 * particular, we want to exclude some constructors:
 *
 * 1) The constructor that takes an integer argument will throw if that number
 * is negative. Our outlining transformation would drop that integer argument
 * and could therefore change observable behavior.
 *
 * 2) The constructor that takes a CharSequence is not accepted because
 * the CharSequence interface can be implemented by mutable types. Mutable types
 * make outlining tricky: see the `mutableCharSequence` test in the
 * StringBuilderOutlinerTest suite for an example.
 */
bool FixpointIterator::is_eligible_init(const DexMethodRef* method) const {
  return method == m_stringbuilder_no_param_init ||
         method == m_stringbuilder_init_with_string;
}

/*
 * Check if it is a method of the form StringBuilder.append(<immutable>).
 */
bool FixpointIterator::is_eligible_append(const DexMethodRef* method) const {
  auto* type_list = method->get_proto()->get_args();
  return method->get_name() == m_append_str && type_list->size() == 1 &&
         (m_immutable_types.count(type_list->at(0)) != 0u);
}

void FixpointIterator::analyze_instruction(const IRInstruction* insn,
                                           Environment* env) const {
  ptrs::escape_heap_referenced_objects(insn, env);

  auto op = insn->opcode();
  if (opcode::is_an_invoke(op) &&
      insn->get_method()->get_class() == m_stringbuilder) {
    auto* method = insn->get_method();
    if (method == m_stringbuilder_init_with_string ||
        is_eligible_append(method)) {
      // When the receiver register may hold any of several builders, the
      // operation modifies only one of them, and the analysis cannot tell which
      // one. Therefore, set the state of each of these builders to top.
      const auto& receivers = env->get_pointers(insn->src(0));
      bool is_single_receiver =
          receivers.is_value() && receivers.elements().size() == 1;
      env->update_store(
          insn->src(0),
          [&](const IRInstruction* ptr, BuilderStore::Domain* store) {
            if (!is_single_receiver) {
              store->set(ptr, BuilderDomain::top());
              return;
            }
            store->update(ptr, [&](const BuilderDomain& builder) {
              auto copy = builder;
              copy.add_operation(insn);
              return copy;
            });
          });
      if (method->get_name() == m_append_str) {
        env->set_pointers(RESULT_REGISTER, env->get_pointers(insn->src(0)));
      }
    } else if (!is_eligible_init(method)) {
      TRACE(STRBUILD, 5, "Unhandled SB method: %s", SHOW(insn));
      ptrs::default_instruction_handler(insn, env);
    }
  } else if (op == OPCODE_NEW_INSTANCE && insn->get_type() == m_stringbuilder) {
    env->set_fresh_pointer(RESULT_REGISTER, insn);
  } else {
    ptrs::default_instruction_handler(insn, env);
  }
}

InstructionSet find_tostring_instructions(const cfg::ControlFlowGraph& cfg,
                                          const DexMethodRef* tostring_method) {
  UnorderedSet<const IRInstruction*> instructions;
  for (auto* block : cfg.blocks()) {
    for (auto& mie : InstructionIterable(block)) {
      auto* insn = mie.insn;
      if (insn->opcode() == OPCODE_INVOKE_VIRTUAL &&
          insn->get_method() == tostring_method) {
        instructions.emplace(insn);
      }
    }
  }
  return instructions;
}

/*
 * Gather the BuilderStates corresponding to StringBuilders whose state we can
 * accurately model for outlining purposes.
 */
BuilderStateMap gather_builder_states(
    const cfg::ControlFlowGraph& cfg,
    const InstructionSet& tostring_instructions) {
  BuilderStateMap tostring_instruction_to_state;
  FixpointIterator fp_iter(cfg);
  fp_iter.run(Environment());
  for (auto* block : cfg.blocks()) {
    auto env = fp_iter.get_entry_state_at(block);
    for (auto& mie : InstructionIterable(block)) {
      auto* insn = mie.insn;
      if (tostring_instructions.count(insn) != 0u) {
        const auto& pointers = env.get_pointers(insn->src(0));
        if (!pointers.is_value() || pointers.elements().size() != 1) {
          TRACE(STRBUILD, 5, "Did not get single pointer for %s", SHOW(insn));
          continue;
        }
        const auto& pointer = *pointers.elements().begin();
        const auto& builder = env.get_store().get(pointer);
        const auto& state_opt = builder.state();
        if (!state_opt) {
          TRACE(STRBUILD, 5, "Did not get state for %s", SHOW(insn));
        } else {
          tostring_instruction_to_state.emplace_back(insn, *state_opt);
        }
      }
      fp_iter.analyze_instruction(insn, &env);
    }
  }
  return tostring_instruction_to_state;
}

} // namespace stringbuilder_analysis
