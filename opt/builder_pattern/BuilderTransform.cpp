/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "BuilderTransform.h"
#include "ConfigFiles.h"

#include <utility>

#include "CFGMutation.h"
#include "Debug.h"
#include "DexClass.h"
#include "InitClassesWithSideEffects.h"
#include "Show.h"
#include "Trace.h"

namespace builder_pattern {

BuilderTransform::BuilderTransform(
    const Scope& scope,
    const ConfigFiles& conf,
    const DexType* root,
    const init_classes::InitClassesWithSideEffects&
        init_classes_with_side_effects,
    inliner::InlinerConfig inliner_config,
    DexStoresVector& stores)
    : m_vscopes(scope),
      m_root(root),
      m_inliner_config(std::move(inliner_config)) {
  UnorderedSet<DexMethod*> no_default_inlinables;
  // customize shrinking options
  m_inliner_config.shrinker = shrinker::ShrinkerConfig();
  m_inliner_config.shrinker.run_const_prop = true;
  m_inliner_config.shrinker.run_cse = true;
  m_inliner_config.shrinker.run_copy_prop = true;
  m_inliner_config.shrinker.run_local_dce = true;
  m_inliner_config.shrinker.compute_pure_methods = false;
  int min_sdk = 0;
  m_inliner = std::unique_ptr<MultiMethodInliner>(new MultiMethodInliner(
      scope, init_classes_with_side_effects, stores, conf,
      no_default_inlinables, std::ref(m_concurrent_method_resolver),
      m_inliner_config, min_sdk, MultiMethodInlinerMode::None));
}

UnorderedSet<IRInstruction*> BuilderTransform::try_inline_calls(
    DexMethod* caller, const UnorderedSet<IRInstruction*>& insns) {
  always_assert(caller && caller->get_code());
  m_inliner->inline_callees(caller, insns);
  UnorderedSet<IRInstruction*> not_inlined_insns;
  // Check if everything was inlined.
  auto* code = caller->get_code();
  auto& cfg = code->cfg();
  for (const auto& mie : InstructionIterable(cfg)) {
    auto* insn = mie.insn;
    if (insns.count(insn) != 0u) {
      not_inlined_insns.emplace(insn);
    }
  }

  return not_inlined_insns;
}

/**
 * For all the methods of the given type, try inlining all super calls and
 * constructors of the super type. If any of them fails, return false.
 */
bool BuilderTransform::inline_super_calls_and_ctors(const DexType* type) {
  auto* cls = type_class(type);

  std::vector<DexMethod*> methods = cls->get_dmethods();
  const std::vector<DexMethod*>& vmethods = cls->get_vmethods();
  methods.insert(methods.end(), vmethods.begin(), vmethods.end());

  const std::vector<DexMethod*>& super_ctors_list =
      type_class(m_root)->get_ctors();
  UnorderedSet<DexMethod*> super_ctors(super_ctors_list.begin(),
                                       super_ctors_list.end());

  for (DexMethod* method : methods) {
    if (method->get_code() == nullptr) {
      continue;
    }
    auto& cfg = method->get_code()->cfg();
    UnorderedSet<IRInstruction*> inlinable_insns;
    for (const auto& mie : InstructionIterable(cfg)) {
      auto* insn = mie.insn;
      if (insn->opcode() == OPCODE_INVOKE_SUPER) {
        inlinable_insns.emplace(insn);
      } else if (opcode::is_invoke_direct(insn->opcode())) {
        auto* callee =
            resolve_method_deprecated(insn->get_method(), MethodSearch::Direct);
        if (super_ctors.count(callee) != 0u) {
          inlinable_insns.emplace(insn);
        }
      }
    }

    if (!inlinable_insns.empty()) {
      TRACE(BLD_PATTERN, 8, "Creating a copy of %s", SHOW(method));

      const auto name_str = method->get_name()->str();
      DexMethod* method_copy = DexMethod::make_method_from(
          method,
          method->get_class(),
          DexString::make_string(name_str + "$redex_builder"));
      m_method_copy[method] = method_copy;

      size_t num_insns_not_inlined =
          try_inline_calls(method, inlinable_insns).size();
      if (num_insns_not_inlined > 0) {
        return false;
      }
    }
  }

  return true;
}

/**
 * Bind virtual calls to the actual implementation.
 */
void BuilderTransform::update_virtual_calls(
    const UnorderedMap<IRInstruction*, const DexType*>& insn_to_type) {

  for (const auto& pair : UnorderedIterable(insn_to_type)) {
    auto* insn = pair.first;
    const auto* current_instance = pair.second;

    if (opcode::is_invoke_virtual(insn->opcode())) {
      auto* method =
          resolve_method_deprecated(insn->get_method(), MethodSearch::Virtual);
      if (method == nullptr) {
        continue;
      }

      if (method->get_class() == m_root) {
        // replace it with the actual implementation if any provided.
        const auto* virtual_scope = m_vscopes.find(method);
        for (const auto* scope_meth : virtual_scope->methods()) {
          auto* m = const_cast<DexMethod*>(scope_meth);
          if (m->get_class() == current_instance && m->is_def()) {
            TRACE(BLD_PATTERN, 3,
                  "Replace virtual method %s with the current implementation "
                  "%s",
                  SHOW(method), SHOW(m));
            insn->set_method(m);
            break;
          }
        }
      }
    }
  }
}

namespace {

std::vector<IRInstruction*> make_initializations(
    const std::map<DexField*, size_t, dexfields_comparator>& field_to_reg) {
  std::vector<IRInstruction*> initializations;
  for (const auto& pair : field_to_reg) {
    auto* field = pair.first;
    auto reg = pair.second;

    IRInstruction* initialization_insn = nullptr;
    if (type::is_wide_type(field->get_type())) {
      initialization_insn = new IRInstruction(OPCODE_CONST_WIDE);
    } else {
      initialization_insn = new IRInstruction(OPCODE_CONST);
    }
    initialization_insn->set_dest(static_cast<reg_t>(reg));
    initialization_insn->set_literal(0);
    initializations.push_back(initialization_insn);
  }
  return initializations;
}

} // namespace

void BuilderTransform::replace_fields(const InstantiationToUsage& usage,
                                      DexMethod* method) {
  auto* code = method->get_code();

  always_assert_log(code->cfg_built(), "Missing CFG for %s", SHOW(method));
  auto& cfg = code->cfg();
  cfg::CFGMutation mutation(cfg);
  std::vector<IRInstruction*> instantiations;
  std::vector<IRInstruction*> entry_initializations;
  auto* first_block = cfg.get_first_block_with_insns();
  auto entry = first_block->to_cfg_instruction_iterator(
      first_block->get_first_non_param_loading_insn());

  for (const auto& mie : InstructionIterable(cfg)) {
    auto* instantiation_insn = mie.insn;
    if (usage.count(instantiation_insn) == 0u) {
      continue;
    }

    always_assert_log(instantiation_insn->opcode() == OPCODE_NEW_INSTANCE,
                      "Only accept new_instance opcodes for builder "
                      "initializations, but got %s\n",
                      SHOW(instantiation_insn));

    auto allocation = cfg.find_insn(instantiation_insn);
    auto allocation_result = cfg.move_result_of(allocation);
    always_assert_log(!allocation_result.is_end(),
                      "Missing allocation result for %s in %s",
                      SHOW(instantiation_insn), SHOW(method));
    instantiations.push_back(instantiation_insn);

    std::map<DexField*, size_t, dexfields_comparator> field_to_reg;
    for (const auto& it : usage.at(instantiation_insn)) {
      auto* insn = it->insn;

      if (opcode::is_an_iput(insn->opcode()) ||
          opcode::is_an_iget(insn->opcode())) {
        auto* field = resolve_field(insn->get_field(), FieldSearch::Instance);
        always_assert_log(field, "Unresolved builder field in %s", SHOW(insn));

        if (field_to_reg.count(field) == 0) {
          field_to_reg[field] = type::is_wide_type(field->get_type())
                                    ? cfg.allocate_wide_temp()
                                    : cfg.allocate_temp();
        }

        // Replace usage.
        IRInstruction* new_insn = nullptr;
        if (type::is_wide_type(field->get_type())) {
          new_insn = new IRInstruction(OPCODE_MOVE_WIDE);
        } else if (type::is_primitive(field->get_type())) {
          new_insn = new IRInstruction(OPCODE_MOVE);
        } else {
          new_insn = new IRInstruction(OPCODE_MOVE_OBJECT);
        }

        if (opcode::is_an_iput(insn->opcode())) {
          new_insn->set_dest(static_cast<reg_t>(field_to_reg[field]));
          new_insn->set_src(0, insn->src(0));
        } else {
          auto move_result = cfg.move_result_of(it);
          always_assert_log(!move_result.is_end(),
                            "Missing result for %s in %s", SHOW(insn),
                            SHOW(method));
          new_insn->set_dest(move_result->insn->dest());
          new_insn->set_src(0, static_cast<reg_t>(field_to_reg[field]));
        }
        mutation.replace(it, {new_insn});
      } else if (insn->opcode() == OPCODE_MOVE_OBJECT ||
                 insn->opcode() == IOPCODE_MOVE_RESULT_PSEUDO_OBJECT ||
                 opcode::is_a_conditional_branch(insn->opcode())) {
        // Keep these instructions as is because we might not be able to clean
        // up all the paths where Object created instead of builder could
        // be used for checking if the builder was created or not.
        // ConstProp + DCE will take care of safe clean up for us.
      } else {
        always_assert_log(insn->opcode() == OPCODE_INVOKE_DIRECT ||
                              insn->opcode() == OPCODE_CHECK_CAST,
                          "Different insn %s", SHOW(insn));
        if (insn->opcode() == OPCODE_INVOKE_DIRECT) {
          auto* invoked = resolve_method_deprecated(insn->get_method(),
                                                    MethodSearch::Direct);

          // We only accept `Object.<init>()` here, since we can't inline it
          // any further. Keep Object.<init> in place to avoid confusing
          // dex2oat.

          always_assert_log(
              invoked && invoked->get_class() == type::java_lang_Object() &&
                  method::is_init(invoked),
              "Unexpected builder invoke %s in %s", SHOW(insn), SHOW(method));
        } else {
          // Replace check-cast with move.
          IRInstruction* new_move = new IRInstruction(OPCODE_MOVE_OBJECT);
          new_move->set_src(0, insn->src(0));
          auto move_result = cfg.move_result_of(it);
          always_assert_log(!move_result.is_end(),
                            "Missing result for %s in %s", SHOW(insn),
                            SHOW(method));
          new_move->set_dest(move_result->insn->dest());
          mutation.replace(it, {new_move});
        }
      }
    }

    // Entry definitions cover paths that join an allocation with NULL.
    auto initializations = make_initializations(field_to_reg);
    entry_initializations.insert(entry_initializations.end(),
                                 initializations.begin(),
                                 initializations.end());
    // Only a successful allocation starts a new field-register lifetime.
    mutation.insert_after(allocation_result,
                          make_initializations(field_to_reg));
  }

  // All rewrite inputs have been checked before changing the method.
  for (auto* insn : instantiations) {
    // Replace builder instance creation with Object creation.
    // Retain an object value for NULL comparisons and Object.<init>().
    insn->set_type(type::java_lang_Object());
  }
  // The entry block can contain only parameters, so its anchor can be end().
  cfg.insert_before(entry, entry_initializations);
  mutation.flush();
}

void BuilderTransform::cleanup() {
  for (const auto& pair : UnorderedIterable(m_method_copy)) {
    auto* method = pair.first;
    auto* copy = pair.second;

    TRACE(BLD_PATTERN,
          8,
          "Replacing method with its original version %s",
          SHOW(method));
    method->set_code(copy->release_code());
    DexMethod::delete_method_DO_NOT_USE(copy);
  }
  m_inliner->flush();
}

} // namespace builder_pattern
