/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ExpandableMethodParams.h"
#include "ApiLevelChecker.h"
#include "CFGMutation.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "LiveRange.h"
#include "Resolver.h"
#include "Show.h"
#include "StringBuilder.h"
#include "TypeUtil.h"
#include "Walkers.h"

namespace {
// Predict what a method's deobfuscated name would be.
std::string show_deobfuscated(const DexType* type,
                              const DexString* name,
                              const DexProto* proto) {
  string_builders::StaticStringBuilder<5> b;
  b << show_deobfuscated(type) << "." << show(name) << ":"
    << show_deobfuscated(proto);
  return b.str();
}
} // namespace

std::vector<const DexType*> ExpandableMethodParams::get_expanded_args_vector(
    DexMethod* method,
    param_index_t param_index,
    const std::vector<DexField*>& fields) {
  auto* args = method->get_proto()->get_args();
  auto is_static_method = is_static(method);
  param_index_t param_count =
      args->size() + static_cast<unsigned long>(!is_static_method);
  std::vector<const DexType*> args_vector;
  args_vector.reserve(param_count - 1 + fields.size());
  for (param_index_t i = 0; i < param_count; i++) {
    if (i == param_index) {
      for (auto* f : fields) {
        args_vector.push_back(f->get_type());
      }
      continue;
    }
    const DexType* arg_type;
    if (i == 0 && !is_static_method) {
      if (method::is_init(method)) {
        continue;
      }
      arg_type = method->get_class();
    } else {
      arg_type = args->at(i - static_cast<int>(!is_static_method));
    }
    args_vector.push_back(arg_type);
  }
  return args_vector;
}

ExpandableMethodParams::MethodInfo ExpandableMethodParams::create_method_info(
    const MethodKey& key) const {
  MethodInfo res;
  auto* cls = type_class(key.type);
  if (cls == nullptr) {
    return res;
  }
  std::set<std::vector<const DexType*>> args_vectors;
  // First, for constructors, collect all of the (guaranteed to be distinct)
  // args.
  if (key.name->str() == "<init>") {
    for (auto* method : cls->get_all_methods()) {
      if (method->get_name() != key.name ||
          method->get_proto()->get_rtype() != key.rtype) {
        continue;
      }
      auto* args = method->get_proto()->get_args();
      std::vector<const DexType*> args_vector(args->begin(), args->end());
      auto inserted = args_vectors.insert(std::move(args_vector)).second;
      always_assert(inserted);
    }
  }
  // Second, for each matching method, and each (non-receiver) parameter
  // that is only used in igets, compute the expanded constructor args and
  // record them if they don't create a conflict.
  for (auto* method : cls->get_all_methods()) {
    if (method->get_name() != key.name ||
        method->get_proto()->get_rtype() != key.rtype) {
      continue;
    }
    auto* code = method->get_code();
    if ((code == nullptr) || method->rstate.no_optimizations()) {
      continue;
    }
    live_range::MoveAwareChains chains(
        code->cfg(),
        /* ignore_unreachable */ false,
        [](auto* insn) { return opcode::is_a_load_param(insn->opcode()); });
    auto du_chains = chains.get_def_use_chains();
    param_index_t param_index{0};
    auto ii = code->cfg().get_param_instructions();
    auto begin = ii.begin();
    if (method::is_init(method)) {
      begin++;
      param_index++;
    }
    for (auto it = begin; it != ii.end(); it++, param_index++) {
      auto* insn = it->insn;
      if (insn->opcode() != IOPCODE_LOAD_PARAM_OBJECT) {
        continue;
      }
      bool expandable{true};
      std::vector<DexField*> fields;
      for (const auto& use : UnorderedIterable(du_chains[it->insn])) {
        if (opcode::is_an_iget(use.insn->opcode())) {
          auto* field =
              resolve_field(use.insn->get_field(), FieldSearch::Instance);
          if (field != nullptr) {
            fields.push_back(field);
            continue;
          }
        }
        expandable = false;
        break;
      }
      if (!expandable) {
        continue;
      }
      std::sort(fields.begin(), fields.end(), compare_dexfields);
      // remove duplicates
      fields.erase(std::unique(fields.begin(), fields.end()), fields.end());
      auto expanded_args_vector =
          get_expanded_args_vector(method, param_index, fields);
      // We need to check if we don't have too many args that won't fit
      // into an invoke/range instruction.
      uint32_t range_size = 0;
      if (method::is_init(method)) {
        range_size++;
      }
      for (const auto* arg_type : expanded_args_vector) {
        range_size += type::is_wide_type(arg_type) ? 2 : 1;
      }
      if (range_size <= 0xff) {
        auto inserted =
            args_vectors.insert(std::move(expanded_args_vector)).second;
        if (inserted) {
          res[method].emplace(param_index, std::move(fields));
        }
      }
    }
  }
  return res;
}

// Get or create the method-info for a given type, method-name, rtype.
const ExpandableMethodParams::MethodInfo*
ExpandableMethodParams::get_method_info(const MethodKey& key) const {
  return m_method_infos
      .get_or_create_and_assert_equal(
          key, [this](const auto& _) { return create_method_info(_); })
      .first;
}

DexMethod* ExpandableMethodParams::make_expanded_method_concrete(
    DexMethodRef* expanded_method_ref) {
  auto [method, param_index] = m_candidates.at(expanded_method_ref);

  // We start from the original method method body, and mutate a copy.
  std::unique_ptr<IRCode> cloned_code =
      std::make_unique<IRCode>(std::make_unique<cfg::ControlFlowGraph>());
  method->get_code()->cfg().deep_copy(&cloned_code->cfg());
  auto& cfg = cloned_code->cfg();
  cfg::CFGMutation mutation(cfg);

  // Replace load-param of (newly created) object with a sequence of
  // load-params for the field values used by the method; initialize the
  // (newly created) object register with a const-0, so that any remaining
  // move-object instructions are still valid.
  auto* block = cfg.entry_block();
  auto load_param_it =
      block->to_cfg_instruction_iterator(block->get_first_insn());
  always_assert(!load_param_it.is_end());
  for (param_index_t i = 0; i < param_index; i++) {
    load_param_it++;
    always_assert(!load_param_it.is_end());
  }
  auto last_load_params_it =
      block->to_cfg_instruction_iterator(block->get_last_param_loading_insn());
  auto* null_insn = (new IRInstruction(OPCODE_CONST))
                        ->set_dest(load_param_it->insn->dest())
                        ->set_literal(0);
  mutation.insert_after(last_load_params_it, {null_insn});

  std::vector<IRInstruction*> new_load_param_insns;
  UnorderedMap<DexField*, reg_t> field_regs;
  auto& fields = m_method_infos.at_unsafe(MethodKey::from_method(method))
                     .at(method)
                     .at(param_index);
  for (auto* field : fields) {
    auto reg = type::is_wide_type(field->get_type()) ? cfg.allocate_wide_temp()
                                                     : cfg.allocate_temp();
    auto inserted = field_regs.emplace(field, reg).second;
    always_assert(inserted);
    auto* load_param_insn =
        (new IRInstruction(opcode::load_opcode(field->get_type())))
            ->set_dest(reg);
    new_load_param_insns.push_back(load_param_insn);
  }
  mutation.replace(load_param_it, new_load_param_insns);

  // Replace all igets on the (newly created) object with moves from the new
  // field value load-params. No other (non-move) uses of the (newly created)
  // object can exist.
  live_range::MoveAwareChains chains(
      cfg, /* ignore_unreachable */ false,
      [](auto* insn) { return opcode::is_a_load_param(insn->opcode()); });
  auto du_chains = chains.get_def_use_chains();
  UnorderedSet<IRInstruction*> use_insns;
  for (const auto& use : UnorderedIterable(du_chains[load_param_it->insn])) {
    use_insns.insert(use.insn);
  }
  auto ii = InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); it++) {
    if (use_insns.count(it->insn) == 0u) {
      continue;
    }
    auto* insn = it->insn;
    always_assert(opcode::is_an_iget(insn->opcode()));
    auto* field = resolve_field(insn->get_field(), FieldSearch::Instance);
    always_assert(field);
    auto move_result_pseudo_it = cfg.move_result_of(it);
    always_assert(!move_result_pseudo_it.is_end());
    auto reg = field_regs.at(field);
    auto dest = move_result_pseudo_it->insn->dest();
    auto* move_insn =
        (new IRInstruction(opcode::move_opcode(field->get_type())))
            ->set_src(0, reg)
            ->set_dest(dest);
    mutation.replace(it, {move_insn});
  }

  // Use the mutated copied method code to concretize the expanded method.
  mutation.flush();
  expanded_method_ref->make_concrete(
      method::is_init(method) ? method->get_access()
                              : (ACC_PUBLIC | ACC_STATIC),
      std::move(cloned_code), /* is_virtual */ false);
  auto* expanded_method = expanded_method_ref->as_def();
  always_assert(expanded_method);
  expanded_method->rstate.set_generated();
  if (method->rstate.force_hot_in_baseline_profile()) {
    expanded_method->rstate.set_force_hot_in_baseline_profile();
  }
  if (method->rstate.force_startup_in_baseline_profile()) {
    expanded_method->rstate.set_force_startup_in_baseline_profile();
  }
  int api_level = api::LevelChecker::get_method_level(method);
  expanded_method->rstate.set_api_level(api_level);
  expanded_method->set_deobfuscated_name(show_deobfuscated(expanded_method));
  return expanded_method;
}

ExpandableMethodParams::ExpandableMethodParams(const Scope& scope) {
  walk::classes(scope, [&](DexClass* cls) {
    for (auto* method : cls->get_all_methods()) {
      const auto* deob = method->get_deobfuscated_name_or_null();
      if (deob != nullptr) {
        m_deobfuscated_method_names.insert(deob);
      }
    }
  });
}

// Try to create a method-ref that represents an expanded method, where a
// particular parameter representing a (newly created) object gets replaced by
// a sequence of field values used by the ctor.
DexMethodRef* ExpandableMethodParams::get_expanded_method_ref(
    DexMethod* method,
    param_index_t param_index,
    std::vector<DexField*> const** fields) const {
  const auto* method_info = get_method_info(MethodKey::from_method(method));
  auto it = method_info->find(method);
  if (it == method_info->end()) {
    return nullptr;
  }
  auto it2 = it->second.find(param_index);
  if (it2 == it->second.end()) {
    return nullptr;
  }

  const auto* name = method->get_name();
  auto args_vector = get_expanded_args_vector(method, param_index, it2->second);
  auto* type_list = DexTypeList::make_type_list(std::move(args_vector));
  auto* proto =
      DexProto::make_proto(method->get_proto()->get_rtype(), type_list);

  if (!method::is_init(method)) {
    name = DexString::make_string(name->str() + "$oea$" +
                                  std::to_string(param_index));
  }
  auto* type = method->get_class();
  auto deob = show_deobfuscated(type, name, proto);
  // Probe with get_string, not make_string: this is a pure predicate, and
  // interning here would permanently add a never-used name to the global
  // string pool on every call. A name that is not interned cannot be in the
  // set, whose insert site skips null.
  if (m_deobfuscated_method_names.count(DexString::get_string(deob)) != 0u) {
    // Some other method ref already has the synthetic deobfuscated name that
    // we'd later want to give to the new generated method.
    return nullptr;
  }

  std::lock_guard<std::mutex> lock_guard(m_candidates_mutex);
  auto* expanded_method_ref = DexMethod::get_method(type, name, proto);
  if (expanded_method_ref != nullptr) {
    if (m_candidates.count(expanded_method_ref) == 0u) {
      // There's already a pre-existing method registered, maybe a method that
      // became unreachable. As other Redex optimizations might have persisted
      // this method-ref, we don't want to interact with it.
      return nullptr;
    }
  } else {
    expanded_method_ref = DexMethod::make_method(type, name, proto);
    always_assert(show_deobfuscated(expanded_method_ref) == deob);
    auto emplaced =
        m_candidates
            .emplace(expanded_method_ref, std::make_pair(method, param_index))
            .second;
    always_assert(emplaced);
  }
  if (fields != nullptr) {
    *fields = &it2->second;
  }
  return expanded_method_ref;
}

// Make sure that all newly used expanded methods actually exist as concrete
// methods.
size_t ExpandableMethodParams::flush(
    const Scope& scope, method_profiles::MethodProfiles* method_profiles) {
  // First, find all expanded_method_ref that made it into the updated code.
  ConcurrentSet<DexMethodRef*> used_expanded_method_refs;
  walk::parallel::opcodes(scope, [&](DexMethod*, IRInstruction* insn) {
    if (opcode::is_an_invoke(insn->opcode()) &&
        (m_candidates.count(insn->get_method()) != 0u)) {
      used_expanded_method_refs.insert(insn->get_method());
    }
  });

  // Second, make them all concrete.
  ConcurrentSet<DexMethod*> expanded_methods;
  workqueue_run<DexMethodRef*>(
      [&](DexMethodRef* expanded_method_ref) {
        expanded_methods.insert(
            make_expanded_method_concrete(expanded_method_ref));
      },
      used_expanded_method_refs);

  // Add the newly concretized methods to their classes.
  auto ordered = unordered_to_ordered(expanded_methods, compare_dexmethods);
  for (auto* expanded_method : ordered) {
    type_class(expanded_method->get_class())->add_method(expanded_method);
  }

  // Finally, derived method-profiles for used candidates, and erase the unused
  // method refs.
  for (auto&& [method, p] : UnorderedIterable(m_candidates)) {
    if (used_expanded_method_refs.count(method) != 0u) {
      method_profiles->derive_stats(method->as_def(), {p.first});
    } else {
      DexMethod::delete_method_DO_NOT_USE(dynamic_cast<DexMethod*>(method));
    }
  }
  return expanded_methods.size();
}
