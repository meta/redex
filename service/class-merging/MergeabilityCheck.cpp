/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "MergeabilityCheck.h"

#include "ClassUtil.h"
#include "DexUtil.h"
#include "IRCode.h"
#include "LiveRange.h"
#include "Model.h"
#include "ReachableClasses.h"
#include "RefChecker.h"
#include "Resolver.h"
#include "Show.h"
#include "Trace.h"
#include "Walkers.h"

using namespace class_merging;

MergeabilityChecker::MergeabilityChecker(const Scope& scope,
                                         const ModelSpec& spec,
                                         const RefChecker& ref_checker,
                                         const TypeSet& generated)
    : m_scope(scope),
      m_spec(spec),
      m_ref_checker(ref_checker),
      m_generated(generated),
      m_const_class_safe_types(spec.const_class_safe_types),
      m_track_use_of_reflection(spec.mergeability_checks_use_of_const_class) {}

void MergeabilityChecker::exclude_unsupported_cls_property(
    TypeSet& non_mergeables) {
  for (const auto& type : UnorderedIterable(m_spec.merging_targets)) {
    const auto& cls = type_class(type);
    if (!can_delete(cls)) {
      non_mergeables.insert(type);
      TRACE(CLMG, 5, "Cannot delete %s", SHOW(type));
      continue;
    }
    // Why uninstantiable classes are not mergeable?
    // Class Merging is good at merging virtual methods horizontally by
    // supporting virtual dispatches. There's no benefit to merge uninstantiable
    // classes and no proper way to merge uninstantiable and instantiable
    // classes together. Exclude the uninstantiable classes from ClassMerging
    // and RemoveUnreachablePass should properly handle parts of them.
    bool has_ctor = false;
    for (const auto& method : cls->get_dmethods()) {
      if (is_constructor(method) && method::is_init(method)) {
        has_ctor = true;
        // keep going
      }
      if (method->rstate.no_optimizations() ||
          (method->get_code() == nullptr)) {
        non_mergeables.insert(type);
        TRACE(CLMG, 5, "Cannot optimize dmethod on %s", SHOW(type));
        break;
      }
    }
    if (!has_ctor) {
      non_mergeables.insert(type);
      TRACE(CLMG, 5, "Has no ctor %s", SHOW(type));
    }
    // We do not support merging abstract and non-abstract classes together.
    if (is_abstract(cls)) {
      non_mergeables.insert(type);
      TRACE(CLMG, 5, "Is abstract %s", SHOW(type));
    }
  }
}

TypeSet MergeabilityChecker::exclude_unsupported_bytecode_refs_for(
    DexMethod* method) {
  TypeSet non_mergeables;
  auto* code = method->get_code();
  if ((code == nullptr) || (m_generated.count(method->get_class()) != 0u)) {
    return non_mergeables;
  }

  bool has_type_tag = m_spec.has_type_tag();
  std::vector<std::pair<IRInstruction*, const DexType*>>
      const_classes_to_verify;
  UnorderedSet<const IRInstruction*> const_classes_to_verify_set;
  std::vector<IRInstruction*> new_instances_to_verify;
  UnorderedSet<const IRInstruction*> new_instances_to_verify_set;
  auto& cfg = code->cfg();
  for (const auto& mie : InstructionIterable(cfg)) {
    auto* insn = mie.insn;

    if (opcode::is_new_instance(insn->opcode()) &&
        (m_spec.merging_targets.count(insn->get_type()) != 0u)) {
      new_instances_to_verify.push_back(insn);
      new_instances_to_verify_set.insert(insn);
      continue;
    }

    // If we have a pure method ref on a mergeable type (the class component is
    // mergeable), we do not merge the type.
    // 1. We cannot properly update type references on pure method refs.
    // 2. We rely the ResolveRefsPass to resolve all pure method refs before
    // running Class Merging. However, there are rare exceptions where resolving
    // method refs to external cannot be done. In this case, it's safer not to
    // merge types with existing pure method refs on the type.
    if (insn->has_method() && !insn->get_method()->is_def()) {
      auto* meth_ref = insn->get_method();
      auto* type = meth_ref->get_class();
      if (m_spec.merging_targets.count(type) > 0) {
        TRACE(CLMG, 5, "[non mergeable] referenced by pure ref %s in %s",
              SHOW(meth_ref), SHOW(method));
        non_mergeables.insert(type);
      }
      continue;
    }

    // The presence of type-like strings can indicate that types are used by
    // reflection, and then it's not safe to merge those types.
    if (m_spec.exclude_type_like_strings() &&
        opcode::is_const_string(insn->opcode())) {
      DexType* maybe_type =
          java_names::get_type_from_external_name(insn->get_string()->str());
      if ((maybe_type != nullptr) &&
          m_spec.merging_targets.count(maybe_type) > 0) {
        non_mergeables.insert(maybe_type);
        TRACE(CLMG, 5,
              "[non mergeable] type like const string unsafe: %s in %s",
              SHOW(insn), SHOW(method));
      }
      continue;
    }

    // Java language level enforcement recommended!
    //
    // For mergeables with type tags, it is not safe to merge those
    // referenced by CONST_CLASS, since we will lose granularity as we can't map
    // to the old type anymore.
    // Type tags distinguish merger instances, not array element classes.
    if (has_type_tag && !opcode::is_const_class(insn->opcode()) &&
        !(opcode::is_instance_of(insn->opcode()) &&
          type::is_array(insn->get_type()))) {
      continue;
    }

    // Java language level enforcement recommended!
    //
    // For mergeables without a type tag, it is not safe to merge
    // those used in an INSTANCE_OF, since we might lose granularity.
    //
    // Example where both <type_0> and <type_1> have the same shape
    // (so end
    //        up in the same merger)
    //
    //    INSTANCE_OF <v_result>, <v_obj> <type_0>
    //    then label:
    //      CHECK_CAST <type_0>
    //    else labe:
    //      CHECK_CAST <type_1>
    if (!has_type_tag && !opcode::is_instance_of(insn->opcode())) {
      continue;
    }

    const auto* type = type::make_element_type_if_array(insn->get_type());
    if (m_spec.merging_targets.count(type) > 0) {
      if (m_track_use_of_reflection) {
        // Always track the const-class usages.
        if (!opcode::is_const_class(insn->opcode())) {
          TRACE(CLMG, 5, "[non mergeable] unsafe opcode @ %s in %s", SHOW(insn),
                SHOW(method));
          non_mergeables.insert(type);
        } else {
          // To verify the usages
          const_classes_to_verify.emplace_back(insn, type);
          const_classes_to_verify_set.insert(insn);
        }
      } else {
        // Old logic that also checks m_const_class_safe_types not being empty.
        if (!opcode::is_const_class(insn->opcode()) ||
            m_const_class_safe_types.empty()) {
          TRACE(CLMG, 5, "[non mergeable] unsafe opcode @ %s in %s", SHOW(insn),
                SHOW(method));
          non_mergeables.insert(type);
        } else {
          // To verify the usages
          const_classes_to_verify.emplace_back(insn, type);
          const_classes_to_verify_set.insert(insn);
        }
      }
    }
  }

  if (const_classes_to_verify.empty() && new_instances_to_verify.empty()) {
    return non_mergeables;
  }

  live_range::MoveAwareChains chains(
      cfg, /* ignore_unreachable */ false, [&](auto* insn) {
        return const_classes_to_verify_set.count(insn) ||
               new_instances_to_verify_set.count(insn);
      });
  live_range::DefUseChains du_chains = chains.get_def_use_chains();

  for (const auto& pair : const_classes_to_verify) {
    auto* const_class_insn = pair.first;
    const auto* referenced_type = pair.second;
    const auto& use_set = du_chains[const_class_insn];
    for (const auto& use : UnorderedIterable(use_set)) {
      auto* use_insn = use.insn;
      if (opcode::is_a_move(use_insn->opcode())) {
        // Ignore moves
        continue;
      }
      if (!use_insn->has_method()) {
        TRACE(CLMG, 5, "[non mergeable] const class unsafe use @ %s in %s",
              SHOW(use_insn), SHOW(method));
        non_mergeables.insert(referenced_type);
        break;
      }
      auto* callee = use_insn->get_method();
      auto* callee_type = callee->get_class();
      if (m_const_class_safe_types.count(callee_type) == 0u) {
        TRACE(CLMG, 5, "[non mergeable] const class unsafe callee %s in %s",
              SHOW(callee), SHOW(method));
        non_mergeables.insert(referenced_type);
        break;
      }
    }
  }

  // We find and exclude classes of which instances are created via
  // new-instance, but then the associated constructor call invokes a
  // constructor of a super type, and not the exact instantiated type.
  // TODO T184662680: Fully support such scenario, e.g. by synthesizing a
  // corresponding constructor on the instantiated class, and not just exclude.
  for (auto* new_instance_insn : UnorderedIterable(new_instances_to_verify)) {
    auto* type = new_instance_insn->get_type();
    const auto& use_set = du_chains[new_instance_insn];
    for (const auto& use : UnorderedIterable(use_set)) {
      if (use.src_index != 0) {
        continue;
      }
      auto* use_insn = use.insn;
      if (opcode::is_a_move(use_insn->opcode())) {
        // Ignore moves
        continue;
      }
      if (!use_insn->has_method()) {
        continue;
      }
      auto* callee = use_insn->get_method();
      if (!method::is_init(callee)) {
        continue;
      }
      const auto* resolved_callee =
          resolve_method_deprecated(callee, opcode_to_search(use_insn), method);
      if ((resolved_callee == nullptr) ||
          resolved_callee->get_class() != type) {
        TRACE(CLMG, 5,
              "[non mergeable] new-instance %s associated with invoke init %s "
              "defined in other type in %s",
              SHOW(new_instance_insn), SHOW(use_insn), SHOW(method));
        non_mergeables.insert(type);
        break;
      }
    }
  }

  return non_mergeables;
}

void MergeabilityChecker::exclude_unsupported_bytecode(
    TypeSet& non_mergeables) {
  TypeSet non_mergeables_opcode =
      walk::parallel::methods<TypeSet, MergeContainers<TypeSet>>(
          m_scope, [this](DexMethod* meth) {
            return exclude_unsupported_bytecode_refs_for(meth);
          });

  non_mergeables.insert(non_mergeables_opcode.begin(),
                        non_mergeables_opcode.end());
}

void MergeabilityChecker::exclude_static_fields(TypeSet& non_mergeables) {
  static const DexType* string_type = type::java_lang_String();

  if (m_spec.merge_types_with_static_fields) {
    return;
  }

  walk::fields(m_scope, [&non_mergeables, this](DexField* field) {
    if (m_spec.merging_targets.count(field->get_class()) != 0u) {
      if (is_static(field)) {
        const auto* rtype = type::make_element_type_if_array(field->get_type());
        if (!type::is_primitive(rtype) && rtype != string_type) {
          // If the type is either non-primitive or a list of
          // non-primitive types (excluding Strings), then exclude it as
          // we might change the initialization order.
          TRACE(CLMG,
                5,
                "[non mergeable] %s as it contains a non-primitive "
                "static field",
                SHOW(field->get_class()));
          non_mergeables.emplace(field->get_class());
        }
      }
    }
  });
}

void MergeabilityChecker::exclude_unsafe_sdk_and_store_refs(
    TypeSet& non_mergeables) {
  const auto mog = method_override_graph::build_graph(m_scope);
  for (const auto* type : UnorderedIterable(m_spec.merging_targets)) {
    if (non_mergeables.count(type) != 0u) {
      continue;
    }
    auto* cls = type_class(type);
    if (!m_ref_checker.check_class(cls, mog)) {
      non_mergeables.insert(type);
    }
    if (!m_spec.include_primary_dex && m_ref_checker.is_in_primary_dex(type)) {
      non_mergeables.insert(type);
    }
  }
}

// Helper to recursively extract all types referenced by an encoded value
// that are in the merging_targets set, and insert them into non_mergeables.
void MergeabilityChecker::collect_referenced_mergeable_types(
    const DexEncodedValue* ev,
    TypeSet& non_mergeables,
    const DexType* anno_type,
    const char* context) {
  if (ev == nullptr) {
    return;
  }

  auto maybe_insert = [&](const DexType* type) {
    if (type != nullptr && m_spec.merging_targets.count(type) > 0) {
      auto [it, inserted] = non_mergeables.insert(type);
      if (inserted) {
        TRACE(CLMG,
              5,
              "[non mergeable] %s referenced by unhandled annotation %s in %s",
              SHOW(type),
              SHOW(anno_type),
              context);
      }
    }
  };

  switch (ev->evtype()) {
  case DEVT_TYPE: {
    const auto* type_ev = dynamic_cast<const DexEncodedValueType*>(ev);
    const auto* type = type::make_element_type_if_array(type_ev->type());
    maybe_insert(type);
    break;
  }
  case DEVT_METHOD: {
    const auto* method_ev = dynamic_cast<const DexEncodedValueMethod*>(ev);
    auto* method = method_ev->method();
    if (method != nullptr) {
      // Check containing class
      maybe_insert(type::make_element_type_if_array(method->get_class()));
      // Check return type and parameter types
      auto* proto = method->get_proto();
      if (proto != nullptr) {
        maybe_insert(type::make_element_type_if_array(proto->get_rtype()));
        if (auto* args = proto->get_args()) {
          for (const auto* arg_type : *args) {
            maybe_insert(type::make_element_type_if_array(arg_type));
          }
        }
      }
    }
    break;
  }
  case DEVT_FIELD: {
    const auto* field_ev = dynamic_cast<const DexEncodedValueField*>(ev);
    auto* field = field_ev->field();
    if (field != nullptr) {
      // Check containing class
      maybe_insert(type::make_element_type_if_array(field->get_class()));
      // Check field type
      maybe_insert(type::make_element_type_if_array(field->get_type()));
    }
    break;
  }
  case DEVT_ARRAY: {
    const auto* array_ev = dynamic_cast<const DexEncodedValueArray*>(ev);
    if (array_ev->evalues() != nullptr) {
      for (const auto& elem : *array_ev->evalues()) {
        collect_referenced_mergeable_types(elem.get(), non_mergeables,
                                           anno_type, context);
      }
    }
    break;
  }
  case DEVT_ANNOTATION: {
    const auto* anno_ev = dynamic_cast<const DexEncodedValueAnnotation*>(ev);
    for (const auto& elem : anno_ev->annotations()) {
      collect_referenced_mergeable_types(elem.encoded_value.get(),
                                         non_mergeables, anno_type, context);
    }
    break;
  }
  default:
    break;
  }
}

// We perform the check here mostly for Android system annotations. Since types
// referenced in the Android annotations if kept in the release app are likely
// to be retained for reflection purposes.
void MergeabilityChecker::exclude_unhandled_anno_refs(TypeSet& non_mergeables) {
  if (m_spec.merging_targets.empty()) {
    return;
  }

  // dalvik.annotation.Signature is handled by TypeStringRewriter, so we skip
  // it. Other annotations that contain type/method/field references to merging
  // targets will cause those targets to be excluded from merging.
  auto* dalvik_sig = type::dalvik_annotation_Signature();

  auto check_anno_set = [&](const DexAnnotationSet* anno_set,
                            const std::string& context) {
    if (anno_set == nullptr) {
      return;
    }
    for (const auto& anno : anno_set->get_annotations()) {
      // Skip Signature annotations - TypeStringRewriter handles them.
      if (anno->type() == dalvik_sig) {
        continue;
      }
      for (const auto& elem : anno->anno_elems()) {
        collect_referenced_mergeable_types(elem.encoded_value.get(),
                                           non_mergeables,
                                           anno->type(),
                                           context.c_str());
      }
    }
  };

  for (const auto* cls : m_scope) {
    std::string cls_name = show(cls);
    check_anno_set(cls->get_anno_set(), cls_name);

    for (const auto* field : cls->get_all_fields()) {
      check_anno_set(field->get_anno_set(), show(field));
    }

    for (const auto* method : cls->get_all_methods()) {
      std::string method_name = show(method);
      check_anno_set(method->get_anno_set(), method_name);
      // Also check parameter annotations
      const auto* param_annos = method->get_param_anno();
      if (param_annos != nullptr) {
        for (const auto& param_anno : *param_annos) {
          check_anno_set(param_anno.second.get(), method_name);
        }
      }
    }
  }
}

TypeSet MergeabilityChecker::get_non_mergeables() {
  TypeSet non_mergeables;
  size_t prev_size = 0;

  exclude_unsupported_cls_property(non_mergeables);
  TRACE(CLMG, 4, "Non mergeables (no delete) %zu", non_mergeables.size());
  prev_size = non_mergeables.size();

  exclude_unsupported_bytecode(non_mergeables);
  TRACE(CLMG,
        4,
        "Non mergeables (opcodes) %zu",
        non_mergeables.size() - prev_size);
  prev_size = non_mergeables.size();

  exclude_static_fields(non_mergeables);
  TRACE(CLMG,
        4,
        "Non mergeables (static fields) %zu",
        non_mergeables.size() - prev_size);
  prev_size = non_mergeables.size();

  exclude_unsafe_sdk_and_store_refs(non_mergeables);
  TRACE(CLMG,
        4,
        "Non mergeables (unsafe refs) %zu",
        non_mergeables.size() - prev_size);
  prev_size = non_mergeables.size();

  exclude_unhandled_anno_refs(non_mergeables);
  TRACE(CLMG,
        4,
        "Non mergeables (unhandled anno refs) %zu",
        non_mergeables.size() - prev_size);
  prev_size = non_mergeables.size();

  if (m_spec.skip_anonymous_classes) {
    for (const auto& type : UnorderedIterable(m_spec.merging_targets)) {
      const auto* cls = type_class(type);
      if (klass::maybe_anonymous_class(cls)) {
        non_mergeables.insert(type);
      }
    }
  }
  TRACE(CLMG,
        4,
        "Non mergeables (skip anonymous classes) %zu",
        non_mergeables.size() - prev_size);

  return non_mergeables;
}
