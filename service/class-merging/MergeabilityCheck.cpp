/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "MergeabilityCheck.h"

#include <array>

#include "ClassAssemblingUtils.h"
#include "ClassUtil.h"
#include "ConstructorAnalysis.h"
#include "DexAnnotation.h"
#include "DexCallSite.h"
#include "DexMethodHandle.h"
#include "DexUtil.h"
#include "IRCode.h"
#include "LiveRange.h"
#include "MethodUtil.h"
#include "Model.h"
#include "ReachableClasses.h"
#include "RefChecker.h"
#include "Resolver.h"
#include "Show.h"
#include "Trace.h"
#include "TypeReference.h"
#include "Walkers.h"

using namespace class_merging;

namespace {

// The class of the member that `method_handle`, held by code of `holder`
// (nullptr outside code), names, and the class of the member it resolves to.
std::array<const DexType*, 2> classes_of_method_handle(
    const DexMethodHandle* method_handle, const DexMethod* holder) {
  if (DexMethodHandle::isInvokeType(method_handle->type())) {
    const auto* method = resolve_method_handle(method_handle, holder);
    return {method_handle->methodref()->get_class(),
            method == nullptr ? nullptr : method->get_class()};
  }
  const auto* field = resolve_field_handle(method_handle);
  return {method_handle->fieldref()->get_class(),
          field == nullptr ? nullptr : field->get_class()};
}

} // namespace

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
    const RelaxedInitsByType& relaxed_inits, TypeSet& non_mergeables) {
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
      if (!method::is_optimizable(method)) {
        non_mergeables.insert(type);
        TRACE(CLMG, 5, "Cannot optimize dmethod on %s", SHOW(type));
        break;
      }
    }
    // Relaxed inits can instantiate a class whose constructors were all
    // inlined; class merging gives it forwarding constructors.
    if (!has_ctor && relaxed_inits.count(type) == 0) {
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

void MergeabilityChecker::exclude_unsupported_method_handle_refs(
    const DexMethodHandle* method_handle,
    const DexMethod* holder,
    TypeSet& non_mergeables) {
  std::vector<const DexType*> pinned_types;
  type_reference::gather_types_pinned_by_method_handle(method_handle,
                                                       pinned_types);
  for (const auto* type : pinned_types) {
    if (m_spec.merging_targets.count(type) > 0) {
      TRACE(CLMG, 5, "[non mergeable] pinned by a method handle in %s",
            SHOW(holder));
      non_mergeables.insert(type);
    }
  }
  for (const auto* type : classes_of_method_handle(method_handle, holder)) {
    if (type != nullptr && m_spec.merging_targets.count(type) > 0) {
      TRACE(CLMG, 5, "[non mergeable] named by a method handle in %s",
            SHOW(holder));
      non_mergeables.insert(type);
    }
  }
}

TypeSet MergeabilityChecker::exclude_unsupported_bytecode_refs_for(
    DexMethod* method) {
  TypeSet non_mergeables;
  auto* code = method->get_code();
  if (code == nullptr) {
    return non_mergeables;
  }

  // Collect the super-type constructors that relaxed inits of merging targets
  // invoke, in generated code too; classify_relaxed_inits decides which ones
  // class merging handles.
  auto relaxed_inits = constructor_analysis::find_relaxed_inits(
      method, [&](const DexType* type) {
        return m_spec.merging_targets.count(type) != 0u;
      });
  UnorderedMap<const IRInstruction*, const DexType*> invoke_types;
  UnorderedSet<const IRInstruction*> shared_invokes;
  for (const auto& relaxed_init : relaxed_inits) {
    auto [it, emplaced] = invoke_types.emplace(
        relaxed_init.invoke, relaxed_init.new_instance->get_type());
    if (!emplaced && it->second != relaxed_init.new_instance->get_type()) {
      shared_invokes.insert(relaxed_init.invoke);
    }
  }
  for (const auto& relaxed_init : relaxed_inits) {
    TRACE(CLMG, 5, "new-instance %s associated with invoke init %s in %s",
          SHOW(relaxed_init.new_instance), SHOW(relaxed_init.invoke),
          SHOW(method));
    bool shared = shared_invokes.contains(relaxed_init.invoke);
    m_relaxed_init_calls.update(
        relaxed_init.new_instance->get_type(),
        [&](const DexType*, RelaxedInitCalls& calls, bool) {
          calls.super_ctors.insert(relaxed_init.resolved_init);
          calls.callers.insert(method);
          calls.shares_invoke |= shared;
        });
  }

  if (m_generated.count(method->get_class()) != 0u) {
    return non_mergeables;
  }

  bool has_type_tag = m_spec.has_type_tag();
  std::vector<std::pair<IRInstruction*, const DexType*>>
      const_classes_to_verify;
  UnorderedSet<const IRInstruction*> const_classes_to_verify_set;
  auto& cfg = code->cfg();
  for (const auto& mie : InstructionIterable(cfg)) {
    auto* insn = mie.insn;

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

    // Any other string of an instruction, such as one that a call site passes
    // to its bootstrap method, can name a class or an array of it for
    // reflection too. Merging rewrites only the strings of const-string
    // instructions, so the class is kept from merging even with `replace`.
    if (!opcode::is_const_string(insn->opcode())) {
      std::vector<const DexString*> strings;
      insn->gather_strings(strings);
      for (const auto* string : strings) {
        auto* type =
            java_names::get_element_type_from_external_name(string->str());
        if ((type != nullptr) && m_spec.merging_targets.count(type) > 0) {
          non_mergeables.insert(type);
          TRACE(CLMG, 5, "[non mergeable] type like string unsafe: %s in %s",
                SHOW(insn), SHOW(method));
        }
      }
    }

    // With type tags, a Class among the bootstrap arguments of a call site is
    // checked like a const-class whose only use passes it to the bootstrap
    // method.
    if (insn->has_callsite()) {
      if (!has_type_tag) {
        continue;
      }
      auto* callsite = insn->get_callsite();
      auto* bootstrap = callsite->method_handle();
      bool safe_bootstrap = DexMethodHandle::isInvokeType(bootstrap->type()) &&
                            m_const_class_safe_types.count(
                                bootstrap->methodref()->get_class()) != 0u;
      for (const auto& arg : callsite->args()) {
        const auto* type_arg =
            dynamic_cast<const DexEncodedValueType*>(arg.get());
        if (type_arg == nullptr) {
          continue;
        }
        const auto* type = type::make_element_type_if_array(type_arg->type());
        if (m_spec.merging_targets.count(type) > 0 && !safe_bootstrap) {
          TRACE(CLMG, 5,
                "[non mergeable] Class bootstrap argument unsafe @ %s in %s",
                SHOW(insn), SHOW(method));
          non_mergeables.insert(type);
        }
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

  if (const_classes_to_verify.empty()) {
    return non_mergeables;
  }

  live_range::MoveAwareChains chains(
      cfg, /* ignore_unreachable */ false,
      [&](auto* insn) { return const_classes_to_verify_set.count(insn); });
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

  return non_mergeables;
}

void MergeabilityChecker::classify_relaxed_inits(Mergeability& mergeability) {
  auto& exclusions = mergeability.relaxed_init_exclusions;
  auto types =
      unordered_to_ordered_keys(m_relaxed_init_calls, compare_dextypes);
  const auto* init_name = DexString::make_string("<init>");
  for (const auto* type : types) {
    // Counted only for types that nothing else excludes.
    if (mergeability.non_mergeables.count(type) != 0u) {
      continue;
    }
    const auto& calls = m_relaxed_init_calls.at_unsafe(type);
    const auto& super_ctor_set = calls.super_ctors;
    auto exclude = [&](uint32_t* reason) {
      ++*reason;
      mergeability.non_mergeables.insert(type);
      TRACE(CLMG, 5, "[non mergeable] unsupported relaxed init of %s",
            SHOW(type));
    };
    if (!m_spec.generate_type_tag()) {
      exclude(&exclusions.type_tag_not_generated);
      continue;
    }
    if (super_ctor_set.count(nullptr) != 0u || calls.shares_invoke) {
      exclude(&exclusions.unsupported);
      continue;
    }
    std::vector<RelaxedInitForwarder> forwarders;
    UnorderedSet<const DexProto*> protos;
    uint32_t* reason = nullptr;
    for (auto* super_ctor :
         unordered_to_ordered(super_ctor_set, compare_dexmethods)) {
      if (!type::is_subclass(super_ctor->get_class(), type)) {
        reason = &exclusions.unsupported;
        break;
      }
      if (super_ctor->is_external() && !is_public(super_ctor) &&
          !is_protected(super_ctor)) {
        reason = &exclusions.inaccessible;
        break;
      }
      if (!m_ref_checker.check_method(super_ctor)) {
        reason = &exclusions.unsafe_refs;
        break;
      }
      // At most one forwarding constructor per proto, and an existing
      // constructor with that proto must already be that forwarder.
      auto* existing_ref = DexMethod::get_method(
          const_cast<DexType*>(type), init_name, super_ctor->get_proto());
      auto* existing_ctor =
          existing_ref == nullptr ? nullptr : existing_ref->as_def();
      if (!protos.insert(super_ctor->get_proto()).second ||
          (existing_ctor != nullptr &&
           !is_forwarding_ctor(existing_ctor, super_ctor))) {
        reason = &exclusions.ctor_conflict;
        break;
      }
      forwarders.push_back(RelaxedInitForwarder{super_ctor, existing_ctor});
    }
    if (reason != nullptr) {
      exclude(reason);
      continue;
    }
    mergeability.relaxed_inits.emplace(
        type,
        RelaxedInits{std::move(forwarders),
                     unordered_to_ordered(calls.callers, compare_dexmethods)});
  }
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

void MergeabilityChecker::exclude_method_handle_refs(TypeSet& non_mergeables) {
  // Merging moves the code of a mergeable into its merger, which has the same
  // superclass, and replaces or deletes its methods and fields. So a mergeable
  // whose code does something that depends on the class that holds it beyond
  // that class's superclass is not merged, and neither is the class of a
  // member that a method handle names or resolves to, which the handle must go
  // on naming. Unlike the other checks of bytecode, this one applies to the
  // code of generated classes too.
  TypeSet excluded = walk::parallel::methods<TypeSet, MergeContainers<TypeSet>>(
      m_scope, [this](DexMethod* method) {
        TypeSet result;
        auto* code = method->get_code();
        if (code == nullptr) {
          return result;
        }
        for (const auto& mie : InstructionIterable(code->cfg())) {
          auto* insn = mie.insn;
          if (depends_on_holder_class_beyond_superclass(insn) &&
              m_spec.merging_targets.count(method->get_class()) > 0) {
            TRACE(CLMG, 5, "[non mergeable] %s depends on its class in %s",
                  SHOW(insn), SHOW(method));
            result.insert(method->get_class());
          }
          for_each_method_handle(insn, [&](const DexMethodHandle* handle) {
            exclude_unsupported_method_handle_refs(handle, method, result);
          });
        }
        return result;
      });
  non_mergeables.insert(excluded.begin(), excluded.end());
}

void MergeabilityChecker::exclude_unsupported_static_value_method_handles(
    TypeSet& non_mergeables) {
  TypeSet non_mergeables_static_value =
      walk::parallel::fields<TypeSet, MergeContainers<TypeSet>>(
          m_scope, [this](DexField* field) {
            TypeSet field_non_mergeables;
            if (auto* value = field->get_static_value()) {
              std::vector<DexMethodHandle*> method_handles;
              value->gather_methodhandles(method_handles);
              for (const auto* method_handle : method_handles) {
                exclude_unsupported_method_handle_refs(
                    method_handle, /* holder */ nullptr, field_non_mergeables);
              }
            }
            return field_non_mergeables;
          });

  non_mergeables.insert(non_mergeables_static_value.begin(),
                        non_mergeables_static_value.end());
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

  auto maybe_insert_proto = [&](const DexProto* proto) {
    if (proto != nullptr) {
      maybe_insert(type::make_element_type_if_array(proto->get_rtype()));
      if (auto* args = proto->get_args()) {
        for (const auto* arg_type : *args) {
          maybe_insert(type::make_element_type_if_array(arg_type));
        }
      }
    }
  };
  auto maybe_insert_method = [&](const DexMethodRef* method) {
    if (method != nullptr) {
      // Check containing class
      maybe_insert(type::make_element_type_if_array(method->get_class()));
      // Check return type and parameter types
      maybe_insert_proto(method->get_proto());
    }
  };
  auto maybe_insert_field = [&](const DexFieldRef* field) {
    if (field != nullptr) {
      // Check containing class
      maybe_insert(type::make_element_type_if_array(field->get_class()));
      // Check field type
      maybe_insert(type::make_element_type_if_array(field->get_type()));
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
    maybe_insert_method(method_ev->method());
    break;
  }
  case DEVT_FIELD: {
    const auto* field_ev = dynamic_cast<const DexEncodedValueField*>(ev);
    maybe_insert_field(field_ev->field());
    break;
  }
  case DEVT_METHOD_HANDLE: {
    const auto* method_handle =
        dynamic_cast<const DexEncodedValueMethodHandle*>(ev)->methodhandle();
    if (DexMethodHandle::isInvokeType(method_handle->type())) {
      maybe_insert_method(method_handle->methodref());
    } else {
      maybe_insert_field(method_handle->fieldref());
    }
    break;
  }
  case DEVT_METHOD_TYPE: {
    const auto* method_type_ev =
        dynamic_cast<const DexEncodedValueMethodType*>(ev);
    maybe_insert_proto(method_type_ev->proto());
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

Mergeability MergeabilityChecker::get_mergeability() {
  Mergeability mergeability;
  auto& non_mergeables = mergeability.non_mergeables;
  size_t prev_size = 0;

  exclude_unsupported_bytecode(non_mergeables);
  TRACE(CLMG, 4, "Non mergeables (opcodes) %zu", non_mergeables.size());
  prev_size = non_mergeables.size();

  classify_relaxed_inits(mergeability);
  TRACE(CLMG,
        4,
        "Non mergeables (relaxed inits) %zu",
        non_mergeables.size() - prev_size);
  prev_size = non_mergeables.size();

  exclude_unsupported_cls_property(mergeability.relaxed_inits, non_mergeables);
  exclude_unsupported_static_value_method_handles(non_mergeables);
  TRACE(CLMG,
        4,
        "Non mergeables (no delete) %zu",
        non_mergeables.size() - prev_size);
  prev_size = non_mergeables.size();

  exclude_method_handle_refs(non_mergeables);
  TRACE(CLMG,
        4,
        "Non mergeables (method handles) %zu",
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

  return mergeability;
}
