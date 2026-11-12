/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "VerticalMerging.h"

#include "AtomicStatCounter.h"
#include "ClassHierarchy.h"
#include "ConcurrentContainers.h"
#include "ConfigFiles.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "DexAnnotation.h"
#include "DexClass.h"
#include "DexUtil.h"
#include "EditableCfgAdapter.h"
#include "IROpcode.h"
#include "PassManager.h"
#include "RClass.h"
#include "Resolver.h"
#include "Show.h"
#include "Trace.h"
#include "TypeReference.h"
#include "TypeStringRewriter.h"
#include "TypeUtil.h"
#include "Walkers.h"

namespace {
using ClassMap = UnorderedMap<DexClass*, DexClass*>;
using MethodRefMap = UnorderedMap<DexMethodRef*, DexMethodRef*>;

bool is_internal_def(DexMethodRef* method) {
  if ((method == nullptr) || !method->is_def()) {
    return false;
  }
  auto* cls = type_class(method->get_class());
  if ((cls == nullptr) || cls->is_external()) {
    return false;
  }
  for (auto* m : cls->get_vmethods()) {
    if (m == method) {
      return true;
    }
  }
  for (auto* m : cls->get_dmethods()) {
    if (m == method) {
      return true;
    }
  }
  // Investigate the case if we hit it.
  not_reached_log(
      "%s is removed from its container class but its definition is not "
      "deleted.",
      SHOW(method));
}

/**
 * If DontMergeState is kStrict, then don't merge no matter this
 * type is merger or mergeable.
 * If DontMergeState is kConditional, then don't merge if this
 * type is mergeable.
 */
enum DontMergeState { kConditional, kStrict };
// `record_dont_merge_state` relies on these being the only two states: every
// raise is to `kStrict`, so concurrent raises cannot store a lower state.
static_assert(kConditional == 0 && kStrict == 1);

using DontMergeStatus = AtomicMap<const DexType*, DontMergeState>;

/**
 * Thread-safe. The state of a type only ever rises to kStrict, so the store
 * cannot lose a concurrent kStrict.
 */
void record_dont_merge_state(const DexType* type,
                             DontMergeState state,
                             DontMergeStatus* dont_merge_status) {
  const auto* element_type = type::get_element_type_if_array(type);
  if (element_type == nullptr) {
    // No class can be defined for a type that does not exist.
    return;
  }
  auto [current, emplaced] = dont_merge_status->emplace(element_type, state);
  if (!emplaced && *current < state) {
    current->store(state);
  }
}

struct TypeLikeStringStats {
  size_t annotation_refs{0};
  size_t code_refs{0};
  size_t static_field_refs{0};
};

size_t record_type_like_strings(const std::vector<const DexString*>& strings,
                                bool record_type_like_string_refs,
                                DontMergeStatus* dont_merge_status) {
  size_t refs{0};
  for (const auto* string : strings) {
    auto* type = java_names::get_element_type_from_external_name(string->str());
    if (type == nullptr) {
      continue;
    }
    refs++;
    if (record_type_like_string_refs) {
      record_dont_merge_state(type, kStrict, dont_merge_status);
    }
  }
  return refs;
}

/**
 * Check child class and parent class's DontMergeState and decide which class
 * should be merged into which class, or not merge at all.
 */
void check_dont_merge_list(const DontMergeStatus& dont_merge_status,
                           DexClass* child_cls,
                           DexClass* parent_cls,
                           ClassMap* mergeable_to_merger) {
  const auto& find_parent = dont_merge_status.find(parent_cls->get_type());
  const auto& find_child = dont_merge_status.find(child_cls->get_type());
  const auto& find_end = dont_merge_status.end();
  if (find_parent == find_end &&
      (find_child == find_end || find_child->second != kStrict)) {
    // Parent class is not referenced, and child class is not having kStrict
    // don't merge status, so we can merge parent class into child class.
    if (is_abstract(parent_cls) && !is_abstract(child_cls)) {
      for (auto* m : parent_cls->get_vmethods()) {
        if (is_abstract(m)) {
          auto* possible_child_method_ref = DexMethod::get_method(
              child_cls->get_type(), m->get_name(), m->get_proto());
          if ((possible_child_method_ref == nullptr) ||
              !is_internal_def(possible_child_method_ref)) {
            // We have parent class having abstract method without implementor,
            // it's a weird situation which we should avoid further merging.
            return;
          }
        }
      }
    }
    (*mergeable_to_merger)[parent_cls] = child_cls;
  } else if (find_child == find_end) {
    // Parent class is in don't remove set but child class is not. Check if we
    // can merge child class into parent class instead (which requires parent
    // class is not having kStrict don't merge status, and child class is
    // removable).
    if (find_parent->second != kStrict && can_delete(child_cls) &&
        can_rename(child_cls)) {
      if (is_abstract(child_cls)) {
        for (auto* method : child_cls->get_vmethods()) {
          if (method->get_code() != nullptr) {
            return;
          }
        }
        for (auto* method : child_cls->get_dmethods()) {
          if (method->get_code() != nullptr) {
            return;
          }
        }
      }
      (*mergeable_to_merger)[child_cls] = parent_cls;
    }
  }
}

/**
 * Gather IRinstructions in method that invoke-super methods in parent_mergeable
 * class.
 */
void get_call_to_super(
    DexMethod* method,
    DexClass* parent_mergeable,
    UnorderedMap<DexMethodRef*, std::vector<IRInstruction*>>* callee_to_insns) {
  if (method->get_code() == nullptr) {
    return;
  }
  auto& cfg = method->get_code()->cfg();
  for (auto& mie : cfg::InstructionIterable(cfg)) {
    auto* insn = mie.insn;
    if (!insn->has_method()) {
      continue;
    }
    auto* insn_method = insn->get_method();
    if (insn_method->get_class() == parent_mergeable->get_type() &&
        opcode::is_invoke_super(insn->opcode())) {
      (*callee_to_insns)[insn_method].push_back(insn);
      TRACE(VMERGE, 5, "Replacing super call %s", SHOW(insn));
    }
  }
}

using SuperCall = std::pair<DexMethodRef*, std::vector<IRInstruction*>>;
using InitCall = std::pair<DexMethod*, UnorderedSet<DexMethod*>>;

/**
 * Relocate callee methods in IRInstruction from mergeable class to merger
 * class. Modify IRInstruction accordingly.
 */
void handle_invoke_super(
    const UnorderedMap<DexMethodRef*, std::vector<IRInstruction*>>&
        callee_to_insns,
    DexClass* merger,
    DexClass* parent_mergeable) {
  auto super_calls = unordered_to_ordered(
      callee_to_insns, [](const SuperCall& call1, SuperCall& call2) {
        return compare_dexmethods(call1.first, call2.first);
      });
  for (const auto& callee_to_insn : super_calls) {
    auto* callee_ref = callee_to_insn.first;
    if (is_internal_def(callee_ref)) {
      //  invoke-super Parent.v => invoke-virtual Child.relocated_parent_v
      auto* callee = callee_ref->as_def();
      parent_mergeable->remove_method(callee);
      DexMethodSpec spec;
      spec.cls = merger->get_type();
      callee->change(spec, true /* rename_on_collision */);
      merger->add_method(callee);
      for (auto* insn : callee_to_insn.second) {
        redex_assert(insn->opcode() == OPCODE_INVOKE_SUPER);
        insn->set_opcode(OPCODE_INVOKE_VIRTUAL);
        insn->set_method(callee);
      }
    } else {
      // The only pure ref we need handle.
      // invoke-super Parent.v => invoke-super GrandParent.v
      auto* new_ref =
          DexMethod::make_method(parent_mergeable->get_super_class(),
                                 callee_ref->get_name(),
                                 callee_ref->get_proto());
      for (auto* insn : callee_to_insn.second) {
        insn->set_method(new_ref);
      }
    }
  }
}

/**
 * Relocate ctor methods called in IRCode from mergeable class to merger
 * class. Add dummy parameter to avoid method collision, Add 'const 0's before
 * call to ctors and modify IRinstruction accordingly.
 */
void handle_invoke_init(
    const UnorderedMap<DexMethod*, UnorderedSet<DexMethod*>>& init_callers,
    DexClass* merger,
    DexClass* mergeable) {
  auto initcalls = unordered_to_ordered(
      init_callers, [](const InitCall& call1, const InitCall& call2) {
        return compare_dexmethods(call1.first, call2.first);
      });
  for (const auto& callee_to_insn : initcalls) {
    DexMethod* callee = callee_to_insn.first;
    size_t num_orig_args = callee->get_proto()->get_args()->size();
    DexProto* new_proto = merger->get_type()->get_non_overlapping_proto(
        callee->get_name(), callee->get_proto());
    size_t num_add_args = new_proto->get_args()->size() - num_orig_args;
    size_t num_orig_src = num_orig_args + 1;
    callee->add_load_params(num_add_args);
    auto callers =
        unordered_to_ordered(callee_to_insn.second, compare_dexmethods);
    for (auto* caller : callers) {
      auto& cfg = caller->get_code()->cfg();
      auto ii = cfg::InstructionIterable(cfg);
      for (auto it = ii.begin(); it != ii.end(); ++it) {
        auto* insn = it->insn;
        if (insn->opcode() != OPCODE_INVOKE_DIRECT) {
          continue;
        }
        DexMethodRef* insn_method = insn->get_method();
        DexMethod* insn_method_def = insn_method->as_def();
        if (insn_method_def == callee) {
          size_t current_add = 0;
          insn->set_srcs_size(num_add_args + num_orig_src);
          while (current_add < num_add_args) {
            auto temp = cfg.allocate_temp();
            IRInstruction* new_insn = new IRInstruction(OPCODE_CONST);
            new_insn->set_literal(0);
            new_insn->set_dest(temp);
            cfg.insert_before(it, new_insn);
            insn->set_src(num_orig_src + current_add, temp);
            ++current_add;
          }
          insn->set_method(callee);
        }
      }
    }
    mergeable->remove_method(callee);
    DexMethodSpec spec;
    spec.cls = merger->get_type();
    spec.proto = new_proto;
    callee->change(spec, false /* rename_on_collision */);
    merger->add_method(callee);
  }
}

/**
 * Collect pairs of parent child classes that are mergeable with the following
 * constraints:
 *   1. Two classes need to be in same store (or primary or secondary dexes).
 *   2. Parent class has only one child class.
 *   3. Both classes are not external classes and not interface.
 *   4. Mergeable class is deletable.
 *   5. Both classes are not in kStrict don't merge state, and mergeable is not
 *      in any don't merge state.
 *   6. Classes are not throwable.
 */
ClassMap collect_can_merge(const Scope& scope,
                           const ClassHierarchy& ch,
                           const XStoreRefs& xstores,
                           const DontMergeStatus& dont_merge_status,
                           size_t* num_single_extend_pairs) {
  ClassMap mergeable_to_merger;
  auto throwables = get_all_children(ch, type::java_lang_Throwable());
  *num_single_extend_pairs = 0;
  for (DexClass* cls : scope) {
    if ((cls != nullptr) && !cls->is_external() && !is_interface(cls) &&
        can_delete(cls) && can_rename(cls)) {
      DexType* cls_type = cls->get_type();
      const auto& children_types = get_children(ch, cls_type);
      if (children_types.size() != 1) {
        continue;
      }
      const DexType* child_type = *children_types.begin();
      if ((throwables.count(cls_type) != 0u) ||
          (throwables.count(child_type) != 0u)) {
        continue;
      }
      if (!get_children(ch, child_type).empty()) {
        // TODO(suree404): we are skipping pairs that child class still have
        // their subclasses, but we might still be able to optimize this case.
        continue;
      }
      if (xstores.get_store_idx(child_type) !=
          xstores.get_store_idx(cls_type)) {
        // Check if cls_type and child_type is in the same dex, if not then
        // skip and proceed.
        continue;
      }
      DexClass* child_cls = type_class_internal(child_type);
      if (child_cls != nullptr) {
        (*num_single_extend_pairs)++;
        check_dont_merge_list(dont_merge_status, child_cls, cls,
                              &mergeable_to_merger);
      }
    }
  }
  return mergeable_to_merger;
}

size_t record_annotation(const Scope& scope,
                         bool record_type_like_string_refs,
                         DontMergeStatus* dont_merge_status) {
  AtomicStatCounter<size_t> type_like_string_refs{0};
  // Remove class if it is the type of an annotation.
  // TODO(suree404): Merge the classes even though it appears in annotation?
  walk::parallel::annotations(scope, [&](DexAnnotation* anno) {
    std::vector<const DexType*> types_in_anno;
    anno->gather_types(types_in_anno);
    for (const auto& type : types_in_anno) {
      record_dont_merge_state(type, kStrict, dont_merge_status);
    }
    if (anno->type() == type::dalvik_annotation_Signature() ||
        anno->type()->str() == "Lkotlin/Metadata;") {
      return;
    }
    std::vector<const DexString*> strings_in_anno;
    anno->gather_strings(strings_in_anno);
    type_like_string_refs += record_type_like_strings(
        strings_in_anno, record_type_like_string_refs, dont_merge_status);
  });
  return type_like_string_refs.load();
}

/**
 * 1. Analyze type usages.
 * 2. To simplify the method/field references updating, exclude the pure refs.
 * When ResolveRefsPass runs before the pass, the step should not drop many
 * mergeables.
 */
size_t record_code_reference(const Scope& scope,
                             bool record_type_like_string_refs,
                             DontMergeStatus* dont_merge_status) {
  AtomicStatCounter<size_t> type_like_string_refs{0};
  walk::parallel::opcodes(
      scope,
      [dont_merge_status, &type_like_string_refs, record_type_like_string_refs](
          DexMethod* /*method*/, IRInstruction* insn) {
        if (insn->has_type()) {
          const auto* type = type::get_element_type_if_array(insn->get_type());
          if (type == nullptr) {
            return;
          }
          if (opcode::is_instance_of(insn->opcode())) {
            // We don't want to merge class if either merger or
            // mergeable was ever accessed in instance_of to prevent
            // semantic error.
            record_dont_merge_state(type, kStrict, dont_merge_status);
            return;
          } else {
            DexClass* cls = type_class(type);
            if ((cls != nullptr) && !is_abstract(cls)) {
              // If a type is referenced and not an abstract type then
              // add it to don't use this type as mergeable.
              record_dont_merge_state(type, kConditional, dont_merge_status);
              TRACE(VMERGE, 9, "dont_merge %s as mergeable for type usage: %s",
                    SHOW(type), SHOW(insn));
            }
          }
        } else if (opcode::is_const_string(insn->opcode())) {
          auto* type = java_names::get_element_type_from_external_name(
              insn->get_string()->str());
          if (type != nullptr) {
            type_like_string_refs++;
            if (record_type_like_string_refs) {
              record_dont_merge_state(type, kStrict, dont_merge_status);
              TRACE(VMERGE, 9,
                    "dont_merge %s for type-like string reference: %s",
                    SHOW(type), SHOW(insn));
            }
          }
        } else if (insn->has_field()) {
          DexField* field = resolve_field(insn->get_field());
          if (field != nullptr) {
            bool resolve_differently =
                field->get_class() != insn->get_field()->get_class();
            if (resolve_differently) {
              // If a field reference need to be resolved, don't merge as
              // renaming it might cause problems.
              // If a field that can't be renamed is being referenced. Don't
              // merge it as we need the field and this field can't be renamed
              // if having collision.
              // TODO(suree404): can improve.
              record_dont_merge_state(field->get_class(), kStrict,
                                      dont_merge_status);
              record_dont_merge_state(insn->get_field()->get_class(), kStrict,
                                      dont_merge_status);
            }
          } else {
            record_dont_merge_state(insn->get_field()->get_class(),
                                    kConditional, dont_merge_status);
          }
        } else if (insn->has_method()) {
          auto* callee_ref = insn->get_method();
          if (opcode::is_invoke_super(insn->opcode())) {
            // The only allowed pure ref is in invoke-super.
            return;
          }
          if (!is_internal_def(callee_ref)) {
            record_dont_merge_state(callee_ref->get_class(), kStrict,
                                    dont_merge_status);
            TRACE(VMERGE, 9, "dont_merge %s for pure ref %s",
                  SHOW(callee_ref->get_class()), SHOW(callee_ref));
            DexMethod* callee =
                resolve_method_deprecated(callee_ref, MethodSearch::Any);
            if (callee != nullptr) {
              record_dont_merge_state(callee->get_class(), kStrict,
                                      dont_merge_status);
              TRACE(VMERGE, 9,
                    "dont_merge %s for it may be invoked as a pure ref %s",
                    SHOW(callee->get_class()), SHOW(callee_ref));
            }
          }
        }
      });
  return type_like_string_refs.load();
}

/**
 * When a method is native or not renamable, we can not change its signature.
 * Record a type as don't merge as a mergeable if it's used in a such method's
 * signature.
 */
void record_method_signature(const Scope& scope,
                             DontMergeStatus* dont_merge_status) {
  walk::parallel::methods(scope, [&](DexMethod* method) {
    if (is_native(method) || !can_rename(method)) {
      DexProto* proto = method->get_proto();
      record_dont_merge_state(proto->get_rtype(), kConditional,
                              dont_merge_status);
      DexTypeList* args = proto->get_args();
      for (const DexType* type : *args) {
        record_dont_merge_state(type, kConditional, dont_merge_status);
      }
    }
  });
}

void record_blocklist(const Scope& scope,
                      DontMergeStatus* dont_merge_status,
                      const std::vector<std::string>& blocklist) {
  if (blocklist.empty()) {
    return;
  }
  walk::classes(scope, [&](DexClass* cls) {
    // Mark class in blocklist as kStrict don't merge
    for (const auto& name : blocklist) {
      if (strstr(cls->get_name()->c_str(), name.c_str()) != nullptr) {
        TRACE(VMERGE,
              5,
              "%s | %s | %d",
              SHOW(cls),
              cls->rstate.str().c_str(),
              can_delete(cls));
        record_dont_merge_state(cls->get_type(), kStrict, dont_merge_status);
        return;
      }
    }
  });
}

/**
 * The resource passes find R classes by name and accept only static fields, a
 * simple <clinit> and a zero-argument constructor. Merging would give an R
 * class the other class's constructor with an added dummy parameter, or move R
 * fields into a class that is not recognized as an R class. So a pair is never
 * merged when either class is an R class.
 */
void record_r_classes(const Scope& scope,
                      const resources::RClassReader& r_class_reader,
                      DontMergeStatus* dont_merge_status) {
  walk::parallel::classes(scope, [&](DexClass* cls) {
    if (r_class_reader.has_r_class_name(cls)) {
      record_dont_merge_state(cls->get_type(), kStrict, dont_merge_status);
    }
  });
}

/**
 * Merging moves and rewrites the methods of both classes and every reference to
 * the class that goes away. A method excluded from optimization must stay
 * untouched, so neither its class nor any type it mentions in its signature,
 * code or annotations may take part in a merge.
 */
void record_no_optimizations(const Scope& scope,
                             DontMergeStatus* dont_merge_status) {
  walk::parallel::methods(scope, [&](DexMethod* method) {
    if (!method->rstate.no_optimizations()) {
      return;
    }
    std::vector<const DexType*> types;
    method->gather_types(types);
    for (const auto* type : types) {
      record_dont_merge_state(type, kStrict, dont_merge_status);
    }
  });
}

/**
 * Remove pair of classes from merging if they both have clinit function.
 */
void remove_both_have_clinit(ClassMap* mergeable_to_merger) {
  UnorderedBag<DexClass*> to_delete;
  for (const auto& pair : UnorderedIterable(*mergeable_to_merger)) {
    if (pair.first->get_clinit() != nullptr &&
        pair.second->get_clinit() != nullptr) {
      to_delete.insert(pair.first);
    }
  }
  for (DexClass* cls : UnorderedIterable(to_delete)) {
    mergeable_to_merger->erase(cls);
  }
}

/**
 * Remove pair of classes from merging if there are potentially name collision
 * for static method that can't be renamed.
 */
void remove_unrenamable_collisions(ClassMap* mergeable_to_merger) {
  UnorderedBag<DexClass*> to_delete;
  for (const auto& pair : UnorderedIterable(*mergeable_to_merger)) {
    auto* mergeable = pair.first;
    auto* merger = pair.second;
    for (auto* m : mergeable->get_dmethods()) {
      if (is_constructor(m) || method::is_clinit(m) || can_rename(m)) {
        continue;
      }
      auto* merger_method_ref = DexMethod::get_method(
          merger->get_type(), m->get_name(), m->get_proto());
      if (merger_method_ref != nullptr) {
        to_delete.insert(mergeable);
        break;
      }
    }
  }
  for (DexClass* cls : UnorderedIterable(to_delete)) {
    mergeable_to_merger->erase(cls);
  }
}

/**
 * Don't merge a class if it is a field's type and this field can't be
 * renamed, of if it appeared in a field value.
 */
size_t record_field_reference(const Scope& scope,
                              bool record_type_like_string_refs,
                              DontMergeStatus* dont_merge_status) {
  AtomicStatCounter<size_t> type_like_string_refs{0};
  walk::parallel::fields(scope, [&](DexField* field) {
    if (auto* value = field->get_static_value()) {
      std::vector<const DexString*> strings;
      value->gather_strings(strings);
      type_like_string_refs += record_type_like_strings(
          strings, record_type_like_string_refs, dont_merge_status);
    }
    if (is_static(field) && field->get_type() == type::java_lang_Class()) {
      // Checking type which might be stored as class in field.
      auto* value = field->get_static_value();
      if (value != nullptr && value->evtype() == DEVT_TYPE) {
        record_dont_merge_state(
            dynamic_cast<DexEncodedValueType*>(value)->type(), kStrict,
            dont_merge_status);
      }
    }
    if (!can_rename(field)) {
      record_dont_merge_state(field->get_type(), kConditional,
                              dont_merge_status);
      record_dont_merge_state(field->get_class(), kConditional,
                              dont_merge_status);
    }
  });
  return type_like_string_refs.load();
}

TypeLikeStringStats record_referenced(
    const Scope& scope,
    const std::vector<std::string>& blocklist,
    const resources::RClassReader& r_class_reader,
    bool record_type_like_string_refs,
    DontMergeStatus* dont_merge_status) {
  TypeLikeStringStats stats;
  stats.annotation_refs =
      record_annotation(scope, record_type_like_string_refs, dont_merge_status);
  stats.code_refs = record_code_reference(scope, record_type_like_string_refs,
                                          dont_merge_status);
  stats.static_field_refs = record_field_reference(
      scope, record_type_like_string_refs, dont_merge_status);
  record_method_signature(scope, dont_merge_status);
  record_blocklist(scope, dont_merge_status, blocklist);
  record_r_classes(scope, r_class_reader, dont_merge_status);
  record_no_optimizations(scope, dont_merge_status);
  return stats;
}

void move_fields(DexClass* from_cls, DexClass* to_cls) {
  DexType* target_cls_type = to_cls->get_type();
  auto fields = from_cls->get_all_fields();
  for (DexField* field : fields) {
    TRACE(VMERGE, 5, "move field : %s ", SHOW(field));
    from_cls->remove_field(field);
    DexFieldSpec field_spec;
    field_spec.cls = target_cls_type;
    field->change(field_spec, true /* rename_on_collision */);

    TRACE(VMERGE, 5, "field after : %s ", SHOW(field));
    to_cls->add_field(field);
  }
}

void update_references(const Scope& scope,
                       const UnorderedMap<DexType*, DexType*>& update_map,
                       const MethodRefMap& methodref_update_map) {
  walk::parallel::opcodes(
      scope,
      [&update_map](DexMethod* method) {
        // Ignore references in methods in classes that are going to be
        // removed.
        return update_map.count(method->get_class()) == 0u;
      },
      [&](DexMethod* method, IRInstruction* insn) {
        if (insn->has_type()) {
          const auto* ref_type = insn->get_type();
          DexType* type =
              const_cast<DexType*>(type::get_element_type_if_array(ref_type));
          auto find_mergeable = update_map.find(type);
          if (find_mergeable == update_map.end()) {
            return;
          }
          always_assert_log(insn->opcode() != OPCODE_NEW_INSTANCE,
                            "Vertical Merging: type reference still exists %s",
                            SHOW(insn));
          auto* merger_type = find_mergeable->second;
          if (type::is_array(ref_type)) {
            auto* array_merger_type = type::make_array_type(
                merger_type, type::get_array_level(ref_type));
            insn->set_type(array_merger_type);
          } else {
            insn->set_type(const_cast<DexType*>(merger_type));
          }
        } else if (insn->has_field()) {
          auto* insn_field = insn->get_field();
          always_assert_log(!update_map.count(insn_field->get_class()),
                            "Vertical Merging: Field reference still exists %s",
                            SHOW(insn));
        } else if (insn->has_method()) {
          auto* insn_method = insn->get_method();
          auto find = methodref_update_map.find(insn_method);
          if (find != methodref_update_map.end()) {
            insn->set_method(find->second);
          } else {
            always_assert_log(
                !update_map.count(insn_method->get_class()),
                "Vertical Merging: Method reference still exists %s in %s",
                SHOW(insn), SHOW(method));
          }
        }
      });
  // Update type refs in all field or method specs.
  type_reference::TypeRefUpdater updater(update_map);
  updater.update_methods_fields(scope);
}

void update_implements(DexClass* from_cls, DexClass* to_cls) {
  std::set<const DexType*, dextypes_comparator> new_intfs;
  TRACE(VMERGE, 5, "interface before : ");
  for (const auto& cls_intf : *to_cls->get_interfaces()) {
    TRACE(VMERGE, 5, "  %s", SHOW(cls_intf));
    new_intfs.emplace(cls_intf);
  }
  for (const auto& cls_intf : *from_cls->get_interfaces()) {
    new_intfs.emplace(cls_intf);
  }
  DexTypeList::ContainerType deque;

  TRACE(VMERGE, 5, "interface after : ");
  for (const auto& intf : new_intfs) {
    TRACE(VMERGE, 5, "  %s", SHOW(intf));
    deque.emplace_back(intf);
  }

  auto* implements = DexTypeList::make_type_list(std::move(deque));
  to_cls->set_interfaces(implements);
}

/**
 * Bring `ch` up to date after the merges, so that it matches
 * `build_type_hierarchy` of the resulting scope.
 */
void update_type_hierarchy(const ClassMap& mergeable_to_merger,
                           ClassHierarchy* ch) {
  for (const auto& [mergeable, merger] :
       UnorderedIterable(mergeable_to_merger)) {
    (*ch)[mergeable->get_super_class()].erase(mergeable->get_type());
    ch->erase(mergeable->get_type());
    (*ch)[merger->get_super_class()].insert(merger->get_type());
  }
}

void remove_merged(Scope& scope, const ClassMap& mergeable_to_merger) {
  if (mergeable_to_merger.empty()) {
    return;
  }
  for (const auto& pair : UnorderedIterable(mergeable_to_merger)) {
    TRACE(VMERGE,
          5,
          "Removing class | %s | merged into | %s",
          SHOW(pair.first),
          SHOW(pair.second));
  }

  scope.erase(remove_if(scope.begin(), scope.end(),
                        [&](DexClass* cls) {
                          return mergeable_to_merger.find(cls) !=
                                 mergeable_to_merger.end();
                        }),
              scope.end());
}

/**
 * Try to resolve the virtual calls on a mergeable type to be a method ref on
 * its merger. If fail, we remove the mergeable-merger pair.
 */
void resolve_virtual_calls_to_merger(const Scope& scope,
                                     ClassMap& mergeable_to_merger) {
  ConcurrentSet<DexClass*> excluded_mergeables;
  InsertOnlyConcurrentMap<IRInstruction*, DexMethodRef*> resolved_virtual_calls;
  walk::parallel::code(scope, [&](DexMethod* /* method */, IRCode& code) {
    cfg_adapter::iterate(&code, [&](MethodItemEntry& mie) {
      auto* insn = mie.insn;
      if (opcode::is_invoke_virtual(insn->opcode())) {
        auto* mergeable_method_ref = insn->get_method();
        auto* container = type_class(mergeable_method_ref->get_class());
        if (container == nullptr) {
          return cfg_adapter::LOOP_CONTINUE;
        }
        auto find_merger = mergeable_to_merger.find(container);
        if (find_merger != mergeable_to_merger.end() &&
            (excluded_mergeables.count(container) == 0u)) {
          auto* merger_method_ref = DexMethod::get_method(
              find_merger->second->get_type(), mergeable_method_ref->get_name(),
              mergeable_method_ref->get_proto());
          // Merger is the subclass.
          if (find_merger->second->get_super_class() == container->get_type()) {
            // XXX(fengliu): The possible overriding from subclasses of the
            // merger class is not checked because the case is excluded earlier
            // in collect_can_merge.
            if ((merger_method_ref != nullptr) &&
                is_internal_def(merger_method_ref)) {
              resolved_virtual_calls.emplace(insn, merger_method_ref);
            }
          } else { // Merger is the superclass.
            if (resolve_virtual_deprecated(find_merger->second,
                                           mergeable_method_ref->get_name(),
                                           mergeable_method_ref->get_proto()) !=
                nullptr) {
              merger_method_ref =
                  DexMethod::make_method(find_merger->second->get_type(),
                                         mergeable_method_ref->get_name(),
                                         mergeable_method_ref->get_proto());
              resolved_virtual_calls.emplace(insn, merger_method_ref);
            } else {
              // There is no instance of the mergeable class. So virtual calls
              // on the mergeable class should be invalid or unreachable. To
              // handle the "impossible" case, we can remove the virtual call or
              // simply not do the merging. Here we exclude the mergeable for
              // simplicity.
              excluded_mergeables.insert(container);
              TRACE(VMERGE, 5,
                    "Exclude a pair: virtual call %s is not resolvable to the "
                    "superclass %s",
                    SHOW(insn), SHOW(find_merger->second));
            }
          }
        }
      }
      return cfg_adapter::LOOP_CONTINUE;
    });
  });
  for (auto* cls : UnorderedIterable(excluded_mergeables)) {
    mergeable_to_merger.erase(cls);
  }
  for (auto& pair : UnorderedIterable(resolved_virtual_calls)) {
    auto* insn = pair.first;
    auto* container = type_class(insn->get_method()->get_class());
    if (mergeable_to_merger.count(container) != 0u) {
      insn->set_method(pair.second);
    }
  }
}

} // namespace

/**
 * For an invoke-super call on a parent's method
 *
 * a) When Parent.v is a pure ref, we update it to a method ref on grandparent
 * class.
 *
 *  invoke-super Parent.v => invoke-super GrandParent.v
 *
 * b) When Parent.v is a method definition, we relocate it to the child class
 * and rename it if conflict. These invocations can only be the merger class.
 *
 *  invoke-super Parent.v => invoke-virtual Child.relocated_parent_v
 *
 * At the time, below invocation can be different when child overrides the
 * method. These invocations should be resolved to child ref before running into
 * this.
 *
 *  invoke-virtual Parent.v => invoke-virtual Child.v
 *
 */
void VerticalMergingPass::change_super_calls(
    const ClassMap& mergeable_to_merger) {

  // Update invoke-super.
  // The invoke-super Parent.v could only be called from child class.
  auto process_subclass_methods = [&](DexClass* child, DexClass* parent) {
    UnorderedMap<DexMethodRef*, std::vector<IRInstruction*>> callee_to_insns;
    for (DexMethod* method : child->get_dmethods()) {
      get_call_to_super(method, parent, &callee_to_insns);
    }
    for (DexMethod* method : child->get_vmethods()) {
      get_call_to_super(method, parent, &callee_to_insns);
    }
    for (DexMethod* method : parent->get_dmethods()) {
      get_call_to_super(method, parent, &callee_to_insns);
    }
    handle_invoke_super(callee_to_insns, child, parent);
  };

  for (const auto& pair : UnorderedIterable(mergeable_to_merger)) {
    DexClass* merger = pair.second;
    DexClass* mergeable = pair.first;
    if (merger->get_super_class() == mergeable->get_type()) {
      process_subclass_methods(merger, mergeable);
    }
  }
}

/**
 * For an invoke-direct call on parent's constructor, move the method to
 * merger class and resolve conflicts.
 */
void VerticalMergingPass::change_init_calls(
    const Scope& scope, const ClassMap& mergeable_to_merger) {

  // Update invoke-direct constructor.
  // The invoke-direct Parent.<init> could be called from child or from parent's
  // constructors, or from any other code.

  ConcurrentMap<DexMethod*, UnorderedSet<DexMethod*>> concurrent_init_callers;
  walk::parallel::opcodes(scope, [&](DexMethod* method, IRInstruction* insn) {
    if (!insn->has_method()) {
      return;
    }
    auto* insn_method = insn->get_method();
    if (!method::is_init(insn_method)) {
      return;
    }
    auto* cls = type_class(insn_method->get_class());
    if (mergeable_to_merger.count(cls) == 0u) {
      return;
    }
    auto* insn_method_def = insn_method->as_def();
    redex_assert(insn_method_def);
    concurrent_init_callers.update(
        insn_method_def,
        [method](auto*, auto& set, auto) { set.insert(method); });
    TRACE(VMERGE, 5, "Changing init call %s", SHOW(insn));
  });

  for (const auto& pair : UnorderedIterable(mergeable_to_merger)) {
    DexClass* merger = pair.second;
    DexClass* mergeable = pair.first;
    if (merger->get_super_class() != mergeable->get_type()) {
      continue;
    }
    UnorderedMap<DexMethod*, UnorderedSet<DexMethod*>> init_callers;
    for (auto* ctor : mergeable->get_ctors()) {
      auto it = concurrent_init_callers.find(ctor);
      if (it != concurrent_init_callers.end()) {
        init_callers.emplace(ctor, std::move(it->second));
      }
    }
    handle_invoke_init(init_callers, merger, mergeable);
  }
}

void VerticalMergingPass::move_methods(DexClass* from_cls,
                                       DexClass* to_cls,
                                       bool is_merging_super_to_sub,
                                       MethodRefMap* methodref_update_map) {
  DexType* target_cls_type = to_cls->get_type();
  TRACE(VMERGE, 5, "Move methods from %s to %s:", SHOW(from_cls), SHOW(to_cls));
  auto move_method = [&](DexMethod* method, bool rename_on_collision) {
    from_cls->remove_method(method);
    DexMethodSpec spec;
    spec.cls = target_cls_type;
    method->change(spec, rename_on_collision);
    to_cls->add_method(method);
  };
  auto all_methods = from_cls->get_all_methods();
  for (DexMethod* method : all_methods) {
    TRACE(VMERGE, 5, "%s | %s | %s", SHOW(from_cls), SHOW(to_cls),
          SHOW(method));
    if (method::is_clinit(method)) {
      // We have removed pairs that both have clinit, so we can just move
      // clinit to target class.
      auto* target_method_ref = DexMethod::get_method(
          target_cls_type, method->get_name(), method->get_proto());
      if (target_method_ref != nullptr) {
        DexMethodRef::erase_method(target_method_ref);
      }
      move_method(method, false /* rename_on_collision */);
    } else if (is_merging_super_to_sub) {
      // Super class is being merged into subclass
      auto* target_method_ref = DexMethod::get_method(
          target_cls_type, method->get_name(), method->get_proto());
      if (target_method_ref != nullptr) {
        TRACE(VMERGE, 5, "ALREADY EXISTED METHODREF %s",
              SHOW(target_method_ref));
        if (!is_internal_def(target_method_ref)) {
          // the method resolved is not defined in target class, so the method
          // in mergeable class should have implementation for the method ref
          // in target class. Remove the method ref in target class and
          // substitute it with real method implementation.
          (*methodref_update_map)[target_method_ref] = method;
          DexMethodRef::erase_method(target_method_ref);
          TRACE(VMERGE, 5, "Erasing method ref.");
          move_method(method, false /* rename_on_collision */);
        } else {
          if (is_constructor(method)) {
            // Referenced constructors are already handled in
            // change_super_calls. The rest constructors are unused and they are
            // discarded.
            continue;
          } else if (!method->is_virtual()) {
            // Static or direct method. Safe to move
            if (can_rename(method)) {

              move_method(method, true /* rename_on_collision */);
            } else {
              move_method(method, false /* rename_on_collision */);
            }
          } else {
            // Otherwise the method is virtual and child class overrides the
            // method in parent, we shouldn't care for the method as it is dead
            // code. But we need to combine annotation of method and their
            // reference state into merger class's method because we are
            // basically merging two methods.
            auto* target_method_def = target_method_ref->as_def();
            target_method_def->combine_annotations_with(method);
            target_method_def->rstate.join_with(method->rstate);
            (*methodref_update_map)[method] = target_method_ref;
          }
        }
      } else {
        always_assert(!is_abstract(method) || is_abstract(to_cls));
        move_method(method, false /* rename_on_collision */);
      }
    } else {
      // Subclass is being merged into super class. Just discard the instance
      // methods as they should not be referenced, otherwise they won't be
      // mergeable. Move the non-constructor static methods from subclass to
      // super class.
      if (is_static(method) && !is_constructor(method)) {
        if (can_rename(method)) {
          move_method(method, true /* rename_on_collision */);
        } else {
          move_method(method, false /* rename_on_collision */);
        }
      }
    }
  }
}

void VerticalMergingPass::merge_classes(const Scope& scope,
                                        const ClassMap& mergeable_to_merger) {
  UnorderedMap<DexType*, DexType*> update_map;
  // To store the needed changes from `Mergeable.method` to `Merger.method`.
  MethodRefMap methodref_update_map;

  change_super_calls(mergeable_to_merger);
  change_init_calls(scope, mergeable_to_merger);

  for (const auto& pair : UnorderedIterable(mergeable_to_merger)) {
    DexClass* merger = pair.second;
    DexClass* mergeable = pair.first;
    bool is_merging_super_to_sub =
        merger->get_super_class() == mergeable->get_type();
    move_fields(mergeable, merger);
    move_methods(mergeable, merger, is_merging_super_to_sub,
                 &methodref_update_map);
    if (is_merging_super_to_sub) {
      // We are merging super class into sub class, set merger's super class to
      // mergeable's super class.
      merger->set_super_class(mergeable->get_super_class());
      update_implements(mergeable, merger);
    }
    update_map[mergeable->get_type()] = merger->get_type();
    // Combine mergeable classes annotation and reference state with those
    // of merger classes.
    merger->combine_annotations_with(mergeable);
    merger->rstate.join_with(mergeable->rstate);
  }
  rewriter::TypeStringMap type_string_map;
  for (const auto& [old_type, new_type] : UnorderedIterable(update_map)) {
    type_string_map.add_type_name(old_type->get_name(), new_type->get_name());
  }
  rewriter::rewrite_dalvik_annotation_signature(scope, type_string_map);
  update_references(scope, update_map, methodref_update_map);
}

size_t VerticalMergingPass::merge_round(
    Scope& scope,
    const XStoreRefs& xstores,
    ClassHierarchy* ch,
    const resources::RClassReader& r_class_reader,
    PassManager& mgr,
    bool first_round) {
  DontMergeStatus dont_merge_status;
  auto type_like_string_stats =
      record_referenced(scope, m_blocklist, r_class_reader,
                        !m_unsafe_ignore_type_like_strings, &dont_merge_status);
  size_t num_single_extend;
  auto mergeable_to_merger = collect_can_merge(
      scope, *ch, xstores, dont_merge_status, &num_single_extend);

  remove_both_have_clinit(&mergeable_to_merger);
  remove_unrenamable_collisions(&mergeable_to_merger);
  resolve_virtual_calls_to_merger(scope, mergeable_to_merger);

  merge_classes(scope, mergeable_to_merger);
  update_type_hierarchy(mergeable_to_merger, ch);
  remove_merged(scope, mergeable_to_merger);
  if (slow_invariants_debug) {
    always_assert(*ch == build_type_hierarchy(scope));
  }
  if (first_round) {
    mgr.set_metric("num_single_extend", num_single_extend);
    mgr.set_metric("num_type_like_string_annotation_refs",
                   type_like_string_stats.annotation_refs);
    mgr.set_metric("num_type_like_string_code_refs",
                   type_like_string_stats.code_refs);
    mgr.set_metric("num_type_like_string_static_field_refs",
                   type_like_string_stats.static_field_refs);
  }
  return mergeable_to_merger.size();
}

void VerticalMergingPass::run_pass(DexStoresVector& stores,
                                   ConfigFiles& conf,
                                   PassManager& mgr) {
  auto scope = build_class_scope(stores);
  XStoreRefs xstores(stores, conf.normal_primary_dex());
  auto ch = build_type_hierarchy(scope);
  resources::RClassReader r_class_reader(conf.get_global_config());
  size_t round_merged = merge_round(scope, xstores, &ch, r_class_reader, mgr,
                                    /* first_round */ true);
  size_t num_merged = round_merged;
  size_t num_rounds = 1;
  while (m_merge_whole_chains && round_merged > 0) {
    round_merged = merge_round(scope, xstores, &ch, r_class_reader, mgr,
                               /* first_round */ false);
    num_merged += round_merged;
    num_rounds++;
  }
  post_dexen_changes(scope, stores);
  mgr.set_metric("num_merged", num_merged);
  mgr.set_metric("num_rounds", num_rounds);
}

static VerticalMergingPass s_pass;
