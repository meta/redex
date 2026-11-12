/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "AnnoKill.h"

#include "AnnotationSignatureParser.h"
#include "ClassHierarchy.h"
#include "DexAnnotation.h"
#include "DexClass.h"
#include "DexUtil.h"
#include "PassManager.h"
#include "Resolver.h"
#include "Show.h"
#include "Timer.h"
#include "Trace.h"
#include "TypeUtil.h"
#include "Walkers.h"

constexpr const char* METRIC_ANNO_KILLED = "num_anno_killed";
constexpr const char* METRIC_ANNO_TOTAL = "num_anno_total";
constexpr const char* METRIC_CLASS_ASETS_CLEARED = "num_class_cleared";
constexpr const char* METRIC_CLASS_ASETS_TOTAL = "num_class_total";
constexpr const char* METRIC_METHOD_ASETS_CLEARED = "num_method_cleared";
constexpr const char* METRIC_METHOD_ASETS_TOTAL = "num_method_total";
constexpr const char* METRIC_METHODPARAM_ASETS_CLEARED =
    "num_methodparam_cleared";
constexpr const char* METRIC_METHODPARAM_ASETS_TOTAL = "num_methodparam_total";
constexpr const char* METRIC_FIELD_ASETS_CLEARED = "num_field_cleared";
constexpr const char* METRIC_FIELD_ASETS_TOTAL = "num_field_total";
constexpr const char* METRIC_SIGNATURES_KILLED = "num_signatures_killed";

AnnoKill::AnnoKill(Scope& scope,
                   bool only_force_kill,
                   bool kill_bad_signatures,
                   const AnnoNames& keep,
                   const AnnoNames& kill,
                   const AnnoNames& force_kill,
                   const UnorderedMap<std::string, std::vector<std::string>>&
                       class_hierarchy_keep_annos,
                   const UnorderedMap<std::string, std::vector<std::string>>&
                       annotated_keep_annos)
    : m_scope(scope),
      m_scope_set(scope.begin(), scope.end()),
      m_only_force_kill(only_force_kill),
      m_kill_bad_signatures(kill_bad_signatures) {
  TRACE(ANNO,
        2,
        "only_force_kill=%d kill_bad_signatures=%d",
        m_only_force_kill,
        kill_bad_signatures);
  // Load annotations that should not be deleted.
  TRACE(ANNO, 2, "Keep annotations count %zu", keep.size());
  for (const auto& anno_name : keep) {
    auto* anno_type = DexType::get_type(anno_name);
    TRACE(ANNO, 2, "Keep annotation type string %s", anno_name.c_str());
    if (anno_type != nullptr) {
      TRACE(ANNO, 2, "Keep annotation type %s", SHOW(anno_type));
      m_keep.insert(anno_type);
    } else {
      TRACE(ANNO, 2, "Cannot find annotation type %s", anno_name.c_str());
    }
  }

  // Load annotations we know and want dead.
  for (auto const& anno_name : kill) {
    DexType* anno = DexType::get_type(anno_name);
    TRACE(ANNO, 2, "Kill annotation type string %s", anno_name.c_str());
    if (anno != nullptr) {
      TRACE(ANNO, 2, "Kill anno: %s", SHOW(anno));
      m_kill.insert(anno);
    } else {
      TRACE(ANNO, 2, "Cannot find annotation type %s", anno_name.c_str());
    }
  }

  // Load annotations we know and want dead.
  for (auto const& anno_name : force_kill) {
    DexType* anno = DexType::get_type(anno_name);
    TRACE(ANNO, 2, "Force kill annotation type string %s", anno_name.c_str());
    if (anno != nullptr) {
      TRACE(ANNO, 2, "Force kill anno: %s", SHOW(anno));
      m_force_kill.insert(anno);
    } else {
      TRACE(ANNO, 2, "Cannot find annotation type %s", anno_name.c_str());
    }
  }

  // Populate class hierarchy keep map
  auto ch = build_type_hierarchy(m_scope);
  for (const auto& it : UnorderedIterable(class_hierarchy_keep_annos)) {
    auto* type = DexType::get_type(it.first);
    auto* type_cls = type != nullptr ? type_class(type) : nullptr;
    if (type_cls == nullptr) {
      continue;
    }

    TypeSet type_refs;
    get_all_children_or_implementors(ch, m_scope, type_cls, type_refs);
    type_refs.insert(type_cls->get_type());
    for (const auto& anno : it.second) {
      auto* anno_type = DexType::get_type(anno);
      for (const auto* type_ref : type_refs) {
        m_anno_class_hierarchy_keep[type_ref].insert(anno_type);
      }
    }
  }
  for (const auto& it : UnorderedIterable(m_anno_class_hierarchy_keep)) {
    for (const auto* type : UnorderedIterable(it.second)) {
      TRACE(ANNO,
            4,
            "anno_class_hier_keep: %s -> %s",
            it.first->get_name()->c_str(),
            type->get_name()->c_str());
    }
  }
  // Populate anno keep map
  for (const auto& it : UnorderedIterable(annotated_keep_annos)) {
    auto* type = DexType::get_type(it.first);
    for (const auto& anno : it.second) {
      auto* anno_type = DexType::get_type(anno);
      m_annotated_keep_annos[type].insert(anno_type);
    }
  }
}

namespace {
void gather_complete_referenced_annos(
    const AnnoKill::AnnoSet& initial_referenced_annos,
    const DexType* type,
    AnnoKill::AnnoSet* result) {
  auto* cls = type_class(type);
  if (cls == nullptr || !is_annotation(cls) || cls->is_external()) {
    return;
  }
  if (result->count(type) > 0) {
    return;
  }
  result->emplace(type);
  if (initial_referenced_annos.count(type) == 0) {
    TRACE(ANNO, 3,
          "Annotation type %s referenced indirectly from a referenced "
          "annotation; keeping.",
          SHOW(type));
  }
  auto process = [&](DexType* t) {
    auto* effective_type =
        const_cast<DexType*>(type::make_element_type_if_array(t));
    gather_complete_referenced_annos(initial_referenced_annos, effective_type,
                                     result);
  };
  // gather_types too broad here (that will keep too much). Just check return
  // type of members of the annotation (arguments should be disallowed) and
  // static field types.
  for (auto* m : cls->get_all_methods()) {
    process(m->get_proto()->get_rtype());
  }
  for (auto* f : cls->get_sfields()) {
    process(f->get_type());
  }
}
} // namespace

AnnoKill::AnnoSet AnnoKill::get_referenced_annos() {
  Timer timer{"get_referenced_annos"};

  AnnoKill::AnnoSet all_annos;

  // all used annotations
  auto annos_in_aset = [&](DexAnnotationSet* aset) {
    if (aset == nullptr) {
      return;
    }
    for (const auto& anno : aset->get_annotations()) {
      all_annos.insert(anno->type());
    }
  };

  for (const auto& cls : m_scope) {
    // all annotations referenced in classes
    annos_in_aset(cls->get_anno_set());

    // all classes marked as annotation
    if (is_annotation(cls)) {
      all_annos.insert(cls->get_type());
    }
  }

  // all annotations in methods
  walk::methods(m_scope, [&](DexMethod* method) {
    annos_in_aset(method->get_anno_set());
    auto* param_annos = method->get_param_anno();
    if (param_annos == nullptr) {
      return;
    }
    for (auto& pa : *param_annos) {
      annos_in_aset(pa.second.get());
    }
  });
  // all annotations in fields
  walk::fields(m_scope,
               [&](DexField* field) { annos_in_aset(field->get_anno_set()); });

  AnnoKill::AnnoSet referenced_annos;

  // mark an annotation as "unremovable" if a field is typed with that
  // annotation
  walk::fields(m_scope, [&](DexField* field) {
    // don't look at fields defined on the annotation itself
    auto* const field_cls_type = field->get_class();
    if (all_annos.count(field_cls_type) > 0) {
      return;
    }

    auto* const field_cls = type_class(field_cls_type);
    if (field_cls != nullptr && is_annotation(field_cls)) {
      return;
    }

    auto* ftype = field->get_type();
    if (all_annos.count(ftype) > 0) {
      TRACE(ANNO,
            3,
            "Field typed with an annotation type %s.%s:%s",
            SHOW(field->get_class()),
            SHOW(field->get_name()),
            SHOW(ftype));
      referenced_annos.insert(ftype);
    }
  });

  // mark an annotation as "unremovable" if a method signature contains a type
  // with that annotation
  walk::methods(m_scope, [&](DexMethod* meth) {
    // don't look at methods defined on the annotation itself
    auto* const meth_cls_type = meth->get_class();
    if (all_annos.count(meth_cls_type) > 0) {
      return;
    }

    auto* const meth_cls = type_class(meth_cls_type);
    if (meth_cls != nullptr && is_annotation(meth_cls)) {
      return;
    }

    const auto& has_anno = [&](const DexType* type) {
      if (all_annos.count(type) > 0) {
        TRACE(ANNO,
              3,
              "Method contains annotation type in signature %s.%s:%s",
              SHOW(meth->get_class()),
              SHOW(meth->get_name()),
              SHOW(meth->get_proto()));
        referenced_annos.insert(type);
      }
    };

    auto* const proto = meth->get_proto();
    has_anno(proto->get_rtype());
    for (const auto& arg : *proto->get_args()) {
      has_anno(arg);
    }
  });

  ConcurrentSet<const DexType*> concurrent_referenced_annos;
  auto add_concurrent_referenced_anno = [&](const DexType* t) {
    if (referenced_annos.count(t) == 0u) {
      concurrent_referenced_annos.insert(t);
    }
  };
  // mark an annotation as "unremovable" if any opcode references the annotation
  // type
  walk::parallel::opcodes(
      m_scope,
      [](DexMethod*) { return true; },
      [&add_concurrent_referenced_anno, &all_annos](DexMethod* meth,
                                                    IRInstruction* insn) {
        // don't look at methods defined on the annotation itself
        auto* const meth_cls_type = meth->get_class();
        if (all_annos.count(meth_cls_type) > 0) {
          return;
        }
        auto* const meth_cls = type_class(meth_cls_type);
        if (meth_cls != nullptr && is_annotation(meth_cls)) {
          return;
        }

        if (insn->has_type()) {
          const auto* type = insn->get_type();
          if (all_annos.count(type) > 0) {
            add_concurrent_referenced_anno(type);
            TRACE(ANNO,
                  3,
                  "Annotation referenced in type opcode\n\t%s.%s:%s - %s",
                  SHOW(meth->get_class()),
                  SHOW(meth->get_name()),
                  SHOW(meth->get_proto()),
                  SHOW(insn));
          }
        } else if (insn->has_field()) {
          auto* field = insn->get_field();
          auto* fdef = resolve_field(field,
                                     opcode::is_an_sfield_op(insn->opcode())
                                         ? FieldSearch::Static
                                         : FieldSearch::Instance);
          if (fdef != nullptr) {
            field = fdef;
          }

          bool referenced = false;
          auto* owner = field->get_class();
          if (all_annos.count(owner) > 0) {
            referenced = true;
            add_concurrent_referenced_anno(owner);
          }
          auto* type = field->get_type();
          if (all_annos.count(type) > 0) {
            referenced = true;
            add_concurrent_referenced_anno(type);
          }
          if (referenced) {
            TRACE(ANNO,
                  3,
                  "Annotation referenced in field opcode\n\t%s.%s:%s - %s",
                  SHOW(meth->get_class()),
                  SHOW(meth->get_name()),
                  SHOW(meth->get_proto()),
                  SHOW(insn));
          }
        } else if (insn->has_method()) {
          auto* method = insn->get_method();
          DexMethod* methdef =
              resolve_method_deprecated(method, opcode_to_search(insn), meth);
          if (methdef != nullptr) {
            method = methdef;
          }

          bool referenced = false;
          auto* owner = method->get_class();
          if (all_annos.count(owner) > 0) {
            referenced = true;
            add_concurrent_referenced_anno(owner);
          }
          auto* proto = method->get_proto();
          auto* rtype = proto->get_rtype();
          if (all_annos.count(rtype) > 0) {
            referenced = true;
            add_concurrent_referenced_anno(rtype);
          }
          auto* arg_list = proto->get_args();
          for (const auto& arg : *arg_list) {
            if (all_annos.count(arg) > 0) {
              referenced = true;
              add_concurrent_referenced_anno(arg);
            }
          }
          if (referenced) {
            TRACE(ANNO,
                  3,
                  "Annotation referenced in method opcode\n\t%s.%s:%s - %s",
                  SHOW(meth->get_class()),
                  SHOW(meth->get_name()),
                  SHOW(meth->get_proto()),
                  SHOW(insn));
          }
        }
      });
  insert_unordered_iterable(referenced_annos, concurrent_referenced_annos);
  // For each referenced annotation, make sure any annotations it references are
  // also tracked as referenced, so we don't end up with a dangling ref.
  AnnoKill::AnnoSet gathered;
  for (const auto* referenced : UnorderedIterable(referenced_annos)) {
    gather_complete_referenced_annos(referenced_annos, referenced, &gathered);
  }
  insert_unordered_iterable(referenced_annos, gathered);
  return referenced_annos;
}

AnnoKill::AnnoSet AnnoKill::get_removable_annotation_instances() {
  // Determine which annotation classes are removable.
  UnorderedSet<const DexType*> bannotations;
  for (auto* clazz : m_scope) {
    if ((clazz->get_access() & DexAccessFlags::ACC_ANNOTATION) == 0u) {
      continue;
    }

    auto* aset = clazz->get_anno_set();
    if (aset == nullptr) {
      continue;
    }

    auto& annos = aset->get_annotations();
    for (auto& anno : annos) {
      if (m_kill.count(anno->type()) != 0u) {
        bannotations.insert(clazz->get_type());
        TRACE(ANNO, 3, "removable annotation class %s",
              SHOW(clazz->get_type()));
      }
    }
  }
  return bannotations;
}

void AnnoKill::count_annotation(const DexAnnotation* da,
                                AnnoKillStats& stats) const {
  if (da->system_visible()) {
    if (traceEnabled(ANNO, 3)) {
      m_system_anno_map.fetch_add(da->type()->get_name()->str(), 1);
    }
    stats.visibility_system_count++;
  } else if (da->runtime_visible()) {
    if (traceEnabled(ANNO, 3)) {
      m_runtime_anno_map.fetch_add(da->type()->get_name()->str(), 1);
    }
    stats.visibility_runtime_count++;
  } else if (da->build_visible()) {
    if (traceEnabled(ANNO, 3)) {
      m_build_anno_map.fetch_add(da->type()->get_name()->str(), 1);
    }
    stats.visibility_build_count++;
  }
}

void AnnoKill::cleanup_aset(
    DexAnnotationSet* aset,
    const AnnoKill::AnnoSet& referenced_annos,
    AnnoKillStats& stats,
    const UnorderedSet<const DexType*>& keep_annos) const {
  stats.annotations += aset->size();
  auto& annos = aset->get_annotations();
  auto fn = [&](const auto& da) {
    auto anno_type = da->type();
    count_annotation(da.get(), stats);

    if (referenced_annos.count(anno_type) > 0) {
      TRACE(ANNO,
            3,
            "Annotation type %s with type referenced in "
            "code, skipping...\n\tannotation: %s",
            SHOW(anno_type),
            SHOW(da.get()));
      return false;
    }

    if (keep_annos.count(anno_type) > 0) {
      TRACE(ANNO, 4, "Prohibited from removing annotation %s", SHOW(da.get()));
      return false;
    }

    if (m_keep.count(anno_type) > 0) {
      TRACE(ANNO,
            3,
            "Exclude annotation type %s, "
            "skipping...\n\tannotation: %s",
            SHOW(anno_type),
            SHOW(da.get()));
      return false;
    }

    if (m_kill.count(anno_type) > 0) {
      TRACE(ANNO,
            3,
            "Annotation instance (type: %s) marked for removal, "
            "annotation: %s",
            SHOW(anno_type),
            SHOW(da.get()));
      stats.annotations_killed++;
      return true;
    }

    if (m_force_kill.count(anno_type) > 0) {
      TRACE(ANNO,
            3,
            "Annotation instance (type: %s) marked for forced removal, "
            "annotation: %s",
            SHOW(anno_type),
            SHOW(da.get()));
      stats.annotations_killed++;
      return true;
    }

    if (!m_only_force_kill && !da->system_visible()) {
      TRACE(ANNO, 3, "Killing annotation instance %s", SHOW(da.get()));
      stats.annotations_killed++;
      return true;
    }

    if (anno_type == type::dalvik_annotation_Signature()) {
      if (should_kill_bad_signature(da.get())) {
        stats.signatures_killed++;
        return true;
      }
    }

    return false;
  };
  annos.erase(std::remove_if(annos.begin(), annos.end(), fn), annos.end());
}

bool AnnoKill::should_kill_bad_signature(DexAnnotation* da) const {
  if (!m_kill_bad_signatures) {
    return false;
  }
  bool res = false;
  annotation_signature_parser::parse(da, [&](auto* devs, auto* sigcls) {
    if (sigcls && !sigcls->is_external() && !m_scope_set.count(sigcls)) {
      // Could not find the (non-external) class in Scope, so set signal
      // to kill
      sigcls = nullptr;
    }
    if (!sigcls) {
      TRACE(ANNO, 3, "Killing bad @Signature: %s", devs->string()->c_str());
      res = true;
      return false;
    }
    return true;
  });
  return res;
}

UnorderedSet<const DexType*> AnnoKill::build_anno_keep(
    DexAnnotationSet* aset) const {
  UnorderedSet<const DexType*> keep_list;
  for (const auto& anno : aset->get_annotations()) {
    auto it = m_annotated_keep_annos.find(anno->type());
    if (it != m_annotated_keep_annos.end()) {
      insert_unordered_iterable(keep_list, it->second);
    }
  }
  return keep_list;
}

bool AnnoKill::kill_annotations() {
  const auto& referenced_annos = get_referenced_annos();
  if (!m_only_force_kill) {
    m_kill = get_removable_annotation_instances();
  }

  Timer::scope("optimize classes", [&] {
    m_stats += walk::parallel::classes<AnnoKillStats>(
        m_scope, [&](auto* clazz) -> AnnoKillStats {
          AnnoKillStats local_stats{};
          DexAnnotationSet* aset = clazz->get_anno_set();
          if (!aset) {
            return local_stats;
          }
          auto keep_list = build_anno_keep(aset);
          {
            auto it = m_anno_class_hierarchy_keep.find(clazz->get_type());
            if (it != m_anno_class_hierarchy_keep.end()) {
              insert_unordered_iterable(keep_list, it->second);
            }
          }

          local_stats.class_asets++;
          cleanup_aset(aset, referenced_annos, local_stats, keep_list);
          if (aset->size() == 0) {
            TRACE(ANNO,
                  3,
                  "Clearing annotation for class %s",
                  SHOW(clazz->get_type()));
            clazz->clear_annotations();
            local_stats.class_asets_cleared++;
          }
          return local_stats;
        });
  });

  Timer::scope("optimize methods", [&] {
    m_stats += walk::parallel::methods<AnnoKillStats>(m_scope, [&](DexMethod*
                                                                       method) {
      // Method annotations
      AnnoKillStats local_stats{};

      auto* method_aset = method->get_anno_set();
      if (method_aset != nullptr) {
        local_stats.method_asets++;
        auto keep_list = build_anno_keep(method_aset);
        cleanup_aset(method_aset, referenced_annos, local_stats, keep_list);
        if (method_aset->size() == 0) {
          TRACE(ANNO,
                3,
                "Clearing annotations for method %s.%s:%s",
                SHOW(method->get_class()),
                SHOW(method->get_name()),
                SHOW(method->get_proto()));
          method->clear_annotations();
          local_stats.method_asets_cleared++;
        }
      }

      // Parameter annotations.
      auto* param_annos = method->get_param_anno();
      if (param_annos != nullptr) {
        local_stats.method_param_asets += param_annos->size();
        bool clear_pas = true;
        for (auto& pa : *param_annos) {
          auto& param_aset = pa.second;
          if (param_aset->size() == 0) {
            continue;
          }
          auto keep_list = build_anno_keep(param_aset.get());
          cleanup_aset(param_aset.get(), referenced_annos, local_stats,
                       keep_list);
          if (param_aset->size() == 0) {
            continue;
          }
          clear_pas = false;
        }
        if (clear_pas) {
          TRACE(ANNO,
                3,
                "Clearing parameter annotations for method parameters %s.%s:%s",
                SHOW(method->get_class()),
                SHOW(method->get_name()),
                SHOW(method->get_proto()));
          local_stats.method_param_asets_cleared += param_annos->size();
          method->release_param_anno();
        }
      }

      return local_stats;
    });
  });

  Timer::scope("optimize fields", [&] {
    m_stats +=
        walk::parallel::fields<AnnoKillStats>(m_scope, [&](DexField* field) {
          AnnoKillStats local_stats{};

          DexAnnotationSet* aset = field->get_anno_set();
          if (aset == nullptr) {
            return local_stats;
          }
          local_stats.field_asets++;
          auto keep_list = build_anno_keep(aset);
          cleanup_aset(aset, referenced_annos, local_stats, keep_list);
          if (aset->size() == 0) {
            TRACE(ANNO,
                  3,
                  "Clearing annotations for field %s.%s:%s",
                  SHOW(field->get_class()),
                  SHOW(field->get_name()),
                  SHOW(field->get_type()));
            field->clear_annotations();
            local_stats.field_asets_cleared++;
          }

          return local_stats;
        });
  });

  bool classes_removed = false;
  // We're done removing annotation instances, go ahead and remove annotation
  // classes.
  m_scope.erase(std::remove_if(m_scope.begin(),
                               m_scope.end(),
                               [&](DexClass* cls) {
                                 if (!is_annotation(cls)) {
                                   return false;
                                 }
                                 auto* type = cls->get_type();
                                 if (referenced_annos.count(type) != 0u) {
                                   return false;
                                 }
                                 if (m_keep.count(type) != 0u) {
                                   return false;
                                 }
                                 // If only_force_kill is set, we do not remove
                                 // other anno classes.
                                 if (m_only_force_kill &&
                                     m_force_kill.count(type) == 0u) {
                                   return false;
                                 }
                                 TRACE(ANNO, 3, "Removing annotation type: %s",
                                       SHOW(type));
                                 classes_removed = true;
                                 return true;
                               }),
                m_scope.end());

  if (traceEnabled(ANNO, 3)) {
    for (const auto& p : UnorderedIterable(m_build_anno_map)) {
      TRACE(ANNO,
            3,
            "Build anno: %zu, %s",
            p.second.load(),
            str_copy(p.first).c_str());
    }

    for (const auto& p : UnorderedIterable(m_runtime_anno_map)) {
      TRACE(ANNO,
            3,
            "Runtime anno: %zu, %s",
            p.second.load(),
            str_copy(p.first).c_str());
    }

    for (const auto& p : UnorderedIterable(m_system_anno_map)) {
      TRACE(ANNO,
            3,
            "System anno: %zu, %s",
            p.second.load(),
            str_copy(p.first).c_str());
    }
  }

  return classes_removed;
}

void AnnoKillPass::run_pass(DexStoresVector& stores,
                            ConfigFiles&,
                            PassManager& mgr) {

  auto scope = build_class_scope(stores);

  AnnoKill ak(scope,
              m_only_force_kill,
              m_kill_bad_signatures,
              m_keep_annos,
              m_kill_annos,
              m_force_kill_annos,
              m_class_hierarchy_keep_annos,
              m_annotated_keep_annos);
  bool classes_removed = ak.kill_annotations();

  if (classes_removed) {
    post_dexen_changes(scope, stores);
  }

  auto stats = ak.get_stats();

  TRACE(ANNO, 1, "AnnoKill report killed/total");
  TRACE(ANNO,
        1,
        "Annotations: %zu/%zu",
        stats.annotations_killed,
        stats.annotations);
  TRACE(ANNO,
        1,
        "Class Asets: %zu/%zu",
        stats.class_asets_cleared,
        stats.class_asets);
  TRACE(ANNO,
        1,
        "Method Asets: %zu/%zu",
        stats.method_asets_cleared,
        stats.method_asets);
  TRACE(ANNO,
        1,
        "MethodParam Asets: %zu/%zu",
        stats.method_param_asets_cleared,
        stats.method_param_asets);
  TRACE(ANNO,
        1,
        "Field Asets: %zu/%zu",
        stats.field_asets_cleared,
        stats.field_asets);

  TRACE(ANNO,
        3,
        "Total referenced Build Annos: %zu",
        stats.visibility_build_count);
  TRACE(ANNO,
        3,
        "Total referenced Runtime Annos: %zu",
        stats.visibility_runtime_count);
  TRACE(ANNO,
        3,
        "Total referenced System Annos: %zu",
        stats.visibility_system_count);
  TRACE(ANNO, 1, "@Signatures Killed: %zu", stats.signatures_killed);

  mgr.incr_metric(METRIC_ANNO_KILLED, stats.annotations_killed);
  mgr.incr_metric(METRIC_ANNO_TOTAL, stats.annotations);
  mgr.incr_metric(METRIC_CLASS_ASETS_CLEARED, stats.class_asets_cleared);
  mgr.incr_metric(METRIC_CLASS_ASETS_TOTAL, stats.class_asets);
  mgr.incr_metric(METRIC_METHOD_ASETS_CLEARED, stats.method_asets_cleared);
  mgr.incr_metric(METRIC_METHOD_ASETS_TOTAL, stats.method_asets);
  mgr.incr_metric(METRIC_METHODPARAM_ASETS_CLEARED,
                  stats.method_param_asets_cleared);
  mgr.incr_metric(METRIC_METHODPARAM_ASETS_TOTAL, stats.method_param_asets);
  mgr.incr_metric(METRIC_FIELD_ASETS_CLEARED, stats.field_asets_cleared);
  mgr.incr_metric(METRIC_FIELD_ASETS_TOTAL, stats.field_asets);
  mgr.incr_metric(METRIC_SIGNATURES_KILLED, stats.signatures_killed);
}

static AnnoKillPass s_pass;
