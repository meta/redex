/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "Reachability.h"

#include <atomic>
#include <cinttypes>

#include "AnnotationSignatureParser.h"
#include "BinarySerialization.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexAnnotation.h"
#include "DexUtil.h"
#include "MethodUtil.h"
#include "PassManager.h"
#include "ProguardConfiguration.h"
#include "ReachableClasses.h"
#include "Resolver.h"
#include "Show.h"
#include "ThrowPropagationImpl.h"
#include "Timer.h"
#include "Trace.h"
#include "TypeUtil.h"
#include "Walkers.h"
#include "WorkQueue.h"

using namespace reachability;

namespace bs = binary_serialization;
namespace mog = method_override_graph;

namespace {

static ReachableObject SEED_SINGLETON{};

GatherMieFunction default_gather_mie_with_gather_methods =
    std::bind(&MethodReferencesGatherer::default_gather_mie,
              std::placeholders::_1,
              std::placeholders::_2,
              std::placeholders::_3,
              /* gather_methods */ true);
} // namespace

namespace reachability {

bool consider_dynamically_referenced(const DexClass* cls) {
  return !root(cls) && !is_interface(cls) && !is_annotation(cls);
}

std::ostream& operator<<(std::ostream& os, const ReachableObject& obj) {
  switch (obj.type) {
  case ReachableObjectType::ANNO:
    return os << show_deobfuscated(obj.anno->type());
  case ReachableObjectType::CLASS:
    return os << show_deobfuscated(obj.cls);
  case ReachableObjectType::FIELD:
    return os << show_deobfuscated(obj.field);
  case ReachableObjectType::METHOD:
    return os << show_deobfuscated(obj.method);
  case ReachableObjectType::INSTANTIABLE:
    return os << "instantiable(" << show_deobfuscated(obj.cls) << ")";
  case ReachableObjectType::METHOD_REFERENCES_GATHERER_INSTANTIABLE:
    return os << "method-references-gatherer-instantiable("
              << show_deobfuscated(obj.cls) << ")";
  case ReachableObjectType::RETURNS:
    return os << "returns(" << show_deobfuscated(obj.method) << ")";
  case ReachableObjectType::METHOD_REFERENCES_GATHERER_RETURNING:
    return os << "method-references-gatherer-returning("
              << show_deobfuscated(obj.method) << ")";
  case ReachableObjectType::SEED: {
    if (obj.keep_reason != nullptr) {
      return os << *obj.keep_reason;
    }
    return os << "<SEED>";
  }
  }
}

bool RootSetMarker::is_canary(const DexClass* cls) {
  return strstr(cls->get_name()->c_str(), "Canary") != nullptr;
}

bool RootSetMarker::should_mark_cls(const DexClass* cls) {
  return root(cls) || is_canary(cls);
}

void RootSetMarker::mark_all_as_seed(const Scope& scope) {
  walk::parallel::classes(scope, [&](const DexClass* cls) {
    TRACE(REACH, 3, "Visiting seed: %s", SHOW(cls));
    push_seed(cls);

    for (auto const& f : cls->get_ifields()) {
      TRACE(REACH, 3, "Visiting seed: %s", SHOW(f));
      push_seed(f, Condition::ClassRetained);
    }
    for (auto const& f : cls->get_sfields()) {
      TRACE(REACH, 3, "Visiting seed: %s", SHOW(f));
      push_seed(f, Condition::ClassRetained);
    }
    for (auto const& m : cls->get_dmethods()) {
      TRACE(REACH, 3, "Visiting seed: %s", SHOW(m));
      push_seed(m, Condition::ClassRetained);
    }
    for (auto const& m : cls->get_vmethods()) {
      TRACE(REACH, 3, "Visiting seed: %s (root)", SHOW(m));
      push_seed(m, Condition::ClassRetained);
    }
  });
}

bool RootSetMarker::is_rootlike_clinit(const DexMethod* m) {
  return method::is_clinit(m) && ((m->get_code() == nullptr) ||
                                  !method::is_trivial_clinit(*m->get_code()));
}

bool RootSetMarker::is_rootlike_init(const DexMethod* m) const {
  // We keep the parameterless constructor, in case it's constructed via
  // .class or Class.forName()
  // if m_remove_no_argument_constructors, make an exception. This is only
  // used for testing
  return !m_remove_no_argument_constructors && method::is_argless_init(m);
}

/*
 * Initializes the root set by marking and pushing nodes onto the work queue.
 * Also conditionally marks class member seeds.
 */
void RootSetMarker::mark(const Scope& scope) {
  walk::parallel::classes(scope, [&](const DexClass* cls) {
    if (should_mark_cls(cls)) {
      TRACE(REACH, 3, "Visiting seed: %s", SHOW(cls));
      push_seed(cls);
    }
    // Applying the same exclusions as the retired DelInitPass
    auto relaxed =
        m_relaxed_keep_class_members && consider_dynamically_referenced(cls);
    // push_seed for an ifield or vmethod
    auto push_iv_seed = [&](auto* m) {
      if (relaxed) {
        push_seed(m, Condition::ClassDynamicallyReferenced);
        push_seed(m, Condition::ClassInstantiable);
      } else {
        push_seed(m, Condition::ClassRetained);
      }
    };
    // push_seed for a dmethod
    auto push_d_seed = [&](auto* m) {
      push_seed(m, (m->get_code() && !method::is_clinit(m) && relaxed)
                       ? Condition::ClassDynamicallyReferenced
                       : Condition::ClassRetained);
    };
    for (auto const& f : cls->get_ifields()) {
      if (root(f)) {
        TRACE(REACH, 3, "Visiting seed: %s", SHOW(f));
        push_iv_seed(f);
      } else if (is_volatile(f) && !m_relaxed_keep_class_members) {
        TRACE(REACH, 3, "Visiting seed (volatile): %s", SHOW(f));
        push_iv_seed(f);
      }
    }
    for (auto const& f : cls->get_sfields()) {
      if (root(f)) {
        TRACE(REACH, 3, "Visiting seed: %s", SHOW(f));
        push_seed(f, Condition::ClassRetained);
      }
    }
    for (auto const& m : cls->get_dmethods()) {
      if (is_rootlike_clinit(m)) {
        TRACE(REACH, 3, "Visiting seed (root-like clinit): %s", SHOW(m));
        push_d_seed(m);
      } else if (is_rootlike_init(m)) {
        TRACE(REACH, 3, "Visiting seed (root-like init): %s", SHOW(m));
        push_d_seed(m);
      } else if (root(m)) {
        TRACE(REACH, 3, "Visiting seed: %s", SHOW(m));
        push_d_seed(m);
      }
    }
    for (auto const& m : cls->get_vmethods()) {
      if (root(m)) {
        TRACE(REACH, 3, "Visiting seed: %s (root)", SHOW(m));
        push_iv_seed(m);
      }
    }
  });

  mark_external_method_overriders();
}

void RootSetMarker::mark_with_exclusions(
    const Scope& scope,
    const ConcurrentSet<const DexClass*>& excluded_classes,
    const ConcurrentSet<const DexMethod*>& excluded_methods) {
  auto excluded = [&excluded_classes, &excluded_methods](auto* item) -> bool {
    if constexpr (std::is_same_v<decltype(item), const DexClass*>) {
      return excluded_classes.find(item) != excluded_classes.end();
    } else if constexpr (std::is_same_v<decltype(item), const DexMethod*>) {
      return excluded_methods.find(item) != excluded_methods.end();
    } else {
      static_assert(std::is_same_v<decltype(item), const DexField*>);
      return false;
    }
  };

  walk::parallel::classes(scope, [&](const DexClass* cls) {
    if (should_mark_cls(cls) && !excluded(cls)) {
      TRACE(REACH, 3, "Visiting seed: %s", SHOW(cls));
      push_seed(cls);
    }
    for (const auto* f : cls->get_ifields()) {
      if ((root(f) || is_volatile(f)) && !excluded(f)) {
        TRACE(REACH, 3, "Visiting seed: %s", SHOW(f));
        push_seed(f, Condition::ClassRetained);
      }
    }
    for (const auto* f : cls->get_sfields()) {
      if (root(f) && !excluded(f)) {
        TRACE(REACH, 3, "Visiting seed: %s", SHOW(f));
        push_seed(f, Condition::ClassRetained);
      }
    }
    for (const auto* m : cls->get_dmethods()) {
      if ((root(m) || is_rootlike_clinit(m) || is_rootlike_init(m)) &&
          !excluded(m)) {
        TRACE(REACH, 3, "Visiting seed: %s", SHOW(m));
        push_seed(m, Condition::ClassRetained);
      }
    }
    for (const auto* m : cls->get_vmethods()) {
      if (root(m) && !excluded(m)) {
        TRACE(REACH, 3, "Visiting seed: %s (root)", SHOW(m));
        push_seed(m, Condition::ClassRetained);
      }
    }
  });

  mark_external_method_overriders();
}

void RootSetMarker::push_seed(const DexClass* cls) {
  if (cls == nullptr) {
    return;
  }
  record_is_seed(cls);
  m_reachable_objects->mark(cls);
  m_root_set->emplace(cls);
}

void RootSetMarker::push_seed(const DexField* field, Condition condition) {
  if (field == nullptr) {
    return;
  }
  switch (condition) {
  case Condition::ClassRetained:
    m_cond_marked->if_class_retained.fields.insert(field);
    break;
  case Condition::ClassDynamicallyReferenced:
    m_cond_marked->if_class_dynamically_referenced.fields.insert(field);
    break;
  case Condition::ClassInstantiable:
    m_cond_marked->if_class_instantiable.fields.insert(field);
    break;
  default:
    not_reached();
  }
}

void RootSetMarker::push_seed(const DexMethod* method, Condition condition) {
  if (method == nullptr) {
    return;
  }
  switch (condition) {
  case Condition::ClassRetained:
    m_cond_marked->if_class_retained.methods.insert(method);
    break;
  case Condition::ClassDynamicallyReferenced:
    m_cond_marked->if_class_dynamically_referenced.methods.insert(method);
    break;
  case Condition::ClassInstantiable:
    m_cond_marked->if_class_instantiable.methods.insert(method);
    break;
  default:
    not_reached();
  }
}

template <class Seed>
void RootSetMarker::record_is_seed(Seed* seed) {
  if (m_record_reachability) {
    redex_assert(seed != nullptr);
    m_reachable_objects->record_is_seed(seed);
  }
}

/*
 * Mark as seeds all methods that override or implement an external method.
 */
void RootSetMarker::mark_external_method_overriders() {
  UnorderedSet<const DexMethod*> visited;
  for (const auto& pair : UnorderedIterable(m_method_override_graph.nodes())) {
    const auto* method = pair.first;
    if (!method->is_external() || (visited.count(method) != 0u)) {
      continue;
    }
    const auto& overriding_methods =
        mog::get_overriding_methods(m_method_override_graph, method);
    for (const auto* overriding : UnorderedIterable(overriding_methods)) {
      // Avoid re-visiting methods found in overriding sets since we would
      // already have conditionally marked all their children.
      visited.emplace(overriding);
      if (!overriding->is_external()) {
        TRACE(REACH, 3, "Visiting seed: %s (implements %s)", SHOW(overriding),
              SHOW(method));
        push_seed(overriding, Condition::ClassInstantiable);
      }
    }
  }
}

/*
 * Marks :obj and pushes its immediately reachable neighbors onto the local
 * task queue of the current worker.
 */
void TransitiveClosureMarkerWorker::visit(const ReachableObject& obj) {
  switch (obj.type) {
  case ReachableObjectType::CLASS:
    visit_cls(obj.cls);
    break;
  case ReachableObjectType::FIELD:
    visit_field_ref(obj.field);
    break;
  case ReachableObjectType::METHOD:
    visit_method_ref(obj.method);
    break;
  case ReachableObjectType::INSTANTIABLE:
    visit_instantiable(obj.cls);
    break;
  case ReachableObjectType::METHOD_REFERENCES_GATHERER_INSTANTIABLE:
    visit_method_references_gatherer_instantiable(obj.cls);
    break;
  case ReachableObjectType::RETURNS:
    visit_returns(dynamic_cast<const DexMethod*>(obj.method));
    break;
  case ReachableObjectType::METHOD_REFERENCES_GATHERER_RETURNING:
    visit_method_references_gatherer_returning(
        dynamic_cast<const DexMethod*>(obj.method));
    break;
  case ReachableObjectType::ANNO:
  case ReachableObjectType::SEED:
    not_reached_log("Unexpected ReachableObject type");
  }
}

template <class Parent, class InputIt>
void TransitiveClosureMarkerWorker::push(const Parent* parent,
                                         InputIt begin,
                                         InputIt end) {
  for (auto it = begin; it != end; ++it) {
    push(parent, *it);
  }
}

template <class Parent>
void TransitiveClosureMarkerWorker::push(const Parent* parent,
                                         const DexType* type) {
  type = type::make_element_type_if_array(type);
  push(parent, type_class(type));
}

void TransitiveClosureMarkerWorker::push(const DexMethodRef* parent,
                                         const DexType* type) {
  type = type::make_element_type_if_array(type);
  push(parent, type_class(type));
}

template <class Parent>
void TransitiveClosureMarkerWorker::push(const Parent* parent,
                                         const DexClass* cls) {
  if (!cls) {
    return;
  }
  if (!m_shared_state->scope_set.count(cls)) {
    if (!cls->is_external()) {
      TRACE(REACH, 2,
            "Warning: push([%s], class [%s]) where child class is not external "
            "and not in scope!",
            SHOW(parent), SHOW(cls));
    }
    return;
  }
  record_reachability(parent, cls);
  if (!m_shared_state->reachable_objects->mark(cls)) {
    return;
  }
  m_worker_state->push_task(ReachableObject(cls));
}

template <class Parent>
void TransitiveClosureMarkerWorker::push(const Parent* parent,
                                         const DexFieldRef* field) {
  if (!field) {
    return;
  }
  record_reachability(parent, field);
  if (!m_shared_state->reachable_objects->mark(field)) {
    return;
  }
  const auto* f = field->as_def();
  if (f) {
    gather_and_push(f);
  }
  m_worker_state->push_task(ReachableObject(field));
}

template <class Parent>
void TransitiveClosureMarkerWorker::push(const Parent* parent,
                                         const DexMethodRef* method) {
  if (!method) {
    return;
  }

  record_reachability(parent, method);
  if (!m_shared_state->reachable_objects->mark(method)) {
    return;
  }
  m_worker_state->push_task(ReachableObject(method));
}

void TransitiveClosureMarkerWorker::push(const DexMethodRef* parent,
                                         const DexMethodRef* method) {
  this->template push<DexMethodRef>(parent, method);
}

void TransitiveClosureMarkerWorker::push_if_class_instantiable(
    const DexMethod* method) {
  if ((method == nullptr) ||
      m_shared_state->reachable_objects->marked(method)) {
    return;
  }
  TRACE(REACH, 4,
        "Conditionally marking method if declaring class is instantiable: %s",
        SHOW(method));
  auto* clazz = type_class(method->get_class());
  m_shared_state->cond_marked->if_class_instantiable.methods.insert(method);
  // If :clazz is already known to be instantiable, then we cannot count on
  // instantiable(DexClass*) to have moved the
  // conditionally-if-instantiable-marked methods into the actually-marked ones
  // -- we have to do it ourselves. Note that we must do this check after adding
  // :method to m_cond_marked to avoid a race condition where we add to
  // m_cond_marked after instantiable(DexClass*) has finished moving its
  // contents over to m_reachable_objects.
  if (m_shared_state->reachable_aspects->instantiable_types.count(clazz) !=
      0u) {
    push(clazz, method);
  }
}

void TransitiveClosureMarkerWorker::push_if_class_instantiable(
    const DexField* field) {
  if ((field == nullptr) || m_shared_state->reachable_objects->marked(field)) {
    return;
  }
  TRACE(REACH, 4,
        "Conditionally marking field if declaring class is instantiable: %s",
        SHOW(field));
  auto* clazz = type_class(field->get_class());
  m_shared_state->cond_marked->if_class_instantiable.fields.insert(field);
  if (m_shared_state->reachable_aspects->instantiable_types.count(clazz) !=
      0u) {
    push(clazz, field);
  }
}

void TransitiveClosureMarkerWorker::push_if_class_instantiable(
    const DexClass* cls) {
  if ((cls == nullptr) || m_shared_state->reachable_objects->marked(cls)) {
    return;
  }
  TRACE(REACH, 4, "Conditionally marking class if instantiable: %s", SHOW(cls));
  m_shared_state->cond_marked->if_class_instantiable.classes.insert(cls);
  if (m_shared_state->reachable_aspects->instantiable_types.count(cls) != 0u) {
    push(cls, cls);
  }
}

void TransitiveClosureMarkerWorker::push_if_class_instantiable(
    const DexClass* cls,
    std::shared_ptr<MethodReferencesGatherer> mrefs_gatherer) {
  always_assert(mrefs_gatherer);
  const auto* method = mrefs_gatherer->get_method();
  bool emplaced = false;
  m_shared_state->cond_marked->method_references_gatherers_if_class_instantiable
      .update(cls, [&](auto*, auto& map, bool) {
        auto* ptr = mrefs_gatherer.get();
        auto p = map.emplace(method, std::move(mrefs_gatherer));
        // Make sure that moved-from value is a well-defined null.
        mrefs_gatherer = nullptr;
        always_assert(ptr == p.first->second.get()); // emplaced or not
        emplaced = p.second;
      });
  always_assert(!mrefs_gatherer);
  if (emplaced && (m_shared_state->reachable_aspects->instantiable_types.count(
                       cls) != 0u)) {
    // We lost the race. Oh well. Let's schedule one extra task to make sure
    // this class gets processed.
    m_worker_state->push_task(ReachableObject(
        cls, ReachableObjectType::METHOD_REFERENCES_GATHERER_INSTANTIABLE));
  }
}

void TransitiveClosureMarkerWorker::push_if_method_returning(
    const DexMethod* returning_method,
    std::shared_ptr<MethodReferencesGatherer> mrefs_gatherer) {
  always_assert(mrefs_gatherer);
  const auto* method = mrefs_gatherer->get_method();
  bool emplaced = false;
  m_shared_state->cond_marked->method_references_gatherers_if_method_returning
      .update(returning_method, [&](auto*, auto& map, bool) {
        auto* ptr = mrefs_gatherer.get();
        auto p = map.emplace(method, std::move(mrefs_gatherer));
        // Make sure that moved-from value is a well-defined null.
        mrefs_gatherer = nullptr;
        always_assert(ptr == p.first->second.get()); // emplaced or not
        emplaced = p.second;
      });
  always_assert(!mrefs_gatherer);
  if (emplaced && (m_shared_state->reachable_aspects->returning_methods.count(
                       returning_method) != 0u)) {
    // We lost the race. Oh well. Let's schedule one extra task to make sure
    // this method gets processed.
    m_worker_state->push_task(ReachableObject(
        returning_method,
        ReachableObjectType::METHOD_REFERENCES_GATHERER_RETURNING));
  }
}

void TransitiveClosureMarkerWorker::push_if_class_retained(
    const DexMethod* method) {
  if ((method == nullptr) ||
      m_shared_state->reachable_objects->marked(method)) {
    return;
  }
  TRACE(REACH, 4,
        "Conditionally marking method if declaring class is retained: %s",
        SHOW(method));
  auto* clazz = type_class(method->get_class());
  m_shared_state->cond_marked->if_class_retained.methods.insert(method);
  if (m_shared_state->reachable_objects->marked(clazz)) {
    push(clazz, method);
  }
}

void TransitiveClosureMarkerWorker::push_if_class_retained(
    const DexField* field) {
  if ((field == nullptr) || m_shared_state->reachable_objects->marked(field)) {
    return;
  }
  TRACE(REACH, 4,
        "Conditionally marking field if declaring class is retained: %s",
        SHOW(field));
  auto* clazz = type_class(field->get_class());
  m_shared_state->cond_marked->if_class_retained.fields.insert(field);
  if (m_shared_state->reachable_objects->marked(clazz)) {
    push(clazz, field);
  }
}

void TransitiveClosureMarkerWorker::
    push_directly_instantiable_if_class_dynamically_referenced(DexType* type) {
  m_shared_state->cond_marked->if_class_dynamically_referenced
      .directly_instantiable_types.insert(type);
  auto* clazz = type_class(type);
  if (m_shared_state->reachable_aspects->dynamically_referenced_classes.count(
          clazz) != 0u) {
    directly_instantiable(type);
  }
}

void TransitiveClosureMarkerWorker::push_if_instance_method_callable(
    std::shared_ptr<MethodReferencesGatherer> mrefs_gatherer) {
  const auto* method = mrefs_gatherer->get_method();
  m_shared_state->cond_marked->if_instance_method_callable.update(
      method, [&](auto*, auto& value, bool) {
        always_assert(!value);
        value = std::move(mrefs_gatherer);
        // Make sure that moved-from value is a well-defined null.
        mrefs_gatherer = nullptr;
      });
  if (m_shared_state->reachable_aspects->callable_instance_methods.count(
          method) != 0u) {
    m_shared_state->cond_marked->if_instance_method_callable.update(
        method,
        [&](auto*, auto& value, bool) { std::swap(mrefs_gatherer, value); });
    if (mrefs_gatherer) {
      gather_and_push(mrefs_gatherer,
                      MethodReferencesGatherer::Advance::callable());
    }
  }
}

// Adapted from retired DelInitPass
namespace relaxed_keep_class_members_impl {

void gather_dynamic_references_impl(const DexAnnotation* anno,
                                    References* references) {
  DexType* dalviksig = type::dalvik_annotation_Signature();
  // Signature annotations contain strings that Jackson uses
  // to construct the underlying types.
  if (anno->type() == dalviksig) {
    annotation_signature_parser::parse(anno, [&](auto*, auto* sigcls) {
      if (sigcls) {
        references->classes_dynamically_referenced.insert(sigcls);
      }
      return true;
    });
    return;
  }
  // Class literals in annotations.
  // Example:
  //    @JsonDeserialize(using=MyJsonDeserializer.class)
  if (anno->runtime_visible()) {
    const auto& elems = anno->anno_elems();
    std::vector<const DexType*> ltype;
    for (auto const& dae : elems) {
      const auto& evalue = dae.encoded_value;
      evalue->gather_types(ltype);
    }
    for (const auto* dextype : ltype) {
      auto* cls = type_class(dextype);
      if (cls != nullptr) {
        references->classes_dynamically_referenced.insert(cls);
      }
    }
  }
}

void gather_dynamic_references_anno_set(const DexAnnotationSet* anno_set,
                                        References* references) {
  if (anno_set != nullptr) {
    for (const auto& anno : anno_set->get_annotations()) {
      gather_dynamic_references_impl(anno.get(), references);
    }
  }
}

template <class T>
void gather_dynamic_references(T item, References* references) {
  gather_dynamic_references_anno_set(item->get_anno_set(), references);
}

template <>
void gather_dynamic_references(const DexMethod* item, References* references) {
  gather_dynamic_references_anno_set(item->get_anno_set(), references);
  const auto* param_anno = item->get_param_anno();
  if (param_anno != nullptr) {
    for (auto&& [_, param_anno_set] : *param_anno) {
      gather_dynamic_references_anno_set(param_anno_set.get(), references);
    }
  }
}

template <>
void gather_dynamic_references(const DexAnnotation* item,
                               References* references) {
  gather_dynamic_references_impl(item, references);
}

// Note: this method will return nullptr if the dotname refers to an unknown
// type.
DexType* get_dextype_from_dotname(std::string_view dotname) {
  std::string buf;
  buf.reserve(dotname.size() + 2);
  buf += 'L';
  buf += dotname;
  buf += ';';
  std::replace(buf.begin(), buf.end(), '.', '/');
  return DexType::get_type(buf);
}

template <>
void gather_dynamic_references(const MethodItemEntry* item,
                               References* references) {
  if (item->type != MFLOW_OPCODE) {
    return;
  }
  auto* insn = item->insn;
  // Matches any stringref that name-aliases a type.
  if (insn->has_string()) {
    const DexString* dsclzref = insn->get_string();
    auto* cls = type_class(get_dextype_from_dotname(dsclzref->str()));
    if (cls != nullptr) {
      references->classes_dynamically_referenced.insert(cls);
    }
  }
  if (opcode::is_new_instance(insn->opcode()) ||
      opcode::is_const_class(insn->opcode())) {
    auto* cls = type_class(insn->get_type());
    if (cls != nullptr) {
      references->classes_dynamically_referenced.insert(cls);
    }
  }
}

} // namespace relaxed_keep_class_members_impl

MethodReferencesGatherer::MethodReferencesGatherer(
    const TransitiveClosureMarkerSharedState* shared_state,
    const DexMethod* method,
    bool consider_code,
    GatherMieFunction gather_mie)
    : m_shared_state(shared_state),
      m_method(method),
      m_consider_code(consider_code),
      m_gather_mie(gather_mie ? std::move(gather_mie)
                              : default_gather_mie_with_gather_methods) {}

std::optional<MethodReferencesGatherer::InstantiableDependency>
MethodReferencesGatherer::get_instantiable_dependency(const IRInstruction* insn,
                                                      References* refs) const {
  auto op = insn->opcode();
  InstantiableDependency res;
  if (opcode::is_an_ifield_op(op)) {
    res.cls = type_class(insn->get_field()->get_class());
    res.may_continue_normally_if_uninstantiable = false;
  } else if (opcode::is_invoke_virtual(op) || opcode::is_invoke_super(op) ||
             opcode::is_invoke_interface(op) ||
             (opcode::is_invoke_direct(op) &&
              (m_shared_state->cfg_gathering_check_instance_callable ||
               !method::is_init(insn->get_method())))) {
    res.cls = type_class(insn->get_method()->get_class());
    res.may_continue_normally_if_uninstantiable = false;
  } else if (opcode::is_instance_of(op)) {
    res.cls = type_class(insn->get_type());
    res.may_throw_if_uninstantiable = false;
    if ((res.cls != nullptr) && !res.cls->is_external()) {
      refs->classes_if_instantiable.push_back(res.cls);
    }
  } else if (opcode::is_check_cast(op)) {
    res.cls = type_class(insn->get_type());
    if ((res.cls != nullptr) && !res.cls->is_external()) {
      refs->classes_if_instantiable.push_back(res.cls);
    }
  }
  auto is_class_instantiable = [this](const auto* cls) -> bool {
    if (!m_shared_state->cfg_gathering_check_instantiable ||
        m_method->rstate.no_optimizations()) {
      return true;
    }
    auto* ra = m_shared_state->reachable_aspects;
    return ra->instantiable_types.count(cls) ||
           ra->deserializable_types.count(cls) ||
           (ra->parcelable_type &&
            type::check_cast(cls->get_type(), ra->parcelable_type));
  };
  if ((res.cls == nullptr) || is_class_instantiable(res.cls) ||
      (res.cls->is_external() && !type::is_void(res.cls->get_type()))) {
    return std::nullopt;
  }
  return res;
};

std::optional<MethodReferencesGatherer::ReturningDependency>
MethodReferencesGatherer::get_returning_dependency(
    const IRInstruction* insn, const References* refs) const {
  auto op = insn->opcode();
  always_assert(opcode::is_an_invoke(op));
  auto is_method_returning = [&](const auto* method) -> bool {
    always_assert(method);
    always_assert(!is_abstract(method));
    return method->is_external() || is_native(method) ||
           method->rstate.no_optimizations() ||
           m_shared_state->reachable_aspects->returning_methods.count(method);
  };
  if (opcode::is_invoke_static(op) || opcode::is_invoke_direct(op)) {
    always_assert(refs->methods.size() == 1);
    const auto* resolved_callee = resolve_method_deprecated(
        insn->get_method(), opcode_to_search(insn), m_method);
    if (resolved_callee != nullptr) {
      always_assert(!resolved_callee->is_virtual());
      always_assert(!is_abstract(resolved_callee));
      if (!is_method_returning(resolved_callee)) {
        return std::optional<MethodReferencesGatherer::ReturningDependency>(
            (ReturningDependency){{resolved_callee}});
      }
    }
  } else if (opcode::is_invoke_super(op) &&
             !refs->invoke_super_targets.empty()) {
    const auto* super_method = only(refs->invoke_super_targets);
    always_assert(super_method->is_virtual());
    always_assert(!super_method->is_external());
    if (!is_abstract(super_method) && !is_method_returning(super_method)) {
      return std::optional<MethodReferencesGatherer::ReturningDependency>(
          (ReturningDependency){{super_method}});
    }
  } else if (opcode::is_invoke_virtual(op) || opcode::is_invoke_interface(op)) {
    if (refs->unknown_invoke_virtual_targets) {
      return std::nullopt;
    }
    // We cannot have both exact and base targets.
    always_assert(
        refs->exact_invoke_virtual_targets_if_class_instantiable.empty() ||
        refs->base_invoke_virtual_targets_if_class_instantiable.empty());
    always_assert(
        refs->base_invoke_virtual_targets_if_class_instantiable.size() <= 1);
    // TODO: Track returnability for base methods (which then includes all
    // overriding methods) to avoid computing and iterating over all overriding
    // methods for each invocation.
    // First, we check whether we already know that any eligible virtual target
    // returns.
    auto any = [&](auto& f) {
      UnorderedSet<const DexMethod*> unique_methods;
      auto identity = [](const auto* x) { return x; };
      auto select_first = [](const auto& p) { return p.first; };
      auto is = [&](const auto& item, const auto& p) {
        auto* m = p(item);
        if (!unique_methods.insert(m).second) {
          return false;
        }
        always_assert(m->is_virtual());
        if (is_abstract(m)) {
          return false;
        }
        return f(m);
      };
      auto any_of = [&](const auto& collection, const auto& p) {
        for (auto&& item : UnorderedIterable(collection)) {
          if (is(item, p)) {
            return true;
          }
        }
        return false;
      };
      if (any_of(refs->exact_invoke_virtual_targets_if_class_instantiable,
                 identity) ||
          any_of(refs->base_invoke_virtual_targets_if_class_instantiable,
                 select_first)) {
        return true;
      }
      for (auto&& [base_method, base_types] : UnorderedIterable(
               refs->base_invoke_virtual_targets_if_class_instantiable)) {
        for (const auto* base_type : UnorderedIterable(base_types)) {
          always_assert(!type_class(base_type)->is_external());
          if (mog::any_overriding_methods(
                  *m_shared_state->method_override_graph, base_method,
                  [&](const DexMethod* overriding_method) {
                    return is(overriding_method, identity);
                  },
                  /* include_interfaces*/ false, base_type)) {
            return true;
          }
        }
      }
      return false;
    };
    if (any(is_method_returning)) {
      return std::nullopt;
    }
    // Second, we build the list of virtual targets we need to wait for.
    UnorderedSet<const DexMethod*> target_methods;
    auto add = [&](const auto* method) {
      target_methods.insert(method);
      return false;
    };
    any(add);
    if (target_methods.empty()) {
      // So there's no method that could be invoked that could ever return. To
      // make our internal accounting happy, and to track this properly, we'll
      // pretend that there's a dependency on the "null" method, which of course
      // will never be found to return.
      target_methods.insert(nullptr);
    }
    return std::optional<MethodReferencesGatherer::ReturningDependency>(
        ReturningDependency{std::move(target_methods)});
  }
  return std::nullopt;
}

void MethodReferencesGatherer::default_gather_mie(const MethodItemEntry& mie,
                                                  References* refs,
                                                  bool gather_methods) {
  mie.gather_strings(refs->strings);
  mie.gather_types(refs->types);
  mie.gather_fields(refs->fields);
  if (gather_methods) {
    mie.gather_methods(refs->methods);
  }
  if (m_shared_state->relaxed_keep_class_members) {
    relaxed_keep_class_members_impl::gather_dynamic_references(&mie, refs);
  }
  if (mie.type == MFLOW_OPCODE) {
    auto* insn = mie.insn;
    auto op = insn->opcode();
    if (opcode::is_new_instance(op)) {
      refs->new_instances.push_back(insn->get_type());
    } else if (gather_methods && opcode::is_invoke_super(op)) {
      auto* callee = resolve_method_deprecated(insn->get_method(),
                                               MethodSearch::Super, m_method);
      if ((callee != nullptr) && !callee->is_external()) {
        always_assert(callee->is_virtual());
        if (is_abstract(callee)) {
          TRACE(REACH, 1,
                "invoke super target of {%s} is abstract method %s in %s",
                SHOW(insn), SHOW(callee), SHOW(m_method));
        } else {
          refs->invoke_super_targets.insert(callee);
        }
      }
    } else if (gather_methods && (opcode::is_invoke_virtual(op) ||
                                  opcode::is_invoke_interface(op))) {
      auto* resolved_callee = resolve_invoke_method_deprecated(insn, m_method);
      if (resolved_callee == nullptr) {
        // Typically clone() on an array, or other obscure external references
        TRACE(REACH, 2, "Unresolved virtual callee at %s", SHOW(insn));
        refs->unknown_invoke_virtual_targets = true;
        return;
      }
      auto* method_ref = insn->get_method();
      auto* base_type = method_ref->get_class();
      refs->base_invoke_virtual_targets_if_class_instantiable[resolved_callee]
          .insert(base_type);
      auto* base_cls = type_class(base_type);
      always_assert(base_cls);
      if (base_cls == nullptr || base_cls->is_external() ||
          (!is_abstract(resolved_callee) && resolved_callee->is_external())) {
        refs->unknown_invoke_virtual_targets = true;
      } else if (opcode::is_invoke_interface(op) && is_interface(base_cls)) {
        // Why can_rename? To mirror what VirtualRenamer looks at.
        if (root(resolved_callee) || !can_rename(resolved_callee) ||
            is_annotation(base_cls)) {
          // We cannot rule out that there are dynamically added classes,
          // possibly even created at runtime via Proxy.newProxyInstance, that
          // override this method. So we assume the worst.
          refs->unknown_invoke_virtual_targets = true;
        }
      }
    } else if (opcode::is_a_return(op)) {
      refs->returns = true;
    }
  }
}

void MethodReferencesGatherer::advance(const Advance& advance,
                                       References* refs) {
  always_assert((advance.kind() & m_next_advance_kinds) != AdvanceKind::None);
  if (advance.kind() == AdvanceKind::Initial) {
    // initial gathering
    m_method->gather_types_shallow(refs->types); // Handle DexMethodRef parts.
    auto gather_from_anno_set = [refs](auto* anno_set) {
      anno_set->gather_strings(refs->strings);
      anno_set->gather_types(refs->types);
      anno_set->gather_fields(refs->fields);
      anno_set->gather_methods(refs->methods);
    };
    const auto* anno_set = m_method->get_anno_set();
    if (anno_set != nullptr) {
      gather_from_anno_set(anno_set);
    }
    const auto* param_anno = m_method->get_param_anno();
    if (param_anno != nullptr) {
      for (auto&& [_, param_anno_set] : *param_anno) {
        gather_from_anno_set(param_anno_set.get());
      }
    }
    if (m_shared_state->relaxed_keep_class_members) {
      relaxed_keep_class_members_impl::gather_dynamic_references(m_method,
                                                                 refs);
    }
    refs->method_references_gatherer_dependency_if_instance_method_callable =
        true;
    m_next_advance_kinds = AdvanceKind::Callable;
    return;
  }
  std::lock_guard<std::mutex> lock_guard(m_mutex);
  std::queue<CFGNeedle> queue;
  if (advance.kind() == AdvanceKind::Callable) {
    std::vector<CFGNeedle> cfg_needles;
    const auto* code = m_method->get_code();
    if (code != nullptr) {
      if (m_consider_code) {
        always_assert_log(code->cfg_built(), "%s does not have cfg",
                          SHOW(m_method));
        const auto& cfg = code->cfg();
        auto* b = cfg.entry_block();
        queue.push((CFGNeedle){b, b->begin()});
        m_pushed_blocks.insert(b);
      } else {
        // While the code's references must get collected elsewhere, we
        // generally assume that the code will return.
        refs->returns = true;
      }
    }
    m_next_advance_kinds = AdvanceKind::InstantiableDependencyResolved |
                           AdvanceKind::ReturningDependencyResolved;
  } else if (advance.kind() == AdvanceKind::InstantiableDependencyResolved) {
    auto it = m_instantiable_dependencies.find(advance.instantiable_cls());
    if (it == m_instantiable_dependencies.end()) {
      return;
    }
    for (auto& cfg_needle : it->second) {
      queue.push(cfg_needle);
    }
    m_instantiable_dependencies.erase(it);
  } else {
    always_assert(advance.kind() == AdvanceKind::ReturningDependencyResolved);
    auto it = m_returning_dependencies.find(advance.returning_method());
    if (it == m_returning_dependencies.end()) {
      return;
    }
    UnorderedSet<const MethodItemEntry*> mies;
    mies.reserve(it->second.size());
    for (auto& cfg_needle : it->second) {
      mies.insert(&*cfg_needle.it);
      queue.push(cfg_needle);
    }
    m_returning_dependencies.erase(it);
    unordered_erase_if(m_returning_dependencies, [&mies](auto& p) {
      auto& cfg_needles = p.second;
      std::erase_if(cfg_needles, [&mies](const auto& cfg_needle) {
        return mies.count(&*cfg_needle.it);
      });
      return cfg_needles.empty();
    });
  }
  using Dependency = std::variant<InstantiableDependency, ReturningDependency>;
  auto advance_in_block = [this, refs](auto* block, auto& it) {
    for (; it != block->end(); ++it) {
      if (it->type == MFLOW_OPCODE) {
        auto instantiable_dep = get_instantiable_dependency(it->insn, refs);
        if (instantiable_dep) {
          return std::make_optional<Dependency>(*instantiable_dep);
        }
        m_instructions_visited++;
        if (opcode::is_an_invoke(it->insn->opcode()) &&
            m_shared_state->cfg_gathering_check_returning &&
            !m_method->rstate.no_optimizations()) {
          auto methods = std::move(refs->methods);
          auto invoke_super_targets = std::move(refs->invoke_super_targets);
          auto exact_invoke_virtual_targets_if_class_instantiable = std::move(
              refs->exact_invoke_virtual_targets_if_class_instantiable);
          auto base_invoke_virtual_targets_if_class_instantiable = std::move(
              refs->base_invoke_virtual_targets_if_class_instantiable);
          auto unknown_invoke_virtual_targets =
              refs->unknown_invoke_virtual_targets;
          refs->unknown_invoke_virtual_targets = false;
          m_gather_mie(this, *it, refs);
          auto returning_dep = get_returning_dependency(it->insn, refs);
          std::swap(methods, refs->methods);
          refs->methods.insert(refs->methods.end(), methods.begin(),
                               methods.end());
          std::swap(invoke_super_targets, refs->invoke_super_targets);
          insert_unordered_iterable(refs->invoke_super_targets,
                                    invoke_super_targets);
          std::swap(exact_invoke_virtual_targets_if_class_instantiable,
                    refs->exact_invoke_virtual_targets_if_class_instantiable);
          insert_unordered_iterable(
              refs->exact_invoke_virtual_targets_if_class_instantiable,
              exact_invoke_virtual_targets_if_class_instantiable);
          std::swap(base_invoke_virtual_targets_if_class_instantiable,
                    refs->base_invoke_virtual_targets_if_class_instantiable);
          for (auto&& [base_method, base_types] : UnorderedIterable(
                   base_invoke_virtual_targets_if_class_instantiable)) {
            insert_unordered_iterable(
                refs->base_invoke_virtual_targets_if_class_instantiable
                    [base_method],
                base_types);
          }
          if (unknown_invoke_virtual_targets) {
            refs->unknown_invoke_virtual_targets = true;
          }
          if (returning_dep) {
            return std::make_optional<Dependency>(std::move(*returning_dep));
          }
          continue;
        }
      }
      m_gather_mie(this, *it, refs);
    }
    return std::optional<Dependency>();
  };
  auto visit_succ = [this, &refs, &queue](auto* e) {
    if (e->type() == cfg::EDGE_THROW) {
      auto catch_type = e->throw_info()->catch_type;
      if (catch_type && m_covered_catch_types.insert(catch_type).second) {
        refs->types.push_back(catch_type);
      }
    }
    if (m_pushed_blocks.insert(e->target()).second) {
      queue.push((CFGNeedle){e->target(), e->target()->begin()});
    }
  };
  auto visit_throw_succs_if_last_insn = [&visit_succ](auto* block,
                                                      const auto& it) {
    if (block->get_last_insn() == it) {
      for (auto* e : block->succs()) {
        if (e->type() == cfg::EDGE_THROW) {
          visit_succ(e);
        }
      }
    }
  };
  while (!queue.empty()) {
    auto [block, it] = queue.front();
    queue.pop();
    auto dep = advance_in_block(block, it);
    if (!dep) {
      always_assert(it == block->end());
      for (auto* e : block->succs()) {
        visit_succ(e);
      }
      continue;
    }
    always_assert(it->type == MFLOW_OPCODE);
    auto* instantiable_dep = std::get_if<InstantiableDependency>(&*dep);
    if (instantiable_dep != nullptr) {
      if (!instantiable_dep->may_continue_normally_if_uninstantiable) {
        auto [deps_it, emplaced] = m_instantiable_dependencies.emplace(
            instantiable_dep->cls, std::vector<CFGNeedle>());
        if (emplaced) {
          refs->method_references_gatherer_dependencies_if_class_instantiable
              .push_back(instantiable_dep->cls);
        }
        deps_it->second.push_back((CFGNeedle){block, it});
        always_assert(instantiable_dep->may_throw_if_uninstantiable);
        visit_throw_succs_if_last_insn(block, it);
        continue;
      }
      m_instructions_visited++;
      queue.push((CFGNeedle){block, std::next(it)});
      continue;
    }
    auto& returning_dep = std::get<ReturningDependency>(*dep);
    for (const auto* m : UnorderedIterable(returning_dep.methods)) {
      auto [deps_it, emplaced] =
          m_returning_dependencies.emplace(m, std::vector<CFGNeedle>());
      if (emplaced) {
        refs->method_references_gatherer_dependencies_if_method_returning
            .push_back(m);
      }
      deps_it->second.push_back((CFGNeedle){block, std::next(it)});
    }
    visit_throw_succs_if_last_insn(block, it);
  }
}

UnorderedSet<const IRInstruction*>
MethodReferencesGatherer::get_non_returning_insns() const {
  UnorderedSet<const IRInstruction*> set;
  for (auto&& [_, needles] : UnorderedIterable(m_returning_dependencies)) {
    for (const auto& needle : needles) {
      set.insert(std::prev(needle.it)->insn);
    }
  }
  return set;
}

void gather_dynamic_references(const DexAnnotation* item,
                               References* references) {
  relaxed_keep_class_members_impl::gather_dynamic_references(item, references);
}

void gather_dynamic_references(const MethodItemEntry* mie,
                               References* references) {
  relaxed_keep_class_members_impl::gather_dynamic_references(mie, references);
}

template <class T>
static References generic_gather(T t, bool include_dynamic_references) {
  References refs;
  t->gather_strings(refs.strings);
  t->gather_types(refs.types);
  t->gather_fields(refs.fields);
  t->gather_methods(refs.methods);
  if (include_dynamic_references) {
    relaxed_keep_class_members_impl::gather_dynamic_references<T>(t, &refs);
  }
  return refs;
}

References TransitiveClosureMarkerWorker::gather(
    const DexAnnotation* anno) const {
  return generic_gather(anno, m_shared_state->relaxed_keep_class_members);
}

References TransitiveClosureMarkerWorker::gather(const DexField* field) const {
  return generic_gather(field, m_shared_state->relaxed_keep_class_members);
}

bool TransitiveClosureMarkerWorker::has_class_forName(const DexMethod* meth) {
  const auto* code = meth->get_code();
  auto* class_forName = method::java_lang_Class_forName();
  if ((code == nullptr) || (class_forName == nullptr)) {
    return false;
  }
  always_assert(code->cfg_built());
  const auto& cfg = code->cfg();
  for (const auto& mie : InstructionIterable(cfg)) {
    auto* insn = mie.insn;
    if (insn->has_method() && insn->get_method() == class_forName) {
      return true;
    }
  }
  return false;
}

void TransitiveClosureMarkerWorker::gather_and_push(
    std::shared_ptr<MethodReferencesGatherer> mrefs_gatherer,
    const MethodReferencesGatherer::Advance& advance) {
  always_assert(mrefs_gatherer);
  References refs;
  mrefs_gatherer->advance(advance, &refs);
  const auto* meth = mrefs_gatherer->get_method();
  if (refs.method_references_gatherer_dependency_if_instance_method_callable &&
      (!m_shared_state->cfg_gathering_check_instantiable ||
       !m_shared_state->cfg_gathering_check_instance_callable ||
       meth->rstate.no_optimizations() || is_static(meth) ||
       (m_shared_state->reachable_aspects->callable_instance_methods.count(
            meth) != 0u))) {
    always_assert(advance.kind() ==
                  MethodReferencesGatherer::AdvanceKind::Initial);
    refs.method_references_gatherer_dependency_if_instance_method_callable =
        false;
    mrefs_gatherer->advance(MethodReferencesGatherer::Advance::callable(),
                            &refs);
    always_assert(
        !refs.method_references_gatherer_dependency_if_instance_method_callable);
  }
  auto* type = meth->get_class();
  auto* cls = type_class(type);
  bool check_strings = m_shared_state->ignore_sets->keep_class_in_string;
  if (!check_strings && !refs.strings.empty() && has_class_forName(meth)) {
    check_strings = true;
  }
  if (m_shared_state->ignore_sets->string_literals.count(type) != 0u) {
    ++m_shared_state->stats->num_ignore_check_strings;
    check_strings = false;
  }
  if ((cls != nullptr) && check_strings) {
    for (const auto& ignore_anno_type :
         UnorderedIterable(m_shared_state->ignore_sets->string_literal_annos)) {
      if (has_anno(cls, ignore_anno_type)) {
        ++m_shared_state->stats->num_ignore_check_strings;
        check_strings = false;
        break;
      }
    }
  }
  if (check_strings) {
    push_typelike_strings(meth, refs.strings);
  }
  push(meth, refs.types.begin(), refs.types.end());
  push(meth, refs.fields.begin(), refs.fields.end());
  push(meth, refs.methods.begin(), refs.methods.end());
  exact_invoke_virtual_target(
      refs.exact_invoke_virtual_targets_if_class_instantiable);
  base_invoke_virtual_target(
      refs.base_invoke_virtual_targets_if_class_instantiable);
  instance_callable(refs.invoke_super_targets);
  for (const auto* iface_cls : refs.classes_if_instantiable) {
    push_if_class_instantiable(iface_cls);
  }
  dynamically_referenced(refs.classes_dynamically_referenced);
  directly_instantiable(refs.new_instances);
  if (refs.method_references_gatherer_dependency_if_instance_method_callable) {
    push_if_instance_method_callable(mrefs_gatherer);
    always_assert(
        refs.method_references_gatherer_dependencies_if_class_instantiable
            .empty());
    always_assert(
        refs.method_references_gatherer_dependencies_if_method_returning
            .empty());
    always_assert(!refs.returns);
    return;
  }
  for (const auto* dep_cls :
       refs.method_references_gatherer_dependencies_if_class_instantiable) {
    push_if_class_instantiable(dep_cls, mrefs_gatherer);
  }
  auto& v = refs.method_references_gatherer_dependencies_if_method_returning;
  if (!v.empty()) {
    for (size_t i = 0; i < v.size() - 1; ++i) {
      push_if_method_returning(v[i], mrefs_gatherer);
    }
    push_if_method_returning(v[v.size() - 1], std::move(mrefs_gatherer));
  }
  if (refs.returns) {
    returns(meth);
  }
}

void TransitiveClosureMarkerWorker::gather_and_push(const DexMethod* meth) {
  gather_and_push(create_method_references_gatherer(meth),
                  MethodReferencesGatherer::Advance::initial());
}

std::shared_ptr<MethodReferencesGatherer>
TransitiveClosureMarkerWorker::create_method_references_gatherer(
    const DexMethod* method, bool consider_code, GatherMieFunction gather_mie) {
  return std::make_shared<MethodReferencesGatherer>(
      m_shared_state, method, consider_code, std::move(gather_mie));
}

template <typename T>
void TransitiveClosureMarkerWorker::gather_and_push(T t) {
  auto refs = gather(t);
  push_typelike_strings(t, refs.strings);
  push(t, refs.types.begin(), refs.types.end());
  push(t, refs.fields.begin(), refs.fields.end());
  push(t, refs.methods.begin(), refs.methods.end());
  dynamically_referenced(refs.classes_dynamically_referenced);
  always_assert_log(!refs.maybe_from_code(),
                    "gather_and_push(%s) should not produce entries that can "
                    "only arise from MethodItemEntries, as those would then "
                    "not get processed by (default_)gather_mie.",
                    typeid(T).name());
}

bool References::maybe_from_code() const {
  return !new_instances.empty() ||
         !exact_invoke_virtual_targets_if_class_instantiable.empty() ||
         !base_invoke_virtual_targets_if_class_instantiable.empty() ||
         !method_references_gatherer_dependencies_if_class_instantiable
              .empty() ||
         method_references_gatherer_dependency_if_instance_method_callable ||
         !invoke_super_targets.empty() || returns;
}

template <class Parent>
void TransitiveClosureMarkerWorker::push_typelike_strings(
    const Parent* parent, const std::vector<const DexString*>& strings) {
  for (auto const& str : strings) {
    auto* type = java_names::get_type_from_external_name(str->str());
    if (!type) {
      continue;
    }
    push(parent, type);
  }
}

void TransitiveClosureMarkerWorker::visit_cls(const DexClass* cls) {
  always_assert(m_shared_state->scope_set.count(cls));
  TRACE(REACH, 4, "Visiting class: %s", SHOW(cls));
  auto is_interface_instantiable = [](const DexClass* interface) {
    if (is_annotation(interface) || root(interface) || !can_rename(interface)) {
      return true;
    }
    for (auto* method : interface->get_vmethods()) {
      if (root(method) || !can_rename(method)) {
        return true;
      }
    }
    return false;
  };
  if (is_interface(cls) && is_interface_instantiable(cls)) {
    instantiable(cls->get_type());
  }
  push(cls, type_class(cls->get_super_class()));
  if (!m_shared_state->relaxed_keep_interfaces) {
    for (const auto* t : *cls->get_interfaces()) {
      push(cls, t);
    }
  }
  const DexAnnotationSet* annoset = cls->get_anno_set();
  if (annoset != nullptr) {
    for (auto const& anno : annoset->get_annotations()) {
      if (anno->type() == type::dalvik_annotation_MemberClasses()) {
        // Ignore inner-class annotations.
        continue;
      }
      record_reachability(cls, anno.get());
      gather_and_push(anno.get());
    }
  }

  if (m_shared_state->relaxed_keep_class_members &&
      consider_dynamically_referenced(cls) && marked_by_string(cls)) {
    dynamically_referenced(cls);
  }

  auto* cond_marked = m_shared_state->cond_marked;
  for (auto const& m : cls->get_ifields()) {
    if (cond_marked->if_class_retained.fields.count(m) != 0u) {
      push(cls, m);
    }
  }
  for (auto const& m : cls->get_sfields()) {
    if (cond_marked->if_class_retained.fields.count(m) != 0u) {
      push(cls, m);
    }
  }
  for (auto const& m : cls->get_dmethods()) {
    if (cond_marked->if_class_retained.methods.count(m) != 0u) {
      push(cls, m);
    }
  }
  for (auto const& m : cls->get_vmethods()) {
    if (cond_marked->if_class_retained.methods.count(m) != 0u) {
      push(cls, m);
    }
  }
}

void TransitiveClosureMarkerWorker::visit_field_ref(const DexFieldRef* field) {
  TRACE(REACH, 4, "Visiting field: %s", SHOW(field));
  if (!field->is_concrete()) {
    auto const& realfield =
        resolve_field(field->get_class(), field->get_name(), field->get_type());
    push(field, realfield);
  }
  push(field, field->get_class());
  push(field, field->get_type());
}

void TransitiveClosureMarkerWorker::visit_instantiable(const DexClass* cls) {
  TRACE(REACH, 4, "Visiting instantiable class: %s", SHOW(cls));

  instantiable(cls->get_super_class());
  for (const auto* intf : *cls->get_interfaces()) {
    instantiable(intf);
  }
  auto* cond_marked = m_shared_state->cond_marked;
  if (cond_marked->if_class_instantiable.classes.count(cls) != 0u) {
    push(cls, cls);
  }
  for (auto const& f : cls->get_ifields()) {
    if (cond_marked->if_class_instantiable.fields.count(f) != 0u) {
      push(cls, f);
    }
  }
  for (auto const& m : cls->get_dmethods()) {
    if (cond_marked->if_class_instantiable.methods.count(m) != 0u) {
      push(cls, m);
    }
  }
  for (auto const& m : cls->get_vmethods()) {
    if (cond_marked->if_class_instantiable.methods.count(m) != 0u) {
      push(cls, m);
    }
  }

  size_t mrefs_gatherers{0};
  cond_marked->method_references_gatherers_if_class_instantiable.update(
      cls, [&](auto*, auto& map, bool) { mrefs_gatherers = map.size(); });
  for (size_t i = 0; i < mrefs_gatherers; i++) {
    m_worker_state->push_task(ReachableObject(
        cls, ReachableObjectType::METHOD_REFERENCES_GATHERER_INSTANTIABLE));
  }
}

void TransitiveClosureMarkerWorker::
    visit_method_references_gatherer_instantiable(const DexClass* cls) {
  TRACE(REACH, 4,
        "Visiting method-references-gatherer for instantiable class: %s",
        SHOW(cls));

  std::shared_ptr<MethodReferencesGatherer> mrefs_gatherer;
  m_shared_state->cond_marked->method_references_gatherers_if_class_instantiable
      .update(cls, [&](auto*, auto& map, bool) {
        if (!map.empty()) {
          auto it = unordered_any(map);
          mrefs_gatherer = std::move(it->second);
          map.erase(it);
        }
      });
  if (mrefs_gatherer) {
    gather_and_push(std::move(mrefs_gatherer),
                    MethodReferencesGatherer::Advance::instantiable(cls));
  }
}

void TransitiveClosureMarkerWorker::visit_returns(const DexMethod* method) {
  TRACE(REACH, 4, "Visiting returning method: %s", SHOW(method));

  size_t mrefs_gatherers{0};
  m_shared_state->cond_marked->method_references_gatherers_if_method_returning
      .update(method,
              [&](auto*, auto& map, bool) { mrefs_gatherers = map.size(); });
  for (size_t i = 0; i < mrefs_gatherers; i++) {
    m_worker_state->push_task(ReachableObject(
        method, ReachableObjectType::METHOD_REFERENCES_GATHERER_RETURNING));
  }
}

void TransitiveClosureMarkerWorker::visit_method_references_gatherer_returning(
    const DexMethod* method) {
  TRACE(REACH, 4,
        "Visiting method-references-gatherer for returning method: %s",
        SHOW(method));

  std::shared_ptr<MethodReferencesGatherer> mrefs_gatherer;
  m_shared_state->cond_marked->method_references_gatherers_if_method_returning
      .update(method, [&](auto*, auto& map, bool) {
        if (!map.empty()) {
          auto it = unordered_any(map);
          mrefs_gatherer = std::move(it->second);
          map.erase(it);
        }
      });
  if (mrefs_gatherer) {
    gather_and_push(std::move(mrefs_gatherer),
                    MethodReferencesGatherer::Advance::returning(method));
  }
}

const DexMethod* resolve_without_context(const DexMethodRef* method,
                                         const DexClass* cls) {
  if (cls == nullptr) {
    return nullptr;
  }
  for (auto const& m : cls->get_vmethods()) {
    if (method::signatures_match(method, m)) {
      return m;
    }
  }
  for (auto const& m : cls->get_dmethods()) {
    if (method::signatures_match(method, m)) {
      return m;
    }
  }
  {
    auto const& superclass = type_class(cls->get_super_class());
    const auto* const resolved = resolve_without_context(method, superclass);
    if (resolved != nullptr) {
      return resolved;
    }
  }
  for (auto const& interface : *cls->get_interfaces()) {
    const auto* const resolved =
        resolve_without_context(method, type_class(interface));
    if (resolved != nullptr) {
      return resolved;
    }
  }
  return nullptr;
}

void TransitiveClosureMarkerWorker::returns(const DexMethod* method) {
  if (!m_shared_state->reachable_aspects->returning_methods.insert(method)) {
    return;
  }
  m_worker_state->push_task(
      ReachableObject(method, ReachableObjectType::RETURNS));
}

void TransitiveClosureMarkerWorker::instantiable(const DexType* type) {
  auto* cls = type_class(type);
  if ((cls == nullptr) || cls->is_external()) {
    return;
  }
  if (!m_shared_state->reachable_aspects->instantiable_types.insert(cls)) {
    return;
  }
  m_worker_state->push_task(
      ReachableObject(cls, ReachableObjectType::INSTANTIABLE));
}

void TransitiveClosureMarkerWorker::directly_instantiable(const DexType* type) {
  if (!m_shared_state->reachable_aspects->directly_instantiable_types.insert(
          type)) {
    return;
  }
  instantiable(type);
  UnorderedSet<const DexMethod*> overridden_methods;
  for (auto* cls = type_class(type); (cls != nullptr) && !cls->is_external();
       cls = type_class(cls->get_super_class())) {
    for (auto* m : cls->get_dmethods()) {
      if (!is_static(m)) {
        instance_callable(m);
      }
    }
    for (auto* m : cls->get_vmethods()) {
      if (overridden_methods.count(m) != 0u) {
        continue;
      }
      if (is_abstract(m)) {
        TRACE(REACH, 1,
              "[marking] abstract method {%s} is not overridden in directly "
              "instantiable class {%s}",
              SHOW(m), SHOW(type));
        m_shared_state->reachable_aspects
            ->incomplete_directly_instantiable_types.insert(type_class(type));
        continue;
      }
      implementation_method(m, &overridden_methods);
    }
  }
}

void TransitiveClosureMarkerWorker::instance_callable(const DexMethod* method) {
  if (!m_shared_state->reachable_aspects->callable_instance_methods.insert(
          method)) {
    return;
  }
  always_assert(!method->is_external());
  always_assert(!is_abstract(method));
  std::shared_ptr<MethodReferencesGatherer> mrefs_gatherer;
  m_shared_state->cond_marked->if_instance_method_callable.update(
      method,
      [&](auto*, auto& value, bool) { std::swap(mrefs_gatherer, value); });
  if (mrefs_gatherer) {
    gather_and_push(mrefs_gatherer,
                    MethodReferencesGatherer::Advance::callable());
  }
}

void TransitiveClosureMarkerWorker::implementation_method(
    const DexMethod* method,
    UnorderedSet<const DexMethod*>* overridden_methods) {
  auto newly_overridden_methods =
      mog::get_overridden_methods(*m_shared_state->method_override_graph,
                                  method, /* include_interfaces */ true);
  insert_unordered_iterable(*overridden_methods, newly_overridden_methods);

  if (!m_shared_state->reachable_aspects->implementation_methods.insert(
          method)) {
    return;
  }
  always_assert(method->is_virtual());
  always_assert(!is_abstract(method));

  auto is_unconditionally_instance_callable = [](const DexMethod* m) {
    return root(m) || m->is_external() || m->rstate.no_optimizations();
  };
  bool unconditionally_instance_callable{
      is_unconditionally_instance_callable(method)};
  for (const auto* overridden_method :
       UnorderedIterable(newly_overridden_methods)) {
    if (is_unconditionally_instance_callable(overridden_method)) {
      unconditionally_instance_callable = true;
    }
  }
  if (unconditionally_instance_callable) {
    instance_callable(method);
  } else {
    instance_callable_if_exact_invoke_virtual_target(method);
  }

  if (!m_shared_state->reachable_objects->marked(method) &&
      unordered_any_of(newly_overridden_methods, [](auto* overridden_method) {
        return is_abstract(overridden_method) ||
               overridden_method->is_external();
      })) {
    m_shared_state->reachable_aspects->zombie_implementation_methods.insert(
        method);
  }
}

void TransitiveClosureMarkerWorker::
    instance_callable_if_exact_invoke_virtual_target(const DexMethod* method) {
  if (!m_shared_state->cond_marked->if_exact_invoke_virtual_target.insert(
          method)) {
    return;
  }
  if (m_shared_state->reachable_aspects->exact_invoke_virtual_targets.count(
          method) != 0u) {
    instance_callable(method);
  }
}

void TransitiveClosureMarkerWorker::exact_invoke_virtual_target(
    const DexMethod* method) {
  always_assert(!is_abstract(method));
  if (method->is_external()) {
    return;
  }
  if (!m_shared_state->reachable_aspects->exact_invoke_virtual_targets.insert(
          method)) {
    return;
  }
  push_if_class_instantiable(method);
  if (m_shared_state->cond_marked->if_exact_invoke_virtual_target.count(
          method) != 0u) {
    instance_callable(method);
  }
}

void TransitiveClosureMarkerWorker::base_invoke_virtual_target(
    const DexMethod* method, const DexType* base_type, bool is_child) {
  if ((base_type != nullptr) && method->get_class() == base_type) {
    base_type = nullptr;
  }
  bool inserted = false;
  m_shared_state->reachable_aspects->base_invoke_virtual_targets.update(
      method,
      [&](auto*, auto& set, bool) { inserted = set.insert(base_type).second; });
  if (!inserted) {
    return;
  }
  const auto& node = m_shared_state->method_override_graph->get_node(method);
  if (!is_abstract(method) && (!is_child || (base_type == nullptr) ||
                               node.overrides(method, base_type))) {
    exact_invoke_virtual_target(method);
  }
  for (auto* child : UnorderedIterable(node.children)) {
    base_invoke_virtual_target(child->method, base_type, /* is_child */ true);
  }
}

void TransitiveClosureMarkerWorker::dynamically_referenced(
    const DexClass* cls) {
  always_assert(m_shared_state->relaxed_keep_class_members);
  if (!consider_dynamically_referenced(cls) ||
      !m_shared_state->reachable_aspects->dynamically_referenced_classes.insert(
          cls)) {
    return;
  }
  auto* cond_marked = m_shared_state->cond_marked;
  for (auto const& f : cls->get_ifields()) {
    if (cond_marked->if_class_dynamically_referenced.fields.count(f) != 0u) {
      push_if_class_retained(f);
    }
  }
  for (auto const& f : cls->get_sfields()) {
    if (cond_marked->if_class_dynamically_referenced.fields.count(f) != 0u) {
      push_if_class_retained(f);
    }
  }
  for (auto const& m : cls->get_dmethods()) {
    if (cond_marked->if_class_dynamically_referenced.methods.count(m) != 0u) {
      push_if_class_retained(m);
    }
  }
  for (auto const& m : cls->get_vmethods()) {
    if (cond_marked->if_class_dynamically_referenced.methods.count(m) != 0u) {
      push_if_class_retained(m);
    }
  }
  auto* type = cls->get_type();
  if (cond_marked->if_class_dynamically_referenced.directly_instantiable_types
          .count(type) != 0u) {
    directly_instantiable(type);
  }
}

void TransitiveClosureMarkerWorker::visit_method_ref(
    const DexMethodRef* method) {
  TRACE(REACH, 4, "Visiting method: %s", SHOW(method));
  auto* cls = type_class(method->get_class());
  const auto* resolved_method = resolve_without_context(method, cls);
  if (resolved_method != nullptr) {
    TRACE(REACH, 5, "    Resolved to: %s", SHOW(resolved_method));
    push(method, resolved_method);
    if (resolved_method == method) {
      gather_and_push(resolved_method);
    }
  }
  push(method, method->get_class());
  push(method, method->get_proto()->get_rtype());
  for (auto const& t : *method->get_proto()->get_args()) {
    push(method, t);
  }
  if ((cls != nullptr) && !is_abstract(cls) && method::is_init(method)) {
    if (!m_shared_state->cfg_gathering_check_instance_callable) {
      instantiable(method->get_class());
    }
    if (m_shared_state->relaxed_keep_class_members &&
        consider_dynamically_referenced(cls)) {
      push_directly_instantiable_if_class_dynamically_referenced(
          method->get_class());
    } else {
      directly_instantiable(method->get_class());
    }
  }

  const auto* m = method->as_def();
  if ((m == nullptr) || m->is_external() || !m->is_virtual()) {
    return;
  }
  always_assert_log(m->is_concrete(), "%s is not concrete", SHOW(m));
  // RootSetMarker already covers external overrides, so we skip them here.
  if (!root(m)) {
    return;
  }
  // We still have to conditionally mark root overrides. RootSetMarker already
  // covers external overrides, so we skip them here.
  base_invoke_virtual_target(m, /* base_type */ nullptr);
  m_shared_state->reachable_aspects->zombie_implementation_methods.erase(m);
}

template <class Parent, class Object>
void TransitiveClosureMarkerWorker::record_reachability(Parent* parent,
                                                        Object* object) {
  if (m_shared_state->record_reachability) {
    redex_assert(parent != nullptr && object != nullptr);
    m_shared_state->reachable_objects->record_reachability(parent, object);
  }
}

void compute_zombie_methods(
    const method_override_graph::Graph& method_override_graph,
    ReachableObjects& reachable_objects,
    ReachableAspects& reachable_aspects) {
  // Some directly instantiable classes may have vmethods that were not
  // marked. Simply removing those methods might leave behind the class with
  // unimplemented inherited abstract methods. Here, we find if that's the case,
  // and pick the first non-abstract override to add as an additional root.
  ConcurrentMap<DexMethod*, UnorderedSet<const DexClass*>> zombies;
  workqueue_run<const DexMethod*>(
      [&](const DexMethod* m) {
        bool any_abstract_methods = false;
        const DexMethod* unmarked_elder = nullptr;
        const DexMethod* elder_parent = m;
        std::function<void(const DexMethod*)> visit_abstract_method;
        visit_abstract_method = [&](const DexMethod* elder) {
          if (reachable_objects.marked_unsafe(elder) || elder->is_external()) {
            any_abstract_methods = true;
          }
          for (auto* parent : UnorderedIterable(
                   method_override_graph.get_node(elder).parents)) {
            if (is_abstract(parent->method)) {
              visit_abstract_method(parent->method);
            }
          }
        };
        while (unmarked_elder != elder_parent) {
          if (reachable_objects.marked_unsafe(elder_parent) ||
              elder_parent->is_external()) {
            reachable_aspects.zombie_implementation_methods.erase(m);
            return;
          }
          unmarked_elder = elder_parent;
          for (auto* parent : UnorderedIterable(
                   method_override_graph.get_node(unmarked_elder).parents)) {
            if (is_abstract(parent->method)) {
              visit_abstract_method(parent->method);
            } else {
              elder_parent = parent->method;
            }
          }
        }
        if (!any_abstract_methods) {
          reachable_aspects.zombie_implementation_methods.erase(m);
          return;
        }
        always_assert_log(unmarked_elder, "{%s} has no unmarked elder",
                          SHOW(m));
        auto* cls = type_class(m->get_class());
        zombies.update(const_cast<DexMethod*>(unmarked_elder),
                       [&](auto*, auto& set, bool) { set.insert(cls); });
      },
      reachable_aspects.zombie_implementation_methods);
  for (auto&& [m, unmarked_implementation_methods_classes] :
       UnorderedIterable(zombies)) {
    for (const auto* cls :
         UnorderedIterable(unmarked_implementation_methods_classes)) {
      reachable_objects.record_reachability(cls, m);
    }
    auto marked = reachable_objects.mark(m);
    always_assert(marked);
    reachable_aspects.zombie_methods.push_back(m);
    // These "zombies" are callable in the sense that possible eager verifier
    // may want to see such methods overriding all inherited abstract methods.
    reachable_aspects.callable_instance_methods.insert(m);
  }
}

void ReachableAspects::finish(const ConditionallyMarked& cond_marked,
                              const ReachableObjects& reachable_objects) {
  Timer t("finish");
  UnorderedMap<const DexMethod*, const MethodReferencesGatherer*>
      remaining_mrefs_gatherers;
  auto add = [&](auto& map) {
    for (auto&& [method, mrefs_gatherer] : UnorderedIterable(map)) {
      remaining_mrefs_gatherers.emplace(method, mrefs_gatherer.get());
    }
  };
  for (auto&& [cls, map] : UnorderedIterable(
           cond_marked.method_references_gatherers_if_class_instantiable)) {
    if (map.empty()) {
      always_assert(instantiable_types.count(cls));
      continue;
    }
    always_assert(!instantiable_types.count(cls));
    uninstantiable_dependencies.insert(cls);
    add(map);
  }
  for (auto&& [method, map] : UnorderedIterable(
           cond_marked.method_references_gatherers_if_method_returning)) {
    if (map.empty()) {
      always_assert(returning_methods.count(method));
      continue;
    }
    always_assert(!returning_methods.count(method));
    non_returning_dependencies.insert(method);
    add(map);
  }
  for (auto&& [method, mrefs_gatherer] :
       UnorderedIterable(remaining_mrefs_gatherers)) {
    auto set = mrefs_gatherer->get_non_returning_insns();
    if (!set.empty()) {
      non_returning_insns.emplace(method, std::move(set));
    }
  }
  std::atomic<uint64_t> concurrent_instructions_unvisited{0};
  workqueue_run<std::pair<const DexMethod*, const MethodReferencesGatherer*>>(
      [&](std::pair<const DexMethod*, const MethodReferencesGatherer*> p) {
        auto ii = InstructionIterable(p.first->get_code()->cfg());
        size_t size = std::distance(ii.begin(), ii.end());
        auto visited = p.second->get_instructions_visited();
        always_assert_log(
            visited <= size, "[%s] visited instructions %u <= %zu:\n%s",
            SHOW(p.first), visited, size, SHOW(p.first->get_code()->cfg()));
        concurrent_instructions_unvisited += size - visited;
      },
      remaining_mrefs_gatherers);
  instructions_unvisited = (uint64_t)concurrent_instructions_unvisited;
  TRACE(RMU, 1,
        "%zu uninstantiable_dependencies, %zu non_returning_dependencies, "
        "%" PRIu64 " instructions_unvisited",
        uninstantiable_dependencies.size(), non_returning_dependencies.size(),
        instructions_unvisited);

  // Prune all unmarked methods from callable_instance_methods
  std::vector<const DexMethod*> to_erase;
  for (const auto* m : UnorderedIterable(callable_instance_methods)) {
    if (!reachable_objects.marked_unsafe(m)) {
      to_erase.push_back(m);
    }
  }
  for (const auto* m : to_erase) {
    callable_instance_methods.erase(m);
  }
}

std::unique_ptr<ReachableObjects> compute_reachable_objects(
    const Scope& scope,
    const method_override_graph::Graph& method_override_graph,
    const IgnoreSets& ignore_sets,
    int* num_ignore_check_strings,
    ReachableAspects* reachable_aspects,
    bool record_reachability,
    bool relaxed_keep_class_members,
    bool relaxed_keep_interfaces,
    bool cfg_gathering_check_instantiable,
    bool cfg_gathering_check_instance_callable,
    bool cfg_gathering_check_returning,
    bool should_mark_all_as_seed,
    bool remove_no_argument_constructors) {
  Timer t("Marking");
  UnorderedSet<const DexClass*> scope_set(scope.begin(), scope.end());
  auto reachable_objects = std::make_unique<ReachableObjects>();
  ConditionallyMarked cond_marked;

  ConcurrentSet<ReachableObject, ReachableObjectHash> root_set;
  RootSetMarker root_set_marker(method_override_graph, record_reachability,
                                relaxed_keep_class_members,
                                remove_no_argument_constructors, &cond_marked,
                                reachable_objects.get(), &root_set);

  if (should_mark_all_as_seed) {
    root_set_marker.mark_all_as_seed(scope);
  } else {
    root_set_marker.mark(scope);
  }

  size_t num_threads = redex_parallel::default_num_threads();
  Stats stats;
  TransitiveClosureMarkerSharedState shared_state{
      std::move(scope_set),
      &ignore_sets,
      &method_override_graph,
      record_reachability,
      relaxed_keep_class_members,
      relaxed_keep_interfaces,
      cfg_gathering_check_instantiable,
      cfg_gathering_check_instance_callable,
      cfg_gathering_check_returning,
      &cond_marked,
      reachable_objects.get(),
      reachable_aspects,
      &stats};

  workqueue_run<ReachableObject>(
      [&](TransitiveClosureMarkerWorkerState* worker_state,
          const ReachableObject& obj) {
        TransitiveClosureMarkerWorker worker(&shared_state, worker_state);
        worker.visit(obj);
        return nullptr;
      },
      root_set, num_threads,
      /*push_tasks_while_running=*/true);
  compute_zombie_methods(method_override_graph, *reachable_objects,
                         *reachable_aspects);

  if (num_ignore_check_strings != nullptr) {
    *num_ignore_check_strings = (int)stats.num_ignore_check_strings;
  }

  reachable_aspects->finish(cond_marked, *reachable_objects);

  return reachable_objects;
}

void ReachableObjects::record_reachability(const DexMethodRef* member,
                                           const DexClass* cls) {
  // Each class member trivially retains its containing class; let's filter out
  // this uninteresting information from our diagnostics.
  if (member->get_class() == cls->get_type()) {
    return;
  }
  m_retainers_of.update(ReachableObject(cls),
                        [&](const ReachableObject&, ReachableObjectSet& set,
                            bool /* exists */) { set.emplace(member); });
}

void ReachableObjects::record_reachability(const DexFieldRef* member,
                                           const DexClass* cls) {
  if (member->get_class() == cls->get_type()) {
    return;
  }
  m_retainers_of.update(ReachableObject(cls),
                        [&](const ReachableObject&, ReachableObjectSet& set,
                            bool /* exists */) { set.emplace(member); });
}

template <class Object>
void ReachableObjects::record_reachability(Object* parent, Object* object) {
  if (parent == object) {
    return;
  }
  m_retainers_of.update(ReachableObject(object),
                        [&](const ReachableObject&, ReachableObjectSet& set,
                            bool /* exists */) { set.emplace(parent); });
}

template <class Parent, class Object>
void ReachableObjects::record_reachability(Parent* parent, Object* object) {
  m_retainers_of.update(ReachableObject(object),
                        [&](const ReachableObject&, ReachableObjectSet& set,
                            bool /* exists */) { set.emplace(parent); });
}

template <class Seed>
void ReachableObjects::record_is_seed(Seed* seed) {
  redex_assert(seed != nullptr);
  const auto& keep_reasons = seed->rstate.keep_reasons();
  m_retainers_of.update(
      ReachableObject(seed),
      [&](const ReachableObject&, ReachableObjectSet& set, bool /* exists */) {
        for (const auto& reason : UnorderedIterable(keep_reasons)) {
          // -keepnames rules are irrelevant when analyzing reachability
          if (reason->type == keep_reason::KEEP_RULE &&
              reason->keep_rule->allowshrinking) {
            continue;
          }
          set.emplace(reason);
        }
      });
}

/*
 * Remove unmarked classes / methods / fields. and add all swept objects to
 * :removed_symbols.
 */
template <class Container, typename EraseHookFn>
static void sweep_if_unmarked(const ReachableObjects& reachables,
                              EraseHookFn erase_hook,
                              Container* c,
                              ConcurrentSet<std::string>* removed_symbols) {
  auto p = [&](const auto& m) {
    if (reachables.marked_unsafe(m) == 0) {
      TRACE(RMU, 2, "Removing %s", SHOW(m));
      return false;
    }
    return true;
  };
  const auto it = std::partition(c->begin(), c->end(), p);
  if (removed_symbols) {
    for (auto i = it; i != c->end(); i++) {
      removed_symbols->insert(show_deobfuscated(*i));
      erase_hook(*i);
    }
  } else {
    for (auto i = it; i != c->end(); i++) {
      erase_hook(*i);
    }
  }
  c->erase(it, c->end());
}

void sweep_interfaces(const ReachableObjects& reachables, DexClass* cls) {
  UnorderedSet<const DexType*> new_interfaces_set;
  std::vector<const DexType*> new_interfaces_vec;
  std::function<void(DexTypeList*)> visit;
  visit = [&](auto* interfaces) {
    for (auto* intf : *interfaces) {
      auto cls_intf = type_class(intf);
      if (cls_intf == nullptr || cls_intf->is_external() ||
          reachables.marked_unsafe(cls_intf)) {
        if (new_interfaces_set.insert(intf).second) {
          new_interfaces_vec.push_back(intf);
        }
        continue;
      }
      visit(cls_intf->get_interfaces());
    }
  };
  visit(cls->get_interfaces());
  always_assert(new_interfaces_set.size() == new_interfaces_vec.size());
  auto* new_interfaces =
      DexTypeList::make_type_list(std::move(new_interfaces_vec));
  if (new_interfaces == cls->get_interfaces()) {
    return;
  }
  TRACE(RMU, 2, "Changing interfaces of %s from {%s} to {%s}", SHOW(cls),
        SHOW(cls->get_interfaces()), SHOW(new_interfaces));
  cls->set_interfaces(new_interfaces);
}

using MarkedAnnotationMembers =
    InsertOnlyConcurrentMap<const DexClass*,
                            std::set<const DexString*, dexstrings_comparator>>;

EncodedAnnotations sweep_annotation_elements(
    const MarkedAnnotationMembers& marked_annotation_members,
    const DexType* annotation_type,
    const EncodedAnnotations& annotation_elements,
    size_t* changes) {
  auto* anno_cls = type_class(annotation_type);
  auto vmethod_names_it = anno_cls == nullptr || anno_cls->is_external()
                              ? marked_annotation_members.end()
                              : marked_annotation_members.find(anno_cls);
  EncodedAnnotations new_elements;
  auto push_orig = [&](const DexAnnotationElement& element) {
    new_elements.push_back(element.clone());
  };
  auto should_keep = [&](const DexString* string) {
    // If the type of this annotation is unknown, or external, keep all
    // annotation elements.
    if (vmethod_names_it == marked_annotation_members.end()) {
      return true;
    }
    const auto& vmethod_names = vmethod_names_it->second;
    return vmethod_names.find(string) != vmethod_names.end();
  };

  for (const auto& element : annotation_elements) {
    if (should_keep(element.string)) {
      TRACE(REACH, 5,
            "Annotation instances of type %s will keep element named %s",
            SHOW(annotation_type), SHOW(element.string));
      // Recurse and look for inner annotations.
      if (element.encoded_value->evtype() == DEVT_ANNOTATION) {
        auto* eva = dynamic_cast<DexEncodedValueAnnotation*>(
            element.encoded_value.get());
        size_t inner_changes{0};
        auto inner_new_elements =
            sweep_annotation_elements(marked_annotation_members, eva->type(),
                                      eva->annotations(), &inner_changes);
        if (inner_changes != 0) {
          auto new_eva =
              std::unique_ptr<DexEncodedValue>(new DexEncodedValueAnnotation(
                  eva->type(), std::move(inner_new_elements)));
          DexAnnotationElement new_element(element.string, std::move(new_eva));
          new_elements.push_back(std::move(new_element));
          *changes += inner_changes;
        } else {
          push_orig(element);
        }
      } else {
        push_orig(element);
      }
    } else {
      TRACE(REACH, 5,
            "Annotation instances of type %s will DROP element named %s",
            SHOW(annotation_type), SHOW(element.string));
      (*changes)++;
    }
  }
  return new_elements;
}

size_t sweep_annotation_set(
    const MarkedAnnotationMembers& marked_annotation_members,
    const DexAnnotationSet* aset,
    DexAnnotationSet* output) {
  always_assert(aset != nullptr);
  always_assert(output != nullptr);

  size_t changes{0};
  for (const auto& anno : aset->get_annotations()) {
    auto updated_anno =
        std::make_unique<DexAnnotation>(anno->type(), anno->viz());
    auto new_elements = sweep_annotation_elements(
        marked_annotation_members, anno->type(), anno->anno_elems(), &changes);
    for (auto& new_element : new_elements) {
      updated_anno->add_element(new_element.clone());
    }
    output->add_annotation(std::move(updated_anno));
  }
  return changes;
}

template <class DexMember>
size_t sweep_annotations_impl(
    const MarkedAnnotationMembers& marked_annotation_members,
    DexMember* member) {
  auto aset = member->get_anno_set();
  if (aset == nullptr) {
    return 0;
  }
  auto updated_set = std::make_unique<DexAnnotationSet>();
  auto changes =
      sweep_annotation_set(marked_annotation_members, aset, updated_set.get());
  if (changes > 0) {
    auto& dest_vec = aset->get_annotations();
    dest_vec.clear();
    auto& src_vec = updated_set->get_annotations();
    std::move(src_vec.begin(), src_vec.end(), std::back_inserter(dest_vec));
  }
  return changes;
}

size_t sweep_annotations(
    const ReachableObjects& reachables,
    const MarkedAnnotationMembers& marked_annotation_members,
    DexClass* cls) {
  always_assert(reachables.marked(cls));
  auto changes = sweep_annotations_impl(marked_annotation_members, cls);
  for (auto* const m : cls->get_all_methods()) {
    changes += sweep_annotations_impl(marked_annotation_members, m);
  }
  for (auto* const f : cls->get_all_fields()) {
    changes += sweep_annotations_impl(marked_annotation_members, f);
  }
  TRACE(REACH, 4, "swept %zu annotation elements on class %s", changes,
        SHOW(cls));
  return changes;
}

std::vector<DexClass*> mark_classes_abstract(
    DexStoresVector& stores,
    const ReachableObjects& reachables,
    const ReachableAspects& reachable_aspects) {
  std::vector<DexClass*> res;
  for (auto& store : stores) {
    for (auto& classes : store.get_dexen()) {
      for (auto* cls : classes) {
        if (!is_abstract(cls) &&
            (reachable_aspects.directly_instantiable_types.count_unsafe(
                 cls->get_type()) == 0u) &&
            reachables.marked_unsafe(cls)) {
          cls->set_access((cls->get_access() & ~ACC_FINAL) | ACC_ABSTRACT);
          res.push_back(cls);
        }
      }
    }
  }
  return res;
}

void sweep(DexStoresVector& stores,
           const ReachableObjects& reachables,
           ConcurrentSet<std::string>* removed_symbols,
           bool output_full_removed_symbols) {
  Timer t("Sweep");
  auto scope = build_class_scope(stores);

  UnorderedSet<DexClass*> sweeped_classes;
  for (auto& dex : DexStoreClassesIterator(stores)) {
    sweep_if_unmarked(
        reachables, [&](auto cls) { sweeped_classes.insert(cls); }, &dex,
        removed_symbols);
  }

  walk::parallel::classes(scope, [&](DexClass* cls) {
    if (sweeped_classes.count(cls) != 0u) {
      for (auto* field : cls->get_all_fields()) {
        DexField::delete_field_DO_NOT_USE(field);
      }
      cls->get_ifields().clear();
      cls->get_sfields().clear();
      for (auto* method : cls->get_all_methods()) {
        if ((removed_symbols != nullptr) && output_full_removed_symbols) {
          removed_symbols->insert(show_deobfuscated(method));
        }
        DexMethod::delete_method(method);
      }
      cls->get_dmethods().clear();
      cls->get_vmethods().clear();
      auto* anno_set = cls->get_anno_set();
      if (anno_set != nullptr) {
        anno_set->get_annotations().clear();
      }
      return;
    }
    sweep_if_unmarked(reachables, DexField::delete_field_DO_NOT_USE,
                      &cls->get_ifields(), removed_symbols);
    sweep_if_unmarked(reachables, DexField::delete_field_DO_NOT_USE,
                      &cls->get_sfields(), removed_symbols);
    sweep_if_unmarked(reachables, DexMethod::delete_method,
                      &cls->get_dmethods(), removed_symbols);
    sweep_if_unmarked(reachables, DexMethod::delete_method,
                      &cls->get_vmethods(), removed_symbols);
    sweep_interfaces(reachables, cls);
  });
}

size_t sweep_annotation_elements(DexStoresVector& stores,
                                 const ReachableObjects& reachables) {
  Timer t("Sweep annotation elements");
  auto scope = build_class_scope(stores);
  // For ease of matching, store up-front the vmethod names of annotation
  // classes that are marked. Annotation elements have only a name, not a
  // method/proto to match against to know what is marked/unmarked.
  MarkedAnnotationMembers marked_annotation_members;
  walk::parallel::classes(scope, [&](DexClass* cls) {
    if (is_annotation(cls)) {
      always_assert(reachables.marked(cls));
      std::set<const DexString*, dexstrings_comparator> vmethod_names;
      for (auto* m : cls->get_vmethods()) {
        always_assert(reachables.marked(m));
        TRACE(REACH, 5, "Marked annotation member %s -> %s", SHOW(cls),
              SHOW(m));
        vmethod_names.emplace(m->get_name());
      }
      marked_annotation_members.emplace(cls, std::move(vmethod_names));
    }
  });

  std::atomic<size_t> swept_annotation_elements{0};
  walk::parallel::classes(scope, [&](DexClass* cls) {
    swept_annotation_elements +=
        sweep_annotations(reachables, marked_annotation_members, cls);
  });
  return swept_annotation_elements;
}

void reanimate_zombie_methods(const ReachableAspects& reachable_aspects) {
  for (auto* m : reachable_aspects.zombie_methods) {
    auto& cfg = m->get_code()->cfg();
    remove_uninstantiables_impl::replace_all_with_unreachable_throw(cfg);
    m->clear_annotations();
    m->release_param_anno();
  }
}

void sweep_code(
    DexStoresVector& stores,
    bool prune_uncallable_instance_method_bodies,
    bool skip_uncallable_virtual_methods,
    const ReachableAspects& reachable_aspects,
    remove_uninstantiables_impl::Stats* remove_uninstantiables_stats,
    std::atomic<size_t>* throws_inserted,
    InsertOnlyConcurrentSet<DexMethod*>* affected_methods) {
  Timer t("Sweep Code");
  auto scope = build_class_scope(stores);
  UnorderedSet<const DexType*> uninstantiable_types;
  UnorderedSet<DexMethod*> uncallable_instance_methods;
  for (auto* cls : scope) {
    if (reachable_aspects.instantiable_types.count_unsafe(cls) == 0u) {
      uninstantiable_types.insert(cls->get_type());
    }
    if (prune_uncallable_instance_method_bodies) {
      for (auto* m : cls->get_dmethods()) {
        if (!is_static(m) &&
            (reachable_aspects.callable_instance_methods.count_unsafe(m) ==
             0u)) {
          uncallable_instance_methods.insert(m);
        }
      }
      for (auto* m : cls->get_vmethods()) {
        if (reachable_aspects.callable_instance_methods.count_unsafe(m) == 0u) {
          uncallable_instance_methods.insert(m);
        }
      }
    }
  }
  uninstantiable_types.insert(type::java_lang_Void());
  *remove_uninstantiables_stats = walk::parallel::methods<
      remove_uninstantiables_impl::Stats>(scope, [&](DexMethod* method) {
    auto* code = method->get_code();
    if ((code == nullptr) || method->rstate.no_optimizations()) {
      return remove_uninstantiables_impl::Stats();
    }
    always_assert(code->cfg_built());
    auto& cfg = code->cfg();
    auto non_returning_it = reachable_aspects.non_returning_insns.find(method);
    if (non_returning_it != reachable_aspects.non_returning_insns.end()) {
      const auto& non_returning_insns = non_returning_it->second;
      throw_propagation_impl::ThrowPropagator impl(cfg, method);
      for (auto* block : cfg.blocks()) {
        auto ii = InstructionIterable(block);
        for (auto it = ii.begin(); it != ii.end(); it++) {
          if (non_returning_insns.count(it->insn) == 0u) {
            continue;
          }
          if (impl.try_apply(block->to_cfg_instruction_iterator(it))) {
            (*throws_inserted)++;
          }
          // Stop processing more instructions in this block
          break;
        }
      }
      cfg.remove_unreachable_blocks();
      affected_methods->insert(method);
    }
    if (uncallable_instance_methods.count(method) != 0u) {
      if (skip_uncallable_virtual_methods && method->is_virtual()) {
        return remove_uninstantiables_impl::Stats();
      }
      affected_methods->insert(method);
      return remove_uninstantiables_impl::replace_all_with_unreachable_throw(
          cfg);
    }
    auto stats = remove_uninstantiables_impl::replace_uninstantiable_refs(
        uninstantiable_types, cfg);
    if (stats.sum() != 0) {
      cfg.remove_unreachable_blocks();
      affected_methods->insert(method);
    }
    return stats;
  });
}

remove_uninstantiables_impl::Stats sweep_uncallable_virtual_methods(
    DexStoresVector& stores, const ReachableAspects& reachable_aspects) {
  Timer t("Sweep Uncallable Virtual Methods");
  auto scope = build_class_scope(stores);
  // We determine which methods are responsible for ultimately overriding
  // abstract methods, if any, so that we won't make them abstract or remove
  // them.
  ConcurrentSet<const DexMethod*> implementation_methods;
  workqueue_run<const DexType*>(
      [&](const DexType* type) {
        UnorderedMap<const DexString*, UnorderedSet<const DexProto*>>
            implemented;
        for (auto* cls = type_class(type);
             (cls != nullptr) && !is_interface(cls) && !cls->is_external();
             cls = type_class(cls->get_super_class())) {
          for (auto* m : cls->get_vmethods()) {
            if (implemented[m->get_name()].insert(m->get_proto()).second) {
              if (is_abstract(m)) {
                TRACE(REACH, 1,
                      "[sweeping] abstract method {%s} is not overridden in "
                      "directly "
                      "instantiable class {%s}",
                      SHOW(m), SHOW(type));
                continue;
              }
              implementation_methods.insert(m);
            }
          }
        }
      },
      reachable_aspects.directly_instantiable_types);
  ConcurrentSet<DexMethod*> uncallable_instance_methods;
  for (auto* cls : scope) {
    if (is_interface(cls)) {
      // TODO: Is this needed?
      continue;
    }
    walk::methods((Scope){cls}, [&](DexMethod* m) {
      if (is_static(m)) {
        return;
      }
      if (!m->rstate.no_optimizations() && (m->get_code() != nullptr) &&
          (reachable_aspects.callable_instance_methods.count_unsafe(m) == 0u)) {
        uncallable_instance_methods.insert(m);
      }
    });
  }
  auto is_implementation_method = [&](const DexMethod* m) {
    return implementation_methods.count_unsafe(m) != 0;
  };
  return remove_uninstantiables_impl::reduce_uncallable_instance_methods(
      scope, uncallable_instance_methods, is_implementation_method);
}

void report(PassManager& pm,
            const ReachableObjects& reachable_objects,
            const ReachableAspects& reachable_aspects) {
  pm.set_metric("marked_classes", reachable_objects.num_marked_classes());
  pm.set_metric("marked_fields", reachable_objects.num_marked_fields());
  pm.set_metric("marked_methods", reachable_objects.num_marked_methods());
  pm.incr_metric("dynamically_referenced_classes",
                 reachable_aspects.dynamically_referenced_classes.size());
  pm.incr_metric("instantiable_types",
                 reachable_aspects.instantiable_types.size());
  pm.incr_metric("uninstantiable_dependencies",
                 reachable_aspects.uninstantiable_dependencies.size());
  pm.incr_metric("instructions_unvisited",
                 reachable_aspects.instructions_unvisited);
  pm.incr_metric("callable_instance_methods",
                 reachable_aspects.callable_instance_methods.size());
  pm.incr_metric("exact_invoke_virtual_targets",
                 reachable_aspects.exact_invoke_virtual_targets.size());
  pm.incr_metric("base_invoke_virtual_targets",
                 reachable_aspects.base_invoke_virtual_targets.size());
  pm.incr_metric("directly_instantiable_types",
                 reachable_aspects.directly_instantiable_types.size());
  pm.incr_metric("implementation_methods",
                 reachable_aspects.implementation_methods.size());
  pm.incr_metric(
      "incomplete_directly_instantiable_types",
      reachable_aspects.incomplete_directly_instantiable_types.size());
  pm.incr_metric("zombie_implementation_methods",
                 reachable_aspects.zombie_implementation_methods.size());
  pm.incr_metric("zombie_methods", reachable_aspects.zombie_methods.size());
  pm.incr_metric("returning_methods",
                 reachable_aspects.returning_methods.size());
}

ObjectCounts count_objects(const DexStoresVector& stores) {
  ObjectCounts counts;
  for (auto const& dex : DexStoreClassesIterator(stores)) {
    counts.num_classes += dex.size();
    for (auto const& cls : dex) {
      counts.num_fields += cls->get_ifields().size();
      counts.num_fields += cls->get_sfields().size();
      counts.num_methods += cls->get_dmethods().size();
      counts.num_methods += cls->get_vmethods().size();
    }
  }
  return counts;
}

namespace {

/*
 * Answers "will `sweep` delete this?", evaluated before any sweeping has run.
 *
 * A class is removed when it was not marked. Every member of a removed class
 * goes with it whatever its own mark state, because the wholly-removed-class
 * branch of `sweep` deletes them all; an unmarked member of a surviving class
 * is removed on its own. Redex only deletes what it owns, so the in-scope check
 * gates the member predicate as well as the class one.
 */
class RemovedObjectPredicate {
 public:
  RemovedObjectPredicate(const Scope& scope, const ReachableObjects& reachables)
      : m_scope_set(scope.begin(), scope.end()), m_reachables(reachables) {}

  bool is_removed(const DexClass* cls) const {
    return in_scope(cls) && !m_reachables.marked_unsafe(cls);
  }

  template <class DexMember>
  bool is_removed_member(const DexClass* owner, const DexMember* member) const {
    return in_scope(owner) && (!m_reachables.marked_unsafe(owner) ||
                               !m_reachables.marked_unsafe(member));
  }

  template <class DexMember>
  bool is_removed_member(const DexMember* member) const {
    return is_removed_member(type_class(member->get_class()), member);
  }

 private:
  bool in_scope(const DexClass* cls) const {
    return cls != nullptr && !cls->is_external() &&
           m_scope_set.count(cls) != 0u;
  }

  UnorderedSet<const DexClass*> m_scope_set;
  const ReachableObjects& m_reachables;
};

// The direct references of one source object, gathered before any lock is
// taken.
struct SourceReferences {
  std::vector<const DexType*> types;
  std::vector<DexFieldRef*> fields;
  std::vector<DexMethodRef*> methods;
};

/*
 * Shallow on purpose: the members of a removed class are sources in their own
 * right, and `DexClass::gather_*` recurses into them, which would attribute
 * every member's dependencies to the class.
 */
void gather_class_references(const DexClass* cls, SourceReferences* refs) {
  refs->types.push_back(cls->get_super_class());
  for (const auto* intf : *cls->get_interfaces()) {
    refs->types.push_back(intf);
  }
  const auto* annos = cls->get_anno_set();
  if (annos == nullptr) {
    return;
  }
  for (const auto& anno : annos->get_annotations()) {
    // Inner-class annotations, which the marker ignores as well.
    if (anno->type() == type::dalvik_annotation_MemberClasses()) {
      continue;
    }
    anno->gather_types(refs->types);
    anno->gather_fields(refs->fields);
    anno->gather_methods(refs->methods);
  }
}

void gather_field_references(const DexField* field, SourceReferences* refs) {
  // `DexField::gather_types` only covers the static value and the annotations,
  // so the declared type has to come from the shallow gather.
  field->gather_types_shallow(refs->types);
  field->gather_types(refs->types);
  field->gather_fields(refs->fields);
  field->gather_methods(refs->methods);
}

void gather_method_references(const DexMethod* method, SourceReferences* refs) {
  // `DexMethod::gather_types` subsumes the shallow prototype gather, and reads
  // the CFG when one is built.
  method->gather_types(refs->types);
  method->gather_fields(refs->fields);
  method->gather_methods(refs->methods);
}

/*
 * Turns gathered references into edges. Targets are normalized -- arrays to
 * their element class, refs to their definitions -- and kept only when they
 * were removed too, so the result is the subgraph induced on removed objects.
 */
class RemovedEdgeRecorder {
 public:
  RemovedEdgeRecorder(const RemovedObjectPredicate& removed,
                      ReachableObjectGraph& graph)
      : m_removed(removed), m_graph(graph) {}

  /*
   * `owner` is the class declaring `source`, or `source` itself when that is a
   * class. Edges to it are dropped, mirroring how the reachability graph
   * suppresses the trivial member-to-own-class reference.
   */
  void record(const ReachableObject& source,
              const DexClass* owner,
              const SourceReferences& refs) const {
    UnorderedSet<ReachableObject, ReachableObjectHash> targets;
    for (const auto* type : refs.types) {
      const auto* cls = type_class(type::make_element_type_if_array(type));
      if (cls != owner && m_removed.is_removed(cls)) {
        targets.insert(ReachableObject(cls));
      }
    }
    for (auto* ref : refs.fields) {
      auto* def = ref->as_def();
      if (def == nullptr) {
        def = resolve_field(ref->get_class(), ref->get_name(), ref->get_type());
      }
      if (def != nullptr && m_removed.is_removed_member(def)) {
        targets.insert(ReachableObject(def));
      }
    }
    for (auto* ref : refs.methods) {
      const auto* def =
          resolve_without_context(ref, type_class(ref->get_class()));
      if (def != nullptr && m_removed.is_removed_member(def)) {
        targets.insert(ReachableObject(def));
      }
    }
    for (const auto& target : UnorderedIterable(targets)) {
      if (!(target == source)) {
        record_edge(source, target);
      }
    }
  }

  // Stored in the retainers_of orientation: `source` becomes a predecessor of
  // `target`.
  void record_edge(const ReachableObject& source,
                   const ReachableObject& target) const {
    m_graph.update(target,
                   [&source](const ReachableObject&, ReachableObjectSet& set,
                             bool /* exists */) { set.emplace(source); });
  }

 private:
  const RemovedObjectPredicate& m_removed;
  ReachableObjectGraph& m_graph;
};

} // namespace

ReachableObjectGraph compute_removed_reachability_graph(
    const Scope& scope, const ReachableObjects& reachables) {
  Timer t("Computing removed reachability graph");
  RemovedObjectPredicate removed(scope, reachables);
  ReachableObjectGraph graph;

  // Every removed object becomes a key, so that isolated ones are still
  // serialized and so that the roots are exactly the keys whose predecessor set
  // is still empty once edges have been gathered.
  walk::parallel::classes(scope, [&](DexClass* cls) {
    if (removed.is_removed(cls)) {
      graph.emplace(ReachableObject(cls));
    }
    for (auto* field : cls->get_all_fields()) {
      if (removed.is_removed_member(cls, field)) {
        graph.emplace(ReachableObject(field));
      }
    }
    for (auto* method : cls->get_all_methods()) {
      if (removed.is_removed_member(cls, method)) {
        graph.emplace(ReachableObject(method));
      }
    }
  });

  // A removed class also gets an edge to each member it takes with it. The
  // reverse containment edge is deliberately absent, so that a member cannot
  // keep its own class from being a root.
  RemovedEdgeRecorder recorder(removed, graph);
  walk::parallel::classes(scope, [&](DexClass* cls) {
    bool class_removed = removed.is_removed(cls);
    if (class_removed) {
      SourceReferences refs;
      gather_class_references(cls, &refs);
      recorder.record(ReachableObject(cls), cls, refs);
    }
    for (auto* field : cls->get_all_fields()) {
      if (!removed.is_removed_member(cls, field)) {
        continue;
      }
      if (class_removed) {
        recorder.record_edge(ReachableObject(cls), ReachableObject(field));
      }
      SourceReferences refs;
      gather_field_references(field, &refs);
      recorder.record(ReachableObject(field), cls, refs);
    }
    for (auto* method : cls->get_all_methods()) {
      if (!removed.is_removed_member(cls, method)) {
        continue;
      }
      if (class_removed) {
        recorder.record_edge(ReachableObject(cls), ReachableObject(method));
      }
      SourceReferences refs;
      gather_method_references(method, &refs);
      recorder.record(ReachableObject(method), cls, refs);
    }
  });

  return graph;
}

// Graph serialization helpers
namespace {

void write_reachable_object(std::ostream& os, const ReachableObject& obj) {
  bs::write<uint8_t>(os, static_cast<uint8_t>(obj.type));
  std::ostringstream ss;
  ss << obj;
  const auto& s = ss.str();
  bs::write<uint32_t>(os, s.size());
  os << s;
}

} // namespace

void dump_graph(std::ostream& os, const ReachableObjectGraph& retainers_of) {
  auto compare = [](const ReachableObject& lhs, const ReachableObject& rhs) {
    if (lhs.type != rhs.type) {
      return lhs.type < rhs.type;
    }
    switch (lhs.type) {
    case ReachableObjectType::CLASS:
      return compare_dexclasses(lhs.cls, rhs.cls);
    case ReachableObjectType::FIELD:
      return compare_dexfields(lhs.field, rhs.field);
    case ReachableObjectType::METHOD:
      return compare_dexmethods(lhs.method, rhs.method);

    case ReachableObjectType::ANNO:
    case ReachableObjectType::SEED: {
      // Pretty terrible, optimize.
      std::ostringstream oss1;
      oss1 << lhs;
      std::ostringstream oss2;
      oss2 << rhs;
      return oss1.str() < oss2.str();
    }

    case ReachableObjectType::INSTANTIABLE:
    case ReachableObjectType::METHOD_REFERENCES_GATHERER_INSTANTIABLE:
    case ReachableObjectType::RETURNS:
    case ReachableObjectType::METHOD_REFERENCES_GATHERER_RETURNING:
      __builtin_unreachable();
    }
    __builtin_unreachable();
  };

  bs::write_header(os, /* version */ 1);
  bs::GraphWriter<ReachableObject, ReachableObjectHash> gw(
      write_reachable_object,
      [&](const ReachableObject& obj) -> std::vector<ReachableObject> {
        if (retainers_of.count(obj) == 0u) {
          return {};
        }
        const auto& preds = retainers_of.at_unsafe(obj);
        auto preds_vec = unordered_to_ordered(preds, compare);
        return preds_vec;
      });

  // Gotta sort the keys or the output is nondeterministic.
  auto keys = unordered_to_ordered_keys(retainers_of, compare);
  gw.write(os, keys);
}

template void TransitiveClosureMarkerWorker::push<DexClass>(
    const DexClass* parent, const DexType* type);
} // namespace reachability
