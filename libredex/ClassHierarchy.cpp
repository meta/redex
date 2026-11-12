/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ClassHierarchy.h"

#include "Debug.h"
#include "RedexContext.h"
#include "Resolver.h"
#include "Show.h"
#include "TypeUtil.h"

namespace {

static const TypeSet empty_set{};

inline bool match(const DexString* name,
                  const DexProto* proto,
                  const DexMethod* cls_meth) {
  return name == cls_meth->get_name() && proto == cls_meth->get_proto();
}

DexMethod* check_vmethods(const DexString* name,
                          const DexProto* proto,
                          const DexType* type) {
  const DexClass* cls = type_class(type);
  for (const auto& method : cls->get_vmethods()) {
    if (match(name, proto, method)) {
      return method;
    }
  }
  return nullptr;
}

DexMethod* check_dmethods(const DexString* name,
                          const DexProto* proto,
                          const DexType* type) {
  const DexClass* cls = type_class(type);
  for (const auto& method : cls->get_dmethods()) {
    if (match(name, proto, method)) {
      return method;
    }
  }
  return nullptr;
}

/**
 * Creates an entry from a parent to a child class.
 */
void build_class_hierarchy(ClassHierarchy& hierarchy, const DexClass* cls) {
  // ensure an entry for the DexClass is created
  hierarchy[cls->get_type()];
  auto* type = cls->get_type();
  auto* const super = cls->get_super_class();
  if (super != nullptr) {
    hierarchy[super].insert(type);
  } else {
    always_assert_log(cls->get_type() == type::java_lang_Object(), "%s",
                      SHOW(cls->get_type()));
  }
}

void build_external_hierarchy(ClassHierarchy& hierarchy) {
  g_redex->walk_type_class([&](const DexType* /*type*/, const DexClass* cls) {
    if (!cls->is_external() || is_interface(cls)) {
      return;
    }
    build_class_hierarchy(hierarchy, cls);
  });
}

// Find all the interfaces that extend 'intf'
bool gather_intf_extenders(const DexType* extender,
                           const DexType* intf,
                           UnorderedSet<const DexType*>& intf_extenders) {
  bool extends = false;
  const DexClass* extender_cls = type_class(extender);
  if (extender_cls == nullptr) {
    return extends;
  }
  if (is_interface(extender_cls)) {
    for (const auto& extends_intf : *extender_cls->get_interfaces()) {
      if (extends_intf == intf ||
          gather_intf_extenders(extends_intf, intf, intf_extenders)) {
        intf_extenders.insert(extender);
        extends = true;
      }
    }
  }
  return extends;
}

void gather_intf_extenders(const Scope& scope,
                           const DexType* intf,
                           UnorderedSet<const DexType*>& intf_extenders) {
  for (const auto& cls : scope) {
    gather_intf_extenders(cls->get_type(), intf, intf_extenders);
  }
}

void build_interface_map(InterfaceMap& interfaces,
                         const ClassHierarchy& hierarchy,
                         const DexClass* current,
                         const TypeSet& implementors) {
  for (const auto& intf : *current->get_interfaces()) {
    interfaces[intf].insert(implementors.begin(), implementors.end());
    auto* const intf_cls = type_class(intf);
    if (intf_cls == nullptr) {
      continue;
    }
    build_interface_map(interfaces, hierarchy, intf_cls, implementors);
  }
}

void load_interface_children(ClassHierarchy& children, const DexClass* intf) {
  for (const auto& super_intf : *intf->get_interfaces()) {
    children[super_intf].insert(intf->get_type());
    auto* const super_intf_cls = type_class(super_intf);
    if (super_intf_cls != nullptr) {
      load_interface_children(children, super_intf_cls);
    }
  }
}

void load_interface_children(ClassHierarchy& children) {
  g_redex->walk_type_class([&](const DexType* /*type*/, const DexClass* cls) {
    if (!cls->is_external() || !is_interface(cls)) {
      return;
    }
    load_interface_children(children, cls);
  });
}

} // namespace

ClassHierarchy build_internal_type_hierarchy(const Scope& scope) {
  ClassHierarchy hierarchy;
  hierarchy.reserve(std::count_if(scope.begin(), scope.end(), [](auto* cls) {
    return !is_interface(cls);
  }));
  // build the type hierarchy
  for (const auto& cls : scope) {
    if (is_interface(cls)) {
      continue;
    }
    build_class_hierarchy(hierarchy, cls);
  }
  return hierarchy;
}

ClassHierarchy build_type_hierarchy(const Scope& scope) {
  auto hierarchy = build_internal_type_hierarchy(scope);
  build_external_hierarchy(hierarchy);
  return hierarchy;
}

InterfaceMap build_interface_map(const ClassHierarchy& hierarchy) {
  InterfaceMap interfaces;
  // build the type hierarchy
  for (const auto& cls_it : UnorderedIterable(hierarchy)) {
    auto* const cls = type_class(cls_it.first);
    if (cls == nullptr) {
      continue;
    }
    if (is_interface(cls)) {
      continue;
    }
    TypeSet implementors;
    get_all_children(hierarchy, cls->get_type(), implementors);
    implementors.insert(cls->get_type());
    build_interface_map(interfaces, hierarchy, cls, implementors);
  }
  return interfaces;
}

ClassHierarchy build_interface_children(const Scope& scope) {
  ClassHierarchy children;
  for (const auto& cls : scope) {
    if (!is_interface(cls)) {
      continue;
    }
    load_interface_children(children, cls);
  }
  load_interface_children(children);
  return children;
}

SubtypeMaps build_subtype_maps(const Scope& scope) {
  auto subclasses = build_type_hierarchy(scope);
  auto implementors = build_interface_map(subclasses);
  return {std::move(subclasses), std::move(implementors),
          build_interface_children(scope)};
}

const TypeSet& get_children(const ClassHierarchy& hierarchy,
                            const DexType* type) {
  const auto& it = hierarchy.find(type);
  return it != hierarchy.end() ? it->second : empty_set;
}

void get_all_children(const ClassHierarchy& hierarchy,
                      const DexType* type,
                      TypeSet& children) {
  const auto& direct = get_children(hierarchy, type);
  for (const auto& child : direct) {
    children.insert(child);
    get_all_children(hierarchy, child, children);
  }
}

TypeSet get_all_children(const ClassHierarchy& hierarchy, const DexType* type) {
  TypeSet children;
  get_all_children(hierarchy, type, children);
  return children;
}

void get_all_implementors(const Scope& scope,
                          const DexType* intf,
                          TypeSet& impls) {
  UnorderedSet<const DexType*> intf_extenders;
  gather_intf_extenders(scope, intf, intf_extenders);

  UnorderedSet<const DexType*> intfs;
  intfs.insert(intf);
  insert_unordered_iterable(intfs, intf_extenders);

  for (auto* cls : scope) {
    auto* cur = cls;
    bool found = false;
    while (!found && cur != nullptr) {
      for (auto* impl : *cur->get_interfaces()) {
        if (intfs.count(impl) > 0) {
          impls.insert(cls->get_type());
          found = true;
          break;
        }
      }
      cur = type_class(cur->get_super_class());
    }
  }
}

DexMethod* find_collision_excepting(const ClassHierarchy& ch,
                                    const DexMethod* except,
                                    const DexString* name,
                                    const DexProto* proto,
                                    const DexClass* cls,
                                    bool is_virtual,
                                    bool check_direct) {
  for (const auto& method : cls->get_dmethods()) {
    if (match(name, proto, method) && method != except) {
      return method;
    }
  }
  for (const auto& method : cls->get_vmethods()) {
    if (match(name, proto, method) && method != except) {
      return method;
    }
  }
  if (!is_virtual) {
    return nullptr;
  }

  auto* super = type_class(cls->get_super_class());
  if (super != nullptr) {
    auto* method = resolve_virtual_deprecated(super, name, proto);
    if ((method != nullptr) && method != except) {
      return method;
    }
  }

  TypeSet children;
  get_all_children(ch, cls->get_type(), children);
  for (const auto& child : children) {
    auto* vmethod = check_vmethods(name, proto, child);
    if ((vmethod != nullptr) && vmethod != except) {
      return vmethod;
    }
    if (check_direct) {
      auto* dmethod = check_dmethods(name, proto, child);
      if ((dmethod != nullptr) && dmethod != except) {
        return dmethod;
      }
    }
  }
  return nullptr;
}
