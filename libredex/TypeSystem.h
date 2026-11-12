/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "ClassHierarchy.h"
#include "DeterministicContainers.h"
#include "DexClass.h"

using TypeVector = std::vector<const DexType*>;
using InstanceOfTable = UnorderedMap<const DexType*, TypeVector>;
using TypeToTypeSet = UnorderedMap<const DexType*, TypeSet>;

/**
 * TypeSystem
 * A class that computes information and caches on the current known state
 * of the universe given a Scope.
 * It provides common API to an object-oriented type system: inheritance
 * relationships and interface relationships.
 *
 * NOTE: if you only need class-level relationships, use ClassHierarchy
 * directly -- the interface tables built here are the reason to reach for
 * TypeSystem. For method-level relationships use MethodOverrideGraph, or
 * virtual_scope::VirtualScopes when you need scopes rather than edges.
 */
class TypeSystem {
 private:
  static const TypeSet& get_empty_set() {
    static const TypeSet empty_set;
    return empty_set;
  }
  static const TypeVector& get_empty_vec() {
    static const TypeVector empty_vec;
    return empty_vec;
  }

  SubtypeMaps m_subtypes;
  InstanceOfTable m_instanceof_table;
  TypeToTypeSet m_interfaces;

 public:
  explicit TypeSystem(const Scope& scope);

  /**
   * Get the direct children of a given type.
   * The type must be a class (not an interface).
   */
  const TypeSet& get_children(const DexType* type) const {
    const auto& children = m_subtypes.subclasses.find(type);
    return children != m_subtypes.subclasses.end() ? children->second
                                                   : get_empty_set();
  }

  /**
   * Get all the children of a given type.
   * The type must be a class (not an interface).
   */
  void get_all_children(const DexType* type, TypeSet& children) const {
    return ::get_all_children(m_subtypes.subclasses, type, children);
  }

  /**
   * Return the chain of parents for a given type.
   * The type in question is included in the parent chain and it's
   * the last element in the returned vector.
   * The vector is ordered starting from the top type (java.lang.Object)
   * The type must be a class (not an interface).
   */
  const TypeVector& parent_chain(const DexType* type) const {
    const auto& parents = m_instanceof_table.find(type);
    if (parents == m_instanceof_table.end()) {
      return get_empty_vec();
    }
    return parents->second;
  }

  /**
   * Return all interfaces implemented by a given type.
   * A type must be a class (not an interface)
   */
  const TypeSet& get_implemented_interfaces(const DexType* type) const {
    const auto& intfs = m_interfaces.find(type);
    return intfs != m_interfaces.end() ? intfs->second : get_empty_set();
  }

  TypeSet get_implemented_interfaces(const TypeSet& types) const {
    TypeSet implemented_intfs;

    for (const auto& type : types) {
      const auto& cls_intfs = get_implemented_interfaces(type);
      implemented_intfs.insert(cls_intfs.begin(), cls_intfs.end());
    }

    return implemented_intfs;
  }

  /**
   * Returns only the interfaces that are implemented by the provided
   * classes.
   */
  TypeSet get_local_interfaces(const TypeSet& classes);

  /**
   * Return true if child is a subclass or equal to parent.
   * The type must be a class (not an interface).
   */
  bool is_subtype(const DexType* parent, const DexType* child) const {
    const auto& parent_it = m_instanceof_table.find(parent);
    const auto& child_it = m_instanceof_table.find(child);
    if (parent_it == m_instanceof_table.end() ||
        child_it == m_instanceof_table.end()) {
      return false;
    }
    const auto& p_chain = parent_it->second;
    const auto& c_chain = child_it->second;
    if (p_chain.size() > c_chain.size()) {
      return false;
    }
    return c_chain.at(p_chain.size() - 1) == parent;
  }

  /**
   * Return true if a given class implements a given interface.
   * The interface may be implemented via some parent of the class
   * or an interface DAG.
   */
  bool implements(const DexType* cls, const DexType* intf) const {
    const auto& implementors = m_subtypes.implementors.find(intf);
    if (implementors == m_subtypes.implementors.end()) {
      return false;
    }
    return implementors->second.count(cls) > 0;
  }

  /**
   * Return all classes that implement an interface.
   * The interface may be implemented via some parent of the class
   * or an interface DAG.
   * The implication is that all children of a type implementing an
   * interface will be included in the returning set.
   */
  const TypeSet& get_implementors(const DexType* intf) const {
    const auto& implementors = m_subtypes.implementors.find(intf);
    if (implementors == m_subtypes.implementors.end()) {
      return get_empty_set();
    }
    return implementors->second;
  }

  /**
   * Return the set of every parent interface of a given interface.
   * The type must be an interface (not a class).
   * The direct list of interfaces implemented can be retrieved in the
   * DexClass.
   */
  void get_all_super_interfaces(const DexType* intf, TypeSet& supers) const;
  TypeSet get_all_super_interfaces(const DexType* intf) const;

  /**
   * Return the direct children of a given interface.
   * The type must be an interface (not a class).
   */
  const TypeSet& get_interface_children(const DexType* intf) const {
    const auto& children = m_subtypes.subinterfaces.find(intf);
    if (children == m_subtypes.subinterfaces.end()) {
      return get_empty_set();
    }
    return children->second;
  }

  /**
   * Return all the children of a given interface.
   * The type must be an interface (not a class).
   */
  void get_all_interface_children(const DexType* intf,
                                  TypeSet& children) const {
    const auto& direct_children = get_interface_children(intf);
    children.insert(direct_children.begin(), direct_children.end());
    for (const auto& child : direct_children) {
      get_all_interface_children(child, children);
    }
  }

  /**
   * Return the ClassHierarchy known when building the type system.
   * Its lifetime is tied to that of the TypeSystem, as such it should not
   * exceed it.
   */
  const ClassHierarchy& get_class_hierarchy() const {
    return m_subtypes.subclasses;
  }

  /**
   * Return the SubtypeMaps known when building the type system, with the same
   * lifetime as get_class_hierarchy().
   */
  const SubtypeMaps& get_subtype_maps() const { return m_subtypes; }

 private:
  void make_instanceof_interfaces_table();
  void make_interfaces_table(const DexType* type);
};
