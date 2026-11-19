/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "VirtualScopes.h"

#include <algorithm>
#include <functional>
#include <limits>
#include <map>
#include <set>
#include <utility>
#include <vector>

#include "ClassHierarchy.h"
#include "CppUtil.h"
#include "DexAccess.h"
#include "DexClass.h"
#include "GraphUtil.h"
#include "MethodOverrideGraph.h"
#include "TypeUtil.h"

/*
 * MOG-backed implementation. Scopes are derived from MethodOverrideGraph (the
 * shared override representation redex already builds) via the rooted-query
 * helpers, instead of a bespoke signature-map. MOG supplies the override family
 * and interface attribution; the class hierarchy is used only for the two
 * things MOG does not encode: member ORDER (legacy hierarchy pre-order) and
 * ESCAPED (propagation through a branch touching an unresolvable interface).
 * Verified byte-identical to legacy `ClassScopes::get` by test/unit/
 * VirtualScopesDifferentialTest.
 */
namespace virtual_scope {

namespace mog = method_override_graph;

namespace {

using DexTypeSetC = std::set<const DexType*, dextypes_comparator>;

// The class hierarchy as a graph from java.lang.Object to its subclasses, with
// each class's children in TypeSet order.
struct ClassHierarchyGraph {
  using Graph = ClassHierarchy;
  using NodeId = const DexType*;
  using EdgeId = const DexType*;
  static NodeId entry(const Graph&) { return type::java_lang_Object(); }
  static const TypeSet& successors(const Graph& graph, const NodeId& type) {
    return get_children(graph, type);
  }
  static NodeId target(const Graph&, const EdgeId& child) { return child; }
};

} // namespace

VirtualScopes::VirtualScopes(const Scope& scope) {
  mog::GraphConfig cfg;
  cfg.include_miranda = true;
  // Mirandas here are consumed only for `scope`'s own hierarchy, so restrict
  // synthesis to scope U external -- matching the locality of legacy
  // ClassScopes(scope) and avoiding make_method_downcast side effects on other
  // stores' classes.
  cfg.miranda_within_scope = true;
  auto graph = mog::build_graph(scope, cfg);
  const ClassHierarchy hierarchy = build_type_hierarchy(scope);

  // Global class-hierarchy pre-order index (legacy member order). This mirrors
  // legacy build_class_scopes(java.lang.Object): a DFS from Object over
  // build_type_hierarchy(scope) -- which is the internal scope PLUS every
  // external class in the redex context (build_external_hierarchy folds all
  // is_external() classes from g_redex into the hierarchy) -- visiting children
  // in TypeSet (dextypes_comparator) order. The dfs_order keys are therefore
  // exactly the set of types legacy roots scopes for.
  UnorderedMap<const DexType*, size_t> dfs_order;
  for (const auto* t : ::graph::preorder_sort<ClassHierarchyGraph>(hierarchy)) {
    dfs_order.emplace(t, dfs_order.size());
  }

  // ESCAPED: a type is escaped if it -- or any ancestor or descendant --
  // implements an unresolvable interface (no DexClass). MOG has no node for
  // such an interface, so this is computed from the class interface lists.
  UnorderedSet<const DexType*> escaped;
  {
    auto has_unknown_intf = [](const DexClass* c) {
      std::vector<const DexType*> st(c->get_interfaces()->begin(),
                                     c->get_interfaces()->end());
      UnorderedSet<const DexType*> seen;
      while (!st.empty()) {
        const auto* itype = st.back();
        st.pop_back();
        if (!seen.insert(itype).second) {
          continue;
        }
        const auto* icls = type_class(itype);
        if (icls == nullptr) {
          return true;
        }
        for (const auto* s : *icls->get_interfaces()) {
          st.push_back(s);
        }
      }
      return false;
    };
    // Seed from EVERY type in build_type_hierarchy(scope) -- internal scope
    // classes and external (runtime-jar) ancestors alike -- exactly as legacy
    // load_interfaces runs per node over the full hierarchy. Seeding only from
    // internal `scope` would miss an internal mergeable that inherits escape
    // from an external ancestor implementing an unresolvable interface.
    //
    // subtree_visited is a separate downward-walk memo (NOT `escaped`): if the
    // result set doubled as the visited set, a class inserted as one seed's
    // ancestor would find itself already present and abort its own subtree walk
    // when later seeded, dropping its descendants. That would make the result
    // depend on seed order, which is nondeterministic (dfs_order keys are
    // DexType* from parallel dex loading). Keeping it outside the loop is
    // O(V+E).
    UnorderedSet<const DexType*> subtree_visited;
    for (auto&& entry : UnorderedIterable(dfs_order)) {
      const auto* cls = type_class(entry.first);
      if (cls == nullptr || !has_unknown_intf(cls)) {
        continue;
      }
      for (const auto* a = cls->get_super_class(); a != nullptr;) {
        escaped.insert(a);
        const auto* acls = type_class(a);
        a = acls != nullptr ? acls->get_super_class() : nullptr;
      }
      std::vector<const DexType*> st{cls->get_type()};
      while (!st.empty()) {
        const auto* t = st.back();
        st.pop_back();
        if (!subtree_visited.insert(t).second) {
          continue;
        }
        escaped.insert(t);
        auto hit = hierarchy.find(t);
        if (hit != hierarchy.end()) {
          for (const auto* ch : hit->second) {
            st.push_back(ch);
          }
        }
      }
    }
  }

  const auto order_of = [&](const DexMethod* m) {
    auto it = dfs_order.find(m->get_class());
    return it != dfs_order.end() ? it->second
                                 : std::numeric_limits<size_t>::max();
  };

  // Project one rooted scope into the public VirtualScope, indexed under
  // `type`.
  const auto add_scope = [&](const DexType* type, DexMethod* root,
                             std::vector<DexMethod*> family,
                             const DexTypeSetC& intfs) {
    // `root` (the topmost dispatch root) stays methods[0]; sort the remaining
    // members by hierarchy pre-order. Sorting the whole vector would sink an
    // external root (no dfs_order -> max) to the end -- legacy keeps it first.
    if (family.size() > 1) {
      std::sort(family.begin() + 1, family.end(),
                [&](const DexMethod* a, const DexMethod* b) {
                  return order_of(a) < order_of(b);
                });
    }
    auto vs = std::unique_ptr<VirtualScope>(new VirtualScope());
    vs->m_root = type;
    vs->m_top_def = root;
    vs->m_methods.reserve(family.size());
    for (auto* m : family) {
      vs->m_methods.push_back(m);
      if (m->is_def()) {
        vs->m_has_def = true;
      }
      // legacy sets VirtualFlags::ESCAPED per member; a scope is escaped if any
      // member's class is in the escaped set (branch touching an unresolvable
      // interface).
      if (escaped.count(m->get_class()) != 0) {
        vs->m_escaped = true;
      }
    }
    for (const auto* i : intfs) {
      vs->m_interfaces.insert(i);
    }
    // legacy is_non_virtual_scope == TOP_DEF|FINAL: a lone root, no interface,
    // not escaped. Restricted to internal-rooted scopes: a scope rooted at an
    // external method (e.g. a java.lang.Object method) stays a plain virtual
    // scope rather than being classified non-virtual.
    const auto* root_cls = type_class(root->get_class());
    const bool root_internal = root_cls != nullptr && !root_cls->is_external();
    vs->m_non_virtual = root_internal && family.size() == 1 && intfs.empty() &&
                        escaped.count(type) == 0;
    m_by_root[type].push_back(vs.get());
    m_storage.push_back(std::move(vs));
  };

  // Legacy interface attribution (VirtualScope.cpp load_interface_methods): a
  // scope's interface set is the union, over every family member's class, of
  // the transitive super-interface closure of that class's directly-declared
  // interfaces, restricted to interfaces that themselves DECLARE a vmethod of
  // the scope's signature. MOG's get_implemented_interfaces yields only the
  // single directly-overridden interface method, not this closure.
  const auto collect_interfaces = [&](const std::vector<DexMethod*>& family,
                                      DexTypeSetC& intfs) {
    const auto* name = family[0]->get_name();
    const auto* proto = family[0]->get_proto();
    const auto declares = [&](const DexClass* icls) {
      for (const auto* im : icls->get_vmethods()) {
        if (im->get_name() == name && im->get_proto() == proto) {
          return true;
        }
      }
      return false;
    };
    UnorderedSet<const DexType*> seen;
    std::vector<const DexType*> st;
    for (const auto* m : family) {
      const auto* c = type_class(m->get_class());
      if (c == nullptr) {
        continue;
      }
      for (const auto* i : *c->get_interfaces()) {
        st.push_back(i);
      }
      // A subclass can declare an interface while inheriting this method from
      // its superclass. MOG records that obligation on the live implementation
      // even when an earlier pass detached the subclass override. Preserve the
      // interface relationship without resurrecting the detached method as a
      // scope member.
      const auto& node = graph->get_node(m);
      if (node.other_interface_implementations != nullptr) {
        for (const auto* parent :
             UnorderedIterable(node.other_interface_implementations->parents)) {
          st.push_back(parent->get_class());
        }
      }
    }
    while (!st.empty()) {
      const auto* it = st.back();
      st.pop_back();
      if (!seen.insert(it).second) {
        continue;
      }
      const auto* icls = type_class(it);
      if (icls == nullptr) {
        continue;
      }
      if (declares(icls)) {
        intfs.insert(it);
      }
      for (const auto* s : *icls->get_interfaces()) {
        st.push_back(s);
      }
    }
  };

  // Group every real vmethod + synthetic miranda node under its topmost
  // class-level dispatch root (find_class_dispatch_root). Each group is one
  // scope, rooted at the dispatch root's class. This unifies plain class scopes
  // (root = the introducing def), interface/miranda scopes (root = a miranda
  // slot at the topmost declaring class), and external-rooted scopes (root = an
  // external method like Object.equals) into a single construction.
  std::map<const DexMethod*, std::vector<DexMethod*>, dexmethods_comparator>
      groups;
  const auto assign = [&](DexMethod* m) {
    const auto* r = mog::find_class_dispatch_root(*graph, m);
    groups[r].push_back(m);
  };
  // Process exactly the type set legacy does: the build_type_hierarchy(scope)
  // nodes, i.e. dfs_order's keys (this-store internal classes PLUS all
  // is_external() classes in the redex context, but NOT other stores' internal
  // classes). MOG's synthesize_miranda_nodes walks ALL of g_redex including
  // other-store internals, so gate both real vmethods and miranda nodes on
  // membership in this set to avoid pulling in types legacy never roots.
  for (auto&& entry : UnorderedIterable(dfs_order)) {
    const auto* cls = type_class(entry.first);
    if (cls == nullptr || is_interface(cls)) {
      continue;
    }
    for (auto* m : cls->get_vmethods()) {
      assign(m);
    }
  }
  for (auto&& [m, node] : UnorderedIterable(graph->nodes())) {
    if (node.is_miranda && dfs_order.count(m->get_class()) != 0) {
      assign(const_cast<DexMethod*>(m));
    }
  }

  for (auto& [root, members] : groups) {
    auto* root_m = const_cast<DexMethod*>(root);
    std::vector<DexMethod*> family;
    family.push_back(root_m);
    for (auto* m : members) {
      if (m != root_m) {
        family.push_back(m);
      }
    }
    DexTypeSetC intfs;
    collect_interfaces(family, intfs);
    add_scope(root_m->get_class(), root_m, std::move(family), intfs);
  }

  // Order the scopes within each type to match legacy get(type)
  // (get_root_scopes): class scopes rooted at a real def come first in the
  // type's vmethod declaration order, then pure-miranda scopes in
  // get_rooted_interface_scope order -- the type's directly-declared interfaces
  // in list order, each interface's own vmethods before its super-interfaces
  // (pre-order DFS, first encounter wins). `groups` is keyed by
  // dexmethods_comparator, which is NOT the legacy order.
  for (auto&& [type, scopes] : UnorderedIterable(m_by_root)) {
    const auto* cls = type_class(type);
    UnorderedMap<const DexMethod*, size_t> vindex;
    size_t nv = 0;
    if (cls != nullptr) {
      for (auto* m : cls->get_vmethods()) {
        vindex[m] = nv++;
      }
    }
    std::map<std::pair<const DexString*, const DexProto*>, size_t> mir_order;
    if (cls != nullptr) {
      size_t mnext = 0;
      UnorderedSet<const DexClass*> walk_visited;
      const auto walk = [&](auto self, const DexClass* c) -> void {
        for (const auto* intf : *c->get_interfaces()) {
          const auto* icls = type_class(intf);
          if (icls == nullptr || !walk_visited.insert(icls).second) {
            continue;
          }
          for (const auto* im : icls->get_vmethods()) {
            mir_order.emplace(std::make_pair(im->get_name(), im->get_proto()),
                              mnext++);
          }
          self(self, icls);
        }
      };
      self_recursive_fn(walk, cls);
    }
    const auto key = [&](const VirtualScope* s) -> size_t {
      const auto* td = s->top_def();
      auto vit = vindex.find(td);
      if (vit != vindex.end()) {
        return vit->second;
      }
      auto mit =
          mir_order.find(std::make_pair(td->get_name(), td->get_proto()));
      return nv + (mit != mir_order.end() ? mit->second : mir_order.size());
    };
    std::stable_sort(scopes.begin(), scopes.end(),
                     [&](const VirtualScope* a, const VirtualScope* b) {
                       return key(a) < key(b);
                     });
  }
}

VirtualScopes::~VirtualScopes() = default;

const std::vector<const VirtualScope*>& VirtualScopes::at(
    const DexType* type) const {
  auto it = m_by_root.find(type);
  if (it != m_by_root.end()) {
    return it->second;
  }
  static const std::vector<const VirtualScope*> empty;
  return empty;
}

const VirtualScope* VirtualScopes::find(const DexMethod* meth) const {
  // Climb `meth`'s superclass chain; at each level return the scope rooted at
  // that type whose top def matches `meth` by name+proto. Since `at(type)`
  // reproduces legacy `ClassScopes::get(type)` exactly, this is byte-for-byte
  // legacy `TypeSystem::find_virtual_scope` (same climb, same match, same
  // nullptr exits).
  const auto* type = meth->get_class();
  while (type != nullptr) {
    for (const auto* scope : at(type)) {
      const auto* td = scope->top_def();
      if (td->get_name() == meth->get_name() &&
          td->get_proto() == meth->get_proto()) {
        return scope;
      }
    }
    const auto* cls = type_class(type);
    if (cls == nullptr) {
      break;
    }
    type = cls->get_super_class();
  }
  return nullptr;
}

void VirtualScopes::walk_interface_scopes(
    const std::function<void(const DexString*,
                             const DexProto*,
                             const std::vector<const VirtualScope*>&,
                             const TypeSet&)>& walker) const {
  // Group interface-implementing scopes by (top-def name, proto). The ordering
  // (dexstrings then dexprotos comparator) reproduces legacy SignatureMap
  // iteration in ClassScopes::walk_all_intf_scopes -- behaviorally significant
  // because the renamer advances a shared seed per group. Scope order WITHIN a
  // group is irrelevant (all scopes in a group are renamed to one shared name).
  std::map<const DexString*,
           std::map<const DexProto*,
                    std::pair<std::vector<const VirtualScope*>, TypeSet>,
                    dexprotos_comparator>,
           dexstrings_comparator>
      groups;
  for (const auto& s : m_storage) {
    if (!s->implements_interface()) {
      continue;
    }
    const auto* td = s->top_def();
    auto& entry = groups[td->get_name()][td->get_proto()];
    entry.first.push_back(s.get());
    for (const auto* i : UnorderedIterable(s->implemented_interfaces())) {
      entry.second.insert(i);
    }
  }
  for (const auto& [name, protos] : groups) {
    for (const auto& [proto, entry] : protos) {
      walker(name, proto, entry.first, entry.second);
    }
  }
}

} // namespace virtual_scope
