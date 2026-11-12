/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "MethodOverrideGraph.h"

#include <iterator>
#include <sparta/PatriciaTreeMap.h>
#include <sparta/PatriciaTreeSet.h>

#include "BinarySerialization.h"
#include "ClassHierarchy.h"
#include "CppUtil.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "RedexContext.h"
#include "Show.h"
#include "Timer.h"
#include "TypeUtil.h"
#include "Walkers.h"

using namespace method_override_graph;

namespace {

using MethodSet = sparta::PatriciaTreeSet<const DexMethod*>;

using ProtoMap = sparta::PatriciaTreeMap<const DexProto*, MethodSet>;

// The set of methods in scope at a particular class. We use PatriciaTreeMaps
// for this because there is a lot shared structure: the maps of subclasses /
// subinterfaces contain many elements from their parent classes / interfaces.
// We also do a lot of unioning operations when analyzing interfaces, and
// PatriciaTreeMaps are well-optimized for that.
using SignatureMap =
    sparta::PatriciaTreeMap<const DexString* /* name */, ProtoMap>;

struct ClassSignatureMap {
  // The methods implemented by the current class or one of its superclasses.
  // The MethodSets here should always be singleton sets.
  SignatureMap implemented;
  // The interface methods not yet implemented by the current class or its
  // superclasses.
  // The MethodSets here can have multiple elements -- a class can implement
  // multiple interfaces where some or all of them define a method with the
  // same signature.
  SignatureMap unimplemented;
};

using ClassSignatureMaps =
    InsertOnlyConcurrentMap<const DexClass*, ClassSignatureMap>;

using InterfaceSignatureMaps =
    InsertOnlyConcurrentMap<const DexClass*, SignatureMap>;

using UnifiedInterfacesSignatureMaps =
    InsertOnlyConcurrentMap<const DexTypeList*, SignatureMap>;

void update_signature_map(const DexMethod* method,
                          MethodSet value,
                          SignatureMap* map) {
  map->update(
      [&](const ProtoMap& protos) {
        auto copy = protos;
        copy.insert_or_assign(method->get_proto(), value);
        return copy;
      },
      method->get_name());
}

void unify_signature_maps(const SignatureMap& to_add, SignatureMap* target) {
  target->union_with(
      [&](const ProtoMap& p1, const ProtoMap& p2) {
        return p1.get_union_with(
            [&](const MethodSet& ms1, const MethodSet& ms2) {
              return ms1.get_union_with(ms2);
            },
            p2);
      },
      to_add);
}

class GraphBuilder {
 public:
  explicit GraphBuilder(const Scope& scope, const GraphConfig& config = {})
      : m_scope(scope), m_config(config) {}

  std::unique_ptr<Graph> run() {
    m_graph = std::make_unique<Graph>();
    walk::parallel::classes(m_scope, [&](const DexClass* cls) {
      if (is_interface(cls)) {
        analyze_interface(cls);
      } else {
        analyze_non_interface(cls);
      }
    });
    if (m_config.include_miranda) {
      synthesize_miranda_nodes();
      m_graph->set_has_miranda(true);
    }
    return std::move(m_graph);
  }

 private:
  const ClassSignatureMap& analyze_non_interface(const DexClass* cls) {
    always_assert(!is_interface(cls));
    const auto* res = m_class_signature_maps.get(cls);
    if (res != nullptr) {
      return *res;
    }

    // Initialize the signature maps from those of the superclass.
    ClassSignatureMap class_signatures;
    if (cls->get_super_class() != nullptr) {
      auto* super_cls = type_class(cls->get_super_class());
      if (super_cls != nullptr) {
        class_signatures = analyze_non_interface(super_cls);
      }
    }

    // Add all methods from the interfaces that the current class directly
    // implements to the set of unimplemented methods.
    unify_signature_maps(unify_super_interface_signatures(cls),
                         &class_signatures.unimplemented);

    auto inherited_implemented = class_signatures.implemented;
    for (auto* method : cls->get_vmethods()) {
      // Replace the overridden methods by the overriding ones.
      update_signature_map(method, MethodSet{method},
                           &class_signatures.implemented);
    }

    // Find all implementation methods reachable via their interface methods.
    // Note that an interface method can be implemented by a method inherited
    // from a superclass.
    std::vector<std::pair<MethodSet, const DexMethod*>>
        unimplemented_implementations;
    for (const auto& protos_pair : class_signatures.unimplemented) {
      const auto* name = protos_pair.first;
      const auto& named_implemented_protos =
          class_signatures.implemented.at(name);
      if (named_implemented_protos.empty()) {
        continue;
      }
      for (const auto& ms_pair : protos_pair.second) {
        const auto* proto = ms_pair.first;
        const auto& implemented_set = named_implemented_protos.at(proto);
        if (implemented_set.empty()) {
          continue;
        }
        const auto* implementation = only(implemented_set);
        unimplemented_implementations.emplace_back(ms_pair.second,
                                                   implementation);
      }
    }
    // Remove the newly implemented methods from the set of unimplemented
    // interface methods.
    for (auto&& [_, implementation] : unimplemented_implementations) {
      update_signature_map(implementation, MethodSet{},
                           &class_signatures.unimplemented);
    }

    auto [map_ptr, emplaced] =
        m_class_signature_maps.emplace(cls, class_signatures);
    if (emplaced) {
      // Mark all overriding methods as reachable via their parent method ref.
      for (auto* method : cls->get_vmethods()) {
        const auto& overridden_set =
            inherited_implemented.at(method->get_name())
                .at(method->get_proto());
        for (const auto* overridden : overridden_set) {
          m_graph->add_edge(overridden, /* overridden_is_interface */ false,
                            method, /* overriding_is_interface */ false);
        }
      }
      // Mark all implementation methods as reachable via their interface
      // methods.
      for (auto&& [unimplementeds, implementation] :
           unimplemented_implementations) {
        for (const auto* unimplemented : unimplementeds) {
          if (implementation->get_class() == cls->get_type() ||
              m_graph->add_other_implementation_class(unimplemented,
                                                      implementation, cls)) {
            m_graph->add_edge(unimplemented,
                              /* overridden_is_interface */ true,
                              implementation,
                              /* overriding_is_interface */ false);
          }
        }
      }
    }

    return *map_ptr;
  }

  const SignatureMap& analyze_interface(const DexClass* cls) {
    always_assert(is_interface(cls));
    const auto* res = m_interface_signature_maps.get(cls);
    if (res != nullptr) {
      return *res;
    }

    SignatureMap interface_signatures = unify_super_interface_signatures(cls);
    auto inherited_interface_signatures = interface_signatures;
    for (auto* method : cls->get_vmethods()) {
      update_signature_map(method, MethodSet{method}, &interface_signatures);
    }

    auto [map_ptr, emplaced] =
        m_interface_signature_maps.emplace(cls, interface_signatures);
    if (emplaced) {
      for (auto* method : cls->get_vmethods()) {
        const auto& overridden_set =
            inherited_interface_signatures.at(method->get_name())
                .at(method->get_proto());
        // These edges connect a method in a superinterface to the overriding
        // methods in a subinterface. A reference to the superinterface's method
        // will not resolve to the subinterface's method at runtime, but these
        // edges are critical because we do not add an edge between overridden
        // superinterface methods and their implementors. Concretely, given the
        // following code:
        //
        //   interface IA { void m(); }
        //   interface IB extends IA { void m(); }
        //   class C implements IB { void m(); }
        //
        // Our graph will contain an edge between IA::m and IB::m, and an edge
        // between IB::m and C::m. It will *not* contain an edge between IA::m
        // and C::m, even though C::m does implement IA::m as well. Therefore to
        // get all the implementors of IA::m, we need to traverse the edges
        // added here to find them. This design reduces the number of edges
        // necessary for building the graph.
        for (const auto* overridden : overridden_set) {
          m_graph->add_edge(overridden, /* overridden_is_interface */ true,
                            method, /* overriding_is_interface */ true);
        }
      }
    }

    return *map_ptr;
  }

  const SignatureMap& unify_super_interface_signatures(const DexClass* cls) {
    auto* type_list = cls->get_interfaces();
    const auto* res = m_unified_interfaces_signature_maps.get(type_list);
    if (res != nullptr) {
      return *res;
    }

    SignatureMap super_interface_signatures;
    for (auto* intf : *type_list) {
      auto* intf_cls = type_class(intf);
      if (intf_cls != nullptr) {
        unify_signature_maps(analyze_interface(intf_cls),
                             &super_interface_signatures);
      }
    }

    auto [map_ptr, _] = m_unified_interfaces_signature_maps.emplace(
        type_list, super_interface_signatures);
    return *map_ptr;
  }

  // For each non-interface class whose directly-declared interfaces have
  // methods absent from the class's own vmethods, synthesize a miranda
  // dispatch slot. This covers both abstract classes with unimplemented
  // obligations and concrete classes that inherit impls from super but
  // directly declare the interface. Adds an edge from each backing
  // interface method to the miranda node so consumers traversing
  // get_overriding_methods see the miranda layer.
  //
  // We do NOT rewire existing interface->concrete-impl edges. Consumers that
  // want miranda-aware grouping should use find_class_dispatch_root(), which
  // walks the class chain and picks up miranda nodes when present.
  void synthesize_miranda_nodes() {
    // Iterate ALL classes processed by analyze_non_interface -- this includes
    // EXTERNAL classes reached transitively via super_class chains from
    // m_scope (internal) classes. Restricting to m_scope alone misses
    // mirandas at external abstract intermediates (e.g., framework classes
    // like android.view.View) that internal classes inherit from. Such
    // mirandas are needed to:
    //   1. Group cross-internal-class methods that share an external
    //      abstract dispatch root (for VirtualMerging).
    //   2. Allow MethodProfiles to resolve profile lines that reference
    //      framework miranda slots.
    auto create_miranda_for = [&](const DexClass* cls,
                                  const DexMethod* iface_method) {
      auto* miranda = DexMethod::make_method_downcast(
          cls->get_type(), iface_method->get_name(), iface_method->get_proto());
      // make_method_downcast dynamic_casts the DexMethodRef to DexMethod*; it
      // yields null if a same-signature ref exists that is not a DexMethod.
      // Skip rather than insert a null-keyed node / mark null as miranda.
      if (miranda == nullptr) {
        return;
      }
      // A miranda is a synthetic dispatch slot with no real definition. If a
      // real def already exists for (cls, name, proto) -- e.g. a direct /
      // static / private / synthetic method whose signature collides with an
      // unimplemented interface method -- do not mark it miranda or add an
      // interface edge; that would make a real method a dispatch root.
      if (miranda->is_def()) {
        return;
      }
      m_graph->add_edge(iface_method, /* overridden_is_interface */ true,
                        miranda, /* overriding_is_interface */ false);
      m_graph->mark_miranda(miranda);
    };

    // For each non-interface class, walk its directly-implemented interfaces
    // (transitively through super-interfaces only -- NOT super class's
    // interfaces). For each interface method, if cls's vmethods don't have a
    // matching one, create a miranda at cls. Even concrete classes that
    // inherit impls from super get a miranda ref at their own type for
    // downstream lookups (e.g., MethodProfiles resolution).
    auto process_cls = [&](const DexClass* cls) {
      if (is_interface(cls)) {
        return;
      }
      // Collect direct interfaces transitively (through super-interfaces).
      std::set<const DexType*, dextypes_comparator> intfs;
      const auto collect = [&](auto self, const DexType* intf_type) -> void {
        if (intf_type == nullptr || !intfs.insert(intf_type).second) {
          return;
        }
        const DexClass* intf_cls = type_class(intf_type);
        if (intf_cls == nullptr) {
          return;
        }
        for (const auto* super_intf : *intf_cls->get_interfaces()) {
          self(self, super_intf);
        }
      };
      for (const auto* intf : *cls->get_interfaces()) {
        self_recursive_fn(collect, intf);
      }
      // For each interface method, check if cls's vmethods has it.
      for (const auto* intf_type : intfs) {
        const DexClass* intf_cls = type_class(intf_type);
        if (intf_cls == nullptr) {
          continue;
        }
        for (const auto* intf_meth : intf_cls->get_vmethods()) {
          const auto* name = intf_meth->get_name();
          auto* proto = intf_meth->get_proto();
          bool has = false;
          for (const auto* m : cls->get_vmethods()) {
            if (m->get_name() == name && m->get_proto() == proto) {
              has = true;
              break;
            }
          }
          if (has) {
            continue;
          }
          // The same (name, proto) may be declared by more than one interface
          // in `intfs` (e.g. a class implementing both List and Collection,
          // both declaring size(); or an interface and a super-interface that
          // re-declares a method). We intentionally call create_miranda_for
          // once per declaring interface method: make_method_downcast returns
          // the SAME miranda ref each time (idempotent) and mark_miranda is
          // idempotent, but each call adds a DISTINCT interface->miranda parent
          // edge -- the one miranda slot legitimately implements the method for
          // every such interface. So this is not duplicate work to dedup; a
          // per-(name, proto) seen-set would be a bug, dropping the extra
          // interface parents that consumers (get_implemented_interfaces) read.
          create_miranda_for(cls, intf_meth);
        }
      }
    };

    // Process all non-interface classes known to g_redex (internal +
    // external). External coverage matters because (a) IR may reference
    // mirandas at framework classes (e.g., android.view.View) that no
    // internal class extends, and (b) MethodProfiles' resolution depends
    // on these refs being lookup-able.
    //
    // When m_config.miranda_within_scope is set, restrict synthesis to the
    // build_type_hierarchy(scope) node set (scope U external): skip other
    // stores' internal classes so make_method_downcast does not materialize
    // refs outside `scope`'s own hierarchy.
    UnorderedSet<const DexType*> in_scope;
    if (m_config.miranda_within_scope) {
      in_scope.reserve(m_scope.size());
      for (const auto* cls : m_scope) {
        in_scope.insert(cls->get_type());
      }
    }
    // walk_type_class iterates g_redex's InsertOnlyConcurrentSet of classes, so
    // each class is visited exactly once -- no dedup set needed.
    g_redex->walk_type_class([&](const DexType* /*type*/, const DexClass* cls) {
      if (m_config.miranda_within_scope && !cls->is_external() &&
          in_scope.count(cls->get_type()) == 0) {
        return;
      }
      process_cls(cls);
    });
  }

  std::unique_ptr<Graph> m_graph;
  ClassSignatureMaps m_class_signature_maps;
  InterfaceSignatureMaps m_interface_signature_maps;
  UnifiedInterfacesSignatureMaps m_unified_interfaces_signature_maps;
  const Scope& m_scope;
  GraphConfig m_config;
};

template <typename F>
bool all_overriding_methods_impl(const Graph& graph,
                                 const DexMethod* method,
                                 const F& f,
                                 bool include_interfaces,
                                 const DexType* base_type) {
  const Node& root = graph.get_node(method);
  if (base_type && method->get_class() == base_type) {
    base_type = nullptr;
  }
  if (root.is_interface) {
    UnorderedSet<const Node*> visited{&root};
    visited.reserve(root.children.size() * 7);
    return self_recursive_fn(
        [&](auto self, const auto& children) -> bool {
          for (const auto* node : UnorderedIterable(children)) {
            if (!visited.emplace(node).second) {
              continue;
            }
            if (!self(self, node->children)) {
              return false;
            }
            if ((include_interfaces || !node->is_interface) &&
                (!base_type || node->overrides(node->method, base_type)) &&
                !f(node->method)) {
              return false;
            }
          }
          return true;
        },
        root.children);
  }
  // optimized code path
  return self_recursive_fn(
      [&](auto self, const auto& children) -> bool {
        for (const auto* node : UnorderedIterable(children)) {
          if (!self(self, node->children)) {
            return false;
          }
          if ((!base_type || node->overrides(node->method, base_type)) &&
              !f(node->method)) {
            return false;
          }
        }
        return true;
      },
      root.children);
}

template <typename F>
bool all_overridden_methods_impl(const Graph& graph,
                                 const DexMethod* method,
                                 const F& f,
                                 bool include_interfaces) {
  const Node& root = graph.get_node(method);
  if (include_interfaces) {
    UnorderedSet<const Node*> visited{&root};
    visited.reserve(root.parents.size() * 7);
    return self_recursive_fn(
        [&](auto self, const auto& children) -> bool {
          for (const auto* node : UnorderedIterable(children)) {
            if (!visited.emplace(node).second) {
              continue;
            }
            if (!include_interfaces && node->is_interface) {
              continue;
            }
            if (!self(self, node->parents)) {
              return false;
            }
            if (!f(node->method)) {
              return false;
            }
          }
          return true;
        },
        root.parents);
  }
  if (root.is_interface) {
    return true;
  }
  // optimized code path
  return self_recursive_fn(
      [&](auto self, const auto& children) -> bool {
        for (const auto* node : UnorderedIterable(children)) {
          if (node->is_interface) {
            continue;
          }
          if (!self(self, node->parents)) {
            return false;
          }
          if (!f(node->method)) {
            return false;
          }
        }
        return true;
      },
      root.parents);
}

} // namespace

namespace method_override_graph {

bool Node::overrides(const DexMethod* current, const DexType* base_type) const {
  // Trivial case.
  if (type::check_cast(current->get_class(), base_type)) {
    return true;
  }
  // We also check if the current method was fulfilling an implementation
  // demand for any class that can be cast to the given base_type.
  if (!other_interface_implementations) {
    return false;
  }
  for (const auto* cls :
       UnorderedIterable(other_interface_implementations->classes)) {
    if (type::check_cast(cls->get_type(), base_type)) {
      return true;
    }
  }
  return false;
}

const Node& Graph::get_node(const DexMethod* method) const {
  auto it = m_nodes.find(method);
  if (it == m_nodes.end()) {
    return get_empty_node();
  }
  return it->second;
}

void Graph::mark_miranda(const DexMethod* method) {
  m_nodes.update(method, [&](const DexMethod*, Node& node, bool /*exists*/) {
    node.method = method;
    node.is_miranda = true;
  });
}

void Graph::add_edge(const DexMethod* overridden, const DexMethod* overriding) {
  // The type-class lookup should only ever fail during testing if the
  // environment isn't fully built up.
  auto may_be_interface = [](DexType* t) {
    auto* cls = type_class(t);
    return (cls == nullptr) || is_interface(cls);
  };
  add_edge(overridden, may_be_interface(overridden->get_class()), overriding,
           may_be_interface(overridden->get_class()));
}

void Graph::add_edge(const DexMethod* overridden,
                     bool overridden_is_interface,
                     const DexMethod* overriding,
                     bool overriding_is_interface) {
  Node* overriding_node = nullptr;
  m_nodes.update(overriding, [&](const DexMethod*, Node& node, bool exists) {
    if (!exists) {
      node.method = overriding;
      node.is_interface = overriding_is_interface;
    }
    overriding_node = &node;
  });

  Node* overridden_node = nullptr;
  m_nodes.update(overridden, [&](const DexMethod*, Node& node, bool exists) {
    if (exists) {
      always_assert(node.is_interface == overridden_is_interface);
    } else {
      node.method = overridden;
      node.is_interface = overridden_is_interface;
    }
    node.children.insert(overriding_node);
    overridden_node = &node;
  });

  m_nodes.update(overriding, [&](const DexMethod*, Node& node, bool exists) {
    redex_assert(exists);
    node.parents.insert(overridden_node);
  });
}

void Node::gather_connected_methods(
    UnorderedSet<const DexMethod*>* visited) const {
  if (method == nullptr) {
    return;
  }
  visited->insert(method);
  for (auto* child : UnorderedIterable(children)) {
    if (visited->count(child->method) != 0u) {
      continue;
    }
    child->gather_connected_methods(visited);
  }
  for (auto* parent : UnorderedIterable(parents)) {
    if (visited->count(parent->method) != 0u) {
      continue;
    }
    parent->gather_connected_methods(visited);
  }
}

bool Graph::add_other_implementation_class(const DexMethod* overridden,
                                           const DexMethod* overriding,
                                           const DexClass* cls) {
  bool parent_inserted = false;
  m_nodes.update(overriding, [&](const DexMethod*, Node& node, bool exists) {
    if (!exists) {
      node.method = overriding;
    }
    auto& oii = node.other_interface_implementations;
    if (!oii) {
      oii = std::make_unique<OtherInterfaceImplementations>();
    }
    oii->classes.insert(cls);
    parent_inserted = oii->parents.insert(overridden).second;
  });
  return parent_inserted;
}

void Graph::dump(std::ostream& os) const {
  namespace bs = binary_serialization;
  bs::write_header(os, /* version */ 1);
  bs::GraphWriter<const DexMethod*> gw(
      [&](std::ostream& os, const DexMethod* method) {
        const auto& s = show_deobfuscated(method);
        bs::write<uint32_t>(os, static_cast<uint32_t>(s.size()));
        os << s;
      },
      [&](const DexMethod* method) -> std::vector<const DexMethod*> {
        const auto& node = get_node(method);
        std::vector<const DexMethod*> succs;
        succs.reserve(node.children.size());
        unordered_transform(node.children,
                            std::back_inserter(succs),
                            [](auto* c) { return c->method; });
        return succs;
      });
  gw.write(os, unordered_keys(m_nodes));
}

std::unique_ptr<const Graph> build_graph(const Scope& scope) {
  Timer t("Building method override graph");
  return GraphBuilder(scope).run();
}

std::unique_ptr<const Graph> build_graph(const Scope& scope,
                                         const GraphConfig& config) {
  Timer t("Building method override graph");
  return GraphBuilder(scope, config).run();
}

UnorderedBag<const DexMethod*> get_overriding_methods(
    const Graph& graph,
    const DexMethod* method,
    bool include_interfaces,
    const DexType* base_type) {
  UnorderedBag<const DexMethod*> res;
  all_overriding_methods_impl(
      graph, method,
      [&](const DexMethod* method) {
        res.insert(method);
        return true;
      },
      include_interfaces, base_type);
  return res;
}

UnorderedBag<const DexMethod*> get_overridden_methods(const Graph& graph,
                                                      const DexMethod* method,
                                                      bool include_interfaces) {
  UnorderedBag<const DexMethod*> res;
  all_overridden_methods_impl(
      graph, method,
      [&](const DexMethod* method) {
        res.insert(method);
        return true;
      },
      include_interfaces);
  return res;
}

bool is_true_virtual(const Graph& graph, const DexMethod* method) {
  if (is_abstract(method)) {
    return true;
  }
  const auto& node = graph.get_node(method);
  return !node.parents.empty() || !node.children.empty();
}

InsertOnlyConcurrentSet<DexMethod*> get_non_true_virtuals(const Graph& graph,
                                                          const Scope& scope) {
  InsertOnlyConcurrentSet<DexMethod*> non_true_virtuals;
  workqueue_run<DexClass*>(
      [&](DexClass* cls) {
        for (auto* method : cls->get_vmethods()) {
          if (!is_true_virtual(graph, method)) {
            non_true_virtuals.insert(method);
          }
        }
      },
      scope);
  return non_true_virtuals;
}

bool all_overriding_methods(const Graph& graph,
                            const DexMethod* method,
                            const std::function<bool(const DexMethod*)>& f,
                            bool include_interfaces,
                            const DexType* base_type) {
  return all_overriding_methods_impl(graph, method, f, include_interfaces,
                                     base_type);
}

bool any_overriding_methods(const Graph& graph,
                            const DexMethod* method,
                            const std::function<bool(const DexMethod*)>& f,
                            bool include_interfaces,
                            const DexType* base_type) {
  return !all_overriding_methods_impl(
      graph, method, [&](const DexMethod* m) { return !f(m); },
      include_interfaces, base_type);
}

bool all_overridden_methods(const Graph& graph,
                            const DexMethod* method,
                            const std::function<bool(const DexMethod*)>& f,
                            bool include_interfaces) {
  return all_overridden_methods_impl(graph, method, f, include_interfaces);
}

bool any_overridden_methods(const Graph& graph,
                            const DexMethod* method,
                            const std::function<bool(const DexMethod*)>& f,
                            bool include_interfaces) {
  return !all_overridden_methods_impl(
      graph, method, [&](const DexMethod* m) { return !f(m); },
      include_interfaces);
}

UnorderedSet<DexClass*> get_classes_with_overridden_finalize(
    const Graph& method_override_graph, const ClassHierarchy& class_hierarchy) {
  UnorderedSet<DexClass*> res;
  auto overriding_methods = method_override_graph::get_overriding_methods(
      method_override_graph, method::java_lang_Object_finalize());
  for (const auto* overriding_method : UnorderedIterable(overriding_methods)) {
    auto* type = overriding_method->get_class();
    auto* cls = type_class(type);
    if ((cls != nullptr) && !cls->is_external()) {
      res.insert(cls);
      auto children = get_all_children(class_hierarchy, type);
      for (const auto* child : children) {
        auto* child_cls = type_class(child);
        if ((child_cls != nullptr) && !child_cls->is_external()) {
          res.insert(child_cls);
        }
      }
    }
  }
  return res;
}

const DexMethod* find_class_dispatch_root(const Graph& graph,
                                          const DexMethod* method) {
  const auto* name = method->get_name();
  auto* proto = method->get_proto();
  const DexMethod* root = method;
  const auto* cls = type_class(method->get_class());
  if (cls == nullptr) {
    return root;
  }
  const bool has_miranda = graph.has_miranda();
  auto* type = cls->get_super_class();
  while (type != nullptr) {
    cls = type_class(type);
    if (cls == nullptr) {
      break;
    }
    if (!is_interface(cls)) {
      // Prefer a real vmethod at this class.
      bool found = false;
      for (const auto* m : cls->get_vmethods()) {
        if (m->get_name() == name && m->get_proto() == proto) {
          root = m;
          found = true;
          break;
        }
      }
      // Otherwise, look for a miranda slot at this class. Only consult the
      // graph if it's miranda-aware -- otherwise miranda nodes don't exist.
      // Note: a synthesized miranda is stored as a DexMethodRef cast to
      // DexMethod* (not a real def), so we don't filter on is_def() here.
      if (!found && has_miranda) {
        auto* maybe_ref = DexMethod::get_method(type, name, proto);
        if (maybe_ref != nullptr) {
          const auto* maybe_miranda = dynamic_cast<const DexMethod*>(maybe_ref);
          if (maybe_miranda != nullptr) {
            const auto& node = graph.get_node(maybe_miranda);
            if (node.is_miranda) {
              root = maybe_miranda;
            }
          }
        }
      }
    }
    type = cls->get_super_class();
  }
  return root;
}

} // namespace method_override_graph
