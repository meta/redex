/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <queue>

#include "ConcurrentContainers.h"
#include "DeterministicContainers.h"
#include "DexClass.h"
class IRInstruction;

namespace method_override_graph {
class Graph;
} // namespace method_override_graph

/*
 * Call graph representation that implements the standard graph interface
 * API for use with fixpoint iteration algorithms.
 */

namespace call_graph {

class Graph;

/*
 * Currently, we only add edges in the graph when we know the exact callee
 * an invoke instruction refers to.  That means only invoke-static and
 * invoke-direct calls, as well as invoke-virtual calls that refer
 * unambiguously to a single method. This keeps the graph smallish and
 * easier to analyze.
 *
 * TODO: Once we have points-to information, we should expand the callgraph
 * to include invoke-virtuals that refer to sets of methods.
 */
Graph single_callee_graph(
    const method_override_graph::Graph& method_override_graph, const Scope&);

Graph multiple_callee_graph(
    const method_override_graph::Graph& method_override_graph,
    const Scope&,
    uint32_t big_override_threshold);

Graph complete_call_graph(
    const method_override_graph::Graph& method_override_graph, const Scope&);

struct CallSite {
  const DexMethod* callee;
  IRInstruction* invoke_insn;

  [[noreturn]] CallSite() { not_reached(); }
  CallSite(const DexMethod* callee, IRInstruction* invoke_insn)
      : callee(callee), invoke_insn(invoke_insn) {}
};

using CallSites = std::vector<CallSite>;
using MethodSet = UnorderedSet<const DexMethod*>;
using MethodBag = UnorderedBag<const DexMethod*>;

struct RootAndDynamic {
  MethodSet roots;
  MethodSet dynamic_methods;
};

/*
 * This class determines how the call graph is built. The Graph ctor will start
 * from the roots and invoke get_callsites() on each returned method
 * recursively until the graph is fully mapped out. One can think of the
 * BuildStrategy as implicitly encoding the graph structure, with the Graph
 * constructor reifying it.
 */
class BuildStrategy {
 public:
  virtual ~BuildStrategy() {}

  virtual RootAndDynamic get_roots() const = 0;

  virtual CallSites get_callsites(const DexMethod*) const = 0;
};

class Node;
using NodeId = const Node*;

class Edge {
 public:
  Edge(NodeId caller, NodeId callee, IRInstruction* invoke_insn);
  IRInstruction* invoke_insn() const { return m_invoke_insn; }
  NodeId caller() const { return m_caller; }
  NodeId callee() const { return m_callee; }

 private:
  NodeId m_caller;
  NodeId m_callee;
  IRInstruction* m_invoke_insn;
};

using EdgeId = const Edge*;

// This exposes a `EdgesVector` as an iterable of `const Edge*`.
class EdgesAdapter {
 public:
  explicit EdgesAdapter(const std::vector<Edge>* edges) : m_edges(edges) {}

  class iterator {
   public:
    using value_type = const Edge*;
    using difference_type = std::ptrdiff_t;
    using pointer = const value_type*;
    using reference = const value_type&;
    using iterator_category = std::input_iterator_tag;

    explicit iterator(value_type current) : m_current(current) {}

    reference operator*() const { return m_current; }

    pointer operator->() const { return &(this->operator*()); }

    bool operator==(const iterator& other) const {
      return m_current == other.m_current;
    }

    bool operator!=(iterator& other) const { return !(*this == other); }

    iterator operator++(int) {
      auto result = *this;
      ++(*this);
      return result;
    }

    iterator& operator++();

   private:
    value_type m_current;
  };

  iterator begin() const { return iterator(&*m_edges->begin()); }

  iterator end() const { return iterator(&*m_edges->end()); }

  size_t size() const { return m_edges->size(); }

 private:
  const std::vector<Edge>* m_edges;
};

class Node final {
  enum NodeType {
    GHOST_ENTRY,
    GHOST_EXIT,
    REAL_METHOD,
  };

 public:
  explicit Node(const DexMethod* m) : m_method(m), m_type(REAL_METHOD) {}
  explicit Node(NodeType type) : m_method(nullptr), m_type(type) {}

  const DexMethod* method() const { return m_method; }
  const std::vector<const Edge*>& callers() const { return m_predecessors; }
  EdgesAdapter callees() const { return EdgesAdapter(&m_successors); }

  bool is_entry() const { return m_type == GHOST_ENTRY; }
  bool is_exit() const { return m_type == GHOST_EXIT; }

  bool operator==(const Node& other) const {
    return m_method == other.m_method && m_type == other.m_type;
  }

 private:
  const DexMethod* m_method;
  std::vector<const Edge*> m_predecessors;
  std::vector<Edge> m_successors;
  NodeType m_type;

  friend class Graph;
};

inline EdgesAdapter::iterator& EdgesAdapter::iterator::operator++() {
  ++m_current;
  return *this;
}

class Graph final {
 public:
  explicit Graph(const BuildStrategy&);

  Graph(Graph&&) = default;
  Graph& operator=(Graph&&) = default;

  // The call graph cannot be copied.
  Graph(const Graph&) = delete;
  Graph& operator=(const Graph&) = delete;

  NodeId entry() const { return m_entry.get(); }
  NodeId exit() const { return m_exit.get(); }

  bool has_node(const DexMethod* m) const {
    return m_nodes.count_unsafe(m) != 0;
  }

  NodeId node(const DexMethod* m) const {
    if (m == nullptr) {
      return this->entry();
    }
    return m_nodes.get_unsafe(m);
  }

  const InsertOnlyConcurrentMap<const IRInstruction*,
                                UnorderedSet<const DexMethod*>>&
  get_insn_to_callee() const {
    return m_insn_to_callee;
  }

  const UnorderedSet<const DexMethod*>& get_dynamic_methods() const {
    return m_dynamic_methods;
  }

  const MethodBag& get_callers(const DexMethod* callee) const;

  // This is an implementation of Breadth-First Search for call-graphs.
  template <typename MethodStartFn>
  void visit_by_levels(const MethodStartFn& method_start_fn) const {
    UnorderedSet<NodeId> visited;
    std::queue<NodeId> queue;
    queue.push(entry());
    visited.insert(entry());

    while (!queue.empty()) {
      const auto* cur = queue.front();
      queue.pop();

      method_start_fn(cur);

      auto callees = cur->callees();
      for (const auto& edge : callees) {
        const auto* callee = edge->callee();
        if (visited.count(callee)) {
          continue;
        }
        visited.insert(callee);
        queue.push(callee);
      }
    }
  }

 private:
  std::unique_ptr<Node> m_entry;
  std::unique_ptr<Node> m_exit;
  InsertOnlyConcurrentMap<const DexMethod*, Node> m_nodes;
  InsertOnlyConcurrentMap<const IRInstruction*, UnorderedSet<const DexMethod*>>
      m_insn_to_callee;
  mutable InsertOnlyConcurrentMap<const DexMethod*, MethodBag>
      m_callee_to_callers;

  // Methods that might have unknown inputs/outputs that we need special handle.
  // Like external methods with internal overrides, they might have external
  // implementation that we don't know about. Or methods that might have
  // dynamically added implementations, created via Proxy.newProxyInstance.
  // Or methods with native implementation.
  // We are only collecting those for multiple callee callgraph because we
  // need to avoid propagating method return values for those true virtual
  // methods.
  UnorderedSet<const DexMethod*> m_dynamic_methods;
};

class SingleCalleeStrategy : public BuildStrategy {
 public:
  explicit SingleCalleeStrategy(const method_override_graph::Graph&,
                                const Scope& scope);
  CallSites get_callsites(const DexMethod* method) const override;
  RootAndDynamic get_roots() const override;

 protected:
  bool is_definitely_virtual(DexMethod* method) const;

  const Scope& m_scope;
  InsertOnlyConcurrentSet<DexMethod*> m_non_virtual;
};

class MultipleCalleeBaseStrategy : public SingleCalleeStrategy {
 public:
  explicit MultipleCalleeBaseStrategy(const method_override_graph::Graph&,
                                      const Scope& scope);

  CallSites get_callsites(const DexMethod* method) const override = 0;
  RootAndDynamic get_roots() const override;

 protected:
  const std::vector<const DexMethod*>&
  get_ordered_overriding_methods_with_code_or_native(
      const DexMethod* method) const;

  const std::vector<const DexMethod*>&
  init_ordered_overriding_methods_with_code_or_native(
      const DexMethod* method, UnorderedBag<const DexMethod*>) const;

  const method_override_graph::Graph& m_method_override_graph;

 private:
  mutable InsertOnlyConcurrentMap<const DexMethod*,
                                  std::vector<const DexMethod*>>
      m_overriding_methods_cache;
};

class CompleteCallGraphStrategy : public MultipleCalleeBaseStrategy {
 public:
  explicit CompleteCallGraphStrategy(const method_override_graph::Graph&,
                                     const Scope& scope);
  CallSites get_callsites(const DexMethod* method) const override;
  RootAndDynamic get_roots() const override;

  // A callee of one resolved invoke of a method: the resolved method itself,
  // or, when `overriding` is set, each of its overriding methods with code or
  // native.
  struct InvokeTarget {
    IRInstruction* invoke_insn;
    const DexMethod* callee;
    bool overriding;
  };
  // The targets of the invokes of `method` whose callee resolves, in
  // instruction order. get_callsites() is these with each `overriding` target
  // replaced by its overriding methods with code or native.
  std::vector<InvokeTarget> get_invoke_targets(const DexMethod* method) const;

  using MultipleCalleeBaseStrategy::
      get_ordered_overriding_methods_with_code_or_native;
};

/*
 * The callers complete_call_graph() records for each method, without building
 * that graph. The graph gives an invoke-virtual or invoke-interface one edge
 * per overriding method with code and records each invoke's callees, so N call
 * sites of an interface method with M implementations cost N * M edges and N
 * sets of M callees. This keeps, for each method reachable from the graph's
 * roots, only its resolved callees, and assembles one method's callers when
 * asked: its direct callers plus the callers of each virtually invoked method
 * it overrides.
 */
class CompleteCallers final {
 public:
  CompleteCallers(const method_override_graph::Graph&, const Scope&);

  // The same set as complete_call_graph(...).get_callers(callee).
  MethodSet get_callers(const DexMethod* callee) const;

 private:
  // Resolved callee -> the reachable methods with an invoke resolved to it.
  ConcurrentMap<const DexMethod*, std::vector<const DexMethod*>>
      m_direct_callers;
  // Callee of a virtual or interface invoke -> the reachable methods with such
  // an invoke. Each of its overriding methods with code or native has them as
  // callers too.
  ConcurrentMap<const DexMethod*, std::vector<const DexMethod*>>
      m_virtual_callers;
  // Overriding method -> the keys of m_virtual_callers it overrides.
  ConcurrentMap<const DexMethod*, std::vector<const DexMethod*>> m_overridden;
};

class MultipleCalleeStrategy : public MultipleCalleeBaseStrategy {
 public:
  explicit MultipleCalleeStrategy(const method_override_graph::Graph&,
                                  const Scope& scope,
                                  uint32_t big_override_threshold);
  CallSites get_callsites(const DexMethod* method) const override;
  RootAndDynamic get_roots() const override;

 protected:
  ConcurrentSet<const DexMethod*> m_big_virtuals;
  ConcurrentSet<const DexMethod*> m_big_virtual_overrides;
};

// A static-method-only API for use with the monotonic fixpoint iterator.
class GraphInterface {
 public:
  using Graph = call_graph::Graph;
  using NodeId = const Node*;
  using EdgeId = const Edge*;

  static NodeId entry(const Graph& graph) { return graph.entry(); }
  static NodeId exit(const Graph& graph) { return graph.exit(); }
  static const std::vector<const Edge*>& predecessors(const Graph&,
                                                      const NodeId& m) {
    return m->callers();
  }
  static EdgesAdapter successors(const Graph&, const NodeId& m) {
    return m->callees();
  }
  static NodeId source(const Graph&, const EdgeId& e) { return e->caller(); }
  static NodeId target(const Graph&, const EdgeId& e) { return e->callee(); }
};

const MethodSet& resolve_callees_in_graph(const Graph& graph,
                                          const IRInstruction* insn);

const MethodBag& get_callee_to_callers(const Graph& graph,
                                       const DexMethod* callee);

bool invoke_is_dynamic(const Graph& graph, const IRInstruction* insn);

struct CallgraphStats {
  uint32_t num_nodes;
  uint32_t num_edges;
  uint32_t num_callsites;
  CallgraphStats(uint32_t num_nodes, uint32_t num_edges, uint32_t num_callsites)
      : num_nodes(num_nodes),
        num_edges(num_edges),
        num_callsites(num_callsites) {}
};

CallgraphStats get_num_nodes_edges(const Graph& graph);

} // namespace call_graph
