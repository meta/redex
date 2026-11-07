/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <cstddef>
#include <deque>
#include <functional>
#include <future>
#include <iterator>
#include <limits>
#include <ostream>
#include <stack>
#include <unordered_map>
#include <utility>
#include <vector>

#include <sparta/Exceptions.h>

namespace sparta {

// Forward declarations
template <typename NodeId>
class WtoComponent;

template <typename NodeId, typename NodeHash>
class WeakTopologicalOrdering;

namespace wto_impl {

// Forward declaration
template <typename NodeId, typename NodeHash, typename SuccFn>
class WtoBuilder;

/*
 * Iterator over the subcomponents of a strongly connected component (head
 * node excluded). This is a regular C++ iterator meant for traversing a
 * strongly connected component. It's not a fixpoint iterator.
 */
template <typename NodeId>
class WtoComponentIterator final {
 public:
  using iterator_category = std::forward_iterator_tag;
  using difference_type = std::ptrdiff_t;
  using value_type = WtoComponent<NodeId>;
  using pointer = value_type*;
  using reference = value_type&;

  WtoComponentIterator& operator++() {
    SPARTA_RUNTIME_CHECK(m_component != m_end, undefined_operation());
    // All components of a WTO are stored linearly inside a vector in reverse
    // order. The subcomponents of an SCC are stored between the head node and
    // the next component in the WTO.
    m_component -= m_component->m_next_component_offset;
    return *this;
  }

  WtoComponentIterator operator++(int) {
    WtoComponentIterator retval = *this;
    ++(*this);
    return retval;
  }

  bool operator==(const WtoComponentIterator& other) const {
    return m_component == other.m_component;
  }

  bool operator!=(const WtoComponentIterator& other) const {
    return !(*this == other);
  }

  const WtoComponent<NodeId>& operator*() {
    SPARTA_RUNTIME_CHECK(m_component != m_end, undefined_operation());
    return *m_component;
  }

  const WtoComponent<NodeId>* operator->() {
    SPARTA_RUNTIME_CHECK(m_component != m_end, undefined_operation());
    return m_component;
  }

 private:
  WtoComponentIterator(const WtoComponent<NodeId>* component,
                       const WtoComponent<NodeId>* end)
      : m_component(component), m_end(end) {}

  const WtoComponent<NodeId>* m_component;
  const WtoComponent<NodeId>* m_end;

  template <typename T>
  friend class sparta::WtoComponent;
  template <typename T1, typename T2>
  friend class sparta::WeakTopologicalOrdering;
};

} // namespace wto_impl

/*
 * A component of a weak topological ordering is either a vertex or a strongly
 * connected set of nodes with a distinguished node (the head).
 */
template <typename NodeId>
class WtoComponent final {
 public:
  using iterator = wto_impl::WtoComponentIterator<NodeId>;

  enum class Kind { Vertex, Scc };

  WtoComponent(const NodeId& node,
               Kind kind,
               int32_t position,
               int32_t next_component_position)
      : m_node(node), m_kind(kind) {
    SPARTA_RUNTIME_CHECK(position > next_component_position, internal_error());
    // When a component is constructed, its position inside the vector is
    // specified by its absolute index. Since we want to navigate the WTO by
    // recursively exploring SCCs, it's more efficient to maintain relative
    // offsets between adjacent components. An absolute position of -1 means
    // the end of an SCC or the end of the WTO.
    m_next_component_offset = position - next_component_position;
  }

  // Correct iteration depends on these objects being in one contiguous piece of
  // memory. Make sure users don't accidentally copy these objects
  WtoComponent(WtoComponent&& that) = default;
  WtoComponent(const WtoComponent& that) = delete;

  /*
   * If the component is not strongly connected, this method returns the single
   * node contained inside a Vertex component.
   */
  const NodeId& head_node() const { return m_node; }

  bool is_vertex() const { return m_kind == Kind::Vertex; }

  bool is_scc() const { return m_kind == Kind::Scc; }

  iterator begin() const {
    SPARTA_RUNTIME_CHECK(is_scc(), undefined_operation());
    // All the components of a WTO are stored linearly inside a vector. A vector
    // guarantees that all its elements are stored adjacently in a contiguous
    // block of memory, which allows us to safely perform pointer arithmetic
    // based on the 'this' pointer (the vector is never resized after the WTO
    // has been constructed).
    return iterator(this - 1, this - m_next_component_offset);
  }

  iterator end() const {
    SPARTA_RUNTIME_CHECK(is_scc(), undefined_operation());
    auto end_ptr = this - m_next_component_offset;
    return iterator(end_ptr, end_ptr);
  }

 private:
  NodeId m_node;
  Kind m_kind;
  // The offset to the next component (NOT subcomponent) in the m_wto_space
  // vector. If we are at the end of the WTO, this will point to one element
  // before the start of the vector. If we are a subcomponent at the end of
  // the parent component, this points to one element past the end of the
  // parent component.
  size_t m_next_component_offset;

  template <typename T>
  friend class wto_impl::WtoComponentIterator;
};

/*
 * Implementation of the decomposition of a rooted directed graph into a weak
 * topological ordering (WTO), as described in Bourdoncle's original paper:
 *
 *   F. Bourdoncle. Efficient chaotic iteration strategies with widenings.
 *   In Formal Methods in Programming and Their Applications, pp 128-141.
 *
 * State-of-the-art fixpoint iteration algorithms use weak topological orderings
 * as the underlying structure for high performance. Although WTOs are primarily
 * used with control-flow graphs of functions or methods, they can come handy
 * when manipulating structures like call graphs or dependency graphs.
 *
 * - NodeId is the identifier of a node in the graph. Nodes should be comparable
 *   using `operator==()`.
 * - NodeHash is a functional structure providing a hash function on nodes.
 *
 * Please note that node identifiers are copied around at various steps of the
 * algorithm, in particular wherever the `m_successors` function is invoked. For
 * performance reasons, it's a good idea to keep the structure of `NodeId` as
 * simple as possible, such as a pointer or a structure of primitive types.
 */
template <typename NodeId, typename NodeHash = std::hash<NodeId>>
class WeakTopologicalOrdering final {
 public:
  using iterator = wto_impl::WtoComponentIterator<NodeId>;

  /*
   * In order to construct a WTO, we just need to specify the root of the graph
   * and the successor function.
   */
  template <typename SuccFn>
  WeakTopologicalOrdering(const NodeId& root, SuccFn successors) {
    if (successors(root).empty()) {
      // If the CFG consists of a single node with no control-flow edges, we
      // don't need to run the general algorithm. This avoids building all the
      // auxiliary data structures required by Bourdoncle's algorithm.
      // This optimization benefits the simple parallel fixpoint iterator, which
      // computes a WTO for each toplevel component of the CFG, most of them
      // single nodes in practice.
      m_components.emplace_back(root, WtoComponent<NodeId>::Kind::Vertex,
                                /* position */ 0,
                                /* next_component_position */ -1);
      return;
    }
    wto_impl::WtoBuilder<NodeId, NodeHash, SuccFn> builder(successors,
                                                           &m_components);
    builder.build(root);
  }

  iterator begin() const {
    return iterator(&m_components.back(), &m_components.front() - 1);
  }

  iterator end() const {
    auto end_ptr = &m_components.front() - 1;
    return iterator(end_ptr, end_ptr);
  }

  // Recursively iterate through the wto order and invoke a callback for each
  // node.
  template <typename Visitor = std::function<void(const NodeId&)>>
  void visit_depth_first(const Visitor& f) {
    auto visit_component = [&f](const auto& self,
                                const WtoComponent<NodeId>& v) -> void {
      f(v.head_node());
      if (v.is_scc()) {
        for (const auto& inner : v) {
          self(self, inner);
        }
      }
    };
    for (const auto& v : *this) {
      visit_component(visit_component, v);
    }
  }

 private:
  // We store all the components of a WTO inside a vector. This is more
  // efficient than allocating each component individually on the heap.
  // It's also more cache-friendly when repeatedly traversing the WTO during
  // a fixpoint iteration.
  std::vector<WtoComponent<NodeId>> m_components;
};

namespace wto_impl {

/*
 * Bourdoncle's algorithm is two mutually recursive procedures, visit and
 * component, whose recursion gets as deep as the longest path the depth-first
 * search follows. The builder keeps the calls in progress on an explicit stack
 * of frames instead, so that a long chain of nodes cannot overflow the native
 * stack, and resumes them in the same order as the recursive procedures.
 */
template <typename NodeId, typename NodeHash, typename SuccFn>
class WtoBuilder final {
 public:
  WtoBuilder(SuccFn successors, std::vector<WtoComponent<NodeId>>* wto_space)
      : m_successors(successors),
        m_wto_space(wto_space),
        m_free_position(0),
        m_num(0) {}

  void build(const NodeId& root) {
    int32_t partition = -1;
    start_visit(root, &partition);
    while (!m_frames.empty()) {
      Frame& frame = m_frames.top();
      if (frame.succ_it == frame.succ_end) {
        if (frame.kind == Frame::Kind::Visit) {
          finish_visit(frame);
        } else {
          finish_component();
        }
        continue;
      }
      NodeId succ = *frame.succ_it;
      ++frame.succ_it;
      uint32_t succ_dfn = get_dfn(succ);
      if (succ_dfn == 0) {
        // The frame resumes once this visit returns.
        start_visit(succ, frame.partition);
      } else if (frame.kind == Frame::Kind::Visit) {
        update_head(frame, succ_dfn);
      }
    }
  }

 private:
  // We keep the notations used by Bourdoncle in the paper to describe the
  // algorithm.

  // What the successor function returns: a container, or a reference to one.
  using Successors =
      decltype(std::declval<SuccFn&>()(std::declval<const NodeId&>()));
  using SuccessorIterator = decltype(std::begin(std::declval<Successors&>()));
  using SuccessorSentinel = decltype(std::end(std::declval<Successors&>()));

  // A call to visit(vertex, partition) or component(vertex) in progress.
  struct Frame {
    enum class Kind { Visit, Component };

    // A visit adds to the caller's partition. A component starts from a copy
    // of it and builds its own.
    Frame(Kind kind,
          const NodeId& vertex,
          int32_t* partition,
          uint32_t head,
          SuccFn& successors)
        : kind(kind),
          vertex(vertex),
          partition(kind == Kind::Visit ? partition : &own_partition),
          own_partition(kind == Kind::Visit ? -1 : *partition),
          head(head),
          succs(successors(vertex)),
          succ_it(std::begin(succs)),
          succ_end(std::end(succs)) {}

    // Frames stay in place: `succ_it` points into `succs`, and the frames
    // above a component point to its `own_partition`.
    Frame(const Frame&) = delete;
    Frame& operator=(const Frame&) = delete;
    Frame(Frame&&) = delete;
    Frame& operator=(Frame&&) = delete;
    ~Frame() = default;

    Kind kind;
    NodeId vertex;
    int32_t* partition;
    int32_t own_partition;
    uint32_t head;
    bool loop{false};
    Successors succs;
    SuccessorIterator succ_it;
    SuccessorSentinel succ_end;
  };

  void start_visit(const NodeId& vertex, int32_t* partition) {
    m_stack.push(vertex);
    uint32_t head = set_dfn(vertex, ++m_num);
    m_frames.emplace(Frame::Kind::Visit, vertex, partition, head, m_successors);
  }

  void update_head(Frame& frame, uint32_t min) {
    if (min <= frame.head) {
      frame.head = min;
      frame.loop = true;
    }
  }

  // The end of visit, once all successors have been explored.
  void finish_visit(Frame& frame) {
    if (frame.head == get_dfn(frame.vertex)) {
      // We encode the special value +oo used in the paper with UINT32_MAX.
      set_dfn(frame.vertex, std::numeric_limits<uint32_t>::max());
      NodeId element = m_stack.top();
      m_stack.pop();
      if (frame.loop) {
        // Nodes are required to be comparable using `operator==()`. We don't
        // assume `operator!=()` to be defined on nodes.
        while (!(element == frame.vertex)) {
          set_dfn(element, 0);
          element = m_stack.top();
          m_stack.pop();
        }
        // `finish_component` adds the SCC once component(vertex) is done.
        m_frames.emplace(Frame::Kind::Component, frame.vertex, frame.partition,
                         /* head */ 0, m_successors);
        return;
      }
      add_component(frame, WtoComponent<NodeId>::Kind::Vertex);
    }
    return_from_visit();
  }

  // The end of component, once all successors have been explored.
  void finish_component() {
    m_frames.pop();
    // The caller of component(vertex) is visit(vertex, partition).
    add_component(m_frames.top(), WtoComponent<NodeId>::Kind::Scc);
    return_from_visit();
  }

  // Pops the visit on top of the stack and hands its result to the caller.
  void return_from_visit() {
    uint32_t head = m_frames.top().head;
    m_frames.pop();
    if (!m_frames.empty() && m_frames.top().kind == Frame::Kind::Visit) {
      update_head(m_frames.top(), head);
    }
  }

  void add_component(Frame& frame, typename WtoComponent<NodeId>::Kind kind) {
    m_wto_space->emplace_back(frame.vertex, kind, m_free_position,
                              *frame.partition);
    *frame.partition = m_free_position++;
  }

  uint32_t get_dfn(const NodeId& node) {
    auto it = m_dfn.find(node);
    if (it != m_dfn.end()) {
      return it->second;
    }
    return 0;
  }

  uint32_t set_dfn(const NodeId& node, uint32_t number) {
    if (number == 0) {
      m_dfn.erase(node);
    } else {
      m_dfn[node] = number;
    }
    return number;
  }

  SuccFn m_successors;
  std::vector<WtoComponent<NodeId>>* m_wto_space;
  // The next available position at the end of the vector of components.
  int32_t m_free_position;
  // These are auxiliary data structures used by Bourdoncle's algorithm.
  std::unordered_map<NodeId, uint32_t, NodeHash> m_dfn;
  std::stack<NodeId> m_stack;
  uint32_t m_num;
  // The calls in progress, innermost last. A deque never moves its elements.
  std::stack<Frame, std::deque<Frame>> m_frames;
};

} // namespace wto_impl

} // namespace sparta

template <typename NodeId>
inline std::ostream& operator<<(
    std::ostream& o, const typename sparta::WtoComponent<NodeId>& c) {
  using namespace sparta;
  if (c.is_scc()) {
    o << "(" << c.head_node();
    for (const WtoComponent<NodeId>& sub : c) {
      o << " " << sub;
    }
    o << ")";
  } else {
    o << c.head_node();
  }
  return o;
}

template <typename NodeId>
inline std::ostream& operator<<(
    std::ostream& o,
    const typename sparta::WeakTopologicalOrdering<NodeId>& wto) {
  for (auto it = wto.begin(); it != wto.end();) {
    o << *it++;
    if (it != wto.end()) {
      o << " ";
    }
  }
  return o;
}
