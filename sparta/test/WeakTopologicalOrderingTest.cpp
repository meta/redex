/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <sparta/WeakTopologicalOrdering.h>

#include <boost/thread/thread.hpp>
#include <cstdint>
#include <gtest/gtest.h>
#include <limits>
#include <list>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

using namespace sparta;

class SimpleGraph final {
 public:
  SimpleGraph() {}

  void add_edge(const std::string& source, const std::string& target) {
    m_edges[source].insert(target);
  }

  std::vector<std::string> successors(const std::string& node) {
    auto& succs = m_edges[node];
    return std::vector<std::string>(succs.begin(), succs.end());
  }

 private:
  std::unordered_map<std::string, std::set<std::string>> m_edges;
  friend std::ostream& operator<<(std::ostream&, const SimpleGraph&);
};

/*
 * Print the graph in the DOT graph description language. You can use Graphviz
 * or a similar program to render the output.
 */
std::ostream& operator<<(std::ostream& o, const SimpleGraph& g) {
  o << "digraph {\n";
  for (auto& edge : g.m_edges) {
    for (auto& succ : edge.second) {
      o << edge.first << " -> " << succ << "\n";
    }
  }
  o << "}\n";
  return o;
}

/*
 * This graph and the corresponding weak topological ordering are described
 * on page 4 of Bourdoncle's paper:
 *   F. Bourdoncle. Efficient chaotic iteration strategies with widenings.
 *   In Formal Methods in Programming and Their Applications, pp 128-141.
 * The graph is given as follows:
 *
 *                 +-----------------------+
 *                 |           +-----+     |
 *                 |           |     |     |
 *                 V           V     |     |
 *     1 --> 2 --> 3 --> 4 --> 5 --> 6 --> 7 --> 8
 *           |           |                 ^     ^
 *           |           |                 |     |
 *           |           +-----------------+     |
 *           +-----------------------------------+
 *
 * Bourdoncle's algorithm computes the following weak topological ordering:
 *
 *     1 2 (3 4 (5 6) 7) 8
 */
TEST(WeakTopologicalOrderingTest, exampleFromThePaper) {
  SimpleGraph g;
  g.add_edge("1", "2");
  g.add_edge("2", "3");
  g.add_edge("3", "4");
  g.add_edge("4", "5");
  g.add_edge("5", "6");
  g.add_edge("6", "7");
  g.add_edge("7", "8");
  g.add_edge("2", "8");
  g.add_edge("4", "7");
  g.add_edge("6", "5");
  g.add_edge("7", "3");

  WeakTopologicalOrdering<std::string> wto(
      "1", [&g](const std::string& n) { return g.successors(n); });

  std::ostringstream s;
  s << wto;
  EXPECT_EQ("1 2 (3 4 (5 6) 7) 8", s.str());

  auto it = wto.begin();
  EXPECT_EQ("1", it->head_node());
  EXPECT_TRUE(it->is_vertex());
  ++it;
  EXPECT_EQ("2", it->head_node());
  EXPECT_TRUE(it->is_vertex());
  ++it;
  EXPECT_EQ("3", it->head_node());
  EXPECT_TRUE(it->is_scc());
  auto it1 = it->begin();
  EXPECT_EQ("4", it1->head_node());
  EXPECT_TRUE(it1->is_vertex());
  ++it1;
  EXPECT_EQ("5", it1->head_node());
  EXPECT_TRUE(it1->is_scc());
  auto it2 = it1->begin();
  EXPECT_EQ("6", it2->head_node());
  EXPECT_TRUE(it2->is_vertex());
  ++it2;
  EXPECT_TRUE(it2 == it1->end());
  ++it1;
  EXPECT_EQ("7", it1->head_node());
  EXPECT_TRUE(it1->is_vertex());
  ++it1;
  EXPECT_TRUE(it1 == it->end());
  ++it;
  EXPECT_EQ("8", it->head_node());
  EXPECT_TRUE(it->is_vertex());
  ++it;
  EXPECT_TRUE(it == wto.end());
}

/*
 * Check that we correctly handle the edge cases where we have a single-node
 * SCC as the last element of the top-level list of components, or as the last
 * subcomponent in a component
 */
TEST(WeakTopologicalOrderingTest, SingletonSccAtEnd) {
  {
    //             +--+
    //             v  |
    // +---+     +------+
    // | 1 | --> |  2   |
    // +---+     +------+
    SimpleGraph g;
    g.add_edge("1", "2");
    g.add_edge("2", "2");
    WeakTopologicalOrdering<std::string> wto(
        "1", [&g](const std::string& n) { return g.successors(n); });
    std::ostringstream s;
    s << wto;
    EXPECT_EQ("1 (2)", s.str()) << "failed to order graph:\n" << g;
    auto it = wto.begin();
    EXPECT_EQ("1", it->head_node());
    ++it;
    EXPECT_EQ("2", it->head_node());
    EXPECT_TRUE(it->is_scc());
    EXPECT_EQ(it->begin(), it->end());
  }

  {
    //             +--+
    //             v  |
    // +---+     +------+     +---+
    // | 1 | <-- |  2   | --> | 3 |
    // +---+     +------+     +---+
    //   |         ^
    //   +---------+
    SimpleGraph g;
    g.add_edge("1", "2");
    g.add_edge("2", "2");
    g.add_edge("2", "1");
    g.add_edge("2", "3");
    WeakTopologicalOrdering<std::string> wto(
        "1", [&g](const std::string& n) { return g.successors(n); });
    std::ostringstream s;
    s << wto;
    EXPECT_EQ("(1 (2)) 3", s.str()) << "failed to order graph:\n" << g;
    auto it = wto.begin();
    EXPECT_EQ("1", it->head_node());
    auto it1 = it->begin();
    EXPECT_EQ("2", it1->head_node());
    EXPECT_TRUE(it1->is_scc());
    EXPECT_EQ(it1->begin(), it1->end());
  }
}

/*
 * Check that we correctly handle the edge cases where we have a multi-node
 * SCC as the last element of the top-level list of components, or as the last
 * subcomponent in a component
 */
TEST(WeakTopologicalOrderingTest, SccAtEnd) {
  {
    //             +---------+
    //             v         |
    // +---+     +---+     +---+
    // | 1 | --> | 2 | --> | 3 |
    // +---+     +---+     +---+
    SimpleGraph g;
    g.add_edge("1", "2");
    g.add_edge("2", "3");
    g.add_edge("3", "2");

    WeakTopologicalOrdering<std::string> wto(
        "1", [&g](const std::string& n) { return g.successors(n); });
    std::ostringstream s;
    s << wto;
    EXPECT_EQ("1 (2 3)", s.str()) << "failed to order graph:\n" << g;
  }

  {
    //   +-------------------+
    //   |                   v
    // +---+     +---+     +---+     +---+
    // | 2 | <-- | 1 | <-- | 3 | --> | 4 |
    // +---+     +---+     +---+     +---+
    //   ^                   |
    //   +-------------------+
    SimpleGraph g;
    g.add_edge("1", "2");
    g.add_edge("2", "3");
    g.add_edge("3", "2");
    g.add_edge("3", "1");
    g.add_edge("3", "4");

    WeakTopologicalOrdering<std::string> wto(
        "1", [&g](const std::string& n) { return g.successors(n); });
    std::ostringstream s;
    s << wto;
    EXPECT_EQ("(1 (2 3)) 4", s.str()) << "failed to order graph:\n" << g;
  }
}

TEST(WeakTopologicalOrderingTest, SingleNode) {
  {
    // +---+
    // | 1 |
    // +---+
    SimpleGraph g;
    WeakTopologicalOrdering<std::string> wto(
        "1", [&g](const std::string& n) { return g.successors(n); });
    std::ostringstream s;
    s << wto;
    EXPECT_EQ("1", s.str()) << "failed to order graph:\n" << g;
    auto it = wto.begin();
    EXPECT_EQ("1", it->head_node());
    ++it;
    EXPECT_EQ(it, wto.end());
  }
}

TEST(WeakTopologicalOrderingTest, InvalidIteratorDeref) {
  SimpleGraph g;
  g.add_edge("1", "1");
  WeakTopologicalOrdering<std::string> wto(
      "1", [&g](const std::string& n) { return g.successors(n); });
  EXPECT_ANY_THROW(*wto.end());
  EXPECT_ANY_THROW(wto.end()->head_node());
  EXPECT_ANY_THROW(wto.end()++);
}

namespace {

// Successor lists indexed by node.
using IntGraph = std::vector<std::vector<uint32_t>>;

std::string wto_to_string(const IntGraph& graph, uint32_t root) {
  WeakTopologicalOrdering<uint32_t> wto(
      root, [&graph](uint32_t n) -> const std::vector<uint32_t>& {
        return graph[n];
      });
  std::ostringstream s;
  s << wto;
  return s.str();
}

// Runs `f` on a thread with a 512 KiB stack, the default size for secondary
// threads on macOS.
template <typename Fn>
void run_on_small_stack(Fn f) {
  boost::thread::attributes attributes;
  attributes.set_stack_size(size_t{512} * 1024);
  boost::thread thread(attributes, std::move(f));
  thread.join();
}

} // namespace

/*
 * The depth of the graph traversal must not translate into native stack depth.
 */
TEST(WeakTopologicalOrderingTest, LongChainOnSmallStack) {
  constexpr uint32_t kLength = 100000;
  // 0 -> 1 -> ... -> kLength-1
  IntGraph chain(kLength);
  for (uint32_t i = 0; i + 1 < kLength; ++i) {
    chain[i].push_back(i + 1);
  }
  // The same chain, closed into a loop by kLength-1 -> 0.
  IntGraph loop = chain;
  loop[kLength - 1].push_back(0);

  std::string chain_wto;
  std::string loop_wto;
  run_on_small_stack([&] {
    chain_wto = wto_to_string(chain, 0);
    loop_wto = wto_to_string(loop, 0);
  });

  std::string expected_chain;
  for (uint32_t i = 0; i < kLength; ++i) {
    expected_chain += (i == 0 ? "" : " ") + std::to_string(i);
  }
  EXPECT_EQ(expected_chain, chain_wto);
  EXPECT_EQ("(" + expected_chain + ")", loop_wto);
}

namespace {

/*
 * A direct transcription of the recursive formulation of Bourdoncle's
 * algorithm, which builds the WTO as nested lists of strings, to check
 * WeakTopologicalOrdering against.
 */
class RecursiveWto final {
 public:
  explicit RecursiveWto(const IntGraph& graph)
      : m_graph(graph), m_dfn(graph.size(), 0) {}

  std::string build(uint32_t root) {
    std::list<std::string> partition;
    visit(root, &partition);
    return join(partition);
  }

 private:
  uint32_t visit(uint32_t vertex, std::list<std::string>* partition) {
    m_stack.push_back(vertex);
    uint32_t head = m_dfn[vertex] = ++m_num;
    bool loop = false;
    for (uint32_t succ : m_graph[vertex]) {
      uint32_t min = m_dfn[succ] == 0 ? visit(succ, partition) : m_dfn[succ];
      if (min <= head) {
        head = min;
        loop = true;
      }
    }
    if (head == m_dfn[vertex]) {
      m_dfn[vertex] = std::numeric_limits<uint32_t>::max();
      uint32_t element = pop();
      if (loop) {
        while (element != vertex) {
          m_dfn[element] = 0;
          element = pop();
        }
        partition->push_front(component(vertex));
      } else {
        partition->push_front(std::to_string(vertex));
      }
    }
    return head;
  }

  std::string component(uint32_t vertex) {
    std::list<std::string> partition;
    for (uint32_t succ : m_graph[vertex]) {
      if (m_dfn[succ] == 0) {
        visit(succ, &partition);
      }
    }
    std::string result = "(" + std::to_string(vertex);
    for (const auto& c : partition) {
      result += " " + c;
    }
    return result + ")";
  }

  uint32_t pop() {
    uint32_t element = m_stack.back();
    m_stack.pop_back();
    return element;
  }

  static std::string join(const std::list<std::string>& partition) {
    std::string result;
    for (const auto& c : partition) {
      result += (result.empty() ? "" : " ") + c;
    }
    return result;
  }

  const IntGraph& m_graph;
  std::vector<uint32_t> m_dfn;
  std::vector<uint32_t> m_stack;
  uint32_t m_num{0};
};

void expect_wto_matches_reference(const IntGraph& graph, uint32_t root) {
  std::ostringstream description;
  for (uint32_t n = 0; n < graph.size(); ++n) {
    for (uint32_t succ : graph[n]) {
      description << n << " -> " << succ << "\n";
    }
  }
  EXPECT_EQ(RecursiveWto(graph).build(root), wto_to_string(graph, root))
      << "root " << root << " of graph:\n"
      << description.str();
}

} // namespace

TEST(WeakTopologicalOrderingTest, RandomGraphsMatchReference) {
  std::mt19937 rng(42);
  for (int i = 0; i < 20000; ++i) {
    uint32_t size = std::uniform_int_distribution<uint32_t>(1, 40)(rng);
    // From sparse to dense, with self-loops and duplicate edges.
    double edges_per_node = std::uniform_real_distribution<>(0.5, 4.0)(rng);
    uint32_t num_edges = static_cast<uint32_t>(size * edges_per_node);
    std::uniform_int_distribution<uint32_t> node(0, size - 1);
    IntGraph graph(size);
    for (uint32_t e = 0; e < num_edges; ++e) {
      graph[node(rng)].push_back(node(rng));
    }
    expect_wto_matches_reference(graph, node(rng));
  }
}

TEST(WeakTopologicalOrderingTest, StructuredGraphsMatchReference) {
  // Loops nested 500 deep: i -> i+1, and 999-i -> i.
  {
    IntGraph graph(1000);
    for (uint32_t i = 0; i < 999; ++i) {
      graph[i].push_back(i + 1);
    }
    for (uint32_t i = 0; i < 500; ++i) {
      graph[999 - i].push_back(i);
    }
    expect_wto_matches_reference(graph, 0);
  }
  // A sequence of 300 loops of 3 nodes, each one exiting to the next.
  {
    IntGraph graph(900);
    for (uint32_t i = 0; i < 900; i += 3) {
      graph[i].push_back(i + 1);
      graph[i + 1].push_back(i + 2);
      graph[i + 2].push_back(i);
      if (i + 3 < 900) {
        graph[i + 2].push_back(i + 3);
      }
    }
    expect_wto_matches_reference(graph, 0);
  }
  // Irreducible: 0 branches into both 1 and 2, which form a loop with two
  // entries; each of 1 and 2 also heads a self-loop and exits to 3.
  {
    IntGraph graph = {{1, 2}, {2, 1, 3}, {1, 2, 3}, {}};
    expect_wto_matches_reference(graph, 0);
    std::swap(graph[0][0], graph[0][1]);
    expect_wto_matches_reference(graph, 0);
  }
  // A chain of 2000 diamonds whose joins all branch back to the first node.
  {
    IntGraph graph(3 * 2000 + 1);
    for (uint32_t i = 0; i < 2000; ++i) {
      uint32_t top = 3 * i;
      graph[top] = {top + 1, top + 2};
      graph[top + 1] = {top + 3};
      graph[top + 2] = {top + 3};
      if (i % 2 == 1) {
        graph[top + 1].push_back(0);
      }
    }
    expect_wto_matches_reference(graph, 0);
  }
  // Complete graphs, which are one SCC in which every node is a back edge
  // target.
  for (uint32_t size : {2, 5, 30}) {
    IntGraph graph(size);
    for (uint32_t n = 0; n < size; ++n) {
      for (uint32_t m = 0; m < size; ++m) {
        graph[n].push_back(m);
      }
    }
    expect_wto_matches_reference(graph, 0);
  }
}
