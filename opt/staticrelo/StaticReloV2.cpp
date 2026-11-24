/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "StaticReloV2.h"

#include "ApiLevelChecker.h"
#include "ClassHierarchy.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexUtil.h"
#include "MethodUtil.h"
#include "PassManager.h"
#include "Resolver.h"
#include "Show.h"
#include "Trace.h"
#include "Walkers.h"

/**
 * Implementation:
 * 1. Generate candidate classes that only contain static methods which can be
 *    renamed and deleted
 * 2. Generate call graph for all these static methods from candidate classes
 * 3. For each other classes, find out their callees from theses static methods
 *    transitively, color these callees into the class's color. Some static
 *    methods may be colored into multiple colors
 * 4. Relocate
 *    a. If a static method only has 1 color, relocate it to the class of that
 *       color
 *    b. If a static method has no color, relocate it if it has only one caller,
 *       log it if it has no caller ( should be deleted by other pass ).
 *    c. If a static method has multiple colors, keep it unchanged.
 */

namespace {

constexpr const char* METRIC_RELOCATED = "num_relocated_static_methods";
constexpr const char* METRIC_EMPTY_CLASSES = "num_empty_classes";

/**
 * The call graph of all the static methods in the candidate classes
 */
struct StaticCallGraph {
  /**
   * Vertex is a static method with additional information for coloring
   */
  struct Vertex {
    // A static method
    DexMethod* method;
    // Color is associated to a DexClass that the static method might be able to
    // relocated to, depends on the final coloring results
    int color; // -1 means empty color, -2 means multiple colors
    // Index of the vertex in the vertices
    int id;
    Vertex(DexMethod* meth, int idx) : method(meth), color(-1), id(idx) {}
    /**
     * Try to color the vertex with color c
     * Return boolean to indicate if we want to continue coloring its neighbors
     */
    bool should_continue_color(int c) {
      if (color == -2 || color == c) { // multiple colors or already colored
        return false;
      } else if (color == -1) { // empty color
        color = c;
      } else { // already colored to another color
        color = -2;
      }
      return true;
    }
  };
  UnorderedMap<DexMethod*, int> method_id_map;
  std::vector<Vertex> vertices;
  // The direction of the edge points from the caller to callee. For example,
  // callees[0] = {1,2} means vertex 0 has two callees and they are 1 and 2
  std::vector<UnorderedSet<int>> callees;
  // The direction of the edge points from the callee to caller
  std::vector<UnorderedSet<int>> callers;

  // push into static methods to construct call graph
  void add_vertex(DexMethod* method) {
    always_assert(method_id_map.count(method) == 0);
    int idx = static_cast<int>(method_id_map.size());
    method_id_map[method] = idx;
    vertices.emplace_back(method, idx);
  }
};

/**
 * Build call graph for all static methods in candidate classes
 */
void build_call_graph(const std::vector<DexClass*>& candidate_classes,
                      StaticCallGraph& graph) {
  walk::classes(candidate_classes, [&](DexClass* cls) {
    // The candidate class set only contains classes with only static methods
    for (auto& method : cls->get_dmethods()) {
      graph.add_vertex(method);
    }
  });

  graph.callers.resize(graph.vertices.size());
  graph.callees.resize(graph.vertices.size());

  for (auto& meth_id : UnorderedIterable(graph.method_id_map)) {
    DexMethod* caller = meth_id.first;
    int caller_id = meth_id.second;
    if (caller->get_code() == nullptr) {
      continue;
    }
    always_assert(caller->get_code()->cfg_built());
    for (const auto& mie :
         cfg::InstructionIterable(caller->get_code()->cfg())) {
      if (mie.insn->has_method()) {
        if (mie.insn->opcode() != OPCODE_INVOKE_STATIC) {
          continue;
        }
        DexMethod* callee = resolve_method_deprecated(mie.insn->get_method(),
                                                      MethodSearch::Static);
        if (graph.method_id_map.find(callee) != graph.method_id_map.end()) {
          int callee_id = graph.method_id_map[callee];
          graph.callers[callee_id].insert(caller_id);
          graph.callees[caller_id].insert(callee_id);
        }
      }
    }
  }
}

void color_vertex(StaticCallGraph& graph, DexMethod* method, int color);

void color_vertex(StaticCallGraph& graph,
                  StaticCallGraph::Vertex& vertex,
                  int color) {
  if (vertex.should_continue_color(color)) {
    // color the callees
    for (int callee_id : UnorderedIterable(graph.callees[vertex.id])) {
      color_vertex(graph, graph.vertices[callee_id], color);
    }
    if (is_private(vertex.method)) {
      // color callers within the same class of this private vertex.method
      for (int caller_id : UnorderedIterable(graph.callers[vertex.id])) {
        DexMethod* caller = graph.vertices[caller_id].method;
        if (caller->get_class() == vertex.method->get_class()) {
          color_vertex(graph, caller, color);
        }
      }
    }
  }
}

void color_vertex(StaticCallGraph& graph, DexMethod* method, int color) {
  // Assume the method is in the map
  always_assert(graph.method_id_map.count(method) == 1);
  int method_id = graph.method_id_map[method];
  color_vertex(graph, graph.vertices[method_id], color);
}

/**
 * Color the vertices for a class
 * For private static method, should color all the caller within the class to
 * the same color
 */
void color_from_a_class(StaticCallGraph& graph, DexClass* cls, int color) {
  auto process_method = [&](DexMethod* caller) {
    IRCode* code = caller->get_code();
    if (code == nullptr) {
      return;
    }
    always_assert(code->cfg_built());
    auto& cfg = code->cfg();
    for (const auto& mie : cfg::InstructionIterable(cfg)) {
      if (mie.insn->has_method()) {
        if (mie.insn->opcode() != OPCODE_INVOKE_STATIC) {
          continue;
        }
        DexMethod* callee = resolve_method_deprecated(mie.insn->get_method(),
                                                      MethodSearch::Static);
        if (graph.method_id_map.find(callee) != graph.method_id_map.end()) {
          color_vertex(graph, callee, color);
        }
      }
    }
  };
  for (DexMethod* method : cls->get_vmethods()) {
    process_method(method);
  }
  for (DexMethod* method : cls->get_dmethods()) {
    process_method(method);
  }
}

// Code whose behavior depends on the class that holds it
// (`depends_on_holder_class`), such as an invoke-direct method handle of a
// method that is not private or an invoke-custom, stays in its class.
bool depends_on_its_class(const DexMethod* method) {
  for (const auto& mie :
       cfg::ConstInstructionIterable(method->get_code()->cfg())) {
    if (depends_on_holder_class(mie.insn)) {
      return true;
    }
  }
  return false;
}

/**
 * Relocate static methods in the graph to their callers
 */
int relocate_clusters(const StaticCallGraph& graph, const Scope& scope) {
  int relocated_methods = 0;
  for (const StaticCallGraph::Vertex& vertex : graph.vertices) {
    bool can_move = !depends_on_its_class(vertex.method);
    // Vertex is not colored, which means the method is unreachable outside the
    // static call graph. Do the proper logging or relocation for them if there
    // are such kind of unreachable static methods.
    if (vertex.color == -1) {
      int number_of_callers = static_cast<int>(graph.callers[vertex.id].size());
      TRACE(STATIC_RELO, 4,
            "method %s has %d static method callers, and the method and its "
            "callers are all unreachable from other classes. Enable "
            "RemoveUnreachablePass to remove them.",
            show(vertex.method).c_str(), number_of_callers);
      if (number_of_callers == 1 && can_move) {
        // Relocate the unreachable method to its caller class if only one
        // caller
        int caller_id = *unordered_any(graph.callers[vertex.id]);
        DexMethod* caller = graph.vertices[caller_id].method;
        change_visibility(vertex.method, caller->get_class());
        relocate_method(vertex.method, caller->get_class());
        relocated_methods++;
        set_public(vertex.method);
      }
    } else if (vertex.color >= 0) {
      // only one color
      auto* to_class = type_class(scope[vertex.color]->get_type());
      // We can relocate method to a class only if the api level of the class is
      // higher or equal to the api level of the method.
      if (can_move && to_class->rstate.get_api_level() >=
                          api::LevelChecker::get_method_level(vertex.method)) {
        change_visibility(vertex.method, to_class->get_type());
        relocate_method(vertex.method, to_class->get_type());
        relocated_methods++;
      }
      set_public(vertex.method);
    }
    // keep multiple colored vertices untouched
  }
  return relocated_methods;
}

} // namespace

namespace static_relo_v2 {

/**
 * Find out leaf classes that only contain static methods that can be renamed
 * and deleted.
 */
std::vector<DexClass*> StaticReloPassV2::gen_candidates(const Scope& scope) {
  std::vector<DexClass*> candidate_classes;
  ClassHierarchy ch = build_type_hierarchy(scope);
  walk::classes(scope, [&](DexClass* cls) {
    if (!cls->is_external() && get_children(ch, cls->get_type()).empty() &&
        !is_interface(cls) && cls->get_ifields().empty() &&
        cls->get_sfields().empty() && cls->get_vmethods().empty()) {
      for (const auto& method : cls->get_dmethods()) {
        if (!is_static(method) || !can_rename(method) || !can_delete(method) ||
            !method::is_optimizable(method)) {
          return;
        }
      }
      if (method::clinit_may_have_side_effects(
              cls, /* allow_benign_method_invocations */ false) != nullptr) {
        TRACE(STATIC_RELO, 9, "%s class initializer may have side effects",
              SHOW(cls));
        return;
      }
      candidate_classes.push_back(cls);
    }
  });
  return candidate_classes;
}

int StaticReloPassV2::run_relocation(
    const Scope& scope, std::vector<DexClass*>& candidate_classes) {
  StaticCallGraph graph;
  build_call_graph(candidate_classes, graph);
  UnorderedSet<DexClass*> set(candidate_classes.begin(),
                              candidate_classes.end());
  for (size_t color = 0; color < scope.size(); color++) {
    if (set.find(scope[color]) != set.end()) {
      continue;
    }
    color_from_a_class(graph, scope[color], static_cast<int>(color));
  }

  return relocate_clusters(graph, scope);
}

void StaticReloPassV2::run_pass(DexStoresVector& stores,
                                ConfigFiles& /* unused */,
                                PassManager& mgr) {
  Scope scope = build_class_scope(stores);
  std::vector<DexClass*> candidate_classes = gen_candidates(scope);
  TRACE(STATIC_RELO, 2, "candidate_classes %zu", candidate_classes.size());

  int relocated_methods = run_relocation(scope, candidate_classes);
  int empty_classes = 0;
  TRACE(STATIC_RELO, 4, "\tEmpty classes after relocation:");
  for (DexClass* cls : candidate_classes) {
    if (cls->get_dmethods().empty()) {
      empty_classes++;
      TRACE(STATIC_RELO, 4, "\t\t%s", show(cls).c_str());
    }
  }

  mgr.set_metric(METRIC_RELOCATED, relocated_methods);
  mgr.set_metric(METRIC_EMPTY_CLASSES, empty_classes);
  TRACE(STATIC_RELO, 2, "\trelocate %d static methods", relocated_methods);
  TRACE(STATIC_RELO, 2, "\tGenerate %d empty classes", empty_classes);
}

static StaticReloPassV2 s_pass;
} // namespace static_relo_v2
