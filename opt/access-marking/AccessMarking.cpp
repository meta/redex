/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "AccessMarking.h"

#include "ClassHierarchy.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "DexUtil.h"
#include "FieldOpTracker.h"
#include "IRCode.h"
#include "MethodOverrideGraph.h"
#include "PassManager.h"
#include "ReachableClasses.h"
#include "Resolver.h"
#include "Show.h"
#include "Trace.h"
#include "Walkers.h"

namespace mog = method_override_graph;

namespace {

size_t mark_classes_final(const Scope& scope) {
  ClassHierarchy ch = build_type_hierarchy(scope);
  size_t n_classes_finalized = 0;
  for (auto const& cls : scope) {
    if (!can_rename(cls) || is_abstract(cls) || is_final(cls)) {
      continue;
    }
    auto const& children = get_children(ch, cls->get_type());
    if (children.empty()) {
      TRACE(ACCESS, 2, "Finalizing class: %s", SHOW(cls));
      set_final(cls);
      ++n_classes_finalized;
    }
  }
  return n_classes_finalized;
}

size_t mark_methods_final(const Scope& scope,
                          const mog::Graph& override_graph,
                          bool mark_do_not_strip_as_final) {
  size_t n_methods_finalized = 0;
  for (auto const& cls : scope) {
    for (auto const& method : cls->get_vmethods()) {
      bool is_can_rename = mark_do_not_strip_as_final
                               ? !method->rstate.no_optimizations()
                               : can_rename(method);
      if (!is_can_rename || is_abstract(method) || is_final(method)) {
        continue;
      }
      if (override_graph.get_node(method).children.empty()) {
        TRACE(ACCESS, 2, "Finalizing method: %s", SHOW(method));
        set_final(method);
        ++n_methods_finalized;
      }
    }
  }
  return n_methods_finalized;
}

size_t mark_fields_final(const Scope& scope,
                         bool consider_unwritten_fields,
                         bool consider_written_fields) {
  field_op_tracker::FieldStatsMap field_stats =
      field_op_tracker::analyze(scope);

  size_t n_fields_finalized = 0;
  for (auto& pair : UnorderedIterable(field_stats)) {
    auto* field = pair.first;
    auto& stats = pair.second;
    if (stats.init_writes == stats.writes && can_rename(field) &&
        !is_final(field) && !is_volatile(field) && !field->is_external()) {
      if (!consider_unwritten_fields && stats.writes == 0) {
        continue;
      }
      if (!consider_written_fields && stats.writes > 0) {
        continue;
      }
      // Note: There is one more thing that javac enforces around final fields:
      // That there's at most one write to the field along any control-flow
      // path. We skip the complexities of checking that here, as the JVM spec
      // doesn't call this out as a requirement.
      //
      // Except for the following special case for sanity:
      if (is_static(field) && !field->get_static_value()->is_zero() &&
          stats.writes > 0) {
        // Let's not make fields final if they have both a static value and are
        // written to in the static initializer. I cannot see where the JVM spec
        // would forbid making it final in this case, but we'll be conservative
        // to be safe and sane.
        continue;
      }
      set_final(field);
      ++n_fields_finalized;
    }
  }
  return n_fields_finalized;
}

ConcurrentSet<DexMethod*> find_private_methods(
    const std::vector<DexClass*>& scope, const mog::Graph& override_graph) {
  ConcurrentSet<DexMethod*> candidates;
  auto is_excluded = [](DexMethod* m) {
    TRACE(ACCESS, 3, "Considering for privatization: %s", SHOW(m));
    return method::is_clinit(m) || !can_rename(m) || is_abstract(m) ||
           is_private(m);
  };
  workqueue_run<DexClass*>(
      [&](DexClass* cls) {
        for (auto* m : cls->get_dmethods()) {
          if (!is_excluded(m)) {
            candidates.insert(m);
          }
        }
        for (auto* m : cls->get_vmethods()) {
          if (!is_excluded(m) &&
              !method_override_graph::is_true_virtual(override_graph, m)) {
            candidates.insert(m);
          }
        }
      },
      scope);

  walk::parallel::opcodes(
      scope,
      [](DexMethod*) { return true; },
      [&](DexMethod* caller, IRInstruction* inst) {
        // A method handle is resolved, and checked for access, in the class of
        // the code that holds it, like an invoke there.
        for_each_invoke(inst, [&](IROpcode opcode, DexMethodRef* method_ref,
                                  const DexMethodHandle* method_handle) {
          auto* callee = method_handle == nullptr
                             ? resolve_method_deprecated(
                                   method_ref, opcode_to_search(opcode), caller)
                             : resolve_method_handle(method_handle, caller);
          // A same-class handle may still name a private method: from ART 8.0
          // on, a private method behind an invoke-instance or invoke-interface
          // handle is called directly, whatever the receiver's class.
          if (callee == nullptr || callee->get_class() == caller->get_class()) {
            return;
          }
          candidates.erase(callee);
        });
      });

  return candidates;
}

void fix_call_sites_private(const std::vector<DexClass*>& scope,
                            const ConcurrentSet<DexMethod*>& privates) {
  walk::parallel::code(scope, [&](DexMethod* caller, IRCode& code) {
    always_assert(code.cfg_built());
    auto& cfg = code.cfg();
    for (const MethodItemEntry& mie : cfg::InstructionIterable(cfg)) {
      IRInstruction* insn = mie.insn;
      if (!insn->has_method()) {
        continue;
      }
      auto* callee = resolve_method_deprecated(insn->get_method(),
                                               opcode_to_search(insn), caller);
      // should be safe to read `privates` here because there are no writers
      if (callee != nullptr && (privates.count_unsafe(callee) != 0u)) {
        insn->set_method(callee);
        if (!is_static(callee)) {
          insn->set_opcode(OPCODE_INVOKE_DIRECT);
        }
      }
    }
  });
}

void mark_methods_private(const ConcurrentSet<DexMethod*>& privates) {
  // Compute an ordered representation of the methods. This matters, as
  // the dmethods and vmethods are not necessarily sorted, but add_method does
  // a best-effort of inserting in an ordered matter.
  // But when dmethods and vmethods are not ordered to begin with, then the
  // order in which we attempt to add matters.
  auto ordered_privates = unordered_to_ordered(privates, compare_dexmethods);

  for (auto* method : ordered_privates) {
    TRACE(ACCESS, 2, "Privatized method: %s", SHOW(method));
    auto* cls = type_class(method->get_class());
    cls->remove_method(method);
    method->set_virtual(false);
    set_private(method);
    cls->add_method(method);
  }
}
} // namespace

void AccessMarkingPass::run_pass(DexStoresVector& stores,
                                 ConfigFiles& /* conf */,
                                 PassManager& pm) {
  auto scope = build_class_scope(stores);
  auto override_graph = mog::build_graph(scope);
  if (m_finalize_classes) {
    auto n_classes_final = mark_classes_final(scope);
    pm.incr_metric("finalized_classes", n_classes_final);
    TRACE(ACCESS, 1, "Finalized %zu classes", n_classes_final);
  }
  if (m_finalize_methods) {
    auto n_methods_final = mark_methods_final(scope, *override_graph,
                                              m_mark_do_not_strip_as_final);
    pm.incr_metric("finalized_methods", n_methods_final);
    TRACE(ACCESS, 1, "Finalized %zu methods", n_methods_final);
  }
  if (m_finalize_unwritten_fields || m_finalize_written_fields) {
    auto n_fields_final = mark_fields_final(scope, m_finalize_unwritten_fields,
                                            m_finalize_written_fields);
    pm.incr_metric("finalized_fields", n_fields_final);
    TRACE(ACCESS, 1, "Finalized %zu fields", n_fields_final);
  }
  if (m_privatize_methods) {
    auto privates = find_private_methods(scope, *override_graph);
    fix_call_sites_private(scope, privates);
    mark_methods_private(privates);
    pm.incr_metric("privatized_methods", privates.size());
    TRACE(ACCESS, 1, "Privatized %zu methods", privates.size());
  }
}

static AccessMarkingPass s_pass;
