/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "DedupVirtualMethods.h"

#include <vector>

#include "Debug.h"
#include "DexUtil.h"
#include "MethodFixup.h"
#include "MethodOverrideGraph.h"
#include "MethodProfiles.h"
#include "Show.h"
#include "Trace.h"
#include "Walkers.h"

namespace {
// Only look at small methods. Increase the limit does not match more
// identical code in practise.
constexpr const uint32_t MAX_NUM_INSTRUCTIONS = 32;

/**
 * Allow code without invoke-super and with less than MAX_NUM_INSTRUCTIONS
 * instructions.
 */
bool eligible_code(const cfg::ControlFlowGraph& cfg) {
  uint32_t count = 0;
  for (const auto& mie : cfg::ConstInstructionIterable(cfg)) {
    auto opcode = mie.insn->opcode();
    if (opcode::is_invoke_super(opcode)) {
      return false;
    }
    if (!opcode::is_an_internal(opcode)) {
      count++;
    }
    if (count > MAX_NUM_INSTRUCTIONS) {
      return false;
    }
  }
  return true;
}

} // namespace

namespace dedup_vmethods {

bool is_removable_copy(const DexMethod* method) {
  if (root(method) || !can_rename(method) ||
      method->rstate.no_optimizations()) {
    return false;
  }
  const auto* code = method->get_code();
  if (code == nullptr) {
    return false;
  }
  always_assert(code->cfg_built());
  return eligible_code(code->cfg());
}

} // namespace dedup_vmethods

namespace {

void find_duplications(const method_override_graph::Graph* graph,
                       const DexMethod* root_method,
                       std::vector<DexMethod*>* result) {
  const auto* root_code = root_method->get_code();
  if (root_code == nullptr) {
    return;
  }

  always_assert(root_code->cfg_built());
  const auto& root_cfg = root_code->cfg();

  for (auto* child_node :
       UnorderedIterable(graph->get_node(root_method).children)) {
    const auto* child = child_node->method;
    // The method definition may be deleted after the overriding graph is
    // created, check if it's still a definition.
    if (!child->is_def() || !dedup_vmethods::is_removable_copy(child)) {
      continue;
    }
    if (root_cfg.structural_equals(child->get_code()->cfg())) {
      result->push_back(const_cast<DexMethod*>(child));
      find_duplications(graph, child, result);
    }
  }
}

/**
 * Make the method and all its overriding methods be public.
 */
void publicize_methods(const method_override_graph::Graph* graph,
                       DexMethod* root_method) {
  set_public(root_method);
  for (auto* child : UnorderedIterable(graph->get_node(root_method).children)) {
    if (is_public(child->method)) {
      // The children of child should all be public, otherwise the code is
      // invalid before this transformation.
      continue;
    }
    redex_assert(is_protected(child->method));
    publicize_methods(graph, const_cast<DexMethod*>(child->method));
  }
}

/**
 * Deduplicate identical overriding code.
 */
uint32_t remove_duplicated_vmethods(
    const Scope& scope,
    const ConcurrentSet<DexMethodRef*>& super_invoked_methods,
    method_profiles::MethodProfiles* method_profiles) {
  uint32_t ret = 0;
  auto graph = method_override_graph::build_graph(scope);
  UnorderedMap<DexMethodRef*, DexMethodRef*> removed_vmethods;

  walk::classes(scope, [&](DexClass* cls) {
    for (auto* method : cls->get_vmethods()) {
      if (method->get_code() == nullptr) {
        // TODO: look at the abstract methods and we can lift the
        // implementations to the abstract class if lots of them are identical.
        continue;
      }
      // Its code at runtime may differ from the code Redex sees.
      if (method->rstate.no_optimizations()) {
        continue;
      }
      if (!is_public_or_protected(method)) {
        // Note: package-private methods are skipped. Need consider package
        // names when change the accessibility of them.
        continue;
      }
      always_assert(method->get_code()->cfg_built());
      if (!eligible_code(method->get_code()->cfg())) {
        continue;
      }
      std::vector<DexMethod*> duplicates;
      find_duplications(graph.get(), method, &duplicates);

      // Now, remove the methods that are called with INVOKE_SUPER from
      // the duplicates set.
      std::erase_if(duplicates, [&](auto& m) {
        return super_invoked_methods.count_unsafe(m);
      });

      if (!duplicates.empty()) {
        if (method_profiles != nullptr) {
          auto sources = duplicates;
          sources.push_back(method);
          method_profiles->substitute_stats(method, sources);
        }
        if (is_protected(method)) {
          publicize_methods(graph.get(), method);
        }
        TRACE(VM, 8, "Same as %s", SHOW(method));
        for (auto* m : duplicates) {
          TRACE(VM, 8, "\t%s", SHOW(m));
          type_class(m->get_class())->remove_method(m);
          removed_vmethods.emplace(m, method);
          DexMethod::delete_method(m);
        }
        ret += duplicates.size();
        TRACE(VM, 9, "%s\n", SHOW(method->get_code()->cfg()));
      }
    }
  });

  method_fixup::fixup_references_to_removed_methods(scope, removed_vmethods);

  return ret;
}

/**
 * Collect all the methods that are called with INVOKE_SUPPER opcode
 */
void collect_all_invoke_super_called(
    const Scope& scope, ConcurrentSet<DexMethodRef*>* super_invoked_methods) {
  walk::parallel::code(scope, [&](DexMethod* /*method*/, IRCode& code) {
    cfg_adapter::iterate(&code, [&](MethodItemEntry& mie) {
      auto* insn = mie.insn;
      if (insn->opcode() == OPCODE_INVOKE_SUPER) {
        auto* callee_ref = insn->get_method();
        super_invoked_methods->insert(callee_ref);
      }
      return cfg_adapter::LOOP_CONTINUE;
    });
  });
}
} // namespace

namespace dedup_vmethods {

uint32_t dedup(const DexStoresVector& stores,
               method_profiles::MethodProfiles* method_profiles) {
  auto scope = build_class_scope(stores);
  ConcurrentSet<DexMethodRef*> super_invoked_methods;
  collect_all_invoke_super_called(scope, &super_invoked_methods);
  auto deduplicated_vmethods =
      remove_duplicated_vmethods(scope, super_invoked_methods, method_profiles);
  TRACE(VM, 2, "deduplicated_vmethods %u\n", deduplicated_vmethods);
  return deduplicated_vmethods;
}

} // namespace dedup_vmethods
