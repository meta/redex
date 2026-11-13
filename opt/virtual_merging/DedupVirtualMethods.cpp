/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "DedupVirtualMethods.h"

#include <map>
#include <vector>

#include "Debug.h"
#include "DexUtil.h"
#include "MethodFixup.h"
#include "MethodOverrideGraph.h"
#include "MethodProfiles.h"
#include "PositionAmbiguity.h"
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

struct Duplication {
  DexMethod* removed;
  DexMethod* survivor;
};

void find_duplications(
    const method_override_graph::Graph* graph,
    const DexMethod* root_method,
    DexMethod* survivor,
    const ConcurrentSet<DexMethodRef*>& super_invoked_methods,
    std::vector<Duplication>* result) {
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
      auto* mutable_child = const_cast<DexMethod*>(child);
      auto* child_survivor = survivor;
      if (super_invoked_methods.count_unsafe(mutable_child) != 0) {
        child_survivor = mutable_child;
      } else {
        result->push_back({mutable_child, survivor});
      }
      find_duplications(graph, child, child_survivor, super_invoked_methods,
                        result);
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
    method_profiles::MethodProfiles* method_profiles,
    positions::JoinStats* join_stats) {
  uint32_t ret = 0;
  auto graph = method_override_graph::build_graph(scope);
  UnorderedMap<DexMethodRef*, DexMethodRef*> removed_vmethods;
  std::vector<Duplication> duplications;
  UnorderedMap<DexMethod*, DexMethod*> removed_to_survivor;

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
      if (removed_to_survivor.count(method) != 0) {
        // Already folded into an ancestor. Its body is dropped below, so it
        // cannot host anything of its own.
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
      std::vector<Duplication> found;
      find_duplications(graph.get(), method, method, super_invoked_methods,
                        &found);
      // Removal is deferred until every body has been read, so a method
      // already folded away is still a definition here and is reached again.
      std::erase_if(found, [&](const auto& duplication) {
        return removed_to_survivor.count(duplication.removed) != 0;
      });

      if (!found.empty()) {
        if (method_profiles != nullptr) {
          std::vector<DexMethod*> sources;
          sources.reserve(found.size() + 1);
          for (const auto& duplication : found) {
            sources.push_back(duplication.removed);
          }
          sources.push_back(method);
          method_profiles->substitute_stats(method, sources);
        }
        if (is_protected(method)) {
          publicize_methods(graph.get(), method);
        }
        for (const auto& duplication : found) {
          auto* removed = duplication.removed;
          TRACE(VM,
                8,
                "%s shares the body of %s; references use %s",
                SHOW(removed),
                SHOW(duplication.survivor),
                SHOW(method));
          removed_to_survivor.emplace(removed, duplication.survivor);
          removed_vmethods.emplace(removed, method);
        }
        ret += found.size();
        duplications.insert(duplications.end(), found.begin(), found.end());
        TRACE(VM, 9, "%s\n", SHOW(method->get_code()->cfg()));
      }
    }
  });

  // A survivor can itself be folded into an ancestor by a later class, so the
  // body that ends up serving a removed method is the end of that chain.
  auto final_survivor = [&removed_to_survivor](DexMethod* survivor) {
    // Every step moves to a strict ancestor, so the chain cannot cycle. The
    // bound turns a broken invariant into a failure instead of a hang.
    for (size_t step = 0; step <= removed_to_survivor.size(); ++step) {
      auto it = removed_to_survivor.find(survivor);
      if (it == removed_to_survivor.end()) {
        return survivor;
      }
      survivor = it->second;
    }
    not_reached_log("a chain of deduplicated overrides does not terminate");
  };

  std::map<DexMethod*, std::vector<DexMethod*>, dexmethods_comparator>
      victims_by_survivor;
  for (const auto& duplication : duplications) {
    victims_by_survivor[final_survivor(duplication.survivor)].push_back(
        duplication.removed);
  }
  // Comparing the lines reads the removed bodies, so it has to happen while
  // they are all still concrete.
  for (const auto& [survivor, victims] : victims_by_survivor) {
    positions::join_throwing_positions(survivor, victims, join_stats);
  }

  for (const auto& duplication : duplications) {
    auto* removed = duplication.removed;
    type_class(removed->get_class())->remove_method(removed);
    DexMethod::delete_method(removed);
  }

  method_fixup::fixup_references_to_removed_methods(scope, removed_vmethods);

  return ret;
}

} // namespace

namespace dedup_vmethods {

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

uint32_t dedup(const DexStoresVector& stores,
               method_profiles::MethodProfiles* method_profiles,
               positions::JoinStats* join_stats) {
  auto scope = build_class_scope(stores);
  ConcurrentSet<DexMethodRef*> super_invoked_methods;
  collect_all_invoke_super_called(scope, &super_invoked_methods);
  auto deduplicated_vmethods = remove_duplicated_vmethods(
      scope, super_invoked_methods, method_profiles, join_stats);
  TRACE(VM, 2, "deduplicated_vmethods %u\n", deduplicated_vmethods);
  return deduplicated_vmethods;
}

} // namespace dedup_vmethods
