/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ReorderInterfacesDecl.h"
#include "ConfigFiles.h"

#include "DeterministicContainers.h"
#include "DexClass.h"
#include "DexUtil.h"
#include "PassManager.h"
#include "Resolver.h"
#include "Walkers.h"

/**
 * This pass reorders Interface list for each class to improve the
 * linear walk of this list when there is an invocation of a function
 * defined in one of these Interfaces.
 *
 * This pass first computes the number of function invocations for each
 * Interface across the app and sorts the Interface list in descending order
 * of the number of invocations. An alphabetical sort is used for tie-breaks
 * to increase consistency across Classes.
 */
namespace {
using CallFrequencyMap = UnorderedMap<const DexType*, int>;

/**
 * Helper class to implement the pass
 */
class ReorderInterfacesDeclImpl {
 public:
  explicit ReorderInterfacesDeclImpl(Scope& scope) : m_scope(scope) {}
  void run();

 private:
  // Map to store the number of method invokes for each Interface
  CallFrequencyMap m_call_frequency_map;

  // Pointer to the Scope object used for the pass
  Scope& m_scope;

  void compute_call_frequencies(IRInstruction* insn);
  void reorder_interfaces();
  void reorder_interfaces_for_class(DexClass* cls);
  DexTypeList* sort_interfaces(const DexTypeList* unsorted_list);
};

/**
 * Run the pass by first computing call frequencies for each interface
 * then sorting the list of Interfaces for each Class.
 */
void ReorderInterfacesDeclImpl::run() {
  // Check out each instruction and process if it is a function invoke
  walk::opcodes(
      m_scope,
      [](DexMethod*) { return true; },
      [this](DexMethod* /* unused */, IRInstruction* insn) {
        compute_call_frequencies(insn);
      });

  // Now that we have the invoke frequencies for each Interface,
  // reorder the list of Interfaces for each Class.
  reorder_interfaces();
}

/**
 * Check whether the given instruction is a call to an Interface.
 * If so, increment the call frequency to that Interface.
 *
 * This method is used when we walk the opcodes in
 * ReorderInterfacesDeclImpl::run.
 */
void ReorderInterfacesDeclImpl::compute_call_frequencies(IRInstruction* insn) {
  // Process only call instructions
  if (opcode::is_a_method_invoke(insn->opcode())) {
    auto* callee = insn->get_method();
    auto* def_callee =
        resolve_method_deprecated(callee, opcode_to_search(insn));
    if (def_callee != nullptr) {
      callee = def_callee;
    }
    if (callee != nullptr) {
      // Get the class this method is in. It may be an Interface or a Class
      auto* const callee_cls_type = callee->get_class();
      auto* const callee_cls = type_class(callee_cls_type);
      if (callee_cls != nullptr) {
        // If we are calling into an Interface, count this call.
        if (is_interface(callee_cls)) {
          m_call_frequency_map[callee_cls_type]++;
        }
      }
    }
  }
}

/**
 * Sort the list of given Interfaces with respect to the number of incoming
 * calls and return the sorted list
 */
DexTypeList* ReorderInterfacesDeclImpl::sort_interfaces(
    const DexTypeList* unsorted_list) {
  DexTypeList::ContainerType sorted_list;
  // Create list of interfaces and store frequencies
  std::vector<std::pair<const DexType*, int>> list_with_frequencies;
  list_with_frequencies.reserve(unsorted_list->size());
  for (const auto* interface : *unsorted_list) {
    list_with_frequencies.emplace_back(interface,
                                       m_call_frequency_map[interface]);
  }

  // Sort the list with respect to number of calls for each Interface.
  std::sort(
      list_with_frequencies.begin(),
      list_with_frequencies.end(),
      [](const auto& a, const auto& b) -> bool {
        return ((b.second < a.second) ||
                ((b.second == a.second) && compare_dextypes(a.first, b.first)));
      });

  // Strip the frequencies
  for (auto interface_frequency : list_with_frequencies) {
    sorted_list.push_back(interface_frequency.first);
  }

  // Return the sorted list
  return DexTypeList::make_type_list(std::move(sorted_list));
}

/**
 * Reorders Interface list for the given Class using the call frequencies
 */
void ReorderInterfacesDeclImpl::reorder_interfaces_for_class(DexClass* cls) {
  const auto* cur_interface_list = cls->get_interfaces();

  // If we have at most one interface implemented by this class,
  // no need to worry about sorting the interface list.
  if (cur_interface_list->size() <= 1) {
    return;
  }

  // Let's sort the Interface list
  auto* updated_interface_list = sort_interfaces(cur_interface_list);

  // Now that we have the sorted list of Interfaces, write it back.
  cls->set_interfaces(updated_interface_list);
}

/**
 * Reorders Interface list for all Classes in the Scope
 */
void ReorderInterfacesDeclImpl::reorder_interfaces() {
  for (auto* cls : m_scope) {
    reorder_interfaces_for_class(cls);
  }
}
} // namespace

/**
 * Compute the number of function invocations for each Interface and
 * sort the list of Interfaces for each Class.
 */
void ReorderInterfacesDeclPass::run_pass(DexStoresVector& stores,
                                         ConfigFiles& /* unused */,
                                         PassManager& /* unused */) {
  auto scope = build_class_scope(stores);

  ReorderInterfacesDeclImpl impl(scope);
  impl.run();
}

static ReorderInterfacesDeclPass ri_pass;
