/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "Deleter.h"

#include "Debug.h"
#include "MethodUtil.h"
#include "ReachableClasses.h"
#include "Show.h"
#include "Trace.h"
#include "Walkers.h"

std::vector<DexMethod*> delete_methods(
    std::vector<DexClass*>& scope,
    UnorderedSet<DexMethod*>& removable,
    std::function<DexMethod*(DexMethodRef*,
                             MethodSearch search,
                             const DexMethod*)> concurrent_resolver) {

  // if a removable candidate is invoked do not delete
  ConcurrentSet<DexMethod*> removable_to_erase;
  walk::parallel::opcodes(
      scope, [](DexMethod* /*meth*/) { return true; },
      [&](DexMethod* meth, IRInstruction* insn) {
        if (!opcode::is_a_method_invoke(insn->opcode())) {
          return;
        }
        auto* callee = concurrent_resolver(insn->get_method(),
                                           opcode_to_search(insn), meth);
        if (callee != nullptr && (removable.count(callee) != 0u)) {
          removable_to_erase.insert(callee);
        }
      });
  for (auto* method : UnorderedIterable(removable_to_erase)) {
    removable.erase(method);
  }

  // if a method handle in code, a static field value or an annotation names a
  // removable candidate or can run it, do not delete
  const auto named_by_method_handles =
      method::gather_methods_named_by_method_handles(scope);
  unordered_erase_if(removable, [&](const DexMethod* method) {
    return named_by_method_handles.count(method) != 0;
  });

  // if a removable candidate is referenced by an annotation do not delete
  walk::annotations(scope, [&](DexAnnotation* anno) {
    for (const auto& anno_element : anno->anno_elems()) {
      const auto& ev = anno_element.encoded_value;
      if (ev->evtype() == DEVT_METHOD) {
        DexEncodedValueMethod* evm =
            dynamic_cast<DexEncodedValueMethod*>(ev.get());
        if (evm->method()->is_def()) {
          removable.erase(evm->method()->as_def());
        }
      }
    }
  });

  std::vector<DexMethod*> deleted;
  for (auto* callee : UnorderedIterable(removable)) {
    if (!callee->is_concrete()) {
      continue;
    }
    if (!can_delete(callee)) {
      continue;
    }
    if (method::is_argless_init(callee)) {
      continue;
    }
    auto* cls = type_class(callee->get_class());
    always_assert_log(cls != nullptr,
                      "%s is concrete but does not have a DexClass\n",
                      SHOW(callee));
    cls->remove_method(callee);
    DexMethod::delete_method(callee);
    deleted.push_back(callee);
    TRACE(DELMET, 4, "removing %s", SHOW(callee));
  }
  return deleted;
}
