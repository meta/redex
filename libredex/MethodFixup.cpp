/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "MethodFixup.h"

#include "Debug.h"
#include "DexMethodHandle.h"
#include "IRCode.h"
#include "MethodHandleRewriter.h"
#include "Show.h"
#include "Walkers.h"

namespace method_fixup {

void fixup_references_to_removed_methods(
    const Scope& scope,
    UnorderedMap<DexMethodRef*, DexMethodRef*>& removed_vmethods) {
  // Forward chains.
  auto&& ui = UnorderedIterable(removed_vmethods);
  using iterator = std::remove_reference_t<decltype(ui)>::iterator;
  std::function<DexMethodRef*(iterator&)> forward;
  forward = [&forward, &ui](iterator& it) {
    auto it2 = ui.find(it->second);
    if (it2 != ui.end()) {
      it->second = forward(it2);
    }
    return it->second;
  };
  for (auto it = ui.begin(); it != ui.end(); it++) {
    forward(it);
  }

  // A method handle of a deleted vmethod cannot name the base one, as invokes
  // do: the receiver type of a handle of an instance method is the class of
  // the method it names. It names the deleted vmethod's class instead, through
  // a reference that resolves to the base one.
  MethodHandleRewriter method_handle_rewriter(
      {.handle = [&](const DexMethodHandle* method_handle,
                     const DexMethod*) -> std::optional<DexMethodHandle> {
        if (!DexMethodHandle::isInvokeType(method_handle->type())) {
          return std::nullopt;
        }
        auto* method_ref = method_handle->methodref();
        if (removed_vmethods.count(method_ref) == 0) {
          return std::nullopt;
        }
        auto* new_method_ref = DexMethod::make_method(method_ref->get_class(),
                                                      method_ref->get_name(),
                                                      method_ref->get_proto());
        always_assert_log(!new_method_ref->is_def(), "%s was not deleted",
                          SHOW(method_ref));
        return DexMethodHandle(method_handle->type(), new_method_ref);
      }});

  // Fixup references in code to deleted vmethods to point to the base one.
  walk::parallel::code(scope, [&](DexMethod* method, IRCode& code) {
    cfg_adapter::iterate(&code, [&](MethodItemEntry& mie) {
      auto* insn = mie.insn;
      method_handle_rewriter.rewrite(insn, method);
      auto op = insn->opcode();
      if (opcode::is_invoke_virtual(op)) {
        auto it = removed_vmethods.find(insn->get_method());
        if (it != removed_vmethods.end()) {
          insn->set_method(it->second);
        }
      }
      always_assert_log((!opcode::is_invoke_virtual(op) &&
                         !opcode::is_invoke_interface(op)) ||
                            !removed_vmethods.count(insn->get_method()),
                        "%s", SHOW(insn));
      return cfg_adapter::LOOP_CONTINUE;
    });
  });
  method_handle_rewriter.rewrite(scope);
}

} // namespace method_fixup
