/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "MethodReference.h"

#include "ControlFlow.h"
#include "Debug.h"
#include "DexMethodHandle.h"
#include "DexUtil.h"
#include "IRList.h"
#include "MethodHandleRewriter.h"
#include "Resolver.h"
#include "Show.h"
#include "Trace.h"
#include "Walkers.h"

namespace {
Scope build_class_scope_excluding_primary_dex(const DexStoresVector& stores) {
  Scope result;
  for (const auto& store : stores) {
    const auto& dexen = store.get_dexen();
    auto it = dexen.begin();
    if (store.is_root_store()) {
      it++;
    }
    for (; it != dexen.end(); it++) {
      for (const auto& clazz : *it) {
        result.push_back(clazz);
      }
    }
  }
  return result;
}
} // namespace

namespace method_reference {

IRInstruction* make_load_const(reg_t dest, size_t val) {
  auto* load = new IRInstruction(OPCODE_CONST);
  load->set_dest(dest);
  load->set_literal(static_cast<int32_t>(val));
  return load;
}

IRInstruction* make_invoke(DexMethod* callee,
                           IROpcode opcode,
                           const std::vector<reg_t>& args) {
  always_assert(callee->is_def() && is_public(callee));
  auto* invoke =
      (new IRInstruction(opcode))->set_method(callee)->set_srcs(args);
  return invoke;
}

void patch_callsite(const CallSite& callsite, const NewCallee& new_callee) {
  if (is_static(new_callee.method) || method::is_any_init(new_callee.method) ||
      new_callee.method->is_virtual()) {
    set_public(new_callee.method);
  }
  always_assert_log(is_public(new_callee.method) ||
                        new_callee.method->get_class() ==
                            callsite.caller->get_class(),
                    "\tUpdating a callsite of %s when not accessible from %s\n",
                    SHOW(new_callee.method), SHOW(callsite.caller));

  auto* code = callsite.caller->get_code();
  if (code->cfg_built()) {
    auto& cfg = code->cfg();
    auto* insn = callsite.insn;
    auto iterator = cfg.find_insn(insn);
    if (new_callee.additional_args != std::nullopt) {
      const auto& args = new_callee.additional_args.value();
      auto old_size = insn->srcs_size();
      insn->set_srcs_size(old_size + args.size());
      size_t pos = old_size;
      for (uint32_t arg : args) {
        auto reg = cfg.allocate_temp();
        // Seems it is different from dasm(OPCODE_CONST, {{VREG, reg}, {LITERAL,
        // arg}}) which will cause instruction_lowering crash. Why?
        auto* load_const = make_load_const(reg, arg);
        cfg.insert_before(iterator, load_const);
        insn->set_src(pos++, reg);
      }
    }
    insn->set_method(new_callee.method);
  } else {
    auto iterator = code->iterator_to(*callsite.mie);
    auto* insn = callsite.mie->insn;
    if (new_callee.additional_args != std::nullopt) {
      const auto& args = new_callee.additional_args.value();
      auto old_size = insn->srcs_size();
      insn->set_srcs_size(old_size + args.size());
      size_t pos = old_size;
      for (uint32_t arg : args) {
        auto reg = code->allocate_temp();
        // Seems it is different from dasm(OPCODE_CONST, {{VREG, reg}, {LITERAL,
        // arg}}) which will cause instruction_lowering crash. Why?
        auto* load_const = make_load_const(reg, arg);
        code->insert_before(iterator, load_const);
        insn->set_src(pos++, reg);
      }
    }
    insn->set_method(new_callee.method);
  }
  // Assuming the following move-result is there and good.
}

void update_call_refs_simple(
    const Scope& scope,
    const UnorderedMap<DexMethod*, DexMethod*>& old_to_new_callee) {
  if (old_to_new_callee.empty()) {
    return;
  }

  // The method that replaces `method`, or nullptr.
  auto get_new_callee = [&](DexMethod* method) -> DexMethod* {
    if (method == nullptr) {
      return nullptr;
    }
    auto it = old_to_new_callee.find(method);
    if (it == old_to_new_callee.end()) {
      return nullptr;
    }
    // At this point, a non static private should not exist.
    always_assert_log(!is_private(it->second) || is_static(it->second), "%s\n",
                      vshow(it->second).c_str());
    return it->second;
  };
  // A method handle calls what `resolve_method_handle` says, which can depend
  // on the class that holds it.
  MethodHandleRewriter method_handle_rewriter(
      {.handle = [&](const DexMethodHandle* method_handle,
                     const DexMethod* meth) -> std::optional<DexMethodHandle> {
        auto* new_callee =
            get_new_callee(resolve_method_handle(method_handle, meth));
        if (new_callee == nullptr) {
          return std::nullopt;
        }
        DexMethodHandle new_method_handle(method_handle->type(), new_callee);
        always_assert_log(resolve_method_handle(&new_method_handle, meth) ==
                              new_callee,
                          "invalid method handle of %s in %s\n",
                          SHOW(new_callee), SHOW(meth));
        TRACE(REFU, 9, " Updated method handle of %s to %s",
              SHOW(method_handle->methodref()), SHOW(new_callee));
        return new_method_handle;
      }});
  auto patch = [&](DexMethod* meth, IRInstruction* insn) {
    if (insn->has_method()) {
      auto* new_callee = get_new_callee(resolve_method_deprecated(
          insn->get_method(), opcode_to_search(insn), meth));
      if (new_callee != nullptr) {
        TRACE(REFU, 9, " Updated call %s to %s", SHOW(insn), SHOW(new_callee));
        insn->set_method(new_callee);
        if (new_callee->is_virtual()) {
          always_assert_log(opcode::is_invoke_virtual(insn->opcode()),
                            "invalid callsite %s\n",
                            SHOW(insn));
        } else if (is_static(new_callee)) {
          always_assert_log(opcode::is_invoke_static(insn->opcode()),
                            "invalid callsite %s\n",
                            SHOW(insn));
        }
      }
    }
    method_handle_rewriter.rewrite(insn, meth);
  };
  walk::parallel::code(scope, [&](DexMethod* meth, IRCode& code) {
    if (code.cfg_built()) {
      for (auto& mie : cfg::InstructionIterable(code.cfg())) {
        patch(meth, mie.insn);
      }
    } else {
      for (auto& mie : InstructionIterable(code)) {
        patch(meth, mie.insn);
      }
    }
  });
  method_handle_rewriter.rewrite(scope);
}

template <typename T>
CallSites collect_call_refs(const Scope& scope, const T& callees) {
  if (callees.empty()) {
    CallSites empty;
    return empty;
  }
  auto patcher = [&](DexMethod* caller) {
    CallSites call_sites;
    auto* code = caller->get_code();
    if (!code) {
      return call_sites;
    }
    if (code->cfg_built()) {
      auto& cfg = code->cfg();
      for (auto& mie : cfg::InstructionIterable(cfg)) {
        auto* insn = mie.insn;
        if (!insn->has_method()) {
          continue;
        }

        auto* const callee = resolve_method_deprecated(
            insn->get_method(), opcode_to_search(insn), caller);
        if (callee == nullptr || callees.count(callee) == 0) {
          continue;
        }

        call_sites.emplace_back(caller, &mie, insn, callee);
        TRACE(REFU, 9, "  Found call %s from %s", SHOW(insn), SHOW(caller));
      }
    } else {
      for (auto& mie : InstructionIterable(caller->get_code())) {
        auto* insn = mie.insn;
        if (!insn->has_method()) {
          continue;
        }

        auto* const callee = resolve_method_deprecated(
            insn->get_method(), opcode_to_search(insn), caller);
        if (callee == nullptr || callees.count(callee) == 0) {
          continue;
        }

        call_sites.emplace_back(caller, &mie, insn, callee);
        TRACE(REFU, 9, "  Found call %s from %s", SHOW(insn), SHOW(caller));
      }
    }

    return call_sites;
  };

  struct Append {
    void operator()(const CallSites& addend, CallSites* accumulator) {
      accumulator->insert(accumulator->end(), addend.begin(), addend.end());
    }
  };

  CallSites call_sites =
      walk::parallel::methods<CallSites, Append>(scope, patcher);
  return call_sites;
}

using MethodOrderedSet = std::set<DexMethod*, dexmethods_comparator>;
template CallSites collect_call_refs<MethodOrderedSet>(
    const Scope& scope, const MethodOrderedSet& callees);
template CallSites collect_call_refs<UnorderedSet<DexMethod*>>(
    const Scope& scope, const UnorderedSet<DexMethod*>& callees);

int wrap_instance_call_with_static(
    DexStoresVector& stores,
    const UnorderedMap<DexMethod*, DexMethod*>& methods_replacement,
    bool exclude_primary_dex) {
  Scope classes;
  if (!exclude_primary_dex) {
    classes = build_class_scope(stores);
  } else {
    classes = build_class_scope_excluding_primary_dex(stores);
  }
  UnorderedSet<DexType*> excluded_types;
  for (const auto& pair : UnorderedIterable(methods_replacement)) {
    always_assert(!is_static(pair.first));
    always_assert(is_static(pair.second));
    excluded_types.insert(pair.second->get_class());
  }
  std::atomic<uint32_t> total(0);
  // The excluded types are supposed to be wrapper and the only callers of the
  // original methods.
  walk::parallel::methods(classes, [&](DexMethod* method) {
    if (excluded_types.count(method->get_class()) != 0u) {
      return;
    }
    auto* code = method->get_code();
    if (code != nullptr) {
      if (code->cfg_built()) {
        auto& cfg = code->cfg();
        for (auto& mie : cfg::InstructionIterable(cfg)) {
          IRInstruction* insn = mie.insn;
          if (insn->opcode() != OPCODE_INVOKE_VIRTUAL) {
            continue;
          }
          auto* method_ref = insn->get_method();
          auto it =
              methods_replacement.find(dynamic_cast<DexMethod*>(method_ref));
          if (it != methods_replacement.end()) {
            always_assert(is_static(it->second));
            insn->set_opcode(OPCODE_INVOKE_STATIC);
            insn->set_method(it->second);
            ++total;
          }
        }
      } else {
        for (auto& mie : InstructionIterable(code)) {
          IRInstruction* insn = mie.insn;
          if (insn->opcode() != OPCODE_INVOKE_VIRTUAL) {
            continue;
          }
          auto* method_ref = insn->get_method();
          auto it =
              methods_replacement.find(dynamic_cast<DexMethod*>(method_ref));
          if (it != methods_replacement.end()) {
            always_assert(is_static(it->second));
            insn->set_opcode(OPCODE_INVOKE_STATIC);
            insn->set_method(it->second);
            ++total;
          }
        }
      }
    }
  });
  return static_cast<int>(total);
}

} // namespace method_reference
