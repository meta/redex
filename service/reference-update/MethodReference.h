/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <optional>

#include "DexClass.h"
#include "DexStore.h"
#include "IRInstruction.h"

struct MethodItemEntry;

using OrderedMethodSet = std::set<DexMethod*, dexmethods_comparator>;

namespace method_reference {

// A callsite instruction in caller. mie should always contain an IRInstruction.
struct CallSite {
  DexMethod* caller;
  MethodItemEntry* mie; // Note: this will be removed once cfg is fully
                        // updated.
  IRInstruction* insn;
  DexMethod* callee;
  CallSite(DexMethod* caller,
           MethodItemEntry* mie,
           IRInstruction* insn,
           DexMethod* callee)
      : caller(caller), mie(mie), insn(insn), callee(callee) {}
};

using CallSites = std::vector<CallSite>;

// A new callee method and optional additional args.
// One example would be passing the type tag in type erased code.
struct NewCallee {
  DexMethod* method;
  std::optional<std::vector<uint32_t>> additional_args = std::nullopt;

  explicit NewCallee(DexMethod* method) : method(method) {}
  NewCallee(DexMethod* method, std::optional<uint32_t> arg) : method(method) {
    if (arg == std::nullopt) {
      return;
    }
    std::vector<uint32_t> args;
    args.push_back(*arg);
    additional_args = std::optional<std::vector<uint32_t>>(args);
  }
  NewCallee(DexMethod* method, std::vector<uint32_t>& args) : method(method) {
    additional_args = std::optional<std::vector<uint32_t>>(args);
  }
};

IRInstruction* make_load_const(reg_t dest, size_t val);

IRInstruction* make_invoke(DexMethod* callee,
                           IROpcode opcode,
                           const std::vector<reg_t>& args);

/**
 * A callsite consists of a caller, a callee and the instruction.
 * A new_callee consists of a new callee method and additional args.
 * Update the callsite with the new_callee.
 */
void patch_callsite(const CallSite& callsite, const NewCallee& new_callee);

/**
 * Makes every invoke and method handle in `scope` that calls a key of
 * `old_to_new_callee` call its value instead.
 */
void update_call_refs_simple(
    const Scope& scope,
    const UnorderedMap<DexMethod*, DexMethod*>& old_to_new_callee);

// Allowed types: * std::set<DexMethod*, dexmethods_comparator>
//                * std::UnorderedSet<DexMethod*>
template <typename T>
CallSites collect_call_refs(const Scope& scope, const T& callees);

/**
 * Replace instance method call with static method call.
 * obj.instance_method(arg1, ...) => XX.static_method(obj, arg1, ...)
 */
int wrap_instance_call_with_static(
    DexStoresVector& stores,
    const UnorderedMap<DexMethod*, DexMethod*>& methods_replacement,
    bool exclude_primary_dex = false);
} // namespace method_reference
