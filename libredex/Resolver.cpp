/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "Resolver.h"

#include <algorithm>

#include "ClassHierarchy.h"
#include "Debug.h"
#include "DeterministicContainers.h"

#include "Show.h"
#include "TypeUtil.h"

namespace {

inline bool match(const DexString* name,
                  const DexProto* proto,
                  const DexMethod* cls_meth) {
  return name == cls_meth->get_name() && proto == cls_meth->get_proto();
}

void collect_all_intfs_in_hierarchy(
    DexClass* cls, UnorderedSet<const DexType*>* intfs_in_hierarchy) {
  for (const auto* intf : *(cls->get_interfaces())) {
    if (intfs_in_hierarchy->find(intf) == intfs_in_hierarchy->end()) {
      intfs_in_hierarchy->emplace(intf);
      auto* intf_cls = type_class(intf);
      if (intf_cls != nullptr) {
        collect_all_intfs_in_hierarchy(intf_cls, intfs_in_hierarchy);
      }
    }
  }
}

DexMethod* resolve_intf_method_ref(const DexClass* cls,
                                   const DexString* name,
                                   const DexProto* proto) {

  auto find_method = [&](const DexClass* cls) -> DexMethod* {
    const auto& vmethods = cls->get_vmethods();
    for (auto* const vmethod : vmethods) {
      if (vmethod->get_name() == name && vmethod->get_proto() == proto) {
        return vmethod;
      }
    }
    return nullptr;
  };

  auto* method = find_method(cls);
  if (method != nullptr) {
    return method;
  }
  for (const auto& super_intf : *cls->get_interfaces()) {
    const auto& super_intf_cls = type_class(super_intf);
    if (super_intf_cls == nullptr) {
      continue;
    }
    method = resolve_intf_method_ref(super_intf_cls, name, proto);
    if (method != nullptr) {
      return method;
    }
  }
  return nullptr;
}

// Helper method to find the most specific interface method matching
// name and proto in the interface hierarchy of the class or interface `cls`
// including `cls` itself
DexMethod* find_most_specific_interface_method(const DexClass* cls,
                                               const DexString* name,
                                               const DexProto* proto,
                                               bool walk_through_super) {
  for (const auto& vmeth : cls->get_vmethods()) {
    if (match(name, proto, vmeth)) {
      return vmeth;
    }
  }
  // If not found directly in this interface, check parent interfaces
  // We need to collect ALL candidates and find the most specific one
  std::set<DexMethod*, dexmethods_comparator> candidates;
  const auto* cur_cls = cls;
  while (cur_cls != nullptr) {
    std::vector<const DexClass*> intf_queue;
    if (cur_cls->get_interfaces() != nullptr) {
      for (const auto& parent_intf : *cur_cls->get_interfaces()) {
        // Maybe incomplete input dependency will cause issue here
        // double check later
        auto* parent_intf_cls = type_class(parent_intf);
        always_assert_log(parent_intf_cls, "%s has no definition in dex",
                          SHOW(parent_intf));
        intf_queue.push_back(parent_intf_cls);
      }
    }
    while (!intf_queue.empty()) {
      const DexClass* current_intf = intf_queue.back();
      intf_queue.pop_back();
      always_assert(current_intf != nullptr);
      // Check if this interface has a matching method
      bool has_match = false;
      for (const auto& vmeth : current_intf->get_vmethods()) {
        if (match(name, proto, vmeth)) {
          has_match = true;
          candidates.emplace(vmeth);
          break;
        }
      }
      if (!has_match) {
        // We didn't find match in this interface, add parent interfaces to
        // queue
        if (current_intf->get_interfaces() != nullptr) {
          for (const auto& parent_intf : *current_intf->get_interfaces()) {
            auto* intf_cls = type_class(parent_intf);
            always_assert_log(intf_cls, "%s has no definition in dex",
                              SHOW(parent_intf));
            intf_queue.push_back(intf_cls);
          }
        }
      }
    }
    if (!walk_through_super) {
      break;
    }
    // Keep walking up the class hierarchy to collect all interface methods
    cur_cls = type_class(cur_cls->get_super_class());
  }

  if (candidates.empty()) {
    return nullptr;
  }

  if (candidates.size() == 1) {
    return *candidates.begin();
  }

  // Find the most specific interface method
  UnorderedSet<const DexType*> super_intfs;
  for (auto* candidate : UnorderedIterable(candidates)) {
    // Collect all intfs that are extended by candidate
    auto* candidate_cls = type_class(candidate->get_class());
    always_assert_log(candidate_cls != nullptr, "%s is not defined in dex",
                      SHOW(candidate));
    collect_all_intfs_in_hierarchy(candidate_cls, &super_intfs);
  }

  std::vector<DexMethod*> filtered_candidates;
  for (auto* candidate : candidates) {
    // If candidate is one of super_intfs's method, it means it will get
    // overridden by a more specific interface method
    if (super_intfs.find(candidate->get_class()) == super_intfs.end()) {
      filtered_candidates.emplace_back(candidate);
    }
  }
  bool has_default_intf = false;
  for (auto* candidate : filtered_candidates) {
    if (!is_abstract(candidate)) {
      has_default_intf = true;
      break;
    }
  }
  if (!has_default_intf) {
    // If all candidates are abstract, we will just pick the first one
    always_assert_log(!filtered_candidates.empty(),
                      "filtered_candidates is empty for %s", SHOW(cls));
    return filtered_candidates[0];
  }

  always_assert_log(filtered_candidates.size() == 1,
                    "Interface hierarchy of %s has more than one most specific "
                    "interface method for %s.%s",
                    SHOW(cls), SHOW(name), SHOW(proto));
  return filtered_candidates[0];
}

DexMethod* resolve_method_impl(const DexClass* cls,
                               const DexString* name,
                               const DexProto* proto,
                               MethodSearch search,
                               const DexMethod* caller,
                               bool default_interface_switch) {
  if (default_interface_switch && search == MethodSearch::InterfaceVirtual) {
    // MethodSearch::InterfaceVirtual is special handling for miranda
    // methods in dex35 context, with default interface methods, we
    // will unify miranda method handling with default interface method
    search = MethodSearch::Virtual;
  }
  if (search == MethodSearch::Interface) {
    if (cls != nullptr) {
      if (!is_interface(cls)) {
        // Interface method resolution fails (JVMS 5.4.3.4). The verifier
        // accepts such an invoke-interface, e.g. in code compiled against an
        // older library; the runtime throws only when the instruction runs.
        return nullptr;
      }
      return resolve_intf_method_ref(cls, name, proto);
    }
  }
  if (search == MethodSearch::Super) {
    always_assert(cls != nullptr);
    if (default_interface_switch) {
      // Check if the method reference is to an interface
      // For super calls to interface default methods, resolve from the
      // interface
      if (is_interface(cls)) {
        auto* mdef = find_most_specific_interface_method(
            cls, name, proto, false /* walk_through_super */);
        if (mdef != nullptr) {
          always_assert_log(!is_abstract(mdef),
                            "invoke-super on a non-default interface method %s",
                            SHOW(mdef));
        }
        return mdef;
      }
    }
    if (caller != nullptr) {
      // caller must be provided. This condition is here to be compatible with
      // old behavior.
      const DexType* containing_type = caller->get_class();
      DexClass* containing_class = type_class(containing_type);
      if (containing_class == nullptr) {
        return nullptr;
      }
      const DexType* super_class = containing_class->get_super_class();
      if (super_class == nullptr) {
        return nullptr;
      }
      cls = type_class(super_class);
    }
    // The rest is the same as virtual.
    search = MethodSearch::Virtual;
  }

  // Save the original class to check interfaces later if needed
  const DexClass* original_cls = cls;

  while (cls != nullptr) {
    if (search == MethodSearch::InterfaceVirtual) {
      auto* try_intf = resolve_intf_method_ref(cls, name, proto);
      if (try_intf != nullptr) {
        return try_intf;
      }
    }
    if (search == MethodSearch::Virtual || search == MethodSearch::Any) {
      for (const auto& vmeth : cls->get_vmethods()) {
        if (match(name, proto, vmeth)) {
          return vmeth;
        }
      }
    }
    if (search == MethodSearch::Direct || search == MethodSearch::Static ||
        search == MethodSearch::Any) {
      for (const auto& dmeth : cls->get_dmethods()) {
        if (match(name, proto, dmeth)) {
          return dmeth;
        }
      }
    }
    // direct methods only look up the given class
    cls = search != MethodSearch::Direct ? type_class(cls->get_super_class())
                                         : nullptr;
  }

  // For Virtual search (including Super converted to Virtual), if not found in
  // class hierarchy, check interfaces for default methods when
  // default_interface_switch is enabled
  if (default_interface_switch && search == MethodSearch::Virtual &&
      original_cls != nullptr) {
    // Search through all interfaces in the class hierarchy for default methods
    // We need to walk up the class hierarchy and collect all interface methods
    return find_most_specific_interface_method(original_cls, name, proto,
                                               true /* walk_through_super */);
  }

  return nullptr;
}

DexMethod* resolve_method_impl(DexMethodRef* method,
                               MethodSearch search,
                               const DexMethod* caller,
                               bool default_interface_switch) {
  if (search == MethodSearch::Super) {
    if (caller != nullptr) {
      auto* cls = type_class(method->get_class());
      if (cls == nullptr) {
        return nullptr;
      }
      return default_interface_switch
                 ? resolve_super(cls, method->get_name(), method->get_proto(),
                                 caller)
                 : resolve_super_deprecated(cls, method->get_name(),
                                            method->get_proto(), caller);
    }
    // According to the JLS and Dalvik bytecode spec, a ::Super search requires
    // knowing the "current class" (of the caller). However, when we get here,
    // we don't have that. So, as a best effort, we are effectively going to do
    // a ::Virtual search starting from the super class.
    // TODO T132919742: Rewrite all callsites of resolve_method(..., ::Super::,
    // ) to always provide the "current class" (given by a caller).
    search = MethodSearch::Virtual;
  }

  auto* m = method->as_def();
  if (m != nullptr) {
    return m;
  }
  auto* cls = type_class(method->get_class());
  if (cls == nullptr) {
    return nullptr;
  }
  return resolve_method_impl(cls, method->get_name(), method->get_proto(),
                             search, nullptr /*caller=*/,
                             default_interface_switch);
}

DexMethod* resolve_method_impl(DexMethodRef* method,
                               MethodSearch search,
                               MethodRefCache& ref_cache,
                               const DexMethod* caller,
                               bool default_interface_switch) {
  if (search == MethodSearch::Super) {
    // We don't have cache for that since caller might be different.
    return resolve_method_impl(method, search, caller,
                               default_interface_switch);
  }
  auto* m = method->as_def();
  if (m != nullptr) {
    return m;
  }
  auto def = ref_cache.find(MethodRefCacheKey{method, search});
  if (def != ref_cache.end()) {
    return def->second;
  }
  auto* mdef =
      resolve_method_impl(method, search, caller, default_interface_switch);
  if (mdef != nullptr) {
    ref_cache.emplace(MethodRefCacheKey{method, search}, mdef);
  }
  return mdef;
}

DexMethod* resolve_method_impl(DexMethodRef* method,
                               MethodSearch search,
                               ConcurrentMethodRefCache& concurrent_ref_cache,
                               const DexMethod* caller,
                               bool default_interface_switch) {
  if (search == MethodSearch::Super) {
    // We don't have cache for that since caller might be different.
    return resolve_method_impl(method, search, caller,
                               default_interface_switch);
  }
  auto* m = method->as_def();
  if (m != nullptr) {
    return m;
  }
  const auto* res = concurrent_ref_cache.get(MethodRefCacheKey{method, search});
  if (res != nullptr) {
    return *res;
  }
  auto* mdef =
      resolve_method_impl(method, search, caller, default_interface_switch);
  if (mdef != nullptr) {
    concurrent_ref_cache.emplace(MethodRefCacheKey{method, search}, mdef);
  }
  return mdef;
}

DexMethod* resolve_invoke_method_impl(IROpcode opcode,
                                      DexMethodRef* callee_ref,
                                      const DexMethod* caller,
                                      bool* resolved_virtual_to_interface,
                                      bool default_interface_switch) {
  auto search = opcode_to_search(opcode);
  auto* callee =
      resolve_method_impl(callee_ref, search, caller, default_interface_switch);
  if (!default_interface_switch && (callee == nullptr) &&
      search == MethodSearch::Virtual) {
    // For new API we will handle miranda methods in virtual search
    callee = resolve_method_impl(callee_ref, MethodSearch::InterfaceVirtual,
                                 caller, default_interface_switch);
  }
  if (resolved_virtual_to_interface != nullptr) {
    *resolved_virtual_to_interface = false;
    if (search == MethodSearch::Virtual && callee != nullptr) {
      auto* callee_cls = type_class(callee->get_class());
      always_assert_log(callee_cls != nullptr,
                        "Resolved method %s has undefined class", SHOW(callee));
      *resolved_virtual_to_interface = is_interface(callee_cls);
    }
  }
  return callee;
}

DexMethod* resolve_invoke_method_impl(const IRInstruction* insn,
                                      MethodRefCache& ref_cache,
                                      const DexMethod* caller,
                                      bool* resolved_virtual_to_interface,
                                      bool default_interface_switch) {
  auto* callee_ref = insn->get_method();
  auto search = opcode_to_search(insn);
  auto* callee = resolve_method_impl(callee_ref, search, ref_cache, caller,
                                     default_interface_switch);
  if (!default_interface_switch && (callee == nullptr) &&
      search == MethodSearch::Virtual) {
    // For new API we will handle miranda methods in virtual search
    callee = resolve_method_impl(callee_ref, MethodSearch::InterfaceVirtual,
                                 ref_cache, caller, default_interface_switch);
  }
  if (resolved_virtual_to_interface != nullptr) {
    *resolved_virtual_to_interface = false;
    if (search == MethodSearch::Virtual && callee != nullptr) {
      auto* callee_cls = type_class(callee->get_class());
      always_assert_log(callee_cls != nullptr,
                        "Resolved method %s has undefined class", SHOW(callee));
      *resolved_virtual_to_interface = is_interface(callee_cls);
    }
  }
  return callee;
}

} // namespace

DexMethod* resolve_invoke_method_deprecated(
    const IRInstruction* insn,
    MethodRefCache& ref_cache,
    const DexMethod* caller,
    bool* resolved_virtual_to_interface) {
  return resolve_invoke_method_impl(insn, ref_cache, caller,
                                    resolved_virtual_to_interface, false);
}

DexMethod* resolve_invoke_method(const IRInstruction* insn,
                                 MethodRefCache& ref_cache,
                                 const DexMethod* caller,
                                 bool* resolved_virtual_to_interface) {
  return resolve_invoke_method_impl(insn, ref_cache, caller,
                                    resolved_virtual_to_interface, true);
}

DexMethod* resolve_method_deprecated(
    DexMethodRef* method,
    MethodSearch search,
    ConcurrentMethodRefCache& concurrent_ref_cache,
    const DexMethod* caller) {
  return resolve_method_impl(method, search, concurrent_ref_cache, caller,
                             false);
}

DexMethod* resolve_method(DexMethodRef* method,
                          MethodSearch search,
                          ConcurrentMethodRefCache& concurrent_ref_cache,
                          const DexMethod* caller) {
  return resolve_method_impl(method, search, concurrent_ref_cache, caller,
                             true);
}

DexMethod* resolve_method_deprecated(DexMethodRef* method,
                                     MethodSearch search,
                                     MethodRefCache& ref_cache,
                                     const DexMethod* caller) {
  return resolve_method_impl(method, search, ref_cache, caller, false);
}

DexMethod* resolve_method(DexMethodRef* method,
                          MethodSearch search,
                          MethodRefCache& ref_cache,
                          const DexMethod* caller) {
  return resolve_method_impl(method, search, ref_cache, caller, true);
}

DexMethod* resolve_method_deprecated(DexMethodRef* method,
                                     MethodSearch search,
                                     const DexMethod* caller) {
  return resolve_method_impl(method, search, caller, false);
}
DexMethod* resolve_method(DexMethodRef* method,
                          MethodSearch search,
                          const DexMethod* caller) {
  return resolve_method_impl(method, search, caller, true);
}

DexMethod* resolve_method_deprecated(const DexClass* cls,
                                     const DexString* name,
                                     const DexProto* proto,
                                     MethodSearch search,
                                     const DexMethod* caller) {
  return resolve_method_impl(cls, name, proto, search, caller, false);
}

DexMethod* resolve_method(const DexClass* cls,
                          const DexString* name,
                          const DexProto* proto,
                          MethodSearch search,
                          const DexMethod* caller) {
  return resolve_method_impl(cls, name, proto, search, caller, true);
}

DexMethod* resolve_invoke_method_deprecated(
    const IRInstruction* insn,
    const DexMethod* caller,
    bool* resolved_virtual_to_interface) {
  return resolve_invoke_method_impl(insn->opcode(), insn->get_method(), caller,
                                    resolved_virtual_to_interface, false);
}

DexMethod* resolve_invoke_method_deprecated(
    IROpcode opcode,
    DexMethodRef* callee_ref,
    const DexMethod* caller,
    bool* resolved_virtual_to_interface) {
  return resolve_invoke_method_impl(opcode, callee_ref, caller,
                                    resolved_virtual_to_interface, false);
}

DexMethod* resolve_invoke_method(const IRInstruction* insn,
                                 const DexMethod* caller,
                                 bool* resolved_virtual_to_interface) {
  return resolve_invoke_method_impl(insn->opcode(), insn->get_method(), caller,
                                    resolved_virtual_to_interface, true);
}

namespace {

// What ART versions run for an invoke-direct handle of `method_ref`, a method
// that is not private, held by code in `caller`.
struct NonvirtualHandleTargets {
  // The implementation in the caller's class, which Android 9 runs. Android 10
  // and later run it too when the named class declares it.
  DexMethod* caller_impl{nullptr};
  // The implementation in the named class's superclass, which Android 10 and
  // later run when the named class does not declare `caller_impl`.
  DexMethod* named_super_impl{nullptr};
  // Whether all versions run `caller_impl`.
  bool agree{false};
  // Every method that some version may run. Where a package-private method
  // may make the method in the slot differ from the one that a search by
  // name and prototype finds, these are all the candidates, and the other
  // fields stay empty.
  std::vector<DexMethod*> callees;
};

// Appends to `methods` the virtual methods named `name` with `proto` that
// `cls` and its superclasses declare, each once.
void append_declared_vmethods(const DexClass* cls,
                              const DexString* name,
                              const DexProto* proto,
                              std::vector<DexMethod*>& methods) {
  for (; cls != nullptr; cls = type_class(cls->get_super_class())) {
    auto* method = DexMethod::get_method(cls->get_type(), name, proto);
    if (method == nullptr || !method->is_def()) {
      continue;
    }
    auto* def = method->as_def();
    if (def->is_virtual() &&
        std::find(methods.begin(), methods.end(), def) == methods.end()) {
      methods.push_back(def);
    }
  }
}

// Whether the vtable slot that holds one of `methods`, which share a name and
// prototype, may hold a method other than the one that a search by name and
// prototype finds. A method takes over the slot of a superclass's method only
// if it can access that method, and it can access a package-private method
// only from the same runtime package: the same package name and class loader.
// An internal and an external class are taken to have different loaders.
bool slots_may_differ_from_names(const std::vector<DexMethod*>& methods) {
  if (std::none_of(methods.begin(), methods.end(),
                   [](const DexMethod* m) { return is_package_private(m); })) {
    return false;
  }
  const auto* first = methods.front();
  return std::any_of(methods.begin(), methods.end(), [&](const DexMethod* m) {
    return !type::same_package(m->get_class(), first->get_class()) ||
           m->is_external() != first->is_external();
  });
}

NonvirtualHandleTargets resolve_nonvirtual_handle_targets(
    DexMethodRef* method_ref, const DexMethod* caller) {
  NonvirtualHandleTargets targets;
  const auto* named_cls = type_class(method_ref->get_class());
  const auto* caller_cls =
      caller == nullptr ? nullptr : type_class(caller->get_class());
  // ART finds an interface's method among the interface's methods, whose
  // indices are not vtable indices, so the vtable entry it then takes from
  // the caller's class is not known to belong to the method.
  if (named_cls == nullptr || is_interface(named_cls) ||
      caller_cls == nullptr) {
    return targets;
  }
  const auto* name = method_ref->get_name();
  const auto* proto = method_ref->get_proto();
  auto* named = resolve_method_deprecated(named_cls, name, proto);
  if (named == nullptr || !named->is_virtual()) {
    return targets;
  }
  // ART takes the entry at the vtable index of `named` in the caller's class,
  // which is the caller's implementation of the method only when the caller's
  // class inherits `named`.
  const auto* cls = caller_cls;
  while (cls != nullptr && cls->get_type() != named->get_class()) {
    cls = type_class(cls->get_super_class());
  }
  if (cls == nullptr) {
    return targets;
  }
  const auto* named_super_cls = type_class(named_cls->get_super_class());
  std::vector<DexMethod*> candidates;
  append_declared_vmethods(caller_cls, name, proto, candidates);
  append_declared_vmethods(named_super_cls, name, proto, candidates);
  if (slots_may_differ_from_names(candidates)) {
    targets.callees = std::move(candidates);
    return targets;
  }
  targets.caller_impl =
      resolve_method_deprecated(caller_cls, name, proto, MethodSearch::Virtual);
  if (named_super_cls != nullptr) {
    targets.named_super_impl = resolve_method_deprecated(
        named_super_cls, name, proto, MethodSearch::Virtual);
  }
  targets.agree = targets.caller_impl != nullptr &&
                  (targets.caller_impl->get_class() == named_cls->get_type() ||
                   targets.caller_impl == targets.named_super_impl);
  if (targets.agree) {
    targets.callees = {targets.caller_impl};
    return targets;
  }
  for (auto* target : {targets.caller_impl, targets.named_super_impl}) {
    if (target != nullptr &&
        std::find(targets.callees.begin(), targets.callees.end(), target) ==
            targets.callees.end()) {
      targets.callees.push_back(target);
    }
  }
  return targets;
}

} // namespace

DexMethod* resolve_method_handle(const DexMethodHandle* method_handle,
                                 const DexMethod* caller) {
  auto opcode = method_handle_opcode(method_handle);
  if (!opcode::is_a_method_invoke(opcode)) {
    return nullptr;
  }
  auto* method_ref = method_handle->methodref();
  if (opcode == OPCODE_INVOKE_INTERFACE || opcode == OPCODE_INVOKE_VIRTUAL) {
    // ART throws IncompatibleClassChangeError when it resolves a handle whose
    // kind disagrees with whether the named class is an interface.
    const auto* cls = type_class(method_ref->get_class());
    if (cls != nullptr &&
        is_interface(cls) != (opcode == OPCODE_INVOKE_INTERFACE)) {
      return nullptr;
    }
  }
  if (opcode == OPCODE_INVOKE_SUPER) {
    auto targets = resolve_nonvirtual_handle_targets(method_ref, caller);
    return targets.agree ? targets.caller_impl : nullptr;
  }
  return resolve_invoke_method_deprecated(opcode, method_ref, caller);
}

std::vector<DexMethod*> resolve_method_handle_callees(
    const DexMethodHandle* method_handle, const DexMethod* caller) {
  auto* callee = resolve_method_handle(method_handle, caller);
  if (callee != nullptr) {
    return {callee};
  }
  if (method_handle_opcode(method_handle) != OPCODE_INVOKE_SUPER) {
    return {};
  }
  return resolve_nonvirtual_handle_targets(method_handle->methodref(), caller)
      .callees;
}

DexMethod* resolve_call(MethodSearch search,
                        DexMethodRef* method_ref,
                        const DexMethodHandle* method_handle,
                        const DexMethod* caller) {
  if (method_handle == nullptr) {
    return resolve_method_deprecated(method_ref, search, caller);
  }
  if (method_handle_opcode(method_handle) == OPCODE_INVOKE_SUPER) {
    // ART finds the named method before it takes the caller's implementation.
    return resolve_method_deprecated(method_handle->methodref(),
                                     MethodSearch::Virtual);
  }
  return resolve_method_handle(method_handle, caller);
}

DexField* resolve_field_handle(const DexMethodHandle* method_handle) {
  auto type = method_handle->type();
  if (DexMethodHandle::isInvokeType(type)) {
    return nullptr;
  }
  const auto* field_ref = method_handle->fieldref();
  bool is_static = type == METHOD_HANDLE_TYPE_STATIC_GET ||
                   type == METHOD_HANDLE_TYPE_STATIC_PUT;
  return resolve_field(field_ref->get_class(), field_ref->get_name(),
                       field_ref->get_type(),
                       is_static ? FieldSearch::Static : FieldSearch::Instance);
}

DexField* resolve_field(const DexType* owner,
                        const DexString* name,
                        const DexType* type,
                        FieldSearch fs) {
  auto field_eq = [&](const DexField* a) {
    return a->get_name() == name && a->get_type() == type;
  };

  const DexClass* cls = type_class(owner);
  while (cls != nullptr) {
    if (fs == FieldSearch::Instance || fs == FieldSearch::Any) {
      for (auto* ifield : cls->get_ifields()) {
        if (field_eq(ifield)) {
          return ifield;
        }
      }
    }
    if (fs == FieldSearch::Static || fs == FieldSearch::Any) {
      for (auto* sfield : cls->get_sfields()) {
        if (field_eq(sfield)) {
          return sfield;
        }
      }
      // static final fields may be coming from interfaces so we
      // have to walk up the interface hierarchy too
      for (const auto& intf : *cls->get_interfaces()) {
        auto* field = resolve_field(intf, name, type, fs);
        if (field != nullptr) {
          return field;
        }
      }
    }
    cls = type_class(cls->get_super_class());
  }
  return nullptr;
}

bool is_external_call(const DexMethodRef* ref, const DexMethod* resolved) {
  return resolved != nullptr ? resolved->is_external()
                             : type_class_internal(ref->get_class()) == nullptr;
}

DexMethod* find_top_impl(const DexClass* cls,
                         const DexString* name,
                         const DexProto* proto) {
  DexMethod* top_impl = nullptr;
  while (cls != nullptr) {
    for (const auto& vmeth : cls->get_vmethods()) {
      if (match(name, proto, vmeth)) {
        top_impl = vmeth;
      }
    }
    cls = type_class(cls->get_super_class());
  }
  return top_impl;
}

DexMethod* find_top_intf_impl(const DexClass* cls,
                              const DexString* name,
                              const DexProto* proto) {
  DexMethod* top_impl = nullptr;
  while (cls != nullptr) {
    DexMethod* top_mir_impl = resolve_intf_method_ref(cls, name, proto);
    if (top_mir_impl != nullptr) {
      top_impl = top_mir_impl;
    }
    cls = type_class(cls->get_super_class());
  }
  return top_impl;
}

bool has_signature_collision(const SubtypeMaps& subtype_maps,
                             const DexMethod* method,
                             const DexProto* new_proto) {
  const auto* name = method->get_name();
  const auto* type = method->get_class();
  if (DexMethod::get_method(type, name, new_proto) != nullptr) {
    return true;
  }
  if (!method->is_virtual()) {
    // Static and private methods and constructors are neither inherited nor
    // overridden, and references to them are resolved to their definitions.
    return false;
  }
  TypeSet subtypes;
  if (is_interface(type_class(type))) {
    subtypes = get_all_implementors(subtype_maps.implementors, type);
    get_all_children(subtype_maps.subinterfaces, type, subtypes);
  } else {
    get_all_children(subtype_maps.subclasses, type, subtypes);
  }
  subtypes.insert(type);
  // MethodSearch::Virtual would also find interface methods, but its search for
  // default methods asserts on interfaces without a definition, which inputs
  // can have.
  const auto inherits = [&](const DexClass* cls) {
    if (resolve_method(cls, name, new_proto) != nullptr) {
      return true;
    }
    for (; cls != nullptr; cls = type_class(cls->get_super_class())) {
      for (const auto* intf : *cls->get_interfaces()) {
        const auto* intf_cls = type_class(intf);
        if (intf_cls != nullptr &&
            resolve_method(intf_cls, name, new_proto,
                           MethodSearch::Interface) != nullptr) {
          return true;
        }
      }
    }
    return false;
  };
  return std::any_of(
      subtypes.begin(), subtypes.end(),
      [&](const DexType* subtype) { return inherits(type_class(subtype)); });
}
