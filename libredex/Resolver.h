/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <boost/functional/hash.hpp>
#include <type_traits>

#include "ConcurrentContainers.h"
#include "DeterministicContainers.h"
#include "DexCallSite.h"
#include "DexClass.h"
#include "DexMethodHandle.h"
#include "IRInstruction.h"
#include "Show.h"

struct SubtypeMaps;

/**
 * Type of search to perform.
 * These flags direct the way lookup if performed up the hierarchy more than
 * the type of method to resolve.
 * Specifically, Direct and Static both look into the dmethods list, however
 * Static searches up the hierarchy whereas Direct only searches into the given
 * class.
 * In a sense they roughly match the opcode and the Dalvik resolution
 * semantic rather than the type of methods.
 */
enum class MethodSearch {
  Direct, // invoke-direct: private and init methods in class only
  Static, // invoke-static: dmethods in class and up the hierarchy
  Virtual, // invoke-virtual: vmethods in class and up the hierarchy
  Super, // invoke-super: vmethods up the hierarchy
  Any, // any method (vmethods or dmethods) in class and up the hierarchy
       // but not interfaces
  Interface, // invoke-interface: vmethods in interface class graph
  InterfaceVirtual // invoke-virtual but the final resolved method is interface
                   // method. Fallback to interface search when virtual search
                   // failed.
                   // This is added because we don't have Miranda methods in
                   // Redex but this case exists:
                   // Interface a { something(); }
                   // class b implements a {}
                   // class c extends b { something(){} }
                   // ... invoke-virtual b.something() ...
                   // MethodSearch::Virtual will return nullptr. So we added
                   // MethodSearch::InterfaceVirtual that can resolve to
                   // a.something()
};

struct MethodRefCacheKey {
  DexMethodRef* method;
  MethodSearch search;

  bool operator==(const MethodRefCacheKey& other) const {
    return method == other.method && search == other.search;
  }
};

struct MethodRefCacheKeyHash {
  std::size_t operator()(const MethodRefCacheKey& key) const {
    std::size_t seed = 0;
    boost::hash_combine(seed, key.method);
    boost::hash_combine(
        seed, static_cast<std::underlying_type_t<MethodSearch>>(key.search));
    return seed;
  }
};

using MethodRefCache =
    UnorderedMap<MethodRefCacheKey, DexMethod*, MethodRefCacheKeyHash>;

using ConcurrentMethodRefCache = InsertOnlyConcurrentMap<MethodRefCacheKey,
                                                         DexMethod*,
                                                         MethodRefCacheKeyHash>;

/**
 * Helper to map an opcode to a MethodSearch rule.
 */
inline MethodSearch opcode_to_search(const IROpcode opcode) {
  always_assert(opcode::is_a_method_invoke(opcode));
  switch (opcode) {
  case OPCODE_INVOKE_DIRECT:
    return MethodSearch::Direct;
  case OPCODE_INVOKE_STATIC:
    return MethodSearch::Static;
  case OPCODE_INVOKE_VIRTUAL:
    return MethodSearch::Virtual;
  case OPCODE_INVOKE_SUPER:
    return MethodSearch::Super;
  case OPCODE_INVOKE_INTERFACE:
    return MethodSearch::Interface;
  default:
    return MethodSearch::Any;
  }
}

/**
 * Helper to map an opcode to a MethodSearch rule.
 */
inline MethodSearch opcode_to_search(const IRInstruction* insn) {
  return opcode_to_search(insn->opcode());
}

/**
 * The instruction that calling `method_handle` acts like: the invoke it
 * performs, or the field get or put (`OPCODE_SGET`, `OPCODE_SPUT`,
 * `OPCODE_IGET` or `OPCODE_IPUT`). An invoke-direct handle of a method that
 * is not private is `OPCODE_INVOKE_SUPER`, the kind ART gives it: its call does
 * not dispatch virtually, and what it runs depends on the class of the code
 * that holds it, though not the way an invoke-super's target does (see
 * `resolve_method_handle`).
 */
inline IROpcode method_handle_opcode(const DexMethodHandle* method_handle) {
  switch (method_handle->type()) {
  case METHOD_HANDLE_TYPE_STATIC_PUT:
    return OPCODE_SPUT;
  case METHOD_HANDLE_TYPE_STATIC_GET:
    return OPCODE_SGET;
  case METHOD_HANDLE_TYPE_INSTANCE_PUT:
    return OPCODE_IPUT;
  case METHOD_HANDLE_TYPE_INSTANCE_GET:
    return OPCODE_IGET;
  case METHOD_HANDLE_TYPE_INVOKE_STATIC:
    return OPCODE_INVOKE_STATIC;
  case METHOD_HANDLE_TYPE_INVOKE_INSTANCE:
    return OPCODE_INVOKE_VIRTUAL;
  case METHOD_HANDLE_TYPE_INVOKE_CONSTRUCTOR:
    return OPCODE_INVOKE_DIRECT;
  case METHOD_HANDLE_TYPE_INVOKE_DIRECT: {
    const auto* target = method_handle->methodref()->as_def();
    return (target != nullptr && is_private(target)) ? OPCODE_INVOKE_DIRECT
                                                     : OPCODE_INVOKE_SUPER;
  }
  case METHOD_HANDLE_TYPE_INVOKE_INTERFACE:
    return OPCODE_INVOKE_INTERFACE;
  }
  // DexIdx rejects any other type when it reads a method handle.
  not_reached_log("Unknown MethodHandleType %d", method_handle->type());
}

/**
 * Calls `f(handle)` for every method handle that `insn` holds: the one that
 * const-method-handle loads, and those among the bootstrap method and
 * arguments of a call site.
 */
template <typename Fn>
void for_each_method_handle(const IRInstruction* insn, Fn&& f) {
  if (insn->has_methodhandle()) {
    f(insn->get_methodhandle());
  } else if (insn->has_callsite()) {
    std::vector<DexMethodHandle*> method_handles;
    insn->get_callsite()->gather_methodhandles(method_handles);
    for (const auto* method_handle : method_handles) {
      f(method_handle);
    }
  }
}

/**
 * Calls `f(opcode, method_ref, method_handle)` for every call that `insn`
 * makes: its own if it is an invoke, with a null `method_handle`, and the call
 * that each method handle it holds makes. `opcode` is the invoke whose rules
 * the call follows; `resolve_method_handle` gives the method that a handle's
 * call runs.
 */
template <typename Fn>
void for_each_invoke(const IRInstruction* insn, Fn&& f) {
  if (opcode::is_a_method_invoke(insn->opcode())) {
    f(insn->opcode(), insn->get_method(),
      static_cast<const DexMethodHandle*>(nullptr));
  }
  for_each_method_handle(insn, [&](const DexMethodHandle* method_handle) {
    auto opcode = method_handle_opcode(method_handle);
    if (opcode::is_a_method_invoke(opcode)) {
      f(opcode, method_handle->methodref(), method_handle);
    }
  });
}

/**
 * Whether what `insn` does depends on the class of the method that holds it,
 * beyond access checks, so that moving it to a method of another class can
 * change what it does: a call that resolves like invoke-super, by the
 * instruction or a method handle it holds, whose target ART finds from that
 * class, or an `invoke-custom`, whose bootstrap method receives a
 * `MethodHandles.Lookup` in that class.
 */
inline bool depends_on_holder_class(const IRInstruction* insn) {
  if (opcode::is_invoke_custom(insn->opcode())) {
    return true;
  }
  bool result = false;
  for_each_invoke(insn, [&](IROpcode opcode, DexMethodRef* /* method_ref */,
                            const DexMethodHandle* /* method_handle */) {
    result = result || opcode == OPCODE_INVOKE_SUPER;
  });
  return result;
}

/**
 * Calls `f(opcode, field_ref, method_handle)` for every field that `insn` reads
 * or writes: its own if it is a field instruction, with a null
 * `method_handle`, and the field that each method handle it holds gets or
 * puts. `opcode` is the field instruction whose rules the access follows.
 */
template <typename Fn>
void for_each_field_access(const IRInstruction* insn, Fn&& f) {
  if (insn->has_field()) {
    f(insn->opcode(), insn->get_field(),
      static_cast<const DexMethodHandle*>(nullptr));
  }
  for_each_method_handle(insn, [&](const DexMethodHandle* method_handle) {
    auto opcode = method_handle_opcode(method_handle);
    if (!opcode::is_a_method_invoke(opcode)) {
      f(opcode, method_handle->fieldref(), method_handle);
    }
  });
}

/**
 * Given a scope defined by DexClass, a name and a proto look for a method
 * definition in scope.
 * The lookup is performed according to the search rules specified via
 * MethodSearch.
 */
DexMethod* resolve_method_deprecated(const DexClass*,
                                     const DexString*,
                                     const DexProto*,
                                     MethodSearch search = MethodSearch::Any,
                                     const DexMethod* caller = nullptr);

DexMethod* resolve_method(const DexClass*,
                          const DexString*,
                          const DexProto*,
                          MethodSearch search = MethodSearch::Any,
                          const DexMethod* caller = nullptr);

/**
 * Given a scope defined by DexClass, a name and a proto look for a vmethod
 * definition in scope.
 */
inline DexMethod* resolve_virtual_deprecated(const DexClass* cls,
                                             const DexString* name,
                                             const DexProto* proto) {
  return resolve_method_deprecated(cls, name, proto, MethodSearch::Virtual);
}

inline DexMethod* resolve_virtual(const DexClass* cls,
                                  const DexString* name,
                                  const DexProto* proto) {
  return resolve_method(cls, name, proto, MethodSearch::Virtual);
}

/**
 * Given a scope defined by DexClass, a name and a proto look for a vmethod
 * definition in scope.
 */
inline DexMethod* resolve_super_deprecated(const DexClass* cls,
                                           const DexString* name,
                                           const DexProto* proto,
                                           const DexMethod* caller) {
  return resolve_method_deprecated(cls, name, proto, MethodSearch::Super,
                                   caller);
}

inline DexMethod* resolve_super(const DexClass* cls,
                                const DexString* name,
                                const DexProto* proto,
                                const DexMethod* caller) {
  return resolve_method(cls, name, proto, MethodSearch::Super, caller);
}

/**
 * Given a scope defined by DexClass, a name and a proto look for a dmethod
 * definition in class only.
 */
inline DexMethod* resolve_direct_deprecated(const DexClass* cls,
                                            const DexString* name,
                                            const DexProto* proto) {
  return resolve_method_deprecated(cls, name, proto, MethodSearch::Direct);
}

inline DexMethod* resolve_direct(const DexClass* cls,
                                 const DexString* name,
                                 const DexProto* proto) {
  return resolve_method(cls, name, proto, MethodSearch::Direct);
}

/**
 * Given a scope defined by DexClass, a name and a proto look for a dmethod
 * definition in scope.
 */
inline DexMethod* resolve_static_deprecated(const DexClass* cls,
                                            const DexString* name,
                                            const DexProto* proto) {
  return resolve_method_deprecated(cls, name, proto, MethodSearch::Static);
}

inline DexMethod* resolve_static(const DexClass* cls,
                                 const DexString* name,
                                 const DexProto* proto) {
  return resolve_method(cls, name, proto, MethodSearch::Static);
}

/**
 * Given a scope defined by DexClass, a name and a proto look for a vmethod
 * definition in the scope defined by the interface.
 */
inline DexMethod* resolve_interface_method_deprecated(const DexClass* cls,
                                                      const DexString* name,
                                                      const DexProto* proto) {
  return resolve_method_deprecated(cls, name, proto, MethodSearch::Interface);
}

inline DexMethod* resolve_interface_method(const DexClass* cls,
                                           const DexString* name,
                                           const DexProto* proto) {
  return resolve_method(cls, name, proto, MethodSearch::Interface);
}

/**
 * Resolve a method to its definition. When searching for a definition of a
 * virtual callsite, we return one of the possible callees.
 *
 * - Handling searching of super class requires `caller` argument to be passed.
 *
 * - When this is used to search for any invoke other than invoke-super, if the
 * method is already a definition return itself.
 *
 * - If the type the method belongs to is unknown return nullptr.
 */
DexMethod* resolve_method_deprecated(DexMethodRef* method,
                                     MethodSearch search,
                                     const DexMethod* caller = nullptr);
DexMethod* resolve_method(DexMethodRef* method,
                          MethodSearch search,
                          const DexMethod* caller = nullptr);

/**
 * Resolve a method and cache the mapping.
 * If the method is already a definition return itself.
 * If the type the method belongs to is unknown return nullptr.
 * This method takes a cache from refs to defs and populate it
 * to help speed up resolution.
 * When walking all the opcodes this method performs better avoiding lookup
 * of refs that had been resolved already.
 * Clients are responsible for the lifetime of the cache.
 *
 * Note that the cache is not thread-safe.
 */
DexMethod* resolve_method_deprecated(DexMethodRef* method,
                                     MethodSearch search,
                                     MethodRefCache& ref_cache,
                                     const DexMethod* caller = nullptr);
DexMethod* resolve_method(DexMethodRef* method,
                          MethodSearch search,
                          MethodRefCache& ref_cache,
                          const DexMethod* caller = nullptr);
/**
 * Resolve a method and cache the mapping. This method has the same behavior as
 * the other resolve_method with a cache, but this method is thread-safe.
 */
DexMethod* resolve_method_deprecated(
    DexMethodRef* method,
    MethodSearch search,
    ConcurrentMethodRefCache& concurrent_ref_cache,
    const DexMethod* caller = nullptr);

DexMethod* resolve_method(DexMethodRef* method,
                          MethodSearch search,
                          ConcurrentMethodRefCache& concurrent_ref_cache,
                          const DexMethod* caller = nullptr);

/**
 * Resolve the method of an invoke instruction. Note that there are some
 * invoke-virtual call on methods whose def are actually in interface. Thus, for
 * an invoke-virtual, it first tries MethodSearch::Virtual, and then
 * MethodSearch::InterfaceVirtual.
 */
DexMethod* resolve_invoke_method_deprecated(
    const IRInstruction* insn,
    const DexMethod* caller = nullptr,
    bool* resolved_virtual_to_interface = nullptr);

// Resolves `callee_ref` as an invoke instruction with `opcode` would.
DexMethod* resolve_invoke_method_deprecated(
    IROpcode opcode,
    DexMethodRef* callee_ref,
    const DexMethod* caller = nullptr,
    bool* resolved_virtual_to_interface = nullptr);

DexMethod* resolve_invoke_method(const IRInstruction* insn,
                                 const DexMethod* caller = nullptr,
                                 bool* resolved_virtual_to_interface = nullptr);

/**
 * The method that calling `method_handle` from code in `caller` runs, or
 * nullptr when the handle gets or puts a field, the method is unknown, or the
 * handle's kind does not match the class (an invoke-interface handle of a
 * class method, an invoke-instance handle of an interface method).
 *
 * ART calls an invoke-direct handle of a method that is not private without
 * virtual dispatch, but which method it runs differs by version. It resolves
 * the named method and takes the implementation that the caller's class has,
 * which Android 9 runs. Android 10 and later run that implementation only when
 * the named class declares it, and otherwise the method at its vtable index in
 * the named class's superclass. For example, for an invoke-direct handle of
 * `A.m` held by `C extends B extends A`, where `B` overrides `m`, Android 9
 * runs `B.m` and Android 10 and later run what `A`'s superclass has at that
 * index, while an invoke-super of `A.m` from `C` would run `B.m` and the
 * JVM would run `A.m`. Such a handle resolves here only where the versions
 * agree: to the caller's implementation when the named class declares it or
 * inherits it from its superclass, and otherwise to nullptr. It resolves to
 * nullptr as well where a package-private method of that name and prototype
 * may keep a method of another package from taking over its vtable slot, as
 * a package-private `p.B.m` does for `q.C.m` in `p.D extends q.C extends p.B`:
 * the slot then need not hold the method that a search by name finds.
 */
DexMethod* resolve_method_handle(const DexMethodHandle* method_handle,
                                 const DexMethod* caller);

/**
 * Every method that calling `method_handle` from code in `caller` can run as
 * its resolved method on some version of ART: the result of
 * `resolve_method_handle` when it has one. For an invoke-direct handle of a
 * method that is not private on whose target ART versions disagree, these are
 * the implementation in the caller's class, which Android 9 runs, and the
 * implementation in the named class's superclass, which Android 10 and later
 * run; when that superclass has none, Android 10 and later read a vtable entry
 * that does not belong to the method, which no method here stands for. Where
 * a package-private method may make the slots differ from what a search by
 * name finds (see `resolve_method_handle`), these are every virtual method of
 * that name and prototype that the caller's class, the named class's
 * superclass or their superclasses declare.
 */
std::vector<DexMethod*> resolve_method_handle_callees(
    const DexMethodHandle* method_handle, const DexMethod* caller);

DexMethod* resolve_invoke_method_deprecated(
    const IRInstruction* insn,
    MethodRefCache& ref_cache,
    const DexMethod* caller = nullptr,
    bool* resolved_virtual_to_interface = nullptr);

DexMethod* resolve_invoke_method(const IRInstruction* insn,
                                 MethodRefCache& ref_cache,
                                 const DexMethod* caller = nullptr,
                                 bool* resolved_virtual_to_interface = nullptr);

/**
 * Whether a call to `ref`, which resolves to `resolved` (nullptr if it does not
 * resolve), is an external call: `resolved` is external, or the call does not
 * resolve and the class `ref` names is not internal (no definition, or
 * external), so its target is above that class, and external classes cannot
 * extend internal ones. A virtual call may still dispatch to an internal
 * override.
 */
bool is_external_call(const DexMethodRef* ref, const DexMethod* resolved);

/**
 * Given a scope defined by DexClass, a name and a proto look for the vmethod
 * on the top ancestor. Essentially finds where the method was introduced.
 * Stop the search when the type is unknown.
 * So effectively this returns the method on the top known ancestor.
 */
DexMethod* find_top_impl(const DexClass*, const DexString*, const DexProto*);

/**
 * Find where a method was introduced from an interface.
 * It may return a concrete method or a miranda depending on whether
 * the class where the interface is declared has a concrete method for the
 * interface method.
 */
DexMethod* find_top_intf_impl(const DexClass* cls,
                              const DexString* name,
                              const DexProto* proto);

/**
 * Whether `method` cannot take `new_proto` in place, keeping its class and
 * name, because calls or overrides could then bind differently: a method with
 * its name and `new_proto` is defined in its class, or, if `method` is
 * virtual, in a subtype (a subclass, or a subinterface or a class implementing
 * it if it is an interface), or in a class or interface that one of those
 * inherits from, including interfaces it implements only through a superclass
 * or a superinterface.
 *
 * Static and private methods and constructors are neither inherited nor
 * overridden, so for them only their own class counts.
 *
 * Method references are assumed to be resolved to their definitions, so
 * references with the new signature elsewhere do not count. One on the class
 * of `method` does: `DexMethodRef::change` cannot take its key.
 */
bool has_signature_collision(const SubtypeMaps& subtype_maps,
                             const DexMethod* method,
                             const DexProto* new_proto);

/**
 * Type of fields to resolve.
 */
enum class FieldSearch { Static, Instance, Any };

/**
 * Given a scope, a field name and a field type search the class
 * hierarchy for a definition of the field
 */
DexField* resolve_field(const DexType*,
                        const DexString*,
                        const DexType*,
                        FieldSearch = FieldSearch::Any);

/**
 * Given a field, search its class hierarchy for the definition.
 * If the field is a definition already the field is returned otherwise a
 * lookup in the class hierarchy is performed looking for the definition.
 */
inline DexField* resolve_field(const DexFieldRef* field,
                               FieldSearch search = FieldSearch::Any) {
  if (field->is_def()) {
    return const_cast<DexField*>(dynamic_cast<const DexField*>(field));
  }
  return resolve_field(field->get_class(), field->get_name(), field->get_type(),
                       search);
}

/**
 * The field that `method_handle` gets or puts, resolved as ART resolves it:
 * from the class that the handle names, among the static fields for a
 * static-get or static-put handle and among the instance fields for an
 * instance-get or instance-put handle, even when the handle names a definition
 * of the other kind. nullptr when the field is unknown, or when the handle
 * calls a method.
 */
DexField* resolve_field_handle(const DexMethodHandle* method_handle);

struct ConcurrentMethodResolverDeprecated {
  ConcurrentMethodRefCache concurrent_resolve_cache;
  DexMethod* operator()(DexMethodRef* method,
                        MethodSearch search,
                        const DexMethod* caller) {
    return resolve_method_deprecated(method, search, concurrent_resolve_cache,
                                     caller);
  }
};

struct ConcurrentMethodResolver {
  ConcurrentMethodRefCache concurrent_resolve_cache;
  DexMethod* operator()(DexMethodRef* method,
                        MethodSearch search,
                        const DexMethod* caller) {
    return resolve_method(method, search, concurrent_resolve_cache, caller);
  }
};
