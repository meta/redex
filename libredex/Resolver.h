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
#include "DexClass.h"
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
  always_assert(opcode::is_an_invoke(opcode));
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
  if (cls == nullptr) {
    return nullptr;
  }
  always_assert_log(is_interface(cls), "Class %s is not an interface\n",
                    SHOW(cls));
  return resolve_method_deprecated(cls, name, proto, MethodSearch::Interface);
}

inline DexMethod* resolve_interface_method(const DexClass* cls,
                                           const DexString* name,
                                           const DexProto* proto) {
  if (cls == nullptr) {
    return nullptr;
  }
  always_assert_log(is_interface(cls), "Class %s is not an interface\n",
                    SHOW(cls));
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

DexMethod* resolve_invoke_method(const IRInstruction* insn,
                                 const DexMethod* caller = nullptr,
                                 bool* resolved_virtual_to_interface = nullptr);

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
