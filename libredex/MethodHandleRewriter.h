/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <functional>
#include <optional>
#include <vector>

#include "ConcurrentContainers.h"
#include "DexMethodHandle.h"

class DexCallSite;
class DexMethod;
class DexProto;
class DexType;
class IRInstruction;

/**
 * Rewrites the method handles and call sites that instructions hold, for one
 * operation of a pass that changes what code refers to.
 *
 * Method handles and call sites are shared: every instruction that names the
 * same method handle or call site item holds the same object, and ART links
 * each call site item once, so instructions that share a call site run its
 * bootstrap method once and then call the same target. A rewriter therefore
 * never changes a handle or call site in place but replaces it, and makes each
 * replacement once: every instruction that held the same original and whose
 * values map alike gets the same replacement, while originals that were
 * distinct stay distinct. Use one rewriter for all instructions of an
 * operation.
 *
 * `rewrite` is thread-safe, so a parallel walk can share a rewriter; the
 * mappings must then be thread-safe too.
 */
class MethodHandleRewriter {
 public:
  struct Mappings {
    // What `handle`, held by code of `holder`, becomes: a value naming the
    // handle type and the method or field. std::nullopt, or a value equal to
    // `handle`, keeps it. What a handle calls can depend on the class that
    // holds it, hence `holder`. Unset keeps every handle.
    std::function<std::optional<DexMethodHandle>(const DexMethodHandle* handle,
                                                 const DexMethod* holder)>
        handle = nullptr;
    // The type whose Class a call site passes to its bootstrap method in place
    // of the Class of `type`; returning `type` keeps it. Unset keeps every
    // Class.
    std::function<DexType*(DexType* type)> class_type = nullptr;
    // The prototype that a call site names in place of `proto`, as its method
    // type or as a method type among its bootstrap arguments; returning
    // `proto` keeps it. Unset keeps every prototype.
    std::function<DexProto*(DexProto* proto)> method_type = nullptr;
  };

  explicit MethodHandleRewriter(Mappings mappings)
      : m_mappings(std::move(mappings)) {}

  /**
   * Makes `insn`, held by code of `holder`, hold the replacement of the method
   * handle it loads (const-method-handle) or of its call site (invoke-custom):
   * a call site is replaced when its bootstrap method, its method type, or a
   * method handle, Class or method type among its bootstrap arguments maps to
   * something else. Returns whether `insn` changed.
   */
  bool rewrite(IRInstruction* insn, const DexMethod* holder);

 private:
  struct HandleKey {
    const DexMethodHandle* original;
    MethodHandleType type;
    const void* member;
    bool operator==(const HandleKey&) const = default;
  };
  struct HandleKeyHash {
    size_t operator()(const HandleKey& key) const;
  };
  // A call site and what each of its values (bootstrap method, method type,
  // then each bootstrap argument) becomes.
  struct CallSiteKey {
    const DexCallSite* original;
    std::vector<const void*> values;
    bool operator==(const CallSiteKey&) const = default;
  };
  struct CallSiteKeyHash {
    size_t operator()(const CallSiteKey& key) const;
  };

  DexMethodHandle* replace(DexMethodHandle* handle, const DexMethod* holder);
  DexType* replace(DexType* type) const;
  DexProto* replace(DexProto* proto) const;
  DexCallSite* replace(DexCallSite* callsite, const DexMethod* holder);

  Mappings m_mappings;
  InsertOnlyConcurrentMap<HandleKey, DexMethodHandle*, HandleKeyHash> m_handles;
  InsertOnlyConcurrentMap<CallSiteKey, DexCallSite*, CallSiteKeyHash>
      m_callsites;
};
