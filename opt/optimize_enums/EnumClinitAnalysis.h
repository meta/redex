/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <optional>

#include "ConcurrentContainers.h"
#include "DeterministicContainers.h"
#include "DexClass.h"
#include "IRInstruction.h"
#include "MethodOverrideGraph.h"

namespace optimize_enums {

/**
 * Enum instances are always stored as static fields with ACC_ENUM access flag.
 * The flag makes it easy to distinguish them from other fields on the enum
 * class.
 */
DexAccessFlags enum_field_access();

/**
 * Enum synthetic $VALUES field's access flag.
 */
DexAccessFlags synth_access();

struct EnumConstant {
  int32_t ordinal;
  const DexString* name;
};

struct EnumFieldValue {
  union {
    int64_t primitive_value;
    const DexString* string_value;
  };
  bool is_resource_id = false;
};
/**
 * Maps enum ordinals to values for a particular instance field.
 */
using EnumInstanceFieldValueMap = std::map<int64_t, EnumFieldValue>;
/**
 * Maps enum instance fields to their value map for a particular enum.
 */
using EnumInstanceFieldMap =
    UnorderedMap<DexFieldRef*, EnumInstanceFieldValueMap>;
/**
 * Maps enum fields to its ordinal and name.
 */
using EnumConstantsMap = UnorderedMap<const DexFieldRef*, EnumConstant>;

struct EnumAttributes {
  EnumConstantsMap m_constants_map;
  EnumInstanceFieldMap m_field_map;
  // The field of the constant that each `new-instance` in `<clinit>` creates.
  // Valid while `<clinit>` is unchanged.
  UnorderedMap<const IRInstruction*, const DexFieldRef*> m_constant_allocations;

  std::map<uint64_t, const DexString*> get_ordered_names() {
    std::map<uint64_t, const DexString*> names;
    for (const auto& pair : UnorderedIterable(m_constants_map)) {
      names[pair.second.ordinal] = pair.second.name;
    }
    return names;
  }
};

/**
 * The enum constants that each method may read, directly or in the code it
 * calls, computed once per method and reused for every enum. Several threads
 * may use it at once: a summary depends only on the program, so when two
 * threads compute one at the same time they compute the same one, and the
 * first one stored is kept.
 *
 * A method's summary is the constants its own instructions read, plus the
 * summaries of the methods it calls; it is unknown when the method may run
 * code Redex cannot see, since that code may read any constant. The analysis
 * is flow-insensitive: a method counts as reading every constant it reads on
 * any path. It does not follow the static initializers that the code may
 * trigger.
 *
 * It trusts a few methods to run no app code, so it does not follow them: the
 * library methods Redex treats as pure (`get_pure_methods`), Kotlin's
 * trustworthy null assertions, `Object.<init>`, `Enum.<init>`, whose effect
 * the analysis of `<clinit>` models, and an array's `clone()`. Where such a
 * method can be overridden, as `Enum.toString()` can, the overrides are
 * followed like any other callee.
 */
class ConstantReadSummaries {
 public:
  // The constants a method may read, or nullopt when it may read any.
  using Summary = std::optional<UnorderedSet<const DexField*>>;

  explicit ConstantReadSummaries(
      const method_override_graph::Graph& override_graph);

  /**
   * Whether the code that `call` runs may read one of `constants`.
   */
  bool call_may_read(const IRInstruction* call,
                     const UnorderedSet<const DexField*>& constants);

  /**
   * The summary of `method`, computing it if needed.
   */
  const Summary& of(const DexMethod* method);

 private:
  // What a method's own instructions read, and the methods it calls.
  struct Body {
    Summary own;
    std::vector<const DexMethod*> callees;
  };

  Body scan(const DexMethod* method);
  void compute(const DexMethod* root);
  // Adds the callees of `call` to `callees`; returns false when the call may
  // run code Redex cannot see.
  bool add_callees(const IRInstruction* call,
                   std::vector<const DexMethod*>* callees) const;

  const method_override_graph::Graph& m_override_graph;
  const UnorderedSet<DexMethodRef*> m_runs_no_app_code;
  InsertOnlyConcurrentMap<const DexMethod*, Summary> m_summaries;
};

/**
 * Returns an EnumInstanceFieldMap and an EnumConstantsMap if success,
 * otherwise, return empty maps.
 */
EnumAttributes analyze_enum_clinit(const DexClass* cls,
                                   bool support_kt_19_enum_entries,
                                   ConstantReadSummaries* reads);

} // namespace optimize_enums
