/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once
#include <functional>
#include <limits>

#include <sparta/PatriciaTreeMapAbstractEnvironment.h>
#include <sparta/PatriciaTreeSetAbstractDomain.h>

#include "BaseIRAnalyzer.h"
#include "ControlFlow.h"
#include "EnumConfig.h"
#include "OptimizeEnumsUnsafeType.h"
#include "TypeUtil.h"

namespace optimize_enums {

/**
 * Return whether the method is
 * LEnumSubtype;.valueOf:(Ljava/lang/String;)LEnumSubtype;
 */
bool is_enum_valueof(const DexMethodRef* method);

/**
 * Return whether the method is LEnumSubtype;.values:()[LEnumSubtype;
 */
bool is_enum_values(const DexMethodRef* method);

/**
 * Return whether the field is
 * LEnumSubtype;.$ENTRIES:Lkotlin/enums/EnumEntries;
 */
bool is_enum_entries(const DexFieldRef* field);

/**
 * Whether `field_ref` is an enum's synthetic values array field, usually
 * `$VALUES`. It is recognized by its type, as shrinkers that ran on a library
 * before Redex may have renamed it.
 */
bool is_enum_values_field(const DexFieldRef* field_ref);

constexpr const char* KT_ENUM_ENTRIES_TYPE = "Lkotlin/enums/EnumEntries;";
constexpr const char* ENUM_VALUES_FIELD = "$VALUES";
constexpr const char* ENUM_ENTRIES_FIELD = "$ENTRIES";
constexpr const char* KT_ENUM_ENTRIES_FACTORY_METHOD =
    "Lkotlin/enums/EnumEntriesKt;.enumEntries:([Ljava/lang/Enum;)Lkotlin/"
    "enums/EnumEntries;";
constexpr const char* KT_ENUM_ENTRIES_LIST_CTOR =
    "Lkotlin/enums/EnumEntriesList;.<init>:([Ljava/lang/Enum;)V";

/**
 * Whether `method` is Kotlin's `EnumEntriesKt.enumEntries(Enum[])`, with
 * which a Kotlin enum's `<clinit>` builds `$ENTRIES` from the values array.
 * It returns `EnumEntries`, or the `EnumEntriesList` that it constructs once
 * ResolveRefsPass has specialized the reference. A method with the same name
 * and arguments that returns anything else is other code, about which nothing
 * is known. OptimizeEnums relies on the factory only allocating, so an app's
 * copy marked `no_optimizations`, whose code may not be what runs, does not
 * count.
 */
bool is_kt_enum_entries_factory(const DexMethodRef* method);

/**
 * Whether `method` is `EnumEntriesList.<init>(Enum[])`, all the factory does.
 * `<clinit>` calls it directly once MethodInlinePass has inlined the factory.
 * As for the factory, a copy marked `no_optimizations` does not count.
 */
bool is_kt_enum_entries_list_ctor(const DexMethodRef* method);

// Store possible types for a register although we only care about Object,
// Enum and Enum's subtypes.
using EnumTypes = sparta::PatriciaTreeSetAbstractDomain<const DexType*>;
using EnumTypeEnvironment =
    sparta::PatriciaTreeMapAbstractEnvironment<reg_t, EnumTypes>;

class EnumFixpointIterator final
    : public ir_analyzer::BaseIRAnalyzer<EnumTypeEnvironment> {
 public:
  explicit EnumFixpointIterator(const cfg::ControlFlowGraph& cfg,
                                const Config& config)
      : ir_analyzer::BaseIRAnalyzer<EnumTypeEnvironment>(cfg),
        m_config(config) {}

  void analyze_instruction(const IRInstruction* insn,
                           EnumTypeEnvironment* env) const override;

  static EnumTypeEnvironment gen_env(const DexMethod* method);

 private:
  const Config& m_config;

  const DexType* ENUM_TYPE = type::java_lang_Enum();
  const DexType* OBJECT_TYPE = type::java_lang_Object();
};

void reject_unsafe_enums(
    const std::vector<DexClass*>& classes,
    Config* config,
    const std::function<void(const DexType*, UnsafeType u)>& reject_fn);
} // namespace optimize_enums
