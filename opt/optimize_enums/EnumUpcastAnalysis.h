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
