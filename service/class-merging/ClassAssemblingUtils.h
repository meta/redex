/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "ControlFlow.h"
#include "DexClass.h"
#include "DexStore.h"
#include "IRInstruction.h"
#include "MergerType.h"

class RefChecker;

namespace class_merging {

struct ModelSpec;

constexpr const char* INTERNAL_TYPE_TAG_FIELD_NAME = "$t";
constexpr const char* EXTERNAL_TYPE_TAG_FIELD_NAME = "mTypeTag";

std::vector<DexField*> create_merger_fields(
    const DexType* owner,
    const FieldsMap& fields_map,
    const DexType* parent,
    const RefChecker& ref_checker,
    bool preserve_unanimous_field_types);

void cook_merger_fields_lookup(
    const std::vector<DexField*>& new_fields,
    const FieldsMap& fields_map,
    UnorderedMap<DexField*, DexField*>& merger_fields_lookup);

DexClass* create_class(const DexType* type,
                       const DexType* super_type,
                       const std::string_view pkg_name,
                       const std::vector<DexField*>& fields,
                       const TypeSet& interfaces,
                       bool with_default_ctor = false,
                       DexAccessFlags access = ACC_PUBLIC);

DexClass* create_merger_class(const DexType* type,
                              const DexType* super_type,
                              const std::vector<DexField*>& merger_fields,
                              const TypeSet& interfaces,
                              const bool add_type_tag_field,
                              bool with_default_ctor = false);

void patch_iput(const cfg::InstructionIterator& it);

void patch_iget(cfg::ControlFlowGraph& cfg,
                const cfg::InstructionIterator& it,
                DexType* original_field_type,
                SourceBlock* prev_sb,
                bool disable_violation_fixes);

void add_class(DexClass* new_cls,
               Scope& scope,
               DexStoresVector& stores,
               std::optional<size_t> dex_id);

} // namespace class_merging
