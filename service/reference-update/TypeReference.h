/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <functional>
#include <optional>

#include "ClassHierarchy.h"
#include "DeterministicContainers.h"
#include "DexClass.h"

using TypeSet = std::set<const DexType*, dextypes_comparator>;
using UnorderedTypeSet = UnorderedSet<const DexType*>;

namespace type_reference {

/**
 * Update old type reference to new type reference in all the fields and methods
 * in the scope, but is not responsible for updating opcodes. The users should
 * take care of other part of analysis and transformations to make sure the
 * updating being valid. This supports updating virtual methods through name
 * mangling instead of walking through virtual scopes.
 * Usage examples:
 *    1. Replace candidate enum types with Integer type after we finish the code
 *       transformation.
 *    2. Replace interfaces or parent classes references with new type
 *       references after we merge them to their single implementation or single
 *       child classes.
 * If the original name of a method or a field is "member_name", the updated
 * name may be "member_name$RDX$some_hash_value".
 */
class TypeRefUpdater final {
 public:
  /**
   * The old types should all have definitions so that it's unlikely that we are
   * trying to update a virtual method that may override any external virtual
   * method.
   */
  explicit TypeRefUpdater(const UnorderedMap<DexType*, DexType*>& old_to_new);
  explicit TypeRefUpdater(
      const UnorderedMap<const DexType*, DexType*>& old_to_new);

  void update_methods_fields(const Scope& scope);

 private:
  std::optional<std::reference_wrapper<const UnorderedMap<DexType*, DexType*>>>
      m_old_to_new;
  std::optional<
      std::reference_wrapper<const UnorderedMap<const DexType*, DexType*>>>
      m_old_to_new_const;
};

/**
 * original_name + "$RDX$" + hash_of_signature
 */
const DexString* new_name(const DexMethodRef* method);

const DexString* new_name(const DexFieldRef* field);

// A helper to stringify method signature for the method dedup mapping file.
std::string get_method_signature(const DexMethod* method);

bool proto_has_reference_to(const DexProto* proto,
                            const UnorderedTypeSet& targets);

/**
 * Get a new proto by updating the type references on the proto from an old type
 * to the provided new type.
 */
DexProto* get_new_proto(
    const DexProto* proto,
    const UnorderedMap<const DexType*, DexType*>& old_to_new);

DexProto* get_new_proto(
    const DexProto* proto,
    const UnorderedMap<const DexType*, const DexType*>& old_to_new);

/**
 * Update all method signature type references in-place using the old_to_new
 * map. We update all references to an old type to the provided new type.
 *
 * The optional `method_debug_map` stores the map from the updated DexMethod to
 * the string representation of the original method signature.
 */
void update_method_signature_type_references(
    const Scope& scope,
    const UnorderedMap<const DexType*, DexType*>& old_to_new,
    const SubtypeMaps& subtype_maps,
    std::optional<std::reference_wrapper<UnorderedMap<DexMethod*, std::string>>>
        method_debug_map = std::nullopt);

void update_field_type_references(
    const Scope& scope,
    const UnorderedMap<const DexType*, DexType*>& old_to_new);

void fix_colliding_dmethods(
    const Scope& scope,
    const std::vector<std::pair<DexMethod*, DexProto*>>& colliding_methods);
} // namespace type_reference
