/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "DeterministicContainers.h"
#include "Pass.h"

/*
 * This pass identifies fields that are never read from and deletes all writes
 * to them. Similarly, all fields that are never written to and do not have
 * a non-zero static value get all of their read instructions replaced by
 * const 0 instructions.
 *
 * This pass relies on RemoveUnreachablePass running afterward to remove the
 * definitions of those fields entirely.
 *
 * Possible future work: This could be extended to eliminate fields that are
 * only used in non-escaping contexts.
 *
 * NOTE: Removing writes to fields may affect the life-time of an object, if all
 * other references to it are weak. Thus, this is a somewhat unsafe, or at least
 * potentially behavior altering optimization.
 */
namespace remove_unused_fields {

constexpr const char* REMOVED_FIELDS_FILENAME = "redex-removed-fields.txt";

struct Config {
  bool remove_unread_fields;
  bool remove_unwritten_fields;
  bool remove_zero_written_fields;
  bool remove_vestigial_objects_written_fields;
  UnorderedSet<const DexType*> blocklist_types;
  UnorderedSet<const DexType*> blocklist_classes;
  UnorderedSet<const DexType*> allowlist_types;
};

// The fields of `scope` with a write that the pass, configured by `config`,
// removes because nothing reads the field. The code of every method must have
// its CFG built. A field is listed when the pass removes at least one of its
// writes; it may also have writes the pass keeps, such as those in methods
// marked `no_optimizations`.
UnorderedSet<const DexField*> fields_with_removable_unread_writes(
    const Config& config, const Scope& scope);

class PassImpl : public Pass {
 public:
  PassImpl() : Pass("RemoveUnusedFieldsPass") {}

  redex_properties::PropertyInteractions get_property_interactions()
      const override {
    using namespace redex_properties::interactions;
    using namespace redex_properties::names;
    return {
        {NeedsAreEqualRefReservation, Establishes},
        {DexLimitsObeyed, Preserves},
        {NoResolvablePureRefs, Preserves},
        {SpuriousGetClassCallsInterned, RequiresAndPreserves},
    };
  }

  void bind_config() override {
    bind("remove_unread_fields", true, m_config.remove_unread_fields);
    bind("remove_unwritten_fields", true, m_config.remove_unwritten_fields);
    bind("remove_zero_written_fields",
         true,
         m_config.remove_zero_written_fields);
    bind("remove_vestigial_objects_written_fields", true,
         m_config.remove_vestigial_objects_written_fields);
    bind("blocklist_types",
         {},
         m_config.blocklist_types,
         "Fields with these types will never be removed.",
         Configurable::bindflags::types::warn_if_unresolvable);
    bind("blocklist_classes",
         {},
         m_config.blocklist_classes,
         "Fields in these classes will never be removed.");
    bind("allowlist_types",
         {},
         m_config.allowlist_types,
         "Fields with these types that are otherwise eligible to be removed "
         "will be removed regardless of their lifetime dependencies.");

    // These options make it a bit more convenient to bisect the list of removed
    // fields to isolate one that's causing issues.
    bind("export_removed",
         false,
         m_export_removed,
         "Write all removed fields to " + std::string(REMOVED_FIELDS_FILENAME));
  }

  void run_pass(DexStoresVector& stores,
                ConfigFiles& conf,
                PassManager& mgr) override;

  const Config& get_config() const { return m_config; }

 private:
  Config m_config;
  bool m_export_removed;
};

} // namespace remove_unused_fields
