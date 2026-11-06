/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <memory>
#include <vector>

#include "AtomicStatCounter.h"
#include "DeterministicContainers.h"
#include "IRList.h"
#include "Pass.h"
#include "StringBuilderAnalysis.h"

namespace stringbuilder_outliner {

using stringbuilder_analysis::BuilderState;
using stringbuilder_analysis::BuilderStateMap;

struct Config {
  size_t max_outline_length{9};
  size_t min_outline_count{10};
  bool derive_method_profiles_stats{true};
};

struct Stats {
  size_t stringbuilders_removed{0};
  size_t operations_removed{0};
  size_t helper_methods_created{0};
  AtomicStatCounter<size_t> tostring_outlined_hot{0};
};

class Outliner {
 public:
  explicit Outliner(Config config = Config());

  const Config& get_config() const { return m_config; }

  const Stats& get_stats() const { return m_stats; }

  void analyze(IRCode& code);

  void create_outline_helpers(DexStoresVector* stores);

  void transform(const DexMethod* source_method, IRCode* code);

  void set_hot_method_from_callsite();

  using OutlinedMethods = ConcurrentMap<DexMethod*, std::vector<DexMethod*>>;

  const OutlinedMethods& get_outlined_methods() const {
    return m_target_to_source_map;
  }

 private:
  const DexTypeList* typelist_from_state(const BuilderState& state) const;

  void gather_outline_candidate_typelists(
      const BuilderStateMap& tostring_instruction_to_state);

  std::unique_ptr<IRCode> create_outline_helper_code(DexMethod*) const;

  static void apply_changes(
      const UnorderedMap<const IRInstruction*, IRInstruction*>& insns_to_insert,
      const UnorderedMap<const IRInstruction*, IRInstruction*>&
          insns_to_replace,
      IRCode* code);

  Config m_config;
  Stats m_stats;

  const DexString* m_append_str;
  DexType* m_stringbuilder;
  DexMethodRef* m_stringbuilder_default_ctor;
  DexMethodRef* m_stringbuilder_capacity_ctor;
  DexMethodRef* m_stringbuilder_tostring;

  // Map typelists of potentially outlinable StringBuilder call sequence to
  // their number of occurrences.
  AtomicMap<const DexTypeList*, size_t> m_outline_typelists;
  // Typelists of call sequences we have chosen to outline -> generated outline
  // helper method.
  UnorderedMap<const DexTypeList*, DexMethod*> m_outline_helpers;

  InsertOnlyConcurrentMap<const IRCode*, BuilderStateMap> m_builder_state_maps;

  // Maps each outlined target method to it's sources to derive method profile
  // stats
  OutlinedMethods m_target_to_source_map;

  // Own snapshots: caller CFGs may change before helper profiles are inserted.
  ConcurrentMap<DexMethod*, std::vector<std::unique_ptr<SourceBlock>>>
      m_target_to_callsite_source_blocks;
};

class StringBuilderOutlinerPass : public Pass {
 public:
  StringBuilderOutlinerPass() : Pass("StringBuilderOutlinerPass") {}

  std::string get_config_doc() override {
    return trim(R"(
This pass looks for recurring sequences of StringBuilder calls and outlines
them. This outlining is special-cased because StringBuilders are one of the
most commonly instantiated objects in Java code, and because we can use
knowledge of the semantics of StringBuilder methods to perform code motion
as part of that outlining. In particular, StringBuilder calls tend to occur
in the following pattern:
```
  new-instance v0 StringBuilder;
  invoke-direct v0 StringBuilder;.<init>:()V
  [sget v1 Foo;.bar:I | iget-object v1 v2 Foo;.baz:I | ...]
  invoke-virtual {v0, v1} StringBuilder;.append:(I)Ljava/lang/StringBuilder;
  [sget v1 Foo;.bar:I | iget-object v1 v2 Foo;.baz:I | ...]
  invoke-virtual {v0, v1} StringBuilder;.append:(I)Ljava/lang/StringBuilder;
  [sget v1 Foo;.bar:I | iget-object v1 v2 Foo;.baz:I | ...]
  invoke-virtual {v0, v1} StringBuilder;.append:(I)Ljava/lang/StringBuilder;
  invoke-virtual v0 StringBuilder;.toString:()Ljava/lang/String;
  move-result-object v0
```
The instructions inside [...] denote a variety of possible instructions that
can generate the values passed to append(). Since these value-generating
instructions tend to vary between StringBuilder use sites, an outliner that
tries to factor out common patterns without reordering instructions would
be thwarted by them. However, since we know that StringBuilder methods are
independent of any state in user code, we can safely move them down to create
contiguous sequences of repetitive code:
```
  [sget v1 Foo;.bar:I | iget-object v1 v4 Foo;.baz:I | ...]
  [sget v2 Foo;.bar:I | iget-object v2 v4 Foo;.baz:I | ...]
  [sget v3 Foo;.bar:I | iget-object v3 v4 Foo;.baz:I | ...]
  // Beginning of outlinable section
  new-instance v0 StringBuilder;
  invoke-direct v0 StringBuilder;.<init>:()V
  invoke-virtual {v0, v1} StringBuilder;.append:(I)Ljava/lang/StringBuilder;
  invoke-virtual {v0, v2} StringBuilder;.append:(I)Ljava/lang/StringBuilder;
  invoke-virtual {v0, v3} StringBuilder;.append:(I)Ljava/lang/StringBuilder;
  invoke-virtual v0 StringBuilder;.toString:()Ljava/lang/String;
  move-result-object v0
```
This code reordering is conceptual -- we don't actually perform the
reordering separately from the outlining. Instead, we use Abstract
Interpretation to model the state of StringBuilder instances, so we can
generate outlined code based on that state.

Note that this transformation means that the StringBuilder instance is no
longer accessible in the caller. That means that it cannot be used by any
operations aside from those in the outlined code. It is a little tricky to
do this analysis, so we defer it to a later run of the ObjectSensitiveDce
pass. Here we just replace calls to StringBuilder.toString() with calls to
the outline helper functions and assume that in most cases the StringBuilder
instance and the append operations on them are going to be removable by
OSDCE. This is generally true in practice.
    )");
  }

  redex_properties::PropertyInteractions get_property_interactions()
      const override {
    using namespace redex_properties::interactions;
    using namespace redex_properties::names;
    return {
        {NoResolvablePureRefs, Preserves},
    };
  }

  void bind_config() override {
    bind("max_outline_length", m_config.max_outline_length,
         m_config.max_outline_length);
    bind("min_outline_count", m_config.min_outline_count,
         m_config.min_outline_count);
    bind("derive_method_profiles_stats",
         m_config.derive_method_profiles_stats,
         m_config.derive_method_profiles_stats,
         "Whether to derive method profile stats for generated outline methods "
         "from methods outlined from");
  }

  void run_pass(DexStoresVector&, ConfigFiles&, PassManager&) override;

 private:
  Config m_config;
};

} // namespace stringbuilder_outliner
