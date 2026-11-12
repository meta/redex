/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <utility>

#include "ConstantPropagationRuntimeAssert.h"
#include "ConstantPropagationTransform.h"
#include "ConstantPropagationWholeProgramState.h"
#include "DeterministicContainers.h"
#include "IPConstantPropagationAnalysis.h"
#include "Pass.h"
#include "TypeSystem.h"

namespace constant_propagation {

namespace interprocedural {

class PassImpl : public Pass {
 public:
  struct Config {
    bool include_virtuals{false};
    bool use_multiple_callee_callgraph{false};
    bool create_runtime_asserts{false};
    // The maximum number of times we will try to refine the WholeProgramState.
    // Setting this to zero means that all field values and return values will
    // be treated as Top.
    uint64_t max_heap_analysis_iterations{0};
    uint32_t big_override_threshold{5};
    UnorderedSet<const DexType*> field_blocklist;
    bool compute_definitely_assigned_ifields{true};
    bool analyze_ancestor_constructors{false};
    bool reduce_stringbuilder_concat{false};
    bool merge_adjacent_constant_appends{false};
    bool replace_constant_stringbuilder_tostring_with_const_string{false};

    Transform::Config transform;
    RuntimeAssertTransform::Config runtime_assert;
  };

  redex_properties::PropertyInteractions get_property_interactions()
      const override {
    using namespace redex_properties::interactions;
    using namespace redex_properties::names;
    return {
        {NeedsAreEqualRefReservation, Establishes},
        {DexLimitsObeyed, Preserves},
        {NoResolvablePureRefs, Preserves},
        {InitialRenameClass, Preserves},
    };
  }

  std::string get_config_doc() override {
    return trim(R"(
Runs the constant-propagation abstract interpretation over the whole program.

#### Semantic changes in reduce_stringbuilder_concat

The rewrite changes reference identity. `String.concat` returns its receiver
when the argument is empty, where `toString()` allocated a new String, so a
concatenation that could only have produced a new object now produces one of its
operands:
```java
  String a = readName();       // "foo", not a compile-time constant
  String s = a + "";
  s.equals(a);                 // true, before and after
  s == a;                      // before: false. after: true.
```
The old `false` is guaranteed rather than incidental: JLS 15.18.1 specifies the
result of `+` to be a newly created String unless the expression is constant.
Contents never differ; only identity-sensitive code can observe the change --
`==`, `identityHashCode`, `IdentityHashMap`, a monitor held on the result, or a
weak reference to it.

#### Semantic changes in replace_constant_stringbuilder_tostring_with_const_string

This rewrite changes reference identity too, observable through the same
operations. `toString()` allocates a fresh String on every call; the
`const-string` that takes its place resolves to the interned instance of that
text, which is the same object every other occurrence of the literal in the
program resolves to (JLS 3.10.5):
```java
  String s = new StringBuilder().append("foo").toString();
  s.equals("foo");             // true, before and after
  s == "foo";                  // before: false. after: true.
```
    )");
  }

  explicit PassImpl(Config config)
      : Pass("InterproceduralConstantPropagationPass"),
        m_config(std::move(config)) {}

  PassImpl() : PassImpl(Config()) {}

  void bind_config() override {
    bind("replace_moves_with_consts",
         true,
         m_config.transform.replace_moves_with_consts);
    bind("remove_dead_switch", true, m_config.transform.remove_dead_switch);
    bind("include_virtuals", false, m_config.include_virtuals);
    bind("use_multiple_callee_callgraph",
         false,
         m_config.use_multiple_callee_callgraph);
    bind("big_override_threshold", UINT32_C(5),
         m_config.big_override_threshold);
    bind("create_runtime_asserts", false, m_config.create_runtime_asserts);
    bind("max_heap_analysis_iterations",
         UINT64_C(0),
         m_config.max_heap_analysis_iterations);
    bind("field_blocklist",
         {},
         m_config.field_blocklist,
         "List of types whose fields that this optimization will omit.");
    bind("compute_definitely_assigned_ifields", true,
         m_config.compute_definitely_assigned_ifields,
         "Whether to predict which instance fields are always written before "
         "they are read, in order to ignore the default value 0.");
    bind("analyze_ancestor_constructors", false,
         m_config.analyze_ancestor_constructors,
         "Analyze constructor calls on ancestor classes when proving instance "
         "field initialization.");
    bind("reduce_stringbuilder_concat", false,
         m_config.reduce_stringbuilder_concat,
         "Rewrite two-append String concatenations to String.concat: "
         "`new StringBuilder().append(a).append(b).toString()` becomes "
         "`a.concat(b)`, when both operands are proven non-null, because "
         "`concat` throws on null where `append` writes the text \"null\". The "
         "builder this orphans is only removed by a later "
         "ObjectSensitiveDcePass "
         "run, which is where the saving comes from. Introduces a semantic "
         "change -- see this pass's documentation. Has no effect once InterDex "
         "has run.");
    bind("merge_adjacent_constant_appends", false,
         m_config.merge_adjacent_constant_appends,
         "Merge consecutive `StringBuilder.append(String)` calls whose "
         "operands are all compile-time constants into a single append of the "
         "concatenation, saving one invocation per append removed.");
    bind("replace_constant_stringbuilder_tostring_with_const_string", false,
         m_config.replace_constant_stringbuilder_tostring_with_const_string,
         "Replace a StringBuilder holding one compile-time constant String "
         "with a const-string of the string it would have produced. The "
         "builder this orphans is only removed by a later "
         "ObjectSensitiveDcePass run, which is where the saving comes from. "
         "Introduces a semantic change -- see this pass's documentation.");
  }

  void eval_pass(DexStoresVector&, ConfigFiles&, PassManager&) override;

  void run_pass(DexStoresVector& stores,
                ConfigFiles& conf,
                PassManager& mgr) override;

  /*
   * run_pass() takes a PassManager object, making it awkward to call in unit
   * tests. run() is a more direct way to call this pass. The caller is
   * responsible for picking the right Config settings.
   */
  void run(const DexStoresVector& stores,
           const ConfigFiles& conf,
           int min_sdk = 0,
           const std::optional<std::string>& = std::nullopt);

  /*
   * Exposed for testing purposes.
   */
  std::unique_ptr<FixpointIterator> analyze(const Scope&,
                                            ImmutableAttributeAnalyzerState*,
                                            ApiLevelAnalyzerState*,
                                            StringAnalyzerState*,
                                            PackageNameState*,
                                            const NullCheckMethods&);

 private:
  void compute_analysis_stats(const WholeProgramState&,
                              const UnorderedSet<const DexField*>&);

  void optimize(const Scope&,
                const TypeSystem& type_system,
                const XStoreRefs& xstores,
                const FixpointIterator&,
                const ImmutableAttributeAnalyzerState*,
                const NullCheckMethods& null_check_methods);

  struct Stats {
    // Number of instance fields that are known to be definitely-assigned, i.e.
    // they are being written to before read during their object's construction.
    size_t definitely_assigned_ifields{0};
    // Number of definitely-assigned instance fields for which useful constant
    // values were found; a "useful constant value" is one that is not top, or
    // in case of Booleans 0 or 1, but some other abstract ConstantValue.
    size_t constant_definitely_assigned_ifields{0};
    // Number of fields for which useful constant values were found.
    size_t constant_fields{0};
    // number of methods for which useful constant return values were found.
    size_t constant_methods{0};

    size_t callgraph_nodes{0};
    size_t callgraph_edges{0};
    size_t callgraph_callsites{0};

    size_t heap_analysis_iterations{0};
    FixpointIterator::Stats fp_iter;
  } m_stats;
  Transform::Stats m_transform_stats;
  // Number of adjacent constant-String appends eliminated by merging.
  size_t m_appends_merged{0};
  // Number of toString() calls replaced by the constant string their
  // single-append builder holds. A builder read by several toString()s counts
  // once per call.
  size_t m_stringbuilder_constant_tostrings_replaced{0};
  // Number of two-append concatenations rewritten to String.concat.
  size_t m_concat_reduced{0};
  // Defaults to true: `run()` never sets it, and treating an unknown pipeline
  // position as post-InterDex keeps ref-adding transformations off.
  bool m_interdex_has_run{true};
  Config m_config;
};

} // namespace interprocedural

} // namespace constant_propagation

using InterproceduralConstantPropagationPass =
    constant_propagation::interprocedural::PassImpl;
