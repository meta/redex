/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "ConcurrentContainers.h"
#include "DeterministicContainers.h"
#include "LiveRange.h"
#include "MethodOverrideGraph.h"
#include "Pass.h"

#include "TypeInference.h"
#include <utility>

using TypeEnvironments =
    UnorderedMap<const IRInstruction*, type_inference::TypeEnvironment>;

namespace mog = method_override_graph;

/*
 * This pass checks that typedef annotations usages are value safe
 * https://developer.android.com/studio/write/annotations#enum-annotations
 */
class TypedefAnnoCheckerPass : public Pass {
 public:
  TypedefAnnoCheckerPass() : Pass("TypedefAnnoCheckerPass") {}

  redex_properties::PropertyInteractions get_property_interactions()
      const override {
    return redex_properties::simple::preserves_all();
  }

  struct Config {
    const DexType* int_typedef{nullptr};
    const DexType* str_typedef{nullptr};
    size_t max_patcher_iteration{10};
    UnorderedSet<const DexType*> generated_type_annos;
    UnorderedSet<std::string> do_not_check_list;
  };

  void bind_config() override {
    bind("int_typedef", {}, m_config.int_typedef);
    bind("str_typedef", {}, m_config.str_typedef);
    bind("max_patcher_iteration",
         10,
         m_config.max_patcher_iteration,
         "Maximum number of Typedef annotation patcher iterations");
    bind("generated_type_annos",
         {},
         m_config.generated_type_annos,
         "Denote annotation types that are flagging generated methods.");
    bind("do_not_check_list",
         {},
         m_config.do_not_check_list,
         "A list of known symbol/methods used as generics that we cannot "
         "enforce safety checks on.");
  }

  explicit TypedefAnnoCheckerPass(Config config)
      : Pass("TypedefAnnoCheckerPass"), m_config(std::move(config)) {}

  void run_pass(DexStoresVector& stores,
                ConfigFiles& conf,
                PassManager& mgr) override;

 private:
  void gather_typedef_values(
      const DexClass* cls,
      InsertOnlyConcurrentMap<const DexClass*, UnorderedSet<const DexString*>>&
          strdef_constants,
      InsertOnlyConcurrentMap<const DexClass*, UnorderedSet<uint64_t>>&
          intdef_constants);

  // The methods a call can resolve to and be checked against: those with a
  // typedef param.
  static void collect_typedef_param_methods(
      const Scope& scope,
      const UnorderedSet<const DexType*>& typedef_annos,
      InsertOnlyConcurrentSet<const DexMethod*>& typedef_param_methods);

  // The checker only reports at a call with typedef params, a write to a
  // typedef field or a return from a method with a typedef return. A method
  // without any of them cannot fail, so it is not checked.
  static bool has_typedef_sink(
      DexMethod* m,
      const InsertOnlyConcurrentSet<const DexMethod*>& typedef_param_methods,
      const UnorderedSet<const DexType*>& typedef_annos);

  Config m_config;
  friend struct TypedefAnnoCheckerTest;
};

struct CheckerStats {
  std::string m_errors;
  size_t m_count{0};

  explicit CheckerStats(std::string error)
      : m_errors(std::move(error)), m_count(1) {}
  CheckerStats() = default;

  CheckerStats& operator+=(const CheckerStats& other) {
    m_count += other.m_count;
    if (m_errors.empty()) {
      m_errors = other.m_errors;
    } else {
      m_errors = m_errors + other.m_errors;
    }
    return *this;
  }
};

using StrDefConstants =
    InsertOnlyConcurrentMap<const DexClass*, UnorderedSet<const DexString*>>;

using IntDefConstants =
    InsertOnlyConcurrentMap<const DexClass*, UnorderedSet<uint64_t>>;

class TypedefAnnoChecker {
 public:
  explicit TypedefAnnoChecker(
      const StrDefConstants& strdef_constants,
      const IntDefConstants& intdef_constants,
      TypedefAnnoCheckerPass::Config config,
      const method_override_graph::Graph& method_override_graph)
      : m_config(std::move(config)),
        m_strdef_constants(strdef_constants),
        m_intdef_constants(intdef_constants),
        m_method_override_graph(method_override_graph) {}

  void run(DexMethod* m);

  bool complete() { return m_good; }

  std::string error() { return m_error; }

 private:
  bool should_skip_method(const DexMethod* m) const;

  void check_instruction(IRInstruction* insn);

  // Resolve a method and collect its overrides into a set.
  UnorderedBag<const DexMethod*> resolve_callees(const DexMethod* method);

  // Returns nullopt if the value is safe, or the error message string if not.
  std::optional<std::string> check_typedef_value(
      const std::optional<const DexType*>& annotation,
      IRInstruction* insn,
      src_index_t src);

  void add_error(const std::string& error);
  std::string format_source_loc(const IRInstruction* insn) const;

  bool m_good{true};
  std::string m_error;
  TypedefAnnoCheckerPass::Config m_config;
  UnorderedMap<const IRInstruction*, const DexPosition*> m_insn_positions;

  // Per-method state, set in run()
  DexMethod* m_method{nullptr};
  const type_inference::TypeInference* m_inference{nullptr};
  const live_range::UseDefChains* m_ud_chains{nullptr};
  const TypeEnvironments* m_envs{nullptr};
  std::optional<const DexType*> m_return_annotation;

  const StrDefConstants& m_strdef_constants;
  const IntDefConstants& m_intdef_constants;
  const method_override_graph::Graph& m_method_override_graph;
};
