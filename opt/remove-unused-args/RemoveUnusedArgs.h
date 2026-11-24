/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "ConcurrentContainers.h"
#include "ControlFlow.h"
#include "InitClassesWithSideEffects.h"
#include "LocalDce.h"
#include "MethodOverrideGraph.h"
#include "MethodUtil.h"
#include "Pass.h"

namespace remove_unused_args {

namespace mog = method_override_graph;

std::map<uint16_t, cfg::InstructionIterator> compute_dead_insns(
    const DexMethod* method, const IRCode& code);

class RemoveArgs {
 public:
  struct MethodStats {
    size_t method_params_removed_count{0};
    size_t method_results_removed_count{0};
    size_t method_protos_reordered_count{0};
    size_t methods_updated_count{0};
    LocalDce::Stats local_dce_stats;
  };
  struct PassStats {
    size_t method_params_removed_count{0};
    size_t methods_updated_count{0};
    size_t callsite_args_removed_count{0};
    size_t method_results_removed_count{0};
    size_t method_protos_reordered_count{0};
    LocalDce::Stats local_dce_stats;
  };

  RemoveArgs(const Scope& scope,
             const init_classes::InitClassesWithSideEffects&
                 init_classes_with_side_effects,
             const std::vector<std::string>& blocklist,
             const UnorderedSet<DexMethodRef*>& pure_methods,
             size_t iteration = 0)
      : m_scope(scope),
        m_methods_named_by_method_handles(
            method::gather_methods_named_by_method_handles(scope)),
        m_init_classes_with_side_effects(init_classes_with_side_effects),
        m_blocklist(blocklist),
        m_iteration(iteration),
        m_pure_methods(pure_methods) {}
  RemoveArgs::PassStats run(ConfigFiles& conf);

 private:
  const Scope& m_scope;
  const InsertOnlyConcurrentSet<const DexMethod*>
      m_methods_named_by_method_handles;
  InsertOnlyConcurrentMap<const DexMethod*, const DexMethod*>
      m_method_representative_map;
  InsertOnlyConcurrentMap<const DexMethod*, UnorderedSet<const DexMethod*>>
      m_related_method_groups;
  const init_classes::InitClassesWithSideEffects&
      m_init_classes_with_side_effects;
  InsertOnlyConcurrentMap<DexMethod*, std::deque<uint16_t>> m_live_arg_idxs_map;
  InsertOnlyConcurrentMap<DexMethod*, std::deque<uint16_t>>
      m_abstract_live_arg_idxs_map;
  // Data structure to remember running indices to make method names unique when
  // we reorder prototypes or remove args across virtual scopes.
  struct NamedRenameMap {
    size_t next_reordering_uniquifiers{0};
    size_t next_removal_uniquifiers{0};
    UnorderedMap<DexTypeList*, size_t> reordering_uniquifiers;
    UnorderedMap<const DexMethod*, size_t> removal_uniquifiers;
  };
  UnorderedMap<const DexString*, NamedRenameMap> m_rename_maps;
  ConcurrentSet<const DexMethod*> m_result_used;
  UnorderedMap<DexProto*, DexProto*> m_reordered_protos;
  const std::vector<std::string>& m_blocklist;
  size_t m_iteration;
  const UnorderedSet<DexMethodRef*>& m_pure_methods;

  DexTypeList::ContainerType get_live_arg_type_list(
      const DexMethod* method, const std::deque<uint16_t>& live_arg_idxs);
  bool update_method_signature(DexMethod* method,
                               DexProto* updated_proto,
                               bool is_reordered);
  MethodStats update_method_protos(
      const mog::Graph& override_graph,
      const UnorderedSet<DexType*>& no_devirtualize_anno);
  size_t update_callsite(IRInstruction* instr);
  std::pair<size_t, LocalDce::Stats> update_callsites();
  void gather_results_used();
  void compute_reordered_protos(const mog::Graph& override_graph);
  void populate_representative_ids(
      const mog::Graph& override_graph,
      const UnorderedSet<DexType*>& no_devirtualize_annos);
  bool compute_remove_result(const DexMethod* method);
  bool can_change_signature(const DexMethod* method) const;

  struct Entry {
    std::vector<cfg::InstructionIterator> dead_insns;
    std::deque<uint16_t> live_arg_idxs;
    bool remove_result;
    bool is_reordered;
    DexProto* updated_proto;
    DexProto* original_proto;
  };

  void gather_updated_entries(
      const UnorderedSet<DexType*>& no_devirtualize_annos,
      InsertOnlyConcurrentMap<DexMethod*, Entry>* updated_entries);
};

class RemoveUnusedArgsPass : public Pass {
 public:
  RemoveUnusedArgsPass() : Pass("RemoveUnusedArgsPass") {}

  redex_properties::PropertyInteractions get_property_interactions()
      const override {
    using namespace redex_properties::interactions;
    using namespace redex_properties::names;
    return {
        {DexLimitsObeyed, Preserves},
        // Finding the used results relies on resolvable method references
        // being definitions.
        {NoResolvablePureRefs, RequiresAndPreserves},
        {InitialRenameClass, Preserves},
    };
  }

  void bind_config() override { bind("blocklist", {}, m_blocklist); }

  void run_pass(DexStoresVector&, ConfigFiles&, PassManager& mgr) override;

 private:
  std::vector<std::string> m_blocklist;
  size_t m_total_iterations{0};
};

} // namespace remove_unused_args
