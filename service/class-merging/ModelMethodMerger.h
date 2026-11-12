/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <optional>

#include "DeterministicContainers.h"
#include "DexClass.h"
#include "IRInstruction.h"
#include "MergerType.h"
#include "MethodProfiles.h"
#include "Model.h"
#include "TypeTags.h"

struct InterfaceMethod;

namespace dispatch {
struct Spec;
struct DispatchMethod;
} // namespace dispatch

namespace class_merging {

using SwitchIndices = std::set<int>;
using MethodOrderedSet = std::set<DexMethod*, dexmethods_comparator>;
using TypeToMethod = UnorderedMap<const DexType*, const DexMethod*>;
using MergerToField = std::map<const MergerType*, DexField*>;
using MergerToMethods = std::map<const MergerType*, std::vector<DexMethod*>>;
using MethodReplacementPair = std::pair<const std::string, const DexMethod*>;
using TypeToMethodMap =
    UnorderedMap<const DexType*, std::vector<MethodReplacementPair>>;
using MethodToType = std::map<DexMethod*, DexType*, dexmethods_comparator>;

constexpr const char* INSTANCE_OF_STUB_NAME = "$instanceof";

struct MergedMethod {
  std::string name;
  size_t count;
  std::vector<std::string> samples;
};

struct MethodStats {
  UnorderedBag<MergedMethod> merged_methods;
  void add(const MethodOrderedSet& methods);
  void print(const std::string& model_name, uint32_t num_mergeables);
};

class ModelMethodMerger {
 public:
  ModelMethodMerger(
      const Scope& scope,
      const std::vector<const MergerType*>& mergers,
      const MergerToField& type_tag_fields,
      const TypeTags* type_tags,
      const UnorderedMap<DexMethod*, std::string>& method_debug_map,
      const ModelSpec& model_spec,
      std::optional<size_t> max_num_dispatch_target,
      std::optional<method_profiles::MethodProfiles*> method_profiles);

  TypeToMethod& merge_methods() {
    merge_ctors();
    dedup_non_ctor_non_virt_methods();
    merge_virt_itf_methods();
    return get_mergeable_ctor_map();
  }

  const ModelStats& get_stats() const { return m_stats; }
  TypeToMethod& get_mergeable_ctor_map() { return m_mergeable_to_merger_ctor; }
  void print_method_stats(const std::string& model_name,
                          uint32_t num_mergeables) {
    m_method_stats.print(model_name, num_mergeables);
  }

  static std::vector<IRInstruction*> make_check_cast(DexType* type,
                                                     reg_t src_dest);

  TypeToMethodMap get_method_dedup_map() { return m_method_dedup_map; }
  dispatch::DispatchMethod create_dispatch_method(
      const dispatch::Spec& spec, const std::vector<DexMethod*>& targets);

 private:
  const Scope& m_scope;
  const std::vector<const MergerType*> m_mergers;
  const MergerToField m_type_tag_fields;
  const TypeTags* m_type_tags;
  const UnorderedMap<DexMethod*, std::string>& m_method_debug_map;
  const ModelSpec m_model_spec;
  // This member is only used for testing purpose. If its value is greator than
  // zero, the splitting decision will bypass the instruction count limit.
  std::optional<size_t> m_max_num_dispatch_target;
  std::optional<method_profiles::MethodProfiles*> m_method_profiles;

  // dmethods
  MergerToMethods m_merger_ctors;
  MergerToMethods m_merger_non_ctors;
  // vmethods
  MergerToMethods m_merger_non_vmethods;
  // merger ctor map
  TypeToMethod m_mergeable_to_merger_ctor;
  // Stats for method dedupping
  MethodStats m_method_stats;
  // Method dedup map
  TypeToMethodMap m_method_dedup_map;

  ModelStats m_stats;
  // Victims already joined into each surviving dispatch target.
  UnorderedMap<DexMethod*, UnorderedSet<DexMethod*>> m_already_joined;

  void merge_ctors();
  void dedup_non_ctor_non_virt_methods();
  void merge_virt_itf_methods();
  void fix_visibility();

  void merge_virtual_methods(
      const Scope& scope,
      DexType* super_type,
      DexType* target_type,
      DexField* type_tag_field,
      const std::vector<MergerType::VirtualMethod>& virt_methods,
      std::vector<std::pair<DexClass*, DexMethod*>>& dispatch_methods,
      UnorderedMap<DexMethod*, DexMethod*>& old_to_new_callee);

  std::map<SwitchIndices, DexMethod*> get_dedupped_indices_map(
      const std::vector<DexMethod*>& targets,
      UnorderedMap<DexMethod*, MethodOrderedSet>* groups = nullptr);

  // Joins each retained dispatch target's throwing positions with those of the
  // methods it now stands for, while every one of them still holds its code.
  void join_ambiguous_positions(
      const UnorderedMap<DexMethod*, MethodOrderedSet>& groups);

  DexType* get_merger_type(DexType* mergeable);

  std::string get_method_signature_string(DexMethod* meth);

  // Helpers
  static void inline_dispatch_entries(
      DexType* merger_type,
      DexMethod* dispatch,
      std::vector<std::pair<DexType*, DexMethod*>>&
          not_inlined_dispatch_entries);
  static void sink_common_ctor_to_return_block(DexMethod* dispatch);
  static std::vector<IRInstruction*> make_string_const(reg_t dest,
                                                       const std::string& val);
};

} // namespace class_merging
