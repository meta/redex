/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ResourceValueMergingPass.h"
#include "ConfigFiles.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "PassManager.h"
#include "RedexResources.h"
#include "Styles.h"
#include "Trace.h"

#define MAX_STYLES_DEPTH 20

using namespace resources;
void print_resources(const UnorderedMap<uint32_t, ResourceAttributeInformation>&
                         optimized_resources) {
  if (!traceEnabled(RES, 3)) {
    return;
  }
  TRACE(RES, 3, "Resources that can be optimized via deletion:");
  for (const auto& [resource_id, attr_ids] :
       UnorderedIterable(optimized_resources)) {
    std::string attributes = "Attribute ID: ";
    for (const auto& attr_id : UnorderedIterable(attr_ids)) {
      std::ostringstream oss;
      oss << " 0x" << std::hex << attr_id << " ";
      attributes += oss.str();
    }
    TRACE(RES, 3, "Resource ID: 0x%x; %s", resource_id, attributes.c_str());
  }
}

void print_resources(
    const UnorderedMap<uint32_t,
                       UnorderedMap<uint32_t, resources::StyleResource::Value>>&
        optimized_resources) {
  if (!traceEnabled(RES, 3)) {
    return;
  }
  TRACE(RES, 3, "Resources that can be optimized via merging:");
  for (const auto& [resource_id, attr_map] :
       UnorderedIterable(optimized_resources)) {
    std::string attributes = "Attributes: ";
    for (const auto& [attr_id, _] : UnorderedIterable(attr_map)) {
      std::ostringstream oss;
      oss << " 0x" << std::hex << attr_id << " ";
      attributes += oss.str();
    }
    TRACE(RES, 3, "Resource ID: 0x%x; %s", resource_id, attributes.c_str());
  }
}

/**
 * Operation Ordering Requirements
 * -------------------------------
 * The operations in this pass must follow a specific order because the sequence
 * of modifications affects the final outcome:
 *
 * Let A = {set of addition operations}
 * Let R = {set of removal operations}
 *
 * Since A ∩ R ≠ ∅ (the intersection may not be empty), we must carefully order
 * our operations.
 *
 * Consider the following example:
 *   - A resource r has attribute a with value v1
 *   - All children of r have attribute a with value v2 (where v1 ≠ v2)
 *   - Then the attribute is removed from r based on the pass's deletion logic
 *   - Finally, attribute a hoists value v2 from its children to r
 *
 * In scenarios like the example above, to correctly update a resource r, the
 * following sequence of operations must be applied:
 * 1. First: Remove existing attribute a with value v1 from r
 * 2. Then: Add new attribute a with value v2 to r
 *
 * This scenario clearly demonstrates that there exists cases where order of
 * operations matters.
 *
 * Thus, Removals must always be applied before additions to ensure the
 * correct final state.
 */

void ResourceValueMergingPass::run_pass(DexStoresVector& stores,
                                        ConfigFiles& conf,
                                        PassManager& /*mgr*/) {
  TRACE(RES, 1, "ResourceValueMergingPass excluded_resources count: %zu",
        m_excluded_resources.size());

  for (const auto& resource : UnorderedIterable(m_excluded_resources)) {
    TRACE(RES, 1, "  Excluded resource: %s", resource.c_str());
  }

  std::string apk_dir;
  conf.get_json_config().get("apk_dir", "", apk_dir);

  auto resources = create_resource_reader(apk_dir);
  auto res_table = resources->load_res_table();
  auto resource_files = resources->find_resources_files();
  auto style_info = res_table->load_style_info();

  resources::ReachabilityOptions options;
  StyleAnalysis style_analysis(apk_dir, conf.get_global_config(), options,
                               stores, UnorderedSet<uint32_t>());

  const auto& ambiguous_styles = style_analysis.ambiguous_styles();
  const auto& directly_reachable_styles =
      style_analysis.directly_reachable_styles();

  if (traceEnabled(RES, 5)) {
    TRACE(RES, 5, "%s", style_analysis.dot(false, true).c_str());
  }

  // Synthetic Parent Optimizations
  const auto& optimized = add_synthetic_nodes_to_graph(
      *res_table, style_info, directly_reachable_styles, ambiguous_styles);
  auto new_styles_modifications =
      get_graph_diffs(style_info, optimized, ambiguous_styles);

  res_table->add_styles(new_styles_modifications, resource_files);
  res_table = resources->load_res_table();
  res_table->apply_attribute_removals_and_additions(new_styles_modifications,
                                                    resource_files);
  res_table = resources->load_res_table();
  // This updates a style's parent and add attributes to the current resource
  res_table->apply_style_merges(new_styles_modifications, resource_files);

  res_table = resources->load_res_table();
  style_info = res_table->load_style_info();

  // Removal and Hoisting Operations
  const auto& optimized_style_graph = get_optimized_graph(
      style_info, ambiguous_styles, directly_reachable_styles);

  std::vector<resources::StyleModificationSpec::Modification> modifications =
      get_graph_diffs(style_info, optimized_style_graph, ambiguous_styles);

  res_table->apply_attribute_removals_and_additions(modifications,
                                                    resource_files);

  res_table = resources->load_res_table();
  style_info = res_table->load_style_info();

  // Merging optimization
  const auto& resources_to_merge = get_resources_to_merge(
      style_info, ambiguous_styles, directly_reachable_styles);
  const auto& merging_modifications =
      get_style_merging_modifications(style_info, resources_to_merge);
  res_table->apply_style_merges(merging_modifications, resource_files);

  if (traceEnabled(RES, 5)) {
    StyleAnalysis style_analysis_end(apk_dir, conf.get_global_config(), options,
                                     stores, UnorderedSet<uint32_t>());
    TRACE(RES, 5, "%s", style_analysis_end.dot(false, true).c_str());
  }
}

/**
 * Helper method to find a style resource for a given resource ID.
 * Returns nullopt if the resource doesn't exist or has multiple style
 * resources.
 */
std::optional<const resources::StyleResource>
ResourceValueMergingPass::find_style_resource(
    uint32_t resource_id, const resources::StyleMap& style_map) {
  auto style_it = style_map.find(resource_id);
  if (style_it == style_map.end()) {
    return std::nullopt;
  }

  const auto& style_resources = style_it->second;
  if (style_resources.size() != 1) {
    return std::nullopt;
  }

  return style_resources[0];
}

std::optional<resources::StyleResource::Value>
ResourceValueMergingPass::get_common_attribute_among_children(
    const UnorderedSet<uint32_t>& resource_ids,
    uint32_t attribute_id,
    const resources::StyleMap& style_map) {

  if (resource_ids.empty()) {
    return std::nullopt;
  }

  std::vector<resources::StyleResource::Value> values;
  for (const auto& resource_id : UnorderedIterable(resource_ids)) {
    const auto& style_resource_opt =
        find_style_resource(resource_id, style_map);
    if (!style_resource_opt.has_value()) {
      return std::nullopt;
    }

    const auto& style_resource = style_resource_opt.value();
    auto attr_it = style_resource.attributes.find(attribute_id);
    if (attr_it == style_resource.attributes.end()) {
      return std::nullopt;
    }

    values.push_back(attr_it->second);
  }

  if (values.empty()) {
    return std::nullopt;
  }

  resources::StyleResource::Value common_value = values[0];
  for (size_t value_idx = 1; value_idx < values.size(); value_idx++) {
    if (!(common_value == values[value_idx])) {
      return std::nullopt;
    }
  }

  return common_value;
}

OptimizableResources ResourceValueMergingPass::get_resource_optimization(
    const resources::StyleInfo& style_info,
    const UnorderedSet<uint32_t>& ambiguous_styles,
    const UnorderedSet<uint32_t>& directly_reachable_styles) {
  OptimizableResources optimizable_candidates;
  auto root_vertices = style_info.get_roots();

  for (const auto& vertex : UnorderedIterable(root_vertices)) {
    find_resource_optimization_candidates(
        vertex, style_info, optimizable_candidates, ambiguous_styles);
  }
  return remove_unoptimizable_resources(optimizable_candidates,
                                        directly_reachable_styles);
}

OptimizableResources ResourceValueMergingPass::remove_unoptimizable_resources(
    const OptimizableResources& optimizable_candidates,
    const UnorderedSet<uint32_t>& directly_reachable_styles) {
  OptimizableResources optimizable_resources;

  for (const auto& [resource_id, attr_ids] :
       UnorderedIterable(optimizable_candidates.removals)) {
    if (directly_reachable_styles.find(resource_id) ==
        directly_reachable_styles.end()) {
      optimizable_resources.removals[resource_id] = attr_ids;
    }
  }

  for (const auto& [resource_id, attr_map] :
       UnorderedIterable(optimizable_candidates.additions)) {
    if (directly_reachable_styles.find(resource_id) ==
        directly_reachable_styles.end()) {
      optimizable_resources.additions[resource_id] = attr_map;
    }
  }

  return optimizable_resources;
}

ResourceAttributeInformation get_common_attributes(
    const std::vector<ResourceAttributeInformation>& attributes) {
  if (attributes.empty()) {
    return ResourceAttributeInformation();
  }

  ResourceAttributeInformation common_attributes = attributes[0];

  for (size_t attribute_idx = 1; attribute_idx < attributes.size();
       attribute_idx++) {
    ResourceAttributeInformation intersection;
    for (const auto& item : UnorderedIterable(attributes[attribute_idx])) {
      if (common_attributes.find(item) != common_attributes.end()) {
        intersection.insert(item);
      }
    }
    common_attributes = intersection;
  }
  return common_attributes;
}

/**
 * Used to track and store common attributes that exist
 * across all style definitions for the same resource ID.
 * These resources will only process unambiguous styles.
 */
ResourceAttributeInformation ResourceValueMergingPass::get_resource_attributes(
    uint32_t resource_id, const resources::StyleMap& style_map) {
  ResourceAttributeInformation attributes;

  const auto& style_resource_opt = find_style_resource(resource_id, style_map);
  if (!style_resource_opt.has_value()) {
    return attributes;
  }

  const auto& style_resource = style_resource_opt.value();
  for (const auto& attr_pair : style_resource.attributes) {
    attributes.insert(attr_pair.first);
  }

  return attributes;
}

ResourceAttributeInformation
ResourceValueMergingPass::get_common_attributes_between_resources(
    const std::vector<uint32_t>& resource_ids,
    const resources::StyleInfo& style_info) {
  std::vector<ResourceAttributeInformation> attr_id_pairs;
  attr_id_pairs.reserve(resource_ids.size());
  for (const auto& resource_id : resource_ids) {
    attr_id_pairs.push_back(
        get_resource_attributes(resource_id, style_info.styles));
  }

  return get_common_attributes(attr_id_pairs);
}

/**
 * Resources are eligible for optimization if they meet specific criteria:
 *
 For deletion candidates:
 * - Attributes that are common across a parent style and all of its children
 * - These attributes can be safely deleted from the parent since they're
 * already defined in all children
 *
 * For hoisted candidates:
 * - Attributes that are common across all children of a parent style
 * - These attributes have identical values in all children
 * - These can be "pulled up" and hoisted into the parent style
 *
 * The optimization process analyzes the style hierarchy graph:
 * - Starting from root styles (those with no incoming edges)
 * - Traversing down to identify common attributes
 * - Marking attributes for either deletion or hoisted based on value equality
 *
 * @return Returns the set of attribute IDs that are defined in the current
 * style resource. This is used by parent nodes to determine which attributes
 * are common across the style hierarchy.
 */
ResourceAttributeInformation
ResourceValueMergingPass::find_resource_optimization_candidates(
    resources::StyleInfo::vertex_t vertex,
    const resources::StyleInfo& style_info,
    OptimizableResources& optimizable_candidates,
    const UnorderedSet<uint32_t>& ambiguous_styles) {
  uint32_t resource_id = style_info.graph[vertex].id;

  if (ambiguous_styles.find(resource_id) != ambiguous_styles.end()) {
    return ResourceAttributeInformation();
  }

  ResourceAttributeInformation resources_common_attributes =
      get_resource_attributes(resource_id, style_info.styles);

  auto children_count = boost::out_degree(vertex, style_info.graph);
  if (children_count == 0u) {
    return resources_common_attributes;
  }

  std::vector<ResourceAttributeInformation> child_attributes;
  UnorderedSet<uint32_t> children_resource_ids;

  for (const auto& edge :
       boost::make_iterator_range(boost::out_edges(vertex, style_info.graph))) {
    auto target_vertex = boost::target(edge, style_info.graph);
    const auto& child_attr = find_resource_optimization_candidates(
        target_vertex, style_info, optimizable_candidates, ambiguous_styles);
    child_attributes.push_back(child_attr);
    children_resource_ids.insert(style_info.graph[target_vertex].id);
  }

  const auto& common_child_attributes = get_common_attributes(child_attributes);
  ResourceAttributeInformation optimized_attributes;

  // These attributes are common across all children and their parent (current
  // node), and the attribute in the parent can be deleted.
  for (const auto& attr_id : UnorderedIterable(resources_common_attributes)) {
    if (common_child_attributes.find(attr_id) !=
        common_child_attributes.end()) {
      optimizable_candidates.removals[resource_id].insert(attr_id);
      optimized_attributes.insert(attr_id);
    }
  }

  // These are attributes that are common across all children and that can
  // potentially be hoisted into their parent.
  for (const auto& attr_id : UnorderedIterable(common_child_attributes)) {
    const auto& common_value = get_common_attribute_among_children(
        children_resource_ids, attr_id, style_info.styles);
    if (optimized_attributes.find(attr_id) == optimized_attributes.end() &&
        common_value.has_value()) {
      optimizable_candidates.additions[resource_id].insert(
          {attr_id, common_value.value()});
    }
  }

  return resources_common_attributes;
}

void ResourceValueMergingPass::remove_attribute_from_descendent(
    uint32_t resource_id,
    const UnorderedMap<uint32_t, resources::StyleResource::Value>& attr_map,
    const resources::StyleInfo& optimized,
    UnorderedMap<uint32_t, ResourceAttributeInformation>& removals) {
  const auto& vertex_find = optimized.id_to_vertex.find(resource_id);
  always_assert(vertex_find != optimized.id_to_vertex.end());
  auto vertex = vertex_find->second;

  for (const auto& edge :
       boost::make_iterator_range(boost::out_edges(vertex, optimized.graph))) {
    auto child_vertex = boost::target(edge, optimized.graph);
    uint32_t child_resource_id = optimized.graph[child_vertex].id;
    for (const auto& [attr_id, _] : UnorderedIterable(attr_map)) {
      removals[child_resource_id].insert(attr_id);
    }
  }
}

resources::StyleInfo ResourceValueMergingPass::get_optimized_graph(
    const resources::StyleInfo& initial,
    const UnorderedSet<uint32_t>& ambiguous_styles,
    const UnorderedSet<uint32_t>& directly_reachable_styles) {
  resources::StyleInfo optimized(initial);
  OptimizableResources optimized_resources;
  int iteration = 0;

  do {
    optimized_resources = get_resource_optimization(optimized, ambiguous_styles,
                                                    directly_reachable_styles);

    for (const auto& [resource_id, attr_map] :
         UnorderedIterable(optimized_resources.additions)) {

      remove_attribute_from_descendent(resource_id, attr_map, optimized,
                                       optimized_resources.removals);
    }

    apply_removals_to_style_graph(optimized, optimized_resources.removals);
    apply_additions_to_style_graph(optimized, optimized_resources.additions);

    iteration++;
  } while ((!optimized_resources.removals.empty() ||
            !optimized_resources.additions.empty()) &&
           iteration < MAX_STYLES_DEPTH);

  return optimized;
}

std::vector<std::vector<uint32_t>>
ResourceValueMergingPass::get_cost_effective_synthetic_style_opportunities(
    const std::vector<std::vector<uint32_t>>& siblings,
    const resources::StyleInfo& style_info,
    uint32_t config_count) {
  std::vector<std::vector<uint32_t>> synthetic_styles;

  for (const auto& sibling : siblings) {
    auto common_attributes =
        get_common_attributes_between_resources(sibling, style_info);
    uint32_t synthetic_style_cost = get_cost_of_synthetic_style(
        config_count, static_cast<uint32_t>(common_attributes.size()));
    if (should_create_synthetic_resources(
            synthetic_style_cost + 24,
            static_cast<uint32_t>(sibling.size()),
            static_cast<uint32_t>(common_attributes.size()))) {
      synthetic_styles.push_back(sibling);
    }
  }

  return synthetic_styles;
}

resources::StyleInfo ResourceValueMergingPass::add_synthetic_nodes_to_graph(
    ResourceTableFile& res_table,
    const resources::StyleInfo& initial,
    const UnorderedSet<uint32_t>& directly_reachable_styles,
    const UnorderedSet<uint32_t>& ambiguous_styles) {
  resources::StyleInfo optimized(initial);
  size_t iteration = 0;
  size_t iterations = initial.get_roots().size();
  std::vector<std::vector<uint32_t>> siblings_to_optimize;
  siblings_to_optimize.reserve(iterations);

  auto config_count = get_config_count(res_table);

  std::vector<std::vector<uint32_t>> intra_graph_opportunities =
      find_intra_graph_hoistings(optimized, directly_reachable_styles,
                                 ambiguous_styles);

  siblings_to_optimize = get_cost_effective_synthetic_style_opportunities(
      intra_graph_opportunities, optimized, config_count);
  introduce_synthetic_resources(optimized, siblings_to_optimize);

  do {
    siblings_to_optimize.clear();
    auto inter_graph_opportunities =
        find_inter_graph_hoistings(optimized, ambiguous_styles);

    siblings_to_optimize = get_cost_effective_synthetic_style_opportunities(
        {inter_graph_opportunities}, optimized, config_count);

    introduce_synthetic_resources(optimized, siblings_to_optimize);

    iteration++;
  } while (!siblings_to_optimize.empty() && iteration < iterations);

  return optimized;
}

void ResourceValueMergingPass::apply_additions_to_style_graph(
    resources::StyleInfo& style_info,
    const UnorderedMap<uint32_t,
                       UnorderedMap<uint32_t, resources::StyleResource::Value>>&
        additions) {
  for (const auto& [resource_id, attr_map] : UnorderedIterable(additions)) {
    auto style_it = style_info.styles.find(resource_id);
    always_assert(style_it != style_info.styles.end());

    auto& style_resources = style_it->second;

    // There should only be one style resource per resource ID based on the fact
    // that optimizations only occur on unambiguous styles.
    auto& style_resource = only(style_resources);
    for (const auto& [attr_id, value] : UnorderedIterable(attr_map)) {
      style_resource.attributes.insert({attr_id, value});
    }
  }
}

void ResourceValueMergingPass::apply_removals_to_style_graph(
    resources::StyleInfo& style_info,
    UnorderedMap<uint32_t, ResourceAttributeInformation> removals) {
  for (const auto& [resource_id, attr_ids] : UnorderedIterable(removals)) {

    auto style_it = style_info.styles.find(resource_id);
    always_assert(style_it != style_info.styles.end());

    auto& style_resources = style_it->second;

    auto& style_resource = only(style_resources);

    for (const auto& attr_id : UnorderedIterable(attr_ids)) {
      auto attr_it = style_resource.attributes.find(attr_id);
      always_assert(attr_it != style_resource.attributes.end());
      style_resource.attributes.erase(attr_it);
    }
  }
}

// Implements a set difference (A - B) = {x | x ∈ A and x ∉ B}
UnorderedMap<uint32_t, resources::StyleResource::Value>
find_attribute_differences(const StyleResource& A, const StyleResource& B) {
  UnorderedMap<uint32_t, resources::StyleResource::Value> diff_attrs;

  // x ∈ A
  for (const auto& [attr_id, value] : UnorderedIterable(A.attributes)) {
    // x ∈ B
    bool is_in_B = B.attributes.find(attr_id) != B.attributes.end();

    if (!is_in_B) {
      diff_attrs.insert({attr_id, value});
    }
  }

  return diff_attrs;
}

void handle_new_resource(
    uint32_t resource_id,
    const StyleResource& resource,
    std::vector<StyleModificationSpec::Modification>& modifications) {
  modifications.emplace_back(resource_id);

  UnorderedMap<uint32_t, StyleResource::Value> parent_attrs;
  for (const auto& [attr_id, value] : UnorderedIterable(resource.attributes)) {
    parent_attrs.insert({attr_id, value});
  }
  modifications.emplace_back(resource_id, resource.parent,
                             std::move(parent_attrs));
}

void handle_modified_resource(
    uint32_t resource_id,
    const StyleResource& initial_resource,
    const StyleResource& optimized_resource,
    std::vector<StyleModificationSpec::Modification>& modifications) {

  const auto removal_attrs =
      find_attribute_differences(initial_resource, optimized_resource);
  for (const auto& [attr_id, _] : UnorderedIterable(removal_attrs)) {
    modifications.emplace_back(resource_id, attr_id);
  }

  const auto addition_attrs =
      find_attribute_differences(optimized_resource, initial_resource);
  for (const auto& [attr_id, value] : UnorderedIterable(addition_attrs)) {
    modifications.emplace_back(resource_id, attr_id, value);
  }

  // Values that exist in initial and optimized but have different values.
  // Changed values are represented as a deletion of the attribute followed by
  // an addition of the same attribute with the updated value.
  for (const auto& [attr_id, initial_value] :
       UnorderedIterable(initial_resource.attributes)) {
    const auto& optimized_attr_it = optimized_resource.attributes.find(attr_id);
    if (optimized_attr_it == optimized_resource.attributes.end()) {
      continue;
    }

    const auto& optimized_value = optimized_attr_it->second;
    if (!(initial_value == optimized_value)) {
      modifications.emplace_back(resource_id, attr_id);
      modifications.emplace_back(resource_id, attr_id, optimized_value);
    }
  }

  // Add parent modification
  if (initial_resource.parent != optimized_resource.parent) {
    modifications.emplace_back(resource_id, optimized_resource.parent,
                               UnorderedMap<uint32_t, StyleResource::Value>());
  }
}

std::vector<resources::StyleModificationSpec::Modification>
ResourceValueMergingPass::get_graph_diffs(
    const StyleInfo& initial,
    const StyleInfo& optimized,
    const UnorderedSet<uint32_t>& ambiguous_styles) {
  std::vector<StyleModificationSpec::Modification> modifications;

  UnorderedSet<uint32_t> all_resource_ids;

  for (const auto& [resource_id, _] : UnorderedIterable(optimized.styles)) {
    if (ambiguous_styles.find(resource_id) == ambiguous_styles.end()) {
      all_resource_ids.insert(resource_id);
    }
  }

  for (const auto& resource_id : UnorderedIterable(all_resource_ids)) {
    const auto initial_it = initial.styles.find(resource_id);
    const auto optimized_it = optimized.styles.find(resource_id);

    const bool exists_in_initial = initial_it != initial.styles.end();
    const bool exists_in_optimized = optimized_it != optimized.styles.end();

    always_assert_log(
        !exists_in_initial || exists_in_optimized,
        "Resource 0x%x was deleted in optimized graph but is found in "
        "initial graph which should not be possible",
        resource_id);

    if (!exists_in_initial && exists_in_optimized) {
      handle_new_resource(resource_id, optimized_it->second[0], modifications);
    } else if (exists_in_initial && exists_in_optimized) {
      handle_modified_resource(resource_id, initial_it->second[0],
                               optimized_it->second[0], modifications);
    }
  }

  return modifications;
}

void ResourceValueMergingPass::find_resources_to_merge(
    resources::StyleInfo::vertex_t vertex,
    const resources::StyleInfo& style_info,
    const UnorderedSet<uint32_t>& ambiguous_styles,
    const UnorderedSet<uint32_t>& directly_reachable_styles,
    std::vector<std::vector<uint32_t>>& resources_to_merge) {

  auto children_count = boost::out_degree(vertex, style_info.graph);
  uint32_t resource_id = style_info.graph[vertex].id;

  if (children_count == 0 ||
      ambiguous_styles.find(resource_id) != ambiguous_styles.end()) {
    return;
  }

  std::vector<uint32_t> merges;
  resources::StyleInfo::vertex_t current_vertex = vertex;

  // Find chains of single-child resources that can be merged
  const auto& children_resource_ids = style_info.get_children(resource_id);
  uint32_t child_resource_id = children_resource_ids[0];

  while (children_count == 1 &&
         directly_reachable_styles.find(resource_id) ==
             directly_reachable_styles.end() &&
         ambiguous_styles.find(resource_id) == ambiguous_styles.end() &&
         ambiguous_styles.find(child_resource_id) == ambiguous_styles.end()) {
    merges.push_back(resource_id);
    auto out_edges = boost::out_edges(current_vertex, style_info.graph);
    current_vertex = boost::target(*out_edges.first, style_info.graph);
    resource_id = style_info.graph[current_vertex].id;
    children_count = boost::out_degree(current_vertex, style_info.graph);

    if (children_count == 0) {
      break;
    }

    child_resource_id = style_info.get_children(resource_id)[0];
  }

  if (!merges.empty()) {
    resources_to_merge.push_back(std::move(merges));
  }

  for (uint32_t child_id : style_info.get_children(resource_id)) {
    auto child_vertex = style_info.id_to_vertex.at(child_id);
    find_resources_to_merge(child_vertex, style_info, ambiguous_styles,
                            directly_reachable_styles, resources_to_merge);
  }
}

std::vector<std::vector<uint32_t>>
ResourceValueMergingPass::get_resources_to_merge(
    const resources::StyleInfo& style_info,
    const UnorderedSet<uint32_t>& ambiguous_styles,
    const UnorderedSet<uint32_t>& directly_reachable_styles) {
  std::vector<std::vector<uint32_t>> merging_resource_pairs;
  auto root_vertices = style_info.get_roots();

  for (const auto& vertex : UnorderedIterable(root_vertices)) {
    find_resources_to_merge(vertex, style_info, ambiguous_styles,
                            directly_reachable_styles, merging_resource_pairs);
  }

  return merging_resource_pairs;
}

resources::StyleModificationSpec::Modification
ResourceValueMergingPass::get_parent_and_attribute_modifications_for_merging(
    const resources::StyleInfo& style_info,
    const std::vector<uint32_t>& resources_to_merge) {
  UnorderedMap<uint32_t, resources::StyleResource::Value> new_attributes;
  always_assert(!resources_to_merge.empty());

  auto chain_parent_id_opt =
      style_info.get_unambiguous_parent(resources_to_merge[0]);
  always_assert_log(chain_parent_id_opt.has_value(),
                    "Parent ID not found for resource 0x%x",
                    resources_to_merge[0]);
  uint32_t chain_parent_id = chain_parent_id_opt.value();

  // The elements in the chain are ordered from parent to child in the style
  // hierarchy
  for (const auto& resource_id : resources_to_merge) {
    const auto& style_resource_opt =
        find_style_resource(resource_id, style_info.styles);
    always_assert_log(style_resource_opt.has_value(), "Resource 0x%x not found",
                      resource_id);

    const auto& style_resource = style_resource_opt.value();
    for (const auto& [attr_id, value] : style_resource.attributes) {
      // Remove any attributes that are already defined then add again because
      // [] operator does not work since resources::StyleResource::Value does
      // not have a default constructor
      auto it = new_attributes.find(attr_id);
      if (it != new_attributes.end()) {
        new_attributes.erase(it);
      }
      new_attributes.insert({attr_id, value});
    }
  }

  auto tail_resource_id = resources_to_merge.back();
  auto final_resource_ids = style_info.get_children(tail_resource_id);
  always_assert_log(final_resource_ids.size() == 1,
                    "Expected exactly one child for resource 0x%x",
                    tail_resource_id);

  // This is the destination resource ID where all attributes from the chain
  // of resources will be merged into - it's the final target of the merging
  // operation
  auto destination_resource_id = final_resource_ids[0];

  return resources::StyleModificationSpec::Modification(
      destination_resource_id, chain_parent_id, std::move(new_attributes));
}

std::vector<resources::StyleModificationSpec::Modification>
ResourceValueMergingPass::get_style_merging_modifications(
    const resources::StyleInfo& style_info,
    const std::vector<std::vector<uint32_t>>& resources_to_merge) {
  std::vector<resources::StyleModificationSpec::Modification> modifications;
  modifications.reserve(resources_to_merge.size());

  for (const auto& merging_resource_pair : resources_to_merge) {
    modifications.emplace_back(
        get_parent_and_attribute_modifications_for_merging(
            style_info, merging_resource_pair));
  }

  return modifications;
}

uint32_t ResourceValueMergingPass::get_cost_of_synthetic_style(
    uint32_t num_configs, uint32_t num_attributes) {
  // All sizes in bytes
  uint32_t res_table_entry_size = sizeof(android::ResTable_map_entry);
  uint32_t new_flags_size = 4;
  uint32_t offset_size = sizeof(uint32_t) * num_configs;
  uint32_t attributes_size = num_attributes * sizeof(android::ResTable_map);
  return res_table_entry_size + new_flags_size + offset_size + attributes_size;
}

bool ResourceValueMergingPass::should_create_synthetic_resources(
    uint32_t synthetic_style_cost,
    uint32_t num_resources_with_all_attributes,
    uint32_t num_attributes) {
  // If creating a synthetic style is more cost-effective than having multiple
  // copies of each attribute, then proceed with creating the synthetic style
  return synthetic_style_cost <
         (num_resources_with_all_attributes * num_attributes *
          static_cast<uint32_t>(sizeof(android::ResTable_map)));
}

uint32_t ResourceValueMergingPass::get_config_count(
    ResourceTableFile& res_table) {
  uint32_t config_count = 0;

  size_t package_count = res_table.package_count();

  always_assert_log(package_count == 1,
                    "Expected exactly one package, but found %zu",
                    package_count);

  uint32_t package_id = APPLICATION_PACKAGE;

  std::vector<std::string> type_names;
  res_table.get_type_names(&type_names);

  for (const auto& type_name : type_names) {
    if (type_name != "style") {
      continue;
    }

    std::vector<android::ResTable_config> configs;
    res_table.get_configurations(package_id, type_name, &configs);

    config_count += configs.size();
  }
  return config_count;
}

std::vector<std::vector<uint32_t>>
ResourceValueMergingPass::find_intra_graph_hoistings(
    const resources::StyleInfo& style_info,
    const UnorderedSet<uint32_t>& directly_reachable_styles,
    const UnorderedSet<uint32_t>& ambiguous_styles) {
  OptimizableResources optimizable_candidates;
  const auto& root_vertices = style_info.get_roots();

  for (const auto& vertex : UnorderedIterable(root_vertices)) {
    find_resource_optimization_candidates(
        vertex, style_info, optimizable_candidates, ambiguous_styles);
  }

  UnorderedMap<uint32_t,
               UnorderedMap<uint32_t, resources::StyleResource::Value>>
      directly_reachable_hoistings;
  for (const auto& [resource_id, attr_map] :
       UnorderedIterable(optimizable_candidates.additions)) {
    if (directly_reachable_styles.find(resource_id) !=
        directly_reachable_styles.end()) {
      directly_reachable_hoistings.insert({resource_id, attr_map});
    }
  }

  // Only hoist attributes to the parent from children that are not ambiguous.
  // `directly_reachable_hoistings` is an UnorderedMap, and the order these
  // groups are emitted in decides which synthetic resource id each one draws
  // from the counter in `get_new_resource_id()`. Emit in resource-id order so
  // that assignment is the same on every run.
  std::vector<std::vector<uint32_t>> valid_hoistings;
  for (uint32_t resource_id :
       unordered_to_ordered_keys(directly_reachable_hoistings)) {
    bool all_children_valid = true;

    for (const auto& child_id : style_info.get_children(resource_id)) {
      if (ambiguous_styles.find(child_id) != ambiguous_styles.end()) {
        all_children_valid = false;
        break;
      }
    }

    if (all_children_valid) {
      valid_hoistings.push_back(style_info.get_children(resource_id));
    }
  }

  return valid_hoistings;
}

UnorderedMap<uint32_t, resources::StyleResource::Value>
ResourceValueMergingPass::get_hoistable_attributes(
    const std::vector<uint32_t>& resource_ids,
    const resources::StyleInfo& style_info) {
  if (resource_ids.empty()) {
    return {};
  }

  auto common_attributes =
      get_common_attributes_between_resources(resource_ids, style_info);
  UnorderedMap<uint32_t, resources::StyleResource::Value> hoistable_attributes;
  UnorderedSet<uint32_t> resource_ids_set(resource_ids.begin(),
                                          resource_ids.end());

  for (const auto& attr_id : UnorderedIterable(common_attributes)) {
    auto common_value = get_common_attribute_among_children(
        resource_ids_set, attr_id, style_info.styles);
    if (common_value.has_value()) {
      hoistable_attributes.insert({attr_id, common_value.value()});
    }
  }
  return hoistable_attributes;
}

std::vector<uint32_t> ResourceValueMergingPass::find_best_hoisting_combination(
    const std::vector<uint32_t>& valid_roots,
    const resources::StyleInfo& style_info) {
  if (valid_roots.size() < 2) {
    return {};
  }

  std::vector<uint32_t> best_combination;
  uint32_t best_savings = 0;

  for (size_t i = 0; i < valid_roots.size(); ++i) {
    for (size_t j = i + 1; j < valid_roots.size(); ++j) {
      std::vector<uint32_t> candidate_pair = {valid_roots[i], valid_roots[j]};
      const auto& hoistable_attributes =
          get_hoistable_attributes(candidate_pair, style_info);
      uint32_t savings = static_cast<uint32_t>(hoistable_attributes.size() *
                                               candidate_pair.size());

      if (savings > best_savings) {
        best_savings = savings;
        best_combination = std::move(candidate_pair);
      }
    }
  }

  if (best_combination.empty()) {
    return {};
  }

  UnorderedSet<uint32_t> used_resources(best_combination.begin(),
                                        best_combination.end());

  bool improvement_found;
  do {
    improvement_found = false;
    uint32_t best_candidate_id = 0;
    uint32_t best_candidate_savings = best_savings;

    for (uint32_t candidate_id : valid_roots) {
      if (used_resources.find(candidate_id) != used_resources.end()) {
        continue;
      }

      best_combination.push_back(candidate_id);

      const auto& hoistable_attributes =
          get_hoistable_attributes(best_combination, style_info);
      uint32_t candidate_savings = static_cast<uint32_t>(
          hoistable_attributes.size() * best_combination.size());

      if (candidate_savings > best_candidate_savings) {
        best_candidate_id = candidate_id;
        best_candidate_savings = candidate_savings;
        improvement_found = true;
      }
      best_combination.pop_back();
    }

    if (improvement_found) {
      best_combination.push_back(best_candidate_id);
      used_resources.insert(best_candidate_id);
      best_savings = best_candidate_savings;
    }
  } while (improvement_found);

  return best_combination;
}

std::vector<uint32_t> ResourceValueMergingPass::find_inter_graph_hoistings(
    const resources::StyleInfo& style_info,
    const UnorderedSet<uint32_t>& ambiguous_styles) {
  auto root_vertices = style_info.get_roots();
  std::vector<uint32_t> valid_roots;
  valid_roots.reserve(root_vertices.size());

  for (const auto& vertex : UnorderedIterable(root_vertices)) {
    auto resource_id = style_info.graph[vertex].id;
    if (ambiguous_styles.find(resource_id) != ambiguous_styles.end()) {
      continue;
    }

    auto style_resource_opt =
        find_style_resource(resource_id, style_info.styles);
    always_assert_log(style_resource_opt.has_value(), "Resource 0x%x not found",
                      resource_id);

    if (style_resource_opt->parent == 0 &&
        style_info.get_depth(resource_id) < MAX_STYLES_DEPTH) {
      valid_roots.push_back(resource_id);
    }
  }

  // `get_roots()` is an UnorderedSet, so `valid_roots` arrives in hash order --
  // and `find_best_hoisting_combination` breaks ties with a strict `>`, so the
  // first-encountered maximum wins. That makes the SET it returns, not merely
  // its order, depend on iteration order. Sort by resource id so equal-savings
  // ties resolve the same way on every run.
  std::sort(valid_roots.begin(), valid_roots.end());
  return find_best_hoisting_combination(valid_roots, style_info);
}

uint32_t ResourceValueMergingPass::get_common_parent(
    const std::vector<uint32_t>& children,
    const resources::StyleInfo& style_info) {
  UnorderedSet<uint32_t> parent_ids;

  for (const auto& child_id : children) {
    const auto parent_opt = style_info.get_unambiguous_parent(child_id);
    always_assert_log(parent_opt.has_value(), "Parent not found for child 0x%x",
                      child_id);
    parent_ids.insert(parent_opt.value());
  }

  if (parent_ids.size() != 1) {
    std::ostringstream children_debug_str;
    for (const auto& child_id : children) {
      children_debug_str << "0x" << std::hex << child_id << " ";
    }

    always_assert_log(
        parent_ids.size() == 1,
        "Expected exactly one parent for children %s, received %zu",
        children_debug_str.str().c_str(), parent_ids.size());
  }

  const uint32_t parent_id = *unordered_any(parent_ids);
  if (parent_id != 0) {
    always_assert_log(style_info.id_to_vertex.find(parent_id) !=
                          style_info.id_to_vertex.end(),
                      "Parent vertex not found for parent 0x%x", parent_id);
  }

  return parent_id;
}

uint32_t ResourceValueMergingPass::create_synthetic_resource_node(
    resources::StyleInfo& style_info, uint32_t original_parent_id) {
  const uint32_t synthetic_resource_id = style_info.get_new_resource_id();

  const auto synthetic_vertex = boost::add_vertex(
      resources::StyleInfo::Node{synthetic_resource_id}, style_info.graph);

  style_info.id_to_vertex.insert({synthetic_resource_id, synthetic_vertex});

  resources::StyleResource synthetic_style;
  synthetic_style.id = synthetic_resource_id;
  synthetic_style.parent = original_parent_id;
  style_info.styles.insert({synthetic_resource_id, {synthetic_style}});

  if (original_parent_id != 0) {
    const auto& parent_vertex = style_info.id_to_vertex.at(original_parent_id);
    boost::add_edge(parent_vertex, synthetic_vertex, style_info.graph);
  }
  return synthetic_resource_id;
}

void ResourceValueMergingPass::update_parent(StyleInfo& style_info,
                                             uint32_t resource_id,
                                             uint32_t new_parent_id) {
  auto style_resource_opt = find_style_resource(resource_id, style_info.styles);
  always_assert_log(style_resource_opt.has_value(), "Resource 0x%x not found",
                    resource_id);

  auto style_it = style_info.styles.find(resource_id);
  always_assert(style_it != style_info.styles.end());

  auto& style_resources = style_it->second;

  auto old_parent_id = style_resource_opt->parent;
  if (old_parent_id != 0) {
    auto old_parent_vertex = style_info.id_to_vertex.at(old_parent_id);
    auto current_vertex = style_info.id_to_vertex.at(resource_id);

    if (auto [edge, exists] =
            boost::edge(old_parent_vertex, current_vertex, style_info.graph);
        exists) {
      boost::remove_edge(edge, style_info.graph);
    }
  }

  if (new_parent_id != 0) {
    auto new_parent_vertex = style_info.id_to_vertex.at(new_parent_id);
    auto current_vertex = style_info.id_to_vertex.at(resource_id);
    boost::add_edge(new_parent_vertex, current_vertex, style_info.graph);
  }

  style_resources[0].parent = new_parent_id;
}

uint32_t ResourceValueMergingPass::introduce_synthetic_resource(
    resources::StyleInfo& style_info, const std::vector<uint32_t>& children) {
  always_assert_log(!children.empty(),
                    "Cannot create synthetic resource with no children");

  const uint32_t original_parent_id = get_common_parent(children, style_info);

  const uint32_t synthetic_resource_id =
      create_synthetic_resource_node(style_info, original_parent_id);

  // Update edges children from the original parent to the synthetic resource

  for (const auto& child_id : children) {
    update_parent(style_info, child_id, synthetic_resource_id);
  }

  auto hoistable_attributes = get_hoistable_attributes(children, style_info);
  UnorderedMap<uint32_t,
               UnorderedMap<uint32_t, resources::StyleResource::Value>>
      parent_additions{{synthetic_resource_id, hoistable_attributes}};
  UnorderedMap<uint32_t, ResourceAttributeInformation> children_removals;

  remove_attribute_from_descendent(synthetic_resource_id, hoistable_attributes,
                                   style_info, children_removals);

  apply_additions_to_style_graph(style_info, parent_additions);
  apply_removals_to_style_graph(style_info, children_removals);
  return synthetic_resource_id;
}

void ResourceValueMergingPass::introduce_synthetic_resources(
    resources::StyleInfo& style_info,
    const std::vector<std::vector<uint32_t>>& synthetic_style_children) {
  for (const auto& children : synthetic_style_children) {
    introduce_synthetic_resource(style_info, children);
  }
}

static ResourceValueMergingPass s_pass;
