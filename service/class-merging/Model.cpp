/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "Model.h"

#include <ostream>
#include <sstream>
#include <string>

#include "AnnoUtils.h"
#include "ApproximateShapeMerging.h"
#include "ConfigFiles.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "MergeabilityCheck.h"
#include "MergingStrategies.h"
#include "MethodUtil.h"
#include "PassManager.h"
#include "RefChecker.h"
#include "Resolver.h"
#include "Show.h"

using namespace class_merging;

namespace {

// A VirtualScope member is a usable virtual-dispatch target only if it is a
// real def (a synthetic miranda placeholder is not) and, for internal methods,
// is not abstract. External methods are treated as usable -- is_abstract() /
// get_access() assert is_def(), so they must be guarded behind !is_external().
bool is_usable_dispatch_target(const DexMethod* m) {
  return m->is_def() && (m->is_external() || !is_abstract(m));
}

std::string to_string(const ModelSpec& spec) {
  std::ostringstream ss;
  ss << spec.name << "(roots: ";
  for (const auto* const root : spec.roots) {
    ss << SHOW(root);
  }
  ss << ", exclude: " << spec.exclude_types.size()
     << ", prefix: " << spec.class_name_prefix
     << ", gen roots: " << spec.gen_types.size() << ")";
  return ss.str();
}

void load_generated_types(const ModelSpec& spec,
                          const Scope& scope,
                          const TypeSystem& type_system,
                          const ConstTypeHashSet& models,
                          TypeSet& generated) {
  if (spec.is_generated_code) {
    insert_unordered_iterable(generated, models);
  }
  for (const auto& type : UnorderedIterable(spec.gen_types)) {
    const auto& cls = type_class(type);
    redex_assert(cls != nullptr);
    generated.insert(type);
    if (is_interface(cls)) {
      const auto& impls = type_system.get_implementors(type);
      generated.insert(impls.begin(), impls.end());
    } else {
      type_system.get_all_children(type, generated);
    }
  }
  if (!spec.gen_annos.empty()) {
    for (auto* const type : scope) {
      if (has_any_annotation(type, spec.gen_annos)) {
        generated.insert(type->get_type());
      }
    }
  }
}

/**
 * Return true if 'left' is a subset of 'right'.
 * That is every element in left is in right as well.
 */
template <class Set>
bool is_subset(const Set& left, const Set& right) {
  for (const auto& el : left) {
    if (right.count(el) == 0) {
      return false;
    }
  }
  return true;
}

void print_interface_maps(const TypeToTypeSet& intf_to_classes,
                          const ConstTypeHashSet& types) {
  auto intfs = unordered_to_ordered_keys(
      intf_to_classes, [&](const DexType* first, const DexType* second) {
        return intf_to_classes.at(first).size() <
               intf_to_classes.at(second).size();
      });
  for (const auto& intf : intfs) {
    const auto& classes = intf_to_classes.at(intf);
    TRACE(CLMG, 8, "- interface %s -> %zu", SHOW(intf), classes.size());
    if (classes.size() <= 5) {
      for (const auto& cls : classes) {
        TRACE(CLMG, 8, "\t-(%zu) %s", types.count(cls), SHOW(cls));
      }
    }
  }
}

/**
 * trim shapes that have the mergeable type count less than ModelSpec.min_count
 */
size_t trim_shapes(MergerType::ShapeCollector& shapes, size_t min_count) {
  size_t num_trimmed_types = 0;
  std::vector<MergerType::Shape> shapes_to_remove;
  for (const auto& shape_it : shapes) {
    if (shape_it.second.types.size() >= min_count) {
      TRACE(CLMG, 7, "Keep shape %s (%zu)", shape_it.first.to_string().c_str(),
            shape_it.second.types.size());
      continue;
    }
    shapes_to_remove.push_back(shape_it.first);
  }
  for (const auto& shape : shapes_to_remove) {
    TRACE(CLMG, 7, "Drop shape %s (%zu)", shape.to_string().c_str(),
          shapes[shape].types.size());
    num_trimmed_types += shapes[shape].types.size();
    shapes.erase(shape);
  }
  return num_trimmed_types;
}

/**
 * trim groups that have the mergeable types count less than ModelSpec.min_count
 */
size_t trim_groups(MergerType::ShapeCollector& shapes, size_t min_count) {
  size_t num_trimmed_types = 0;
  TRACE(CLMG, 5, "Trim groups with min_count %zu", min_count);
  for (auto& shape_it : shapes) {
    std::vector<TypeSet> groups_to_remove;
    for (const auto& group_it : shape_it.second.groups) {
      if (group_it.second.size() >= min_count) {
        TRACE(CLMG, 7, "Keep group (%zu) on %s", group_it.second.size(),
              shape_it.first.to_string().c_str());
        continue;
      }
      groups_to_remove.push_back(group_it.first);
    }
    for (const auto& group : groups_to_remove) {
      auto& types = shape_it.second.groups[group];
      TRACE(CLMG, 7, "Drop group (%zu) on %s", types.size(),
            shape_it.first.to_string().c_str());
      num_trimmed_types += types.size();
      for (const auto& type : types) {
        shape_it.second.types.erase(type);
      }
      shape_it.second.groups.erase(group);
    }
  }

  return num_trimmed_types;
}

} // namespace

const TypeSet Model::empty_set = TypeSet();

Model::Model(const Scope& scope,
             const DexStoresVector& stores,
             ConfigFiles& conf,
             const ModelSpec& spec,
             const TypeSystem& type_system,
             const virtual_scope::VirtualScopes& vscopes,
             const RefChecker& refchecker)
    : m_spec(spec),
      m_type_system(type_system),
      m_vscopes(vscopes),
      m_ref_checker(refchecker),
      m_scope(scope),
      m_conf(conf),
      m_x_dex(XDexRefs(stores)) {
  init(scope, spec, type_system);
}

void Model::init(const Scope& scope,
                 const ModelSpec& spec,
                 const TypeSystem& type_system) {
  build_hierarchy(spec.roots);
  for (const auto* const root : spec.roots) {
    build_interface_map(root, {});
  }
  print_interface_maps(m_intf_to_classes, m_spec.merging_targets);

  for (const auto* const root : spec.roots) {
    MergerType* root_merger = build_mergers(root);
    m_roots.push_back(root_merger);
  }

  // load all generated types and find non mergeables
  TypeSet generated;
  load_generated_types(spec, scope, type_system, m_spec.merging_targets,
                       generated);
  TRACE(CLMG, 4, "Generated types %zu", generated.size());
  exclude_types(spec.exclude_types);
  MergeabilityChecker checker(scope, spec, m_ref_checker, generated);
  m_non_mergeables = checker.get_non_mergeables();
  TRACE(CLMG, 3, "Non mergeables %zu", m_non_mergeables.size());
  m_stats.m_non_mergeables = static_cast<uint32_t>(m_non_mergeables.size());
  m_stats.m_all_types = static_cast<uint32_t>(m_spec.merging_targets.size());
  if (m_spec.hot_cold_grouping) {
    m_hot_methods = get_hot_methods(scope, m_conf);
  }
}

void Model::build_hierarchy(const TypeSet& roots) {
  for (const auto& type : UnorderedIterable(m_spec.merging_targets)) {
    if (roots.count(type) > 0) {
      continue;
    }
    auto* const cls = type_class(type);
    auto* const super = cls->get_super_class();
    redex_assert(super != nullptr);
    m_hierarchy[super].insert(type);
    m_parents[type] = super;
  }
}

void Model::build_interface_map(const DexType* type, TypeSet implemented) {
  TypeSet class_intfs = m_type_system.get_implemented_interfaces(type);
  for (const auto& impl : implemented) {
    class_intfs.erase(impl);
  }
  if (!class_intfs.empty()) {
    for (const auto* const intf : class_intfs) {
      m_class_to_intfs[type].insert(intf);
      m_intf_to_classes[intf].insert(type);
    }
    implemented.insert(class_intfs.begin(), class_intfs.end());
  }
  const auto& children = m_hierarchy.find(type);
  if (children != m_hierarchy.end()) {
    for (const auto& child : children->second) {
      build_interface_map(child, implemented);
    }
  }
}

MergerType* Model::build_mergers(const DexType* root) {
  auto& merger = create_dummy_merger(root);
  const auto& children = m_hierarchy.find(root);
  if (children != m_hierarchy.end()) {
    for (const auto& child : children->second) {
      create_dummy_mergers_if_children(child);
    }
  }
  return &merger;
}

MergerType& Model::create_dummy_merger(const DexType* type) {
  auto& merger = m_mergers[type];
  merger.type = type;
  merger.dummy = true;
  return merger;
}

void Model::create_dummy_mergers_if_children(const DexType* type) {
  if (is_excluded(type)) {
    m_excluded.insert(type);
    return;
  }
  if (m_non_mergeables.count(type) > 0) {
    return;
  }
  const auto& children = m_hierarchy.find(type);
  if (children == m_hierarchy.end()) {
    return;
  }
  create_dummy_merger(type);
  for (const auto& child : children->second) {
    create_dummy_mergers_if_children(child);
  }
}

MergerType& Model::create_merger_shape(
    const DexType* shape_type,
    const MergerType::Shape& shape,
    const DexType* parent,
    const TypeSet& intfs,
    const std::vector<const DexType*>& classes) {
  TRACE(CLMG, 7, "Create Shape %s - %s, parent %s, intfs %zu, classes %zu",
        SHOW(shape_type), shape.to_string().c_str(), SHOW(parent), intfs.size(),
        classes.size());
  auto& merger = m_mergers[shape_type];
  merger.type = shape_type;
  merger.shape = shape;
  merger.from_shape = true;

  always_assert(classes.size() > 1);
  for (const auto& cls : classes) {
    // add the class to the mergeables of this shape
    merger.mergeables.insert(cls);

    // update interface<->class maps
    for (const auto& intf : intfs) {
      auto erased = m_intf_to_classes[intf].erase(cls);
      always_assert(erased > 0);
      erased = m_class_to_intfs[cls].erase(intf);
      always_assert(erased > 0);
    }
    always_assert(m_class_to_intfs[cls].empty());
    m_class_to_intfs.erase(cls);

    // update the parent<->child relationship
    const auto& cls_parent = m_parents.find(cls);
    always_assert(cls_parent != m_parents.end());
    auto erased = m_hierarchy[cls_parent->second].erase(cls);
    always_assert(erased > 0);
    if (m_hierarchy[cls_parent->second].empty()) {
      erased = m_hierarchy.erase(cls_parent->second);
      always_assert(erased > 0);
    }
    m_parents.erase(cls_parent);
  }

  // set up type system info for the shape
  set_parent_child(parent, shape_type);
  for (const auto& intf : intfs) {
    m_intf_to_classes[intf].insert(shape_type);
    m_class_to_intfs[shape_type].insert(intf);
  }

  return merger;
}

MergerType& Model::create_merger_helper(
    const DexType* merger_type,
    const MergerType::Shape& shape,
    const TypeSet& intf_set,
    const std::optional<size_t>& dex_id,
    const ConstTypeVector& group_values,
    const std::optional<InterdexSubgroupIdx>& interdex_subgroup_idx,
    const InterdexSubgroupIdx subgroup_idx) {
  size_t group_count = m_shape_to_count[shape]++;
  UnorderedSet<size_t>& hash_cache = m_shape_hash_cache[shape];
  std::string name;
  // If the interdex grouping option is disabled, we assume that the model can
  // collapse nicely into a small set of merged shape classes. In this case, the
  // legacy naming scheme is more stable. The trailing hash of the mergeable set
  // is actually likely to make the shape symbol less stable.
  if (m_spec.interdex_config.is_enabled() && m_spec.use_stable_shape_names) {
    name = shape.build_type_name(m_spec.class_name_prefix, merger_type,
                                 group_values, intf_set, group_count, dex_id,
                                 interdex_subgroup_idx, hash_cache);
  } else {
    name = shape.build_type_name_legacy(m_spec.class_name_prefix, merger_type,
                                        intf_set, dex_id, group_count,
                                        interdex_subgroup_idx, subgroup_idx);
  }
  const auto& shape_type = DexType::make_type(name);
  TRACE(CLMG, 7, "Build shape type %s", SHOW(shape_type));
  auto& merger_shape = create_merger_shape(shape_type, shape, merger_type,
                                           intf_set, group_values);
  merger_shape.dex_id = dex_id;
  merger_shape.interdex_subgroup = interdex_subgroup_idx;

  map_fields(merger_shape, group_values);
  return merger_shape;
}

void Model::create_mergers_helper(
    const DexType* merger_type,
    const MergerType::Shape& shape,
    const TypeSet& intf_set,
    const std::optional<size_t>& dex_id,
    const TypeSet& group_values,
    const strategy::Strategy strategy,
    const std::optional<InterdexSubgroupIdx>& interdex_subgroup_idx,
    const std::optional<size_t>& max_mergeables_count,
    size_t min_mergeables_count) {
  InterdexSubgroupIdx subgroup_cnt = 0;
  strategy::MergingStrategy ms(strategy, group_values);
  ms.apply_grouping(min_mergeables_count, max_mergeables_count,
                    [&](const ConstTypeVector& group) {
                      create_merger_helper(merger_type, shape, intf_set, dex_id,
                                           group, interdex_subgroup_idx,
                                           subgroup_cnt++);
                      m_stats.m_merging_size_counts[group.size()]++;
                    });
}

void Model::create_hot_cold_mergers(
    const DexType* merger_type,
    const MergerType::Shape& shape,
    const TypeSet& intf_set,
    const std::optional<size_t>& dex_id,
    const TypeSet& group_values,
    const std::optional<InterdexSubgroupIdx>& interdex_subgroup_idx) {
  if (!m_spec.hot_cold_grouping) {
    create_mergers_helper(merger_type, shape, intf_set, dex_id, group_values,
                          m_spec.strategy, interdex_subgroup_idx,
                          m_spec.max_count, m_spec.min_count);
    return;
  }

  TypeSet hot;
  TypeSet cold;
  for (const auto* type : group_values) {
    const auto* cls = type_class(type);
    always_assert(cls);
    if (is_hot_mergeable(cls, m_vscopes, m_hot_methods)) {
      hot.insert(type);
    } else {
      cold.insert(type);
    }
  }
  TRACE(CLMG, 5, "Hot/cold split of %zu mergeables: %zu hot, %zu cold",
        group_values.size(), hot.size(), cold.size());
  m_stats.m_hot_mergeables += hot.size();
  m_stats.m_cold_mergeables += cold.size();
  if (!hot.empty() && !cold.empty()) {
    m_stats.m_hot_cold_split_groups++;
  }

  const auto create_part_mergers = [&](const TypeSet& part) {
    if (part.empty()) {
      return;
    }
    if (part.size() < m_spec.min_count) {
      m_stats.m_hot_cold_dropped += part.size();
      m_stats.m_dropped += part.size();
      return;
    }
    create_mergers_helper(merger_type, shape, intf_set, dex_id, part,
                          m_spec.strategy, interdex_subgroup_idx,
                          m_spec.max_count, m_spec.min_count);
  };
  create_part_mergers(hot);
  create_part_mergers(cold);
}

/**
 * Excluding the types specified in the "exclude" option of the config.
 * We don't perform any checks on the given types. We simply assume the good
 * intention of adding them as excluded types in the config, and exclude them
 * from the merging transformation.
 */
void Model::exclude_types(const ConstTypeHashSet& exclude_types) {
  for (const auto& type : UnorderedIterable(exclude_types)) {
    const auto& cls = type_class(type);
    if (cls == nullptr) {
      continue;
    }
    if (is_interface(cls)) {
      const auto& impls = m_type_system.get_implementors(type);
      m_excluded.insert(impls.begin(), impls.end());
    } else {
      m_excluded.insert(type);
      m_type_system.get_all_children(type, m_excluded);
    }
  }
  TRACE(CLMG, 4, "Excluding types %zu", m_excluded.size());
}

bool Model::is_excluded(const DexType* type) const {
  if (m_excluded.count(type) != 0u) {
    return true;
  }
  const auto type_name = type->get_name()->str();
  for (const auto& prefix : UnorderedIterable(m_spec.exclude_prefixes)) {
    if (type_name.starts_with(prefix)) {
      return true;
    }
  }
  return false;
}

/**
 * Aggregate all mergeable types under a merger according to their shape.
 * Create a merger for every shape and move the mergeable types under
 * that shape.
 * Example:
 * class A { int f1; String f2; }
 * class B { int f1; Object f2; }
 * class C { int[] f1; int f2; }
 * The 3 classes above have all the same shape:
 * class Shape { Object field0; int field1; }
 */
void Model::shape_model() {
  // sort mergers before creating the shapes.
  std::vector<MergerType*> mergers;
  mergers.reserve(m_mergers.size());
  for (auto& merger_it : UnorderedIterable(m_mergers)) {
    mergers.emplace_back(&merger_it.second);
  }
  std::sort(mergers.begin(), mergers.end(),
            [](const MergerType* first, const MergerType* second) {
              return compare_dextypes(first->type, second->type);
            });

  InterDexGrouping interdex_grouping(m_scope, m_conf, m_spec.interdex_config,
                                     m_spec.merging_targets);
  for (auto* merger : mergers) {
    TRACE(CLMG, 6, "Build shapes from %s", SHOW(merger->type));
    MergerType::ShapeCollector shapes;
    shape_merger(*merger, interdex_grouping, shapes);
    approximate_shapes(shapes);

    m_stats.m_dropped += trim_shapes(shapes, m_spec.min_count);
    for (auto& shape_it : shapes) {
      break_by_interface(*merger, shape_it.first, shape_it.second);
    }

    flatten_shapes(interdex_grouping, *merger, shapes);
  }

  // Update excluded metrics
  m_stats.m_excluded = static_cast<uint32_t>(m_excluded.size());
  TRACE(CLMG, 4, "Excluded types total %zu", m_excluded.size());
}

void Model::shape_merger(const MergerType& root,
                         const InterDexGrouping& /*interdex_grouping*/,
                         MergerType::ShapeCollector& shapes) {
  // if the root has got no children there is nothing to "shape"
  const auto& children = m_hierarchy.find(root.type);
  if (children == m_hierarchy.end()) {
    return;
  }

  // build a map from shape to types with that shape
  for (const auto& child : children->second) {
    if (m_hierarchy.find(child) != m_hierarchy.end()) {
      continue;
    }
    if (is_excluded(child)) {
      m_excluded.insert(child);
      continue;
    }
    if (m_non_mergeables.count(child) != 0u) {
      continue;
    }
    const auto& cls = type_class(child);
    if (cls == nullptr) {
      continue;
    }

    MergerType::Shape shape(cls->get_ifields());

    TRACE(CLMG, 9, "Shape of %s [%zu]: %s", SHOW(child),
          cls->get_ifields().size(), shape.to_string().c_str());

    shapes[shape].types.insert(child);
  }
}

/**
 * Depending the spec, choosing a approximation algorithm to merge different
 * shapes together. By default, no approximation is done.
 */
void Model::approximate_shapes(MergerType::ShapeCollector& shapes) {
  if (m_spec.approximate_shape_merging.isNull()) {
    TRACE(CLMG, 3, "[approx] No approximate shape merging specified.");
    return;
  }

  JsonWrapper approx_spec = JsonWrapper(m_spec.approximate_shape_merging);
  std::string algo_name;
  approx_spec.get("algorithm", "", algo_name);

  // List shapes before approximation
  size_t num_total_mergeable = 0;
  size_t num_before_shapes = 0;
  TRACE(CLMG, 3, "[approx] Shapes before approximation:");
  for (const auto& s : shapes) {
    TRACE(CLMG, 3, "         Shape: %s, mergeables = %zu",
          s.first.to_string().c_str(), s.second.types.size());
    num_before_shapes++;
    num_total_mergeable += s.second.types.size();
  }
  TRACE(CLMG, 3, "[approx] Total shapes before approximation = %zu",
        num_before_shapes);

  if (num_total_mergeable == 0) {
    return;
  }

  // Select an approximation algorithm
  if (algo_name == "simple_greedy") {
    simple_greedy_approximation(approx_spec, shapes, m_stats.m_approx_stats);
  } else if (algo_name == "max_mergeable_greedy") {
    max_mergeable_greedy(approx_spec, m_conf, shapes, m_stats.m_approx_stats);
  } else if (algo_name == "max_shape_merged_greedy") {
    max_shape_merged_greedy(approx_spec, m_conf, shapes,
                            m_stats.m_approx_stats);
  } else {
    TRACE(CLMG, 3,
          "[approx] Invalid approximate shape merging spec, skipping...");
    return;
  }

  // List shapes after approximation
  size_t num_after_shapes = 0;
  TRACE(CLMG, 3, "[approx] Shapes after approximation:");
  for (const auto& s_pair : shapes) {
    TRACE(CLMG, 3, "         Shape: %s, mergeables = %zu",
          s_pair.first.to_string().c_str(), s_pair.second.types.size());
    num_after_shapes++;
    num_total_mergeable -= s_pair.second.types.size();
  }
  always_assert(num_total_mergeable == 0);
  TRACE(CLMG, 3, "[approx] Total shapes after approximation = %zu",
        num_after_shapes);
}

/**
 * Break up a set of types by their interfaces implemention.
 * This step is critical to keep the type system "happy".
 */
void Model::break_by_interface(const MergerType& merger,
                               const MergerType::Shape& shape,
                               MergerType::ShapeHierarchy& hier) {
  always_assert(!hier.types.empty());
  // group classes by interfaces implemented
  TRACE(CLMG, 7, "Break up shape %s parent %s", shape.to_string().c_str(),
        SHOW(merger.type));
  for (const auto& type : hier.types) {
    const auto& cls_intfs = m_class_to_intfs.find(type);
    if (cls_intfs == m_class_to_intfs.end()) {
      hier.groups[Model::empty_set].insert(type);
      continue;
    }
    auto& intfs = cls_intfs->second;
    hier.groups[intfs].insert(type);
  }
  TRACE(CLMG, 7, "%zu groups created for shape %s (%zu)", hier.groups.size(),
        shape.to_string().c_str(), hier.types.size());
}

namespace class_merging {

/**
 * Group merging targets according to their dex ids. Return a vector of dex_id
 * and types.
 */
TypeGroupByDex Model::group_per_dex(const TypeSet& types,
                                    const ModelSpec& spec) {
  if (!spec.per_dex_grouping) {
    TypeSet group(types.begin(), types.end());
    return {{std::nullopt, group}};
  }
  std::vector<TypeSet> new_groups(m_x_dex.num_dexes());
  for (const auto* type : types) {
    auto dex_id = m_x_dex.get_dex_idx(type);
    redex_assert(dex_id < new_groups.size());
    new_groups[dex_id].emplace(type);
  }
  TypeGroupByDex result(m_x_dex.num_dexes());
  for (size_t dex_id = 0; dex_id < new_groups.size(); ++dex_id) {
    auto& group = new_groups[dex_id];
    if (group.size() >= spec.min_count) {
      TRACE(CLMG, 7, "dex_id %zu: group %zu", dex_id, group.size());
      result.emplace_back(
          std::make_pair(std::optional<size_t>(dex_id), std::move(group)));
    }
  }
  return result;
}

void Model::flatten_shapes(const InterDexGrouping& interdex_grouping,
                           const MergerType& merger,
                           MergerType::ShapeCollector& shapes) {
  size_t num_trimmed_types = trim_groups(shapes, m_spec.min_count);
  m_stats.m_dropped += num_trimmed_types;

  // Shape based grouping layer
  // sort shapes by mergeables count
  std::vector<const MergerType::Shape*> keys;
  for (auto& shape_it : shapes) {
    keys.emplace_back(&shape_it.first);
  }
  std::sort(
      keys.begin(), keys.end(),
      [&](const MergerType::Shape* first, const MergerType::Shape* second) {
        return shapes[*first].types.size() > shapes[*second].types.size();
      });

  // create shapes
  for (const auto& shape : keys) {
    const auto& shape_hierarchy = shapes[*shape];

    std::vector<const TypeSet*> intf_sets;
    for (const auto& group_it : shape_hierarchy.groups) {
      intf_sets.emplace_back(&group_it.first);
    }

    // sort groups by mergeables count
    std::sort(intf_sets.begin(),
              intf_sets.end(),
              [&](const TypeSet* left, const TypeSet* right) {
                const auto& left_group = shape_hierarchy.groups.at(*left);
                const auto& right_group = shape_hierarchy.groups.at(*right);

                if (left_group.size() == right_group.size()) {
                  const DexType* left_first_type = *left_group.begin();
                  const DexType* right_first_type = *right_group.begin();

                  return compare_dextypes(left_first_type, right_first_type);
                }

                return left_group.size() > right_group.size();
              });
    // Type identity grouping layer (interface impl set)
    for (const TypeSet* intf_set : intf_sets) {
      const TypeSet& implementors = shape_hierarchy.groups.at(*intf_set);
      // Per dex grouping layer
      for (auto& pair : group_per_dex(implementors, m_spec)) {
        auto dex_id = pair.first;
        auto group = pair.second;
        const auto interdex_visitor = [&](const InterdexSubgroupIdx gid,
                                          const TypeSet& itd_group) {
          create_hot_cold_mergers(merger.type, *shape, *intf_set, dex_id,
                                  itd_group, gid);
          m_stats.m_interdex_groups[gid] += itd_group.size();
        };
        // InterDex grouping layer
        if (interdex_grouping.num_groups() > 1) {
          interdex_grouping.visit_groups(m_spec, group, interdex_visitor);
        } else {
          create_hot_cold_mergers(merger.type, *shape, *intf_set, dex_id, group,
                                  std::nullopt);
        }
      }
    }
  }
}

void Model::map_fields(MergerType& merger,
                       const std::vector<const DexType*>& classes) {
  TRACE(CLMG, 8, "Build field map for %s", SHOW(merger.type));
  always_assert(merger.is_shape());
  if (merger.field_count() == 0) {
    return;
  }
  // for each mergeable type build order the field according to the
  // shape. The field order shape is implicit and defined by the shape itself
  for (const auto& type : classes) {
    TRACE(CLMG, 8, "Collecting fields for %s", SHOW(type));
    std::vector<DexField*> fields(merger.field_count());
    const DexClass* cls = type_class(type);
    for (const auto& field : cls->get_ifields()) {
      size_t index = merger.start_index_for(field->get_type());
      for (; index < fields.size(); index++) {
        if (fields[index] != nullptr) {
          continue;
        }
        TRACE(CLMG, 8, "Add field %s", show_deobfuscated(field).c_str());
        fields[index] = field;
        break;
      }
      always_assert(index < fields.size());
    }
    for (size_t index = 0; index < fields.size(); index++) {
      // If the fields array is not fully filled, this means the shape is larger
      // than the actual class (possibly due to approximate shape merging), we
      // make a new field as a placeholder.
      if (fields[index] != nullptr) {
        continue;
      }
      std::ostringstream ss;
      ss << "placeholder_" << index;
      auto* field_type = merger.field_type_at(static_cast<int>(index));
      fields[index] = DexField::make_field(
                          type, DexString::make_string(ss.str()), field_type)
                          ->make_concrete(ACC_PUBLIC);
      TRACE(CLMG, 9,
            "  -- A hole found at index %zu, created a placeholder field of "
            "type %s",
            index, field_type->c_str());
    }
    TRACE(CLMG, 8, "Add field map item [%zu]", fields.size());
    merger.field_map[type] = fields;
  }
}

/**
 * Build the method lists for a merger, collecting all methods that
 * belong to the mergeable types.
 */
void Model::collect_methods() {
  // Shared across all ModelSpecs (built once per pass), so specs see the same
  // pre-merge scope -- matching legacy's single shared ClassScopes.
  const auto& vscopes = m_vscopes;
  // distribute_virtual_methods cache; keyed by VirtualScope* from `vscopes`, so
  // it shares `vscopes`'s lifetime and is threaded through the recursion below
  // rather than kept as model state.
  ScopeClassMethodMap scope_class_method_map;
  // collect all vmethods and dmethods of mergeable types into the merger
  for (auto& merger_it : UnorderedIterable(m_mergers)) {
    auto& merger = merger_it.second;
    if (merger.mergeables.empty()) {
      continue;
    }
    TRACE(CLMG,
          8,
          "Collect methods for merger %s [%zu]",
          SHOW(merger.type),
          merger.mergeables.size());
    UnorderedSet<const virtual_scope::VirtualScope*> processed_intf_scopes;
    for (const auto* mergeable : merger.mergeables) {
      const auto* cls = type_class(mergeable);
      always_assert(cls);
      TRACE(CLMG, 8, "  mergeable %s", SHOW(mergeable));
      TRACE(CLMG,
            8,
            "%zu dmethods in %s",
            cls->get_dmethods().size(),
            SHOW(cls->get_type()));
      bool has_ctor = false;
      for (auto* method : cls->get_dmethods()) {
        if (method::is_init(method)) {
          has_ctor = true;
        }
        always_assert_log(method->get_code(), "dmethod w/o code %s",
                          SHOW(method));
        merger.dmethods.emplace_back(method);
      }
      always_assert_log(has_ctor,
                        "[ClassMerging] No ctor found for mergeable %s",
                        SHOW(mergeable));

      const auto& virt_scopes = vscopes.at(mergeable);
      TRACE(CLMG, 8, "%zu virtual scopes in %s", virt_scopes.size(),
            SHOW(mergeable));
      for (const auto* virt_scope : virt_scopes) {

        // interface methods
        if (virt_scope->implements_interface()) {
          if (processed_intf_scopes.count(virt_scope) == 0) {
            processed_intf_scopes.insert(virt_scope);
            TRACE(CLMG,
                  8,
                  "interface virtual scope [%zu]",
                  virt_scope->methods().size());
            add_interface_scope(merger, *virt_scope);
          }
          continue;
        }

        // non virtual methods
        if (virt_scope->is_effectively_final()) {
          const auto* meth = virt_scope->top_def();
          TRACE(CLMG,
                8,
                "non virtual scope %s (%s)",
                meth->get_deobfuscated_name_or_empty_copy().c_str(),
                SHOW(meth->get_name()));
          merger.non_virt_methods.emplace_back(const_cast<DexMethod*>(meth));
          continue;
        }

        // virtual methods
        add_virtual_scope(merger, *virt_scope);
      }
    }

    for (auto& intf_meths : merger.intfs_methods) {
      if (intf_meths.methods.size() == merger.mergeables.size()) {
        // If the InterfaceMethod entry completely overrides the overridden one,
        // we don't need to track the overridden anymore. That way we don't
        // generate a call to the overridden fall back, since it won't be
        // reachable.
        intf_meths.overridden_meth = nullptr;
      }
    }
  }

  // now for the virtual methods up the hierarchy and those in the type
  // of the merger (if an existing type) distribute them across the
  // proper merger
  // collect all virtual scope up the hierarchy from a root
  for (const MergerType* merger_root : m_roots) {
    std::vector<const virtual_scope::VirtualScope*> base_scopes;
    // get the first existing type from roots (has a DexClass)
    auto find_class = [&]() {
      const auto* root_type = merger_root->type;
      auto* cls = type_class(root_type);
      while (cls == nullptr) {
        const auto parent = m_parents.find(root_type);
        if (parent == m_parents.end()) {
          break;
        }
        root_type = parent->second;
        cls = type_class(parent->second);
      }
      return cls;
    };
    auto* cls = find_class();
    always_assert_log(cls != nullptr, "No class for %s",
                      SHOW(merger_root->type));
    // load all parents scopes
    const auto& parents = m_type_system.parent_chain(cls->get_type());
    if (parents.size() > 1) {
      for (auto index = parents.size() - 1; index > 0; --index) {
        const auto* const type = parents[index - 1];
        for (const auto* virt_scope : vscopes.at(type)) {
          base_scopes.emplace_back(virt_scope);
        }
      }
    }

    distribute_virtual_methods(merger_root->type, base_scopes, vscopes,
                               scope_class_method_map);
  }
}

/**
 * Add methods in `virt_scope` to a new MergerType.vmethods entry.
 * `virt_scope` is a VirtualScope rooted from a mergeable type of the current
 * `merger`.
 */
void Model::add_virtual_scope(MergerType& merger,
                              const virtual_scope::VirtualScope& virt_scope) {
  // Add a new MergerType.vmethods entry w/o the base. This is just the
  // placeholder. VirtualMethod.base and VirtualMethod.overrides are to be
  // populated at a later point.
  merger.vmethods.emplace_back(nullptr);
  for (const auto* vmeth : virt_scope.methods()) {
    TRACE(CLMG, 9, "check virtual method %s", SHOW(vmeth));
    always_assert_log(vmeth->is_def(), "not def %s", SHOW(vmeth));
    if (merger.mergeables.count(vmeth->get_class()) == 0) {
      continue;
    }
    TRACE(CLMG, 8, "add virtual method %s", SHOW(vmeth));
    merger.vmethods.back().overrides.emplace_back(
        const_cast<DexMethod*>(vmeth));
  }
}

/**
 * Add methods in `virt_scope` to a new MergerType.intfs_methods entry.
 * `virt_scope` is a VirtualScope rooted from a mergeable type of the current
 * `merger`. `virt_scope` is also known to implement at least one interface
 * method.
 */
void Model::add_interface_scope(MergerType& merger,
                                const virtual_scope::VirtualScope& intf_scope) {

  const auto& insert_to = [&merger, &intf_scope](
                              MergerType::InterfaceMethod& intf_meth) {
    bool inserted = false;
    for (const auto* intf :
         UnorderedIterable(intf_scope.implemented_interfaces())) {
      intf_meth.interfaces.insert(intf);
    }
    for (const auto* vmeth : intf_scope.methods()) {
      // Skip synthetic miranda placeholders (!is_def()) -- they are not real
      // methods to merge and would crash downstream consumers (e.g.
      // ModelMethodMerger::fix_visibility). Matches legacy add_interface_scope.
      if (!vmeth->is_def()) {
        continue;
      }
      // Only collect intf methods on mergeable types
      if (merger.mergeables.count(vmeth->get_class()) == 0) {
        continue;
      }
      TRACE(CLMG,
            8,
            "add interface method %s (%s)",
            vmeth->get_deobfuscated_name_or_empty_copy().c_str(),
            SHOW(vmeth->get_name()));
      intf_meth.methods.emplace_back(const_cast<DexMethod*>(vmeth));
      inserted = true;
    }

    if (!inserted) {
      return;
    }

    // An interface VirtualScope rooted from a mergeable needs to consider
    // the interface method it implements. The interface method can be a
    // default method or even an external default method.
    // In the default method case, if it's not overridden by all mergeables,
    // we need to identify the default method as the fall back.
    // Here we check if the overridden interface is an external non-abstract
    // class. If it is, we assume it's an external default method, and
    // update MergerType.InterfaceMethod.overridden_method accordingly.
    if (intf_meth.overridden_meth == nullptr) {
      const auto& intfs = intf_scope.implemented_interfaces();
      always_assert(!intfs.empty());
      // Iterate in a deterministic order: this loop commits to the first
      // external default method it finds as the fallback, so an unordered
      // walk would make the choice (and the output) nondeterministic.
      for (const auto* intf : unordered_to_ordered(intfs, compare_dextypes)) {
        const auto* intf_cls = type_class(intf);
        always_assert(intf_cls);
        const auto* meth = intf_meth.methods.front();
        auto* intf_method = resolve_interface_method_deprecated(
            intf_cls, meth->get_name(), meth->get_proto());
        if ((intf_method != nullptr) && !is_abstract(intf_method)) {
          intf_meth.overridden_meth = intf_method;
          TRACE(CLMG, 8, "Update InterfaceMethod.overridden_meth %s",
                SHOW(intf_method));
          break;
        }
      }
    }
  };

  always_assert(!intf_scope.methods().empty());
  const auto* vmethod = intf_scope.methods()[0];
  for (auto& intf_meths : merger.intfs_methods) {
    if (method::signatures_match(intf_meths.methods[0], vmethod)) {
      insert_to(intf_meths);
      return;
    }
  }

  // No match for existing InterfaceMethods. Now create a new InterfaceMethod
  // and insert the current VirtualScope. But we only do so if the VirtualScope
  // has at least one method def.
  if (intf_scope.has_def()) {
    merger.intfs_methods.emplace_back();
    insert_to(merger.intfs_methods.back());
  }
}

void Model::distribute_virtual_methods(
    const DexType* type,
    std::vector<const virtual_scope::VirtualScope*> base_scopes,
    const virtual_scope::VirtualScopes& vscopes,
    ScopeClassMethodMap& scope_class_method_map) {
  TRACE(CLMG,
        8,
        "distribute virtual methods for %s, parent virtual scope %zu",
        SHOW(type),
        base_scopes.size());
  // add to the base_scope the class scope of the merger type
  const auto& virt_scopes = vscopes.at(type);
  for (const auto* virt_scope : virt_scopes) {
    if (virt_scope->methods().size() == 1) {
      continue;
    }
    TRACE(CLMG,
          8,
          "virtual scope found [%zu] %s",
          virt_scope->methods().size(),
          SHOW(virt_scope->top_def()));
    base_scopes.emplace_back(virt_scope);
  }

  const auto& merger_it = m_mergers.find(type);
  if (merger_it != m_mergers.end() && !merger_it->second.mergeables.empty()) {
    auto& merger = merger_it->second;
    TRACE(CLMG, 8, "merger found %s", SHOW(merger.type));
    // loop through the parent scopes of the mergeable types and
    // if a method is from a mergeable type add it to the merger
    for (const auto* virt_scope : base_scopes) {
      TRACE(
          CLMG,
          8,
          "walking virtual scope [%s, %zu] %s (%s)",
          SHOW(virt_scope->root()),
          virt_scope->methods().size(),
          virt_scope->top_def()->get_deobfuscated_name_or_empty_copy().c_str(),
          SHOW(virt_scope->top_def()->get_name()));
      bool is_interface = virt_scope->implements_interface();
      std::vector<DexMethod*>* insert_list = nullptr;
      // If the top def is concrete, it's a valid virtual fallback for
      // mergeables w/o override. Otherwise (abstract top def) we probe the
      // scope for the nearest concrete def sitting on a base class of the
      // targeted mergeables, not on a separate inheritance branch. We commit on
      // the 1st valid base impl; virtual method refs can be rebound at a later
      // point.
      const DexMethod* top_def = virt_scope->top_def();
      // We emit invoke_super against the overridden method by default in the
      // virtual dispatch. A non-external abstract method is not a valid target
      // for invoke-super, so we skip it.
      const auto get_initial_overridden =
          [](const DexMethod* meth) -> DexMethod* {
        // top_def() is always a real method, so no null check is needed here;
        // an abstract (non-external) top def, however, is not a valid
        // invoke-super target.
        if (!meth->is_def()) {
          return nullptr;
        }
        if (!meth->is_external() && is_abstract(meth)) {
          return nullptr;
        }
        return const_cast<DexMethod*>(meth);
      };
      DexMethod* overridden_meth = get_initial_overridden(top_def);
      // No top-def/miranda gate is needed: is_top_def(flags) is
      // `(flags & TOP_DEF) == TOP_DEF` with TOP_DEF == 0x0, i.e. true for every
      // method.
      const auto update_overridden = [&merger,
                                      &overridden_meth](DexMethod* virt_meth) {
        always_assert(virt_meth->is_def());
        if (overridden_meth == nullptr) {
          const auto* cls = virt_meth->get_class();
          const auto& mergeables = merger.mergeables;
          always_assert(!mergeables.empty());
          const auto* a_mergeable = *mergeables.begin();
          if (cls != a_mergeable && type::is_subclass(cls, a_mergeable)) {
            overridden_meth = virt_meth;
            TRACE(CLMG, 9, "Update overridden_meth to %s", SHOW(virt_meth));
          }
        }
      };

      // Optimization: instead of iterating ALL methods in the scope
      // (which can be 10K+ for common virtual methods), first find
      // overridden_meth from non-mergeable methods, then iterate
      // only the merger's mergeables to find their methods in the scope.

      // Step 1: Find overridden_meth from non-mergeable methods
      // (skip if already set from top_def)
      if (overridden_meth == nullptr) {
        for (const auto* m : virt_scope->methods()) {
          auto* virt_meth = const_cast<DexMethod*>(m);
          if (!is_usable_dispatch_target(virt_meth)) {
            continue;
          }
          if (merger.mergeables.count(virt_meth->get_class()) == 0) {
            update_overridden(virt_meth);
            if (overridden_meth != nullptr) {
              break;
            }
          }
        }
      }

      // Step 2: Build a class->method map for this scope (cached)
      auto scope_map_it = scope_class_method_map.find(virt_scope);
      if (scope_map_it == scope_class_method_map.end()) {
        auto& class_method_map = scope_class_method_map[virt_scope];
        for (const auto* m : virt_scope->methods()) {
          auto* virt_meth = const_cast<DexMethod*>(m);
          if (!is_usable_dispatch_target(virt_meth)) {
            continue;
          }
          class_method_map[virt_meth->get_class()] = virt_meth;
        }
        scope_map_it = scope_class_method_map.find(virt_scope);
      }
      const auto& class_method_map = scope_map_it->second;

      // Step 3: Iterate merger's mergeables and look up their methods
      for (const auto* mergeable : merger.mergeables) {
        auto meth_it = class_method_map.find(mergeable);
        if (meth_it == class_method_map.end()) {
          continue;
        }
        auto* virt_meth = meth_it->second;
        TRACE(CLMG,
              9,
              "method %s (%s)",
              virt_meth->get_deobfuscated_name_or_empty_copy().c_str(),
              SHOW(virt_meth->get_name()));
        if (is_interface) {
          if (insert_list == nullptr) {
            // must be a new method
            TRACE(CLMG,
                  8,
                  "add interface method %s (%s) w/ overridden_meth %s",
                  virt_meth->get_deobfuscated_name_or_empty_copy().c_str(),
                  SHOW(virt_meth->get_name()),
                  SHOW(overridden_meth));
            merger.intfs_methods.emplace_back();
            auto& intf_meth = merger.intfs_methods.back();
            intf_meth.overridden_meth = overridden_meth;
            for (const auto* intf :
                 UnorderedIterable(virt_scope->implemented_interfaces())) {
              merger.intfs_methods.back().interfaces.insert(intf);
            }
            insert_list = &merger.intfs_methods.back().methods;
          }
          insert_list->emplace_back(virt_meth);
        } else {
          if (insert_list == nullptr) {
            // must be a new method
            TRACE(CLMG,
                  8,
                  "add virtual method %s w/ overridden_meth %s",
                  SHOW(virt_meth),
                  SHOW(overridden_meth));
            merger.vmethods.emplace_back(overridden_meth);
            insert_list = &merger.vmethods.back().overrides;
          }
          insert_list->emplace_back(virt_meth);
        }
      }
    }
  }

  // walk the children and keep distributing as needed
  const auto& children = m_hierarchy.find(type);
  if (children != m_hierarchy.end()) {
    for (const auto& child : children->second) {
      distribute_virtual_methods(child, base_scopes, vscopes,
                                 scope_class_method_map);
    }
  }
}

std::string Model::show_type(const DexType* type) { return show(type); }

std::string Model::print() const {
  size_t count{0};
  for (const auto& merger : UnorderedIterable(m_mergers)) {
    count += merger.second.mergeables.size();
  }
  std::ostringstream ss;
  ss << m_spec.name << " Model: all types " << m_spec.merging_targets.size()
     << ", merge types " << m_mergers.size() << ", mergeables " << count
     << "\n";
  for (auto* const root_merger : m_roots) {
    ss << print(root_merger->type, 1);
  }
  return ss.str();
}

std::string Model::print(const MergerType& merger) const {
  std::ostringstream ss;
  ss << SHOW(merger.type) << " mergeables(" << merger.mergeables.size() << ")"
     << " shape(str: " << merger.shape.string_fields
     << ", refs: " << merger.shape.reference_fields
     << ", bool: " << merger.shape.bool_fields
     << ", int: " << merger.shape.int_fields
     << ", long: " << merger.shape.long_fields
     << ", double: " << merger.shape.double_fields
     << ", float: " << merger.shape.float_fields << ") dmethods("
     << merger.dmethods.size() << ") non_virt_methods("
     << merger.non_virt_methods.size() << ") vmethods("
     << merger.vmethods.size();
  for (const auto& meths : merger.vmethods) {
    ss << "[" << meths.overrides.size() << "]";
  }
  ss << ") intf_methods(" << merger.intfs_methods.size();
  for (const auto& intf_meths : merger.intfs_methods) {
    ss << "[" << intf_meths.methods.size() << "]";
  }
  ss << ")";
  const auto& children = m_hierarchy.find(merger.type);
  if (children != m_hierarchy.end()) {
    ss << " children(" << children->second.size() << ")";
  }
  const auto& intfs = m_class_to_intfs.find(merger.type);
  if (intfs != m_class_to_intfs.end()) {
    ss << " interfaces(" << intfs->second.size() << ")";
    if (intfs->second.size() <= 7) {
      for (const auto& intf : intfs->second) {
        ss << ", " << SHOW(intf);
      }
    }
  }
  return ss.str();
}

std::string Model::print(const DexType* type) const {
  std::ostringstream ss;
  ss << SHOW(type);
  const auto& children = m_hierarchy.find(type);
  if (children != m_hierarchy.end()) {
    ss << " children(" << children->second.size() << ")";
  }
  const auto& intfs = m_class_to_intfs.find(type);
  if (intfs != m_class_to_intfs.end()) {
    ss << " interfaces(" << intfs->second.size() << ")";
    size_t count = 0;
    for (const auto& intf : intfs->second) {
      if (count++ > 6) {
        break;
      }
      ss << ", " << SHOW(intf);
    }
  }
  return ss.str();
}

std::string Model::print(const DexType* type, int nest) const {
  std::ostringstream ss;

  const auto indent = [&](char ch) {
    for (int i = 0; i < nest; i++) {
      ss << ch;
    }
  };

  const auto merger_it = m_mergers.find(type);
  indent('+');
  ss << " ";
  if (merger_it != m_mergers.end()) {
    const MergerType& merger = merger_it->second;
    ss << print(merger);
  } else {
    ss << print(type);
  }
  ss << "\n";

  if (merger_it != m_mergers.end()) {
    const MergerType& merger = merger_it->second;
    for (const auto& mergeable : merger.mergeables) {
      indent('-');
      ss << " " << print(mergeable) << "\n";
      auto* const cls = type_class(mergeable);
      for (const auto& field : cls->get_ifields()) {
        indent('-');
        ss << "* " << show_deobfuscated(field) << " ("
           << field->get_name()->c_str() << ")\n";
      }
    }

    const auto meth_str = [&](const DexMethod* meth,
                              const std::string& suffix = "") {
      indent('-');
      if (meth != nullptr) {
        ss << "# " << show_deobfuscated(meth) << " ("
           << meth->get_name()->c_str() << ") ["
           << (meth->get_code() != nullptr
                   ? meth->get_code()->cfg().num_opcodes()
                   : 0)
           << "]";
      } else {
        ss << "# missing";
      }
      ss << (suffix.empty() ? "" : " (") << suffix << ")\n";
    };

    if (!merger_it->second.dmethods.empty()) {
      indent('-');
      ss << "# " << merger.dmethods.size() << " dmethods:\n";
      for (const auto* meth : merger.dmethods) {
        meth_str(meth);
      }
    }

    if (!merger_it->second.non_virt_methods.empty()) {
      indent('-');
      ss << "# " << merger.non_virt_methods.size() << " non virtual methods:\n";
      for (const auto* meth : merger_it->second.non_virt_methods) {
        meth_str(meth);
      }
    }

    if (!merger.vmethods.empty()) {
      indent('-');
      ss << "# " << merger.vmethods.size() << " virtual methods:\n";
      for (const auto& vmeths : merger.vmethods) {
        meth_str(vmeths.base, "base");
        for (const auto* meth : vmeths.overrides) {
          meth_str(meth);
        }
      }
    }

    if (!merger_it->second.intfs_methods.empty()) {
      indent('-');
      ss << "# " << merger.intfs_methods.size() << " interface methods:\n";
      for (const auto& intf_meths : merger.intfs_methods) {
        meth_str(intf_meths.overridden_meth, "overridden");
        for (const auto* meth : intf_meths.methods) {
          meth_str(meth);
        }
        if (merger.mergeables.size() > intf_meths.methods.size()) {
          if (intf_meths.overridden_meth == nullptr) {
            const auto& methods = intf_meths.methods;
            TRACE(CLMG, 8,
                  "interface method entry missing overridden method %s %zu",
                  SHOW(methods.front()), methods.size());
          }
        }
      }
    }
  }
  const auto& children = m_hierarchy.find(type);
  if (children != m_hierarchy.end()) {
    for (const auto* child : children->second) {
      ss << print(child, nest + 1);
    }
  }
  return ss.str();
}

Model Model::build_model(const Scope& scope,
                         const DexStoresVector& stores,
                         ConfigFiles& conf,
                         const ModelSpec& spec,
                         const TypeSystem& type_system,
                         const virtual_scope::VirtualScopes& vscopes,
                         const RefChecker& refchecker) {
  Timer t("build_model");

  TRACE(CLMG, 3, "Build Model for %s", to_string(spec).c_str());
  Model model(scope, stores, conf, spec, type_system, vscopes, refchecker);
  TRACE(CLMG, 3, "Model:\n%s\nBuild Model done", model.print().c_str());

  TRACE(CLMG, 3, "Shape Model");
  model.shape_model();
  TRACE(CLMG, 3, "Model:\n%s\nShape Model done", model.print().c_str());

  TRACE(CLMG, 3, "Final Model");
  model.collect_methods();
  TRACE(CLMG, 3, "Model:\n%s\nFinal Model done", model.print().c_str());

  return model;
}

ModelStats& ModelStats::operator+=(const ModelStats& stats) {
  m_all_types += stats.m_all_types;
  m_non_mergeables += stats.m_non_mergeables;
  m_excluded += stats.m_excluded;
  m_dropped += stats.m_dropped;

  for (const auto& pair : stats.m_interdex_groups) {
    m_interdex_groups[pair.first] += pair.second;
  }

  m_hot_cold_split_groups += stats.m_hot_cold_split_groups;
  m_hot_mergeables += stats.m_hot_mergeables;
  m_cold_mergeables += stats.m_cold_mergeables;
  m_hot_cold_dropped += stats.m_hot_cold_dropped;

  for (const auto& pair : stats.m_merging_size_counts) {
    m_merging_size_counts[pair.first] += pair.second;
  }

  m_approx_stats += stats.m_approx_stats;

  m_num_classes_merged += stats.m_num_classes_merged;
  m_num_merged_volatile_fields += stats.m_num_merged_volatile_fields;
  m_num_merged_final_fields += stats.m_num_merged_final_fields;
  m_num_generated_classes += stats.m_num_generated_classes;
  m_num_ctor_dedupped += stats.m_num_ctor_dedupped;
  m_num_static_non_virt_dedupped += stats.m_num_static_non_virt_dedupped;
  m_num_vmethods_dedupped += stats.m_num_vmethods_dedupped;
  m_num_const_lifted_methods += stats.m_num_const_lifted_methods;
  m_updated_profile_method += stats.m_updated_profile_method;
  return *this;
}

void ModelStats::update_redex_stats(const std::string& prefix,
                                    PassManager& mgr) const {
  mgr.incr_metric(prefix + "_all_types", m_all_types);
  mgr.incr_metric(prefix + "_non_mergeables", m_non_mergeables);
  mgr.incr_metric(prefix + "_excluded_types", m_excluded);
  mgr.incr_metric(prefix + "_dropped_types", m_dropped);

  for (const auto& pair : m_interdex_groups) {
    auto group_id = pair.first;
    auto group_size = pair.second;
    mgr.incr_metric(prefix + "_interdex_group_" + std::to_string(group_id),
                    group_size);
    TRACE(CLMG, 3, "InterDex Group %s_%u %zu", prefix.c_str(), group_id,
          group_size);
  }

  // Only emitted when hot/cold grouping ran, so disabled models add no keys.
  if (m_hot_mergeables + m_cold_mergeables > 0) {
    mgr.incr_metric(prefix + "_hot_cold_split_groups", m_hot_cold_split_groups);
    mgr.incr_metric(prefix + "_hot_mergeables", m_hot_mergeables);
    mgr.incr_metric(prefix + "_cold_mergeables", m_cold_mergeables);
    mgr.incr_metric(prefix + "_hot_cold_dropped", m_hot_cold_dropped);
  }

  for (const auto& pair : m_merging_size_counts) {
    auto merging_size = pair.first;
    auto count = pair.second;
    mgr.incr_metric(prefix + "_merging_size_" + std::to_string(merging_size),
                    count);
    TRACE(CLMG, 3, "Merging size %s_%zu %zu", prefix.c_str(), merging_size,
          count);
  }

  m_approx_stats.update_redex_stats(prefix, mgr);

  mgr.incr_metric(prefix + "_merger_class_generated", m_num_generated_classes);
  mgr.incr_metric(prefix + "_class_merged", m_num_classes_merged);
  mgr.incr_metric(prefix + "_ctor_dedupped", m_num_ctor_dedupped);
  mgr.incr_metric(prefix + "_static_non_virt_dedupped",
                  m_num_static_non_virt_dedupped);
  mgr.incr_metric(prefix + "_vmethods_dedupped", m_num_vmethods_dedupped);
  mgr.incr_metric(prefix + "_updated_profile_method", m_updated_profile_method);
  mgr.set_metric(prefix + "_const_lifted_methods", m_num_const_lifted_methods);
}

} // namespace class_merging
