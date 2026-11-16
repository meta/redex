/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "DedupResources.h"

#include <boost/filesystem/path.hpp>
#include <boost/format.hpp>
#include <fstream>
#include <map>

#include "ConfigFiles.h"
#include "Debug.h"
#include "IOUtil.h"
#include "OptimizeResources.h"
#include "PassManager.h"
#include "RClass.h"
#include "ReachableResources.h"
#include "ReadMaybeMapped.h"
#include "RedexResources.h"
#include "Timer.h"
#include "Trace.h"
#include "WorkQueue.h"
#include "murmur_hash.h"

namespace {

constexpr decltype(redex_parallel::default_num_threads()) kReadFileThreads = 4u;

template <typename ItemType>
void print_duplicates(
    const std::vector<std::vector<ItemType>>& duplicates,
    const std::function<std::string(const ItemType&)>& printer_fn) {
  if (!traceEnabled(DEDUP_RES, 3)) {
    return;
  }
  for (const auto& vec : duplicates) {
    auto size = vec.size();
    always_assert(size > 1);
    std::stringstream ss;
    ss << "Canonical: " << printer_fn(vec[0]) << " {";
    for (size_t i = 1; i < size; i++) {
      ss << (i == 1 ? " " : ", ");
      ss << printer_fn(vec[i]);
    }
    ss << " }";
    TRACE(DEDUP_RES, 3, "%s", ss.str().c_str());
  }
}

template <typename ItemType>
void get_duplicates_impl(
    const UnorderedSet<ItemType>& disallowed,
    const std::map<size_t, std::vector<ItemType>>& item_by_hash,
    const std::function<bool(const ItemType&, const ItemType&)>&
        are_identical_fn,
    std::vector<std::vector<ItemType>>* duplicates) {
  // Within hash buckets, compare elements (N^2, but buckets should be small).
  for (const auto& p : item_by_hash) {
    std::vector<ItemType> bucket = p.second;
    std::sort(bucket.begin(), bucket.end());
    UnorderedSet<ItemType> already_duped;
    for (size_t i = 0; i < bucket.size() - 1; ++i) {
      ItemType primary_item = bucket[i];
      if (already_duped.count(primary_item)) {
        continue;
      }
      std::vector<ItemType> sub_duplicates = {primary_item};
      for (size_t j = i + 1; j < bucket.size(); ++j) {
        ItemType secondary_item = bucket[j];
        if (already_duped.count(secondary_item) ||
            disallowed.count(secondary_item)) {
          continue;
        }
        if (are_identical_fn(primary_item, secondary_item)) {
          sub_duplicates.push_back(secondary_item);
          already_duped.emplace(secondary_item);
        }
      }
      if (sub_duplicates.size() > 1) {
        duplicates->push_back(sub_duplicates);
      }
    }
  }
}

std::vector<std::vector<uint32_t>> get_duplicates_from_rows(
    ResourceTableFile* res_table,
    const std::vector<uint32_t>& ids,
    const UnorderedSet<uint32_t>& disallowed_ids) {
  std::vector<std::vector<uint32_t>> duplicates;
  std::map<size_t, std::vector<uint32_t>> res_by_hash;
  // Strategy:
  // Rows are passed in already grouped by type.
  // Further group rows by hash.
  res_table->collect_resid_values_and_hashes(ids, &res_by_hash);
  auto resource_value_identical = [&](const uint32_t& a, const uint32_t& b) {
    return res_table->resource_value_identical(a, b);
  };
  get_duplicates_impl<uint32_t>(disallowed_ids, res_by_hash,
                                resource_value_identical, &duplicates);
  auto printer = [&](const uint32_t& id) {
    std::stringstream stream;
    stream << "0x" << std::hex << id << std::dec << " ("
           << res_table->id_to_name.at(id) << ")";
    return std::string(stream.str());
  };
  print_duplicates<uint32_t>(duplicates, printer);
  return duplicates;
}

std::map<uint32_t, uint32_t> find_duplicate_resources(
    ResourceTableFile* res_table,
    const std::vector<uint32_t>& sorted_res_ids,
    const UnorderedSet<uint32_t>& disallowed_types,
    const UnorderedSet<uint32_t>& disallowed_ids) {
  always_assert(!sorted_res_ids.empty());
  std::map<uint32_t, uint32_t> dupe_to_canon;
  std::vector<std::vector<uint32_t>> all_duplicates;

  const int TYPE_IDENTIFIER_MASK = 0x00FF0000;
  uint32_t current_type = sorted_res_ids[0] & TYPE_IDENTIFIER_MASK;
  std::vector<uint32_t> ids_in_current_type;
  for (size_t i = 0; i < sorted_res_ids.size(); ++i) {
    uint32_t id = sorted_res_ids[i];
    uint32_t type_id = id & TYPE_IDENTIFIER_MASK;
    if (disallowed_types.count(type_id) != 0u) {
      continue;
    }

    if (type_id != current_type) {
      auto type_dupes = get_duplicates_from_rows(res_table, ids_in_current_type,
                                                 disallowed_ids);
      all_duplicates.insert(all_duplicates.end(), type_dupes.begin(),
                            type_dupes.end());
      ids_in_current_type.clear();
      current_type = type_id;
    }

    ids_in_current_type.push_back(id);
  }

  auto type_dupes =
      get_duplicates_from_rows(res_table, ids_in_current_type, disallowed_ids);
  all_duplicates.insert(all_duplicates.end(), type_dupes.begin(),
                        type_dupes.end());

  for (std::vector<uint32_t> v : all_duplicates) {
    always_assert(v.size() > 1);
    for (size_t i = 1; i < v.size(); ++i) {
      dupe_to_canon[v[i]] = v[0];
    }
  }

  return dupe_to_canon;
}

std::map<uint32_t, uint32_t> deduplicate_restable_rows(
    ResourceTableFile* res_table,
    const std::vector<uint32_t>& sorted_res_ids,
    const UnorderedSet<uint32_t>& disallowed_types,
    const UnorderedSet<uint32_t>& disallowed_ids,
    PassManager& mgr) {
  auto dupe_to_canon = find_duplicate_resources(
      res_table, sorted_res_ids, disallowed_types, disallowed_ids);
  for (const auto& pair : dupe_to_canon) {
    res_table->delete_resource(pair.first);
  }
  OptimizeResourcesPass::report_metric(DEDUP_RES, "num_duplicate_rows_deleted",
                                       static_cast<int>(dupe_to_canon.size()),
                                       mgr);
  return dupe_to_canon;
}

std::map<uint32_t, uint32_t> build_remapping(
    const std::vector<uint32_t>& sorted_res_ids,
    std::map<uint32_t, std::string> id_to_name,
    std::map<uint32_t, uint32_t> dupe_to_canon,
    const std::string& out_file) {
  std::map<uint32_t, uint32_t> old_to_new_ids;
  uint32_t current_type = 0;
  int subtrahend_for_current_type = 0;
  Json::Value map_json;

  // First build up a map that only takes into account the deleted rows.
  for (size_t index = 0; index < sorted_res_ids.size(); ++index) {
    uint32_t id = sorted_res_ids[index];
    const uint32_t PACKAGE_IDENTIFIER_MASK = 0xFF000000;
    uint32_t package_id = id & PACKAGE_IDENTIFIER_MASK;
    always_assert(package_id == PACKAGE_RESID_START);
    const uint32_t TYPE_IDENTIFIER_MASK = 0x00FF0000;
    uint32_t type_id = id & TYPE_IDENTIFIER_MASK;
    if (type_id != current_type) {
      subtrahend_for_current_type = 0;
      current_type = type_id;
    }

    if (dupe_to_canon.count(id) != 0u) {
      subtrahend_for_current_type++;
    } else {
      old_to_new_ids[id] = id - subtrahend_for_current_type;
    }
  }

  // Then, apply the remapping from dupe to canon, taking into account the
  // deleted row mapping from above.
  for (size_t index = 0; index < sorted_res_ids.size(); ++index) {
    uint32_t id = sorted_res_ids[index];

    Json::Value json_row;
    json_row["old_id"] = (boost::format("%x") % id).str();
    json_row["name"] = id_to_name[id];

    auto p = dupe_to_canon.find(id);
    if (p != dupe_to_canon.end()) {
      uint32_t remapped_canon = old_to_new_ids[p->second];
      old_to_new_ids[id] = remapped_canon;
    }

    json_row["new_id"] = (boost::format("%x") % old_to_new_ids[id]).str();

    map_json.append(json_row);
  }

  write_string_to_file(out_file, map_json.toStyledString());

  return old_to_new_ids;
}

template <typename HashType>
void compute_res_file_hashes(
    const std::string& zip_dir,
    ResourceTableFile* res_table,
    const std::vector<uint32_t>& sorted_res_ids,
    const std::function<HashType(const void* data, size_t size, HashType seed)>&
        hash_fn,
    std::map<size_t, std::vector<std::string>>* hash_to_absolute_paths,
    UnorderedMap<std::string, std::string>* absolute_path_to_device_path) {
  Timer t("compute_res_file_hashes");
  auto base_path = boost::filesystem::path(zip_dir);
  std::vector<std::string> tasks;
  UnorderedSet<std::string> seen_paths;
  // The following loop should exclude the string type from consideration; it
  // may not be obvious which strings are user visible vs file paths.
  auto string_type_ids = res_table->get_types_by_name_prefixes({"string"});
  for (size_t i = 0; i < sorted_res_ids.size(); ++i) {
    uint32_t id = sorted_res_ids[i];
    uint32_t type_id = id & TYPE_MASK_BIT;
    if (string_type_ids.count(type_id) > 0) {
      TRACE(DEDUP_RES, 3, "Will not check ID 0x%x for file paths", id);
      continue;
    }
    // We need to hash and check for equality files as they appear in the zip
    // (including the module name in case of .aab input), but when deduplicating
    // and writing the path to canonical file into the resource table we must
    // always write the path from the device perspective, which does not include
    // module name.
    auto zip_paths = res_table->get_files_by_rid(id, ResourcePathType::ZipPath);
    auto device_paths =
        res_table->get_files_by_rid(id, ResourcePathType::DevicePath);
    auto file_count = zip_paths.size();
    always_assert_log(file_count == device_paths.size(),
                      "Incorrect size for ID 0x%x", id);
    for (size_t j = 0; j < file_count; j++) {
      auto absolute_path = (base_path / zip_paths[j]).string();
      absolute_path_to_device_path->emplace(absolute_path, device_paths[j]);
      // Need to gracefully handle any file paths pointed to by multiple entries
      if (seen_paths.count(absolute_path) == 0) {
        tasks.emplace_back(absolute_path);
        seen_paths.emplace(absolute_path);
      }
    }
  }
  std::mutex out_mutex;
  workqueue_run<std::string>(
      [&](sparta::WorkerState<std::string>* /* unused */, std::string path) {
        HashType hash = 31;
        redex::read_file_with_contents(path,
                                       [&](const char* data, size_t size) {
                                         hash = hash_fn(data, size, hash);
                                       });
        {
          std::unique_lock<std::mutex> lock(out_mutex);
          (*hash_to_absolute_paths)[hash].push_back(std::move(path));
        }
      },
      tasks,
      std::min(redex_parallel::default_num_threads(), kReadFileThreads));
}

bool compare_files(const std::string& p1, const std::string& p2) {
  std::ifstream f1(p1, std::ifstream::binary | std::ifstream::ate);
  std::ifstream f2(p2, std::ifstream::binary | std::ifstream::ate);
  always_assert_log(!f1.fail(), "Failed to read path %s", p1.c_str());
  always_assert_log(!f2.fail(), "Failed to read path %s", p2.c_str());
  if (f1.tellg() != f2.tellg()) {
    return false; // size mismatch
  }
  // seek back to beginning and use std::equal to compare contents
  f1.seekg(0, std::ifstream::beg);
  f2.seekg(0, std::ifstream::beg);
  return std::equal(std::istreambuf_iterator<char>(f1.rdbuf()),
                    std::istreambuf_iterator<char>(),
                    std::istreambuf_iterator<char>(f2.rdbuf()));
}

void deduplicate_resource_files(PassManager& mgr, const std::string& zip_dir) {
  auto resources = create_resource_reader(zip_dir);
  auto res_table = resources->load_res_table();

  std::map<size_t, std::vector<std::string>> hash_to_absolute_paths;
  UnorderedMap<std::string, std::string> absolute_path_to_device_path;
  compute_res_file_hashes<uint32_t>(
      zip_dir, res_table.get(), res_table->sorted_res_ids, murmur_hash3,
      &hash_to_absolute_paths, &absolute_path_to_device_path);

  UnorderedSet<std::string> do_not_deduplicate;
  std::vector<std::vector<std::string>> duplicates;
  get_duplicates_impl<std::string>(do_not_deduplicate, hash_to_absolute_paths,
                                   compare_files, &duplicates);
  print_duplicates<std::string>(duplicates,
                                [](const std::string& s) { return s; });

  // Build remapping, this must be done in terms of device paths.
  UnorderedMap<std::string, std::string> file_mapping;
  UnorderedSet<std::string> files_to_delete;
  for (const auto& vec : duplicates) {
    auto size = vec.size();
    always_assert(size > 1);
    auto canonical_device_path = absolute_path_to_device_path.at(vec[0]);
    for (size_t i = 1; i < size; i++) {
      auto duplicate = vec[i];
      files_to_delete.emplace(duplicate);
      auto dup_device_path = absolute_path_to_device_path.at(duplicate);
      TRACE(DEDUP_RES, 4, "Will rewrite path %s to %s", dup_device_path.c_str(),
            canonical_device_path.c_str());
      file_mapping.emplace(dup_device_path, canonical_device_path);
    }
  }
  auto resource_files = resources->find_resources_files();
  res_table->remap_file_paths_and_serialize(resource_files, file_mapping);

  delete_files_absolute(files_to_delete);
  OptimizeResourcesPass::report_metric(DEDUP_RES, "deleted_files",
                                       static_cast<int>(files_to_delete.size()),
                                       mgr);
}

// Types that when referred to from .xml files are usually just simple values (
// and not references to other files). This is just an observation base on real
// world examples, so that we can perform a lightweight dedup step initially on
// a subset of data. This is probably not something that needs a per-app config.
const UnorderedSet<std::string> SIMPLE_REFERENCE_TYPES = {"bool", "color",
                                                          "dimen", "integer"};

void deduplicate_resource_file_references(
    const std::string& zip_dir,
    const UnorderedSet<std::string>& disallowed_type_names,
    const UnorderedSet<uint32_t>& disallowed_ids) {
  auto resources = create_resource_reader(zip_dir);
  auto res_table = resources->load_res_table();

  bool allow_reference_dedup = false;
  std::vector<std::string> effective_disallowed_type_names;
  res_table->get_type_names(&effective_disallowed_type_names);
  for (auto it = effective_disallowed_type_names.begin();
       it != effective_disallowed_type_names.end();) {
    auto t = *it;
    if (SIMPLE_REFERENCE_TYPES.count(t) > 0 &&
        disallowed_type_names.count(t) == 0) {
      it = effective_disallowed_type_names.erase(it);
      allow_reference_dedup = true;
      TRACE(DEDUP_RES, 2,
            "Will check xml references of type %s for canonicalization.",
            t.c_str());
    } else {
      it++;
    }
  }

  if (allow_reference_dedup) {
    auto effective_disallowed_types =
        res_table->get_types_by_name(effective_disallowed_type_names);
    auto dupe_to_canon =
        find_duplicate_resources(res_table.get(), res_table->sorted_res_ids,
                                 effective_disallowed_types, disallowed_ids);
    TRACE(DEDUP_RES, 2, "Found %zu xml references to canonicalize.",
          dupe_to_canon.size());
    if (!dupe_to_canon.empty()) {
      const auto& relevant_xml_files = resources->find_all_xml_files();
      for (const std::string& path : UnorderedIterable(relevant_xml_files)) {
        resources->remap_xml_reference_attributes(path, dupe_to_canon);
      }
    }
  }
}
} // namespace

void DedupResourcesPass::prepare_disallowed_ids(
    const std::string& zip_dir,
    UnorderedSet<uint32_t>* disallowed_types,
    UnorderedSet<uint32_t>* disallowed_ids) {
  auto resources = create_resource_reader(zip_dir);
  auto res_table = resources->load_res_table();

  auto types = res_table->get_types_by_name(m_disallowed_types);
  insert_unordered_iterable(*disallowed_types, types);

  auto disallowed_by_name = resources::get_resources_by_prefix_and_name(
      m_disallowed_resource_prefixes, m_disallowed_resources,
      res_table->name_to_ids);
  insert_unordered_iterable(*disallowed_ids, disallowed_by_name);
  // Overlayable ids, keep as-is.
  auto overlayable_ids = res_table->get_overlayable_id_roots();
  insert_unordered_iterable(*disallowed_ids, overlayable_ids);

  auto& plugin_registery = opt_res::ReachableResourcesPluginRegistry::get();
  for (const auto& p : plugin_registery.get_plugins()) {
    auto ids = p->get_reachable_resources(resources->get_base_assets_dir(),
                                          res_table->name_to_ids);
    TRACE(DEDUP_RES, 2, "Plugin %s disallowing %zu root(s)",
          p->get_name().c_str(), ids.size());
    insert_unordered_iterable(*disallowed_ids, ids);
  }
}

void DedupResourcesPass::eval_pass(DexStoresVector& /*stores*/,
                                   ConfigFiles& conf,
                                   PassManager&) {
  auto& plugin_registery = opt_res::ReachableResourcesPluginRegistry::get();
  plugin_registery.configure_plugins(conf);
}

void DedupResourcesPass::run_pass(DexStoresVector& stores,
                                  ConfigFiles& conf,
                                  PassManager& mgr) {
  std::string apk_dir;
  conf.get_json_config().get("apk_dir", "", apk_dir);
  always_assert(!apk_dir.empty());

  // 1. Basic information about what shoudln't be operate on.
  UnorderedSet<uint32_t> disallowed_types;
  UnorderedSet<uint32_t> disallowed_ids;
  prepare_disallowed_ids(apk_dir, &disallowed_types, &disallowed_ids);

  // 2. Compute duplicates/canonical resource identifiers for some types which
  //    can be references in .xml files. This step is meant to increase the
  //    liklihood of finding identical files in the next step.
  deduplicate_resource_file_references(apk_dir, m_disallowed_types,
                                       disallowed_ids);

  // 3. Perform a deduplication of individual files, which may increase the
  //    number of res table rows identified as duplicates (by rewriting file
  //    paths to a canonical version of the file).
  deduplicate_resource_files(mgr, apk_dir);

  // 4. Re-parse the resource table data to ensure latest written changes are
  //    recognized (writes do not update any cached data in these APIs).
  auto resources = create_resource_reader(apk_dir);
  auto res_table = resources->load_res_table();

  // 5. Determine the duplicate rows in the arsc; delete the duplicates, and
  //    produce a mapping from old to new resource ID's.
  std::map<uint32_t, uint32_t> dupe_to_canon =
      deduplicate_restable_rows(res_table.get(), res_table->sorted_res_ids,
                                disallowed_types, disallowed_ids, mgr);

  // 6. Renumber resources based on the deduplicated rows.
  std::map<uint32_t, uint32_t> old_to_new =
      build_remapping(res_table->sorted_res_ids,
                      res_table->id_to_name,
                      dupe_to_canon,
                      conf.metafile("redex-resid-dedup-mapping.json"));

  // 7. Renumber resources in R$ classes and all relevant XML files
  resources::RClassWriter r_class_writer(conf.get_global_config());
  r_class_writer.remap_resource_class_scalars(stores, old_to_new);

  const auto& relevant_xml_files = resources->find_all_xml_files();
  for (const std::string& path : UnorderedIterable(relevant_xml_files)) {
    resources->remap_xml_reference_attributes(path, old_to_new);
  }

  // 8. Fix up the arrays in the base R class, as well as R$styleable- any
  //    deleted entries are removed, the rest are remapped.
  r_class_writer.remap_resource_class_arrays(stores, old_to_new);

  // 9. Renumber all resource references within the resource table. And write
  // out result
  const auto& res_files = resources->find_resources_files();
  res_table->remap_res_ids_and_serialize(res_files, old_to_new);
}

static DedupResourcesPass s_pass;
