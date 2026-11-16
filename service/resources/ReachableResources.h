/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <utility>

#include "DeterministicContainers.h"
#include "GlobalConfig.h"
#include "PassManager.h"
#include "RClass.h"
#include "RedexResources.h"

namespace resources {
// Returns the IDs of every resource whose name is in `names` or starts with one
// of `prefixes`.
UnorderedSet<uint32_t> get_resources_by_prefix_and_name(
    const std::vector<std::string>& prefixes,
    const UnorderedSet<std::string>& names,
    const std::map<std::string, std::vector<uint32_t>>& name_to_ids);

class ReachableResources {
 public:
  ReachableResources(const std::string& zip_dir,
                     const GlobalConfig& global_config,
                     ReachabilityOptions options)
      : m_zip_dir(zip_dir), m_options(std::move(options)) {
    m_resources = create_resource_reader(zip_dir);
    m_res_table = m_resources->load_res_table();
    m_r_class_reader = std::make_unique<RClassReader>(global_config);
  }
  ReachableResources(const std::string& zip_dir,
                     const ResourceConfig& global_resources_config,
                     ReachabilityOptions options)
      : m_zip_dir(zip_dir), m_options(std::move(options)) {
    m_resources = create_resource_reader(zip_dir);
    m_res_table = m_resources->load_res_table();
    m_r_class_reader = std::make_unique<RClassReader>(global_resources_config);
  }

  // Establishes reachable entry points from the given classes,
  // AndroidManifest.xml files in the unpack dir, and IDs matching any
  // configured resource name prefixes.
  UnorderedSet<uint32_t> get_resource_roots(DexStoresVector& stores);
  UnorderedSet<uint32_t> compute_transitive_closure(
      const UnorderedSet<uint32_t>& roots);

  // During the computation of roots and traversals, visited xml files will be
  // tracked. Returns the state of what this object instance has explored.
  UnorderedSet<std::string> explored_xml_files() {
    return m_explored_xml_files;
  }

  // Helper objects for other callers to use
  AndroidResources* get_android_resources() { return m_resources.get(); }
  ResourceTableFile* get_res_table() { return m_res_table.get(); }

  // Metrics
  size_t code_roots_size() const { return m_code_roots; }
  size_t manifest_roots_size() const { return m_manifest_roots; }
  size_t assumed_roots_size() const { return m_assumed_roots; }

 private:
  const std::string m_zip_dir;
  const ReachabilityOptions m_options;
  std::unique_ptr<AndroidResources> m_resources;
  std::unique_ptr<ResourceTableFile> m_res_table;
  std::unique_ptr<RClassReader> m_r_class_reader;
  // State variables for what has been processed, during all API calls to this
  // class.
  UnorderedSet<std::string> m_explored_xml_files;
  // Metrics
  size_t m_code_roots{0};
  size_t m_manifest_roots{0};
  size_t m_assumed_roots{0};
};
} // namespace resources
