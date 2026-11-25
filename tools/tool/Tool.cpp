/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <boost/algorithm/string.hpp>
#include <boost/filesystem/directory.hpp>
#include <boost/filesystem/operations.hpp>
#include <boost/filesystem/path.hpp>
#include <boost/regex.hpp> // NOLINT
#include <fstream>
#include <iostream>

#include "ClassChecker.h"
#include "Debug.h"
#include "DexLoader.h"
#include "DexUtil.h"
#include "JarLoader.h"
#include "JsonWrapper.h"
#include "ReachableClasses.h"
#include "Tool.h"
#include "Trace.h"

namespace fs = boost::filesystem;

namespace {

void load_store_dexen(DexStore& store,
                      const DexMetadata& store_metadata,
                      bool verbose,
                      bool balloon,
                      bool throw_on_balloon_error,
                      int support_dex_version = 35) {
  for (const auto& file_path : store_metadata.get_files()) {
    if (verbose) {
      std::cout << "Loading " << file_path << '\n';
    }
    DexClasses classes =
        load_classes_from_dex(DexLocation::make_location("", file_path),
                              /*stats=*/nullptr,
                              /*input_dex_version*/ nullptr,
                              balloon,
                              throw_on_balloon_error,
                              support_dex_version);
    store.add_classes(std::move(classes));
  }
}

DexMetadata parse_store_metadata(const fs::path& metadata_path) {
  DexMetadata metadata;
  std::ifstream file(metadata_path.string(), std::ios::in);
  std::string line;
  while (std::getline(file, line)) {
    std::vector<std::string> tokens;
    boost::split(tokens, line, boost::is_any_of(" "));
    if (tokens.size() > 1) {
      if (tokens[0] == ".id") {
        metadata.set_id(tokens[1]);
      } else if (tokens[0] == ".requires") {
        metadata.get_dependencies().emplace_back(tokens[1]);
      }
    }
  }
  return metadata;
}

std::vector<std::string> find_store_dexen(const fs::path& store_dir_path) {
  std::vector<std::string> dexen;
  auto end = fs::directory_iterator();
  for (fs::directory_iterator it(store_dir_path); it != end; ++it) {
    auto file = it->path();
    if (fs::is_regular_file(file) &&
        (file.extension().compare(std::string(".dex")) == 0)) {
      dexen.emplace_back(file.string());
    }
  }
  return dexen;
}

std::vector<DexMetadata> find_stores(const std::string& apk_dir_str,
                                     const std::string& dexen_dir_str) {
  fs::path apk_dir_path(apk_dir_str);
  fs::path dexen_dir_path(dexen_dir_str);
  auto end = fs::directory_iterator();
  std::vector<DexMetadata> metadatas;
  for (fs::directory_iterator it(dexen_dir_path); it != end; ++it) {
    // Look for metadata.txt for this store in the apk dir
    auto metadata_path = apk_dir_path;
    metadata_path += fs::path::preferred_separator;
    metadata_path += "assets";
    metadata_path += fs::path::preferred_separator;
    metadata_path += it->path().filename().string();
    metadata_path += fs::path::preferred_separator;
    metadata_path += "metadata.txt";
    if (fs::is_regular_file(metadata_path) && fs::exists(metadata_path)) {
      // Build metadata for store
      auto metadata = parse_store_metadata(metadata_path);
      metadata.set_files(find_store_dexen(it->path()));
      metadatas.emplace_back(metadata);
    }
  }
  return metadatas;
}

} // namespace

void Tool::add_standard_options(po::options_description& options) const {
  options.add_options()(
      "jars,j",
      po::value<std::string>()->value_name("foo.jar,bar.jar,...")->required(),
      "delimited list of system jars")(
      "apkdir,a",
      po::value<std::string>()
          ->value_name("/tmp/redex_extracted_apk")
          ->required(),
      "path of an apk dir obtained from redex.py -u")(
      "dexendir,d",
      po::value<std::string>()
          ->value_name("/tmp/"
                       "redex_dexen")
          ->required(),
      "path of a dexen dir "
      "obtained from redex.py "
      "-u");
}

DexStoresVector Tool::init(const std::string& system_jar_paths,
                           const std::string& apk_dir_str,
                           const std::string& dexen_dir_str,
                           bool balloon,
                           bool throw_on_balloon_error,
                           int support_dex_version) {
  if (!fs::is_directory(fs::path(apk_dir_str))) {
    throw std::invalid_argument("'" + apk_dir_str + "' is not a directory");
  }
  if (!fs::is_directory(fs::path(dexen_dir_str))) {
    throw std::invalid_argument("'" + dexen_dir_str + "' is not a directory");
  }

  // Load jars
  if (!system_jar_paths.empty()) {
    auto delim = boost::is_any_of(":,");
    std::vector<std::string> system_jars;
    boost::split(system_jars, system_jar_paths, delim);
    for (const auto& system_jar : system_jars) {
      if (m_verbose) {
        std::cout << "Loading " << system_jar << '\n';
      }
      if (!load_jar_file(DexLocation::make_location("", system_jar))) {
        throw std::runtime_error("Could not load system jar file '" +
                                 system_jar + "'");
      }
    }
  }

  // Load dexen
  DexStore root_store("dex");
  DexStoresVector stores;

  // Load root dexen
  load_root_dexen(root_store,
                  dexen_dir_str,
                  balloon,
                  throw_on_balloon_error,
                  m_verbose,
                  support_dex_version);
  stores.emplace_back(std::move(root_store));

  // Load module dexen
  for (const auto& metadata : find_stores(apk_dir_str, dexen_dir_str)) {
    DexStore store(metadata);

    load_store_dexen(store,
                     metadata,
                     m_verbose,
                     balloon,
                     throw_on_balloon_error,
                     support_dex_version);
    stores.emplace_back(std::move(store));
  }

  Scope scope = build_class_scope(stores);
  auto class_hierarchy_errors = check_class_hierarchy(scope);
  // The message argument is evaluated only when the assertion fails.
  always_assert_type_log(!class_hierarchy_errors, RedexError::INVALID_DEX, "%s",
                         class_hierarchy_errors->c_str());

  // Initialize reachable classes
  if (m_verbose) {
    std::cout << "Initializing reachable classes" << '\n';
  }
  JsonWrapper config;
  init_reachable_classes(scope, ReachableClassesConfig(config));

  return stores;
}

void load_root_dexen(DexStore& store,
                     const std::string& dexen_dir_str,
                     bool balloon,
                     bool throw_on_balloon_error,
                     bool verbose,
                     int support_dex_version) {
  namespace fs = boost::filesystem;
  fs::path dexen_dir_path(dexen_dir_str);
  // NOLINTNEXTLINE(bugprone-assert-side-effect)
  redex_assert(fs::is_directory(dexen_dir_path));

  // Discover dex files
  auto end = fs::directory_iterator();
  std::vector<fs::path> dexen;
  for (fs::directory_iterator it(dexen_dir_path); it != end; ++it) {
    auto file = it->path();
    if (fs::is_regular_file(file) &&
        (file.extension().compare(std::string(".dex")) == 0)) {
      dexen.emplace_back(file);
    }
  }

  /*
   * Comparator for dexen filename. 'classes.dex' should sort first,
   * followed by [^\d]*[\d]+.dex ordered by N numerically.
   */
  auto dex_comparator = [](const fs::path& a, const fs::path& b) {
    boost::regex s_dex_regex("[^0-9]*([0-9]+)\\.dex");

    auto as = a.filename().string();
    auto bs = b.filename().string();
    boost::smatch amatch;
    boost::smatch bmatch;
    bool amatched = boost::regex_match(as, amatch, s_dex_regex);
    bool bmatched = boost::regex_match(bs, bmatch, s_dex_regex);

    if (!amatched && bmatched) {
      return true;
    } else if (amatched && !bmatched) {
      return false;
    } else if (!amatched && !bmatched) {
      // Compare strings, probably the same
      return strcmp(as.c_str(), bs.c_str()) > 0;
    } else {
      // Compare captures as integers
      auto anum = std::stoi(amatch[1]);
      auto bnum = std::stoi(bmatch[1]);
      return bnum > anum;
    }
  };

  // Sort all discovered dex files
  std::sort(dexen.begin(), dexen.end(), dex_comparator);
  // Load all discovered dex files
  for (const auto& dex : dexen) {
    if (verbose) {
      TRACE(MAIN, 1, "Loading %s", dex.string().c_str());
    }
    // N.B. throaway stats for now
    DexClasses classes = load_classes_from_dex(
        DexLocation::make_location("dex", dex.string()),
        /*stats=*/nullptr, /*input_dex_version=*/nullptr, balloon,
        /* throw_on_balloon_error */ throw_on_balloon_error,
        support_dex_version);
    store.add_classes(std::move(classes));
  }
}
