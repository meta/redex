/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ConfigFiles.h"

#include <boost/algorithm/string.hpp>
#include <boost/filesystem.hpp>
#include <fstream>
#include <json/json.h>
#include <string>
#include <utility>
#include <vector>

#include "BaselineProfileConfig.h"
#include "ClassUtil.h"
#include "Debug.h"
#include "DexClass.h"
#include "FrameworkApi.h"
#include "GlobalConfig.h"
#include "MethodProfiles.h"
#include "ProguardMap.h"
#include "Trace.h"

using namespace std::string_literals;
using TypeSet = std::set<const DexType*, dextypes_comparator>;

namespace {

constexpr const char* CLASS_MARKER_DELIMITER = "DexEndMarker";
constexpr const char* COLD_START_20PCT_END = "LColdStart20PctEnd";
constexpr const char* COLD_START_1PCT_END = "LColdStart1PctEnd";

enum class ComplementBetamapMode {
  kDisabled,
  kAnon,
  kAll,
  // Like kAll, but only complements the betamap's 20% tier: classes below the
  // 20% appearance threshold are dropped instead of being spliced in before
  // COLD_START_1PCT_END.
  kAll20Pct,
};

ComplementBetamapMode parse_complement_betamap_mode(const std::string& mode) {
  if (mode.empty() || mode == "disabled") {
    return ComplementBetamapMode::kDisabled;
  }
  if (mode == "anon") {
    return ComplementBetamapMode::kAnon;
  }
  if (mode == "all") {
    return ComplementBetamapMode::kAll;
  }
  if (mode == "all-20pct") {
    return ComplementBetamapMode::kAll20Pct;
  }
  always_assert_log(
      false,
      "Unknown complement_betamap_with_method_profiles_symbols "
      "mode: %s. Expected \"disabled\", \"anon\", \"all\", or \"all-20pct\".",
      mode.c_str());
}

class StringTabSplitter {
 private:
  std::string_view m_line;
  std::string_view::size_type m_start{0};
  std::string_view::size_type m_end;

  std::string_view::size_type get_end() const {
    auto end = m_line.find('\t', m_start);
    return end == std::string::npos ? m_line.size() : end;
  }

 public:
  explicit StringTabSplitter(std::string_view line)
      : m_line(line), m_end(get_end()) {}

  std::string_view get() const {
    return m_line.substr(m_start, m_end - m_start);
  }

  bool next() {
    if (m_end == m_line.size()) {
      return false;
    }
    always_assert(m_line[m_end] == '\t');
    m_start = m_end + 1;
    m_end = get_end();
    return true;
  }
};

void from_chars(std::string_view s, int64_t* res) {
  if (s.empty()) {
    return; // keep default value
  }
  std::string copy(s);
  char* endptr = nullptr;
  *res = strtol(copy.data(), &endptr, 10);
  if (endptr != copy.data() + copy.size()) {
    // Non-numeric value (e.g. "null" from Hive NULL serialization).
    // Treat as missing data and keep the struct default.
    fprintf(stderr,
            "[warning] dead_class_list: non-numeric value \"%s\", "
            "treating as default\n",
            copy.c_str());
    return;
  }
}

// Strip surrounding double quotes from a string_view, if present.
std::string_view unquote(std::string_view s) {
  if (s.size() >= 2 && s.front() == '"' && s.back() == '"') {
    s.remove_prefix(1);
    s.remove_suffix(1);
  }
  return s;
}
} // namespace

ConfigFiles::ConfigFiles(const Json::Value& config, std::string outdir)
    : m_json(config),
      outdir(std::move(outdir)),
      m_global_config(
          std::make_unique<GlobalConfig>(GlobalConfig::default_registry())),
      m_proguard_map(
          new ProguardMap(config.get("proguard_map", "").asString(),
                          config.get("use_new_rename_map", 0).asBool())),
      m_coldstart_methods_filename(
          config.get("coldstart_methods_file", "").asString()),
      m_preprocessed_baseline_profile_directory(
          config.get("preprocessed_baseline_profile_directory", "").asString()),
      m_printseeds(config.get("printseeds", "").asString()),
      m_method_profiles(new method_profiles::MethodProfiles()) {

  m_coldstart_class_filename = config.get("coldstart_classes", "").asString();
  if (m_coldstart_class_filename.empty()) {
    m_coldstart_class_filename =
        config.get("default_coldstart_classes", "").asString();
  }

  m_class_frequency_filename = config.get("class_frequencies", "").asString();
  if (m_class_frequency_filename.empty()) {
    m_class_frequency_filename =
        config.get("default_class_frequencies", "").asString();
  }

  uint32_t instruction_size_bitwidth_limit =
      config.get("instruction_size_bitwidth_limit", 0).asUInt();
  always_assert_log(
      instruction_size_bitwidth_limit < 32,
      "instruction_size_bitwidth_limit must be between 0 and 31, actual: %u\n",
      instruction_size_bitwidth_limit);
  m_instruction_size_bitwidth_limit = instruction_size_bitwidth_limit;

  m_recognize_coldstart_pct_marker =
      config.get("recognize_betamap_coldstart_pct_marker", false).asBool();

  m_baseline_profile_config_file_name =
      config.get("baseline_profile_config", "").asString();
  if (!m_baseline_profile_config_file_name.empty()) {
    m_baseline_profile_config_file_name += "/baseline_profile_configs.json";
  }
}

ConfigFiles::ConfigFiles(const Json::Value& config) : ConfigFiles(config, "") {}

ConfigFiles::~ConfigFiles() {
  // Here so that we can use `unique_ptr` to hide full class defs in the header.
}

/**
 * This function relies on the g_redex.
 */
const UnorderedSet<DexType*>& ConfigFiles::get_no_optimizations_annos() {
  if (m_no_optimizations_annos.empty()) {
    Json::Value no_optimizations_anno;
    m_json.get("no_optimizations_annotations", Json::nullValue,
               no_optimizations_anno);
    if (!no_optimizations_anno.empty()) {
      for (auto const& config_anno_name : no_optimizations_anno) {
        std::string anno_name = config_anno_name.asString();
        DexType* anno = DexType::get_type(anno_name);
        if (anno != nullptr) {
          m_no_optimizations_annos.insert(anno);
        }
      }
    }
  }
  return m_no_optimizations_annos;
}

const UnorderedSet<std::string>& ConfigFiles::get_no_optimizations_blocklist() {
  if (m_no_optimizations_blocklist.empty()) {
    Json::Value no_optimizations_blocklist;
    m_json.get("no_optimizations_blocklist", Json::nullValue,
               no_optimizations_blocklist);
    if (!no_optimizations_blocklist.empty()) {
      for (auto const& name : no_optimizations_blocklist) {
        m_no_optimizations_blocklist.insert(name.asString());
      }
    }
  }
  return m_no_optimizations_blocklist;
}

/**
 * This function relies on the g_redex.
 */
const UnorderedSet<DexMethodRef*>& ConfigFiles::get_pure_methods() {
  if (m_pure_methods.empty()) {
    Json::Value pure_methods;
    m_json.get("pure_methods", Json::nullValue, pure_methods);
    if (!pure_methods.empty()) {
      for (auto const& method_name : pure_methods) {
        std::string name = method_name.asString();
        DexMethodRef* method = DexMethod::get_method(name);
        if (method != nullptr) {
          m_pure_methods.insert(method);
        }
      }
    }
  }
  return m_pure_methods;
}

/**
 * This function relies on the g_redex.
 */
const UnorderedSet<const DexString*>& ConfigFiles::get_finalish_field_names() {
  if (m_finalish_field_names.empty()) {
    Json::Value finalish_field_names;
    m_json.get("finalish_field_names", Json::nullValue, finalish_field_names);
    if (!finalish_field_names.empty()) {
      for (auto const& field_name : finalish_field_names) {
        std::string name = field_name.asString();
        const auto* str = DexString::make_string(name);
        if (str != nullptr) {
          m_finalish_field_names.insert(str);
        }
      }
    }
  }
  return m_finalish_field_names;
}

/**
 * This function relies on the g_redex.
 */

const UnorderedSet<DexType*>& ConfigFiles::get_do_not_devirt_anon() {
  if (m_no_devirtualize_annos.empty()) {
    std::vector<std::string> no_devirtualize_anno_names;
    m_json.get("no_devirtualize_annos", {}, no_devirtualize_anno_names);
    if (!no_devirtualize_anno_names.empty()) {
      for (auto& name : no_devirtualize_anno_names) {
        auto* typ = DexType::get_type(name);
        if (typ != nullptr) {
          m_no_devirtualize_annos.insert(typ);
        }
      }
    }
  }
  return m_no_devirtualize_annos;
}

UnorderedMap<const DexString*, std::vector<uint8_t>>
ConfigFiles::load_class_frequencies() {
  if (m_class_frequency_filename.empty()) {
    return {};
  }
  Timer t("loading class frequencies");
  std::ifstream input(m_class_frequency_filename, std::ios_base::in);

  UnorderedMap<const DexString*, std::vector<uint8_t>> class_freq_map;

  std::string line;
  std::getline(input, line);
  // line containing all interactions
  boost::trim(line);
  boost::split(m_interactions, line, boost::is_any_of(" "));

  while (std::getline(input, line)) {
    // each line follows the format
    // class_name,0 0 0 0 0
    auto comma = line.find(',');

    std::vector<std::string> frequencies;
    boost::split(frequencies, line.substr(comma + 1, line.length()),
                 boost::is_any_of(" "));
    std::vector<uint8_t> int_frequencies(frequencies.size());
    std::transform(frequencies.begin(), frequencies.end(),
                   int_frequencies.begin(),
                   [](const std::string& val) { return std::stoi(val); });

    class_freq_map[DexString::make_string(line.substr(0, comma))] =
        int_frequencies;
  }
  return class_freq_map;
}

/**
 * Read an interdex list file and return as a vector of appropriately-formatted
 * classname strings.
 */
std::vector<std::string> ConfigFiles::load_coldstart_classes() {
  if (m_coldstart_class_filename.empty()) {
    return {};
  }

  static constexpr std::string_view kClassTail = ".class";
  static constexpr size_t lentail = kClassTail.size();

  std::vector<std::string> coldstart_classes;

  std::ifstream input(m_coldstart_class_filename);
  if (!input) {
    throw RedexException(
        RedexError::INVALID_BETAMAP,
        "[error] Cannot open <coldstart_classes> file, path is "s +
            m_coldstart_class_filename);
  }

  auto validate_class_spec =
      [](std::string_view class_spec) -> std::pair<bool, size_t> {
    if (lentail >= class_spec.size()) {
      return {false, static_cast<size_t>(-1)};
    }

    auto pos_tail = class_spec.size() - lentail;

    if (class_spec.compare(pos_tail, lentail, kClassTail) != 0) {
      return {false, static_cast<size_t>(-1)};
    }

    return {true, pos_tail};
  };

  // Inject MethodProfile coldstart classes
  const auto& coldstart_stats =
      get_method_profiles().method_stats(method_profiles::COLD_START);
  auto complement_mode_str = get_json_config().get(
      "complement_betamap_with_method_profiles_symbols", std::string(""));
  auto complement_mode = parse_complement_betamap_mode(complement_mode_str);
  TRACE(CF, 1, "complement_betamap mode: \"%s\"", complement_mode_str.c_str());
  bool add_method_profiles_symbols =
      complement_mode != ComplementBetamapMode::kDisabled &&
      !coldstart_stats.empty();
  TypeSet coldstart_20pct_classes;
  TypeSet coldstart_1pct_classes;
  TypeSet non_anon_classes;
  if (add_method_profiles_symbols) {
    always_assert(!coldstart_stats.empty());
    for (const auto& meth_stats : UnorderedIterable(coldstart_stats)) {
      const DexMethodRef* method = meth_stats.first;

      const auto* clz = type_class(method->get_class());
      if (clz == nullptr) {
        TRACE(CF, 2, "Skipping method from class not in scope: %s",
              method->get_class()->c_str());
        continue;
      }
      if (complement_mode == ComplementBetamapMode::kAnon &&
          !klass::maybe_anonymous_class(clz)) {
        continue;
      }
      if (!klass::maybe_anonymous_class(clz)) {
        non_anon_classes.insert(method->get_class());
      }

      if (meth_stats.second.appear_percent >= 20.0) {
        coldstart_20pct_classes.insert(method->get_class());
      } else if (complement_mode != ComplementBetamapMode::kAll20Pct &&
                 meth_stats.second.appear_percent >= 1.0) {
        coldstart_1pct_classes.insert(method->get_class());
      }
    }

    TRACE(CF, 1, "coldstart class: 20 pct %zu", coldstart_20pct_classes.size());
    TRACE(CF, 1, "coldstart class: 1 pct %zu", coldstart_1pct_classes.size());
    TRACE(CF, 1, "coldstart class: non-anon %zu", non_anon_classes.size());
  }

  std::string clzname;
  while (input >> clzname) {
    auto [valid_class_spec, pos_tail] = validate_class_spec(clzname);
    if (!valid_class_spec) {
      throw RedexException(RedexError::INVALID_BETAMAP,
                           "Bailing, invalid class spec"s +
                               m_coldstart_class_filename +
                               " in interdex file " + clzname);
    }

    clzname.replace(pos_tail, lentail, ";");
    clzname = m_proguard_map->translate_class("L" + clzname);
    coldstart_classes.emplace_back(clzname);

    if (add_method_profiles_symbols) {
      // Dedup anonymous classes
      auto* type = DexType::get_type(clzname);
      if (type == nullptr) {
        continue;
      } else if (coldstart_20pct_classes.count(type) != 0u) {
        coldstart_20pct_classes.erase(type);
      } else if (coldstart_1pct_classes.count(type) != 0u) {
        coldstart_1pct_classes.erase(type);
      }
    }
  }

  if (add_method_profiles_symbols) {
    TRACE(CF, 1, "coldstart class: 20 pct %zu", coldstart_20pct_classes.size());
    TRACE(CF, 1, "coldstart class: 1 pct %zu", coldstart_1pct_classes.size());

    if (traceEnabled(CF, 3)) {
      for (const auto* type : coldstart_20pct_classes) {
        auto* appended_cls = type_class(type);
        TRACE(CF, 3, "coldstart appended 20pct %s: %s",
              (appended_cls && klass::maybe_anonymous_class(appended_cls))
                  ? "anon"
                  : "general",
              type->c_str());
      }
      for (const auto* type : coldstart_1pct_classes) {
        auto* appended_cls = type_class(type);
        TRACE(CF, 3, "coldstart appended 1pct %s: %s",
              (appended_cls && klass::maybe_anonymous_class(appended_cls))
                  ? "anon"
                  : "general",
              type->c_str());
      }
    }

    std::vector<std::string> coldstart_classes_with_method_profile_symbols;
    coldstart_classes_with_method_profile_symbols.reserve(
        coldstart_classes.size() + coldstart_20pct_classes.size() +
        coldstart_1pct_classes.size());

    for (auto& cls_name : coldstart_classes) {
      if (cls_name.find(COLD_START_20PCT_END) != std::string::npos) {
        for (const auto* type : coldstart_20pct_classes) {
          coldstart_classes_with_method_profile_symbols.emplace_back(
              type->str_copy());
        }
      } else if (cls_name.find(COLD_START_1PCT_END) != std::string::npos) {
        for (const auto* type : coldstart_1pct_classes) {
          coldstart_classes_with_method_profile_symbols.emplace_back(
              type->str_copy());
        }
      }

      coldstart_classes_with_method_profile_symbols.emplace_back(cls_name);
    }

    // Finally swap the coldstart_classes.
    coldstart_classes = coldstart_classes_with_method_profile_symbols;
  }

  return coldstart_classes;
}

/**
 * Read a method ordering file for coldstart and return as a vector of
 * appropriately-formatted methodname strings.
 */
std::vector<std::string> ConfigFiles::load_coldstart_methods() {
  if (m_coldstart_methods_filename.empty()) {
    return {};
  }
  std::vector<std::string> coldstart_methods;
  std::ifstream input(m_coldstart_methods_filename);
  if (!input) {
    throw RedexException(
        RedexError::INTERNAL_ERROR,
        "[error] Cannot open <coldstart_meth_ordering> file, path is "s +
            m_coldstart_methods_filename);
  }

  std::string method;
  while (input >> method) {
    coldstart_methods.emplace_back(method);
  }
  return coldstart_methods;
}

std::string ConfigFiles::get_preprocessed_baseline_profile_file(
    const std::string& config_name) const {
  return m_preprocessed_baseline_profile_directory + "/" + config_name +
         "-baseline-profile.txt";
}

/**
 * Read a map of {list_name : class_list} from json
 */
UnorderedMap<std::string, std::vector<std::string>>
ConfigFiles::load_class_lists() {
  UnorderedMap<std::string, std::vector<std::string>> lists;
  std::string class_lists_filename;
  this->m_json.get("class_lists", "", class_lists_filename);

  if (class_lists_filename.empty()) {
    return lists;
  }

  std::ifstream input(class_lists_filename);
  Json::Reader reader;
  Json::Value root;
  bool parsing_succeeded = reader.parse(input, root);
  always_assert_log(
      parsing_succeeded, "Failed to parse class list json from file: %s\n%s",
      class_lists_filename.c_str(), reader.getFormattedErrorMessages().c_str());

  for (Json::ValueIterator it = root.begin(); it != root.end(); ++it) {
    std::vector<std::string> class_list;
    Json::Value current_list = *it;
    for (Json::ValueIterator list_it = current_list.begin();
         list_it != current_list.end();
         ++list_it) {
      lists[it.key().asString()].push_back((*list_it).asString());
    }
  }

  lists["secondary_dex_head.list"] = get_coldstart_classes();

  return lists;
}

const UnorderedMap<std::string, ConfigFiles::DeadClassLoadCounts>&
ConfigFiles::get_dead_class_list() {
  build_dead_class_and_live_class_split_lists();
  return m_dead_classes;
}

const std::vector<std::string>& ConfigFiles::get_halfnosis_block_list() {
  build_halfnosis_block_list();
  return m_halfnosis_block_list;
}

const UnorderedSet<std::string>& ConfigFiles::get_live_class_split_list() {
  build_dead_class_and_live_class_split_lists();
  return m_live_relocated_classes;
}

bool ConfigFiles::is_relocated_class(std::string_view name) const {
  return name.ends_with(CLASS_SPLITTING_RELOCATED_SUFFIX);
}

void ConfigFiles::remove_relocated_part(std::string_view* name) {
  always_assert(name != nullptr);
  if (name->length() < CLASS_SPLITTING_RELOCATED_SUFFIX_LEN) {
    return;
  }
  name->remove_suffix(CLASS_SPLITTING_RELOCATED_SUFFIX_LEN);
}

void ConfigFiles::build_dead_class_and_live_class_split_lists() {
  if (!m_dead_class_list_attempted) {
    m_dead_class_list_attempted = true;
    std::string dead_class_list_filename;
    this->m_json.get("dead_class_list", "", dead_class_list_filename);
    if (!dead_class_list_filename.empty()) {
      std::ifstream input(dead_class_list_filename);
      if (!input) {
        fprintf(stderr,
                "[error] Cannot open <dead_class_list> file, path is %s\n",
                dead_class_list_filename.c_str());
        exit(EXIT_FAILURE);
      }
      for (std::string line; std::getline(input, line);) {
        // trim trailing whitespace
        line.erase(std::find_if(line.rbegin(), line.rend(),
                                [](auto c) { return c > ' '; })
                       .base(),
                   line.end());
        DeadClassLoadCounts load_counts;
        StringTabSplitter splitter(line);
        std::string_view classname = unquote(splitter.get());
        const uint32_t k_num_remaining_columns = 5;
        std::array<int64_t*, k_num_remaining_columns> columns = {
            &load_counts.sampled, &load_counts.unsampled,
            &load_counts.beta_unsampled, &load_counts.last_modified_count,
            &load_counts.seconds_since_last_modified};
        for (uint32_t i = 0; splitter.next() && i < k_num_remaining_columns;
             i++) {
          from_chars(splitter.get(), columns[i]);
        }

        bool is_relocated = is_relocated_class(classname);
        if (is_relocated) {
          remove_relocated_part(&classname);
        }
        std::string converted;
        converted.reserve(classname.size() + 2);
        converted.append(1, 'L');
        converted.append(classname);
        converted.append(1, ';');
        std::replace(converted.begin(), converted.end(), '.', '/');
        if (!is_relocated) {
          auto translated = m_proguard_map->translate_class(converted);
          m_dead_classes.emplace(std::move(translated), load_counts);
        } else {
          // No need to proguard translate the name of the live classes since
          // we use the unobfuscated name. The unobfuscated name is already
          // translated in ProguardMap.apply_deobfuscated_names called
          // from redex_frontend in main.cpp.
          m_live_relocated_classes.insert(std::move(converted));
        }
      }
    }
  }
}

void ConfigFiles::build_halfnosis_block_list() {
  if (!m_halfnosis_block_list_attempted) {
    m_halfnosis_block_list_attempted = true;
    std::string halfnosis_block_list_filename;
    this->m_json.get("halfnosis_block_list", "", halfnosis_block_list_filename);
    if (!halfnosis_block_list_filename.empty()) {
      std::ifstream input(halfnosis_block_list_filename);
      if (!input) {
        fprintf(stderr,
                "[error] Cannot open <halfnosis_block_list> file, path is %s\n",
                halfnosis_block_list_filename.c_str());
        exit(EXIT_FAILURE);
      }
      for (std::string line; std::getline(input, line);) {
        // trim trailing whitespace
        line.erase(std::find_if(line.rbegin(), line.rend(),
                                [](auto c) { return c > ' '; })
                       .base(),
                   line.end());
        m_halfnosis_block_list.push_back(line);
      }
    }
  }
}

const method_profiles::MethodProfiles& ConfigFiles::get_method_profiles()
    const {
  always_assert_log(m_method_profiles->is_initialized(),
                    "Cannot initialize method stats in a const function.");
  return *m_method_profiles;
}

void ConfigFiles::ensure_agg_method_stats_loaded() {
  if (m_method_profiles->is_initialized()) {
    return;
  }
  std::vector<std::string> csv_filenames;
  get_json_config().get("agg_method_stats_files", {}, csv_filenames);
  std::vector<std::string> baseline_profile_csv_filenames;
  get_json_config().get("baseline_profile_agg_method_stats_files", {},
                        baseline_profile_csv_filenames);
  if (csv_filenames.empty() && baseline_profile_csv_filenames.empty() &&
      !baseline_profiles_has_manual_profiles()) {
    return;
  }
  m_method_profiles->initialize(csv_filenames, baseline_profile_csv_filenames,
                                get_baseline_profile_configs());
  bool ignore_split_methods = false;
  get_json_config().get("agg_method_stats_ignore_split_methods", false,
                        ignore_split_methods);
  if (ignore_split_methods) {
    auto dropped = m_method_profiles->drop_unresolved_split_lines();
    TRACE(METH_PROF, 1,
          "Dropped %zu unresolved method profile lines of split "
          "methods",
          dropped);
  }
}

bool ConfigFiles::get_did_use_bzl_baseline_profile_config() {
  return !m_baseline_profile_config_file_name.empty();
}

void ConfigFiles::init_baseline_profile_configs() {
  Json::Value baseline_profile_config_list_json;
  if (!m_baseline_profile_config_file_name.empty()) {
    std::ifstream input(m_baseline_profile_config_file_name);
    Json::Reader reader;
    bool parsing_succeeded =
        reader.parse(input, baseline_profile_config_list_json);
    always_assert_log(parsing_succeeded,
                      "Failed to parse class list json from file: %s\n%s",
                      m_baseline_profile_config_file_name.c_str(),
                      reader.getFormattedErrorMessages().c_str());
  } else {
    get_json_config().get("baseline_profile", {},
                          baseline_profile_config_list_json);
  }

  UnorderedMap<std::string, baseline_profiles::BaselineProfileConfig>
      baseline_profile_config_list;

  // Make sure that if list is not empty, it has a default config
  always_assert(baseline_profile_config_list_json.empty() ||
                baseline_profile_config_list_json.isMember(std::string(
                    baseline_profiles::DEFAULT_BASELINE_PROFILE_CONFIG_NAME)));
  for (auto it = baseline_profile_config_list_json.begin();
       it != baseline_profile_config_list_json.end();
       ++it) {
    std::string config_name = it.memberName();
    const auto& baseline_profile_config_jw = JsonWrapper(*it);
    auto current_baseline_profile_config =
        baseline_profiles::BaselineProfileConfig();
    baseline_profile_config_jw.get(
        "oxygen_modules", false,
        current_baseline_profile_config.options.oxygen_modules);
    baseline_profile_config_jw.get(
        "strip_classes", false,
        current_baseline_profile_config.options.strip_classes);
    baseline_profile_config_jw.get(
        "transitively_close_classes", true,
        current_baseline_profile_config.options.transitively_close_classes);
    baseline_profile_config_jw.get(
        "use_redex_generated_profile", false,
        current_baseline_profile_config.options.use_redex_generated_profile);
    baseline_profile_config_jw.get("use_final_redex_generated_profile", true,
                                   current_baseline_profile_config.options
                                       .use_final_redex_generated_profile);
    baseline_profile_config_jw.get("include_betamap_20pct_coldstart", true,
                                   current_baseline_profile_config.options
                                       .include_betamap_20pct_coldstart);
    baseline_profile_config_jw.get(
        "betamap_include_coldstart_1pct", false,
        current_baseline_profile_config.options.betamap_include_coldstart_1pct);
    Json::Value deepdata_interactions_json;
    baseline_profile_config_jw.get(
        "include_all_startup_classes", false,
        current_baseline_profile_config.options.include_all_startup_classes);
    baseline_profile_config_jw.get("deep_data_interaction_config", {},
                                   deepdata_interactions_json);
    for (auto interaction_it = deepdata_interactions_json.begin();
         interaction_it != deepdata_interactions_json.end();
         ++interaction_it) {
      std::string key = interaction_it.memberName();

      const auto& interaction_id = key;

      current_baseline_profile_config.interaction_configs[interaction_id] = {};

      auto& bpi_config =
          current_baseline_profile_config.interaction_configs[interaction_id];

      const auto& bpi_config_jw = JsonWrapper(*interaction_it);

      bpi_config_jw.get("call_threshold", 1, bpi_config.call_threshold);
      bpi_config_jw.get("classes", true, bpi_config.classes);
      bpi_config_jw.get("post_startup", true, bpi_config.post_startup);
      bpi_config_jw.get("startup", false, bpi_config.startup);
      bpi_config_jw.get("threshold", 80, bpi_config.threshold);
      always_assert(bpi_config_jw.contains("name"));
      std::string name = bpi_config_jw.get("name", std::string());

      current_baseline_profile_config.interactions.emplace_back(
          interaction_id, std::move(name));
    }
    Json::Value harvest_config_json;
    baseline_profile_config_jw.get("harvest_config", {}, harvest_config_json);
    current_baseline_profile_config.harvest_config.load_from_json(
        harvest_config_json);

    baseline_profile_config_jw.get(
        "manual_profiles",
        std::vector<std::string>(),
        current_baseline_profile_config.manual_files);

    // The manual profiles exist in the same folder as the config file
    // so mutate the path to reflect that.
    if (!m_baseline_profile_config_file_name.empty()) {
      boost::filesystem::path p(m_baseline_profile_config_file_name);
      boost::filesystem::path dir = p.parent_path();
      for (auto& manual_file : current_baseline_profile_config.manual_files) {
        manual_file = (dir / manual_file).string();
      }
    }

    baseline_profile_config_list.emplace(std::move(config_name),
                                         current_baseline_profile_config);
  }

  // Insert a default-constructed config with default values if
  // no "default" key was found.  Otherwise, this looks up the existing
  // value for "default".
  baseline_profile_config_list.emplace(
      std::string(baseline_profiles::DEFAULT_BASELINE_PROFILE_CONFIG_NAME),
      baseline_profiles::BaselineProfileConfig());

  m_baseline_profile_config_list = std::make_unique<
      UnorderedMap<std::string, baseline_profiles::BaselineProfileConfig>>(
      std::move(baseline_profile_config_list));
}

const baseline_profiles::BaselineProfileConfigMap&
ConfigFiles::get_baseline_profile_configs() {
  if (m_baseline_profile_config_list == nullptr) {
    init_baseline_profile_configs();
    redex_assert(m_baseline_profile_config_list != nullptr);
  }

  always_assert(m_baseline_profile_config_list->count(
      baseline_profiles::DEFAULT_BASELINE_PROFILE_CONFIG_NAME));
  return *m_baseline_profile_config_list;
}

bool ConfigFiles::baseline_profiles_has_manual_profiles() {
  const auto& baseline_profile_configs =
      UnorderedIterable(get_baseline_profile_configs());
  return std::any_of(
      baseline_profile_configs.begin(), baseline_profile_configs.end(),
      [](const auto& p) { return !p.second.manual_files.empty(); });
}

const baseline_profiles::BaselineProfileConfig&
ConfigFiles::get_default_baseline_profile_config() {
  if (m_baseline_profile_config_list == nullptr) {
    init_baseline_profile_configs();
    redex_assert(m_baseline_profile_config_list != nullptr);
  }
  return m_baseline_profile_config_list->at(
      std::string(baseline_profiles::DEFAULT_BASELINE_PROFILE_CONFIG_NAME));
}

void ConfigFiles::parse_global_config() {
  redex_assert(m_global_config != nullptr);
  m_global_config->parse_config(m_json);
}

void ConfigFiles::load(const Scope& scope, Architecture architecture) {
  auto* inliner_config =
      get_global_config().get_config_by_name<InlinerConfig>("inliner");
  inliner_config->set_architecture(architecture);
  inliner_config->populate(scope);
}

void ConfigFiles::process_unresolved_method_profile_lines() {
  ensure_agg_method_stats_loaded();
  m_method_profiles->process_unresolved_lines();
}

const api::AndroidSDK& ConfigFiles::get_android_sdk_api(int32_t min_sdk_api) {
  if (m_android_min_sdk_api == nullptr) {
    always_assert(m_min_sdk_api_level == 0); // not set
    m_min_sdk_api_level = min_sdk_api;
    auto api_file = get_android_sdk_api_file(min_sdk_api);
    m_android_min_sdk_api = std::make_unique<api::AndroidSDK>(api_file);
  }

  always_assert(min_sdk_api == m_min_sdk_api_level);
  return *m_android_min_sdk_api;
}

const ProguardMap& ConfigFiles::get_proguard_map() const {
  return *m_proguard_map;
}

bool ConfigFiles::force_single_dex() const {
  return m_json.get("force_single_dex", false);
}

bool ConfigFiles::disable_violation_fixes() const {
  return m_json.get("disable_violation_fixes", false);
}

bool ConfigFiles::preserve_count_integrity() const {
  return m_json.get("preserve_count_integrity", false);
}

bool ConfigFiles::emit_incoming_hashes() const {
  return m_json.get("emit_incoming_hashes", false);
}

bool ConfigFiles::emit_outgoing_hashes() const {
  return m_json.get("emit_outgoing_hashes", false);
}

bool ConfigFiles::create_init_class_insns() const {
  return m_json.get("create_init_class_insns", true);
}

bool ConfigFiles::finalize_resource_table() const {
  return m_json.get("finalize_resource_table", false);
}

bool ConfigFiles::evaluate_package_name() const {
  return m_json.get("evaluate_package_name", true);
}

bool ConfigFiles::enforce_class_order() const {
  return m_json.get("enforce_class_order", false);
}

bool ConfigFiles::normal_primary_dex() const {
  // Sniff the InterDexPass config, to avoid having redundant configuration
  // values all over.
  bool result{true};
  Json::Value interdex_pass_config;
  m_json.get("InterDexPass", Json::nullValue, interdex_pass_config);
  if (!interdex_pass_config.empty()) {
    JsonWrapper interdex_jw(interdex_pass_config);
    interdex_jw.get("normal_primary_dex", true, result);
  }
  return result;
}

void ConfigFiles::set_outdir(const std::string& new_outdir) {
  // Gotta ensure "meta" exists.
  auto meta_path = boost::filesystem::path(new_outdir) / "meta";
  boost::filesystem::create_directory(meta_path);
  outdir = new_outdir;
}

void ConfigFiles::set_class_lists(
    UnorderedMap<std::string, std::vector<std::string>> l) {
  m_class_lists = std::move(l);
  m_load_class_lists_attempted = true;
}

void ConfigFiles::build_cls_interdex_groups() {
  const auto& interdex_order = get_coldstart_classes();
  if (interdex_order.empty()) {
    // No grouping based on interdex.
    m_num_interdex_groups = 0;
    return;
  }

  size_t group_id = 0;
  for (auto it = interdex_order.begin(); it != interdex_order.end(); ++it) {
    const auto& cls_name = *it;
    bool is_marker_delim =
        cls_name.find(CLASS_MARKER_DELIMITER) != std::string::npos;
    auto is_coldstart_pct_marker = [this](const std::string& cls_name) {
      if (!m_recognize_coldstart_pct_marker) {
        return false;
      }
      return cls_name.find(COLD_START_20PCT_END) != std::string::npos ||
             cls_name.find(COLD_START_1PCT_END) != std::string::npos;
    };

    if (is_marker_delim || is_coldstart_pct_marker(cls_name) ||
        std::next(it) == interdex_order.end()) {
      group_id++;

      if (is_marker_delim) {
        continue;
      }
    }

    DexType* type = DexType::get_type(cls_name);
    if (type != nullptr) {
      m_cls_to_interdex_group.try_emplace(type, group_id);
    }
  }

  // group_id + 1 represents the number of groups (considering the classes
  // outside of the interdex order as a group on its own).
  m_num_interdex_groups = group_id + 1;
}

const GlobalConfig& ConfigFiles::get_global_config() const {
  redex_assert(m_global_config != nullptr);
  return *m_global_config;
}
