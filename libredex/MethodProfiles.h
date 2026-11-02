/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <optional>
#include <string_view>

#include "BaselineProfileConfig.h"
#include "DeterministicContainers.h"
#include "DexClass.h"
#include "Timer.h"
#include "Trace.h"

struct MethodProfileOrderingConfig;

namespace method_profiles {

// These names (and their order) match the columns of the csv
enum : uint8_t {
  INDEX,
  NAME,
  APPEAR100,
  APPEAR_NUMBER,
  AVG_CALL,
  AVG_ORDER,
  AVG_RANK100,
  MIN_API_LEVEL,
};

enum ParsingMode {
  // NONE is the initial state. We haven't parsed a header yet
  NONE,
  MAIN,
  METADATA,
};

struct Stats {
  // The percentage of samples that this method appeared in
  double appear_percent{0.0}; // appear100

  // Number of invocations of this method (averaged over all samples)
  double call_count{0.0}; // avg_call

  // Relative index when this method is first executed (averaged over all
  // samples)
  // * 0.0 means the beginning of the measured period
  // * 100.0 means the end of the measured period
  double order_percent{0.0}; // avg_rank100

  // The minimum API level that this method was observed running on
  int16_t min_api_level{0}; // min_api_level

  bool operator==(const Stats& other) const {
    return appear_percent == other.appear_percent &&
           call_count == other.call_count &&
           order_percent == other.order_percent &&
           min_api_level == other.min_api_level;
  }
};

using StatsMap = UnorderedMap<const DexMethodRef*, Stats>;
using AllInteractions = std::map<std::string, StatsMap>;
inline const std::string COLD_START = "ColdStart";

class MethodProfiles {
 public:
  MethodProfiles() {}

  void initialize(
      const std::vector<std::string>& csv_filenames,
      const std::vector<std::string>& baseline_profile_csv_filenames,
      const UnorderedMap<std::string, baseline_profiles::BaselineProfileConfig>&
          baseline_profile_configs);

  // For testing purposes.
  static MethodProfiles initialize(
      const std::string& interaction_id,
      UnorderedMap<const DexMethodRef*, Stats> data) {
    MethodProfiles ret{};
    ret.m_initialized = true;
    ret.m_method_stats[interaction_id] = std::move(data);
    return ret;
  }

  bool is_initialized() const { return m_initialized; }

  bool has_stats() const { return !m_method_stats.empty(); }

  size_t size() const {
    size_t sum{0};
    for (const auto& p : m_method_stats) {
      sum += p.second.size();
    }
    return sum;
  }

  size_t unresolved_size() const { return m_unresolved_lines.size(); }

  // Get the method profiles for some interaction id.
  // If no interactions are found by that interaction id, Return an empty map.
  const StatsMap& method_stats(const std::string& interaction_id) const;

  const StatsMap& method_stats_for_baseline_config(
      const std::string& interaction_id,
      const std::string& baseline_config_name) const;

  const AllInteractions& all_interactions() const { return m_method_stats; }

  std::optional<Stats> get_method_stat(const std::string& interaction_id,
                                       const DexMethodRef* m) const {
    const auto& stats = method_stats(interaction_id);
    auto it = stats.find(m);
    if (it == stats.end()) {
      return std::nullopt;
    }
    return it->second;
  }

  void set_method_stats(const std::string& interaction_id,
                        const DexMethodRef* m,
                        Stats stats);

  std::optional<uint32_t> get_interaction_count(
      const std::string& interaction_id) const;

  // Try to resolve previously unresolved lines
  void process_unresolved_lines();

  // Drops the unresolved lines of split methods, so methods created later by
  // method splitting are never matched to them by name. Split names such as
  // `get$split$hot_cold$0$2` give a position, not the code: the method with
  // that name in this build can hold different code from the profiled one.
  // Returns how many lines were dropped.
  size_t drop_unresolved_split_lines();

  struct ManualProfileLine {
    std::string current_line;
    std::string flags;
    std::vector<std::string> method_and_class;
    std::vector<std::string> config_names;
    std::string manual_filename;
  };

  UnorderedSet<dex_member_refs::MethodDescriptorTokens>
  get_unresolved_method_descriptor_tokens() const;

  void resolve_method_descriptor_tokens(
      const UnorderedMap<dex_member_refs::MethodDescriptorTokens,
                         std::vector<DexMethodRef*>>& map);

  // If there are no observed stats for the target, derive it from the given
  // sources.
  size_t derive_stats(DexMethod* target,
                      const std::vector<DexMethod*>& sources);

  // Substitute target method's stat with derived stats from given sources.
  size_t substitute_stats(DexMethod* target,
                          const std::vector<DexMethod*>& sources);

 private:
  static AccumulatingTimer& get_process_unresolved_lines_timer();
  AllInteractions m_method_stats;
  AllInteractions m_baseline_profile_method_stats;
  std::map<std::string, AllInteractions*> m_baseline_manual_interactions;
  std::map<std::string, AllInteractions> m_manual_profile_interactions;
  // Resolution may fail because of renaming or generated methods. Store the
  // unresolved lines here (per interaction) so we can update after passes run
  // and change the names of methods
  struct ParsedMain {
    std::unique_ptr<std::string> line_interaction_id;
    std::unique_ptr<std::string> ref_str;
    std::optional<dex_member_refs::MethodDescriptorTokens> mdt;
    DexMethodRef* ref = nullptr;
    Stats stats;
  };
  std::vector<ParsedMain> m_unresolved_lines;
  std::vector<ParsedMain> m_baseline_profile_unresolved_lines;
  std::vector<ManualProfileLine> m_unresolved_manual_lines;
  UnorderedMap<std::string, UnorderedMap<std::string, DexMethodRef*>>
      m_baseline_profile_method_map;
  std::unordered_set<DexMethodRef*> m_parsed_manual_methods;
  ParsingMode m_mode{NONE};
  // A map from interaction ID to the number of times that interaction was
  // triggered. This can be used to compare relative prevalence of different
  // interactions.
  UnorderedMap<std::string, uint32_t> m_interaction_counts;
  // A map from column index to column header
  UnorderedMap<uint32_t, std::string> m_optional_columns;
  // The interaction id from the metadata at the top of the file
  std::string m_interaction_id;
  bool m_initialized{false};

  // Read a "simple" csv file (no quoted commas or extra spaces) and populate
  // m_method_stats
  bool parse_stats_file(const std::string& csv_filename,
                        bool baseline_profile_variant);

  const UnorderedMap<std::string, UnorderedMap<std::string, DexMethodRef*>>&
  get_baseline_profile_method_map(bool recompute);

  // Read a line of data (not a header)
  bool parse_line(const std::string& line, bool baseline_profile_variant);
  // Read a line from the main section of the aggregated stats file and put an
  // entry into m_method_stats
  bool parse_main(const std::string& line,
                  std::string* interaction_id,
                  bool baseline_profile_variant);
  std::optional<ParsedMain> parse_main_internal(std::string_view line);
  bool apply_main_internal_result(ParsedMain v,
                                  std::string* interaction_id,
                                  bool baseline_profile_variant);
  // Read a line of data from the metadata section (at the top of the file)
  bool parse_metadata(std::string_view line);

  // Parse the first line and make sure it matches our expectations
  bool parse_header(std::string_view line);

  void process_unresolved_lines(bool baseline_profile_variant);
  void resolve_method_descriptor_tokens(
      const UnorderedMap<dex_member_refs::MethodDescriptorTokens,
                         std::vector<DexMethodRef*>>& map,
      bool baseline_profile_variant);
};

// NOTE: Do not use this comparator directly in `std::sort` calls, as it is
// stateful. libstdc++ copies the comparator during sorting. Instead, use
// `std::ref` of a local instance.
class dexmethods_profiled_comparator {
  const MethodProfiles* m_method_profiles;
  const UnorderedSet<std::string>* m_allowlisted_substrings;
  UnorderedMap<DexMethod*, double> m_cache;
  double m_min_appear_percent;
  double m_second_min_appear_percent;
  std::vector<std::string> m_interactions;

  const DexMethod* m_coldstart_start_marker;
  const DexMethod* m_coldstart_end_marker;

  UnorderedMap<DexMethod*, size_t> m_initial_order;

  // The profiled method order is broken into sections, one section for each
  // interaction. Each section has a range of floating point numbers assigned to
  // it (RANGE_SIZE) and the sections are separated by RANGE_STRIDE (which must
  // be larger than RANGE_SIZE). Stride is larger than size so that there is no
  // overlap between regions.
  //
  // Lower sort_num values correspond to occurring earlier in the dex file
  static constexpr double RANGE_SIZE = 1.0;
  static constexpr double RANGE_STRIDE = 2.0;
  static constexpr double COLD_START_RANGE_BEGIN = 0.0;

  double get_method_sort_num_override(const DexMethod* method);
  double get_method_sort_num(const DexMethod* method);

 public:
  static constexpr double VERY_END = std::numeric_limits<double>::max();
  double get_overall_method_sort_num(const DexMethod* method);

  dexmethods_profiled_comparator(
      const std::vector<DexMethod*>& initial_order,
      const method_profiles::MethodProfiles* method_profiles,
      const MethodProfileOrderingConfig* config);

  // See class comment.
  dexmethods_profiled_comparator(const dexmethods_profiled_comparator&) =
      delete;
  dexmethods_profiled_comparator& operator=(
      const dexmethods_profiled_comparator&) = delete;

  bool operator()(DexMethod* a, DexMethod* b);
};

} // namespace method_profiles
