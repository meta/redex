/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "MethodProfiles.h"

#include <algorithm>
#include <vector>

#include "Debug.h"
#include "RedexContext.h"

#include <boost/algorithm/string/classification.hpp>
#include <boost/algorithm/string/join.hpp>
#include <boost/algorithm/string/regex.hpp>
#include <boost/algorithm/string/split.hpp>
#include <charconv>
#include <fstream>
#include <iostream>
#include <stdlib.h>

#include "CppUtil.h"
#include "GlobalConfig.h"
#include "Show.h"
#include "WorkQueue.h"

using namespace method_profiles;

extern int errno;

namespace {

template <class Func>
bool parse_cells(std::string_view line, const Func& parse_cell) {
  uint32_t i = 0;
  // Assuming there are no quoted strings containing commas!
  for (auto cell : split_string(line, ",")) {
    if (cell.back() == '\n') {
      cell.remove_suffix(1);
    }
    bool success = parse_cell(cell, i);
    if (!success) {
      return false;
    }
    ++i;
  }
  return true;
}

bool empty_column(std::string_view sv) { return sv.empty() || sv == "\n"; }

} // namespace

AccumulatingTimer& MethodProfiles::get_process_unresolved_lines_timer() {
  static AccumulatingTimer s_process_unresolved_lines_timer(
      "MethodProfiles::process_unresolved_lines");
  return s_process_unresolved_lines_timer;
}

std::tuple<const StatsMap&, bool> method_stats_for_interaction_id(
    const std::string& interaction_id, const AllInteractions& interactions) {
  const auto& search1 = interactions.find(interaction_id);
  if (search1 != interactions.end()) {
    return {search1->second, true};
  }
  if (interaction_id == COLD_START) {
    // Originally, the stats file had no interaction_id column and it only
    // covered coldstart. Search for the default (empty string) for backwards
    // compatibility when we're searching for coldstart but it's not found.
    const auto& search2 = interactions.find("");
    if (search2 != interactions.end()) {
      return {search2->second, true};
    }
  }

  static StatsMap empty_map = {};
  return {empty_map, false};
}

const StatsMap& MethodProfiles::method_stats_for_baseline_config(
    const std::string& interaction_id,
    const std::string& baseline_config_name) const {
  // Try to find the interaction id first in the manual profile map
  if (baseline_config_name !=
      baseline_profiles::DEFAULT_BASELINE_PROFILE_CONFIG_NAME) {
    if (m_baseline_manual_interactions.count(baseline_config_name) != 0u) {
      const auto& method_stats =
          *(m_baseline_manual_interactions.at(baseline_config_name));
      const auto& [stats, found] =
          method_stats_for_interaction_id(interaction_id, method_stats);
      if (found) {
        return stats;
      }
    }
  }
  // If we can't find it there, try to find it in the default method stats
  const auto& [stats, found] =
      method_stats_for_interaction_id(interaction_id, m_method_stats);
  if (found) {
    return stats;
  }
  // If we can't find it there, try to find it in the baseline profile variant
  // stats
  const auto& [variant_stats, _] = method_stats_for_interaction_id(
      interaction_id, m_baseline_profile_method_stats);
  return variant_stats;
}

const StatsMap& MethodProfiles::method_stats(
    const std::string& interaction_id) const {
  const auto& search1 = m_method_stats.find(interaction_id);
  if (search1 != m_method_stats.end()) {
    return search1->second;
  }
  if (interaction_id == COLD_START) {
    // Originally, the stats file had no interaction_id column and it only
    // covered coldstart. Search for the default (empty string) for backwards
    // compatibility when we're searching for coldstart but it's not found.
    const auto& search2 = m_method_stats.find("");
    if (search2 != m_method_stats.end()) {
      return search2->second;
    }
  }

  static StatsMap empty_map = {};
  return empty_map;
}

// Escape any special character in regex
inline std::string regex_escape(const std::string& text) {
  const boost::regex esc("[.^$|()\\[\\]{}*+?\\\\]");
  const std::string rep("\\\\&");
  return regex_replace(text, esc, rep,
                       boost::match_default | boost::format_sed);
}

// Converts a wildcard string (*, **, and ?) to a regular expression
std::string wildcard_to_regex(const std::string& wildcard_string) {
  const std::string star_star_regex = "[-\\w\\$<>/;\[\\]]*";
  const std::string star_regex = "[-\\w\\$<>\\[\\]]*";
  const std::string question_regex = "[\\w<>\\[\\]]";

  // A list of strings divided first by "**", then by "*", then by "?"
  // For example, "this*is?a*very**long*sentence?that**will**be*tokens"
  // would become [[[this], [is, a], [very]], [[long], [sentence, that]],
  // [[[will]]], [[be], [tokens]]]
  std::vector<std::vector<std::vector<std::string>>> tokenized_list;
  std::vector<std::string> stars_list;
  boost::split_regex(stars_list, wildcard_string, boost::regex("\\*\\*"));
  for (const std::string& stars_str : stars_list) {
    std::vector<std::string> star_list;
    boost::split(star_list, stars_str, boost::is_any_of("*"));
    std::vector<std::vector<std::string>> star_and_question_list;
    for (const std::string& star_str : star_list) {
      std::vector<std::string> question_list;
      boost::split(question_list, star_str, boost::is_any_of("?"));
      star_and_question_list.emplace_back(question_list);
    }
    tokenized_list.emplace_back(star_and_question_list);
  }

  // Reduce list back into a string, substituting in the redex values
  // and escaping non-tokens
  std::vector<std::string> escaped_with_questions_and_stars;
  for (const auto& star_and_question_list : tokenized_list) {
    std::vector<std::string> escaped_with_questions;
    for (const auto& question_list : star_and_question_list) {
      std::vector<std::string> escaped_list;
      escaped_list.reserve(question_list.size());
      for (const auto& str : question_list) {
        escaped_list.emplace_back(regex_escape(str));
      }
      escaped_with_questions.emplace_back(
          boost::join(escaped_list, question_regex));
    }
    escaped_with_questions_and_stars.emplace_back(
        boost::join(escaped_with_questions, star_regex));
  }

  // The above algorithm doesn't take into account whether the string begins or
  // ends with a special character, so we check that now
  std::string prefix;
  if (wildcard_string.find("**") == 0) {
    prefix = star_star_regex;
  } else if (wildcard_string.find('*') == 0) {
    prefix = star_regex;
  } else if (wildcard_string.find('?') == 0) {
    prefix = question_regex;
  }
  std::string suffix;
  if (wildcard_string.rfind("**") == wildcard_string.size() - 2) {
    suffix = star_star_regex;
  } else if (wildcard_string.rfind('*') == wildcard_string.size() - 1) {
    suffix = star_regex;
  } else if (wildcard_string.rfind('?') == wildcard_string.size() - 1) {
    suffix = question_regex;
  }

  return prefix +
         boost::join(escaped_with_questions_and_stars, star_star_regex) +
         suffix;
}

namespace {
namespace manual_profile {

void apply_manual_profile(
    DexMethodRef* ref,
    const std::string& flags,
    const std::string& manual_filename,
    const std::vector<std::string>& config_names,
    std::map<std::string, AllInteractions>& manual_profile_interactions,
    AllInteractions& method_stats) {
  // These are just randomly selected stats that seemed reasonable
  const struct Stats stats = {100.0, 100, 50, 0};
  always_assert_log(!config_names.empty(),
                    "Manual profiles must come from a baseline config.");
  if (config_names.size() > 1 ||
      config_names.front() !=
          baseline_profiles::DEFAULT_BASELINE_PROFILE_CONFIG_NAME) {
    static std::mutex manual_all_interactions_mutex = {};
    std::lock_guard<std::mutex> manual_all_interactions_lock{
        manual_all_interactions_mutex};

    auto& manual_all_interactions =
        manual_profile_interactions[manual_filename];
    manual_all_interactions["manual"].emplace(ref, stats);
    if (flags.find('H') != std::string::npos) {
      manual_all_interactions["manual_hot"].emplace(ref, stats);
    }
    if (flags.find('S') != std::string::npos) {
      manual_all_interactions["manual_startup"].emplace(ref, stats);
    }
    if (flags.find('P') != std::string::npos) {
      manual_all_interactions["manual_post_startup"].emplace(ref, stats);
    }
  }
  // We store the default config manual profile in method_stats so it can be
  // used by other passes
  if (std::find(config_names.begin(), config_names.end(),
                baseline_profiles::DEFAULT_BASELINE_PROFILE_CONFIG_NAME) !=
      config_names.end()) {
    static std::mutex method_stats_mutex = {};
    std::lock_guard<std::mutex> method_stats_lock{method_stats_mutex};

    method_stats["manual"].emplace(ref, stats);
    if (flags.find('H') != std::string::npos) {
      method_stats["manual_hot"].emplace(ref, stats);
    }
    if (flags.find('S') != std::string::npos) {
      method_stats["manual_startup"].emplace(ref, stats);
    }
    if (flags.find('P') != std::string::npos) {
      method_stats["manual_post_startup"].emplace(ref, stats);
    }
  }
}

bool parse_manual_file_line_complex(
    const MethodProfiles::ManualProfileLine& manual_profile_line,
    const UnorderedMap<std::string, UnorderedMap<std::string, DexMethodRef*>>&
        baseline_profile_method_map,
    std::map<std::string, AllInteractions>& manual_profile_interactions,
    AllInteractions& method_stats) {
  const auto& config_names = manual_profile_line.config_names;
  const auto& manual_filename = manual_profile_line.manual_filename;
  const auto& method_and_class = manual_profile_line.method_and_class;
  const auto& flags = manual_profile_line.flags;

  const auto& klass = method_and_class[0];
  const auto& method = method_and_class[1];

  // Regexes can be slow. See if parts are simple.

  auto apply_class =
      [&](const UnorderedMap<std::string, DexMethodRef*>& method_name_to_method,
          const auto& method_filter_fn) {
        for (const auto& [method_name, method_ref] :
             UnorderedIterable(method_name_to_method)) {
          if (!method_filter_fn(method_name)) {
            continue;
          }
          apply_manual_profile(method_ref, flags, manual_filename, config_names,
                               manual_profile_interactions, method_stats);
        }
      };
  auto apply = [&](const auto& class_filter_fn, const auto& method_filter_fn) {
    for (const auto& [classname, method_name_to_method] :
         UnorderedIterable(baseline_profile_method_map)) {
      if (!class_filter_fn(classname)) {
        continue;
      }
      apply_class(method_name_to_method, method_filter_fn);
    }
  };

  // A value that ends with '**' and contains no other '*' or '?' is a prefix
  // match.
  auto maybe_prefix = [](const auto& str) -> std::optional<std::string_view> {
    if (str.size() > 2 && str.back() == '*' &&
        str.find('*') == str.size() - 2 && str.find('?') == std::string::npos) {
      return std::string_view(str.data(), str.size() - 2);
    }
    return std::nullopt;
  };

  bool exact_klass = klass.find('*') == std::string::npos &&
                     klass.find('?') == std::string::npos;
  std::optional<std::string_view> klass_prefix_opt =
      exact_klass ? std::nullopt : maybe_prefix(klass);
  bool all_methods = method == "**(**)**";

  struct RegexMatch {
    const boost::regex regex;
    explicit RegexMatch(const std::string& filter_str)
        : regex(wildcard_to_regex(filter_str)) {}
    bool operator()(const std::string& name) const {
      boost::smatch matches;
      return boost::regex_search(name, matches, regex);
    }
  };

  // Fastest.
  if (exact_klass) {
    auto it = baseline_profile_method_map.find(klass);
    if (it != baseline_profile_method_map.end()) {
      if (all_methods) {
        apply_class(it->second, [](const auto&) { return true; });
      } else {
        apply_class(it->second, RegexMatch{method});
      }
    }
  } else if (klass_prefix_opt) {
    auto& klass_prefix = *klass_prefix_opt;
    auto klass_prefix_fn = [&klass_prefix](const auto& classname) {
      return classname.starts_with(klass_prefix);
    };
    if (all_methods) {
      apply(klass_prefix_fn, [](const auto&) { return true; });
    } else {
      apply(klass_prefix_fn, RegexMatch{method});
    }
  } else {
    RegexMatch class_regex{klass};
    if (all_methods) {
      apply(class_regex, [](const auto&) { return true; });
    } else {
      apply(class_regex, RegexMatch{method});
    }
  }

  // We need to add wildcard lines regardless
  return true;
}

// Returns true if the line was unresolved
bool parse_manual_file_line(
    const MethodProfiles::ManualProfileLine& manual_profile_line,
    const UnorderedMap<std::string, UnorderedMap<std::string, DexMethodRef*>>&
        baseline_profile_method_map,
    std::map<std::string, AllInteractions>& manual_profile_interactions,
    AllInteractions& method_stats) {
  const auto& current_line = manual_profile_line.current_line;
  const auto& config_names = manual_profile_line.config_names;
  const auto& manual_filename = manual_profile_line.manual_filename;
  const auto& method_and_class = manual_profile_line.method_and_class;
  const auto& flags = manual_profile_line.flags;
  // This is not a method, so do nothing
  if (method_and_class.size() != 2) {
    return false;
  }
  // If the line does not contains wildcard characters, do a map look up
  if (current_line.find('*') == std::string::npos &&
      current_line.find('?') == std::string::npos) {
    auto class_it = baseline_profile_method_map.find(method_and_class[0]);
    if (class_it != baseline_profile_method_map.end()) {
      auto method_it = class_it->second.find(method_and_class[1]);
      if (method_it != class_it->second.end()) {
        apply_manual_profile(method_it->second, flags, manual_filename,
                             config_names, manual_profile_interactions,
                             method_stats);
        return false;
      }
    }
    return true;
  }
  return parse_manual_file_line_complex(manual_profile_line,
                                        baseline_profile_method_map,
                                        manual_profile_interactions,
                                        method_stats);
}

void parse_manual_file(
    const std::string& manual_filename,
    const std::vector<std::string>& config_names,
    const UnorderedMap<std::string, UnorderedMap<std::string, DexMethodRef*>>&
        baseline_profile_method_map,
    std::map<std::string, AllInteractions*>& baseline_manual_interactions,
    std::map<std::string, AllInteractions>& manual_profile_interactions,
    AllInteractions& method_stats,
    std::vector<MethodProfiles::ManualProfileLine>& unresolved_manual_lines) {
  Timer t("Parsing Manual File " + manual_filename);
  std::ifstream manual_file(manual_filename);
  always_assert_log(manual_file.good(),
                    "Could not open manual profile at %s",
                    manual_filename.c_str());
  std::string current_line;
  manual_profile_interactions[manual_filename] = AllInteractions();
  for (const auto& config_name : config_names) {
    baseline_manual_interactions[config_name] =
        &(manual_profile_interactions.at(manual_filename));
  }
  // Wildcard rules are kinda expensive, so we want to parallelize them. To
  // simplify first capture all data from the file, then process. It is
  // assumed that manual profiles are not humongous and can fit into memory.
  std::vector<MethodProfiles::ManualProfileLine> manual_profile_lines;
  manual_profile_lines.reserve(10000);

  while (std::getline(manual_file, current_line)) {
    if (current_line.empty() || current_line[0] == '#' ||
        current_line[0] == '[') {
      continue;
    }
    auto hash_pos = current_line.find('#');
    if (hash_pos != std::string::npos) {
      current_line = current_line.substr(0, hash_pos);
    }
    // Extract flags
    boost::smatch flag_matches;
    boost::regex flag_expression("^([HSP]{0,3})(L.+)");
    always_assert_log(
        boost::regex_search(current_line, flag_matches, flag_expression,
                            boost::match_default),
        "Line %s did not match the regular expression \"^([HSP]*)L.+\"",
        current_line.c_str());
    auto flags = flag_matches[1].str();
    auto method_and_class_string = flag_matches[2].str();
    std::vector<std::string> method_and_class;
    boost::split_regex(method_and_class, method_and_class_string,
                       boost::regex("->"));
    always_assert(method_and_class.size() == 1 || method_and_class.size() == 2);
    manual_profile_lines.push_back(
        {current_line, flags, method_and_class, config_names, manual_filename});
  }

  std::mutex unresolved_mutex;
  workqueue_run_for<size_t>(0, manual_profile_lines.size(), [&](size_t index) {
    auto& manual_profile_line = manual_profile_lines.at(index);
    if (parse_manual_file_line(manual_profile_line, baseline_profile_method_map,
                               manual_profile_interactions, method_stats)) {
      std::lock_guard<std::mutex> unresolved_lock{unresolved_mutex};
      unresolved_manual_lines.emplace_back(std::move(manual_profile_line));
    }
  });
}

void parse_manual_files(
    const UnorderedMap<std::string, std::vector<std::string>>&
        manual_file_to_config_names,
    const UnorderedMap<std::string, UnorderedMap<std::string, DexMethodRef*>>&
        baseline_profile_method_map,
    std::map<std::string, AllInteractions*>& baseline_manual_interactions,
    std::map<std::string, AllInteractions>& manual_profile_interactions,
    AllInteractions& method_stats,
    std::vector<MethodProfiles::ManualProfileLine>& unresolved_manual_lines) {
  Timer t("parse_manual_files");
  // Two of the writes below are order-sensitive, so the files have to be
  // visited in a fixed order rather than in the map's iteration order:
  // parse_manual_file assigns baseline_manual_interactions[config] with
  // last-write-wins, and a config may be listed in more than one file; and the
  // rows it contributes to the shared method_stats are emplaced first-wins, so
  // when two files name the same method and interaction, whichever file is
  // parsed first decides the stats that survive.
  auto ordered_files = unordered_to_ordered_keys(manual_file_to_config_names);
  for (const auto& manual_file : ordered_files) {
    auto it = manual_file_to_config_names.find(manual_file);
    always_assert(it != manual_file_to_config_names.end());
    parse_manual_file(manual_file, it->second, baseline_profile_method_map,
                      baseline_manual_interactions, manual_profile_interactions,
                      method_stats, unresolved_manual_lines);
  }
  constexpr int DUMP_LEVEL = 1;
  if (traceEnabled(METH_PROF, DUMP_LEVEL)) {
    auto print_manual = [](const auto& map, const char* prefix) {
      auto num = [&map](const char* key) -> ssize_t {
        auto it = map.find(key);
        return it != map.end() ? it->second.size() : -1;
      };
      TRACE(METH_PROF, DUMP_LEVEL, "%s %zd/%zd/%zd/%zd", prefix, num("manual"),
            num("manual_hot"), num("manual_startup"),
            num("manual_post_startup"));
    };
    for (auto& [file, interactions] : manual_profile_interactions) {
      print_manual(interactions, file.c_str());
    }
    print_manual(method_stats, "MethodStats: ");
  }
}

} // namespace manual_profile
} // namespace

const UnorderedMap<std::string, UnorderedMap<std::string, DexMethodRef*>>&
MethodProfiles::get_baseline_profile_method_map(bool recompute) {
  if ((m_baseline_profile_method_map.empty() &&
       m_parsed_manual_methods.empty()) ||
      recompute) {
    Timer t("Recomputing baseline profile method map");
    m_baseline_profile_method_map =
        g_redex->get_baseline_profile_method_map(m_parsed_manual_methods);
  }
  return m_baseline_profile_method_map;
}

bool MethodProfiles::parse_stats_file(const std::string& csv_filename,
                                      bool baseline_profile_variant) {
  TRACE(METH_PROF, 3, "input csv filename: %s", csv_filename.c_str());
  if (csv_filename.empty()) {
    TRACE(METH_PROF, 2, "No csv file given");
    return false;
  }

  // Using C-style file reading and parsing because it's faster than the
  // iostreams equivalent and we expect to read very large csv files.
  std::ifstream ifs(csv_filename);
  if (!ifs.good()) {
    std::cerr << "FAILED to open " << csv_filename << '\n';
    return false;
  }

  // getline will allocate a buffer and put a pointer to it here
  std::string line;
  while (std::getline(ifs, line)) {
    bool success = false;
    if (line.back() == '\n') {
      line.pop_back();
    }
    // Just in case the files were generated on a Windows OS
    // or with Windows line ending.
    if (line.back() == '\r') {
      line.pop_back();
    }
    if (m_mode == NONE) {
      success = parse_header(line);
    } else {
      success = parse_line(line, baseline_profile_variant);
    }
    if (!success) {
      return false;
    }
  }
  if (ifs.bad()) {
    std::cerr << "FAILED to read a line!" << '\n';
    return false;
  }

  TRACE(METH_PROF, 1,
        "MethodProfiles successfully parsed %zu rows; %zu unresolved lines",
        size(), unresolved_size());
  return true;
}

template <typename IntType = int64_t>
IntType parse_int(std::string_view tok) {
  IntType result{};
  auto [ptr, ec]{std::from_chars(tok.data(), tok.data() + tok.size(), result)};
  std::string_view rest(ptr, tok.size() - (ptr - tok.data()));

  always_assert_log(ec == std::errc(), "can't parse %s into an int: %s",
                    SHOW(tok), std::make_error_condition(ec).message().c_str());
  always_assert_log(empty_column(rest), "can't parse %s into an int",
                    SHOW(tok));
  return result;
}

// `strtol` and `strtod` requires c string to be null terminated,
// std::string_view::data() doesn't have this guarantee. Our `string_view`s are
// taken from `std::string`s. This should be safe.
// Combine with parse_int above after we drop some older compiler support.
double parse_double(std::string_view tok) {
  char* ptr = nullptr;
  // NOLINTNEXTLINE(bugprone-suspicious-stringview-data-usage)
  const auto result = strtod(tok.data(), &ptr);
  always_assert_log(
      ptr <= (tok.data() + tok.size()),
      "strtod went over std::string_view boundary for string_view %s",
      SHOW(tok));

  std::string_view rest(ptr, tok.size() - (ptr - tok.data()));
  always_assert_log(ptr != tok.data(), "can't parse %s into a double",
                    SHOW(tok));
  always_assert_log(empty_column(rest), "can't parse %s into a double",
                    SHOW(tok));
  return result;
}

bool MethodProfiles::parse_metadata(std::string_view line) {
  always_assert(m_mode == METADATA);
  uint32_t interaction_count{0};
  auto parse_cell = [&](std::string_view cell, uint32_t col) -> bool {
    switch (col) {
    case 0:
      m_interaction_id = std::string(cell);
      return true;
    case 1: {
      auto parsed = parse_int(cell);
      always_assert(parsed <= std::numeric_limits<uint32_t>::max());
      always_assert(parsed >= 0);
      interaction_count = static_cast<uint32_t>(parsed);
      return true;
    }
    default: {
      bool ok = empty_column(cell);
      if (!ok) {
        std::cerr << "Unexpected extra value in metadata: " << cell << '\n';
      }
      return ok;
    }
    }
  };
  bool success = parse_cells(line, parse_cell);
  if (!success) {
    return false;
  }
  m_interaction_counts.emplace(m_interaction_id, interaction_count);
  // There should only be one line of metadata per file. Once we've processed
  // it, change the parsing mode back to NONE.
  m_mode = NONE;
  return true;
}

std::optional<MethodProfiles::ParsedMain> MethodProfiles::parse_main_internal(
    std::string_view line) {
  always_assert(m_mode == MAIN);
  ParsedMain result;
  auto parse_cell = [&](std::string_view cell, uint32_t col) -> bool {
    switch (col) {
    case INDEX:
      // Don't need this raw data. It's an arbitrary index (the line number in
      // the file)
      return true;
    case NAME:
      // We move the string to a unique_ptr, so that its location is pinned, and
      // the string_views of the mdt are defined.
      result.ref_str = std::make_unique<std::string>(cell);
      result.mdt =
          dex_member_refs::parse_method</*kCheckFormat=*/true>(*result.ref_str);
      result.ref = DexMethod::get_method(*result.mdt);
      if (result.ref == nullptr) {
        TRACE(METH_PROF, 6, "failed to resolve %s", SHOW(cell));
      }
      return true;
    case APPEAR100:
      result.stats.appear_percent = parse_double(cell);
      return true;
    case APPEAR_NUMBER:
      // Don't need this raw data. appear_percent is the same thing but
      // normalized
      return true;
    case AVG_CALL:
      result.stats.call_count = parse_double(cell);
      return true;
    case AVG_ORDER:
      // Don't need this raw data. order_percent is the same thing but
      // normalized
      return true;
    case AVG_RANK100:
      result.stats.order_percent = parse_double(cell);
      return true;
    case MIN_API_LEVEL: {
      result.stats.min_api_level = parse_int<int16_t>(cell);
      return true;
    }
    default:
      const auto& search = m_optional_columns.find(col);
      if (search != m_optional_columns.end()) {
        if (search->second == "interaction") {
          result.line_interaction_id = std::make_unique<std::string>(cell);
          return true;
        }
      }
      std::cerr << "FAILED to parse line. Unknown extra column\n";
      return false;
    }
  };

  bool success = parse_cells(line, parse_cell);
  if (!success) {
    return std::nullopt;
  }
  return std::move(result);
}

bool MethodProfiles::apply_main_internal_result(ParsedMain v,
                                                std::string* interaction_id,
                                                bool baseline_profile_variant) {
  if (v.ref != nullptr) {
    if (v.line_interaction_id) {
      // Interaction IDs from the current row have priority over the interaction
      // id from the top of the file. This shouldn't happen in practice, but
      // this is the conservative approach.
      interaction_id = v.line_interaction_id.get();
    }
    always_assert(interaction_id);
    TRACE(METH_PROF, 6, "(%s, %s) -> {%f, %f, %f, %d}", SHOW(v.ref),
          interaction_id->c_str(), v.stats.appear_percent, v.stats.call_count,
          v.stats.order_percent, v.stats.min_api_level);
    if (baseline_profile_variant) {
      m_baseline_profile_method_stats[*interaction_id].emplace(v.ref, v.stats);
    } else {
      m_method_stats[*interaction_id].emplace(v.ref, v.stats);
    }
    return true;
  } else if (v.ref_str == nullptr) {
    std::cerr << "FAILED to parse line. Missing name column\n";
    return false;
  } else {
    always_assert(interaction_id);
    if (!v.line_interaction_id) {
      v.line_interaction_id = std::make_unique<std::string>(*interaction_id);
    }
    if (baseline_profile_variant) {
      m_baseline_profile_unresolved_lines.emplace_back(std::move(v));
    } else {
      m_unresolved_lines.emplace_back(std::move(v));
    }
    return false;
  }
}

void MethodProfiles::set_method_stats(const std::string& interaction_id,
                                      const DexMethodRef* m,
                                      Stats stats) {
  m_method_stats.at(interaction_id)[m] = stats;
}

size_t MethodProfiles::derive_stats(DexMethod* target,
                                    const std::vector<DexMethod*>& sources) {
  auto ordered_sources = sources;
  std::sort(ordered_sources.begin(), ordered_sources.end(), compare_dexmethods);
  size_t res = 0;
  for (auto& [interaction_id, method_stats] : m_method_stats) {
    if (method_stats.count(target) != 0u) {
      // No need to derive anything, we have a match.
      continue;
    }

    std::optional<Stats> stats;
    for (auto* src : ordered_sources) {
      auto it = method_stats.find(src);
      if (it == method_stats.end()) {
        continue;
      }
      if (!stats) {
        stats = it->second;
        continue;
      }
      stats->appear_percent =
          std::max(stats->appear_percent, it->second.appear_percent);
      stats->call_count += it->second.call_count;
      stats->order_percent =
          std::min(stats->order_percent, it->second.order_percent);
      stats->min_api_level =
          std::min(stats->min_api_level, it->second.min_api_level);
    }

    if (stats) {
      method_stats.emplace(target, *stats);
      res++;
    }
  }
  return res;
}

size_t MethodProfiles::substitute_stats(
    DexMethod* target, const std::vector<DexMethod*>& sources) {
  auto ordered_sources = sources;
  std::sort(ordered_sources.begin(), ordered_sources.end(), compare_dexmethods);
  size_t res = 0;
  for (auto& [interaction_id, method_stats] : m_method_stats) {
    std::optional<Stats> stats;
    for (auto* src : ordered_sources) {
      auto it = method_stats.find(src);
      if (it == method_stats.end()) {
        continue;
      }
      if (!stats) {
        stats = it->second;
        continue;
      }
      stats->appear_percent += it->second.appear_percent;
      stats->call_count += it->second.call_count;
      stats->order_percent =
          std::min(stats->order_percent, it->second.order_percent);
      stats->min_api_level =
          std::min(stats->min_api_level, it->second.min_api_level);
    }

    if (stats) {
      auto [target_it, emplaced] = method_stats.emplace(target, *stats);
      if (!emplaced) {
        auto& target_stats = target_it->second;
        if (target_stats == *stats) {
          // Target method has stats and is same as the stats to be substituted.
          // Do not change.
          continue;
        }
        target_stats = *stats;
      }
      res++;
    } else {
      auto target_it = method_stats.find(target);
      if (target_it != method_stats.end()) {
        method_stats.erase(target_it);
        res++;
      }
    }
  }
  return res;
}

bool MethodProfiles::parse_main(const std::string& line,
                                std::string* interaction_id,
                                bool baseline_profile_variant) {
  auto result = parse_main_internal(line);
  if (!result) {
    return false;
  }
  (void)apply_main_internal_result(std::move(result.value()), interaction_id,
                                   baseline_profile_variant);
  return true;
}

bool MethodProfiles::parse_line(const std::string& line,
                                bool baseline_profile_variant) {
  if (m_mode == MAIN) {
    return parse_main(line, &m_interaction_id, baseline_profile_variant);
  } else if (m_mode == METADATA) {
    return parse_metadata(line);
  } else {
    always_assert_log(false, "invalid parsing mode");
  }
}

std::optional<uint32_t> MethodProfiles::get_interaction_count(
    const std::string& interaction_id) const {
  const auto& search = m_interaction_counts.find(interaction_id);
  if (search == m_interaction_counts.end()) {
    return std::nullopt;
  } else {
    return search->second;
  }
}

size_t MethodProfiles::drop_unresolved_split_lines() {
  auto is_split = [](const ParsedMain& line) {
    always_assert(line.mdt);
    return line.mdt->name.find("$split$") != std::string_view::npos;
  };
  return std::erase_if(m_unresolved_lines, is_split) +
         std::erase_if(m_baseline_profile_unresolved_lines, is_split);
}

void MethodProfiles::process_unresolved_lines() {
  Timer::scope("Processing unresolved profile lines", [&] {
    process_unresolved_lines(false);
    process_unresolved_lines(true);
  });
  if (!m_unresolved_manual_lines.empty()) {
    Timer t("Processing unresolved manual lines");
    get_baseline_profile_method_map(true);
    for (auto it = m_unresolved_manual_lines.begin();
         it < m_unresolved_manual_lines.end();) {
      const auto& manual_profile_line = *it;
      if (manual_profile::parse_manual_file_line(
              manual_profile_line, get_baseline_profile_method_map(false),
              m_manual_profile_interactions, m_method_stats)) {
        ++it;
      } else {
        it = m_unresolved_manual_lines.erase(it);
      }
    }
  }
}

void MethodProfiles::process_unresolved_lines(bool baseline_profile_variant) {
  auto& unresolved_lines_ref = baseline_profile_variant
                                   ? m_baseline_profile_unresolved_lines
                                   : m_unresolved_lines;
  if (unresolved_lines_ref.empty()) {
    return;
  }

  auto timer_scope = get_process_unresolved_lines_timer().scope();

  std::set<ParsedMain*> resolved;
  std::mutex resolved_mutex;
  workqueue_run_for<size_t>(0, unresolved_lines_ref.size(), [&](size_t index) {
    auto& parsed_main = unresolved_lines_ref.at(index);
    always_assert(parsed_main.ref_str != nullptr);
    always_assert(parsed_main.mdt);
    parsed_main.ref = DexMethod::get_method(*parsed_main.mdt);
    if (parsed_main.ref == nullptr) {
      TRACE(METH_PROF, 6, "failed to resolve %s", SHOW(*parsed_main.ref_str));
    } else {
      std::lock_guard<std::mutex> lock_guard(resolved_mutex);
      resolved.emplace(&parsed_main);
    }
  });
  auto unresolved_lines = unresolved_lines_ref.size();
  // Note that resolved is ordered by the (addresses of the) unresolved lines,
  // to ensure determinism
  for (const auto& parsed_main_ptr : resolved) {
    auto* interaction_id_ptr = &*parsed_main_ptr->line_interaction_id;
    always_assert(parsed_main_ptr->ref != nullptr);
    bool success = apply_main_internal_result(std::move(*parsed_main_ptr),
                                              interaction_id_ptr,
                                              baseline_profile_variant);
    always_assert(success);
  }
  always_assert(unresolved_lines == unresolved_lines_ref.size());
  std::erase_if(unresolved_lines_ref, [&](auto& unresolved_line) {
    return resolved.count(&unresolved_line);
  });
  always_assert(unresolved_lines - resolved.size() ==
                unresolved_lines_ref.size());

  size_t total_rows = 0;
  for (const auto& pair : m_method_stats) {
    total_rows += pair.second.size();
  }
  TRACE(METH_PROF, 1,
        "After processing unresolved lines: MethodProfiles successfully parsed "
        "%zu rows; %zu unresolved lines",
        total_rows, unresolved_size());
}

UnorderedSet<dex_member_refs::MethodDescriptorTokens>
MethodProfiles::get_unresolved_method_descriptor_tokens() const {
  UnorderedSet<dex_member_refs::MethodDescriptorTokens> result;
  for (const auto& parsed_main : m_unresolved_lines) {
    always_assert(parsed_main.mdt);
    result.insert(*parsed_main.mdt);
  }
  for (const auto& parsed_main : m_baseline_profile_unresolved_lines) {
    always_assert(parsed_main.mdt);
    result.insert(*parsed_main.mdt);
  }
  return result;
}

MethodProfiles::ResolutionStats
MethodProfiles::resolve_method_descriptor_tokens(
    const UnorderedMap<dex_member_refs::MethodDescriptorTokens,
                       std::vector<DexMethodRef*>>& map) {
  // The keys of `map` are MethodDescriptorTokens, which are non-owning
  // string_views into the ref_str buffers of BOTH
  // m_baseline_profile_unresolved_lines and m_unresolved_lines (see
  // get_unresolved_method_descriptor_tokens, which merges the two). Erasing
  // from either vector destroys those buffers, so neither erasure may happen
  // until both variants have finished looking keys up. Otherwise the second
  // lookup hashes and compares keys that point into freed memory.
  auto baseline = resolve_method_descriptor_tokens(map, true);
  auto main = resolve_method_descriptor_tokens(map, false);
  erase_resolved_lines(m_baseline_profile_unresolved_lines, baseline.to_remove);
  erase_resolved_lines(m_unresolved_lines, main.to_remove);
  return ResolutionStats{
      /* lines_resolved */ main.to_remove.size(),
      /* rows_added */ main.added,
      /* baseline_lines_resolved */ baseline.to_remove.size(),
      /* baseline_rows_added */ baseline.added,
  };
}

void MethodProfiles::erase_resolved_lines(
    std::vector<ParsedMain>& unresolved_lines_ref,
    const UnorderedSet<std::string*>& to_remove) {
  std::erase_if(unresolved_lines_ref, [&to_remove](auto& parsed_main) {
    return to_remove.count(parsed_main.ref_str.get());
  });
}

MethodProfiles::VariantResolution
MethodProfiles::resolve_method_descriptor_tokens(
    const UnorderedMap<dex_member_refs::MethodDescriptorTokens,
                       std::vector<DexMethodRef*>>& map,
    bool baseline_profile_variant) {
  size_t removed{0};
  size_t added{0};
  // Note that we don't remove unresolved_lines_ref as we go, as the given map
  // might reference its mdts. The caller performs the removal, once both
  // variants are done, for the same reason.
  UnorderedSet<std::string*> to_remove;
  auto& unresolved_lines_ref = baseline_profile_variant
                                   ? m_baseline_profile_unresolved_lines
                                   : m_unresolved_lines;
  for (auto& parsed_main : unresolved_lines_ref) {
    always_assert(parsed_main.mdt);
    auto it = map.find(*parsed_main.mdt);
    if (it == map.end()) {
      continue;
    }
    to_remove.insert(parsed_main.ref_str.get());
    removed++;
    for (auto* method_ref : it->second) {
      ParsedMain resolved_parsed_main{
          std::make_unique<std::string>(*parsed_main.line_interaction_id),
          /* ref_str */ nullptr,
          /* mdt */ std::nullopt, method_ref, parsed_main.stats};
      auto* interaction_id_ptr = &*resolved_parsed_main.line_interaction_id;
      always_assert(resolved_parsed_main.ref != nullptr);
      bool success = apply_main_internal_result(std::move(resolved_parsed_main),
                                                interaction_id_ptr,
                                                baseline_profile_variant);
      always_assert(success);
      added++;
    }
  }
  TRACE(METH_PROF, 1,
        "After resolving unresolved lines: %zu unresolved lines removed, %zu "
        "rows added",
        removed, added);
  return VariantResolution{std::move(to_remove), added};
}

bool MethodProfiles::parse_header(std::string_view line) {
  always_assert(m_mode == NONE);
  auto check_cell = [](std::string_view expected, std::string_view cell,
                       uint32_t col) -> bool {
    if (expected != cell) {
      std::cerr << "Unexpected Header (column " << col << "): " << cell
                << " != " << expected << "\n";
      return false;
    }
    return true;
  };
  if (line.starts_with("interaction")) {
    m_mode = METADATA;
    // Extra metadata at the top of the file that we want to parse
    auto parse_cell = [&](std::string_view cell, uint32_t col) -> bool {
      switch (col) {
      case 0:
        return check_cell("interaction", cell, col);
      case 1:
        return check_cell("appear#", cell, col);
      default: {
        auto ok = empty_column(cell);
        if (!ok) {
          std::cerr << "Unexpected Metadata Column: " << cell << '\n';
        }
        return ok;
      }
      }
    };
    return parse_cells(line, parse_cell);
  } else {
    m_mode = MAIN;
    auto parse_cell = [&](std::string_view cell, uint32_t col) -> bool {
      switch (col) {
      case INDEX:
        return check_cell("index", cell, col);
      case NAME:
        return check_cell("name", cell, col);
      case APPEAR100:
        return check_cell("appear100", cell, col);
      case APPEAR_NUMBER:
        return check_cell("appear#", cell, col);
      case AVG_CALL:
        return check_cell("avg_call", cell, col);
      case AVG_ORDER:
        return check_cell("avg_order", cell, col);
      case AVG_RANK100:
        return check_cell("avg_rank100", cell, col);
      case MIN_API_LEVEL:
        return check_cell("min_api_level", cell, col);
      default:
        m_optional_columns.emplace(col, std::string(cell));
        return true;
      }
    };
    return parse_cells(line, parse_cell);
  }
}

dexmethods_profiled_comparator::dexmethods_profiled_comparator(
    const std::vector<DexMethod*>& initial_order,
    const method_profiles::MethodProfiles* method_profiles,
    const MethodProfileOrderingConfig* config)
    : m_method_profiles(method_profiles),
      m_allowlisted_substrings(&config->method_sorting_allowlisted_substrings),
      m_min_appear_percent(config->min_appear_percent),
      m_second_min_appear_percent(config->second_min_appear_percent) {
  always_assert(m_method_profiles != nullptr);
  always_assert(m_allowlisted_substrings != nullptr);

  m_cache.reserve(initial_order.size());

  auto* start_ref = DexMethod::get_method(
      "Lcom/facebook/common/methodpreloader/primarydeps/"
      "StartColdStartMethodPreloaderMethodMarker;"
      ".startColdStartMethods:()V");
  m_coldstart_start_marker =
      (start_ref != nullptr) ? start_ref->as_def() : nullptr;

  auto* end_ref = DexMethod::get_method(
      "Lcom/facebook/common/methodpreloader/primarydeps/"
      "EndColdStartMethodPreloaderMethodMarker;"
      ".endColdStartMethods:()V");
  m_coldstart_end_marker = (end_ref != nullptr) ? end_ref->as_def() : nullptr;

  for (const auto& pair : m_method_profiles->all_interactions()) {
    std::string interaction_id = pair.first;
    if (interaction_id.empty()) {
      // For backwards compatibility. Older versions of the aggregate profiles
      // only have cold start (and no interaction_id column)
      interaction_id = COLD_START;
    }
    m_interactions.push_back(interaction_id);
  }
  std::sort(m_interactions.begin(), m_interactions.end(),
            [this](const std::string& a, const std::string& b) {
              if (a == b) {
                return false;
              }

              // Cold Start always comes first;
              if (a == COLD_START) {
                return true;
              }
              if (b == COLD_START) {
                return false;
              }

              // Give priority to interactions that happen more often, ranking
              // any interaction with a known count above one without. Comparing
              // a counted against an uncounted interaction alphabetically
              // instead would not be a strict weak ordering: with counts Feed=5
              // and Story=10 and an uncounted Notifications, Story < Feed by
              // count, Notifications < Story alphabetically, and Feed <
              // Notifications alphabetically, which is a cycle. std::sort on an
              // intransitive comparator is undefined behaviour.
              //
              // std::optional orders nullopt below every value, which is
              // exactly that ranking. Do not spell it with a sentinel: in
              // `count ? *count : -1` the usual arithmetic conversions turn -1
              // into UINT32_MAX, which sorts uncounted first instead of last.
              auto a_count = m_method_profiles->get_interaction_count(a);
              auto b_count = m_method_profiles->get_interaction_count(b);

              // Ties -- equal counts, or two uncounted interactions -- fall
              // back to alphabetical, so the unstable sort has nothing left to
              // decide.
              return a_count == b_count ? a < b : a_count > b_count;
            });

  for (auto* method : initial_order) {
    m_initial_order.emplace(method, m_initial_order.size());
  }
}

double dexmethods_profiled_comparator::get_method_sort_num(
    const DexMethod* method) {
  double range_begin = 0.0;

  std::optional<double> secondary_ordering = std::nullopt;

  for (const auto& interaction_id : m_interactions) {
    if (interaction_id == COLD_START && m_coldstart_start_marker != nullptr &&
        m_coldstart_end_marker != nullptr) {
      if (method == m_coldstart_start_marker) {
        return range_begin;
      } else if (method == m_coldstart_end_marker) {
        return range_begin + RANGE_SIZE;
      }
    }
    const auto& stats_map = m_method_profiles->method_stats(interaction_id);
    auto it = stats_map.find(method);
    if (it != stats_map.end()) {
      const auto& stat = it->second;

      auto mixed_ordering = [](double appear_percent, double appear_bias,
                               double order_percent, double order_multiplier) {
        // Prefer high appearance percents and low order percents. This
        // intentionally doesn't strictly order methods by appear_percent then
        // order_percent, rather both values are used and with greater weight
        // given to appear_percent.
        double raw_score =
            (appear_bias - appear_percent) + order_multiplier * order_percent;
        return std::min(100.0, std::max(raw_score, 0.0));
      };

      if (stat.appear_percent >= m_min_appear_percent) {
        double score =
            mixed_ordering(stat.appear_percent, 100.0, stat.order_percent, 0.1);
        // Reminder: Lower sort numbers come sooner in the dex file
        return range_begin + score * RANGE_SIZE / 100.0;
      }

      if (stat.appear_percent >= m_second_min_appear_percent) {
        if (!secondary_ordering) {
          double score =
              mixed_ordering(stat.appear_percent, m_min_appear_percent,
                             stat.order_percent, 0.1);

          secondary_ordering =
              RANGE_STRIDE * static_cast<double>(m_interactions.size()) +
              range_begin + score * RANGE_SIZE / 100.0;
        }
        continue;
      }
    }
    range_begin += RANGE_STRIDE;
  }

  if (secondary_ordering) {
    return *secondary_ordering;
  }

  // If the method is not present in profiled order file we'll put it in the
  // end of the code section
  return VERY_END;
}

double dexmethods_profiled_comparator::get_method_sort_num_override(
    const DexMethod* method) {
  const auto deobfname = method->get_deobfuscated_name_or_empty();
  for (const std::string& substr :
       UnorderedIterable(*m_allowlisted_substrings)) {
    if (deobfname.find(substr) != std::string::npos) {
      return COLD_START_RANGE_BEGIN + RANGE_SIZE / 2;
    }
  }
  return VERY_END;
}

double dexmethods_profiled_comparator::get_overall_method_sort_num(
    const DexMethod* m) {
  double w = get_method_sort_num(m);
  if (w == VERY_END) {
    // For methods not included in the profiled methods file, move them to
    // the top section anyway if they match one of the allowed substrings.
    w = get_method_sort_num_override(m);
  }
  return w;
}

bool dexmethods_profiled_comparator::operator()(DexMethod* a, DexMethod* b) {
  if (a == nullptr) {
    return b != nullptr;
  } else if (b == nullptr) {
    return false;
  }

  auto get_sort_num = [this](DexMethod* m) -> double {
    const auto& search = m_cache.find(m);
    if (search != m_cache.end()) {
      return search->second;
    }

    double w = get_overall_method_sort_num(m);

    m_cache.emplace(m, w);
    return w;
  };

  double sort_num_a = get_sort_num(a);
  double sort_num_b = get_sort_num(b);

  if (sort_num_a != sort_num_b) {
    return sort_num_a < sort_num_b;
  }

  return m_initial_order.at(a) < m_initial_order.at(b);
}

void MethodProfiles::initialize(
    const std::vector<std::string>& csv_filenames,
    const std::vector<std::string>& baseline_profile_csv_filenames,
    const UnorderedMap<std::string, baseline_profiles::BaselineProfileConfig>&
        baseline_profile_configs) {
  m_initialized = true;
  Timer t("Parsing agg_method_stats_files");
  for (const std::string& csv_filename : csv_filenames) {
    m_interaction_id = "";
    m_mode = NONE;
    bool success = parse_stats_file(csv_filename, false);
    always_assert_log(success,
                      "Failed to parse %s. See stderr for more details",
                      csv_filename.c_str());
    always_assert_log(!m_method_stats.empty(),
                      "No valid data found in the profile %s. See stderr "
                      "for more details.",
                      csv_filename.c_str());
  }
  // Parse csv files that are only used in baseline profile variants
  for (const std::string& csv_filename : baseline_profile_csv_filenames) {
    m_interaction_id = "";
    m_mode = NONE;
    bool success = parse_stats_file(csv_filename, true);
    always_assert_log(success,
                      "Failed to parse %s. See stderr for more details",
                      csv_filename.c_str());
    always_assert_log(!m_method_stats.empty(),
                      "No valid data found in the profile %s. See stderr "
                      "for more details.",
                      csv_filename.c_str());
  }
  // Parse manual interactions
  UnorderedMap<std::string, std::vector<std::string>>
      manual_file_to_config_names;
  // Create a mapping of manual_file to config names
  // this way we can only parse each manual_file exactly once
  for (const auto& [baseline_config_name, baseline_profile_config] :
       UnorderedIterable(baseline_profile_configs)) {
    for (const auto& manual_file : baseline_profile_config.manual_files) {
      manual_file_to_config_names[manual_file].emplace_back(
          baseline_config_name);
    }
  }
  manual_profile::parse_manual_files(manual_file_to_config_names,
                                     get_baseline_profile_method_map(false),
                                     m_baseline_manual_interactions,
                                     m_manual_profile_interactions,
                                     m_method_stats,
                                     m_unresolved_manual_lines);
}
