/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <fstream>
#include <limits>
#include <type_traits>

#include "ConcurrentContainers.h"
#include "Debug.h"
#include "DexClass.h"
#include "DexPosition.h"
#include "DexUtil.h"
#include "RedexContext.h"
#include "Show.h"
#include "Trace.h"
#include "WorkQueue.h"

DexPosition::DexPosition(const DexString* file, uint32_t line)
    : file(file), line(line) {
  always_assert(file != nullptr);
}

DexPosition::DexPosition(const DexString* method,
                         const DexString* file,
                         uint32_t line)
    : method(method), file(file), line(line) {
  always_assert(file != nullptr);
}

void DexPosition::bind(const DexString* method_, const DexString* file_) {
  always_assert(file_ != nullptr);
  this->method = method_;
  this->file = file_;
}

void DexPosition::bind(const DexString* method_) { this->method = method_; }

bool DexPosition::operator==(const DexPosition& that) const {
  return method == that.method && file == that.file && line == that.line &&
         (parent == that.parent ||
          (parent != nullptr && that.parent != nullptr &&
           *parent == *that.parent));
}

std::unique_ptr<DexPosition> DexPosition::make_synthetic_entry_position(
    const DexMethod* method) {
  const auto* method_str = DexString::make_string(show_deobfuscated(method));

  // For source, see if the class has a source.
  const DexString* source = nullptr;
  auto* cls = type_class(method->get_class());
  if (cls != nullptr) {
    source = cls->get_source_file();
  }
  // Fall back to "UnknownSource".
  if (source == nullptr) {
    source = DexString::make_string("UnknownSource");
  }

  return std::make_unique<DexPosition>(method_str, source, 0);
}

PositionPatternSwitchManager::PositionPatternSwitchManager()
    : m_pattern_string(DexString::make_string("Lredex/$Position;.pattern:()V")),
      m_switch_string(DexString::make_string("Lredex/$Position;.switch:()V")),
      m_unknown_source_string(DexString::make_string("UnknownSource")) {}

DexPosition* PositionPatternSwitchManager::internalize(DexPosition* pos) {
  always_assert(pos);
  // An interned position is its own hash key, so it must never be mutated
  // afterwards -- and `process_pattern_switch_positions` does rewrite the line
  // of every switch position it emits. That is safe only because a pattern or
  // switch position never reaches here, which is what this checks. Enabling
  // CAN_OUTLINED_METHOD_INVOKE_OUTLINED_METHOD is what would break it.
  always_assert_log(!is_pattern_position(pos) && !is_switch_position(pos),
                    "interning a synthetic pattern/switch position; its line "
                    "is rewritten at output time, which would corrupt the key "
                    "it is stored under");
  m_internalize_calls.fetch_add(1, std::memory_order_relaxed);
  // Copy ctor, not the (method, file, line) ctor: that one always_asserts a
  // non-null file, and a parent in the chain may legitimately have none.
  DexPosition probe(*pos);
  probe.clear_provenance();
  if (pos->parent != nullptr) {
    // Bottom-up, so the probe's parent is already canonical when it is hashed.
    probe.parent = internalize(pos->parent);
  }
  // No `std::move`: DexPosition is trivially copyable -- a static_assert here
  // keeps it that way -- so moving is a copy and clang-tidy flags it.
  return m_positions.insert_unsafe(probe).first;
}

uint32_t PositionPatternSwitchManager::make_pattern(
    PositionPattern pos_pattern) {
  for (auto& pos : pos_pattern) {
    always_assert(pos->file);
    pos = internalize(pos);
  }
  auto it = m_patterns_map.find(pos_pattern);
  if (it == m_patterns_map.end()) {
    it = m_patterns_map.emplace(pos_pattern, m_patterns.size()).first;
    m_patterns.push_back(std::move(pos_pattern));
  }
  return it->second;
}

uint32_t PositionPatternSwitchManager::make_switch(PositionSwitch pos_switch) {
  for (auto& c : pos_switch) {
    always_assert(c.position);
    always_assert(c.position->file);
    c.position = internalize(c.position);
  }
  auto it = m_switches_map.find(pos_switch);
  if (it == m_switches_map.end()) {
    it = m_switches_map.emplace(pos_switch, m_switches.size()).first;
    m_switches.push_back(std::move(pos_switch));
  }
  return it->second;
}

std::unique_ptr<DexPosition>
PositionPatternSwitchManager::make_pattern_position(uint32_t pattern_id) const {
  always_assert(pattern_id < m_patterns.size());
  return std::make_unique<DexPosition>(m_pattern_string,
                                       m_unknown_source_string, pattern_id);
}

std::unique_ptr<DexPosition> PositionPatternSwitchManager::make_switch_position(
    uint32_t switch_id) const {
  always_assert(switch_id < m_switches.size());
  return std::make_unique<DexPosition>(m_switch_string, m_unknown_source_string,
                                       switch_id);
}

void RealPositionMapper::register_position(DexPosition* pos) {
  always_assert(pos->file);
  auto [_, emplaced] = m_pos_line_map.emplace(pos, -1);
  if (emplaced) {
    m_possibly_incomplete_positions.push(pos);
  }
}

int64_t RealPositionMapper::add_position(DexPosition* pos) {
  auto [it, _] = m_pos_line_map.emplace(pos, -1);
  if (it->second == -1) {
    it->second = static_cast<int64_t>(m_positions.size());
    m_positions.push_back(pos);
  }
  return it->second;
}

uint32_t RealPositionMapper::get_line(DexPosition* pos) {
  return static_cast<uint32_t>(m_pos_line_map.at(pos) + 1);
}

uint32_t RealPositionMapper::position_to_line(DexPosition* pos) {
  return static_cast<uint32_t>(add_position(pos) + 1);
}

void RealPositionMapper::write_map() {
  if (!m_filename_v2.empty()) {
    write_map_v2();
  }
}

void RealPositionMapper::process_pattern_switch_positions() {
  auto* manager = g_redex->get_position_pattern_switch_manager();
  if (manager->empty()) {
    return;
  }

  // First. we find all reachable patterns, switches and cases.
  auto switches = manager->get_switches();
  ConcurrentMap<uint32_t, std::vector<PositionCase>> reachable_patterns;
  InsertOnlyConcurrentSet<uint32_t> reachable_switches;
  InsertOnlyConcurrentSet<DexPosition*> visited;
  std::function<void(DexPosition*)> visit;
  visit = [&](DexPosition* pos) {
    always_assert(pos);
    for (; (pos != nullptr) && visited.insert(pos).second; pos = pos->parent) {
      if (manager->is_pattern_position(pos)) {
        std::vector<PositionCase> cases;
        reachable_patterns.update(pos->line,
                                  [&](auto, auto& pending, bool exists) {
                                    if (exists) {
                                      cases = std::move(pending);
                                    }
                                  });
        for (auto& c : cases) {
          visit(c.position);
        }
      } else if (manager->is_switch_position(pos)) {
        if (reachable_switches.insert(pos->line).second) {
          for (auto& c : switches.at(pos->line)) {
            bool pattern_reachable = false;
            reachable_patterns.update(c.pattern_id,
                                      [&](auto, auto& pending, bool exists) {
                                        if (exists && pending.empty()) {
                                          pattern_reachable = true;
                                          return;
                                        }
                                        pending.push_back(c);
                                      });
            if (pattern_reachable) {
              visit(c.position);
            }
          }
        }
      }
    }
  };

  workqueue_run<DexPosition*>(visit, m_positions);

  const auto* count_string =
      DexString::make_string("Lredex/$Position;.count:()V");
  const auto* case_string =
      DexString::make_string("Lredex/$Position;.case:()V");
  const auto* unknown_source_string = DexString::make_string("UnknownSource");

  // Second, we encode the switches and cases via extra positions.
  // For example, at some start line, we'll create 3 consecutive entries such
  // as the following, where 12345 and 54321 are pattern-ids.
  //
  // ...
  // 23: (some actual position)
  // ...
  // 42: (some actual position)
  // ...
  // 101: method Lredex/$Position;.count:()V, line 2 (no parent)
  // 102: method Lredex/$Position;.case:()V, line 12345, parent 23
  // 103: method Lredex/$Position;.case:()V, line 54321, parent 42
  UnorderedMap<uint32_t, uint32_t> switch_line_map;
  for (uint32_t switch_id = 0; switch_id < switches.size(); ++switch_id) {
    if (reachable_switches.count(switch_id) == 0u) {
      continue;
    }
    // We go over cases once to make sure all referenced positions are
    // registered and fully initialized. Note that only positions with a valid
    // file are considered.
    std::vector<PositionCase> reachable_cases;
    for (auto& c : switches.at(switch_id)) {
      if (reachable_patterns.count(c.pattern_id) == 0u) {
        continue;
      }
      for (auto* pos = c.position; (pos != nullptr) && (pos->file != nullptr);
           pos = pos->parent) {
        auto [it, emplaced] = m_pos_line_map.emplace(pos, m_positions.size());
        if (emplaced) {
          m_positions.push_back(pos);
        } else {
          always_assert(it->second != -1);
        }
      }
      reachable_cases.push_back(c);
    }
    // Sort cases by pattern-id, so that we can later do a binary search when
    // finding a matching pattern-id
    std::sort(reachable_cases.begin(), reachable_cases.end(),
              [](const PositionCase& a, const PositionCase& b) {
                return a.pattern_id < b.pattern_id;
              });
    // We emit a first entry holding the count
    switch_line_map.emplace(switch_id, m_positions.size());
    {
      auto* count_pos = new DexPosition(count_string, unknown_source_string,
                                        reachable_cases.size());
      m_owned_auxiliary_positions.emplace_back(count_pos);
      add_position(count_pos);
    }
    // Then we emit consecutive list of cases
    for (auto& c : reachable_cases) {
      auto* case_pos =
          new DexPosition(case_string, unknown_source_string, c.pattern_id);
      m_owned_auxiliary_positions.emplace_back(case_pos);
      always_assert(c.position);
      always_assert(c.position->file);
      case_pos->parent = c.position;
      add_position(case_pos);
    }
  }

  // Finally, we rewrite all switch positions to reference the emitted case
  // lists. For the above example, if the case-list for some switch_id was
  // emitted starting at line 101, then we'll update the referencing position to
  //
  // (some line): method Lredex/$Position;.switch:()V, line 101
  //
  // Note that the callsite remains unchanged, still referencing the pattern-id,
  // e.g.
  //
  // (some line): method Lredex/$Position;.pattern:()V, line 12345
  //
  // TODO: Should we undo this when we are done writing the map?
  for (auto* pos : m_positions) {
    if (manager->is_switch_position(pos)) {
      pos->line = switch_line_map.at(pos->line);
    }
  }
}

uint32_t RealPositionMapper::size() const { return m_positions.size(); }

void RealPositionMapper::write_map_v2() {
  // to ensure that the line numbers in the Dex are as compact as possible,
  // we put the emitted positions at the start of the list and rest at the end
  while (!m_possibly_incomplete_positions.empty()) {
    auto* pos = m_possibly_incomplete_positions.front();
    m_possibly_incomplete_positions.pop();
    auto& line = m_pos_line_map[pos];
    if (line == -1) {
      auto idx = m_positions.size();
      m_positions.emplace_back(pos);
      line = static_cast<int64_t>(idx);
    }
  }

  process_pattern_switch_positions();

  /*
   * Map file layout:
   * 0xfaceb000 (magic number)
   * version (4 bytes)
   * string_pool_size (4 bytes)
   * string_pool[string_pool_size]
   * positions_size (4 bytes)
   * positions[positions_size]
   * optionally, the provenance trailer -- see `namespace position_map`. Known
   * count-driven readers stop after the declared positions array and ignore the
   * optional suffix.
   *
   * Each member of the string pool is encoded as follows:
   * string_length (4 bytes)
   * char[string_length]
   */

  // We initially build a somewhat dense mapping of strings to ids; the exact
  // ids are not deterministic, and there might be some skipped ids due to
  // races.
  InsertOnlyConcurrentMap<std::string_view, uint32_t> semi_dense_string_ids;
  InsertOnlyConcurrentMap<uint32_t, std::unique_ptr<std::string>> string_pool;
  std::atomic<uint32_t> next_semi_dense_string_id{0};
  auto semi_dense_id_of_string = [&](std::string_view s) -> uint32_t {
    // Fast path
    const uint32_t* opt_id = semi_dense_string_ids.get(s);
    if (opt_id != nullptr) {
      return *opt_id;
    }

    // Slow path
    auto id = next_semi_dense_string_id.fetch_add(1);
    always_assert(id < std::numeric_limits<uint32_t>::max());
    auto p = std::make_unique<std::string>(s);
    auto [id_ptr, emplaced] = semi_dense_string_ids.emplace(*p, id);
    if (emplaced) {
      string_pool.emplace(id, std::move(p));
    } // else, we wasted a string-id. Oh well... We'll renumber densely later.
    return *id_ptr;
  };

  // Many DexPositions refer to the same method. We cache its class and method
  // string ids.
  struct MethodInfo {
    uint32_t class_id;
    uint32_t method_id;
    bool operator==(const MethodInfo& other) const {
      return class_id == other.class_id && method_id == other.method_id;
    }
  };
  InsertOnlyConcurrentMap<const DexString*, MethodInfo> method_infos;
  auto get_method_info = [&](const DexString* method) -> const MethodInfo& {
    return *method_infos
                .get_or_create_and_assert_equal(
                    method,
                    [&semi_dense_id_of_string](auto* m) {
                      // of the form
                      // "class_name.method_name:(arg_types)return_type"
                      const auto full_method_name = m->str();
                      // strip out the args and return type
                      const auto qualified_method_name =
                          full_method_name.substr(0,
                                                  full_method_name.find(':'));
                      auto class_name = java_names::internal_to_external(
                          qualified_method_name.substr(
                              0, qualified_method_name.rfind('.')));
                      auto method_name = qualified_method_name.substr(
                          qualified_method_name.rfind('.') + 1);
                      auto class_id = semi_dense_id_of_string(class_name);
                      auto method_id = semi_dense_id_of_string(method_name);
                      return MethodInfo{class_id, method_id};
                    })
                .first;
  };

  std::atomic<size_t> unregistered_parent_positions{0};

  static_assert(std::is_same<decltype(m_positions[0]->line), uint32_t>::value);
  static_assert(
      std::is_same<decltype(semi_dense_id_of_string("")), uint32_t>::value);
  std::vector<uint32_t> pos_data(5 * m_positions.size());

  // We process positions in parallel in batches to benefit from cache locality.
  const size_t BATCH_SIZE = 100;
  workqueue_run_for<size_t>(
      0, (m_positions.size() + BATCH_SIZE - 1) / BATCH_SIZE, [&](size_t batch) {
        auto end = std::min(m_positions.size(), (batch + 1) * BATCH_SIZE);
        for (size_t idx = batch * BATCH_SIZE; idx < end; ++idx) {
          auto* pos = m_positions[idx];
          uint32_t parent_line = 0;
          try {
            parent_line = pos->parent == nullptr ? 0 : get_line(pos->parent);
          } catch (std::out_of_range&) {
            ++unregistered_parent_positions;
            TRACE(OPUT, 1, "Parent position %s of %s was not registered",
                  SHOW(pos->parent), SHOW(pos));
          }
          auto [class_id, method_id] = get_method_info(pos->method);
          auto file_id = semi_dense_id_of_string(pos->file->str());
          pos_data[5 * idx + 0] = class_id;
          pos_data[5 * idx + 1] = method_id;
          pos_data[5 * idx + 2] = file_id;
          pos_data[5 * idx + 3] = pos->line;
          pos_data[5 * idx + 4] = parent_line;
        }
      });
  always_assert(pos_data.size() == 5 * m_positions.size());
  always_assert(semi_dense_string_ids.size() == string_pool.size());

  if (unregistered_parent_positions.load() > 0 && !traceEnabled(OPUT, 1)) {
    TRACE(OPUT, 0,
          "%zu parent positions had not been registered. Run with TRACE=OPUT:1 "
          "to list them.",
          unregistered_parent_positions.load());
  }

  std::ofstream ofs(m_filename_v2.c_str(),
                    std::ofstream::out | std::ofstream::binary |
                        std::ofstream::trunc);
  uint32_t magic = 0xfaceb000; // serves as endianness check
  ofs.write(reinterpret_cast<const char*>(&magic), sizeof(magic));
  uint32_t version = 2;
  ofs.write(reinterpret_cast<const char*>(&version), sizeof(version));
  uint32_t spool_count = static_cast<uint32_t>(string_pool.size());
  ofs.write(reinterpret_cast<const char*>(&spool_count), sizeof(spool_count));
  always_assert(string_pool.size() < std::numeric_limits<uint32_t>::max());

  // Finally, rewrite the string-ids following the deterministic ordering of the
  // positions.
  auto map = std::make_unique<uint32_t[]>(next_semi_dense_string_id.load());
  const uint32_t unmapped = 0;
  const uint32_t first_mapped = 1;
  uint32_t next_mapped = first_mapped;
  auto order = [&](uint32_t& string_id) {
    auto& mapped = map[string_id];
    if (mapped == unmapped) {
      const auto& s = string_pool.at(string_id);
      uint32_t ssize = static_cast<uint32_t>(s->size());
      ofs.write(reinterpret_cast<const char*>(&ssize), sizeof(ssize));
      ofs.write(s->data(), static_cast<std::streamsize>(ssize * sizeof(char)));
      mapped = next_mapped++;
    }
    string_id = mapped - first_mapped;
  };
  for (size_t idx = 0; idx < m_positions.size(); ++idx) {
    order(pos_data[5 * idx + 0]); // class_id
    order(pos_data[5 * idx + 1]); // method_id
    order(pos_data[5 * idx + 2]); // file_id
  }
  always_assert(next_mapped - first_mapped == string_pool.size());
  uint32_t pos_count = static_cast<uint32_t>(m_positions.size());
  ofs.write(reinterpret_cast<const char*>(&pos_count), sizeof(pos_count));
  ofs.write(reinterpret_cast<const char*>(pos_data.data()),
            static_cast<std::streamsize>(sizeof(uint32_t) * pos_data.size()));

  write_provenance_trailer(ofs);
  ofs.flush();
  always_assert_log(ofs.good(), "failed to write the line-number map to disk");

  TRACE(OPUT, 2,
        "positions: %zu, string pool size: %zu, semi-dense string ids: %u",
        m_positions.size(), string_pool.size(),
        next_semi_dense_string_id.load());
}

void RealPositionMapper::write_provenance_trailer(std::ofstream& ofs) {
  // `m_positions` is walked in index order, so the entries come out sorted by
  // record index without a sort, and identically on every run.
  std::vector<position_map::ProvenanceEntry> entries;
  for (size_t idx = 0; idx < m_positions.size(); ++idx) {
    auto* pos = m_positions[idx];
    if (!pos->is_unreliable()) {
      continue;
    }
    always_assert(idx <= std::numeric_limits<uint32_t>::max());
    entries.push_back(position_map::ProvenanceEntry{static_cast<uint32_t>(idx),
                                                    /* alt_record_index */ 0,
                                                    /* total_candidates */ 0});
  }

  if (entries.empty()) {
    // With no unreliable positions, the declared v2 body ends at EOF; even an
    // empty trailer would add bytes without carrying information.
    return;
  }

  auto current_offset = [&](const char* description) {
    always_assert_log(ofs.good(),
                      "failed to determine line-map output offset before %s",
                      description);
    const auto offset = ofs.tellp();
    always_assert_log(offset != std::streampos(-1),
                      "failed to determine line-map output offset before %s",
                      description);
    return static_cast<uint64_t>(static_cast<std::streamoff>(offset));
  };
  const auto section_offset = current_offset("provenance section offset");
  const auto section_length =
      static_cast<uint64_t>(entries.size() * sizeof(entries[0]));
  ofs.write(reinterpret_cast<const char*>(entries.data()),
            static_cast<std::streamsize>(section_length));

  const auto directory_offset = current_offset("provenance directory offset");
  position_map::SectionEntry entry{
      static_cast<uint32_t>(position_map::SectionTag::Provenance),
      /* reserved */ 0, section_offset, section_length};
  ofs.write(reinterpret_cast<const char*>(&entry), sizeof(entry));

  position_map::Trailer trailer{directory_offset, /* section_count */ 1,
                                position_map::kTrailerMagic};
  ofs.write(reinterpret_cast<const char*>(&trailer), sizeof(trailer));

  TRACE(OPUT, 2, "provenance: %zu of %zu positions are unreliable",
        entries.size(), m_positions.size());
}

PositionMapper* PositionMapper::make(const std::string& map_filename_v2) {
  if (map_filename_v2.empty()) {
    // If no path is provided for the map, just pass the original line numbers
    // through to the output. This does mean that the line numbers will be
    // incorrect for inlined code.
    return new NoopPositionMapper();
  } else {
    return new RealPositionMapper(map_filename_v2);
  }
}

const DexString* RealPositionMapper::get_source_file(const DexClass*) {
  // Note: When remapping line numbers, we don't simply emit DEX_NO_INDEX for
  // the source_file_idx because that would cause stack traces to print
  // "at com.foo.bar (Unknown source)" even when line number data is
  // available. So we make the source_file_idx point at an empty string
  // instead.
  return DexString::make_string("");
}

const DexString* NoopPositionMapper::get_source_file(const DexClass* clz) {
  return clz->get_source_file();
}
