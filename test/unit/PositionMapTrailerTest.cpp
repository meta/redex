/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include <unistd.h>

#include <algorithm>
#include <array>
#include <cstdio>
#include <cstring>
#include <fstream>
#include <string>
#include <vector>

#include "Creators.h"
#include "DexPosition.h"
#include "PositionJoin.h"
#include "RedexContext.h"
#include "RedexTest.h"
#include "TypeUtil.h"

namespace {

class PositionMapTrailerTest : public RedexTest {
 protected:
  std::string map_path(const char* name) {
    // Per-process as well as per-name: TPX can run this binary more than once
    // on a host at a time, and a shared name would have the runs overwrite each
    // other's map.
    auto path = testing::TempDir() + "redex-position-map-trailer-" + name +
                "-" + std::to_string(getpid()) + ".bin";
    // Removed in TearDown rather than at the end of each test body: a failing
    // ASSERT_* returns from the test immediately, so a trailing `std::remove`
    // is exactly the line that does not run on the path that leaves a file
    // behind.
    m_paths.push_back(path);
    return path;
  }

  void TearDown() override {
    for (const auto& path : m_paths) {
      std::remove(path.c_str());
    }
    m_paths.clear();
    RedexTest::TearDown();
  }

  std::vector<std::string> m_paths;

  static std::vector<char> read_file(const std::string& path) {
    std::ifstream ifs(path, std::ios::binary);
    EXPECT_TRUE(ifs.is_open()) << "could not open " << path;
    return std::vector<char>((std::istreambuf_iterator<char>(ifs)),
                             std::istreambuf_iterator<char>());
  }

  // The v2 body, parsed the way a consumer would: header, string pool, then the
  // fixed-width position records.
  struct ParsedMap {
    std::vector<std::string> string_pool;
    std::vector<std::array<uint32_t, 5>> positions;
  };

  static ParsedMap parse(const std::vector<char>& bytes) {
    ParsedMap parsed;
    size_t at = 0;
    auto u32 = [&]() {
      uint32_t v = 0;
      memcpy(&v, bytes.data() + at, sizeof(v));
      at += sizeof(v);
      return v;
    };
    EXPECT_EQ(u32(), 0xfaceb000u);
    EXPECT_EQ(u32(), 2u);
    uint32_t spool_count = u32();
    for (uint32_t i = 0; i < spool_count; ++i) {
      uint32_t ssize = u32();
      parsed.string_pool.emplace_back(bytes.data() + at, ssize);
      at += ssize;
    }
    uint32_t pos_count = u32();
    for (uint32_t i = 0; i < pos_count; ++i) {
      std::array<uint32_t, 5> record{};
      memcpy(record.data(), bytes.data() + at, sizeof(record));
      at += sizeof(record);
      parsed.positions.push_back(record);
    }
    return parsed;
  }

  static bool read_u32(const std::vector<char>& bytes,
                       size_t* offset,
                       uint32_t* value) {
    if (*offset > bytes.size() || bytes.size() - *offset < sizeof(*value)) {
      return false;
    }
    memcpy(value, bytes.data() + *offset, sizeof(*value));
    *offset += sizeof(*value);
    return true;
  }

  // The provenance trailer, read the way a consumer would: the trailer at the
  // end of the file, the first section its directory lists, and that section's
  // entries. A part behind a missing magic or an out-of-bounds offset is left
  // empty, so each test asserts on exactly the parts it relies on.
  struct Provenance {
    position_map::Trailer trailer{};
    position_map::SectionEntry section{};
    std::vector<position_map::ProvenanceEntry> entries;
  };

  static Provenance read_provenance(const std::vector<char>& bytes) {
    Provenance read;
    if (bytes.size() < sizeof(read.trailer)) {
      return read;
    }
    memcpy(&read.trailer, bytes.data() + bytes.size() - sizeof(read.trailer),
           sizeof(read.trailer));
    if (read.trailer.magic != position_map::kTrailerMagic ||
        size_t{read.trailer.directory_offset} + sizeof(read.section) >
            bytes.size()) {
      return read;
    }
    memcpy(&read.section, bytes.data() + read.trailer.directory_offset,
           sizeof(read.section));
    if (size_t{read.section.offset} + read.section.length > bytes.size()) {
      return read;
    }
    read.entries.resize(read.section.length /
                        sizeof(position_map::ProvenanceEntry));
    memcpy(read.entries.data(), bytes.data() + read.section.offset,
           read.entries.size() * sizeof(position_map::ProvenanceEntry));
    return read;
  }

  static std::unique_ptr<DexPosition> pos(uint32_t line) {
    return std::make_unique<DexPosition>(
        DexString::make_string("LFoo;.bar:()V"),
        DexString::make_string("Foo.java"), line);
  }

  // The kind of position Redex puts at the start of a method it generated,
  // such as an outlined method (`MethodCreator`, the outliner, the method
  // splitter). It names no source method.
  static std::unique_ptr<DexPosition> redex_generated() {
    auto position = std::make_unique<DexPosition>(
        DexString::make_string("RedexGenerated"), 0);
    position->bind(
        DexString::make_string("Lcom/redex/Outlined$0$0;.$outlined$0:()V"));
    return position;
  }

  static std::vector<uint32_t> member_lines(
      const PositionPatternSwitchManager::AltSet& alt_set) {
    std::vector<uint32_t> lines;
    for (const auto* member : alt_set.members) {
      lines.push_back(member->line);
    }
    return lines;
  }
};

// A map with no provenance must end exactly after the v2 positions array.
// An empty section would add bytes without information.
TEST_F(PositionMapTrailerTest, a_map_with_no_provenance_gains_no_bytes) {
  auto path = map_path("clean");
  auto positions = std::vector<std::unique_ptr<DexPosition>>{};
  positions.push_back(pos(10));
  positions.push_back(pos(11));

  RealPositionMapper mapper(path);
  for (auto& p : positions) {
    mapper.position_to_line(p.get());
  }
  mapper.write_map();

  auto bytes = read_file(path);
  ASSERT_FALSE(bytes.empty());

  size_t offset = 0;
  uint32_t magic = 0;
  uint32_t version = 0;
  uint32_t string_count = 0;
  ASSERT_TRUE(read_u32(bytes, &offset, &magic));
  ASSERT_TRUE(read_u32(bytes, &offset, &version));
  ASSERT_TRUE(read_u32(bytes, &offset, &string_count));
  EXPECT_EQ(magic, 0xfaceb000u);
  EXPECT_EQ(version, 2u);
  for (uint32_t i = 0; i < string_count; ++i) {
    uint32_t string_size = 0;
    ASSERT_TRUE(read_u32(bytes, &offset, &string_size));
    ASSERT_LE(offset, bytes.size());
    ASSERT_LE(string_size, bytes.size() - offset);
    offset += string_size;
  }
  uint32_t position_count = 0;
  ASSERT_TRUE(read_u32(bytes, &offset, &position_count));
  constexpr size_t words_per_position = 5;
  ASSERT_LE(offset, bytes.size());
  ASSERT_LE(position_count,
            (bytes.size() - offset) / (words_per_position * sizeof(uint32_t)));
  offset += position_count * words_per_position * sizeof(uint32_t);
  EXPECT_EQ(offset, bytes.size());

  // Body bytes must not masquerade as a provenance trailer.
  ASSERT_GE(bytes.size(), sizeof(position_map::Trailer));
  EXPECT_NE(read_provenance(bytes).trailer.magic, position_map::kTrailerMagic);
}

// Synthetic line-0 helper positions do not imply ambiguity. Emitting them into
// the map must therefore leave the trailer absent.
TEST_F(PositionMapTrailerTest, a_synthetic_position_alone_gains_no_bytes) {
  auto path = map_path("synthetic");
  auto* cls_type = DexType::make_type("LSynthetic;");
  auto* proto =
      DexProto::make_proto(type::_void(), DexTypeList::make_type_list({}));
  auto* method =
      DexMethod::make_method(cls_type, DexString::make_string("m"), proto)
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  auto synthetic = DexPosition::make_synthetic_entry_position(method);

  RealPositionMapper mapper(path);
  mapper.position_to_line(synthetic.get());
  mapper.write_map();

  auto bytes = read_file(path);
  ASSERT_GE(bytes.size(), sizeof(position_map::Trailer));
  EXPECT_NE(read_provenance(bytes).trailer.magic, position_map::kTrailerMagic);
}

TEST_F(PositionMapTrailerTest, interning_clears_only_the_copy_provenance) {
  auto original = pos(10);
  original->mark_unreliable();

  PositionPatternSwitchManager manager;
  auto pattern_id = manager.make_pattern(PositionPattern{original.get()});
  auto* interned = manager.get_patterns().at(pattern_id).at(0);

  EXPECT_TRUE(original->is_unreliable());
  EXPECT_FALSE(interned->is_unreliable());
}

TEST_F(PositionMapTrailerTest,
       unreliable_positions_are_sorted_in_an_exact_trailer_layout) {
  auto path = map_path("marked");
  auto positions = std::vector<std::unique_ptr<DexPosition>>{};
  positions.reserve(4);
  positions.push_back(pos(10));
  positions.push_back(pos(11));
  positions.push_back(pos(12));
  positions.push_back(pos(13));
  positions[1]->mark_unreliable();
  positions[3]->mark_unreliable();

  RealPositionMapper mapper(path);
  std::vector<uint32_t> record_indices;
  record_indices.reserve(positions.size());
  for (auto& p : positions) {
    // position_to_line returns a 1-based line; the record index is one less.
    record_indices.push_back(mapper.position_to_line(p.get()) - 1);
  }
  mapper.write_map();

  auto bytes = read_file(path);
  ASSERT_GT(bytes.size(), sizeof(position_map::Trailer));

  auto read = read_provenance(bytes);
  const auto& trailer = read.trailer;
  ASSERT_EQ(trailer.magic, position_map::kTrailerMagic);
  ASSERT_EQ(trailer.section_count, 1u);
  EXPECT_EQ(trailer.directory_offset +
                trailer.section_count * sizeof(position_map::SectionEntry) +
                sizeof(position_map::Trailer),
            bytes.size());

  const auto& entry = read.section;
  EXPECT_EQ(entry.tag,
            static_cast<uint32_t>(position_map::SectionTag::Provenance));
  ASSERT_EQ(entry.length, 2 * sizeof(position_map::ProvenanceEntry));
  ASSERT_LE(entry.offset + entry.length, trailer.directory_offset);

  const auto& provenance = read.entries;
  EXPECT_EQ(provenance[0].record_index, record_indices[1]);
  EXPECT_EQ(provenance[1].record_index, record_indices[3]);
  EXPECT_LT(provenance[0].record_index, provenance[1].record_index);
  for (const auto& item : provenance) {
    EXPECT_EQ(item.alt_record_index, 0u);
    EXPECT_EQ(item.total_candidates, 0u);
  }
}

// The candidate records are reached only through a position's alt id, which the
// reachability walk over the positions array cannot see. If that seeding is
// missed the entry still points somewhere -- into whatever record happens to
// sit at that index -- so this follows the index and checks what is actually
// there.
TEST_F(PositionMapTrailerTest, candidates_are_emitted_and_the_entry_resolves) {
  auto path = map_path("candidates");
  auto survivor = pos(10);
  auto first = pos(20);
  auto second = pos(30);

  auto* manager = g_redex->get_position_pattern_switch_manager();
  manager->record_candidates(survivor.get(), {first.get(), second.get()});
  ASSERT_TRUE(survivor->is_unreliable());
  ASSERT_NE(survivor->alt_id(), 0u);

  RealPositionMapper mapper(path);
  uint32_t survivor_index = mapper.position_to_line(survivor.get()) - 1;
  mapper.write_map();

  auto bytes = read_file(path);
  auto read = read_provenance(bytes);
  ASSERT_EQ(read.trailer.magic, position_map::kTrailerMagic);
  ASSERT_EQ(read.section.length, sizeof(position_map::ProvenanceEntry));
  const auto& provenance = read.entries.at(0);
  EXPECT_EQ(provenance.record_index, survivor_index);
  // Not capped, so no pre-cap total is reported: the records themselves say how
  // many there are, and repeating it would put the same number on every row.
  EXPECT_EQ(provenance.total_candidates, 0u);
  ASSERT_NE(provenance.alt_record_index, 0u);

  auto parsed = parse(bytes);
  ASSERT_LT(provenance.alt_record_index + 2u, parsed.positions.size());
  // The record the entry points at is the count, holding the number of cases,
  // and the two after it are the cases.
  const auto& count_record = parsed.positions[provenance.alt_record_index];
  EXPECT_EQ(parsed.string_pool[count_record[1]], "count");
  EXPECT_EQ(count_record[3], 2u);
  for (uint32_t i = 1; i <= 2; ++i) {
    const auto& case_record = parsed.positions[provenance.alt_record_index + i];
    EXPECT_EQ(parsed.string_pool[case_record[1]], "case");
    // All-mode alternatives have no discriminator; each case encodes line 0.
    EXPECT_EQ(case_record[3], 0u);
    // Each case points at a real candidate through its parent.
    EXPECT_NE(case_record[4], 0u);
  }
  std::remove(path.c_str());
}

// More candidates than are worth reading are capped, and the count before
// capping is kept so the result can say "8 of 12" instead of pretending.
TEST_F(PositionMapTrailerTest, an_oversized_candidate_list_is_capped_honestly) {
  auto path = map_path("capped");
  auto survivor = pos(10);
  std::vector<std::unique_ptr<DexPosition>> owned;
  std::vector<DexPosition*> candidates;
  for (uint32_t i = 0; i < 12; ++i) {
    owned.push_back(pos(100 + i));
    candidates.push_back(owned.back().get());
  }

  auto* manager = g_redex->get_position_pattern_switch_manager();
  manager->record_candidates(
      survivor.get(),
      std::vector<const DexPosition*>(candidates.begin(), candidates.end()));

  RealPositionMapper mapper(path);
  mapper.position_to_line(survivor.get());
  mapper.write_map();

  auto bytes = read_file(path);
  auto read = read_provenance(bytes);
  const auto& provenance = read.entries.at(0);

  EXPECT_EQ(provenance.total_candidates, 12u);
  auto parsed = parse(bytes);
  const auto& count_record = parsed.positions[provenance.alt_record_index];
  EXPECT_EQ(count_record[3], PositionPatternSwitchManager::kMaxCandidates);
  std::remove(path.c_str());
}

// A survivor merged into twice stands for the sites of both merges. Fails if
// the second call names only its own candidates: the count reads 2 and the
// first merge's site is absent from the cases.
TEST_F(PositionMapTrailerTest, a_second_merge_adds_to_the_sites_already_named) {
  auto path = map_path("accumulated");
  auto survivor = pos(10);
  auto first = pos(20);
  auto second = pos(30);
  auto third = pos(40);

  auto* manager = g_redex->get_position_pattern_switch_manager();
  manager->record_candidates(survivor.get(), {first.get()});
  auto after_first = survivor->alt_id();
  ASSERT_NE(after_first, 0u);
  manager->record_candidates(survivor.get(), {second.get(), third.get()});
  // A different set, so a different id: the survivor is not left pointing at
  // the set it had when it stood for one site.
  EXPECT_NE(survivor->alt_id(), after_first);

  RealPositionMapper mapper(path);
  mapper.position_to_line(survivor.get());
  mapper.write_map();

  auto bytes = read_file(path);
  auto read = read_provenance(bytes);
  const auto& provenance = read.entries.at(0);

  auto parsed = parse(bytes);
  const auto& count_record = parsed.positions[provenance.alt_record_index];
  EXPECT_EQ(parsed.string_pool[count_record[1]], "count");
  EXPECT_EQ(count_record[3], 3u);
  std::remove(path.c_str());
}

// Full membership survives the emission cap, so a later unique candidate
// advances the exact total even when it does not enter the emitted first eight.
TEST_F(PositionMapTrailerTest, an_oversized_set_counts_a_new_member) {
  auto path = map_path("capped-then-merged");
  auto survivor = pos(10);
  std::vector<std::unique_ptr<DexPosition>> owned;
  std::vector<DexPosition*> candidates;
  for (uint32_t i = 0; i < 12; ++i) {
    owned.push_back(pos(100 + i));
    candidates.push_back(owned.back().get());
  }
  auto late = pos(500);

  auto* manager = g_redex->get_position_pattern_switch_manager();
  manager->record_candidates(
      survivor.get(),
      std::vector<const DexPosition*>(candidates.begin(), candidates.end()));
  manager->record_candidates(survivor.get(), {late.get()});

  RealPositionMapper mapper(path);
  mapper.position_to_line(survivor.get());
  mapper.write_map();

  auto bytes = read_file(path);
  auto read = read_provenance(bytes);
  const auto& provenance = read.entries.at(0);

  EXPECT_EQ(provenance.total_candidates, 13u);
  auto parsed = parse(bytes);
  const auto& count_record = parsed.positions[provenance.alt_record_index];
  EXPECT_EQ(count_record[3], PositionPatternSwitchManager::kMaxCandidates);
}

TEST_F(PositionMapTrailerTest,
       readding_a_dropped_member_does_not_inflate_the_count) {
  auto path = map_path("capped-duplicate");
  auto survivor = pos(10);
  std::vector<std::unique_ptr<DexPosition>> owned;
  std::vector<DexPosition*> candidates;
  for (uint32_t i = 0; i < 12; ++i) {
    owned.push_back(pos(100 + i));
    candidates.push_back(owned.back().get());
  }

  auto* manager = g_redex->get_position_pattern_switch_manager();
  manager->record_candidates(
      survivor.get(),
      std::vector<const DexPosition*>(candidates.begin(), candidates.end()));
  auto duplicate_of_dropped = pos(110);
  manager->record_candidates(survivor.get(), {duplicate_of_dropped.get()});

  RealPositionMapper mapper(path);
  mapper.position_to_line(survivor.get());
  mapper.write_map();

  auto bytes = read_file(path);
  auto read = read_provenance(bytes);
  const auto& provenance = read.entries.at(0);
  EXPECT_EQ(provenance.total_candidates, 12u);
}

// Code Redex gave a synthetic entry position still came from that method, at a
// line nobody knows. The candidate names the method, and its record carries
// line 0, which is rendered as a frame without a line.
TEST_F(PositionMapTrailerTest,
       a_synthetic_entry_position_is_a_method_level_candidate) {
  auto path = map_path("method-level");
  auto* cls_type = DexType::make_type("LSyntheticEntry;");
  ClassCreator creator(cls_type);
  creator.set_super(type::java_lang_Object());
  auto* cls = creator.create();
  cls->set_source_file(DexString::make_string("SyntheticEntry.java"));
  auto* proto =
      DexProto::make_proto(type::_void(), DexTypeList::make_type_list({}));
  auto* method =
      DexMethod::make_method(cls_type, DexString::make_string("m"), proto)
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  auto entry = DexPosition::make_synthetic_entry_position(method);
  ASSERT_TRUE(entry->is_synthetic());

  auto survivor = pos(10);
  auto* manager = g_redex->get_position_pattern_switch_manager();
  manager->record_candidates(survivor.get(), {entry.get()});

  ASSERT_TRUE(survivor->is_unreliable());
  ASSERT_NE(survivor->alt_id(), 0u);
  const auto& alt_set = manager->get_alt_set(survivor->alt_id());
  ASSERT_EQ(alt_set.members.size(), 1u);
  EXPECT_EQ(alt_set.members[0]->method, entry->method);
  EXPECT_EQ(alt_set.members[0]->file->str(), "SyntheticEntry.java");
  EXPECT_EQ(alt_set.members[0]->line, 0u);

  RealPositionMapper mapper(path);
  mapper.position_to_line(survivor.get());
  mapper.write_map();

  auto bytes = read_file(path);
  auto read = read_provenance(bytes);
  ASSERT_EQ(read.trailer.magic, position_map::kTrailerMagic);
  // The candidate itself is not merged, so only the survivor has an entry.
  ASSERT_EQ(read.section.length, sizeof(position_map::ProvenanceEntry));
  const auto& provenance = read.entries.at(0);
  ASSERT_NE(provenance.alt_record_index, 0u);

  auto parsed = parse(bytes);
  ASSERT_LT(provenance.alt_record_index + 1u, parsed.positions.size());
  EXPECT_EQ(parsed.positions[provenance.alt_record_index][3], 1u);
  const auto& case_record = parsed.positions[provenance.alt_record_index + 1];
  EXPECT_EQ(parsed.string_pool[case_record[1]], "case");
  ASSERT_NE(case_record[4], 0u);
  const auto& candidate = parsed.positions.at(case_record[4] - 1);
  EXPECT_EQ(parsed.string_pool[candidate[0]], "SyntheticEntry");
  EXPECT_EQ(parsed.string_pool[candidate[1]], "m");
  EXPECT_EQ(parsed.string_pool[candidate[2]], "SyntheticEntry.java");
  EXPECT_EQ(candidate[3], 0u);
}

// The position at the start of a method Redex generated names no source
// method, so offering it records that the sites were not captured.
TEST_F(PositionMapTrailerTest,
       a_redex_generated_methods_own_position_is_never_a_candidate) {
  auto survivor = pos(10);
  auto generated = redex_generated();
  auto* manager = g_redex->get_position_pattern_switch_manager();
  manager->record_candidates(survivor.get(), {generated.get()});

  EXPECT_TRUE(survivor->is_unreliable());
  EXPECT_EQ(survivor->alt_id(), 0u);
}

// Outliner switch positions are wire records whose lines are ids.
TEST_F(PositionMapTrailerTest, switch_positions_are_not_candidates) {
  auto* manager = g_redex->get_position_pattern_switch_manager();
  auto slot = pos(20);
  auto pattern_id = manager->make_pattern({slot.get()});
  auto other_slot = pos(21);
  auto other_pattern_id = manager->make_pattern({other_slot.get()});
  auto switch_id = manager->make_switch(
      {{pattern_id, slot.get()}, {other_pattern_id, other_slot.get()}});
  auto switch_position = manager->make_switch_position(switch_id);

  auto survivor = pos(10);
  manager->record_candidates(survivor.get(), {switch_position.get()});
  EXPECT_TRUE(survivor->is_unreliable());
  EXPECT_EQ(survivor->alt_id(), 0u);
}

TEST_F(PositionMapTrailerTest,
       a_redex_generated_ancestor_disqualifies_a_candidate) {
  auto survivor = pos(10);
  auto generated = redex_generated();
  auto candidate = pos(20);
  candidate->parent = generated.get();
  auto* manager = g_redex->get_position_pattern_switch_manager();
  manager->record_candidates(survivor.get(), {candidate.get()});

  EXPECT_TRUE(survivor->is_unreliable());
  EXPECT_EQ(survivor->alt_id(), 0u);
}

TEST_F(PositionMapTrailerTest, a_merged_synthetic_position_stays_synthetic) {
  auto survivor = DexPosition::make_synthetic_position(
      DexString::make_string("LFabricated;.m:()V"));
  auto candidate = pos(20);
  auto* manager = g_redex->get_position_pattern_switch_manager();
  manager->record_candidates(survivor.get(), {candidate.get()});

  EXPECT_TRUE(survivor->is_synthetic());
  EXPECT_TRUE(survivor->is_unreliable());
  ASSERT_NE(survivor->alt_id(), 0u);

  // Merged again, it stands for its own method at an unknown line and for the
  // site it already stood for.
  auto outer = pos(30);
  manager->record_candidates(outer.get(), {survivor.get()});
  EXPECT_TRUE(outer->is_unreliable());
  ASSERT_NE(outer->alt_id(), 0u);
  auto lines = member_lines(manager->get_alt_set(outer->alt_id()));
  std::sort(lines.begin(), lines.end());
  EXPECT_EQ(lines, (std::vector<uint32_t>{0, 20}));
}

// A candidate that already stands for other sites contributes its own line and
// those sites, as one flat list.
TEST_F(PositionMapTrailerTest,
       a_candidate_that_is_itself_ambiguous_contributes_its_sites) {
  auto path = map_path("nested");
  auto outer = pos(10);
  auto inner = pos(20);
  auto first = pos(30);
  auto second = pos(40);
  auto* manager = g_redex->get_position_pattern_switch_manager();
  manager->record_candidates(inner.get(), {first.get(), second.get()});
  manager->record_candidates(outer.get(), {inner.get()});

  RealPositionMapper mapper(path);
  mapper.position_to_line(outer.get());
  mapper.write_map();

  auto bytes = read_file(path);
  auto read = read_provenance(bytes);
  ASSERT_EQ(read.trailer.magic, position_map::kTrailerMagic);
  EXPECT_EQ(read.section.length, sizeof(position_map::ProvenanceEntry));

  auto parsed = parse(bytes);
  size_t count_records = 0;
  std::vector<uint32_t> case_lines;
  for (const auto& record : parsed.positions) {
    if (parsed.string_pool[record[1]] == "count") {
      ++count_records;
      EXPECT_EQ(record[3], 3u);
    } else if (parsed.string_pool[record[1]] == "case") {
      EXPECT_EQ(record[3], 0u);
      ASSERT_NE(record[4], 0u);
      case_lines.push_back(parsed.positions.at(record[4] - 1)[3]);
    }
  }
  EXPECT_EQ(count_records, 1u);
  EXPECT_EQ(case_lines, (std::vector<uint32_t>{20, 30, 40}));
}

// One source place counts once, however many candidates name it. Here line 5
// is offered directly and through a candidate that stood for line 7 as well,
// and line 7 is offered directly too.
TEST_F(PositionMapTrailerTest, each_source_place_counts_once) {
  auto survivor = pos(3);
  auto direct = pos(5);
  auto merged = pos(5);
  auto merged_site = pos(7);
  auto other = pos(7);
  auto* manager = g_redex->get_position_pattern_switch_manager();
  manager->record_candidates(merged.get(), {merged_site.get()});
  ASSERT_NE(merged->alt_id(), 0u);

  manager->record_candidates(survivor.get(),
                             {direct.get(), merged.get(), other.get()});

  ASSERT_NE(survivor->alt_id(), 0u);
  const auto& alt_set = manager->get_alt_set(survivor->alt_id());
  EXPECT_EQ(alt_set.total_candidates(), 2u);
  EXPECT_EQ(member_lines(alt_set), (std::vector<uint32_t>{5, 7}));
  for (const auto* member : alt_set.members) {
    EXPECT_FALSE(member->is_unreliable());
  }
}

// Identity is method, file, line and parent chain. Two candidates that differ
// only in what is known about their caller name the same place.
TEST_F(PositionMapTrailerTest,
       candidates_differing_only_in_provenance_count_once) {
  auto clean_caller = pos(1);
  auto merged_caller = pos(1);
  auto caller_site = pos(2);
  auto* manager = g_redex->get_position_pattern_switch_manager();
  manager->record_candidates(merged_caller.get(), {caller_site.get()});
  ASSERT_NE(merged_caller->alt_id(), 0u);
  auto first = pos(20);
  first->parent = clean_caller.get();
  auto second = pos(20);
  second->parent = merged_caller.get();

  auto survivor = pos(10);
  manager->record_candidates(survivor.get(), {first.get(), second.get()});

  ASSERT_NE(survivor->alt_id(), 0u);
  EXPECT_EQ(manager->get_alt_set(survivor->alt_id()).total_candidates(), 1u);
}

// The survivor's own place is what the frame already shows, so it is never one
// of its other possible places, even when a candidate stood for it.
TEST_F(PositionMapTrailerTest, the_survivors_own_place_is_not_a_candidate) {
  auto survivor = pos(10);
  auto merged = pos(20);
  auto survivor_copy = pos(10);
  auto* manager = g_redex->get_position_pattern_switch_manager();
  manager->record_candidates(merged.get(), {survivor_copy.get()});

  manager->record_candidates(survivor.get(), {merged.get()});

  ASSERT_NE(survivor->alt_id(), 0u);
  EXPECT_EQ(member_lines(manager->get_alt_set(survivor->alt_id())),
            (std::vector<uint32_t>{20}));
}

// Candidates that all name the survivor's own place add nothing to what the
// survivor already presents, so the survivor is left exactly as it was.
TEST_F(PositionMapTrailerTest,
       candidates_naming_only_the_survivors_place_leave_it_unmarked) {
  auto survivor = pos(10);
  auto copy = pos(10);
  auto another_copy = pos(10);
  auto* manager = g_redex->get_position_pattern_switch_manager();
  EXPECT_EQ(manager->record_candidates(survivor.get(),
                                       {copy.get(), another_copy.get()}),
            positions::FidelityChange::Unchanged);

  EXPECT_FALSE(survivor->is_unreliable());
  EXPECT_EQ(survivor->alt_id(), 0u);
  EXPECT_EQ(manager->get_num_alt_sets(), 0u);
}

TEST_F(PositionMapTrailerTest,
       all_mode_emission_is_ordered_by_candidate_content) {
  auto first_path = map_path("ordered-first");
  auto second_path = map_path("ordered-second");
  auto first_survivor = pos(10);
  auto second_survivor = pos(10);
  auto first_low = pos(20);
  auto first_high = pos(30);
  auto second_low = pos(20);
  auto second_high = pos(30);
  auto* manager = g_redex->get_position_pattern_switch_manager();
  manager->record_candidates(first_survivor.get(),
                             {first_low.get(), first_high.get()});
  manager->record_candidates(second_survivor.get(),
                             {second_high.get(), second_low.get()});

  RealPositionMapper first_mapper(first_path);
  first_mapper.position_to_line(first_survivor.get());
  first_mapper.write_map();
  RealPositionMapper second_mapper(second_path);
  second_mapper.position_to_line(second_survivor.get());
  second_mapper.write_map();

  EXPECT_EQ(read_file(first_path), read_file(second_path));
}

TEST_F(PositionMapTrailerTest,
       candidate_sets_do_not_alias_pattern_selected_switches) {
  auto survivor = pos(10);
  auto first = pos(20);
  auto second = pos(30);
  auto* manager = g_redex->get_position_pattern_switch_manager();
  manager->record_candidates(survivor.get(), {first.get(), second.get()});
  auto alt_set = manager->get_alt_set(survivor->alt_id());

  PositionSwitch position_switch{{0, first.get()}, {1, second.get()}};
  auto switch_id = manager->make_switch(std::move(position_switch));

  EXPECT_NE(alt_set.alternatives_id, switch_id);
  EXPECT_EQ(manager->get_alternatives().at(alt_set.alternatives_id).selection,
            PositionAlternativesSelection::All);
  EXPECT_EQ(manager->get_alternatives().at(switch_id).selection,
            PositionAlternativesSelection::ByPattern);
}

TEST_F(PositionMapTrailerTest,
       outliner_provenance_marks_only_the_matching_target_record) {
  auto path = map_path("outliner-provenance");
  auto first_slot = pos(100);
  auto second_slot = pos(101);
  second_slot->mark_unreliable();
  auto other_first_slot = pos(200);
  auto other_second_slot = pos(201);
  auto* manager = g_redex->get_position_pattern_switch_manager();
  std::vector<DexPosition*> first_slots;
  auto first_pattern_id = manager->make_pattern(
      {first_slot.get(), second_slot.get()}, &first_slots);
  std::vector<DexPosition*> second_slots;
  auto second_pattern_id = manager->make_pattern(
      {other_first_slot.get(), other_second_slot.get()}, &second_slots);
  // The switch for the second instruction selects each pattern's second slot.
  auto switch_id = manager->make_switch({
      {first_pattern_id, second_slot.get(), first_slots.at(1)},
      {second_pattern_id, other_second_slot.get(), second_slots.at(1)},
  });

  auto first_pattern_position =
      manager->make_pattern_position(first_pattern_id);
  auto second_pattern_position =
      manager->make_pattern_position(second_pattern_id);
  auto switch_position = manager->make_switch_position(switch_id);
  RealPositionMapper mapper(path);
  mapper.position_to_line(first_pattern_position.get());
  mapper.position_to_line(second_pattern_position.get());
  mapper.position_to_line(switch_position.get());
  mapper.write_map();

  auto bytes = read_file(path);
  auto read = read_provenance(bytes);
  ASSERT_EQ(read.trailer.magic, position_map::kTrailerMagic);
  ASSERT_EQ(read.section.length, sizeof(position_map::ProvenanceEntry));
  const auto& provenance = read.entries.at(0);

  auto parsed = parse(bytes);
  ASSERT_LT(provenance.record_index, parsed.positions.size());
  EXPECT_EQ(parsed.positions[provenance.record_index][3], 101u);
  std::remove(path.c_str());
}

// Two patterns of one outlined method select the same interned target, and
// only one of them disagreed about that slot. The target's record is shared by
// both cases -- and by any other switch selecting it -- so the disagreement
// has to land on a record of its own, not on the shared one.
TEST_F(PositionMapTrailerTest,
       an_unreliable_slot_does_not_mark_a_shared_target_record) {
  auto path = map_path("outliner-shared-target");
  auto marked_target = pos(30);
  marked_target->mark_unreliable();
  auto first_rest = pos(100);
  auto target = pos(30);
  auto other_rest = pos(200);
  auto* manager = g_redex->get_position_pattern_switch_manager();
  std::vector<DexPosition*> unreliable_slots;
  auto unreliable_pattern_id = manager->make_pattern(
      {marked_target.get(), first_rest.get()}, &unreliable_slots);
  ASSERT_NE(unreliable_slots.at(0), nullptr);
  std::vector<DexPosition*> reliable_slots;
  auto reliable_pattern_id =
      manager->make_pattern({target.get(), other_rest.get()}, &reliable_slots);
  ASSERT_EQ(reliable_slots.at(0), nullptr);
  auto switch_id = manager->make_switch({
      {unreliable_pattern_id, marked_target.get(), unreliable_slots.at(0)},
      {reliable_pattern_id, target.get(), reliable_slots.at(0)},
  });

  auto unreliable_pattern_position =
      manager->make_pattern_position(unreliable_pattern_id);
  auto reliable_pattern_position =
      manager->make_pattern_position(reliable_pattern_id);
  auto switch_position = manager->make_switch_position(switch_id);
  RealPositionMapper mapper(path);
  mapper.position_to_line(unreliable_pattern_position.get());
  mapper.position_to_line(reliable_pattern_position.get());
  mapper.position_to_line(switch_position.get());
  mapper.write_map();

  auto bytes = read_file(path);
  auto read = read_provenance(bytes);
  ASSERT_EQ(read.trailer.magic, position_map::kTrailerMagic);
  ASSERT_EQ(read.section.length, sizeof(position_map::ProvenanceEntry));
  const auto& provenance = read.entries.at(0);

  auto parsed = parse(bytes);
  ASSERT_LT(provenance.record_index, parsed.positions.size());
  EXPECT_EQ(parsed.positions[provenance.record_index][3], 30u);

  size_t cases = 0;
  for (const auto& record : parsed.positions) {
    if (parsed.string_pool.at(record[1]) != "case") {
      continue;
    }
    ++cases;
    ASSERT_NE(record[4], 0u);
    const auto target_index = record[4] - 1;
    EXPECT_EQ(parsed.positions.at(target_index)[3], 30u);
    if (record[3] == unreliable_pattern_id) {
      EXPECT_EQ(target_index, provenance.record_index);
    } else {
      EXPECT_EQ(record[3], reliable_pattern_id);
      EXPECT_NE(target_index, provenance.record_index);
    }
  }
  EXPECT_EQ(cases, 2u);
}

// A duplicate folded into an equal survivor contributes no new line of its own,
// but the survivor inherits every site the duplicate already stood for.
TEST_F(PositionMapTrailerTest,
       folding_a_duplicate_keeps_the_sites_it_stood_for) {
  auto survivor = pos(10);
  auto duplicate = pos(10);
  auto first = pos(20);
  auto second = pos(30);
  auto* manager = g_redex->get_position_pattern_switch_manager();
  manager->record_candidates(duplicate.get(), {first.get(), second.get()});
  ASSERT_NE(duplicate->alt_id(), 0u);

  manager->record_candidates(survivor.get(), {duplicate.get()});

  EXPECT_TRUE(survivor->is_unreliable());
  ASSERT_NE(survivor->alt_id(), 0u);
  EXPECT_EQ(manager->get_alt_set(survivor->alt_id()).total_candidates(), 2u);
}

// A survivor that already stands for several sites can be merged into again.
// Stopping at the ambiguity bit would leave the recorded total short of the
// truth while it is still written as exact.
TEST_F(PositionMapTrailerTest,
       a_later_merge_reaches_an_already_ambiguous_survivor) {
  auto survivor = pos(10);
  auto first = pos(20);
  auto late = pos(30);
  auto* manager = g_redex->get_position_pattern_switch_manager();
  manager->record_candidates(survivor.get(), {first.get()});
  ASSERT_EQ(manager->get_alt_set(survivor->alt_id()).total_candidates(), 1u);

  manager->record_candidates(survivor.get(), {late.get()});

  ASSERT_NE(survivor->alt_id(), 0u);
  EXPECT_EQ(manager->get_alt_set(survivor->alt_id()).total_candidates(), 2u);
}

// A victim that is itself ambiguous carries its sites into the survivor rather
// than degrading it to a bare ambiguity bit.
TEST_F(PositionMapTrailerTest,
       a_merge_carries_over_the_sites_the_victim_stood_for) {
  auto survivor = pos(10);
  auto victim = pos(20);
  auto site = pos(30);
  auto* manager = g_redex->get_position_pattern_switch_manager();
  manager->record_candidates(victim.get(), {site.get()});

  manager->record_candidates(survivor.get(), {victim.get()});

  EXPECT_TRUE(survivor->is_unreliable());
  ASSERT_NE(survivor->alt_id(), 0u);
  EXPECT_EQ(member_lines(manager->get_alt_set(survivor->alt_id())),
            (std::vector<uint32_t>{20, 30}));
}

// Merging in a site that cannot be named makes the set incomplete, and the
// format has no way to say "these, plus others". Keeping the old set would
// present an incomplete list as the whole truth.
TEST_F(PositionMapTrailerTest,
       an_unnamed_site_discards_the_set_it_invalidates) {
  auto survivor = pos(10);
  auto first = pos(20);
  auto* manager = g_redex->get_position_pattern_switch_manager();
  manager->record_candidates(survivor.get(), {first.get()});
  ASSERT_NE(survivor->alt_id(), 0u);

  auto generated = redex_generated();
  manager->record_candidates(survivor.get(), {generated.get()});

  EXPECT_TRUE(survivor->is_unreliable());
  EXPECT_EQ(survivor->alt_id(), 0u);
}

TEST_F(PositionMapTrailerTest, a_merge_with_no_victim_discards_the_set) {
  auto survivor = pos(10);
  auto first = pos(20);
  auto* manager = g_redex->get_position_pattern_switch_manager();
  manager->record_candidates(survivor.get(), {first.get()});
  ASSERT_NE(survivor->alt_id(), 0u);

  positions::mark_merged(survivor.get());

  EXPECT_TRUE(survivor->is_unreliable());
  EXPECT_EQ(survivor->alt_id(), 0u);
}

// Once a site has gone unrecorded the set can never be complete again, so a
// later nameable site must not resurrect one.
TEST_F(PositionMapTrailerTest,
       a_survivor_with_unnamed_sites_never_regains_a_set) {
  auto survivor = pos(10);
  auto generated = redex_generated();
  auto* manager = g_redex->get_position_pattern_switch_manager();
  manager->record_candidates(survivor.get(), {generated.get()});
  ASSERT_TRUE(survivor->is_unreliable());
  ASSERT_EQ(survivor->alt_id(), 0u);

  auto later = pos(20);
  manager->record_candidates(survivor.get(), {later.get()});

  EXPECT_EQ(survivor->alt_id(), 0u);
}

// `record_candidates` documents that a candidate "itself ambiguous with its own
// sites uncaptured" leaves the survivor uncaptured. A different-line uncaptured
// candidate must not instead be recorded as a member of a set the trailer then
// presents as complete.
TEST_F(PositionMapTrailerTest,
       an_uncaptured_candidate_on_another_line_leaves_the_survivor_uncaptured) {
  auto survivor = pos(10);
  auto uncaptured = pos(20);
  uncaptured->mark_unreliable();
  ASSERT_EQ(uncaptured->alt_id(), 0u);

  auto* manager = g_redex->get_position_pattern_switch_manager();
  manager->record_candidates(survivor.get(), {uncaptured.get()});

  EXPECT_TRUE(survivor->is_unreliable());
  EXPECT_EQ(survivor->alt_id(), 0u);
}

// The record a switch case points at, for the case selecting `pattern_id` in
// the cases following the count record at `count_index`.
size_t case_target(const std::vector<std::array<uint32_t, 5>>& positions,
                   const std::vector<std::string>& string_pool,
                   size_t count_index,
                   uint32_t pattern_id) {
  EXPECT_EQ(string_pool.at(positions.at(count_index)[1]), "count");
  for (size_t i = 1; i <= positions.at(count_index)[3]; ++i) {
    const auto& record = positions.at(count_index + i);
    EXPECT_EQ(string_pool.at(record[1]), "case");
    if (record[3] == pattern_id) {
      EXPECT_NE(record[4], 0u);
      return record[4] - 1;
    }
  }
  ADD_FAILURE() << "no case for pattern " << pattern_id;
  return 0;
}

const position_map::ProvenanceEntry* provenance_of(
    const std::vector<position_map::ProvenanceEntry>& entries,
    size_t record_index) {
  for (const auto& entry : entries) {
    if (entry.record_index == record_index) {
      return &entry;
    }
  }
  return nullptr;
}

// The lines of the candidate records an entry's alternate points at.
std::vector<uint32_t> candidate_lines(
    const std::vector<std::array<uint32_t, 5>>& positions,
    const position_map::ProvenanceEntry& entry) {
  std::vector<uint32_t> lines;
  const auto& count = positions.at(entry.alt_record_index);
  for (size_t i = 1; i <= count[3]; ++i) {
    const auto& record = positions.at(entry.alt_record_index + i);
    lines.push_back(positions.at(record[4] - 1)[3]);
  }
  return lines;
}

// The line map entry of a switch (a `Lredex/$Position;.switch` record), whose
// line the writer rewrote into the index of its count record.
size_t switch_count_index(const std::vector<std::array<uint32_t, 5>>& positions,
                          const std::vector<std::string>& string_pool) {
  for (const auto& record : positions) {
    if (string_pool.at(record[1]) == "switch") {
      return record[3];
    }
  }
  ADD_FAILURE() << "no switch record";
  return 0;
}

// An outlined call site whose line had a candidate set keeps that set: the
// switch case points at a record whose provenance entry names the candidates,
// not at a fresh copy merged with nothing captured.
TEST_F(PositionMapTrailerTest, an_outlined_slot_keeps_its_candidate_set) {
  auto path = map_path("outlined-leaf-set");
  auto* manager = g_redex->get_position_pattern_switch_manager();
  auto slot = pos(20);
  auto first = pos(21);
  auto second = pos(22);
  manager->record_candidates(slot.get(), {first.get(), second.get()});
  ASSERT_NE(slot->alt_id(), 0u);
  std::vector<DexPosition*> provenance;
  auto pattern_id = manager->make_pattern({slot.get()}, &provenance);
  auto other_slot = pos(30);
  auto other_pattern_id = manager->make_pattern({other_slot.get()});
  auto switch_id = manager->make_switch({
      {pattern_id, slot.get(), provenance.at(0)},
      {other_pattern_id, other_slot.get(), nullptr},
  });

  auto pattern_position = manager->make_pattern_position(pattern_id);
  auto other_pattern_position =
      manager->make_pattern_position(other_pattern_id);
  auto switch_position = manager->make_switch_position(switch_id);
  RealPositionMapper mapper(path);
  mapper.position_to_line(pattern_position.get());
  mapper.position_to_line(other_pattern_position.get());
  mapper.position_to_line(switch_position.get());
  mapper.write_map();

  auto bytes = read_file(path);
  auto parsed = parse(bytes);
  auto read = read_provenance(bytes);
  ASSERT_EQ(read.trailer.magic, position_map::kTrailerMagic);
  auto count_index = switch_count_index(parsed.positions, parsed.string_pool);
  auto target = case_target(parsed.positions, parsed.string_pool, count_index,
                            pattern_id);
  EXPECT_EQ(parsed.positions.at(target)[3], 20u);
  const auto* entry = provenance_of(read.entries, target);
  ASSERT_NE(entry, nullptr);
  ASSERT_NE(entry->alt_record_index, 0u);
  EXPECT_EQ(candidate_lines(parsed.positions, *entry),
            (std::vector<uint32_t>{21, 22}));

  auto other_target = case_target(parsed.positions, parsed.string_pool,
                                  count_index, other_pattern_id);
  EXPECT_EQ(provenance_of(read.entries, other_target), nullptr);
}

// Only the inlined caller frame of an outlined call site was ambiguous. The
// leaf still names one line, and the caller's set stays on the caller's record.
TEST_F(PositionMapTrailerTest,
       an_ambiguous_caller_of_an_outlined_slot_keeps_its_set_there) {
  auto path = map_path("outlined-caller-set");
  auto* manager = g_redex->get_position_pattern_switch_manager();
  auto caller = pos(100);
  auto other_caller = pos(110);
  manager->record_candidates(caller.get(), {other_caller.get()});
  ASSERT_NE(caller->alt_id(), 0u);
  auto slot = pos(20);
  slot->parent = caller.get();
  std::vector<DexPosition*> provenance;
  auto pattern_id = manager->make_pattern({slot.get()}, &provenance);
  ASSERT_NE(provenance.at(0), nullptr);
  auto other_slot = pos(30);
  auto other_pattern_id = manager->make_pattern({other_slot.get()});
  auto switch_id = manager->make_switch({
      {pattern_id, slot.get(), provenance.at(0)},
      {other_pattern_id, other_slot.get(), nullptr},
  });

  auto pattern_position = manager->make_pattern_position(pattern_id);
  auto other_pattern_position =
      manager->make_pattern_position(other_pattern_id);
  auto switch_position = manager->make_switch_position(switch_id);
  RealPositionMapper mapper(path);
  mapper.position_to_line(pattern_position.get());
  mapper.position_to_line(other_pattern_position.get());
  mapper.position_to_line(switch_position.get());
  mapper.write_map();

  auto bytes = read_file(path);
  auto parsed = parse(bytes);
  auto read = read_provenance(bytes);
  ASSERT_EQ(read.trailer.magic, position_map::kTrailerMagic);
  auto count_index = switch_count_index(parsed.positions, parsed.string_pool);
  auto leaf = case_target(parsed.positions, parsed.string_pool, count_index,
                          pattern_id);
  EXPECT_EQ(parsed.positions.at(leaf)[3], 20u);
  EXPECT_EQ(provenance_of(read.entries, leaf), nullptr);
  ASSERT_NE(parsed.positions.at(leaf)[4], 0u);
  auto caller_record = parsed.positions.at(leaf)[4] - 1;
  EXPECT_EQ(parsed.positions.at(caller_record)[3], 100u);
  const auto* entry = provenance_of(read.entries, caller_record);
  ASSERT_NE(entry, nullptr);
  ASSERT_NE(entry->alt_record_index, 0u);
  EXPECT_EQ(candidate_lines(parsed.positions, *entry),
            (std::vector<uint32_t>{110}));
}

// Two outlined methods share one pattern id because their call sites hold the
// same lines, but only one call site's line had a candidate set. Each switch
// keeps what its own call site knew.
TEST_F(PositionMapTrailerTest,
       call_sites_sharing_a_pattern_keep_their_own_provenance) {
  auto path = map_path("outlined-shared-pattern");
  auto* manager = g_redex->get_position_pattern_switch_manager();
  auto ambiguous_slot = pos(20);
  auto candidate = pos(21);
  manager->record_candidates(ambiguous_slot.get(), {candidate.get()});
  auto clean_slot = pos(20);
  std::vector<DexPosition*> ambiguous_provenance;
  auto pattern_id =
      manager->make_pattern({ambiguous_slot.get()}, &ambiguous_provenance);
  std::vector<DexPosition*> clean_provenance;
  ASSERT_EQ(manager->make_pattern({clean_slot.get()}, &clean_provenance),
            pattern_id);
  ASSERT_NE(ambiguous_provenance.at(0), nullptr);
  ASSERT_EQ(clean_provenance.at(0), nullptr);
  auto first_other = pos(30);
  auto first_other_id = manager->make_pattern({first_other.get()});
  auto second_other = pos(31);
  auto second_other_id = manager->make_pattern({second_other.get()});
  auto ambiguous_switch = manager->make_switch({
      {pattern_id, ambiguous_slot.get(), ambiguous_provenance.at(0)},
      {first_other_id, first_other.get(), nullptr},
  });
  auto clean_switch = manager->make_switch({
      {pattern_id, clean_slot.get(), clean_provenance.at(0)},
      {second_other_id, second_other.get(), nullptr},
  });

  std::vector<std::unique_ptr<DexPosition>> code_positions;
  for (auto id : {pattern_id, first_other_id, second_other_id}) {
    code_positions.push_back(manager->make_pattern_position(id));
  }
  auto ambiguous_switch_position =
      manager->make_switch_position(ambiguous_switch);
  auto clean_switch_position = manager->make_switch_position(clean_switch);
  RealPositionMapper mapper(path);
  for (auto& position : code_positions) {
    mapper.position_to_line(position.get());
  }
  auto ambiguous_index =
      mapper.position_to_line(ambiguous_switch_position.get()) - 1;
  auto clean_index = mapper.position_to_line(clean_switch_position.get()) - 1;
  mapper.write_map();

  auto bytes = read_file(path);
  auto parsed = parse(bytes);
  auto read = read_provenance(bytes);
  ASSERT_EQ(read.trailer.magic, position_map::kTrailerMagic);
  auto ambiguous_target =
      case_target(parsed.positions, parsed.string_pool,
                  parsed.positions.at(ambiguous_index)[3], pattern_id);
  auto clean_target =
      case_target(parsed.positions, parsed.string_pool,
                  parsed.positions.at(clean_index)[3], pattern_id);
  EXPECT_NE(ambiguous_target, clean_target);
  EXPECT_EQ(parsed.positions.at(ambiguous_target)[3], 20u);
  EXPECT_EQ(parsed.positions.at(clean_target)[3], 20u);
  const auto* entry = provenance_of(read.entries, ambiguous_target);
  ASSERT_NE(entry, nullptr);
  EXPECT_EQ(candidate_lines(parsed.positions, *entry),
            (std::vector<uint32_t>{21}));
  EXPECT_EQ(provenance_of(read.entries, clean_target), nullptr);
}

// Two occurrences of one outlined method share a slot. What the method knows
// about it is everything either occurrence knew, level by level.
TEST_F(PositionMapTrailerTest, joining_slot_provenance_unions_each_level) {
  auto* manager = g_redex->get_position_pattern_switch_manager();
  auto first = pos(20);
  auto first_candidate = pos(21);
  manager->record_candidates(first.get(), {first_candidate.get()});
  auto second = pos(20);
  auto second_candidate = pos(22);
  manager->record_candidates(second.get(), {second_candidate.get()});
  auto clean = pos(20);
  auto uncaptured = pos(20);
  uncaptured->mark_unreliable();
  std::vector<DexPosition*> provenance;
  for (auto* slot :
       {first.get(), second.get(), clean.get(), uncaptured.get()}) {
    std::vector<DexPosition*> slot_provenance;
    manager->make_pattern({slot}, &slot_provenance);
    provenance.push_back(slot_provenance.at(0));
  }

  auto* joined = manager->join_slot_provenance(provenance[0], provenance[1]);
  ASSERT_NE(joined, nullptr);
  ASSERT_NE(joined->alt_id(), 0u);
  EXPECT_EQ(member_lines(manager->get_alt_set(joined->alt_id())),
            (std::vector<uint32_t>{21, 22}));
  EXPECT_EQ(manager->join_slot_provenance(provenance[0], provenance[2]),
            provenance[0]);
  EXPECT_EQ(manager->join_slot_provenance(provenance[2], provenance[2]),
            nullptr);
  auto* absorbed = manager->join_slot_provenance(provenance[0], provenance[3]);
  ASSERT_NE(absorbed, nullptr);
  EXPECT_TRUE(absorbed->is_unreliable());
  EXPECT_EQ(absorbed->alt_id(), 0u);
}

std::unique_ptr<DexPosition> caller_pos(uint32_t line) {
  return std::make_unique<DexPosition>(
      DexString::make_string("LCaller;.run:()V"),
      DexString::make_string("Caller.java"),
      line);
}

// A victim names the survivor's place, but its inlined caller is merged with
// sites nobody captured. The survivor's caller is no longer exact for the code
// it now governs, so the survivor's place re-enters its set carrying the
// uncaptured caller.
TEST_F(PositionMapTrailerTest,
       a_copy_of_the_survivors_place_with_an_uncaptured_caller_marks_it) {
  auto* manager = g_redex->get_position_pattern_switch_manager();
  auto survivor_caller = caller_pos(100);
  auto victim_caller = caller_pos(100);
  victim_caller->mark_unreliable();
  auto survivor = pos(20);
  survivor->parent = survivor_caller.get();
  auto victim = pos(20);
  victim->parent = victim_caller.get();
  ASSERT_FALSE(positions::same_source_claim(survivor.get(), victim.get()));

  EXPECT_EQ(manager->record_candidates(survivor.get(), {victim.get()}),
            positions::FidelityChange::BecameUnreliable);

  ASSERT_TRUE(survivor->is_unreliable());
  ASSERT_NE(survivor->alt_id(), 0u);
  const auto& alt_set = manager->get_alt_set(survivor->alt_id());
  ASSERT_EQ(alt_set.members.size(), 1u);
  const auto* member = alt_set.members[0];
  EXPECT_EQ(*member, *survivor);
  EXPECT_FALSE(member->is_unreliable());
  EXPECT_TRUE(member->parent->is_unreliable());
  EXPECT_EQ(member->parent->alt_id(), 0u);
  EXPECT_FALSE(survivor_caller->is_unreliable());
}

// The same with a captured set on the victim's caller: Caller.java:107 is kept
// on the caller level of the survivor's place.
TEST_F(PositionMapTrailerTest,
       a_copy_of_the_survivors_place_keeps_its_callers_set) {
  auto* manager = g_redex->get_position_pattern_switch_manager();
  auto survivor_caller = caller_pos(100);
  auto victim_caller = caller_pos(100);
  auto caller_elsewhere = caller_pos(107);
  manager->record_candidates(victim_caller.get(), {caller_elsewhere.get()});
  ASSERT_NE(victim_caller->alt_id(), 0u);
  auto survivor = pos(20);
  survivor->parent = survivor_caller.get();
  auto victim = pos(20);
  victim->parent = victim_caller.get();
  ASSERT_FALSE(positions::same_source_claim(survivor.get(), victim.get()));

  manager->record_candidates(survivor.get(), {victim.get()});

  ASSERT_TRUE(survivor->is_unreliable());
  ASSERT_NE(survivor->alt_id(), 0u);
  const auto& alt_set = manager->get_alt_set(survivor->alt_id());
  ASSERT_EQ(alt_set.members.size(), 1u);
  const auto* member = alt_set.members[0];
  EXPECT_EQ(*member, *survivor);
  ASSERT_NE(member->parent->alt_id(), 0u);
  EXPECT_EQ(member_lines(manager->get_alt_set(member->parent->alt_id())),
            (std::vector<uint32_t>{107}));

  // What the survivor's own caller already says is not repeated.
  auto merged_survivor_caller = caller_pos(100);
  manager->record_candidates(merged_survivor_caller.get(),
                             {caller_elsewhere.get()});
  auto settled = pos(20);
  settled->parent = merged_survivor_caller.get();
  EXPECT_EQ(manager->record_candidates(settled.get(), {victim.get()}),
            positions::FidelityChange::Unchanged);
  EXPECT_FALSE(settled->is_unreliable());
}

// Two candidates name one place and differ only in their caller's provenance.
// The one member kept for that place joins both callers: here the second
// caller's set {Caller.java:107}.
TEST_F(PositionMapTrailerTest,
       members_naming_one_place_join_their_callers_provenance) {
  auto* manager = g_redex->get_position_pattern_switch_manager();
  auto clean_caller = caller_pos(100);
  auto merged_caller = caller_pos(100);
  auto caller_elsewhere = caller_pos(107);
  manager->record_candidates(merged_caller.get(), {caller_elsewhere.get()});
  auto first = pos(30);
  first->parent = clean_caller.get();
  auto second = pos(30);
  second->parent = merged_caller.get();

  for (const auto& order :
       {std::vector<const DexPosition*>{first.get(), second.get()},
        std::vector<const DexPosition*>{second.get(), first.get()}}) {
    auto survivor = pos(10);
    manager->record_candidates(survivor.get(), order);

    ASSERT_NE(survivor->alt_id(), 0u);
    const auto& alt_set = manager->get_alt_set(survivor->alt_id());
    ASSERT_EQ(alt_set.members.size(), 1u);
    const auto* member = alt_set.members[0];
    ASSERT_NE(member->parent, nullptr);
    ASSERT_NE(member->parent->alt_id(), 0u);
    EXPECT_EQ(member_lines(manager->get_alt_set(member->parent->alt_id())),
              (std::vector<uint32_t>{107}));
  }
}

// A pattern position governs the call of an outlined method, and a throw there
// comes from inside the outlined method, at any of its slots. The call site
// does not say which, so the pattern position names no source.
TEST_F(PositionMapTrailerTest, a_pattern_candidate_is_uncaptured) {
  auto* manager = g_redex->get_position_pattern_switch_manager();
  auto first_slot = pos(40);
  auto last_slot = pos(41);
  auto pattern_id = manager->make_pattern({first_slot.get(), last_slot.get()});
  auto empty_pattern_id = manager->make_pattern({});
  auto caller = caller_pos(200);

  for (auto id : {pattern_id, empty_pattern_id}) {
    auto pattern_position = manager->make_pattern_position(id);
    pattern_position->parent = caller.get();
    auto survivor = pos(10);
    manager->record_candidates(survivor.get(), {pattern_position.get()});
    EXPECT_TRUE(survivor->is_unreliable());
    EXPECT_EQ(survivor->alt_id(), 0u);
  }
}

} // namespace
