/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include <unistd.h>

#include <cstdio>
#include <fstream>
#include <string>
#include <vector>

#include "DexPosition.h"
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

} // namespace
