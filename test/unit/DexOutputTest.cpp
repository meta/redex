/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "DexOutput.h"
#include "Creators.h"
#include "IODIMetadata.h"
#include "IODIPlan.h"
#include "RedexTest.h"
#include "TypeUtil.h"
#include <cstring>
#include <gtest/gtest.h>
#include <json/reader.h>
#include <json/value.h>

class IODIMetadataTest : public RedexTest {};

TEST_F(IODIMetadataTest, SerializationUsesMethodIdentityNotInsertionOrder) {
  ClassCreator creator(DexType::make_type("LOrderedIodi;"));
  creator.set_super(type::java_lang_Object());
  std::vector<DexMethod*> methods;
  for (size_t i = 0; i < 16; ++i) {
    auto name = std::string("m") + (i < 10 ? "0" : "") + std::to_string(i);
    auto* method = DexMethod::make_method("LOrderedIodi;." + name + ":()V")
                       ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
    creator.add_method(method);
    methods.push_back(method);
  }
  creator.create();
  ClassCreator second(DexType::make_type("LSecondOrderedIodi;"));
  second.set_super(type::java_lang_Object());
  auto* other = DexMethod::make_method("LSecondOrderedIodi;.a:()V")
                    ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  second.add_method(other);
  second.create();
  std::vector<std::pair<std::string, uint64_t>> expected;
  for (size_t i = 0; i < methods.size(); ++i) {
    auto name =
        std::string("OrderedIodi.m") + (i < 10 ? "0" : "") + std::to_string(i);
    if (i % 3 != 0) {
      name += "@" + std::to_string(i % 3);
    }
    expected.emplace_back(name, i + 1);
  }
  methods.push_back(other);
  expected.emplace_back("SecondOrderedIodi.a@1", methods.size());
  std::string first;
  for (bool reverse : {false, true}) {
    IODIMetadata metadata;
    UnorderedMap<DexMethod*, uint64_t> ids;
    for (size_t i = 0; i < methods.size(); ++i) {
      const size_t index = reverse ? methods.size() - i - 1 : i;
      metadata.set_iodi_layer(methods[index], index % 3);
      ids.emplace(methods[index], index + 1);
    }
    std::ostringstream stream;
    metadata.write(stream, ids);
    const auto bytes = stream.str();
    if (!reverse) {
      first = bytes;
    } else {
      EXPECT_EQ(first, bytes);
    }
    ASSERT_GE(bytes.size(), 16u);
    uint32_t count;
    std::memcpy(&count, bytes.data() + 8, sizeof(count));
    ASSERT_EQ(count, expected.size());
    size_t offset = 16;
    std::vector<std::pair<std::string, uint64_t>> actual;
    for (uint32_t i = 0; i < count; ++i) {
      ASSERT_GE(bytes.size() - offset, 10u);
      uint16_t length;
      uint64_t id;
      std::memcpy(&length, bytes.data() + offset, sizeof(length));
      std::memcpy(&id, bytes.data() + offset + 2, sizeof(id));
      offset += 10;
      ASSERT_GE(bytes.size() - offset, length);
      actual.emplace_back(bytes.substr(offset, length), id);
      offset += length;
    }
    EXPECT_EQ(actual, expected);
    EXPECT_EQ(offset, bytes.size());
  }
}

TEST(DexOutput, checkMethodInstructionSizeLimit) {

  Json::Value json_cfg;
  std::istringstream temp_json(
      "{\"redex\":{\"passes\":[]}, \"instruction_size_bitwidth_limit\": 0}");

  temp_json >> json_cfg;
  json_cfg["instruction_size_bitwidth_limit"] = 16;
  ConfigFiles conf(json_cfg);
  bool described = false;
  EXPECT_NO_THROW(DexOutput::check_method_instruction_size_limit(
      conf, 65536, [&described]() {
        described = true;
        return std::string("method");
      }));
  EXPECT_FALSE(described);
  EXPECT_THROW(DexOutput::check_method_instruction_size_limit(
                   conf,
                   65537,
                   [&described]() {
                     described = true;
                     return std::string("method");
                   }),
               RedexException);
  EXPECT_TRUE(described);
}

TEST(DexOutput, rejectsNegativeSizeWithoutConfiguredLimit) {
  Json::Value json_cfg;
  std::istringstream temp_json(
      "{\"redex\":{\"passes\":[]}, \"instruction_size_bitwidth_limit\": 0}");
  temp_json >> json_cfg;
  ConfigFiles conf(json_cfg);

  bool described = false;
  EXPECT_THROW(DexOutput::check_method_instruction_size_limit(
                   conf,
                   -1,
                   [&described]() {
                     described = true;
                     return std::string("method");
                   }),
               RedexException);
  EXPECT_TRUE(described);
}

namespace {

// With no parameters and a zero start line a program encodes as two uleb128
// header bytes, one byte per line entry, and DBG_END_SEQUENCE.
constexpr size_t kProgramOverhead = 3;

iodi::Plan plan_for(const std::vector<uint32_t>& method_sizes,
                    const std::vector<uint64_t>& normal_debug_sizes,
                    size_t max_inflated_size = iodi::kMaxInflatedSize) {
  return iodi::plan_programs(method_sizes, normal_debug_sizes,
                             /*param_size=*/0,
                             /*line_start=*/0,
                             /*requires_iodi_programs=*/true,
                             max_inflated_size);
}

// Checks invariants required by the emitter.
void verify_plan(const iodi::Plan& plan,
                 const std::vector<uint32_t>& method_sizes,
                 size_t max_inflated_size = iodi::kMaxInflatedSize) {
  ASSERT_EQ(plan.program_of_method.size(), method_sizes.size());
  ASSERT_LE(plan.first_iodi_index, method_sizes.size());

  std::vector<size_t> users(plan.programs.size(), 0);
  for (size_t i = 0; i < method_sizes.size(); ++i) {
    const auto program_index = plan.program_of_method[i];
    if (i < plan.first_iodi_index || plan.programs.empty()) {
      EXPECT_EQ(program_index, iodi::Plan::kNoProgram) << "method " << i;
      continue;
    }
    ASSERT_LT(program_index, plan.programs.size());
    // A program maps the instruction offsets [0, size) to lines, so it has to
    // be at least as long as every method it serves.
    EXPECT_GE(plan.programs[program_index].size, method_sizes[i])
        << "method " << i;
    users[program_index]++;
  }

  size_t footprint = 0;
  for (size_t i = 0; i < plan.programs.size(); ++i) {
    const auto& program = plan.programs[i];
    // A program nothing points at is dead weight in the dex.
    EXPECT_GT(users[i], 0u) << "program " << i;
    // Inflation is accounted against the methods actually assigned.
    EXPECT_EQ(users[i], program.user_count) << "program " << i;
    const size_t program_footprint = size_t{program.size} * program.user_count;
    // A method above the per-program bound cannot be made to fit, so it gets
    // a program to itself.
    EXPECT_TRUE(program_footprint <= iodi::kMaxBucketInflatedSize ||
                program.user_count == 1)
        << "program " << i;
    footprint += program_footprint;
  }
  EXPECT_EQ(footprint, plan.total_inflated_footprint);
  EXPECT_LE(footprint, max_inflated_size);
}

} // namespace

TEST(IODIPlan, SplitsMethodsThatDoNotShareAProgram) {
  // 5000 * 2 exceeds the per-program bound, so the smaller method cannot be
  // served by the larger method's program.
  const std::vector<uint32_t> method_sizes{5000, 4000};
  const std::vector<uint64_t> normal_debug_sizes{20000, 20000};

  auto plan = plan_for(method_sizes, normal_debug_sizes);

  EXPECT_EQ(plan.first_iodi_index, 0);
  ASSERT_EQ(plan.programs.size(), 2);
  EXPECT_EQ(plan.programs[0].size, 5000);
  EXPECT_EQ(plan.programs[0].user_count, 1);
  EXPECT_EQ(plan.programs[1].size, 4000);
  EXPECT_EQ(plan.programs[1].user_count, 1);
  EXPECT_EQ(plan.program_of_method[0], 0);
  EXPECT_EQ(plan.program_of_method[1], 1);
  EXPECT_EQ(plan.total_inflated_footprint, 9000);
  EXPECT_EQ(plan.total_debug_size, 9000 + 2 * kProgramOverhead);
  verify_plan(plan, method_sizes);
}

TEST(IODIPlan, KeepsEqualSizedProgramsIndependentlyAddressable) {
  // 4000 * 3 exceeds the per-program bound, so two programs of equal size are
  // needed. Each serves its own methods.
  const std::vector<uint32_t> method_sizes{4000, 4000, 4000};
  const std::vector<uint64_t> normal_debug_sizes{20000, 20000, 20000};

  auto plan = plan_for(method_sizes, normal_debug_sizes);

  EXPECT_EQ(plan.first_iodi_index, 0);
  ASSERT_EQ(plan.programs.size(), 2);
  EXPECT_EQ(plan.programs[0].size, 4000);
  EXPECT_EQ(plan.programs[0].user_count, 2);
  EXPECT_EQ(plan.programs[1].size, 4000);
  EXPECT_EQ(plan.programs[1].user_count, 1);
  EXPECT_EQ(plan.program_of_method[0], 0);
  EXPECT_EQ(plan.program_of_method[1], 0);
  EXPECT_EQ(plan.program_of_method[2], 1);
  EXPECT_EQ(plan.total_inflated_footprint, 12000);
  verify_plan(plan, method_sizes);
}

TEST(IODIPlan, GivesAnOversizedMethodItsOwnProgram) {
  const std::vector<uint32_t> method_sizes{
      static_cast<uint32_t>(iodi::kMaxBucketInflatedSize) + 1,
      static_cast<uint32_t>(iodi::kMaxBucketInflatedSize) + 1};
  const std::vector<uint64_t> normal_debug_sizes{100000, 100000};

  auto plan = plan_for(method_sizes, normal_debug_sizes);

  EXPECT_EQ(plan.first_iodi_index, 0);
  ASSERT_EQ(plan.programs.size(), 2);
  EXPECT_EQ(plan.programs[0].user_count, 1);
  EXPECT_EQ(plan.programs[1].user_count, 1);
  verify_plan(plan, method_sizes);
}

TEST(IODIPlan, HandsEqualSizedTrailingUsersToTheNextProgram) {
  // Greedy packing gives the 3000-byte program two users, one of which is a
  // 2000-byte method that the 2000-byte program serves just as well. Both
  // groupings emit the same two program sizes, so they cost the same bytes,
  // but the greedy one inflates that method against 3000 instead of 2000.
  const std::vector<uint32_t> method_sizes{3000, 2000, 2000};
  const std::vector<uint64_t> normal_debug_sizes{20000, 20000, 20000};

  auto plan = plan_for(method_sizes, normal_debug_sizes);

  EXPECT_EQ(plan.first_iodi_index, 0);
  ASSERT_EQ(plan.programs.size(), 2);
  EXPECT_EQ(plan.programs[0].size, 3000);
  EXPECT_EQ(plan.programs[0].user_count, 1);
  EXPECT_EQ(plan.programs[1].size, 2000);
  EXPECT_EQ(plan.programs[1].user_count, 2);
  EXPECT_EQ(plan.total_inflated_footprint, 7000);
  // Greedy packing would have cost the same bytes for 8000 entries.
  EXPECT_EQ(plan.total_debug_size, 3000 + 2000 + 2 * kProgramOverhead);
  verify_plan(plan, method_sizes);
}

TEST(IODIPlan, KeepsAMethodItCanServeWithinTheAggregateLimit) {
  // 255 oversized methods leave 7,937 entries of aggregate budget. Greedy
  // grouping uses 8,000 for the tail; rebalancing uses 7,000 at the same
  // encoded size, so no method needs exclusion.
  std::vector<uint32_t> method_sizes(
      255, static_cast<uint32_t>(iodi::kMaxBucketInflatedSize) + 1);
  method_sizes.insert(method_sizes.end(), {3000, 2000, 2000});
  const std::vector<uint64_t> normal_debug_sizes(method_sizes.size(), 100000);

  auto plan = plan_for(method_sizes, normal_debug_sizes);

  EXPECT_EQ(plan.first_iodi_index, 0);
  ASSERT_EQ(plan.programs.size(), 257);
  EXPECT_EQ(plan.programs[255].size, 3000);
  EXPECT_EQ(plan.programs[255].user_count, 1);
  EXPECT_EQ(plan.programs[256].size, 2000);
  EXPECT_EQ(plan.programs[256].user_count, 2);
  EXPECT_EQ(plan.total_inflated_footprint, 255 * 8193 + 7000);
  EXPECT_EQ(
      plan.total_debug_size,
      255 * (8193 + kProgramOverhead) + 3000 + 2000 + 2 * kProgramOverhead);
  verify_plan(plan, method_sizes);
}

TEST(IODIPlan, RejectsSuffixesThatExceedTheAggregateLimit) {
  // Dropping the first method lets the second absorb both remaining methods,
  // which raises the footprint from 6544 to 7362. The cheaper suffix is
  // therefore the unsafe one, and the plan has to keep the full range.
  const std::vector<uint32_t> method_sizes{2863, 2454, 409, 409};
  const std::vector<uint64_t> normal_debug_sizes{1, 9000, 9000, 9000};
  constexpr size_t kMaxInflatedSize = 7000;

  auto plan = plan_for(method_sizes, normal_debug_sizes, kMaxInflatedSize);

  EXPECT_EQ(plan.first_iodi_index, 0);
  ASSERT_EQ(plan.programs.size(), 2);
  EXPECT_EQ(plan.programs[0].size, 2863);
  EXPECT_EQ(plan.programs[0].user_count, 2);
  EXPECT_EQ(plan.programs[1].size, 409);
  EXPECT_EQ(plan.programs[1].user_count, 2);
  EXPECT_EQ(plan.total_inflated_footprint, 6544);
  verify_plan(plan, method_sizes, kMaxInflatedSize);
}

TEST(IODIPlan, ExcludesMethodsThatCostMoreThanTheirDebugInfo) {
  const std::vector<uint32_t> method_sizes{8000, 100, 100, 100};
  const std::vector<uint64_t> normal_debug_sizes{5, 5000, 5000, 5000};

  auto plan = plan_for(method_sizes, normal_debug_sizes);

  EXPECT_EQ(plan.first_iodi_index, 1);
  ASSERT_EQ(plan.programs.size(), 1);
  EXPECT_EQ(plan.programs[0].size, 100);
  EXPECT_EQ(plan.programs[0].user_count, 3);
  EXPECT_EQ(plan.total_inflated_footprint, 300);
  EXPECT_EQ(plan.total_debug_size, 5 + 100 + kProgramOverhead);
  verify_plan(plan, method_sizes);
}

TEST(IODIPlan, OptsOutWhenProgramsCostMoreThanNormalDebugInfo) {
  const std::vector<uint32_t> method_sizes{100, 100};
  const std::vector<uint64_t> normal_debug_sizes{5, 5};

  auto plan = plan_for(method_sizes, normal_debug_sizes);

  EXPECT_EQ(plan.first_iodi_index, 2);
  EXPECT_TRUE(plan.programs.empty());
  EXPECT_EQ(plan.total_inflated_footprint, 0);
  EXPECT_EQ(plan.total_debug_size, 10);
  verify_plan(plan, method_sizes);
}

TEST(IODIPlan, CostsTheEncodedProgramHeader) {
  // A layered program starts at line 1 << 28, whose uleb128 takes 5 bytes, and
  // carries one byte for each of the two absent parameter names.
  const std::vector<uint32_t> method_sizes{100, 100};
  const std::vector<uint64_t> normal_debug_sizes{20000, 20000};

  auto plan = iodi::plan_programs(method_sizes, normal_debug_sizes,
                                  /*param_size=*/2,
                                  /*line_start=*/1u << 28,
                                  /*requires_iodi_programs=*/true);

  ASSERT_EQ(plan.programs.size(), 1);
  EXPECT_EQ(plan.programs[0].encoded_size, 5 + 1 + 2 + 100 + 1);
  EXPECT_EQ(plan.total_debug_size, plan.programs[0].encoded_size);
  verify_plan(plan, method_sizes);
}

TEST(IODIPlan, DoesNotFilterWhenNoProgramIsEmitted) {
  const std::vector<uint32_t> method_sizes{
      static_cast<uint32_t>(iodi::kMaxInflatedSize) + 1};
  const std::vector<uint64_t> normal_debug_sizes{7};

  auto plan = iodi::plan_programs(method_sizes, normal_debug_sizes,
                                  /*param_size=*/0,
                                  /*line_start=*/0,
                                  /*requires_iodi_programs=*/false);

  EXPECT_EQ(plan.first_iodi_index, 0);
  EXPECT_TRUE(plan.programs.empty());
  EXPECT_EQ(plan.total_inflated_footprint, 0);
  EXPECT_EQ(plan.total_debug_size, 0);
  verify_plan(plan, method_sizes);
}

TEST(IODIPlan, ExhaustedCandidatesFallBackToNormalDebugInfo) {
  const std::vector<uint32_t> method_sizes{
      static_cast<uint32_t>(iodi::kMaxInflatedSize) + 1};
  const std::vector<uint64_t> normal_debug_sizes{7};

  auto plan = plan_for(method_sizes, normal_debug_sizes);

  EXPECT_EQ(plan.first_iodi_index, 1);
  EXPECT_TRUE(plan.programs.empty());
  EXPECT_EQ(plan.total_debug_size, 7);
  verify_plan(plan, method_sizes);
}
