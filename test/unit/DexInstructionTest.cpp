/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "DexCallSite.h"
#include "DexInstruction.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"
#include "Show.h"

class DexInstructionTest : public RedexTest {};

TEST_F(DexInstructionTest, test_encode_fill_array_data_payload_8) {
  std::vector<int8_t> vec{1, 2, 3, 4, 5};
  auto payload = encode_fill_array_data_payload(vec);
  const uint16_t* udata16 = payload->data();

  // data32 removed the 16 bit width field
  [[maybe_unused]] const int8_t* data8 = (const int8_t*)(payload->data() + 3);

  // DexOpcodeData constructor ignored the FOPCODE_FILL_ARRAY
  EXPECT_EQ(udata16[0], 1); // width

  auto result = get_fill_array_data_payload<int8_t>(payload.get());
  EXPECT_EQ(result.size(), 5);
  EXPECT_EQ(result[0], 1);
  EXPECT_EQ(result[1], 2);
  EXPECT_EQ(result[2], 3);
  EXPECT_EQ(result[3], 4);
  EXPECT_EQ(result[4], 5);
}

TEST_F(DexInstructionTest, test_encode_fill_array_data_payload_16) {
  std::vector<int16_t> vec{1, 2, 3, 4, 5};
  auto payload = encode_fill_array_data_payload(vec);
  const uint16_t* udata16 = payload->data();
  [[maybe_unused]] const int16_t* data16 = (const int16_t*)payload->data() + 3;

  // DexOpcodeData constructor ignored the FOPCODE_FILL_ARRAY
  EXPECT_EQ(udata16[0], 2); // width

  auto result = get_fill_array_data_payload<uint16_t>(payload.get());
  EXPECT_EQ(result.size(), 5);
  EXPECT_EQ(result[0], 1);
  EXPECT_EQ(result[1], 2);
  EXPECT_EQ(result[2], 3);
  EXPECT_EQ(result[3], 4);
  EXPECT_EQ(result[4], 5);
}

TEST_F(DexInstructionTest, test_encode_fill_array_data_payload_32) {
  std::vector<int32_t> vec{1, 2, 3, 4, 5};
  auto payload = encode_fill_array_data_payload(vec);
  const uint16_t* udata16 = payload->data();

  // data32 removed the 16 bit width field
  [[maybe_unused]] const int32_t* data32 =
      (const int32_t*)(payload->data() + 1);

  // DexOpcodeData constructor ignored the FOPCODE_FILL_ARRAY
  EXPECT_EQ(udata16[0], 4); // width

  auto result = get_fill_array_data_payload<int32_t>(payload.get());
  EXPECT_EQ(result.size(), 5);
  EXPECT_EQ(result[0], 1);
  EXPECT_EQ(result[1], 2);
  EXPECT_EQ(result[2], 3);
  EXPECT_EQ(result[3], 4);
  EXPECT_EQ(result[4], 5);
}

// `invoke-custom` names a call site, not a method.
TEST_F(DexInstructionTest, invoke_custom_names_a_call_site) {
  for (auto op : {DOPCODE_INVOKE_CUSTOM, DOPCODE_INVOKE_CUSTOM_RANGE}) {
    std::unique_ptr<DexInstruction> insn(DexInstruction::make_instruction(op));
    EXPECT_NE(dynamic_cast<DexOpcodeCallSite*>(insn.get()), nullptr);
  }

  auto* callsite = redex::make_callsite("run", "()V");
  DexOpcodeCallSite insn(DOPCODE_INVOKE_CUSTOM, callsite);
  EXPECT_EQ(show(&insn), "invoke-custom " + show(callsite));
}
