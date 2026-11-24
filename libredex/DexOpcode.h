/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <cstdint>
#include <string>

#include "DexOpcodeDefs.h"

std::string show(DexOpcode);

using bit_width_t = uint8_t;

namespace dex_opcode {

// max number of register args supported by non-range opcodes
const size_t NON_RANGE_MAX = 5;

OpcodeFormat format(DexOpcode opcode);

bool has_dest(DexOpcode);
// we can't tell the srcs size from the opcode alone -- format 35c opcodes
// encode that separately. So this just returns the minimum.
unsigned min_srcs_size(DexOpcode);

bit_width_t dest_bit_width(DexOpcode);

// the number of bits an opcode has available to encode a given register
bit_width_t src_bit_width(DexOpcode, uint16_t i);

// if a source register is used as a destination too
bool dest_is_src(DexOpcode);
bool has_literal(DexOpcode);
bool has_offset(DexOpcode);
bool has_range(DexOpcode);

// If an opcode has a variable number of register operands
inline bool has_arg_word_count(DexOpcode op) {
  auto fmt = format(op);
  return fmt == FMT_f35c || fmt == FMT_f45cc || fmt == FMT_f57c;
}

bool is_commutative(DexOpcode op);

bool is_branch(DexOpcode);

bool is_conditional_branch(DexOpcode);

inline bool is_switch(DexOpcode op) {
  return op == DOPCODE_PACKED_SWITCH || op == DOPCODE_SPARSE_SWITCH;
}

bool is_goto(DexOpcode);

bool is_move(DexOpcode);

DexOpcode invert_conditional_branch(DexOpcode op);

inline bool is_invoke_range(DexOpcode op) {
  return op >= DOPCODE_INVOKE_VIRTUAL_RANGE &&
         op <= DOPCODE_INVOKE_INTERFACE_RANGE;
}

inline bool is_invoke(DexOpcode op) {
  return op >= DOPCODE_INVOKE_VIRTUAL && op <= DOPCODE_INVOKE_INTERFACE_RANGE;
}

inline bool is_fopcode(DexOpcode op) {
  return op == FOPCODE_PACKED_SWITCH || op == FOPCODE_SPARSE_SWITCH ||
         op == FOPCODE_FILLED_ARRAY;
}

inline bool is_iget(DexOpcode op) {
  return op >= DOPCODE_IGET && op <= DOPCODE_IGET_SHORT;
}

inline bool is_iput(DexOpcode op) {
  return op >= DOPCODE_IPUT && op <= DOPCODE_IPUT_SHORT;
}

inline bool is_sput(DexOpcode op) {
  return op >= DOPCODE_SPUT && op <= DOPCODE_SPUT_SHORT;
}

inline bool is_sget(DexOpcode op) {
  return op >= DOPCODE_SGET && op <= DOPCODE_SGET_SHORT;
}

inline bool is_literal_const(DexOpcode op) {
  return op >= DOPCODE_CONST_4 && op <= DOPCODE_CONST_WIDE_HIGH16;
}

inline bool is_return(DexOpcode op) {
  return op >= DOPCODE_RETURN_VOID && op <= DOPCODE_RETURN_OBJECT;
}

} // namespace dex_opcode
