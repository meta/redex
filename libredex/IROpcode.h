/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <cstdint>
#include <iosfwd>
#include <optional>
#include <string>

#include "Debug.h"

class DexField;
class DexMethod;
class DexMethodRef;
class DexType;

enum DexOpcode : uint16_t;

namespace opcode {

enum class Ref {
  None,
  Literal,
  String,
  Type,
  Field,
  Method,
  CallSite,
  MethodHandle,
  Data,
  Proto,
  // A DexSignaturePolymorphicRef: a method and the prototype of the call site.
  SignaturePolymorphic,
};

} // namespace opcode

enum IROpcode : uint16_t {
#define OP(uc, lc, code, ...) OPCODE_##uc,
#define IOP(uc, lc, code, ...) IOPCODE_##uc,
#define OPRANGE(...)
#include "IROpcodes.def"
};
// clang-format on

std::string show(IROpcode);

std::ostream& operator<<(std::ostream& os, const IROpcode& op);

using bit_width_t = uint8_t;

namespace opcode {

// clang-format off
constexpr inline Ref ref(IROpcode opcode) {
  switch (opcode) {
#define OP(uc, lc, ref, ...) \
  case OPCODE_##uc:          \
    return ref;
#define IOP(uc, lc, ref, ...) \
  case IOPCODE_##uc:          \
    return ref;
#define OPRANGE(...)
#include "IROpcodes.def"
  }
  not_reached_log("Unexpected opcode 0x%x", opcode);
}
// clang-format on

/*
 * 2addr and non-2addr DexOpcode pairs will get mapped to the same IROpcode.
 * range and non-range DexOpcode pairs will get mapped to the same IROpcode.
 * goto, goto/16, and goto/32 will get mapped to the same IROpcode.
 * move, move/from16, and move/16 will get mapped to the same IROpcode. Same
 * for the move-object and move-wide opcode families.
 * const/4, const/16, and const will all get mapped to the same IROpcode. Same
 * for the const-wide opcode family.
 * All other DexOpcodes have a 1-1 mapping with an IROpcode.
 */
std::optional<IROpcode> from_dex_opcode(DexOpcode);

/*
 * Only non-internal IROpcodes are valid inputs to this function.
 *
 * This function is roughly the inverse of `from_dex_opcode`. When there are
 * are multiple DexOpcodes that map to a single IROpcode, we pick one of them
 * to return here.
 */
DexOpcode to_dex_opcode(IROpcode);

// if an IROpcode can be translated to a DexOpcode of /range format
bool has_range_form(IROpcode);

bool has_variable_srcs_size(IROpcode op);

/*
 * These instructions have observable side effects so must always be considered
 * live, regardless of whether their output is consumed by another instruction.
 */
bool has_side_effects(IROpcode opc);

bool is_move_result_any(IROpcode op);

bool is_commutative(IROpcode opcode);

bool is_binop64(IROpcode op);

/**
 * Whether the opcode can raise an exception that transfers control to a catch
 * handler. Update according to
 * https://cs.android.com/android/platform/superproject/main/+/main:art/libdexfile/dex/dex_instruction_list.h
 *
 * NOTE: this is false for OPCODE_THROW itself (that is covered by `can_throw`)
 * AND for `return-*` opcodes. So `may_throw` is NOT a test for "ends a block /
 * transfers control": both `throw` and `return` are block terminators yet
 * `may_throw` is false for them. To test "no instruction may follow in this
 * block" use `opcode::is_terminal` (branch/throw/return); to test "can raise to
 * a handler" use `can_throw` (= `may_throw || is_throw`).
 */
bool may_throw(IROpcode);

/**
 * Creates predicates from definitions in IROpcode.defs, e.g. with the
 * following signatures:
 *
 *   inline bool is_a_move(IROpcode op);  // OPRANGE(a_move, ...)
 *   inline bool is_move(IROpcode op);    // OP(MOVE, move, ...)
 *   inline bool is_load_param(IROpcode); // IOP(LOAD_PARAM, load_param, ...)
 */
#define OPRANGE(NAME, FST, LST)                  \
  constexpr inline bool is_##NAME(IROpcode op) { \
    return (FST) <= op && op <= (LST);           \
  }
#define OP(UC, LC, ...) \
  constexpr inline bool is_##LC(IROpcode op) { return op == OPCODE_##UC; }
#define IOP(UC, LC, ...) \
  constexpr inline bool is_##LC(IROpcode op) { return op == IOPCODE_##UC; }
#include "IROpcodes.def"

/**
 * Should represent value in
 * https://cs.android.com/android/platform/superproject/main/+/main:art/libdexfile/dex/dex_instruction_list.h
 */
inline bool can_throw(IROpcode op) { return may_throw(op) || is_throw(op); }

constexpr inline bool writes_result_register(IROpcode op) {
  return is_an_invoke(op) || is_filled_new_array(op);
}

constexpr inline bool is_branch(IROpcode op) {
  switch (op) {
  case OPCODE_SWITCH:
  case OPCODE_IF_EQ:
  case OPCODE_IF_NE:
  case OPCODE_IF_LT:
  case OPCODE_IF_GE:
  case OPCODE_IF_GT:
  case OPCODE_IF_LE:
  case OPCODE_IF_EQZ:
  case OPCODE_IF_NEZ:
  case OPCODE_IF_LTZ:
  case OPCODE_IF_GEZ:
  case OPCODE_IF_GTZ:
  case OPCODE_IF_LEZ:
  case OPCODE_GOTO:
    return true;
  default:
    return false;
  }
}

// True for the hard block terminators -- opcodes after which no instruction
// may follow in a block (a branch, a `throw`, or a `return`). This is the
// predicate enforced by ControlFlowGraph::insert. Note it deliberately does
// NOT include `may_throw` instructions: those are not terminators (inserting
// after one splits the block and copies its throw edges).
constexpr bool is_terminal(IROpcode op) {
  return is_branch(op) || is_throw(op) || is_a_return(op);
}

constexpr inline bool is_div_int_or_long(IROpcode op) {
  return op == OPCODE_DIV_INT || op == OPCODE_DIV_LONG;
}

constexpr inline bool is_rem_int_or_long(IROpcode op) {
  return op == OPCODE_REM_INT || op == OPCODE_REM_LONG;
}

DexOpcode range_version(IROpcode);

IROpcode load_param_to_move(IROpcode);

IROpcode iget_to_move(IROpcode);

IROpcode iput_to_move(IROpcode);

IROpcode invert_conditional_branch(IROpcode op);

IROpcode move_result_pseudo_for_iget(IROpcode op);

IROpcode move_result_pseudo_for_sget(IROpcode op);

IROpcode move_result_for_invoke(const DexMethodRef* method);

IROpcode invoke_for_method(const DexMethod* method);

IROpcode return_opcode(const DexType* type);

IROpcode load_opcode(const DexType* type);

IROpcode move_opcode(const DexType* type);

IROpcode move_result_to_move(IROpcode);

IROpcode return_to_move(IROpcode);

IROpcode move_result_to_pseudo(IROpcode op);

IROpcode pseudo_to_move_result(IROpcode op);

IROpcode iget_opcode_for_field(const DexField* field);

IROpcode sget_opcode_for_field(const DexField* field);

// The aget and aput opcodes for an array whose elements have type `component`.
IROpcode aget_opcode_for_type(const DexType* component);
IROpcode aput_opcode_for_type(const DexType* component);

// The move-result-pseudo that takes the value of `op`, an opcode that has one.
IROpcode move_result_pseudo_for(IROpcode op);

enum Branchingness : uint8_t {
  BRANCH_NONE,
  BRANCH_RETURN,
  BRANCH_GOTO,
  BRANCH_IF,
  BRANCH_SWITCH,
  BRANCH_THROW // both always throw and may_throw
};

Branchingness branchingness(IROpcode op);

} // namespace opcode

/*
 * The functions below probably shouldn't be accessed directly by opt/ code.
 * They're implementation details wrapped by IRInstruction and DexInstruction.
 */
namespace opcode_impl {

bool has_dest(IROpcode);

bool has_move_result_pseudo(IROpcode);

// we can't tell the srcs size from the opcode alone -- format 35c opcodes
// encode that separately. So this just returns the minimum.
unsigned min_srcs_size(IROpcode);

bool dest_is_wide(IROpcode);

bool dest_is_object(IROpcode);

} // namespace opcode_impl
