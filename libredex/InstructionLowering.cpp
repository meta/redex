/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "InstructionLowering.h"

#include "ConfigFiles.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexInstruction.h"
#include "DexOpcodeDefs.h"
#include "DexStore.h"
#include "DexUtil.h"
#include "IRInstruction.h"
#include "MethodProfiles.h"
#include "Show.h"
#include "Walkers.h"
#include <array>
#include <optional>

namespace instruction_lowering {

namespace {

constexpr double kSparseSwitchHotMethodAppearThreshold = 0.0;

} // namespace

/*
 * Returns whether the given value can fit in an integer of :width bits.
 */
template <int width>
static bool signed_int_fits(int64_t v) {
  auto shift = 64 - width;
  return int64_t(uint64_t(v) << shift) >> shift == v;
}

/*
 * Returns whether the given value's significant bits can fit in the top 16
 * bits of an integer of :total_width bits. For example, since v is a signed
 * 64-bit int, a value v that can fit into the top 16 bits of a 32-bit int
 * would have the form 0xffffffffrrrr0000, where rrrr are the significant bits.
 */
template <int total_width>
static bool signed_int_fits_high16(int64_t v) {
  auto right_zeros = total_width - 16;
  auto left_ones = 64 - total_width;
  return int64_t(uint64_t(v >> right_zeros) << (64 - 16)) >> left_ones == v;
}

/*
 * Helpers for lower()
 */

/*
 * Returns an array of move opcodes of the appropriate type, sorted by
 * increasing size.
 */
static std::array<DexOpcode, 3> move_opcode_tuple(IROpcode op) {
  switch (op) {
  case OPCODE_MOVE:
    return {{DOPCODE_MOVE, DOPCODE_MOVE_FROM16, DOPCODE_MOVE_16}};
  case OPCODE_MOVE_WIDE:
    return {
        {DOPCODE_MOVE_WIDE, DOPCODE_MOVE_WIDE_FROM16, DOPCODE_MOVE_WIDE_16}};
  case OPCODE_MOVE_OBJECT:
    return {{DOPCODE_MOVE_OBJECT, DOPCODE_MOVE_OBJECT_FROM16,
             DOPCODE_MOVE_OBJECT_16}};
  default:
    not_reached();
  }
}

namespace impl {

DexOpcode select_move_opcode(const IRInstruction* insn) {
  auto move_tuple = move_opcode_tuple(insn->opcode());
  auto dest_width = required_bit_width(insn->dest());
  auto src_width = required_bit_width(insn->src(0));
  if (dest_width <= 4 && src_width <= 4) {
    return move_tuple.at(0);
  } else if (dest_width <= 8) {
    return move_tuple.at(1);
  } else {
    return move_tuple.at(2);
  }
}

DexOpcode select_const_opcode(IROpcode op,
                              int64_t literal,
                              bit_width_t dest_width) {
  switch (op) {
  case OPCODE_CONST:
    if (dest_width <= 4 && signed_int_fits<4>(literal)) {
      return DOPCODE_CONST_4;
    } else if (signed_int_fits<16>(literal)) {
      return DOPCODE_CONST_16;
    } else if (signed_int_fits_high16<32>(literal)) {
      return DOPCODE_CONST_HIGH16;
    } else {
      always_assert(signed_int_fits<32>(literal));
      return DOPCODE_CONST;
    }
  case OPCODE_CONST_WIDE:
    if (signed_int_fits<16>(literal)) {
      return DOPCODE_CONST_WIDE_16;
    } else if (signed_int_fits<32>(literal)) {
      return DOPCODE_CONST_WIDE_32;
    } else if (signed_int_fits_high16<64>(literal)) {
      return DOPCODE_CONST_WIDE_HIGH16;
    } else {
      return DOPCODE_CONST_WIDE;
    }
  default:
    not_reached();
  }
}

DexOpcode select_const_opcode(const IRInstruction* insn) {
  auto dest_width = required_bit_width(insn->dest());
  always_assert(dest_width <= 8);
  return select_const_opcode(insn->opcode(), insn->get_literal(), dest_width);
}

DexOpcode select_binop_lit_opcode(const IRInstruction* insn) {
  auto op = insn->opcode();
  auto literal = insn->get_literal();
  if (signed_int_fits<8>(literal)) { // lit8 -> literal is 8 bits
    switch (op) {
    case OPCODE_ADD_INT_LIT:
      return DOPCODE_ADD_INT_LIT8;
    case OPCODE_RSUB_INT_LIT:
      return DOPCODE_RSUB_INT_LIT8;
    case OPCODE_MUL_INT_LIT:
      return DOPCODE_MUL_INT_LIT8;
    case OPCODE_DIV_INT_LIT:
      return DOPCODE_DIV_INT_LIT8;
    case OPCODE_REM_INT_LIT:
      return DOPCODE_REM_INT_LIT8;
    case OPCODE_AND_INT_LIT:
      return DOPCODE_AND_INT_LIT8;
    case OPCODE_OR_INT_LIT:
      return DOPCODE_OR_INT_LIT8;
    case OPCODE_XOR_INT_LIT:
      return DOPCODE_XOR_INT_LIT8;
    case OPCODE_SHL_INT_LIT:
      return DOPCODE_SHL_INT_LIT8;
    case OPCODE_SHR_INT_LIT:
      return DOPCODE_SHR_INT_LIT8;
    case OPCODE_USHR_INT_LIT:
      return DOPCODE_USHR_INT_LIT8;
    default:
      not_reached();
    }
  } else if (signed_int_fits<16>(literal)) { // lit16 -> literal is 16 bits
    switch (op) {
    case OPCODE_ADD_INT_LIT:
      return DOPCODE_ADD_INT_LIT16;
    case OPCODE_RSUB_INT_LIT:
      return DOPCODE_RSUB_INT;
    case OPCODE_MUL_INT_LIT:
      return DOPCODE_MUL_INT_LIT16;
    case OPCODE_DIV_INT_LIT:
      return DOPCODE_DIV_INT_LIT16;
    case OPCODE_REM_INT_LIT:
      return DOPCODE_REM_INT_LIT16;
    case OPCODE_AND_INT_LIT:
      return DOPCODE_AND_INT_LIT16;
    case OPCODE_OR_INT_LIT:
      return DOPCODE_OR_INT_LIT16;
    case OPCODE_XOR_INT_LIT:
      return DOPCODE_XOR_INT_LIT16;
    default:
      not_reached();
    }
  } else {
    // literal > 16 not yet supported
    always_assert_log(
        false, "binop_lit doesn't support literals greater than 16 bits");
  }
}

static DexOpcode convert_3to2addr(DexOpcode op) {
  always_assert(op >= DOPCODE_ADD_INT && op <= DOPCODE_REM_DOUBLE);
  constexpr uint16_t offset = DOPCODE_ADD_INT_2ADDR - DOPCODE_ADD_INT;
  return static_cast<DexOpcode>(op + offset);
}

bool try_2addr_conversion(MethodItemEntry* mie) {
  auto* insn = mie->dex_insn;
  auto op = insn->opcode();
  if (dex_opcode::is_commutative(op) && insn->dest() == insn->src(1) &&
      insn->dest() <= 0xf && insn->src(0) <= 0xf) {
    auto* new_insn = new DexInstruction(convert_3to2addr(op));
    new_insn->set_dest(insn->dest());
    new_insn->set_src(1, insn->src(0));
    delete mie->dex_insn;
    mie->dex_insn = new_insn;
    return true;
  } else if (op >= DOPCODE_ADD_INT && op <= DOPCODE_REM_DOUBLE &&
             insn->dest() == insn->src(0) && insn->dest() <= 0xf &&
             insn->src(1) <= 0xf) {
    auto* new_insn = new DexInstruction(convert_3to2addr(op));
    new_insn->set_dest(insn->dest());
    new_insn->set_src(1, insn->src(1));
    delete mie->dex_insn;
    mie->dex_insn = new_insn;
    return true;
  }
  return false;
}

} // namespace impl

size_t const_code_units(IROpcode op, int64_t literal) {
  return DexInstruction(
             impl::select_const_opcode(op, literal, /*dest_width=*/4))
      .size();
}

using namespace impl;

namespace {

/*
 * Checks that the load-param opcodes are consistent with the method prototype.
 */
void check_load_params(DexMethod* method) {
  auto* code = method->get_code();
  auto params = code->get_param_instructions();
  auto param_ops = InstructionIterable(params);
  if (param_ops.empty()) {
    return;
  }
  auto* args_list = method->get_proto()->get_args();
  auto it = param_ops.begin();
  auto end = param_ops.end();
  reg_t next_ins = it->insn->dest();
  if (!is_static(method)) {
    auto op = it->insn->opcode();
    always_assert(op == IOPCODE_LOAD_PARAM_OBJECT);
    it.reset(code->erase_and_dispose(it.unwrap()));
    ++next_ins;
  }
  auto args_it = args_list->begin();
  for (; it != end; ++it) {
    auto op = it->insn->opcode();
    // check that the param registers are contiguous
    always_assert(next_ins == it->insn->dest());
    // TODO: have load param opcodes store the actual type of the param and
    // check that they match the method prototype here
    always_assert(args_it != args_list->end());
    auto expected_op = opcode::load_opcode(*args_it);
    always_assert(op == expected_op);
    ++args_it;
    next_ins += it->insn->dest_is_wide() ? 2 : 1;
  }
  always_assert(args_it == args_list->end());
  // check that the params are at the end of the frame
  for (auto& mie : InstructionIterable(code)) {
    auto* insn = mie.insn;
    if (insn->has_dest()) {
      always_assert_log(insn->dest() < next_ins,
                        "Instruction %s refers to a register (v%u) >= size (%u)"
                        " in method %s\n",
                        SHOW(insn),
                        insn->dest(),
                        next_ins,
                        SHOW(method));
    }
    for (size_t i = 0; i < insn->srcs_size(); ++i) {
      always_assert_log(insn->src(i) < next_ins,
                        "Instruction %s refers to a register (v%u) >= size (%u)"
                        " in method %s\n",
                        SHOW(insn),
                        insn->src(i),
                        next_ins,
                        SHOW(method));
    }
  }
}

DexInstruction* create_dex_instruction(const IRInstruction* insn) {
  always_assert_log(insn->opcode() != IOPCODE_R_CONST,
                    "All IOPCODE_R_CONST should already be lowered by "
                    "LowerResourceConstantsPass");
  // TODO: Assert that this never happens. IOPCODE_INIT_CLASS should never make
  // it here.
  if (insn->opcode() == IOPCODE_INIT_CLASS) {
    return new DexInstruction(DOPCODE_NOP);
  }
  // TODO: Assert that this never happens. IOPCODE_INJECTION_ID should never
  // make it here.
  if (insn->opcode() == IOPCODE_INJECTION_ID) {
    return new DexInstruction(DOPCODE_CONST);
  }
  // TODO: Assert that this never happens. IOPCODE_UNREACHABLE should never
  // make it here.
  if (insn->opcode() == IOPCODE_UNREACHABLE) {
    return new DexInstruction(DOPCODE_CONST);
  }
  always_assert(insn->opcode() != IOPCODE_WRITE_BARRIER);

  auto op = opcode::to_dex_opcode(insn->opcode());
  switch (opcode::ref(insn->opcode())) {
  case opcode::Ref::None:
  case opcode::Ref::Data:
  case opcode::Ref::Literal:
    return new DexInstruction(op);
  case opcode::Ref::String:
    return new DexOpcodeString(op, insn->get_string());
  case opcode::Ref::Type:
    return new DexOpcodeType(op, insn->get_type());
  case opcode::Ref::Field:
    return new DexOpcodeField(op, insn->get_field());
  case opcode::Ref::Method:
    return new DexOpcodeMethod(op, insn->get_method());
  case opcode::Ref::CallSite:
    return new DexOpcodeCallSite(op, insn->get_callsite());
  case opcode::Ref::MethodHandle:
    return new DexOpcodeMethodHandle(op, insn->get_methodhandle());
  case opcode::Ref::Proto:
    return new DexOpcodeProto(op, insn->get_proto());
  }
}

// IRCode::remove_opcode doesn't support removal of move-result-pseudo
// instructions in isolation -- it only removes them when the caller calls it
// with the associated 'primary' prefix instruction -- so we use this function
// specifically for this purpose.
void remove_move_result_pseudo(const IRList::iterator& it) {
  always_assert(opcode::is_a_move_result_pseudo(it->insn->opcode()));
  delete it->insn;
  it->insn = nullptr;
  it->type = MFLOW_FALLTHROUGH;
}

/*
 * Returns the number of DexInstructions added during lowering (not including
 * the check-cast).
 */
size_t lower_check_cast(DexMethod*, IRCode* code, IRList::iterator* it_) {
  auto& it = *it_;
  const auto* insn = it->insn;
  size_t extra_instructions{0};
  auto* move = ir_list::move_result_pseudo_of(it);
  // Built before any replace_ir_with_dex, which deletes `insn`.
  auto* dex_insn = new DexOpcodeType(DOPCODE_CHECK_CAST, insn->get_type());
  dex_insn->set_src(0, move->dest());
  if (move->dest() != insn->src(0)) {
    // convert check-cast v1; move-result-pseudo v0 into
    //
    //   move v0, v1
    //   check-cast v0
    // TODO: factor this code a little
    auto move_template = std::make_unique<IRInstruction>(OPCODE_MOVE_OBJECT);
    move_template->set_dest(move->dest());
    move_template->set_src(0, insn->src(0));
    auto* dex_mov = new DexInstruction(select_move_opcode(move_template.get()));
    dex_mov->set_dest(move->dest());
    dex_mov->set_src(0, insn->src(0));
    // The emitted order is move, then check-cast, either way. The MOVE goes in
    // the EXISTING MethodItemEntry and the cast in the new one, so the entry
    // that survives lowering is the one holding the FIRST emitted instruction.
    // Output is unchanged -- same opcodes, same order, same addresses; only
    // which entry owns which DexInstruction differs.
    it->replace_ir_with_dex(dex_mov);
    it = code->insert_after(it, dex_insn);
    ++extra_instructions;
  } else {
    it->replace_ir_with_dex(dex_insn);
  }
  remove_move_result_pseudo(++it);

  return extra_instructions;
}

void lower_fill_array_data(DexMethod*, IRCode* code, IRList::iterator* it_) {
  auto& it = *it_;
  const auto* insn = it->insn;
  auto* dex_insn = new DexInstruction(DOPCODE_FILL_ARRAY_DATA);
  dex_insn->set_src(0, insn->src(0));
  auto* bt = new BranchTarget(&*it);
  code->push_back(bt);
  code->push_back(insn->get_data()->clone());
  it->replace_ir_with_dex(dex_insn);
}

void lower_to_range_instruction(DexMethod* method,
                                IRCode* code,
                                IRList::iterator* it_) {
  auto& it = *it_;
  const auto* insn = it->insn;
  always_assert_log(
      insn->has_contiguous_range_srcs_denormalized(),
      "Instruction %s has non-contiguous srcs in method %s.\nContext:\n%s\n",
      SHOW(insn),
      SHOW(method),
      SHOW_CONTEXT(code, insn));
  auto* dex_insn = create_dex_instruction(insn);
  dex_insn->set_opcode(opcode::range_version(insn->opcode()));
  dex_insn->set_range_base(insn->src(0));
  dex_insn->set_range_size(insn->srcs_size());
  it->replace_ir_with_dex(dex_insn);
}

void lower_simple_instruction(DexMethod*, IRCode*, IRList::iterator* it_) {
  auto& it = *it_;
  const auto* insn = it->insn;
  auto op = insn->opcode();

  DexInstruction* dex_insn;
  if (opcode::is_a_move(op)) {
    dex_insn = new DexInstruction(select_move_opcode(insn));
  } else if (op >= OPCODE_CONST && op <= OPCODE_CONST_WIDE) {
    dex_insn = new DexInstruction(select_const_opcode(insn));
  } else if (op >= OPCODE_ADD_INT_LIT && op <= OPCODE_USHR_INT_LIT) {
    dex_insn = new DexInstruction(select_binop_lit_opcode(insn));
  } else {
    dex_insn = create_dex_instruction(insn);
  }
  if (insn->has_dest()) {
    dex_insn->set_dest(insn->dest());
  } else if (insn->has_move_result_pseudo()) {
    dex_insn->set_dest(ir_list::move_result_pseudo_of(it)->dest());
  }
  for (size_t i = 0; i < insn->srcs_size(); ++i) {
    dex_insn->set_src(static_cast<int>(i), insn->src(i));
  }
  if (insn->has_literal()) {
    dex_insn->set_literal(insn->get_literal());
  }
  auto dex_op = dex_insn->opcode();
  if (dex_opcode::has_arg_word_count(dex_op)) {
    dex_insn->set_arg_word_count(insn->srcs_size());
  }
  auto has_move_result_pseudo = insn->has_move_result_pseudo();
  it->replace_ir_with_dex(dex_insn);
  if (has_move_result_pseudo) {
    remove_move_result_pseudo(++it);
  }
}

} // namespace

Stats lower(DexMethod* method, ConfigFiles* conf) {
  Stats stats;
  auto* code = method->get_code();
  always_assert(code != nullptr);

  // Check the load-param opcodes make sense before removing them
  check_load_params(method);

  UnorderedMap<MethodItemEntry*, std::vector<int32_t>> case_keys;
  for (const MethodItemEntry& it : *code) {
    if (it.type == MFLOW_TARGET) {
      BranchTarget* bt = it.target;
      if (bt->type == BRANCH_MULTI) {
        case_keys[bt->src].push_back(bt->case_key);
      }
    }
  }
  for (auto& entry : UnorderedIterable(case_keys)) {
    std::sort(entry.second.begin(), entry.second.end());
  }

  std::optional<bool> method_is_hot = std::nullopt;

  for (auto it = code->begin(); it != code->end(); ++it) {
    if (it->type != MFLOW_OPCODE) {
      continue;
    }
    auto* insn = it->insn;
    auto op = insn->opcode();
    insn->denormalize_registers();

    if (opcode::is_a_load_param(op)) {
      code->remove_opcode(it);
    } else if (op == OPCODE_CHECK_CAST) {
      stats.move_for_check_cast += lower_check_cast(method, code, &it);
    } else if (op == OPCODE_FILL_ARRAY_DATA) {
      lower_fill_array_data(method, code, &it);
    } else if (needs_range_conversion(insn)) {
      lower_to_range_instruction(method, code, &it);
    } else {
      lower_simple_instruction(method, code, &it);
    }

    // Overwrite the switch dex opcode with the correct type, depending on how
    // its cases are laid out.
    if (op == OPCODE_SWITCH) {
      const auto& keys = case_keys.at(&*it);
      DexOpcode dop = CaseKeysExtent::from_ordered(keys).sufficiently_sparse()
                          ? DOPCODE_SPARSE_SWITCH
                          : DOPCODE_PACKED_SWITCH;
      it->dex_insn->set_opcode(dop);
      if (dop == DexOpcode::DOPCODE_SPARSE_SWITCH) {
        if (!method_is_hot) {
          if (conf != nullptr) {
            method_is_hot = [&]() {
              for (const auto& p :
                   conf->get_method_profiles().all_interactions()) {
                auto profile_it = p.second.find(method);
                if (profile_it != p.second.end() &&
                    profile_it->second.appear_percent >
                        kSparseSwitchHotMethodAppearThreshold) {
                  return true;
                }
              }
              return false;
            }();
          } else {
            method_is_hot = false;
          }
        }

        Stats::SparseSwitches::Data data(1, (*method_is_hot) ? 1 : 0);
        stats.sparse_switches.data[keys.size()] += data;
      }
    }
  }
  for (auto it = code->begin(); it != code->end(); ++it) {
    always_assert(it->type != MFLOW_OPCODE);
    if (it->type != MFLOW_DEX_OPCODE) {
      continue;
    }
    stats.to_2addr += static_cast<unsigned long>(try_2addr_conversion(&*it));
  }
  return stats;
}

Stats run(DexStoresVector& stores, ConfigFiles* conf) {
  auto scope = build_class_scope(stores);
  return walk::parallel::methods<Stats>(scope, [conf](DexMethod* m) {
    Stats stats;
    if (m->get_code() == nullptr) {
      return stats;
    }
    return lower(m, conf);
  });
}

void normalize_cfg(DexStoresVector& stores) {
  walk::parallel::code(build_class_scope(stores), [](DexMethod*, IRCode& code) {
    code.build_cfg();
    code.clear_cfg();
  });
}

CaseKeysExtent CaseKeysExtent::from_ordered(
    const std::vector<int32_t>& case_keys) {
  always_assert(!case_keys.empty());
  always_assert(case_keys.front() <= case_keys.back());
  return CaseKeysExtent{case_keys.front(), case_keys.back(),
                        (uint32_t)case_keys.size()};
}

// Computes number of entries needed for a packed switch, accounting for any
// holes that might exist
uint64_t CaseKeysExtent::get_packed_switch_size() const {
  always_assert(first_key <= last_key);
  always_assert(size > 0);
  return (uint64_t)((int64_t)last_key - first_key + 1);
}

// Whether a sparse switch statement will be more compact than a packed switch
bool CaseKeysExtent::sufficiently_sparse() const {
  uint64_t packed_switch_size = get_packed_switch_size();
  // packed switches must have less than 2^16 entries, and
  // sparse switches pay off once there are more holes than entries
  return packed_switch_size > std::numeric_limits<uint16_t>::max() ||
         packed_switch_size / 2 > size;
}

uint32_t CaseKeysExtent::estimate_switch_payload_code_units() const {
  if (sufficiently_sparse()) {
    // sparse-switch-payload
    return 2 + 4 * size;
  } else {
    // packed-switch-payload
    const uint64_t packed_switch_size = get_packed_switch_size();
    return 4 + static_cast<uint32_t>(packed_switch_size * 2);
  }
}

void CaseKeysExtentBuilder::insert(int32_t case_key) {
  if (!m_info) {
    m_info = (CaseKeysExtent){case_key, case_key, 1};
    return;
  }
  m_info->first_key = std::min(m_info->first_key, case_key);
  m_info->last_key = std::max(m_info->last_key, case_key);
  m_info->size++;
}

const CaseKeysExtent& CaseKeysExtentBuilder::operator*() const {
  always_assert(m_info);
  return *m_info;
}

const CaseKeysExtent* CaseKeysExtentBuilder::operator->() const {
  always_assert(m_info);
  return &*m_info;
}

} // namespace instruction_lowering
