/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "IRInstruction.h"

#include "Debug.h"
#include "DexCallSite.h"
#include "DexClass.h"
#include "DexInstruction.h"
#include "DexMethodHandle.h"
#include "DexUtil.h"
#include "Show.h"
#include "TypeUtil.h"

#include <cstring>
#include <iterator>

IRInstruction::IRInstruction(IROpcode op) : m_opcode(op) {
  auto count = opcode_impl::min_srcs_size(op);
  m_num_srcs = count;
  if (count > MAX_NUM_INLINE_SRCS) {
    always_assert(count < std::numeric_limits<src_index_t>::max());
    m_srcs = new reg_t[count];
  }
}

IRInstruction::IRInstruction(const IRInstruction& other)
    : m_opcode(other.m_opcode),
      m_num_srcs(other.m_num_srcs),
      m_dest(other.m_dest),
      // TODO: This can trigger undefined behavior.
      m_literal(other.m_literal) {
  if (m_num_srcs <= MAX_NUM_INLINE_SRCS) {
    for (src_index_t i = 0; i < m_num_srcs; ++i) {
      m_inline_srcs[i] = other.m_inline_srcs[i];
    }
  } else {
    m_srcs = new reg_t[m_num_srcs];
    std::memcpy(m_srcs, other.m_srcs, m_num_srcs * sizeof(reg_t));
  }
  if (other.has_data()) {
    m_data = other.m_data->clone();
  }
}

IRInstruction& IRInstruction::operator=(const IRInstruction& other) {
  if (this == &other) {
    return *this;
  }
  // Free old resources before overwriting.
  if (m_num_srcs > MAX_NUM_INLINE_SRCS) {
    delete[] m_srcs;
  }
  if (has_data()) {
    delete m_data;
  }
  m_opcode = other.m_opcode;
  m_num_srcs = other.m_num_srcs;
  m_dest = other.m_dest;
  // TODO: This can trigger undefined behavior.
  m_literal = other.m_literal;
  if (m_num_srcs <= MAX_NUM_INLINE_SRCS) {
    for (src_index_t i = 0; i < m_num_srcs; ++i) {
      m_inline_srcs[i] = other.m_inline_srcs[i];
    }
  } else {
    m_srcs = new reg_t[m_num_srcs];
    std::memcpy(m_srcs, other.m_srcs, m_num_srcs * sizeof(reg_t));
  }
  if (other.has_data()) {
    m_data = other.m_data->clone();
  }
  return *this;
}

IRInstruction::~IRInstruction() {
  if (m_num_srcs > MAX_NUM_INLINE_SRCS) {
    delete[] m_srcs;
  }
  if (has_data()) {
    delete m_data;
  }
}

IRInstruction* IRInstruction::set_data(std::unique_ptr<DexOpcodeData> data) {
  always_assert(has_data());
  delete m_data;
  m_data = data.release();
  return this;
}

// Structural equality of opcodes except branches offsets are ignored
// because they are unknown until we sync back to DexInstructions.
bool IRInstruction::operator==(const IRInstruction& that) const {
  bool simple_fields_match = m_opcode == that.m_opcode &&
                             m_num_srcs == that.m_num_srcs &&
                             m_dest == that.m_dest;
  if (!simple_fields_match) {
    return false;
  }

  // Avoid calling opcode::ref(); there's only one instruction that has data.
  if (m_opcode == OPCODE_FILL_ARRAY_DATA) {
    // NOLINTNEXTLINE(bugprone-assert-side-effect) No side effect here.
    redex_assert(opcode::ref(m_opcode) == opcode::Ref::Data);
    auto size = m_data->data_size();
    if (size != that.m_data->data_size() ||
        std::memcmp(m_data->data(),
                    that.m_data->data(),
                    size * sizeof(uint16_t)) != 0) {
      return false;
    }
  } else {
    // NOLINTNEXTLINE(bugprone-assert-side-effect) No side effect here.
    redex_assert(opcode::ref(m_opcode) != opcode::Ref::Data);
    if (m_literal != that.m_literal) { // just test one member of the union
      return false;
    }
  }

  // Check the source registers union
  if (m_num_srcs <= MAX_NUM_INLINE_SRCS) {
    for (src_index_t i = 0; i < m_num_srcs; ++i) {
      if (m_inline_srcs[i] != that.m_inline_srcs[i]) {
        return false;
      }
    }
    return true;
  }
  return std::memcmp(m_srcs, that.m_srcs, m_num_srcs * sizeof(reg_t)) == 0;
}

reg_t IRInstruction::src(src_index_t i) const {
  always_assert(i < m_num_srcs);
  if (m_num_srcs <= MAX_NUM_INLINE_SRCS) {
    return m_inline_srcs[i];
  }
  return m_srcs[i];
}

IRInstruction::reg_range IRInstruction::srcs() const {
  const reg_t* begin =
      m_num_srcs <= MAX_NUM_INLINE_SRCS ? std::begin(m_inline_srcs) : m_srcs;
  const reg_t* end = begin + m_num_srcs;
  return reg_range(begin, end);
}

std::vector<reg_t> IRInstruction::srcs_copy() const {
  std::vector<reg_t> result;
  result.reserve(srcs_size());
  for (reg_t src : srcs()) {
    result.push_back(src);
  }
  return result;
}

IRInstruction* IRInstruction::set_srcs(const reg_range& r) {
  if (r.size() != m_num_srcs) {
    if (m_num_srcs > MAX_NUM_INLINE_SRCS) {
      delete[] m_srcs;
    }
    if (r.size() > MAX_NUM_INLINE_SRCS) {
      always_assert(r.size() < std::numeric_limits<src_index_t>::max());
      m_srcs = new reg_t[r.size()];
    }
  }
  if (r.size() <= MAX_NUM_INLINE_SRCS) {
    for (src_index_t i = 0; i < r.size(); ++i) {
      m_inline_srcs[i] = r[i];
    }
  } else {
    for (src_index_t i = 0; i < r.size(); ++i) {
      m_srcs[i] = r[i];
    }
  }
  m_num_srcs = r.size();
  return this;
}

IRInstruction* IRInstruction::set_src(src_index_t i, reg_t reg) {
  always_assert(i < m_num_srcs);
  if (m_num_srcs <= MAX_NUM_INLINE_SRCS) {
    m_inline_srcs[i] = reg;
  } else {
    m_srcs[i] = reg;
  }
  return this;
}

size_t IRInstruction::srcs_size() const { return m_num_srcs; }

IRInstruction* IRInstruction::set_srcs_size(size_t count) {
  if (m_num_srcs <= MAX_NUM_INLINE_SRCS) {
    if (count <= MAX_NUM_INLINE_SRCS) {
      // staying in the inline regs state
      for (src_index_t i = m_num_srcs; i < count; ++i) {
        m_inline_srcs[i] = 0;
      }
    } else {
      // inline regs -> array
      always_assert(count < std::numeric_limits<src_index_t>::max());
      auto* srcs = new reg_t[count];
      for (src_index_t i = 0; i < m_num_srcs; ++i) {
        srcs[i] = m_inline_srcs[i];
      }
      std::memset(srcs + m_num_srcs, 0, (count - m_num_srcs) * sizeof(reg_t));
      m_srcs = srcs;
    }
  } else {
    if (count <= MAX_NUM_INLINE_SRCS) {
      // array -> inline regs
      auto* old_srcs = m_srcs;
      for (src_index_t i = 0; i < count; ++i) {
        m_inline_srcs[i] = old_srcs[i];
      }
      delete[] old_srcs;
    } else if (count != m_num_srcs) {
      // staying in the array state
      always_assert(count < std::numeric_limits<src_index_t>::max());
      auto* srcs = new reg_t[count];
      auto copy_count = std::min((src_index_t)count, m_num_srcs);
      std::memcpy(srcs, m_srcs, copy_count * sizeof(reg_t));
      std::memset(srcs + copy_count, 0, (count - copy_count) * sizeof(reg_t));
      delete[] m_srcs;
      m_srcs = srcs;
    }
  }
  m_num_srcs = count;
  return this;
}

uint16_t IRInstruction::size() const {
  auto op = m_opcode;
  if (opcode::is_write_barrier(op)) {
    op = OPCODE_INVOKE_STATIC;
  }
  if (opcode::is_an_internal(op)) {
    if (opcode::is_r_const(op)) {
      return 3;
    } else if (opcode::is_injection_id(op)) {
      return 2;
    } else if (opcode::is_unreachable(op)) {
      return 1;
    }
    return 0;
  }
  static int args[] = {
      0, /* FMT_f00x   */
      1, /* FMT_f10x   */
      1, /* FMT_f12x   */
      1, /* FMT_f12x_2 */
      1, /* FMT_f11n   */
      1, /* FMT_f11x_d */
      1, /* FMT_f11x_s */
      1, /* FMT_f10t   */
      2, /* FMT_f20t   */
      2, /* FMT_f20bc  */
      2, /* FMT_f22x   */
      2, /* FMT_f21t   */
      2, /* FMT_f21s   */
      2, /* FMT_f21h   */
      2, /* FMT_f21c_d */
      2, /* FMT_f21c_s */
      2, /* FMT_f23x_d */
      2, /* FMT_f23x_s */
      2, /* FMT_f22b   */
      2, /* FMT_f22t   */
      2, /* FMT_f22s   */
      2, /* FMT_f22c_d */
      2, /* FMT_f22c_s */
      2, /* FMT_f22cs  */
      3, /* FMT_f30t   */
      3, /* FMT_f32x   */
      3, /* FMT_f31i   */
      3, /* FMT_f31t   */
      3, /* FMT_f31c   */
      3, /* FMT_f35c   */
      3, /* FMT_f35ms  */
      3, /* FMT_f35mi  */
      3, /* FMT_f3rc   */
      3, /* FMT_f3rms  */
      3, /* FMT_f3rmi  */
      5, /* FMT_f51l   */
      4, /* FMT_f41c_d */
      4, /* FMT_f41c_s */
      5, /* FMT_f52c_d */
      5, /* FMT_f52c_s */
      5, /* FMT_f5rc */
      5, /* FMT_f57c */
      0, /* FMT_fopcode   */
  };
  return args[dex_opcode::format(opcode::to_dex_opcode(op))];
}

// The instruction format doesn't tell us the width of registers for invoke
// so we inspect the signature of the method we're calling
bool IRInstruction::invoke_src_is_wide(src_index_t i) const {
  always_assert(has_method());

  // virtual methods have `this` as the 0th register argument, but the
  // arg list does NOT include `this`
  if (!opcode::is_invoke_static(m_opcode)) {
    if (i == 0) {
      // reference to `this`. References are never wide
      return false;
    }
    --i;
  }

  return type::is_wide_type(m_method->get_proto()->get_args()->at(i));
}

bool IRInstruction::src_is_wide(src_index_t i) const {
  always_assert(i < srcs_size());

  if (opcode::is_an_invoke(m_opcode)) {
    return invoke_src_is_wide(i);
  }

  switch (opcode()) {
  case OPCODE_MOVE_WIDE:
  case OPCODE_RETURN_WIDE:
    return i == 0;

  case OPCODE_CMPL_DOUBLE:
  case OPCODE_CMPG_DOUBLE:
  case OPCODE_CMP_LONG:
    return i == 0 || i == 1;

  case OPCODE_APUT_WIDE:
  case OPCODE_IPUT_WIDE:
  case OPCODE_SPUT_WIDE:
    return i == 0;

  case OPCODE_NEG_LONG:
  case OPCODE_NOT_LONG:
  case OPCODE_NEG_DOUBLE:
  case OPCODE_LONG_TO_INT:
  case OPCODE_LONG_TO_FLOAT:
  case OPCODE_LONG_TO_DOUBLE:
  case OPCODE_DOUBLE_TO_INT:
  case OPCODE_DOUBLE_TO_LONG:
  case OPCODE_DOUBLE_TO_FLOAT:
    return i == 0;

  case OPCODE_ADD_LONG:
  case OPCODE_SUB_LONG:
  case OPCODE_MUL_LONG:
  case OPCODE_DIV_LONG:
  case OPCODE_REM_LONG:
  case OPCODE_AND_LONG:
  case OPCODE_OR_LONG:
  case OPCODE_XOR_LONG:
  case OPCODE_ADD_DOUBLE:
  case OPCODE_SUB_DOUBLE:
  case OPCODE_MUL_DOUBLE:
  case OPCODE_DIV_DOUBLE:
  case OPCODE_REM_DOUBLE:
    return i == 0 || i == 1;

  case OPCODE_SHL_LONG:
  case OPCODE_SHR_LONG:
  case OPCODE_USHR_LONG:
    return i == 0;

  default:
    return false;
  }
}

bool IRInstruction::normalize_registers(std::string* error_msg) {
  if (opcode::is_an_invoke(opcode())) {
    auto* args = get_method()->get_proto()->get_args();
    size_t old_srcs_idx{0};
    size_t srcs_idx{0};
    if (m_opcode != OPCODE_INVOKE_STATIC) {
      ++srcs_idx;
      ++old_srcs_idx;
    }
    for (size_t args_idx = 0; args_idx < args->size(); ++args_idx) {
      if (old_srcs_idx >= srcs_size()) {
        if (error_msg != nullptr) {
          *error_msg = "Invalid arg indices in " + show(this);
        }
        return false;
      }
      set_src(srcs_idx++, src(old_srcs_idx));
      old_srcs_idx += type::is_wide_type(args->at(args_idx)) ? 2 : 1;
    }
    if (old_srcs_idx != srcs_size()) {
      if (error_msg != nullptr) {
        *error_msg = "Number of registers wrong in " + show(this);
      }
      return false;
    }
    set_srcs_size(srcs_idx);
  }
  return true;
}

void IRInstruction::denormalize_registers() {
  if (opcode::is_an_invoke(m_opcode)) {
    auto* args = get_method()->get_proto()->get_args();
    bool has_wide = false;
    for (const auto& arg : *args) {
      if (type::is_wide_type(arg)) {
        has_wide = true;
        break;
      }
    }
    if (!has_wide) {
      return;
    }

    std::vector<reg_t> srcs;
    size_t args_idx{0};
    size_t srcs_idx{0};
    if (m_opcode != OPCODE_INVOKE_STATIC) {
      srcs.push_back(src(srcs_idx++));
    }
    for (; args_idx < args->size(); ++args_idx, ++srcs_idx) {
      srcs.push_back(src(srcs_idx));
      if (type::is_wide_type(args->at(args_idx))) {
        srcs.push_back(src(srcs_idx) + 1);
      }
    }

    set_srcs(srcs);
  }
}

bit_width_t required_bit_width(uint16_t v) {
  bit_width_t result{1};
  while ((v >>= 1) != 0) {
    ++result;
  }
  return result;
}

std::vector<IRInstruction*> make_check_cast(const DexType* type,
                                            reg_t src_dest) {
  auto* check_cast = new IRInstruction(OPCODE_CHECK_CAST);
  check_cast->set_type(type)->set_src(0, src_dest);
  auto* move_result_pseudo =
      new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT);
  move_result_pseudo->set_dest(src_dest);
  return {check_cast, move_result_pseudo};
}

bool needs_range_conversion(const IRInstruction* insn) {
  auto op = insn->opcode();
  if (!opcode::has_range_form(op)) {
    return false;
  }
  if (insn->srcs_size() > dex_opcode::NON_RANGE_MAX) {
    return true;
  }
  always_assert(!opcode::is_an_internal(op));
  auto dex_op = opcode::to_dex_opcode(op);
  for (size_t i = 0; i < insn->srcs_size(); ++i) {
    if (required_bit_width(insn->src(i)) >
        dex_opcode::src_bit_width(dex_op, i)) {
      return true;
    }
  }
  return false;
}

uint64_t IRInstruction::hash() const {
  uint64_t result = opcode();

  for (size_t i = 0; i < srcs_size(); i++) {
    result ^= src(i);
  }

  if (has_dest()) {
    result ^= dest();
  }

  switch (opcode::ref(opcode())) {
  case opcode::Ref::Data: {
    size_t size = get_data()->data_size();
    const auto& data = get_data()->data();
    for (size_t i = 0; i < size; i++) {
      result ^= data[i];
    }
    break;
  }
  case opcode::Ref::Proto:
  case opcode::Ref::CallSite:
  case opcode::Ref::MethodHandle:
  case opcode::Ref::Field:
  case opcode::Ref::Method:
  case opcode::Ref::Literal:
  case opcode::Ref::String:
  case opcode::Ref::Type: {
    result ^= m_literal;
    break;
  }
  case opcode::Ref::None:
    break;
  }

  return result;
}

void IRInstruction::gather_init_classes(
    std::vector<const DexType*>& ltype) const {
  const auto* type = get_init_class_type_demand(this);
  if (type != nullptr) {
    ltype.push_back(type->to_mutable());
  }
}

void IRInstruction::gather_types(std::vector<const DexType*>& ltype) const {
  switch (opcode::ref(opcode())) {
  case opcode::Ref::None:
  case opcode::Ref::String:
  case opcode::Ref::Literal:
  case opcode::Ref::Data:
  case opcode::Ref::CallSite:
  case opcode::Ref::MethodHandle:
  case opcode::Ref::Proto:
    break;

  case opcode::Ref::Type:
    ltype.push_back(const_cast<DexType*>(m_type));
    break;

  case opcode::Ref::Field:
    m_field->gather_types_shallow(ltype);
    break;

  case opcode::Ref::Method:
    m_method->gather_types_shallow(ltype);
    break;
  }
}

void IRInstruction::gather_fields(std::vector<DexFieldRef*>& lfield) const {
  if (has_field()) {
    lfield.push_back(m_field);
  }
  if (has_callsite()) {
    m_callsite->gather_fields(lfield);
  }
  if (has_methodhandle()) {
    m_methodhandle->gather_fields(lfield);
  }
}

void IRInstruction::gather_methods(std::vector<DexMethodRef*>& lmethod) const {
  if (has_method()) {
    lmethod.push_back(m_method);
  }
  if (has_callsite()) {
    m_callsite->gather_methods(lmethod);
  }
  if (has_methodhandle()) {
    m_methodhandle->gather_methods(lmethod);
  }
}

void IRInstruction::gather_methodhandles(
    std::vector<DexMethodHandle*>& lmethodhandle) const {
  if (has_methodhandle()) {
    lmethodhandle.push_back(m_methodhandle);
  }
  if (has_callsite()) {
    m_callsite->gather_methodhandles(lmethodhandle);
  }
}

std::string IRInstruction::show_opcode() const { return show(m_opcode); }
