/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <boost/range/iterator_range_core.hpp>
#include <limits>
#include <memory>
#include <string>
#include <vector>

#include "Debug.h"
#include "IROpcode.h"

class DexCallSite;
class DexFieldRef;
class DexMethodHandle;
class DexMethodRef;
class DexOpcodeData;
class DexProto;
class DexString;
class DexType;

/*
 * Our IR is very similar to the Dalvik instruction set, but with a few tweaks
 * to make it easier to analyze and manipulate. Key differences are:
 *
 * 1. Registers of arbitrary size can be addressed. For example, neg-int is no
 *    longer limited to addressing registers < 16. The expectation is that the
 *    register allocator will sort things out.
 *
 * 2. 2addr opcodes do not exist in IROpcode. Not aliasing src and dest values
 *    simplifies analyses.
 *
 * 3. range instructions do not exist in IROpcode. invoke-* instructions in our
 *    IR are not constrained in their number of src operands.
 *
 * 4. invoke-* instructions no longer reference both halves of a wide register.
 *    I.e. our IR represents them like `invoke-static {v0} LFoo;.bar(J)V` even
 *    though the Dex format will represent that as
 *    `invoke-static {v0, v1} LFoo;.bar(J)V`. All other instructions in the Dex
 *    format only refer to the lower half of a wide pair, so this makes things
 *    uniform.
 *
 * 5. Any opcode that can both throw and write to a dest register is split into
 *    two separate pieces in our IR: one piece that may throw but does not
 *    write to a dest, and one move-result-pseudo instruction that writes to a
 *    dest but does not throw. This makes accurate liveness analysis easy.
 *    This is elaborated further below.
 *
 * 6. check-cast also has a move-result-pseudo suffix. check-cast has a side
 *    effect in the runtime verifier when the cast succeeds. The runtime
 *    verifier updates the type in the source register to its more specific
 *    type. As such, for many analyses, it is semantically equivalent to
 *    creating a new value. By representing the opcode in our IR as having a
 *    dest field via move-result-pseudo, these analyses can be simplified by
 *    not having to treat check-cast as a special case.
 *
 *    See this link for the relevant verifier code:
 *    androidxref.com/7.1.1_r6/xref/art/runtime/verifier/method_verifier.cc#2383
 *
 * 7. payload instructions no longer exist. fill-array-data-payload is attached
 *    directly to the fill-array-data instruction that references it.
 *    {packed, sparse}-switch-payloads are represented by MFLOW_TARGET entries
 *    in the IRCode instruction stream.
 *
 * 8. There is only one type of switch. Sparse switches and packed switches are
 *    both represented as the single `switch` IR opcode. Lowering will choose
 *    the better option.
 *
 * Background behind move-result-pseudo
 * ====================================
 * Opcodes that write to a register (say v0) but may also throw are somewhat
 * tricky to handle. Our dataflow analyses must consider v0 to be written
 * only if the opcode does not end up throwing.
 *
 * For example, say we have the following Dex code:
 *
 *   sget-object v1 <some field of type LQux;>
 *   const v0 #0
 *   start try block
 *   iget-object v0 v1 LQux;.a:LFoo;
 *   return-void
 *   // end try block
 *
 *   // exception handler
 *   invoke-static {v0} LQux;.a(LFoo;)V
 *
 * If `iget-object` throws, it will not have written to v0, so the `const` is
 * necessary to ensure that v0 is always initialized when control flow reaches
 * B2. In other words, v0 must be live-out at `const v0 #0`.
 *
 * Prior to this diff, we dealt with this by putting any potentially throwing
 * opcodes in the subsequent basic block when converting from Dex to IR:
 *
 *   B0:
 *     sget-object v1 <some field of type LQux;>
 *     const v0 #0
 *   B1: <throws to B2> // v1 is live-in here
 *     iget-object v0 v1 LQux;.a:LFoo;
 *     return-void
 *   B2: <catches exceptions from B1>
 *     invoke-static {v0} LQux;.a(LFoo;)V
 *
 * This way, straightforward liveness analysis will consider v0 to be
 * live-out at `const`. Obviously, this is still somewhat inaccurate: we end
 * up considering v1 as live-in at B1 when it should really be dead. Being
 * conservative about liveness generally doesn't create wrong behavior, but
 * can result in poorer optimizations.
 *
 * With move-result-pseudo, the above example will be represented as follows:
 *
 *   B0:
 *     sget-object v1 <some field of type LQux;>
 *     const v0 #0
 *     iget-object v1 LQux;.a:LFoo;
 *   B1: <throws to B2> // no registers are live-in here
 *     move-result-pseudo-object v0
 *     return-void
 *   B2: <catches exceptions from B1>
 *     invoke-static {v0} LQux;.a(LFoo;)V
 */
using reg_t = uint32_t;
using src_index_t = uint16_t;

// Index to a method parameter. Used in an invoke instruction.
using param_index_t = src_index_t;

// We use this special register to denote the result of a method invocation or a
// filled-array creation. If the result is a wide value, RESULT_REGISTER + 1
// holds the second component of the result.
constexpr reg_t RESULT_REGISTER = std::numeric_limits<reg_t>::max() - 1;

class IRInstruction final {
 public:
  explicit IRInstruction(IROpcode op);
  IRInstruction(const IRInstruction&);
  IRInstruction& operator=(const IRInstruction&);
  ~IRInstruction();

  /*
   * Ensures that wide registers only have their first register referenced
   * in the srcs list. This only affects invoke-* instructions.
   */
  [[nodiscard]] bool normalize_registers(std::string* error_msg = nullptr);
  /*
   * Ensures that wide registers have both registers in the pair referenced
   * in the srcs list.
   */
  void denormalize_registers();

  /*
   * Estimates the number of 16-bit code units required to encode this
   * IRInstruction. Since the exact encoding is only determined during
   * instruction lowering, this is just an estimate.
   */
  uint16_t size() const;

  bool operator==(const IRInstruction&) const;

  bool operator!=(const IRInstruction& that) const { return !(*this == that); }

  bool has_string() const {
    return opcode::ref(m_opcode) == opcode::Ref::String;
  }

  bool has_type() const { return opcode::ref(m_opcode) == opcode::Ref::Type; }

  bool has_field() const { return opcode::ref(m_opcode) == opcode::Ref::Field; }

  bool has_method() const {
    return opcode::ref(m_opcode) == opcode::Ref::Method;
  }

  bool has_literal() const {
    return opcode::ref(m_opcode) == opcode::Ref::Literal;
  }
  bool has_callsite() const {
    return opcode::ref(m_opcode) == opcode::Ref::CallSite;
  }
  bool has_methodhandle() const {
    return opcode::ref(m_opcode) == opcode::Ref::MethodHandle;
  }

  bool has_data() const { return opcode::ref(m_opcode) == opcode::Ref::Data; }

  bool has_proto() const { return opcode::ref(m_opcode) == opcode::Ref::Proto; }

  /*
   * Number of registers used.
   */
  bool has_dest() const { return opcode_impl::has_dest(m_opcode); }

  size_t srcs_size() const;

  bool has_move_result_pseudo() const {
    return opcode_impl::has_move_result_pseudo(m_opcode);
  }

  bool has_move_result() const {
    return has_method() || m_opcode == OPCODE_FILLED_NEW_ARRAY;
  }

  bool has_move_result_any() const {
    return has_move_result() || has_move_result_pseudo();
  }

  bool has_contiguous_range_srcs_denormalized() const {
    if (srcs_size() == 0) {
      return true;
    }
    auto last = src(0);
    for (size_t i = 1; i < srcs_size(); ++i) {
      if (src(i) - last != 1) {
        return false;
      }
      last = src(i);
    }
    return true;
  }

  /*
   * Information about operands.
   */

  // Invoke instructions treat wide registers differently than *-wide
  // instructions. They explicitly refer to both halves of a pair, rather than
  // just the lower half. This method returns true on both lower and upper
  // halves.
  bool invoke_src_is_wide(src_index_t i) const;

  bool src_is_wide(src_index_t i) const;
  bool dest_is_wide() const {
    always_assert(has_dest());
    return opcode_impl::dest_is_wide(m_opcode);
  }
  bool dest_is_object() const {
    always_assert(has_dest());
    return opcode_impl::dest_is_object(m_opcode);
  }
  bool is_wide() const {
    for (size_t i = 0; i < srcs_size(); i++) {
      if (src_is_wide(i)) {
        return true;
      }
    }
    return has_dest() && dest_is_wide();
  }

  /*
   * Accessors for logical parts of the instruction.
   */
  IROpcode opcode() const { return m_opcode; }
  reg_t dest() const {
    always_assert_log(has_dest(), "No dest for %s", show_opcode().c_str());
    return m_dest;
  }
  reg_t src(src_index_t i) const;

 private:
  using reg_range_super = boost::iterator_range<const reg_t*>;

 public:
  class reg_range : public reg_range_super {
    // Remove the bool conversion operator. It's too surprising and error-prone.
    operator bool() const = delete;
    // inherit the constructors
    using reg_range_super::reg_range_super;

   public:
    explicit reg_range(const std::vector<reg_t>& srcs)
        : reg_range_super(srcs.data(), srcs.data() + srcs.size()) {}
  };
  // Provides a read-only view into the source registers
  reg_range srcs() const;
  // Provides a copy of the source registers
  std::vector<reg_t> srcs_copy() const;
  IRInstruction* set_srcs(const reg_range&);
  IRInstruction* set_srcs(const std::vector<reg_t>& srcs) {
    return set_srcs(reg_range(srcs));
  }

  /*
   * Setters for logical parts of the instruction.
   */
  IRInstruction* set_opcode(IROpcode op) {
    m_opcode = op;
    return this;
  }
  IRInstruction* set_dest(reg_t reg) {
    always_assert(has_dest());
    m_dest = reg;
    return this;
  }
  IRInstruction* set_src(src_index_t i, reg_t reg);
  IRInstruction* set_srcs_size(size_t count);

  int64_t get_literal() const {
    always_assert(has_literal());
    return static_cast<int64_t>(m_literal);
  }

  IRInstruction* set_literal(int64_t literal) {
    always_assert(has_literal());
    m_literal = literal;
    return this;
  }

  const DexString* get_string() const {
    always_assert(has_string());
    return m_string;
  }

  IRInstruction* set_string(const DexString* str) {
    always_assert(has_string());
    m_string = str;
    return this;
  }

  const DexType* get_type() const {
    always_assert(has_type());
    return m_type;
  }

  IRInstruction* set_type(const DexType* type) {
    always_assert(has_type());
    m_type = type;
    return this;
  }

  DexFieldRef* get_field() const {
    always_assert(has_field());
    return m_field;
  }

  IRInstruction* set_field(DexFieldRef* field) {
    always_assert(has_field());
    m_field = field;
    return this;
  }

  DexMethodRef* get_method() const {
    always_assert(has_method());
    return m_method;
  }

  IRInstruction* set_method(DexMethodRef* method) {
    always_assert(has_method());
    m_method = method;
    return this;
  }

  DexCallSite* get_callsite() const {
    always_assert(has_callsite());
    return m_callsite;
  }

  IRInstruction* set_callsite(DexCallSite* callsite) {
    always_assert(has_callsite());
    m_callsite = callsite;
    return this;
  }

  DexMethodHandle* get_methodhandle() const {
    always_assert(has_methodhandle());
    return m_methodhandle;
  }

  IRInstruction* set_methodhandle(DexMethodHandle* methodhandle) {
    always_assert(has_methodhandle());
    m_methodhandle = methodhandle;
    return this;
  }

  DexOpcodeData* get_data() const {
    always_assert(has_data());
    return m_data;
  }

  IRInstruction* set_data(std::unique_ptr<DexOpcodeData> data);

  DexProto* get_proto() const {
    always_assert(has_proto());
    return m_proto;
  }

  IRInstruction* set_proto(DexProto* proto) {
    always_assert(has_proto());
    m_proto = proto;
    return this;
  }

  void gather_strings(std::vector<const DexString*>& lstring) const {
    if (has_string()) {
      lstring.push_back(m_string);
    }
  }

  void gather_types(std::vector<const DexType*>& ltype) const;

  void gather_init_classes(std::vector<const DexType*>& ltype) const;

  void gather_fields(std::vector<DexFieldRef*>& lfield) const;

  void gather_methods(std::vector<DexMethodRef*>& lmethod) const;

  void gather_callsites(std::vector<DexCallSite*>& lcallsite) const {
    if (has_callsite()) {
      lcallsite.push_back(m_callsite);
    }
  }

  void gather_methodhandles(std::vector<DexMethodHandle*>& lmethodhandle) const;

  void gather_protos(std::vector<DexProto*>& lproto) const {
    if (has_proto()) {
      lproto.push_back(m_proto);
    }
  }

  // Compute current instruction's hash.
  uint64_t hash() const;

 private:
  std::string show_opcode() const; // To avoid "Show.h" in the header.

  // 4 is chosen as it brings up the size of IRInstruction to 32 bytes (on a 64
  // bit system). We could bring it down to 24 with a maximum value of 2, but
  // jemalloc puts both 24-bytes and 32-byte objects into the same bucket. In
  // practice, most IRInstructions have 2 or fewer source registers, so we can
  // avoid a vector allocation most of the time.
  static constexpr uint8_t MAX_NUM_INLINE_SRCS = 4;

  // The fields of IRInstruction are carefully selected and ordered to avoid
  // empty packing bytes and minimize total size. This is optimized for 8 byte
  // alignment on a 64bit system.

  IROpcode m_opcode; // 2 bytes
  // If m_num_srcs > MAX_NUM_INLINE_SRCS, then the registers reside in an
  // out-of-line m_srcs array which is appropriately sized.
  src_index_t m_num_srcs{0}; // 2 bytes
  reg_t m_dest{0}; // 4 bytes
  // 8 bytes so far
  union {
    // Zero-initialize this union with the uint64_t member instead of a
    // pointer-type member so that it works properly even on 32-bit machines
    uint64_t m_literal{0};
    const DexString* m_string;
    const DexType* m_type;
    DexFieldRef* m_field;
    DexMethodRef* m_method;
    DexOpcodeData* m_data;
    DexCallSite* m_callsite;
    DexMethodHandle* m_methodhandle;
    DexProto* m_proto;
  };
  // 16 bytes so far
  union {
    // m_inline_srcs is used when m_num_srcs <= MAX_NUM_INLINE_SRCS
    reg_t m_inline_srcs[MAX_NUM_INLINE_SRCS] = {0};
    // m_srcs points to an array of srcs when m_num_srcs > MAX_NUM_INLINE_SRCS
    // Be careful to malloc and free it correctly!
    reg_t* m_srcs;
  };
  // 32 bytes total
};

/*
 * The number of bits required to encode the given value. I.e. the offset of
 * the most significant bit.
 */
bit_width_t required_bit_width(uint16_t v);

/*
 * Whether instruction must be converted to /range form in order to encode it
 * as a DexInstruction
 */
bool needs_range_conversion(const IRInstruction*);
