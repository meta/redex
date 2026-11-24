/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <charconv>
#include <cstring>
#include <memory>
#include <string>
#include <type_traits>
#include <utility>

#include "CppUtil.h"
#include "Debug.h"
#include "DexOpcode.h"
#include "Gatherable.h"
#include "IROpcode.h"

#define MAX_ARG_COUNT (4)

class DexIdx;
class DexOutputIdx;
class DexString;

class DexInstruction : public Gatherable {
 protected:
  enum {
    REF_NONE,
    REF_STRING,
    REF_TYPE,
    REF_FIELD,
    REF_METHOD,
    REF_CALLSITE,
    REF_METHODHANDLE,
    REF_PROTO,
  } m_ref_type{REF_NONE};

 private:
  uint16_t m_opcode = OPCODE_NOP;
  uint16_t m_arg[MAX_ARG_COUNT] = {};

 protected:
  uint16_t m_count = 0;

  // use clone() instead
  DexInstruction(const DexInstruction&) = default;
  DexInstruction& operator=(const DexInstruction&) = default;

  // Ref-less opcodes, largest size is 5 insns.
  // If the constructor is called with a non-numeric
  // count, we'll have to add an assert here.
  // Holds formats:
  // 10x 11x 11n 12x 22x 21s 21h 31i 32x 51l
  DexInstruction(const uint16_t* opcodes, int count) {
    always_assert_log(count <= MAX_ARG_COUNT,
                      "arg count %d exceeded the limit of %d",
                      count,
                      MAX_ARG_COUNT);
    m_opcode = *opcodes++;
    m_count = count;
    for (int i = 0; i < count; i++) {
      m_arg[i] = opcodes[i];
    }
  }

 public:
  explicit DexInstruction(DexOpcode op)
      : m_opcode(op), m_count(count_from_opcode()) {}

  DexInstruction(DexOpcode opcode, uint16_t arg) : DexInstruction(opcode) {
    redex_assert(m_count == 1);
    m_arg[0] = arg;
  }

 protected:
  void encode_args(uint16_t*& insns) const {
    for (int i = 0; i < m_count; i++) {
      *insns++ = m_arg[i];
    }
  }

  void encode_opcode(uint16_t*& insns) const { *insns++ = m_opcode; }

 public:
  static DexInstruction* make_instruction(DexIdx* idx,
                                          const uint16_t** insns_ptr,
                                          const uint16_t* end);
  /* Creates the right subclass of DexInstruction for the given opcode */
  static DexInstruction* make_instruction(DexOpcode);
  virtual void encode(DexOutputIdx* dodx, uint16_t*& insns) const;
  virtual size_t size() const;
  virtual DexInstruction* clone() const { return new DexInstruction(*this); }
  bool operator==(const DexInstruction&) const;

  bool has_string() const { return m_ref_type == REF_STRING; }
  bool has_type() const { return m_ref_type == REF_TYPE; }
  bool has_field() const { return m_ref_type == REF_FIELD; }
  bool has_method() const { return m_ref_type == REF_METHOD; }
  bool has_callsite() const { return m_ref_type == REF_CALLSITE; }
  bool has_methodhandle() const { return m_ref_type == REF_METHODHANDLE; }
  bool has_proto() const { return m_ref_type == REF_PROTO; }

  bool has_range() const { return dex_opcode::has_range(opcode()); }
  bool has_literal() const { return dex_opcode::has_literal(opcode()); }
  bool has_offset() const { return dex_opcode::has_offset(opcode()); }

  /*
   * Number of registers used.
   */
  bool has_dest() const;
  unsigned srcs_size() const;

  /*
   * Accessors for logical parts of the instruction.
   */
  DexOpcode opcode() const;
  uint16_t dest() const;
  uint16_t src(size_t i) const;
  uint16_t arg_word_count() const;
  uint16_t range_base() const;
  uint16_t range_size() const;
  int64_t get_literal() const;
  int32_t offset() const;

  /*
   * Setters for logical parts of the instruction.
   */
  DexInstruction* set_opcode(DexOpcode);
  DexInstruction* set_dest(uint16_t vreg);
  DexInstruction* set_src(size_t i, uint16_t vreg);
  DexInstruction* set_srcs(const std::vector<uint16_t>& vregs);
  DexInstruction* set_arg_word_count(uint16_t count);
  DexInstruction* set_range_base(uint16_t base);
  DexInstruction* set_range_size(uint16_t size);
  DexInstruction* set_literal(int64_t literal);
  DexInstruction* set_offset(int32_t offset);

  /*
   * The number of shorts needed to encode the args.
   */
  uint16_t count() const { return m_count; }

  friend std::string show(const DexInstruction* insn);
  friend std::string show_deobfuscated(const DexInstruction* insn);

 private:
  unsigned count_from_opcode() const;
};

class DexOpcodeString : public DexInstruction {
 private:
  const DexString* m_string;

 public:
  size_t size() const override;
  void encode(DexOutputIdx* dodx, uint16_t*& insns) const override;
  void gather_strings(std::vector<const DexString*>& lstring) const override;
  DexOpcodeString* clone() const override { return new DexOpcodeString(*this); }

  DexOpcodeString(DexOpcode opcode, const DexString* str)
      : DexInstruction(opcode) {
    m_string = str;
    m_ref_type = REF_STRING;
  }

  const DexString* get_string() const { return m_string; }

  bool jumbo() const { return opcode() == DOPCODE_CONST_STRING_JUMBO; }

  void set_string(const DexString* str) { m_string = str; }
};

class DexOpcodeType : public DexInstruction {
 private:
  const DexType* m_type;

 public:
  size_t size() const override;
  void encode(DexOutputIdx* dodx, uint16_t*& insns) const override;
  void gather_types(std::vector<const DexType*>& ltype) const override;
  DexOpcodeType* clone() const override { return new DexOpcodeType(*this); }

  DexOpcodeType(DexOpcode opcode, const DexType* type)
      : DexInstruction(opcode) {
    m_type = type;
    m_ref_type = REF_TYPE;
  }

  DexOpcodeType(DexOpcode opcode, const DexType* type, uint16_t arg)
      : DexInstruction(opcode, arg) {
    m_type = type;
    m_ref_type = REF_TYPE;
  }

  const DexType* get_type() const { return m_type; }

  void set_type(const DexType* type) { m_type = type; }
};

class DexOpcodeField : public DexInstruction {
 private:
  DexFieldRef* m_field;

 public:
  size_t size() const override;
  void encode(DexOutputIdx* dodx, uint16_t*& insns) const override;
  void gather_fields(std::vector<DexFieldRef*>& lfield) const override;
  DexOpcodeField* clone() const override { return new DexOpcodeField(*this); }

  DexOpcodeField(DexOpcode opcode, DexFieldRef* field)
      : DexInstruction(opcode) {
    m_field = field;
    m_ref_type = REF_FIELD;
  }

  DexFieldRef* get_field() const { return m_field; }
  void set_field(DexFieldRef* field) { m_field = field; }
};

class DexOpcodeMethod : public DexInstruction {
 private:
  DexMethodRef* m_method;

 public:
  size_t size() const override;
  void encode(DexOutputIdx* dodx, uint16_t*& insns) const override;
  void gather_methods(std::vector<DexMethodRef*>& lmethod) const override;
  DexOpcodeMethod* clone() const override { return new DexOpcodeMethod(*this); }

  DexOpcodeMethod(DexOpcode opcode, DexMethodRef* meth, uint16_t arg = 0)
      : DexInstruction(opcode, arg) {
    m_method = meth;
    m_ref_type = REF_METHOD;
  }

  DexMethodRef* get_method() const { return m_method; }

  void set_method(DexMethodRef* method) { m_method = method; }
};

// `invoke-polymorphic` and `invoke-polymorphic/range` (formats 45cc and 4rcc):
// a signature-polymorphic method, the argument registers, and the prototype of
// the call site.
class DexOpcodeSignaturePolymorphic : public DexOpcodeMethod {
 private:
  DexProto* m_callsite_proto;

 public:
  size_t size() const override;
  void encode(DexOutputIdx* dodx, uint16_t*& insns) const override;
  void gather_protos(std::vector<DexProto*>& lproto) const override;
  DexOpcodeSignaturePolymorphic* clone() const override {
    return new DexOpcodeSignaturePolymorphic(*this);
  }

  DexOpcodeSignaturePolymorphic(DexOpcode opcode,
                                DexMethodRef* meth,
                                DexProto* callsite_proto,
                                uint16_t arg = 0)
      : DexOpcodeMethod(opcode, meth, arg), m_callsite_proto(callsite_proto) {}

  DexProto* get_callsite_proto() const { return m_callsite_proto; }
};

class DexOpcodeCallSite : public DexInstruction {
 private:
  DexCallSite* m_callsite;

 public:
  size_t size() const override;
  void encode(DexOutputIdx* dodx, uint16_t*& insns) const override;
  void gather_callsites(std::vector<DexCallSite*>& lcallsite) const override;
  void gather_strings(std::vector<const DexString*>& lstring) const override;
  void gather_methodhandles(
      std::vector<DexMethodHandle*>& lmethodhandle) const override;
  void gather_methods(std::vector<DexMethodRef*>& lmethod) const override;
  void gather_fields(std::vector<DexFieldRef*>& lfield) const override;
  DexOpcodeCallSite* clone() const override {
    return new DexOpcodeCallSite(*this);
  }

  DexOpcodeCallSite(DexOpcode opcode, DexCallSite* callsite, uint16_t arg = 0)
      : DexInstruction(opcode, arg) {
    m_callsite = callsite;
    m_ref_type = REF_CALLSITE;
  }

  DexCallSite* get_callsite() const { return m_callsite; }

  void set_callsite(DexCallSite* callsite) { m_callsite = callsite; }
};

class DexOpcodeMethodHandle : public DexInstruction {
 private:
  DexMethodHandle* m_methodhandle;

 public:
  size_t size() const override;
  void encode(DexOutputIdx* dodx, uint16_t*& insns) const override;
  void gather_methodhandles(
      std::vector<DexMethodHandle*>& lmethodhandle) const override;
  void gather_methods(std::vector<DexMethodRef*>& lmethod) const override;
  void gather_fields(std::vector<DexFieldRef*>& lfield) const override;
  DexOpcodeMethodHandle* clone() const override {
    return new DexOpcodeMethodHandle(*this);
  }

  DexOpcodeMethodHandle(DexOpcode opcode, DexMethodHandle* methodhandle)
      : DexInstruction(opcode) {
    m_methodhandle = methodhandle;
    m_ref_type = REF_METHODHANDLE;
  }

  DexMethodHandle* get_methodhandle() const { return m_methodhandle; }

  void set_methodhandle(DexMethodHandle* methodhandle) {
    m_methodhandle = methodhandle;
  }
};

class DexOpcodeData : public DexInstruction {
 private:
  std::unique_ptr<uint16_t[]> m_data;
  size_t m_data_count;

 public:
  // This size refers to the whole instruction, not just the data portion
  size_t size() const override;
  void encode(DexOutputIdx* dodx, uint16_t*& insns) const override;
  DexOpcodeData* clone() const override { return new DexOpcodeData(*this); }
  std::unique_ptr<DexOpcodeData> clone_as_unique_ptr() const {
    return std::make_unique<DexOpcodeData>(*this);
  }

  DexOpcodeData(const uint16_t* opcodes, size_t count)
      : DexInstruction(opcodes, 0),
        m_data(std::make_unique<uint16_t[]>(count)),
        m_data_count(count) {
    opcodes++;
    memcpy(m_data.get(), opcodes, count * sizeof(uint16_t));
  }

  explicit DexOpcodeData(const std::vector<uint16_t>& opcodes)
      : DexInstruction(opcodes.data(), 0),
        m_data(std::make_unique<uint16_t[]>(opcodes.size() - 1)),
        m_data_count(opcodes.size() - 1) {
    const uint16_t* data = opcodes.data() + 1;
    memcpy(m_data.get(), data, (opcodes.size() - 1) * sizeof(uint16_t));
  }

  DexOpcodeData(const DexOpcodeData& op)
      : DexInstruction(op),
        m_data(std::make_unique<uint16_t[]>(op.m_data_count)),
        m_data_count(op.m_data_count) {
    memcpy(m_data.get(), op.m_data.get(), m_data_count * sizeof(uint16_t));
  }

  DexOpcodeData& operator=(DexOpcodeData op) {
    DexInstruction::operator=(op);
    std::swap(m_data, op.m_data);
    return *this;
  }

  const uint16_t* data() const { return m_data.get(); }
  // This size refers to just the length of the data array
  size_t data_size() const { return m_data_count; }
};

class DexOpcodeProto : public DexInstruction {
 private:
  DexProto* m_proto;

 public:
  size_t size() const override;
  void encode(DexOutputIdx* dodx, uint16_t*& insns) const override;
  void gather_strings(std::vector<const DexString*>& lstring) const override;
  void gather_protos(std::vector<DexProto*>& lproto) const override;

  DexOpcodeProto* clone() const override { return new DexOpcodeProto(*this); }

  DexOpcodeProto(DexOpcode opcode, DexProto* proto) : DexInstruction(opcode) {
    m_proto = proto;
    m_ref_type = REF_PROTO;
  }

  DexProto* get_proto() const { return m_proto; }

  void set_proto(DexProto* proto) { m_proto = proto; }
};

inline uint16_t fill_array_data_payload_width(const DexOpcodeData* op_data) {
  always_assert_log(op_data->opcode() == FOPCODE_FILLED_ARRAY,
                    "DexOpcodeData is not an array payload");
  always_assert(op_data->data_size() >= 3);
  return *op_data->data();
}

inline uint32_t fill_array_data_payload_element_count(
    const DexOpcodeData* op_data) {
  always_assert_log(op_data->opcode() == FOPCODE_FILLED_ARRAY,
                    "DexOpcodeData is not an array payload");
  always_assert(op_data->data_size() >= 3);
  const auto* size_ptr = reinterpret_cast<const uint32_t*>(op_data->data() + 1);
  return *size_ptr;
}

// helper function to create fill-array-data-payload according to
// https://source.android.com/devices/tech/dalvik/dalvik-bytecode#fill-array
template <typename IntType>
std::unique_ptr<DexOpcodeData> encode_fill_array_data_payload(
    const std::vector<IntType>& vec) {
  static_assert(std::is_integral<IntType>::value,
                "fill-array-data-payload can only contain integral values.");
  int width = sizeof(IntType);
  size_t total_copy_size = vec.size() * width;
  // one "code unit" is a 2 byte word
  int total_used_code_units = static_cast<int>(
      (total_copy_size + 1 /* for rounding up int division */) / 2 + 4);
  std::vector<uint16_t> data(total_used_code_units);
  uint16_t* ptr = data.data();
  ptr[0] = FOPCODE_FILLED_ARRAY; // header
  ptr[1] = width;
  *reinterpret_cast<uint32_t*>(ptr + 2) = vec.size();
  uint8_t* data_bytes = reinterpret_cast<uint8_t*>(ptr + 4);
  memcpy(data_bytes, vec.data(), total_copy_size);
  return std::make_unique<DexOpcodeData>(data);
}

// Like above, but parse from a vector of hex string elements
template <typename IntType>
std::unique_ptr<DexOpcodeData> encode_fill_array_data_payload_from_string(
    const std::vector<std::string>& elements) {
  static_assert(std::is_integral<IntType>::value,
                "fill-array-data-payload can only contain integral values.");
  std::vector<IntType> vec;
  for (const auto& item : elements) {
    IntType val;
    auto trimmed = trim_whitespaces(item);
    auto result = std::from_chars(trimmed.data(),
                                  trimmed.data() + trimmed.size(), val, 16);
    always_assert_log(result.ec != std::errc::invalid_argument,
                      "Invalid payload: \"%s\"", item.c_str());
    vec.emplace_back(val);
  }
  return encode_fill_array_data_payload(vec);
}

template <typename IntType>
std::vector<IntType> get_fill_array_data_payload(const DexOpcodeData* op_data) {
  static_assert(std::is_integral<IntType>::value,
                "fill-array-data-payload can only contain integral values.");
  int width = sizeof(IntType);
  const auto* data = op_data->data();
  always_assert_log(*data++ == width, "Incorrect width");
  auto count = *reinterpret_cast<const uint32_t*>(data);
  data += 2;
  std::vector<IntType> vec;
  vec.reserve(count);
  const auto* element_data = reinterpret_cast<const uint8_t*>(data);
  for (size_t i = 0; i < count; i++) {
    IntType result = 0;
    memcpy(&result, element_data, width);
    vec.emplace_back(result);
    element_data += width;
  }
  return vec;
}

/**
 * Return a copy of the instruction passed in.
 */
DexInstruction* copy_insn(DexInstruction* insn);
