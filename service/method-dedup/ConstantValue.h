/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "ControlFlow.h"
#include "IRCode.h"
#include "MethodReference.h"
#include "TypeTags.h"
#include "TypeUtil.h"

namespace constant_uses {
class ConstantUses;
} // namespace constant_uses

class ConstantValue {

  /////////////////////////////////////////////////////////////////////////
  // The kind of constant value emitted in the @MethodMeta annotation.
  //
  // INT: @MethodMeta(constantTypes = "I", constantValues = "42")
  //       A 64 bit integer constant like an offset or hash code.
  // TYPE: @MethodMeta(constantTypes = "T",
  //                   constantValues = "Lcom/facebook/CommentModels$ModelA;")
  //       The constant in the annotated method is a reference to a mergeable
  //       type. We only process if the refernced type is merged to a Shape.
  //       In that case, the type reference becomes the type tag constant and a
  //       reference to the merger type. As a result, the type tag integer
  //       constant is the only constant value we need to lift.
  //       The Type case can be considered as a special Int case, where type tag
  //       become the only constant making the annotated methods different from
  //       each other after merging.
  //       This is specially useful when the type tags are not accessible from
  //       the code-gen.
  // STRING: @MethodMeta(constantTypes = "S", constantValues = "post_id")
  //         A string constant like the name of a parameter.
  // INVALID:
  //        Whenever the annotated value cannot be processed. For instance, the
  //        emitted Type cannot be found or is not merged.
  //
  // Note: must be an enum class to not shadow TYPE used in Trace.
  enum class ConstantKind { INT, TYPE, STRING, INVALID };

 public:
  // The insn and the dest. OPCODE_CONST_STRING does not have a dest in itself.
  using ConstantLoad = std::pair<cfg::InstructionIterator, reg_t>;

  ConstantValue(const TypeTags* type_tags,
                const std::string& kind_str,
                const std::string& val_str,
                reg_t param_reg);

  bool is_int_value() const {
    return m_kind == ConstantKind::INT || m_kind == ConstantKind::TYPE;
  }
  bool is_str_value() const { return m_kind == ConstantKind::STRING; }
  int64_t get_int_value() {
    always_assert(is_int_value());
    return m_int_val;
  }
  bool is_int_kind() { return m_kind == ConstantKind::INT; }
  bool is_invalid() const { return m_kind == ConstantKind::INVALID; }
  bool is_valid() const { return !is_invalid(); }
  std::string get_str_value() {
    always_assert(is_str_value());
    return m_str_val;
  }
  DexType* get_constant_type() const {
    if (is_int_value()) {
      return type::_int();
    } else {
      return type::java_lang_String();
    }
  }

  // An int constant matches only a `const` whose uses all accept an `int`
  // parameter in its place; `uses` describes the uses in `cfg` and is needed
  // only for an int constant.
  std::vector<ConstantLoad> collect_constant_loads_in(
      cfg::ControlFlowGraph& cfg, const constant_uses::ConstantUses* uses);

  std::vector<IRInstruction*> make_load_const(reg_t const_reg);

  reg_t get_param_reg() const { return m_param_reg; }

  std::string to_str() const {
    std::ostringstream ss;
    if (is_int_value()) {
      ss << m_int_val;
    } else if (is_str_value()) {
      ss << m_str_val;
    } else {
      ss << "invalid";
    }
    return ss.str();
  }

 private:
  ConstantKind m_kind;
  int64_t m_int_val;
  std::string m_str_val;
  // The allocated param reg holding the original value of the constant.
  reg_t m_param_reg;
};

class ConstantValues {

  using ConstantValueLoad =
      std::pair<ConstantValue, ConstantValue::ConstantLoad>;

 public:
  ConstantValues(const TypeTags* type_tags,
                 const std::string& kinds_str,
                 const std::string& vals_str,
                 const size_t stud_method_threshold,
                 cfg::ControlFlowGraph& cfg);

  std::vector<ConstantValueLoad> collect_constant_loads(DexMethod* method);

  std::vector<ConstantValue> get_constant_values() const {
    return m_const_vals;
  }

  std::vector<const DexType*> get_constant_types() {
    std::vector<const DexType*> res;
    for (const auto& c : m_const_vals) {
      if (c.is_invalid()) {
        continue;
      }
      res.push_back(c.get_constant_type());
    }
    return res;
  }

  std::vector<IRInstruction*> make_const_loads(std::vector<reg_t>& const_regs);

  size_t size() const {
    size_t res = 0;
    for (const auto& c : m_const_vals) {
      if (c.is_valid()) {
        ++res;
      }
    }
    return res;
  }

  std::string to_str() {
    std::ostringstream ss;
    ss << "(";
    for (const auto& c : m_const_vals) {
      ss << c.to_str();
      ss << ",";
    }
    ss.seekp(-1, std::ios_base::end);
    ss << ")";
    return ss.str();
  }

  bool needs_stub() const { return size() >= m_stub_method_threshold; }

  DexMethod* create_stub_method(DexMethod* callee);

 private:
  std::vector<ConstantValue> m_const_vals;
  /**
   * This is a hack. The issue is CFP will replace reference to its removed type
   * to a `const 0`. This change conflicts with the parsing of constant loads
   * when the annotated constant is an int of value 0. In this case, constant
   * lifting will replace the `wrong const 0` to a move from the lifted int
   * param. This unexpected transformation leads to a type violation detected by
   * the IRTypeChecker. What we need to do here is whenever we failed to find a
   * type constant, we will skip replacing multiple `const 0`, which will likely
   * lead to the above mentioned bug.
   */
  bool m_skip_multiple_const_0 = false;

  size_t m_stub_method_threshold;
};
