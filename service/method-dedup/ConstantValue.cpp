/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ConstantValue.h"

#include <optional>

#include <boost/algorithm/string.hpp>

#include "ConstantUses.h"
#include "Creators.h"
#include "Debug.h"
#include "DexAsm.h"
#include "Show.h"
#include "Trace.h"

using namespace dex_asm;

namespace {

constexpr uint64_t MAX_NUM_CONST_VALUE = 10;

std::vector<IRInstruction*> make_string_const(reg_t dest,
                                              const std::string& val) {
  std::vector<IRInstruction*> res;
  auto* load = dasm(OPCODE_CONST_STRING, DexString::make_string(val));
  auto* move_res = dasm(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT, {{VREG, dest}});
  res.push_back(load);
  res.push_back(move_res);
  return res;
}

} // namespace

ConstantValue::ConstantValue(const TypeTags* type_tags,
                             const std::string& kind_str,
                             const std::string& val_str,
                             reg_t param_reg)
    : m_param_reg(param_reg) {
  if (kind_str == "I") {
    m_kind = ConstantKind::INT;
    m_int_val = std::stoll(val_str);
  } else if (kind_str == "T") {
    auto* type_val = DexType::get_type(val_str);
    if (type_val != nullptr && type_tags->has_type_tag(type_val)) {
      m_kind = ConstantKind::TYPE;
      m_int_val = type_tags->get_type_tag(type_val);
      if (m_int_val == 0) {
        TRACE(METH_DEDUP, 9, "const value: skipping type tag value of 0");
        m_kind = ConstantKind::INVALID;
      }
      return;
    } else if (type_val == nullptr) {
      TRACE(METH_DEDUP,
            9,
            "const value: unable to find type %s",
            val_str.c_str());
    } else {
      TRACE(
          METH_DEDUP, 9, "const value: no type tag found %s", val_str.c_str());
    }
    // Cannot find type or not type tag.
    m_kind = ConstantKind::INVALID;
  } else if (kind_str == "S") {
    m_kind = ConstantKind::STRING;
    m_str_val = val_str;
  } else {
    always_assert_log(
        kind_str.size() > 1, "Unexpected kind str %s\n", kind_str.c_str());
    TRACE(METH_DEDUP,
          9,
          "const lift: trying to decode more than one kind %s",
          kind_str.c_str());
    m_kind = ConstantKind::INVALID;
  }
}

std::vector<ConstantValue::ConstantLoad>
ConstantValue::collect_constant_loads_in(
    cfg::ControlFlowGraph& cfg, const constant_uses::ConstantUses* uses) {
  always_assert(!is_int_value() || uses != nullptr);
  std::vector<ConstantValue::ConstantLoad> res;
  always_assert(is_valid());
  auto ii = InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    auto* insn = it->insn;
    if (is_int_value() && insn->opcode() == OPCODE_CONST) {
      int64_t literal = insn->get_literal();
      // Special handling for type tags to avoid sign extensionon on int64_t.
      if (m_kind == ConstantKind::TYPE) {
        literal = static_cast<uint32_t>(literal);
      }
      if (literal == m_int_val && uses->accepts_any_int(insn)) {
        res.emplace_back(it, insn->dest());
      }
    } else if (is_str_value() && insn->opcode() == OPCODE_CONST_STRING) {
      if (strcmp(insn->get_string()->c_str(), m_str_val.c_str()) == 0) {
        auto* pseudo_move = cfg.move_result_of(it)->insn;
        always_assert(pseudo_move->opcode() ==
                      IOPCODE_MOVE_RESULT_PSEUDO_OBJECT);
        res.emplace_back(it, pseudo_move->dest());
      }
    }
  }

  return res;
}

std::vector<IRInstruction*> ConstantValue::make_load_const(reg_t const_reg) {
  always_assert(is_valid());

  if (is_int_value()) {
    std::vector<IRInstruction*> res;
    auto* load = method_reference::make_load_const(const_reg, m_int_val);
    res.push_back(load);
    return res;
  } else {
    return make_string_const(const_reg, m_str_val);
  }
}

ConstantValues::ConstantValues(const TypeTags* type_tags,
                               const std::string& kinds_str,
                               const std::string& vals_str,
                               const size_t stud_method_threshold,
                               cfg::ControlFlowGraph& cfg)
    : m_stub_method_threshold(stud_method_threshold) {
  // Split vals_str.
  std::vector<std::string> vals_vec;
  boost::split(vals_vec, vals_str, [](char c) { return c == ':'; });
  always_assert(vals_vec.size() == kinds_str.length());

  if (kinds_str.size() > MAX_NUM_CONST_VALUE) {
    TRACE(METH_DEDUP,
          8,
          "const value: skip large number of const values %zu",
          kinds_str.size());
    return;
  }

  // Build kind_to_val pairs.
  std::vector<std::pair<std::string, std::string>> kind_to_val;
  auto vals_it = vals_vec.begin();
  for (std::string::const_iterator it = kinds_str.begin();
       it != kinds_str.end();
       ++it) {
    std::string kind_str = std::string(1, *it);
    kind_to_val.emplace_back(kind_str, *vals_it);
    ++vals_it;
  }

  // Populate the const_vals set.
  for (auto& pair : kind_to_val) {
    auto param_reg = cfg.allocate_temp();
    ConstantValue cval(type_tags, pair.first, pair.second, param_reg);
    m_const_vals.emplace_back(cval);
    if (cval.is_invalid()) {
      m_skip_multiple_const_0 = true;
      TRACE(METH_DEDUP, 9, "const value: skip multiple const 0");
    }
  }
}

std::vector<ConstantValues::ConstantValueLoad>
ConstantValues::collect_constant_loads(DexMethod* method) {
  auto& cfg = method->get_code()->cfg();
  std::vector<ConstantValueLoad> const_val_loads;
  std::optional<constant_uses::ConstantUses> uses;
  UnorderedSet<IRInstruction*> matched_loads;
  for (auto& const_val : m_const_vals) {
    if (const_val.is_invalid()) {
      continue;
    }
    if (const_val.is_int_value() && !uses) {
      uses.emplace(cfg, method);
    }
    auto const_loads =
        const_val.collect_constant_loads_in(cfg, uses ? &*uses : nullptr);
    if (m_skip_multiple_const_0 && const_val.is_int_kind() &&
        const_val.get_int_value() == 0 && !const_loads.empty()) {
      const_val_loads.emplace_back(const_val, const_loads.front());
      TRACE(METH_DEDUP, 9, "const value: skip const 0 loads");
      continue;
    }
    for (auto& load : const_loads) {
      if (matched_loads.count(load.first->insn) > 0) {
        // If the same const load insn has been matched for multiple const
        // values in the @MethodMeta annotation, we skip it.
        // Trying to lift the same const load insn later will lead to a crash.
        continue;
      }
      const_val_loads.emplace_back(const_val, load);
      TRACE(METH_DEDUP,
            9,
            "const value: %s matched with const-load %s",
            const_val.to_str().c_str(),
            SHOW(load.first->insn));
      matched_loads.insert(load.first->insn);
    }
  }
  return const_val_loads;
}

std::vector<IRInstruction*> ConstantValues::make_const_loads(
    std::vector<reg_t>& const_regs) {
  always_assert(const_regs.size() == size());
  std::vector<IRInstruction*> res;
  size_t reg_idx = 0;
  for (auto& cval : m_const_vals) {
    if (cval.is_valid()) {
      auto loads = cval.make_load_const(const_regs.at(reg_idx++));
      res.insert(res.end(), loads.begin(), loads.end());
    }
  }
  return res;
}

/**
 * Will return a newly created method that loads the argument values and
 * passes them to the `callee` method.
 *
 *   <ret_type> <method_name>$redex(<method_args>...) {
 *      const-* <local_reg_0> field_1_data
 *      const-* <local_reg_1> field_2_data
 *      ...
 *      invoke-static <callee> <method_args ...> <local_regs ...>
 *   }
 */
DexMethod* ConstantValues::create_stub_method(DexMethod* callee) {
  DexType* type = callee->get_class();
  // Assuming that callee's proto is already modified by appending the lifted
  // params.
  auto* appended_proto = callee->get_proto();
  auto* stub_arg_list = appended_proto->get_args()->pop_back(size());
  auto* stub_proto =
      DexProto::make_proto(appended_proto->get_rtype(), stub_arg_list);
  const auto* name =
      DexString::make_string(callee->get_name()->str() + "$stub");
  name = DexMethod::get_unique_name(type, name, stub_proto);
  TRACE(METH_DEDUP, 9, "const value: stub name %s", name->c_str());
  auto mc = MethodCreator(type,
                          name,
                          stub_proto,
                          callee->get_access(),
                          /* anno=*/nullptr,
                          /* with_debug_item= */ false);
  auto* mb = mc.get_main_block();
  // Setup args for calling the callee.
  size_t arg_loc = 0;
  std::vector<Location> args;
  if (!is_static(callee)) {
    args.push_back(mc.get_local(arg_loc++));
  }
  for (size_t i = 0; i < stub_arg_list->size(); ++i) {
    args.push_back(mc.get_local(arg_loc++));
  }
  for (auto& cval : m_const_vals) {
    if (cval.is_invalid()) {
      continue;
    }
    auto loc = mc.make_local(cval.get_constant_type());
    if (cval.is_int_value()) {
      mb->load_const(loc, static_cast<int32_t>(cval.get_int_value()));
    } else {
      mb->load_const(loc, DexString::make_string(cval.get_str_value()));
    }
    args.push_back(loc);
  }
  mb->invoke(callee, args);

  DexType* ret_type = callee->get_proto()->get_rtype();
  if (ret_type == type::_void()) {
    mb->ret_void();
  } else {
    auto ret_loc = mc.make_local(ret_type);
    mb->move_result(ret_loc, ret_type);
    mb->ret(ret_type, ret_loc);
  }

  auto* stub = mc.create();
  // Propogate deobfuscated name
  const auto orig_name = callee->get_deobfuscated_name_or_empty();
  auto pos = orig_name.find(':');
  always_assert(pos != std::string::npos);
  auto new_name =
      orig_name.substr(0, pos) + "$stub" + ":" + show_deobfuscated(stub_proto);
  stub->set_deobfuscated_name(new_name);
  TRACE(METH_DEDUP, 9, "stub's new deobfuscated name %s", new_name.c_str());
  // Add stub to class
  type_class(type)->add_method(stub);
  TRACE(METH_DEDUP,
        9,
        "const value: created stub %s\n%s",
        SHOW(stub),
        SHOW(stub->get_code()));
  return stub;
}
