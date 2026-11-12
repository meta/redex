/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "CheckCastAnalysis.h"

#include "Debug.h"
#include "FrameworkApi.h"
#include "ReachingDefinitions.h"
#include "Show.h"

namespace check_casts {

namespace impl {

// Nullptr indicates that the type demand could not be computed exactly, and no
// weakening should take place.
const DexType* CheckCastAnalysis::get_type_demand(IRInstruction* insn,
                                                  size_t src_index) const {
  always_assert(src_index < insn->srcs_size());
  switch (insn->opcode()) {
  case OPCODE_GOTO:
  case IOPCODE_LOAD_PARAM:
  case IOPCODE_LOAD_PARAM_OBJECT:
  case IOPCODE_LOAD_PARAM_WIDE:
  case OPCODE_NOP:
  case IOPCODE_MOVE_RESULT_PSEUDO:
  case OPCODE_MOVE_RESULT:
  case IOPCODE_MOVE_RESULT_PSEUDO_OBJECT:
  case OPCODE_MOVE_RESULT_OBJECT:
  case IOPCODE_MOVE_RESULT_PSEUDO_WIDE:
  case OPCODE_MOVE_RESULT_WIDE:
  case OPCODE_MOVE_EXCEPTION:
  case OPCODE_RETURN_VOID:
  case IOPCODE_R_CONST:
  case OPCODE_CONST:
  case OPCODE_CONST_WIDE:
  case OPCODE_CONST_STRING:
  case OPCODE_CONST_CLASS:
  case OPCODE_NEW_INSTANCE:
  case OPCODE_SGET:
  case OPCODE_SGET_BOOLEAN:
  case OPCODE_SGET_BYTE:
  case OPCODE_SGET_CHAR:
  case OPCODE_SGET_SHORT:
  case OPCODE_SGET_WIDE:
  case OPCODE_SGET_OBJECT:
  case OPCODE_RETURN:
  case OPCODE_RETURN_WIDE:
  case OPCODE_MOVE:
  case OPCODE_MOVE_WIDE:
  case OPCODE_NEW_ARRAY:
  case OPCODE_SWITCH:
  case OPCODE_NEG_INT:
  case OPCODE_NOT_INT:
  case OPCODE_INT_TO_BYTE:
  case OPCODE_INT_TO_CHAR:
  case OPCODE_INT_TO_SHORT:
  case OPCODE_INT_TO_LONG:
  case OPCODE_INT_TO_FLOAT:
  case OPCODE_INT_TO_DOUBLE:
  case OPCODE_ADD_INT:
  case OPCODE_SUB_INT:
  case OPCODE_MUL_INT:
  case OPCODE_AND_INT:
  case OPCODE_OR_INT:
  case OPCODE_XOR_INT:
  case OPCODE_SHL_INT:
  case OPCODE_SHR_INT:
  case OPCODE_USHR_INT:
  case OPCODE_DIV_INT:
  case OPCODE_REM_INT:
  case OPCODE_ADD_INT_LIT:
  case OPCODE_RSUB_INT_LIT:
  case OPCODE_MUL_INT_LIT:
  case OPCODE_AND_INT_LIT:
  case OPCODE_OR_INT_LIT:
  case OPCODE_XOR_INT_LIT:
  case OPCODE_SHL_INT_LIT:
  case OPCODE_SHR_INT_LIT:
  case OPCODE_USHR_INT_LIT:
  case OPCODE_DIV_INT_LIT:
  case OPCODE_REM_INT_LIT:
  case OPCODE_CMPL_FLOAT:
  case OPCODE_CMPG_FLOAT:
  case OPCODE_NEG_FLOAT:
  case OPCODE_FLOAT_TO_INT:
  case OPCODE_FLOAT_TO_LONG:
  case OPCODE_FLOAT_TO_DOUBLE:
  case OPCODE_ADD_FLOAT:
  case OPCODE_SUB_FLOAT:
  case OPCODE_MUL_FLOAT:
  case OPCODE_DIV_FLOAT:
  case OPCODE_REM_FLOAT:
  case OPCODE_CMPL_DOUBLE:
  case OPCODE_CMPG_DOUBLE:
  case OPCODE_NEG_DOUBLE:
  case OPCODE_DOUBLE_TO_INT:
  case OPCODE_DOUBLE_TO_LONG:
  case OPCODE_DOUBLE_TO_FLOAT:
  case OPCODE_ADD_DOUBLE:
  case OPCODE_SUB_DOUBLE:
  case OPCODE_MUL_DOUBLE:
  case OPCODE_DIV_DOUBLE:
  case OPCODE_REM_DOUBLE:
  case OPCODE_CMP_LONG:
  case OPCODE_NEG_LONG:
  case OPCODE_NOT_LONG:
  case OPCODE_LONG_TO_INT:
  case OPCODE_LONG_TO_FLOAT:
  case OPCODE_LONG_TO_DOUBLE:
  case OPCODE_ADD_LONG:
  case OPCODE_SUB_LONG:
  case OPCODE_MUL_LONG:
  case OPCODE_AND_LONG:
  case OPCODE_OR_LONG:
  case OPCODE_XOR_LONG:
  case OPCODE_DIV_LONG:
  case OPCODE_REM_LONG:
  case OPCODE_SHL_LONG:
  case OPCODE_SHR_LONG:
  case OPCODE_USHR_LONG:
  case OPCODE_IF_LTZ:
  case OPCODE_IF_GEZ:
  case OPCODE_IF_GTZ:
  case OPCODE_IF_LEZ:
  case OPCODE_IF_LT:
  case OPCODE_IF_GE:
  case OPCODE_IF_GT:
  case OPCODE_IF_LE:
  case OPCODE_SPUT:
  case OPCODE_SPUT_BOOLEAN:
  case OPCODE_SPUT_BYTE:
  case OPCODE_SPUT_CHAR:
  case OPCODE_SPUT_SHORT:
  case OPCODE_SPUT_WIDE:
  case IOPCODE_INIT_CLASS:
  case IOPCODE_INJECTION_ID:
  case IOPCODE_UNREACHABLE:
  case IOPCODE_WRITE_BARRIER:
    not_reached();

  case OPCODE_FILLED_NEW_ARRAY:
    return type::make_array_component_type(insn->get_type());

  case OPCODE_RETURN_OBJECT:
    return m_rtype;

  case OPCODE_MOVE_OBJECT:
  case OPCODE_MONITOR_ENTER:
  case OPCODE_MONITOR_EXIT:
    return type::java_lang_Object();

  case OPCODE_ARRAY_LENGTH:
  case OPCODE_FILL_ARRAY_DATA:
  case OPCODE_AGET:
  case OPCODE_AGET_BOOLEAN:
  case OPCODE_AGET_BYTE:
  case OPCODE_AGET_CHAR:
  case OPCODE_AGET_SHORT:
  case OPCODE_AGET_WIDE:
  case OPCODE_AGET_OBJECT:
    return nullptr;

  case OPCODE_THROW:
    return type::java_lang_Throwable();

  case OPCODE_IGET:
  case OPCODE_IGET_BOOLEAN:
  case OPCODE_IGET_BYTE:
  case OPCODE_IGET_CHAR:
  case OPCODE_IGET_SHORT:
  case OPCODE_IGET_WIDE:
  case OPCODE_IGET_OBJECT:
    return insn->get_field()->get_class();

  case OPCODE_INSTANCE_OF:
  case OPCODE_CHECK_CAST:
  case OPCODE_IF_EQ:
  case OPCODE_IF_NE:
  case OPCODE_IF_EQZ:
  case OPCODE_IF_NEZ:
    return type::java_lang_Object();

  case OPCODE_APUT_OBJECT:
    if (src_index == 0) {
      // There seems to be very little static verification for this
      // instruction, as most is deferred to runtime.
      // https://android.googlesource.com/platform/dalvik/+/android-cts-4.4_r4/vm/analysis/CodeVerify.cpp#186
      // So, we can just get away with the following:
      return type::java_lang_Object();
    }
    if (src_index == 1) {
      return DexType::make_type("[Ljava/lang/Object;");
    }
    BOOST_FALLTHROUGH;
  case OPCODE_APUT:
  case OPCODE_APUT_BOOLEAN:
  case OPCODE_APUT_BYTE:
  case OPCODE_APUT_CHAR:
  case OPCODE_APUT_SHORT:
  case OPCODE_APUT_WIDE:
    return nullptr;

  case OPCODE_IPUT_OBJECT:
    if (src_index == 0) {
      return insn->get_field()->get_type();
    }
    BOOST_FALLTHROUGH;
  case OPCODE_IPUT:
  case OPCODE_IPUT_BOOLEAN:
  case OPCODE_IPUT_BYTE:
  case OPCODE_IPUT_CHAR:
  case OPCODE_IPUT_SHORT:
  case OPCODE_IPUT_WIDE:
    if (src_index == 1) {
      return insn->get_field()->get_class();
    }
    return nullptr;

  case OPCODE_SPUT_OBJECT:
    return insn->get_field()->get_type();

  case OPCODE_INVOKE_VIRTUAL:
  case OPCODE_INVOKE_SUPER:
  case OPCODE_INVOKE_DIRECT:
  case OPCODE_INVOKE_STATIC:
  case OPCODE_INVOKE_INTERFACE: {
    DexMethodRef* insn_method = insn->get_method();
    const auto* arg_types = insn_method->get_proto()->get_args();
    size_t expected_args =
        (insn->opcode() != OPCODE_INVOKE_STATIC ? 1 : 0) + arg_types->size();
    always_assert(insn->srcs_size() == expected_args);

    if (insn->opcode() != OPCODE_INVOKE_STATIC) {
      // The first argument is a reference to the object instance on which the
      // method is invoked.
      if (src_index-- == 0) {
        return insn_method->get_class();
      }
    }
    return arg_types->at(src_index);
  }
  case OPCODE_INVOKE_CUSTOM:
  case OPCODE_INVOKE_POLYMORPHIC:
  case OPCODE_CONST_METHOD_HANDLE:
  case OPCODE_CONST_METHOD_TYPE:
    not_reached_log("Unsupported instruction {%s}\n", SHOW(insn));
  }
}

// This function is conservative and returns false if type_class is missing.
// A type is "interfacy" if it's an interface, or an array of an interface.
static bool is_not_interfacy(const DexType* type) {
  auto* cls = type_class(type::make_element_type_if_array(type));
  return (cls != nullptr) && !is_interface(cls);
}

// Weakens the given type in a way that's aware of the check-cast relationship
// of arrays. (However, it does not consider interfaces in a special way.)
static const DexType* weaken_type(const DexType* type) {
  if (type::is_array(type)) {
    auto* element_type = type::make_array_element_type(type);
    if (!type::is_primitive(element_type)) {
      const auto* weakened_element_type = weaken_type(element_type);
      if (weakened_element_type != nullptr) {
        return type::make_array_type(weakened_element_type);
      }
    }
  }
  auto* cls = type_class(type);
  if (cls == nullptr) {
    return nullptr;
  }
  return cls->get_super_class();
}

const DexType* CheckCastAnalysis::weaken_to_demand(
    IRInstruction* insn,
    const DexType* type,
    bool weaken_to_not_interfacy) const {
  if (!m_insn_demands) {
    // Weakening is disabled.
    return type;
  }
  auto it = m_insn_demands->find(insn);
  if (it == m_insn_demands->end()) {
    return type::java_lang_Object();
  }
  auto& demands = it->second;
  always_assert(!demands.empty());
  if (demands.size() == 1) {
    const auto* weakened_type = *unordered_any(demands);
    // Nullptr indicates that the type demand could not be computed exactly, and
    // no weakening should take place.
    if (weakened_type == nullptr) {
      return type;
    }
    if (weakened_type == type::java_lang_Enum()) {
      // TODO: Weaking across enums is technically correct, but exposes a
      // limitation in the EnumTransformer, so we just don't do it for now
      return type;
    }
    // Note that this singleton-demand may be an interface
    if (!weaken_to_not_interfacy || is_not_interfacy(weakened_type)) {
      return weakened_type;
    }
  }
  always_assert(!demands.count(nullptr));
  auto meets_demands = [&](const DexType* t) {
    for (const auto* d : UnorderedIterable(demands)) {
      if (!type::check_cast(t, d)) {
        return false;
      }
    }
    return true;
  };
  // A function that checks if a given type can be safely used.
  // In particular, we need to filter out external types that are not already
  // explicitly mentioned (in the demand set), as they might refer to a type
  // that's only available on a particular Android platform.
  auto is_safe = [&](const DexType* t) {
    const auto* u = type::is_array(t) ? type::make_array_element_type(t) : t;
    auto* cls = type_class(u);
    return (cls != nullptr) &&
           (!cls->is_external() || (demands.count(t) != 0u));
  };
  while (true) {
    const auto* weakened_type = weaken_type(type);
    if (weakened_type == nullptr || !meets_demands(weakened_type) ||
        !is_safe(weakened_type)) {
      return type;
    }
    if (weakened_type == type::java_lang_Enum()) {
      // TODO: Weaking across enums is technically correct, but exposes a
      // limitation in the EnumTransformer, so we just don't do it for now
      return type;
    }
    type = weakened_type;
  }
}

CheckCastAnalysis::CheckCastAnalysis(const CheckCastConfig& config,
                                     cfg::ControlFlowGraph& cfg,
                                     bool is_static,
                                     DexType* declaring_type,
                                     DexTypeList* args,
                                     DexType* rtype,
                                     const ParamAnnotations* param_anno,
                                     const api::AndroidSDK& api)
    : m_class_cast_exception_type(
          DexType::make_type("Ljava/lang/ClassCastException;")),
      m_cfg(cfg),
      m_is_static(is_static),
      m_declaring_type(declaring_type),
      m_args(args),
      m_rtype(rtype),
      m_param_anno(param_anno),
      m_api(api) {
  always_assert(m_class_cast_exception_type);

  auto iterable = cfg::InstructionIterable(cfg);
  for (auto it = iterable.begin(); it != iterable.end(); ++it) {
    IRInstruction* insn = it->insn;
    if (insn->opcode() == OPCODE_CHECK_CAST) {
      m_check_cast_its.push_back(it);
    }
  }
  if (m_check_cast_its.empty()) {
    return;
  }

  if (!config.weaken) {
    return;
  }
  m_insn_demands = std::make_unique<InstructionTypeDemands>();
  reaching_defs::MoveAwareFixpointIterator reaching_definitions(cfg);
  reaching_definitions.run({});
  for (cfg::Block* block : cfg.blocks()) {
    auto env = reaching_definitions.get_entry_state_at(block);
    if (env.is_bottom()) {
      continue;
    }
    for (auto& mie : InstructionIterable(block)) {
      IRInstruction* insn = mie.insn;
      for (size_t src_index = 0; src_index < insn->srcs_size(); src_index++) {
        auto src = insn->src(src_index);
        const auto& defs = env.get(src);
        always_assert(!defs.is_bottom() && !defs.is_top());
        for (auto* def : defs.elements()) {
          auto def_opcode = def->opcode();
          if (def_opcode == OPCODE_CHECK_CAST) {
            // When two check-casts interact, we prevent weakening of the
            // first to avoid situations where both get removed as they may
            // make each other redundant.
            const auto* t = insn->opcode() == OPCODE_CHECK_CAST
                                ? nullptr
                                : get_type_demand(insn, src_index);
            always_assert(t == nullptr || type::is_object(t));
            if (t != type::java_lang_Object()) {
              (*m_insn_demands)[def].insert(t);
            }
          }
        }
      }
      reaching_definitions.analyze_instruction(insn, &env);
    }
  }

  // Simplify demands
  for (auto& p : UnorderedIterable(*m_insn_demands)) {
    auto& demands = p.second;
    if (demands.count(nullptr) != 0u) {
      // no need to keep around anything else
      unordered_erase_if(demands, [](auto* t) { return t; });
      always_assert(demands.count(nullptr));
      always_assert(demands.size() == 1);
      continue;
    }
    // Remove weakened types.
    UnorderedSet<const DexType*> weakened_types;
    std::queue<const DexType*> queue;
    auto enqueue_weakened_types = [&queue](const DexType* type) {
      const auto* weakened_type = weaken_type(type);
      if (weakened_type != nullptr) {
        queue.push(weakened_type);
      }
      // We also handle interface hierarchies here.
      auto* cls = type_class(type);
      if (cls != nullptr) {
        for (auto* interface : *cls->get_interfaces()) {
          queue.push(interface);
        }
      }
    };
    for (const auto* demand : UnorderedIterable(demands)) {
      enqueue_weakened_types(demand);
    }
    while (!queue.empty()) {
      const auto* weakened_type = queue.front();
      queue.pop();
      if (weakened_types.insert(weakened_type).second) {
        enqueue_weakened_types(weakened_type);
      }
    }
    for (const auto* weakened_type : UnorderedIterable(weakened_types)) {
      if (demands.erase(weakened_type) != 0u) {
        // Double check that the just erased demand was indeed redundant
        always_assert(unordered_any_of(demands, [&](const DexType* demand) {
          return !weakened_types.count(demand) &&
                 type::check_cast(demand, weakened_type);
        }));
      }
    }
  }
}

CheckCastAnalysis CheckCastAnalysis::forMethod(const CheckCastConfig& config,
                                               DexMethod* method,
                                               const api::AndroidSDK& api) {
  return CheckCastAnalysis(config, method->get_code()->cfg(), is_static(method),
                           method->get_class(), method->get_proto()->get_args(),
                           method->get_proto()->get_rtype(),
                           method->get_param_anno(), api);
}

CheckCastReplacements CheckCastAnalysis::collect_redundant_checks_replacement()
    const {
  CheckCastReplacements redundant_check_casts;
  for (const auto& it : m_check_cast_its) {
    cfg::Block* block = it.block();
    IRInstruction* insn = it->insn;
    always_assert(insn->opcode() == OPCODE_CHECK_CAST);
    const auto* check_type = insn->get_type();
    if (!can_catch_class_cast_exception(block)) {
      check_type = weaken_to_demand(insn, check_type,
                                    /* weaken_to_not_interfacy */ false);
    }
    if (is_check_cast_redundant(insn, check_type)) {
      auto src = insn->src(0);
      auto move = m_cfg.move_result_of(it);
      if (move.is_end()) {
        continue;
      }

      auto dst = move->insn->dest();
      if (src == dst) {
        redundant_check_casts.emplace_back(block, insn, std::nullopt,
                                           std::nullopt);
      } else {
        auto* new_move = new IRInstruction(OPCODE_MOVE_OBJECT);
        new_move->set_src(0, src);
        new_move->set_dest(dst);
        redundant_check_casts.emplace_back(
            block, insn, std::optional<IRInstruction*>(new_move), std::nullopt);
      }
    } else if (check_type != insn->get_type()) {
      // We don't want to weaken a class to an interface for performance reason.
      // Re-compute the weakened type in that case, excluding interfaces.
      if (is_not_interfacy(insn->get_type()) && !is_not_interfacy(check_type)) {
        check_type = weaken_to_demand(insn, insn->get_type(),
                                      /* weaken_to_not_interfacy */ true);
      }
      if (check_type != insn->get_type()) {
        redundant_check_casts.emplace_back(
            block, insn, std::nullopt,
            std::optional<const DexType*>(check_type));
      }
    }
  }

  return redundant_check_casts;
}

bool CheckCastAnalysis::is_check_cast_redundant(
    IRInstruction* insn, const DexType* check_type) const {
  always_assert(insn->opcode() == OPCODE_CHECK_CAST);
  if (check_type == type::java_lang_Object()) {
    return true;
  }

  auto reg = insn->src(0);
  auto* type_inference = get_type_inference();
  auto& envs = type_inference->get_type_environments();
  auto& env = envs.at(insn);

  auto type = env.get_type(reg);
  if (type.equals(type_inference::TypeDomain(IRType::ZERO))) {
    return true;
  }

  auto dex_type = env.get_dex_type(reg);
  if (!dex_type || !type::check_cast(*dex_type, check_type)) {
    return false;
  }

  // Ensure that the relationship is available in the MinSdk.
  if (!type::is_min_sdk_acceptable(*dex_type, check_type, m_api)) {
    return false;
  }

  return true;
}

type_inference::TypeInference* CheckCastAnalysis::get_type_inference() const {
  if (!m_type_inference) {
    m_type_inference = std::make_unique<type_inference::TypeInference>(m_cfg);
    m_type_inference->run(m_is_static, m_declaring_type, m_args, m_param_anno);
  }
  return m_type_inference.get();
}

bool CheckCastAnalysis::can_catch_class_cast_exception(
    cfg::Block* block) const {
  for (auto* edge : block->succs()) {
    if (edge->type() != cfg::EDGE_THROW) {
      continue;
    }
    auto* catch_type = edge->throw_info()->catch_type;
    if ((catch_type == nullptr) ||
        type::is_subclass(catch_type, m_class_cast_exception_type)) {
      return true;
    }
  }
  return false;
}

} // namespace impl

} // namespace check_casts
