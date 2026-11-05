/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "BuilderAnalysis.h"

#include <sparta/ConstantAbstractDomain.h>
#include <sparta/PatriciaTreeMapAbstractEnvironment.h>

#include "BaseIRAnalyzer.h"
#include "Debug.h"
#include "Liveness.h"
#include "MethodUtil.h"
#include "Resolver.h"
#include "Show.h"
#include "Trace.h"
#include "TypeUtil.h"

using namespace sparta;

namespace builder_pattern {

namespace impl {

using namespace ir_analyzer;

namespace {

using NullableConstantValue =
    acd_impl::ConstantAbstractValue<const IRInstruction*>;

class NullableConstantDomain final
    : public AbstractDomainScaffolding<NullableConstantValue,
                                       NullableConstantDomain> {
 public:
  using ConstantType = const IRInstruction*;
  using BaseClass =
      AbstractDomainScaffolding<NullableConstantValue, NullableConstantDomain>;

  NullableConstantDomain() { set_to_top(); }

  explicit NullableConstantDomain(const ConstantType& cst) {
    set_to_value(NullableConstantValue(cst));
  }

  explicit NullableConstantDomain(AbstractValueKind kind) : BaseClass(kind) {}

  std::optional<ConstantType> get_constant() const {
    return is_value() ? std::optional<ConstantType>(get_value()->get_constant())
                      : std::nullopt;
  }

  void join_with(const NullableConstantDomain& other) {
    if (is_value() && other.is_value()) {
      if (get_value()->get_constant()->opcode() == OPCODE_CONST &&
          other.get_value()->get_constant()->opcode() != OPCODE_CONST) {
        TRACE(BLD_PATTERN, 5, "Join NULL const with builder %s:%s",
              SHOW(get_value()->get_constant()),
              SHOW(other.get_value()->get_constant()));
        set_to_value(*other.get_value());
        return;
      }
      if (get_value()->get_constant()->opcode() != OPCODE_CONST &&
          other.get_value()->get_constant()->opcode() == OPCODE_CONST) {
        TRACE(BLD_PATTERN, 5, "Join NULL const with builder %s:%s",
              SHOW(get_value()->get_constant()),
              SHOW(other.get_value()->get_constant()));
        // Do nothing, the value is already builder.
        return;
      }
    }
    BaseClass::join_with(other);
  }
};

} // namespace

using IRInstructionConstantDomain = NullableConstantDomain;

/**
 * For each register that holds an instance of a builder keeps track
 * of the instruction that initialized it.
 **/
using IRInstructionConstantEnvironment =
    PatriciaTreeMapAbstractEnvironment<reg_t, IRInstructionConstantDomain>;

class InstructionToEnvMap final
    : public UnorderedMap<const IRInstruction*,
                          impl::IRInstructionConstantEnvironment> {};

class Analyzer final : public BaseIRAnalyzer<IRInstructionConstantEnvironment> {

 public:
  Analyzer(const cfg::ControlFlowGraph& cfg,
           const ConstTypeHashSet& builder_types,
           const ConstTypeHashSet& excluded_builder_types,
           bool accept_excluded)
      : BaseIRAnalyzer<IRInstructionConstantEnvironment>(cfg),
        m_builder_types(builder_types),
        m_excluded_builder_types(excluded_builder_types),
        m_accept_excluded(accept_excluded) {
    MonotonicFixpointIterator::run(IRInstructionConstantEnvironment::top());
  }

  void analyze_instruction(
      const IRInstruction* insn,
      IRInstructionConstantEnvironment* current_state) const override {

    auto default_case = [&]() {
      // If we get here, reset destination.
      if (insn->has_dest()) {
        current_state->set(insn->dest(), IRInstructionConstantDomain::top());
        if (insn->dest_is_wide()) {
          current_state->set(insn->dest() + 1,
                             IRInstructionConstantDomain::top());
        }
      } else if (insn->has_move_result_any()) {
        // Here we don't need to update RESULT_REGISTER + 1 for wide cases,
        // since we only care about keeping track of the builders
        // (which are not wide). We only use this result for object move result
        // opcodes.
        current_state->set(RESULT_REGISTER, IRInstructionConstantDomain::top());
      }
    };

    switch (insn->opcode()) {
    case OPCODE_MOVE_OBJECT: {
      current_state->set(insn->dest(), current_state->get(insn->src(0)));
      break;
    }

    case IOPCODE_MOVE_RESULT_PSEUDO_OBJECT:
    case OPCODE_MOVE_RESULT_OBJECT: {
      current_state->set(insn->dest(), current_state->get(RESULT_REGISTER));
      break;
    }

    case OPCODE_CONST:
      if (insn->get_literal() == 0) {
        // NULL const is a special case required for conditional creation.
        current_state->set(insn->dest(), IRInstructionConstantDomain(insn));
      } else {
        default_case();
      }
      break;

    case OPCODE_NEW_INSTANCE: {
      if (is_builder(insn->get_type())) {
        // Keep track of the instantiation.
        current_state->set(RESULT_REGISTER, IRInstructionConstantDomain(insn));
      } else {
        default_case();
      }
      break;
    }

    case OPCODE_CHECK_CAST: {
      current_state->set(RESULT_REGISTER, current_state->get(insn->src(0)));
      break;
    }

    case OPCODE_INVOKE_DIRECT:
    case OPCODE_INVOKE_VIRTUAL:
    case OPCODE_INVOKE_STATIC: {
      auto* method =
          resolve_method_deprecated(insn->get_method(), opcode_to_search(insn));
      if (method == nullptr) {
        default_case();
        break;
      }

      auto* rtype = method->get_proto()->get_rtype();
      if (insn->opcode() != OPCODE_INVOKE_STATIC &&
          method->get_class() == rtype) {
        // NOTE: We expect that the method actually operates on the same
        //       instance and returns it. We are going to verify that later.
        current_state->set(RESULT_REGISTER, current_state->get(insn->src(0)));
      } else if (is_builder(rtype)) {
        // Keep track of the callsite that created / got the instance..
        current_state->set(RESULT_REGISTER, IRInstructionConstantDomain(insn));
      } else {
        default_case();
      }
      break;
    }

    default: {
      default_case();
      break;
    }
    }
  }

 private:
  const ConstTypeHashSet& m_builder_types;
  const ConstTypeHashSet& m_excluded_builder_types;
  const bool m_accept_excluded;

  bool is_builder(const DexType* type) const {
    const bool is_not_excluded =
        m_accept_excluded || m_excluded_builder_types.count(type) == 0;
    return (m_builder_types.count(type) != 0u) && is_not_excluded;
  }
};

} // namespace impl

BuilderAnalysis::~BuilderAnalysis() {}

BuilderAnalysis::BuilderAnalysis(const ConstTypeHashSet& builder_types,
                                 const ConstTypeHashSet& excluded_builder_types,
                                 DexMethod* method)
    : m_builder_types(builder_types),
      m_excluded_builder_types(excluded_builder_types),
      m_insn_to_env(new impl::InstructionToEnvMap),
      m_method(method),
      m_accept_excluded(true) {}

void BuilderAnalysis::run_analysis() {
  auto* code = m_method->get_code();
  if (code == nullptr) {
    return;
  }

  always_assert(code->cfg_built());
  cfg::ControlFlowGraph& cfg = code->cfg();
  cfg.calculate_exit_block();
  m_analyzer.reset(new impl::Analyzer(
      cfg, m_builder_types, m_excluded_builder_types, m_accept_excluded));

  populate_usage();
  cfg.recompute_registers_size();
  update_stats();
}

void BuilderAnalysis::print_usage() {
  if ((m_method == nullptr) || (m_method->get_code() == nullptr)) {
    return;
  }

  always_assert(m_analyzer);
  if (m_usage.empty()) {
    return;
  }

  TRACE(BLD_PATTERN, 4, "\nMethod %s", SHOW(m_method));
  for (const auto& pair : UnorderedIterable(m_usage)) {
    TRACE(BLD_PATTERN, 4, "\nInitialization in %s", SHOW(pair.first));

    for (const auto& it : pair.second) {
      TRACE(BLD_PATTERN, 4, "\t Usage: %s", SHOW(it->insn));
    }
  }
}

void BuilderAnalysis::update_stats() {
  // We only keep track of total usages once per method, to avoid redundant
  // computation. At the same time, we switch m_accept_excluded to false,
  // which will ignore the excluded builder types in the analysis.
  //
  // TODO(emmasevastian): maybe move this to the caller instead?
  if (m_accept_excluded) {
    m_total_usages = m_usage.size() + m_excluded_instantiation.size();
    m_accept_excluded = false;
  }
}

namespace {

const DexType* get_instantiated_type(const IRInstruction* insn) {
  const DexType* current_instance = nullptr;

  switch (insn->opcode()) {
  case OPCODE_CONST:
    break;

  case OPCODE_NEW_INSTANCE:
    current_instance = insn->get_type();
    break;

  case OPCODE_INVOKE_STATIC:
  case OPCODE_INVOKE_VIRTUAL:
  case OPCODE_INVOKE_DIRECT: {
    auto* method =
        resolve_method_deprecated(insn->get_method(), opcode_to_search(insn));
    current_instance = method->get_proto()->get_rtype();
    break;
  }

  default:
    not_reached_log("Different instantion opcode %s", SHOW(insn));
  }

  return current_instance;
}

} // namespace

void BuilderAnalysis::populate_usage() {
  m_usage.clear();
  m_insn_to_env->clear();

  auto* code = m_method->get_code();
  auto& cfg = code->cfg();

  // If the instantiated type is not excluded, updates the usages map.
  // Otherwise, update the excluded instantiation list.
  auto update_usages = [&](const IRInstruction* val,
                           const cfg::InstructionIterator& use) {
    if (const auto* referenced_type = get_instantiated_type(val)) {
      if (m_excluded_builder_types.count(referenced_type) == 0) {
        m_usage[val].push_back(use);

        auto* insn = use->insn;
        if (opcode::is_an_invoke(insn->opcode())) {
          m_invoke_to_builder_instance[insn] = referenced_type;
        }
      }

      m_excluded_instantiation.emplace(val);
    }
  };

  for (cfg::Block* block : cfg.blocks()) {
    auto env = m_analyzer->get_entry_state_at(block);
    for (auto& mie : InstructionIterable(block)) {
      auto it = block->to_cfg_instruction_iterator(mie);
      IRInstruction* insn = mie.insn;
      m_insn_to_env->emplace(insn, env);
      m_analyzer->analyze_instruction(insn, &env);

      if (insn->has_dest()) {
        auto dest = insn->dest();
        auto val_dest = env.get(dest).get_constant();
        if (val_dest) {
          update_usages(*val_dest, it);
        }
      }

      for (size_t index = 0; index < insn->srcs_size(); index++) {
        auto src = insn->src(index);
        auto val_src = env.get(src).get_constant();
        if (val_src) {
          update_usages(*val_src, it);
        }
      }
    }
  }
}

UnorderedMap<IRInstruction*, const DexType*>
BuilderAnalysis::get_vinvokes_to_this_infered_type() {
  UnorderedMap<IRInstruction*, const DexType*> result;

  for (const auto& pair : UnorderedIterable(m_usage)) {
    if (opcode::is_invoke_virtual(pair.first->opcode())) {
      always_assert(!result.count(const_cast<IRInstruction*>(pair.first)));

      const auto* current_instance = get_instantiated_type(pair.first);
      result[const_cast<IRInstruction*>(pair.first)] = current_instance;
    }

    for (const auto& it : pair.second) {
      auto* insn = it->insn;
      if (opcode::is_invoke_virtual(insn->opcode())) {
        auto this_reg = insn->src(0);
        auto val = m_insn_to_env->at(insn).get(this_reg).get_constant();

        if (val) {
          const auto* infered_type = get_instantiated_type(*val);
          always_assert(!result.count(const_cast<IRInstruction*>(insn)) ||
                        result[const_cast<IRInstruction*>(insn)] ==
                            infered_type);
          result[insn] = infered_type;
        };
      }
    }
  }

  return result;
}

UnorderedSet<IRInstruction*> BuilderAnalysis::get_all_inlinable_insns() {
  UnorderedSet<IRInstruction*> result;

  for (const auto& pair : UnorderedIterable(m_usage)) {
    if (opcode::is_an_invoke(pair.first->opcode())) {
      result.emplace(const_cast<IRInstruction*>(pair.first));
    }

    for (const auto& it : pair.second) {
      auto* insn = it->insn;
      if (opcode::is_an_invoke(insn->opcode())) {
        result.emplace(insn);
      }
    }
  }

  // Filter out non-inlinable ones.
  unordered_erase_if(result, [&](auto* insn) {
    always_assert(insn->has_method());

    auto method =
        resolve_method_deprecated(insn->get_method(), opcode_to_search(insn));
    if (!method || !method->get_code()) {
      return true;
    }

    if (method::is_init(method)) {
      auto this_reg = insn->src(0);
      auto val = m_insn_to_env->at(insn).get(this_reg).get_constant();
      if (!val || get_instantiated_type(*val) != method->get_class()) {
        return true;
      }
    }

    return false;
  });

  return result;
}

ConstTypeHashSet BuilderAnalysis::get_escaped_types_from_invokes(
    const UnorderedSet<IRInstruction*>& invoke_insns) const {
  ConstTypeHashSet result;

  for (const auto* invoke : UnorderedIterable(invoke_insns)) {
    if (m_invoke_to_builder_instance.count(invoke) != 0u) {
      result.emplace(m_invoke_to_builder_instance.at(invoke));
    }
  }
  return result;
}

ConstTypeHashSet BuilderAnalysis::get_instantiated_types() {
  ConstTypeHashSet result;

  for (const auto& pair : UnorderedIterable(m_usage)) {
    const auto* type = get_instantiated_type(pair.first);
    result.emplace(type);
  }

  return result;
}

namespace {

DexMethodRef* get_obj_default_ctor() {
  auto* obj_type = type::java_lang_Object();
  const auto* ctor_name = DexString::get_string("<init>");
  auto* default_ctor = DexMethod::get_method(
      obj_type,
      ctor_name,
      DexProto::get_proto(type::_void(), DexTypeList::make_type_list({})));

  return default_ctor;
}

} // namespace

ConstTypeHashSet BuilderAnalysis::non_removable_types() {
  auto non_removable_types = escape_types();

  // Consider other non-removable usages (for example synchronization usage).
  for (const auto& pair : UnorderedIterable(m_usage)) {
    const auto* instantiation = pair.first;
    const auto* current_instance = get_instantiated_type(instantiation);

    if (non_removable_types.count(current_instance) != 0u) {
      // Already decided it isn't removable.
      continue;
    }

    // Check if the instantiation is an invoke and non-inlinable.
    if (opcode::is_an_invoke(instantiation->opcode())) {
      auto* method = resolve_method_deprecated(instantiation->get_method(),
                                               opcode_to_search(instantiation));
      if ((method == nullptr) || (method->get_code() == nullptr)) {
        non_removable_types.emplace(current_instance);
        TRACE(BLD_PATTERN, 3, "non removal instantiation %s",
              SHOW(instantiation));
      }
    }

    for (const auto& it : pair.second) {
      if (opcode::is_a_monitor(it->insn->opcode())) {
        non_removable_types.emplace(current_instance);
        break;
      }
    }
  }

  return non_removable_types;
}

ConstTypeHashSet BuilderAnalysis::escape_types() {
  auto* code = m_method->get_code();
  auto& cfg = code->cfg();

  // Don't treat as escaping a builder passed to Object.<init>().
  auto* acceptable_method = get_obj_default_ctor();

  ConstTypeHashSet escape_types;
  for (const auto& pair : UnorderedIterable(m_usage)) {
    const auto* instantiation_insn = pair.first;
    const auto* current_instance = get_instantiated_type(instantiation_insn);

    for (const auto& it : pair.second) {
      auto* insn = it->insn;
      // If there is any invoke here, it is because we couldn't inline it.
      if (opcode::is_an_invoke(insn->opcode())) {
        // We accept Object.<init> calls.
        if (insn->get_method() == acceptable_method) {
          continue;
        }

        auto* method =
            resolve_method_deprecated(insn->get_method(), MethodSearch::Any);

        TRACE(BLD_PATTERN, 2, "Excluding type %s since we couldn't inline %s",
              SHOW(current_instance), SHOW(method));
        escape_types.emplace(current_instance);
      } else if (insn->opcode() == OPCODE_INSTANCE_OF) {
        TRACE(BLD_PATTERN, 2, "Excluding type %s since instanceof used",
              SHOW(current_instance));
        escape_types.emplace(current_instance);
      } else if (opcode::is_an_iput(insn->opcode()) ||
                 opcode::is_an_sput(insn->opcode()) ||
                 insn->opcode() == OPCODE_APUT_OBJECT ||
                 opcode::is_a_return(insn->opcode())) {
        auto src = insn->src(0);

        auto escaped = m_insn_to_env->at(insn).get(src).get_constant();
        if (escaped && *escaped == instantiation_insn) {
          TRACE(BLD_PATTERN, 2,
                "Excluding type %s since it is stored or returned in %s",
                SHOW(current_instance), SHOW(insn));
          escape_types.emplace(current_instance);
        }
      }
    }
  }

  LivenessFixpointIterator liveness_iter(cfg);
  liveness_iter.run(LivenessDomain());

  for (cfg::Block* block : cfg.blocks()) {
    const auto& current_env = m_analyzer->get_exit_state_at(block);

    for (const auto& succ : block->succs()) {
      cfg::Block* block_succ = succ->target();
      const auto& entry_env_at_succ =
          m_analyzer->get_entry_state_at(block_succ);
      const auto& live_in_vars_at_succ =
          liveness_iter.get_live_in_vars_at(succ->target());

      // Check that live registers, if they hold a builder at the end of block
      // B, then they hold the same one at the entry of any successor block.
      for (reg_t live_reg : live_in_vars_at_succ.elements()) {
        if (!entry_env_at_succ.get(live_reg).equals(
                current_env.get(live_reg))) {
          // It escapes here, since we couldn't follow it anymore.
          TRACE(BLD_PATTERN, 5,
                "Liveness missmatch for register v%u\nPRED:\n%sSUCC:\n%s",
                live_reg, SHOW(block), SHOW(block_succ));
          TRACE(BLD_PATTERN, 5, "Register value in PRED: %s",
                SHOW(*current_env.get(live_reg).get_constant()));
          if (auto succ_val = entry_env_at_succ.get(live_reg).get_constant()) {
            TRACE(BLD_PATTERN, 5, "Register value in SUCC: %s",
                  SHOW(*succ_val));
          } else {
            TRACE(BLD_PATTERN, 5, "Register value in SUCC: NONE");
          }

          const auto* init_insn = *current_env.get(live_reg).get_constant();
          if (init_insn->opcode() != OPCODE_CONST) {
            // NULL const cannot escape only builder can escape.
            const auto* current_instance = get_instantiated_type(init_insn);
            TRACE(BLD_PATTERN, 2,
                  "Excluding type %s since it escapes method %s",
                  SHOW(current_instance), SHOW(m_method));
            escape_types.emplace(current_instance);
          }
        }
      }
    }
  }

  // One allocation site owns one set of field registers. Another execution
  // cannot reuse them while an earlier instance from that site is still live.
  for (cfg::Block* block : cfg.blocks()) {
    auto live = liveness_iter.get_live_out_vars_at(block);
    auto instructions = InstructionIterable(block);
    for (auto it = instructions.end(); it != instructions.begin();) {
      auto* insn = (--it)->insn;
      if (insn->opcode() == OPCODE_NEW_INSTANCE && m_usage.count(insn) != 0u) {
        const auto& env = m_insn_to_env->at(insn);
        for (reg_t reg : live.elements()) {
          auto val = env.get(reg).get_constant();
          if (val && *val == insn) {
            TRACE(BLD_PATTERN, 2,
                  "Excluding type %s since an older instance is live at %s",
                  SHOW(insn->get_type()), SHOW(insn));
            escape_types.emplace(insn->get_type());
            break;
          }
        }
      }
      liveness_iter.analyze_instruction(insn, &live);
    }
  }

  return escape_types;
}

} // namespace builder_pattern
