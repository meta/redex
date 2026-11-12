/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ConstantPropagationTransform.h"

#include <algorithm>
#include <optional>
#include <unordered_set>
#include <vector>

#include "Debug.h"
#include "IRCode.h"
#include "Match.h"
#include "ReachableClasses.h"
#include "ReachingDefinitions.h"
#include "RedexContext.h"
#include "Resolver.h"
#include "ScopedMetrics.h"
#include "SignedConstantDomain.h"
#include "SourceBlocks.h"
#include "Trace.h"
#include "TypeInference.h"
#include "TypeUtil.h"

namespace constant_propagation {

// Verify that Intrinsics.areEqual has the expected semantics.
// Returns std::nullopt on success, or an error message on failure.
// Not a perfect check, but should be sufficient to catch most semantic
// changes from upstream.
std::optional<std::string> verify_areequal_semantics() {
  auto* areequal_ref = method::kotlin_jvm_internal_Intrinsics_areEqual();
  if (areequal_ref == nullptr) {
    return "Intrinsics.areEqual method not found";
  }
  if (areequal_ref->get_code() == nullptr) {
    return "Intrinsics.areEqual has no code";
  }
  DexMethodRef* object_equals = method::java_lang_Object_equals();
  always_assert(object_equals != nullptr);

  const auto insns = InstructionIterable(areequal_ref->get_code());

  // Must have exactly two nullness checks and no other branches.
  const auto null_checks =
      m::find_insn_match(insns, m::if_eqz_() || m::if_nez_());
  if (null_checks.size() != 2) {
    return "Intrinsics.areEqual has " + std::to_string(null_checks.size()) +
           " null checks, expected 2";
  }
  const auto all_branches =
      m::find_insn_match(insns, m::a_conditional_branch());
  if (all_branches.size() != 2) {
    return "Intrinsics.areEqual has " + std::to_string(all_branches.size()) +
           " branches, expected 2";
  }

  // Must call Object.equals exactly once, with no other invokes.
  const auto all_invokes =
      m::find_insn_match(insns, m::invoke_virtual_() || m::invoke_static_() ||
                                    m::invoke_direct_() || m::invoke_super_() ||
                                    m::invoke_interface_());
  const auto non_equals = m::find_insn_match(
      insns,
      (m::invoke_virtual_() || m::invoke_static_() || m::invoke_direct_() ||
       m::invoke_super_() || m::invoke_interface_()) &&
          !m::invoke_virtual_(m::has_method(m::equals(object_equals))));
  const auto equals_calls = m::find_insn_match(
      insns, m::invoke_virtual_(m::has_method(m::equals(object_equals))));
  if (equals_calls.size() != 1) {
    return "Intrinsics.areEqual has " + std::to_string(equals_calls.size()) +
           " Object.equals calls, expected 1; first invoke: " +
           (non_equals.empty() ? "(none)" : SHOW(non_equals.front()));
  }
  if (all_invokes.size() != 1) {
    return "Intrinsics.areEqual has " + std::to_string(all_invokes.size()) +
           " invokes, expected 1; first unexpected: " +
           SHOW(non_equals.front());
  }
  return std::nullopt;
}

namespace {

struct ClassLiteralMethodsReplacerContext {
  const DexMethodRef* class_isinstance{nullptr};
  std::optional<reg_t> class_isinstance_temp_reg{std::nullopt};

  const DexMethodRef* class_cast{nullptr};
  std::optional<reg_t> class_cast_temp_reg{std::nullopt};

  reg_t get_class_isinstance_temp_reg(cfg::ControlFlowGraph& cfg) {
    if (!class_isinstance_temp_reg) {
      class_isinstance_temp_reg = cfg.allocate_temp();
    }
    return *class_isinstance_temp_reg;
  }

  reg_t get_class_cast_temp_reg(cfg::ControlFlowGraph& cfg) {
    if (!class_cast_temp_reg) {
      class_cast_temp_reg = cfg.allocate_temp();
    }
    return *class_cast_temp_reg;
  }
};

} // namespace

struct Transform::Context {
  ClassLiteralMethodsReplacerContext clmr;
};

// Whether the check-cast `primary`, whose result holds `value`, may throw
// ClassCastException.
static bool is_possibly_throwing_check_cast(const IRInstruction* primary,
                                            const ConstantValue& value) {
  if (!opcode::is_check_cast(primary->opcode()) || value.is_zero()) {
    return false;
  }
  const DexType* src_type = get_object_constant_type(value);
  return src_type == nullptr ||
         !type::check_cast(src_type, primary->get_type());
}

/*
 * Replace an instruction that has a single destination register with a `const`
 * load. `env` holds the state of the registers after `insn` has been
 * evaluated. So, `env.get(dest)` holds the _new_ value of the destination
 * register.
 */
bool Transform::replace_with_const(const ConstantEnvironment& env,
                                   const cfg::InstructionIterator& cfg_it,
                                   const XStoreRefs* xstores,
                                   const DexType* declaring_type) {
  auto* insn = cfg_it->insn;
  auto value = env.get(insn->dest());
  auto replacement = ConstantValue::apply_visitor(
      value_to_instruction_visitor(insn, xstores, declaring_type), value);
  if (replacement.empty()) {
    return false;
  }
  if (opcode::is_a_move_result_pseudo(insn->opcode())) {
    auto primary_it = cfg_it.cfg().primary_instruction_of_move_result(cfg_it);
    // Materializing a constant into a move-result-pseudo's dest replaces -- and
    // therefore deletes -- the primary instruction. Keep a check-cast that
    // could throw, since deleting it would drop the exception.
    if (is_possibly_throwing_check_cast(primary_it->insn, value)) {
      return false;
    }
    always_assert(!replacement.empty());
    if (replacement.size() == 1) {
      IROpcode opcode = replacement.front()->opcode();
      always_assert(opcode::is_a_literal_const(opcode) ||
                    opcode == IOPCODE_R_CONST);
      // The move-result-pseudo instruction might be in a different block. We
      // cannot use the CFGMutator's replace functionality, as it would put the
      // replacement into the wrong block --- the block of the primary
      // instruction, not the following block. This is not generally a problem,
      // except that we might later want to run forward_targets, which requires
      // blocks, their recorded entry/state states and containing instructions
      // to be consistent. So we work around that here by directly inserting in
      // the right place...
      cfg_it.cfg().insert_after(cfg_it, replacement);
      m_mutation->remove(primary_it);
    } else {
      always_assert(opcode::may_throw(replacement.front()->opcode()));
      m_mutation->replace(primary_it, replacement);
    }
  } else {
    m_mutation->replace(cfg_it, replacement);
  }
  ++m_stats.materialized_consts;
  return true;
}

/*
 * Add an const after load param section for a known value load_param.
 * This will depend on future run of RemoveUnusedArgs pass to get the win of
 * removing not used arguments.
 */
void Transform::generate_const_param(const ConstantEnvironment& env,
                                     const cfg::InstructionIterator& cfg_it,
                                     const XStoreRefs* xstores,
                                     const DexType* declaring_type) {
  auto* insn = cfg_it->insn;
  auto value = env.get(insn->dest());
  auto replacement = ConstantValue::apply_visitor(
      value_to_instruction_visitor(insn, xstores, declaring_type), value);
  if (replacement.empty()) {
    return;
  }
  m_added_param_values.insert(m_added_param_values.end(), replacement.begin(),
                              replacement.end());
  ++m_stats.added_param_const;
}

bool is_known_non_null(const ConstantValue& val) {
  return val.is_object() || val.is_nez();
}

bool Transform::eliminate_redundant_null_check(
    const ConstantEnvironment& env,
    const WholeProgramState& /* unused */,
    const cfg::InstructionIterator& cfg_it) {
  auto* insn = cfg_it->insn;
  switch (insn->opcode()) {
  case OPCODE_INVOKE_STATIC: {
    // Kotlin null check.
    if (auto index = get_null_check_object_index(insn, m_null_check_methods)) {
      ++m_stats.null_checks_method_calls;
      if (is_known_non_null(env.get(insn->src(*index)))) {
        m_mutation->remove(cfg_it);
        ++m_stats.null_checks;
        return true;
      }
    }
    // Redex null check.
    if (insn->get_method() ==
        m_null_check_methods.redex_null_check_assertion()) {
      ++m_stats.null_checks_method_calls;
      if (is_known_non_null(env.get(insn->src(0)))) {
        m_mutation->remove(cfg_it);
        ++m_stats.null_checks;
        return true;
      }
    }
    break;
  }
  default:
    break;
  }
  return false;
}

// Membership test for a hardcoded allowlist. Returns true iff T belongs
// to a set of types whose equals method is symmetric across the whole set. The
// symmetry nature of these methods isn't tested at runtime.
//
// A type T has an equals that is symmetric iff a.equals(b) == b.equals(a) is
// guaranteed. There are two noticeable traps that can break this symmetry:
//   1. T must be final. Without finality, a subclass override could break
//      symmetry -- cf. java.util.Date / java.sql.Timestamp.
//   2. This must be true even for heterogeneous types, e.g., a
//      is of a type that is different from that of b.
bool is_safe_symmetric_equals_type(const DexType* t) {
  static const std::unordered_set<const DexType*> safe_types = []() {
    std::unordered_set<const DexType*> s = {
        type::java_lang_Boolean(),   type::java_lang_Byte(),
        type::java_lang_Character(), type::java_lang_Class(),
        type::java_lang_Integer(),   type::java_lang_Long(),
        type::java_lang_Short(),     type::java_lang_String(),
    };
    // Framework / stdlib types only added if present in the dex.
    using namespace std::string_view_literals;
    for (std::string_view desc : {
             "Landroid/graphics/Bitmap;"sv,
             "Landroid/graphics/Rect;"sv,
             "Landroid/os/Bundle;"sv,
             "Landroid/os/Looper;"sv,
             "Ljava/util/UUID;"sv,
         }) {
      if (auto* type = DexType::get_type(desc)) {
        s.insert(type);
      }
    }
    return s;
  }();
  always_assert(!safe_types.contains(nullptr));
  return safe_types.contains(t);
}

// Swap areEqual(a, b) to areEqual(b, a) when b is non-null and both args are
// final types with symmetric equals, so the non-null arg becomes first.
void Transform::swap_kotlin_areequal(
    const intraprocedural::FixpointIterator& intra_cp,
    cfg::ControlFlowGraph& cfg,
    bool is_static,
    const DexType* declaring_type,
    DexProto* proto) {
  auto* kotlin_areequal = method::kotlin_jvm_internal_Intrinsics_areEqual();
  if (kotlin_areequal == nullptr) {
    return;
  }
  // Skip TypeInference if no areEqual calls in this method.
  if (auto ii = cfg::ConstInstructionIterable(cfg);
      !std::any_of(ii.begin(), ii.end(), [&](const auto& mie) {
        return mie.insn->opcode() == OPCODE_INVOKE_STATIC &&
               mie.insn->get_method() == kotlin_areequal;
      })) {
    return;
  }
  type_inference::TypeInference ti(cfg);
  ti.run(is_static, declaring_type, proto->get_args());
  auto& type_envs = ti.get_type_environments();
  for (const auto& block : cfg.blocks()) {
    auto env = intra_cp.get_entry_state_at(block);
    if (env.is_bottom()) {
      continue;
    }
    for (auto& mie : InstructionIterable(block)) {
      auto* insn = mie.insn;
      intra_cp.analyze_instruction(insn, &env, false);
      if (insn->opcode() != OPCODE_INVOKE_STATIC ||
          insn->get_method() != kotlin_areequal) {
        continue;
      }
      // Skip if first arg is already non-null or known null -- swapping
      // gains nothing.
      if (auto src0_val = env.get(insn->src(0));
          is_known_non_null(src0_val) || src0_val.is_zero()) {
        continue;
      }
      if (!is_known_non_null(env.get(insn->src(1)))) {
        continue;
      }
      auto ti_it = type_envs.find(insn);
      if (ti_it == type_envs.end()) {
        continue;
      }
      auto& type_env = ti_it->second;
      auto type0 = type_env.get_dex_type(insn->src(0));
      auto type1 = type_env.get_dex_type(insn->src(1));
      if (!type0 || !type1 || !is_safe_symmetric_equals_type(*type0) ||
          !is_safe_symmetric_equals_type(*type1)) {
        continue;
      }
      auto src0 = insn->src(0);
      insn->set_src(0, insn->src(1));
      insn->set_src(1, src0);
      ++m_stats.kotlin_areequal_swapped;
    }
  }
}

bool Transform::replace_kotlin_areequal(
    const ConstantEnvironment& env, const cfg::InstructionIterator& cfg_it) {
  auto* insn = cfg_it->insn;
  if (insn->opcode() != OPCODE_INVOKE_STATIC) {
    return false;
  }
  auto* kotlin_areequal = method::kotlin_jvm_internal_Intrinsics_areEqual();
  if (kotlin_areequal == nullptr || insn->get_method() != kotlin_areequal) {
    return false;
  }
  // areEqual(a, b) calls a.equals(b) when a is non-null. When we can prove
  // a is non-null, replace with invoke-virtual Object.equals directly.
  // Both invoke-static areEqual and invoke-virtual equals take two source
  // registers (the static args / receiver + arg), so in-place modification
  // preserves the associated move-result-pseudo.
  if (!is_known_non_null(env.get(insn->src(0)))) {
    return false;
  }
  auto* object_equals = method::java_lang_Object_equals();
  always_assert(object_equals != nullptr);
  insn->set_opcode(OPCODE_INVOKE_VIRTUAL);
  insn->set_method(object_equals);
  ++m_stats.kotlin_areequal_replaced;
  return true;
}

bool Transform::eliminate_redundant_put(
    const ConstantEnvironment& env,
    const WholeProgramState& wps,
    const cfg::InstructionIterator& cfg_it) {
  auto* insn = cfg_it->insn;
  switch (insn->opcode()) {
  case OPCODE_SPUT:
  case OPCODE_SPUT_BOOLEAN:
  case OPCODE_SPUT_BYTE:
  case OPCODE_SPUT_CHAR:
  case OPCODE_SPUT_OBJECT:
  case OPCODE_SPUT_SHORT:
  case OPCODE_SPUT_WIDE:
  case OPCODE_IPUT:
  case OPCODE_IPUT_BOOLEAN:
  case OPCODE_IPUT_BYTE:
  case OPCODE_IPUT_CHAR:
  case OPCODE_IPUT_OBJECT:
  case OPCODE_IPUT_SHORT:
  case OPCODE_IPUT_WIDE: {
    auto* field = resolve_field(insn->get_field());
    if (field == nullptr) {
      break;
    }
    // WholeProgramState tells us the observable abstract value of a field
    // across all program traces outside their class's <clinit> or <init>, so we
    // need to join with 0 here as we are effectively creating a new observation
    // point at which the field might still have its default value.
    // The ConstantEnvironment tells us the abstract value of a non-escaping
    // field at this particular program point.
    ConstantValue existing_val;
    if (m_config.class_under_init == field->get_class()) {
      existing_val = env.get(field);
    } else {
      existing_val = wps.get_field_value(field);
      existing_val.join_with(SignedConstantDomain(0));
    }
    auto new_val = env.get(insn->src(0));
    if (ConstantValue::apply_visitor(runtime_equals_visitor(), existing_val,
                                     new_val)) {
      TRACE(FINALINLINE, 2, "%s has %s", SHOW(field), SHOW(existing_val));
      // This field must already hold this value. We don't need to write to it
      // again.
      m_mutation->remove(cfg_it);
      ++m_stats.redundant_puts_removed;
      return true;
    }
    break;
  }
  default: {
    break;
  }
  }
  return false;
}

namespace {

void try_simplify(const ConstantEnvironment& env,
                  const cfg::InstructionIterator& cfg_it,
                  const Transform::Config& config,
                  cfg::CFGMutation& mutation) {
  auto* insn = cfg_it->insn;

  auto reg_is_exact = [&env](reg_t reg, int64_t val) {
    auto value = env.get(reg).maybe_get<SignedConstantDomain>();
    return (value != std::nullopt) && (value->get_constant() != std::nullopt) &&
           (*value->get_constant() == val);
  };

  auto reg_fits_lit = [&](reg_t reg) -> std::optional<int16_t> {
    auto value = env.get(reg).maybe_get<SignedConstantDomain>();
    if (!value || !value->get_constant()) {
      return std::nullopt;
    }
    int64_t val = *value->get_constant();
    if (config.to_int_lit8 && val >= -128 && val <= 127) {
      return (int16_t)val;
    }
    if (config.to_int_lit16 && val >= -32768 && val <= 32767) {
      return (int16_t)val;
    }
    return std::nullopt;
  };

  auto maybe_reduce_lit = [&](size_t idx) -> bool {
    auto val = reg_fits_lit(insn->src(idx));
    if (!val) {
      return false;
    }

    auto new_op = [&]() -> IROpcode {
      switch (insn->opcode()) {
      case OPCODE_ADD_INT:
        return OPCODE_ADD_INT_LIT;
      // TODO: SUB to RSUB
      case OPCODE_MUL_INT:
        return OPCODE_MUL_INT_LIT;
      case OPCODE_AND_INT:
        return OPCODE_AND_INT_LIT;
      case OPCODE_OR_INT:
        return OPCODE_OR_INT_LIT;
      case OPCODE_XOR_INT:
        return OPCODE_XOR_INT_LIT;
      default:
        always_assert(false);
      }
      not_reached();
    }();

    auto* repl = new IRInstruction(new_op);
    repl->set_src(0, insn->src(idx == 0 ? 1 : 0));
    repl->set_dest(insn->dest());
    repl->set_literal(*val);
    mutation.replace(cfg_it, {repl});
    return true;
  };

  auto maybe_reduce_lit_both = [&]() {
    if (maybe_reduce_lit(0)) {
      return true;
    }
    if (maybe_reduce_lit(1)) {
      return true;
    }
    return false;
  };

  auto replace_with_move = [&](reg_t src_reg) {
    auto* move = new IRInstruction(OPCODE_MOVE);
    move->set_src(0, src_reg);
    move->set_dest(insn->dest());
    mutation.replace(cfg_it, {move});
  };

  auto replace_with_move_wide = [&](reg_t src_reg) {
    auto* move = new IRInstruction(OPCODE_MOVE_WIDE);
    move->set_src(0, src_reg);
    move->set_dest(insn->dest());
    mutation.replace(cfg_it, {move});
  };

  auto replace_with_const = [&](int64_t val) {
    auto* c = new IRInstruction(OPCODE_CONST);
    c->set_dest(insn->dest());
    c->set_literal(val);
    mutation.replace(cfg_it, {c});
  };

  auto replace_with_const_wide = [&](int64_t val) {
    auto* c = new IRInstruction(OPCODE_CONST_WIDE);
    c->set_dest(insn->dest());
    c->set_literal(val);
    mutation.replace(cfg_it, {c});
  };

  auto replace_with_neg = [&](reg_t src_reg) {
    auto* neg = new IRInstruction(OPCODE_NEG_INT);
    neg->set_src(0, src_reg);
    neg->set_dest(insn->dest());
    mutation.replace(cfg_it, {neg});
  };

  auto replace_with_neg_long = [&](reg_t src_reg) {
    auto* neg = new IRInstruction(OPCODE_NEG_LONG);
    neg->set_src(0, src_reg);
    neg->set_dest(insn->dest());
    mutation.replace(cfg_it, {neg});
  };

  switch (insn->opcode()) {
    // These should have been handled by PeepHole, really.

  case OPCODE_ADD_INT_LIT: {
    if (insn->get_literal() == 0) {
      replace_with_move(insn->src(0));
    }
    break;
  }

  case OPCODE_RSUB_INT_LIT: {
    if (insn->get_literal() == 0) {
      replace_with_neg(insn->src(0));
    }
    break;
  }

  case OPCODE_MUL_INT_LIT: {
    if (insn->get_literal() == 1) {
      replace_with_move(insn->src(0));
      break;
    }
    if (insn->get_literal() == 0) {
      replace_with_const(0);
      break;
    }
    if (insn->get_literal() == -1) {
      replace_with_neg(insn->src(0));
      break;
    }
    break;
  }
  case OPCODE_AND_INT_LIT: {
    if (insn->get_literal() == 0) {
      replace_with_const(0);
      break;
    }
    if (insn->get_literal() == -1) {
      replace_with_move(insn->src(0));
      break;
    }
    break;
  }
  case OPCODE_OR_INT_LIT: {
    if (insn->get_literal() == 0) {
      replace_with_move(insn->src(0));
      break;
    }
    if (insn->get_literal() == -1) {
      replace_with_const(-1);
      break;
    }
    break;
  }
  case OPCODE_XOR_INT_LIT: {
    if (insn->get_literal() == 0) {
      replace_with_move(insn->src(0));
      break;
    }
    break;
  }

  case OPCODE_SHL_INT_LIT:
  case OPCODE_USHR_INT_LIT:
  case OPCODE_SHR_INT_LIT: {
    // Can at most simplify the operand, but doesn't make much sense.
    break;
  }

  case OPCODE_ADD_INT: {
    if (reg_is_exact(insn->src(0), 0)) {
      replace_with_move(insn->src(1));
    } else if (reg_is_exact(insn->src(1), 0)) {
      replace_with_move(insn->src(0));
    } else if (maybe_reduce_lit_both()) {
      break;
    }
    break;
  }

  case OPCODE_SUB_INT: {
    if (reg_is_exact(insn->src(0), 0)) {
      replace_with_neg(insn->src(1));
    } else if (reg_is_exact(insn->src(1), 0)) {
      replace_with_move(insn->src(0));
    }
    break;
  }

  case OPCODE_MUL_INT: {
    if (reg_is_exact(insn->src(0), 1)) {
      replace_with_move(insn->src(1));
    } else if (reg_is_exact(insn->src(1), 1)) {
      replace_with_move(insn->src(0));
    } else if (reg_is_exact(insn->src(0), 0) || reg_is_exact(insn->src(1), 0)) {
      replace_with_const(0);
    } else if (reg_is_exact(insn->src(0), -1)) {
      replace_with_neg(insn->src(1));
    } else if (reg_is_exact(insn->src(1), -1)) {
      replace_with_neg(insn->src(0));
    } else if (maybe_reduce_lit_both()) {
      break;
    }
    break;
  }

  case OPCODE_AND_INT: {
    if (reg_is_exact(insn->src(0), -1)) {
      replace_with_move(insn->src(1));
    } else if (reg_is_exact(insn->src(1), -1)) {
      replace_with_move(insn->src(0));
    } else if (reg_is_exact(insn->src(0), 0) || reg_is_exact(insn->src(1), 0)) {
      replace_with_const(0);
    } else if (maybe_reduce_lit_both()) {
      break;
    }
    break;
  }

  case OPCODE_OR_INT: {
    if (reg_is_exact(insn->src(0), 0)) {
      replace_with_move(insn->src(1));
    } else if (reg_is_exact(insn->src(1), 0)) {
      replace_with_move(insn->src(0));
    } else if (reg_is_exact(insn->src(0), -1) ||
               reg_is_exact(insn->src(1), -1)) {
      replace_with_const(-1);
    } else if (maybe_reduce_lit_both()) {
      break;
    }
    break;
  }

  case OPCODE_XOR_INT: {
    if (reg_is_exact(insn->src(0), 0)) {
      replace_with_move(insn->src(1));
    } else if (reg_is_exact(insn->src(1), 0)) {
      replace_with_move(insn->src(0));
    } else if (maybe_reduce_lit_both()) {
      break;
    }
    break;
  }

  case OPCODE_ADD_LONG: {
    if (reg_is_exact(insn->src(0), 0)) {
      replace_with_move_wide(insn->src(1));
    } else if (reg_is_exact(insn->src(1), 0)) {
      replace_with_move_wide(insn->src(0));
    }
    break;
  }
  case OPCODE_SUB_LONG: {
    if (reg_is_exact(insn->src(0), 0)) {
      replace_with_neg_long(insn->src(1));
    } else if (reg_is_exact(insn->src(1), 0)) {
      replace_with_move_wide(insn->src(0));
    }
    break;
  }
  case OPCODE_MUL_LONG: {
    if ((reg_is_exact(insn->src(0), 0)) || (reg_is_exact(insn->src(1), 0))) {
      replace_with_const_wide(0);
    } else if (reg_is_exact(insn->src(0), 1)) {
      replace_with_move_wide(insn->src(1));
    } else if (reg_is_exact(insn->src(1), 1)) {
      replace_with_move_wide(insn->src(0));
    } else if (reg_is_exact(insn->src(0), -1)) {
      replace_with_neg_long(insn->src(1));
    } else if (reg_is_exact(insn->src(1), -1)) {
      replace_with_neg_long(insn->src(0));
    }
    break;
  }
  case OPCODE_AND_LONG: {
    if ((reg_is_exact(insn->src(0), 0)) || (reg_is_exact(insn->src(1), 0))) {
      replace_with_const_wide(0);
    } else if (reg_is_exact(insn->src(0), -1)) {
      replace_with_move_wide(insn->src(1));
    } else if (reg_is_exact(insn->src(1), -1)) {
      replace_with_move_wide(insn->src(0));
    }
    break;
  }
  case OPCODE_OR_LONG: {
    if ((reg_is_exact(insn->src(0), -1)) || (reg_is_exact(insn->src(1), -1))) {
      replace_with_const_wide(-1);
    } else if (reg_is_exact(insn->src(0), 0)) {
      replace_with_move_wide(insn->src(1));
    } else if (reg_is_exact(insn->src(1), 0)) {
      replace_with_move_wide(insn->src(0));
    }
    break;
  }
  case OPCODE_XOR_LONG: {
    if (reg_is_exact(insn->src(0), 0)) {
      replace_with_move_wide(insn->src(1));
    } else if (reg_is_exact(insn->src(1), 0)) {
      replace_with_move_wide(insn->src(0));
    }
    break;
  }

  default:
    return;
  }
}

struct ClassLiteralMethodsReplacer {

  static bool matches(const DexMethodRef* ref,
                      const Transform::Context& context) {
    return ref == context.clmr.class_isinstance ||
           ref == context.clmr.class_cast;
  }

  static const DexType* maybe_get_class(const IRInstruction* insn,
                                        const ConstantEnvironment& env) {
    const auto& val = env.get(insn->src(0));
    if (val.is_top() || val.is_bottom()) {
      return nullptr;
    }
    const auto* class_val =
        boost::get<ConstantClassObjectDomain>(&val.variant());
    if (class_val == nullptr) {
      return nullptr;
    }
    redex_assert(!class_val->is_top());
    if (class_val->is_bottom()) {
      return nullptr;
    }
    redex_assert(class_val->get_constant());
    return *class_val->get_constant();
  }

  static void replace_class_isinstance(const IRInstruction* insn,
                                       const ConstantEnvironment& env,
                                       const cfg::InstructionIterator& cfg_it,
                                       cfg::CFGMutation& mutation,
                                       Transform::Stats& stats,
                                       Transform::Context& context) {
    const auto* class_type = maybe_get_class(insn, env);
    if (class_type == nullptr) {
      return;
    }

    // Replace with direct instance-of.
    auto* repl = new IRInstruction(OPCODE_INSTANCE_OF);
    repl->set_src(0, insn->src(1));
    repl->set_type(class_type);

    auto* move = new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO);
    // Find move-result.
    auto& cfg = cfg_it.cfg();
    auto move_result_it = cfg.move_result_of(cfg_it);
    move->set_dest(move_result_it.is_end()
                       ? context.clmr.get_class_isinstance_temp_reg(cfg)
                       : move_result_it->insn->dest());

    mutation.replace(cfg_it, {repl, move});
    ++stats.class_isinstance_replaced;
  }

  static void replace_class_cast(const IRInstruction* insn,
                                 const ConstantEnvironment& env,
                                 const cfg::InstructionIterator& cfg_it,
                                 cfg::CFGMutation& mutation,
                                 Transform::Stats& stats,
                                 Transform::Context& context) {
    const auto* class_type = maybe_get_class(insn, env);
    if (class_type == nullptr) {
      return;
    }

    // Replace with direct checkcast.
    auto* repl = new IRInstruction(OPCODE_CHECK_CAST);
    repl->set_src(0, insn->src(1));
    repl->set_type(class_type);

    auto* move = new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT);
    // Find move-result.
    auto& cfg = cfg_it.cfg();
    auto move_result_it = cfg.move_result_of(cfg_it);
    move->set_dest(move_result_it.is_end()
                       ? context.clmr.get_class_cast_temp_reg(cfg)
                       : move_result_it->insn->dest());

    mutation.replace(cfg_it, {repl, move});
    ++stats.class_cast_replaced;
  }

  static void replace(const IRInstruction* insn,
                      const DexMethodRef* ref,
                      const ConstantEnvironment& env,
                      const cfg::InstructionIterator& cfg_it,
                      cfg::CFGMutation& mutation,
                      Transform::Stats& stats,
                      Transform::Context& context) {
    if (ref == context.clmr.class_isinstance) {
      replace_class_isinstance(insn, env, cfg_it, mutation, stats, context);
      return;
    }
    if (ref == context.clmr.class_cast) {
      replace_class_cast(insn, env, cfg_it, mutation, stats, context);
      return;
    }
  }

  static ClassLiteralMethodsReplacerContext create_context() {
    return ClassLiteralMethodsReplacerContext{
        .class_isinstance = method::java_lang_Class_isInstance(),
        .class_cast = method::java_lang_Class_cast(),
    };
  }
};

} // namespace

bool Transform::assumenosideeffects(DexMethodRef* ref, DexMethod* meth) const {
  if (::assumenosideeffects(meth)) {
    return true;
  }
  return m_config.pure_methods->find(ref) != m_config.pure_methods->end();
}

void Transform::simplify_instruction(const ConstantEnvironment& env,
                                     const WholeProgramState& /*wps*/,
                                     const cfg::InstructionIterator& cfg_it,
                                     const XStoreRefs* xstores,
                                     const DexType* declaring_type,
                                     Context& context) {
  auto* insn = cfg_it->insn;
  switch (insn->opcode()) {
  case IOPCODE_LOAD_PARAM:
  case IOPCODE_LOAD_PARAM_OBJECT:
  case IOPCODE_LOAD_PARAM_WIDE: {
    if (m_config.add_param_const) {
      generate_const_param(env, cfg_it, xstores, declaring_type);
    }
    break;
  }
  case OPCODE_MOVE:
  case OPCODE_MOVE_WIDE:
    if (m_config.replace_moves_with_consts) {
      replace_with_const(env, cfg_it, xstores, declaring_type);
    }
    break;
  case IOPCODE_MOVE_RESULT_PSEUDO:
  case IOPCODE_MOVE_RESULT_PSEUDO_WIDE:
  case IOPCODE_MOVE_RESULT_PSEUDO_OBJECT: {
    auto& cfg = cfg_it.cfg();
    auto* primary_insn = cfg.primary_instruction_of_move_result(cfg_it)->insn;
    auto op = primary_insn->opcode();
    if (opcode::is_an_sget(op) || opcode::is_an_iget(op) ||
        opcode::is_an_aget(op) || opcode::is_div_int_lit(op) ||
        opcode::is_rem_int_lit(op) || opcode::is_instance_of(op) ||
        opcode::is_rem_int_or_long(op) || opcode::is_div_int_or_long(op) ||
        opcode::is_check_cast(op) || opcode::is_array_length(op)) {
      replace_with_const(env, cfg_it, xstores, declaring_type);
    }
    break;
  }
  // Currently it's default to not replace move-result opcodes with consts
  // because it's unlikely that we can get a more compact encoding (move-result
  // can address 8-bit register operands while taking up just 1 code unit).
  // However it can be a net win if we can remove the invoke opcodes as well --
  // we need a purity analysis for that though.
  case OPCODE_MOVE_RESULT:
  case OPCODE_MOVE_RESULT_WIDE:
  case OPCODE_MOVE_RESULT_OBJECT: {
    if (m_config.replace_move_result_with_consts) {
      replace_with_const(env, cfg_it, xstores, declaring_type);
      break;
    }
    if ((m_config.getter_methods_for_immutable_fields == nullptr) &&
        (m_config.pure_methods == nullptr)) {
      break;
    }

    auto& cfg = cfg_it.cfg();
    auto* primary_insn = cfg.primary_instruction_of_move_result(cfg_it)->insn;
    if (!opcode::is_an_invoke(primary_insn->opcode())) {
      break;
    }
    auto* invoked = resolve_method_deprecated(primary_insn->get_method(),
                                              opcode_to_search(primary_insn));
    if (invoked == nullptr) {
      break;
    }
    if ((m_config.getter_methods_for_immutable_fields != nullptr) &&
        opcode::is_invoke_virtual(primary_insn->opcode()) &&
        (m_config.getter_methods_for_immutable_fields->count(invoked) != 0u)) {
      replace_with_const(env, cfg_it, xstores, declaring_type);
      break;
    }

    if ((m_config.pure_methods != nullptr) &&
        assumenosideeffects(primary_insn->get_method(), invoked)) {
      replace_with_const(env, cfg_it, xstores, declaring_type);
      break;
    }
    break;
  }
  case OPCODE_ADD_INT_LIT:
  case OPCODE_RSUB_INT_LIT:
  case OPCODE_MUL_INT_LIT:
  case OPCODE_AND_INT_LIT:
  case OPCODE_OR_INT_LIT:
  case OPCODE_XOR_INT_LIT:
  case OPCODE_SHL_INT_LIT:
  case OPCODE_SHR_INT_LIT:
  case OPCODE_USHR_INT_LIT:
  case OPCODE_ADD_INT:
  case OPCODE_SUB_INT:
  case OPCODE_MUL_INT:
  case OPCODE_AND_INT:
  case OPCODE_OR_INT:
  case OPCODE_XOR_INT:
  case OPCODE_ADD_LONG:
  case OPCODE_SUB_LONG:
  case OPCODE_MUL_LONG:
  case OPCODE_AND_LONG:
  case OPCODE_OR_LONG:
  case OPCODE_XOR_LONG:
  case OPCODE_NOT_INT:
  case OPCODE_NEG_INT:
  case OPCODE_NEG_LONG:
  case OPCODE_NOT_LONG:
  case OPCODE_INT_TO_LONG:
  case OPCODE_INT_TO_BYTE:
  case OPCODE_INT_TO_CHAR:
  case OPCODE_INT_TO_SHORT:
  case OPCODE_LONG_TO_INT:
  case OPCODE_NEG_FLOAT:
  case OPCODE_NEG_DOUBLE:
  case OPCODE_FLOAT_TO_INT:
  case OPCODE_INT_TO_FLOAT:
  case OPCODE_FLOAT_TO_LONG:
  case OPCODE_LONG_TO_FLOAT:
  case OPCODE_DOUBLE_TO_INT:
  case OPCODE_DOUBLE_TO_LONG:
  case OPCODE_DOUBLE_TO_FLOAT:
  case OPCODE_INT_TO_DOUBLE:
  case OPCODE_LONG_TO_DOUBLE:
  case OPCODE_FLOAT_TO_DOUBLE: {
    if (replace_with_const(env, cfg_it, xstores, declaring_type)) {
      break;
    }
    try_simplify(env, cfg_it, m_config, *m_mutation);
    break;
  }

  case OPCODE_INVOKE_VIRTUAL:
  case OPCODE_INVOKE_STATIC:
  case OPCODE_INVOKE_DIRECT: {
    // It is OK not to resolve the method, as these are core Java classes.
    if (ClassLiteralMethodsReplacer::matches(insn->get_method(), context)) {
      ClassLiteralMethodsReplacer::replace(
          insn, insn->get_method(), env, cfg_it, *m_mutation, m_stats, context);
      break;
    }

    break;
  }

  default: {
  }
  }
}

void Transform::remove_dead_switch(
    const intraprocedural::FixpointIterator& intra_cp,
    const ConstantEnvironment& env,
    cfg::ControlFlowGraph& cfg,
    cfg::Block* block) {

  if (!m_config.remove_dead_switch) {
    return;
  }

  auto insn_it = block->get_last_insn();
  always_assert(insn_it != block->end());
  auto* insn = insn_it->insn;
  always_assert(opcode::is_switch(insn->opcode()));

  // Prune infeasible or unnecessary branches
  cfg::Edge* goto_edge = cfg.get_succ_edge_of_type(block, cfg::EDGE_GOTO);
  cfg::Block* goto_target = goto_edge->target();
  UnorderedMap<cfg::Block*, uint32_t> remaining_branch_targets;
  std::vector<cfg::Edge*> remaining_branch_edges;
  for (auto* branch_edge :
       cfg.get_succ_edges_of_type(block, cfg::EDGE_BRANCH)) {
    auto branch_is_feasible =
        !intra_cp.analyze_edge(branch_edge, env).is_bottom();
    if (branch_is_feasible) {
      remaining_branch_edges.push_back(branch_edge);
      remaining_branch_targets[branch_edge->target()]++;
      continue;
    }
    m_edge_deletes.push_back(branch_edge);
  }

  bool goto_is_feasible = !intra_cp.analyze_edge(goto_edge, env).is_bottom();
  if (!goto_is_feasible && !remaining_branch_targets.empty()) {
    // Rewire infeasible goto to absorb all cases to most common target
    std::optional<int32_t> most_common_case_key;
    cfg::Block* most_common_target{nullptr};
    uint32_t most_common_target_count{0};
    UnorderedSet<cfg::Block*> visited;
    for (cfg::Edge* e : remaining_branch_edges) {
      auto case_key = *e->case_key();
      auto* target = e->target();
      auto count = remaining_branch_targets.at(target);
      always_assert(count > 0);
      if (count > most_common_target_count ||
          (count == most_common_target_count &&
           case_key > *most_common_case_key)) {
        most_common_case_key = case_key;
        most_common_target = target;
        most_common_target_count = count;
      }
    }
    always_assert(most_common_target != nullptr);
    if (most_common_target != goto_target) {
      m_edge_deletes.push_back(goto_edge);
      goto_target = most_common_target;
      m_edge_adds.emplace_back(block, goto_target, cfg::EDGE_GOTO);
      goto_edge = nullptr;
    }
    auto removed = std::erase_if(remaining_branch_edges, [&](auto* e) {
      if (e->target() == most_common_target) {
        m_edge_deletes.push_back(e);
        return true;
      }
      return false;
    });
    always_assert(removed == most_common_target_count);
    remaining_branch_targets.erase(most_common_target);
    ++m_stats.branches_removed;
    // goto is now feasible
  }

  // When all remaining branches are infeasible, the cfg will remove the switch
  // instruction.
  if (remaining_branch_targets.empty()) {
    ++m_stats.branches_removed;
    return;
  }
  always_assert(!remaining_branch_edges.empty());

  remaining_branch_targets[goto_target]++;
  if (remaining_branch_targets.size() > 1) {
    return;
  }

  always_assert(remaining_branch_targets.size() == 1);
  ++m_stats.branches_removed;
  // Replace the switch by a goto to the uniquely reachable block
  // We do that by deleting all but one of the remaining branch edges, and then
  // the cfg will rewrite the remaining branch into a goto and remove the switch
  // instruction.
  m_edge_deletes.insert(m_edge_deletes.end(),
                        remaining_branch_edges.begin(),
                        remaining_branch_edges.end());
}

/*
 * If the last instruction in a basic block is an if-* instruction, determine
 * whether it is dead (i.e. whether the branch always taken or never taken).
 * If it is, we can replace it with either a nop or a goto.
 */
void Transform::eliminate_dead_branch(
    const intraprocedural::FixpointIterator& intra_cp,
    const ConstantEnvironment& env,
    cfg::ControlFlowGraph& cfg,
    cfg::Block* block) {
  auto insn_it = block->get_last_insn();
  if (insn_it == block->end()) {
    return;
  }
  auto* insn = insn_it->insn;
  if (opcode::is_switch(insn->opcode())) {
    remove_dead_switch(intra_cp, env, cfg, block);
    return;
  }

  if (!opcode::is_a_conditional_branch(insn->opcode())) {
    return;
  }

  // Get all normal succs (goto/branch edges, excluding ghost edges).
  const auto succs = cfg.get_succ_edges_if(block, [](const auto* e) {
    return e->type() == cfg::EDGE_GOTO || e->type() == cfg::EDGE_BRANCH;
  });
  always_assert_log(succs.size() == 2, "actually %zu\n%s in B%zu:\n%s",
                    succs.size(), SHOW(InstructionIterable(*block)),
                    block->id(), SHOW(cfg));
  for (const auto& edge : succs) {
    // Check if the fixpoint analysis has determined the successors to be
    // unreachable
    if (intra_cp.analyze_edge(edge, env).is_bottom()) {
      TRACE(CONSTP, 2, "Removing conditional branch %s", SHOW(insn));
      ++m_stats.branches_removed;
      // We delete the infeasible edge, and then the cfg will rewrite the
      // remaining branch into a goto and remove the if- instruction.
      m_edge_deletes.push_back(edge);
      // Assuming :block is reachable, then at least one of its successors must
      // be reachable, so we can break after finding one that's unreachable
      break;
    }
  }
}

bool Transform::replace_with_throw(
    const ConstantEnvironment& env,
    const cfg::InstructionIterator& cfg_it,
    npe::NullPointerExceptionCreator* npe_creator) {
  auto* insn = cfg_it->insn;
  auto dereferenced_object_src_index = get_dereferenced_object_src_index(insn);
  if (!dereferenced_object_src_index) {
    return false;
  }

  auto reg = insn->src(*dereferenced_object_src_index);
  auto value = env.get(reg).maybe_get<SignedConstantDomain>();
  std::vector<IRInstruction*> new_insns;
  if (!value || !value->get_constant() || *value->get_constant() != 0) {
    return false;
  }

  // We'll replace this instruction with a different instruction sequence that
  // unconditionally throws a null pointer exception.

  m_mutation->replace_mie(cfg_it, npe_creator->get_insns(insn));
  ++m_stats.throws;

  if (insn->has_move_result_any()) {
    auto& cfg = cfg_it.cfg();
    auto move_result_it = cfg.move_result_of(cfg_it);
    if (!move_result_it.is_end()) {
      m_redundant_move_results.insert(move_result_it->insn);
    }
  }
  return true;
}

void Transform::apply_changes(cfg::ControlFlowGraph& cfg) {
  if (!m_edge_adds.empty()) {
    for (auto& t : m_edge_adds) {
      cfg.add_edge(std::get<0>(t), std::get<1>(t), std::get<2>(t));
    }
    m_edge_adds.clear();
  }
  if (!m_edge_deletes.empty()) {
    cfg.delete_edges(m_edge_deletes.begin(), m_edge_deletes.end());
    m_edge_deletes.clear();
  }

  always_assert(m_mutation != nullptr);
  m_mutation->flush();

  if (!m_added_param_values.empty()) {
    // Insert after last load-param (and not before first non-load-param
    // instructions, as that may suggest that the added instructions are to be
    // associated with the position of the non-load-param instruction).
    cfg.insert_after_param_loads(m_added_param_values);
    m_added_param_values.clear();
  }
}

void Transform::apply(const intraprocedural::FixpointIterator& fp_iter,
                      const WholeProgramState& wps,
                      cfg::ControlFlowGraph& cfg,
                      const XStoreRefs* xstores,
                      bool is_static,
                      DexType* declaring_type,
                      DexProto* proto) {
  swap_kotlin_areequal(fp_iter, cfg, is_static, declaring_type, proto);
  legacy_apply_constants_and_prune_unreachable(fp_iter, wps, cfg, xstores,
                                               declaring_type);
  if ((xstores != nullptr) && !g_redex->instrument_mode) {
    m_stats.unreachable_instructions_removed += cfg.simplify();
    fp_iter.clear_switch_succ_cache();
    // legacy_apply_constants_and_prune_unreachable creates some new blocks that
    // fp_iter isn't aware of. As turns out, legacy_apply_forward_targets
    // doesn't care, and will still do the right thing.
    legacy_apply_forward_targets(fp_iter, cfg, is_static, declaring_type, proto,
                                 xstores);
    m_stats.unreachable_instructions_removed +=
        cfg.remove_unreachable_blocks().first;
  }
}

void Transform::legacy_apply_constants_and_prune_unreachable(
    const intraprocedural::FixpointIterator& intra_cp,
    const WholeProgramState& wps,
    cfg::ControlFlowGraph& cfg,
    const XStoreRefs* xstores,
    const DexType* declaring_type) {
  Context context{
      .clmr = ClassLiteralMethodsReplacer::create_context(),
  };

  always_assert(m_mutation == nullptr);
  m_mutation = std::make_unique<cfg::CFGMutation>(cfg);
  npe::NullPointerExceptionCreator npe_creator(&cfg);
  for (const auto& block : cfg.blocks()) {
    auto env = intra_cp.get_entry_state_at(block);
    // This block is unreachable, no point mutating its instructions -- DCE
    // will be removing it anyway
    if (env.is_bottom()) {
      continue;
    }
    auto last_insn = block->get_last_insn();
    auto ii = InstructionIterable(block);
    for (auto it = ii.begin(); it != ii.end(); it++) {
      auto cfg_it = block->to_cfg_instruction_iterator(it);
      bool any_changes = eliminate_redundant_put(env, wps, cfg_it) ||
                         eliminate_redundant_null_check(env, wps, cfg_it) ||
                         replace_kotlin_areequal(env, cfg_it) ||
                         replace_with_throw(env, cfg_it, &npe_creator);
      auto* insn = cfg_it->insn;
      intra_cp.analyze_instruction(insn, &env, insn == last_insn->insn);
      if (!any_changes && (m_redundant_move_results.count(insn) == 0u)) {
        simplify_instruction(env, wps, cfg_it, xstores, declaring_type,
                             context);
      }
    }
    eliminate_dead_branch(intra_cp, env, cfg, block);
  }
  apply_changes(cfg);
  m_mutation = nullptr;
  cfg.simplify();
}

void Transform::forward_targets(
    const intraprocedural::FixpointIterator& intra_cp,
    const ConstantEnvironment& env,
    cfg::ControlFlowGraph& cfg,
    cfg::Block* block,
    std::unique_ptr<LivenessFixpointIterator>& liveness_fixpoint_iter) {
  always_assert(!env.is_bottom());
  // normal edges are of type goto or branch, not throw or ghost
  auto is_normal = [](const cfg::Edge* e) {
    return e->type() == cfg::EDGE_GOTO || e->type() == cfg::EDGE_BRANCH;
  };

  // Data structure that holds a possible target block, together with a set out
  // registers that would have been assigned along the way to the target block.
  struct TargetAndAssignedRegs {
    cfg::Block* target;
    UnorderedSet<reg_t> assigned_regs;
  };

  // Helper function that computs (ordered) list of unconditional target blocks,
  // together with the sets of assigned registers.
  auto get_unconditional_targets =
      [&](cfg::Edge* succ_edge) -> std::vector<TargetAndAssignedRegs> {
    auto succ_env = intra_cp.analyze_edge(succ_edge, env);
    if (succ_env.is_bottom()) {
      return {};
    }

    std::vector<TargetAndAssignedRegs> unconditional_targets{
        (TargetAndAssignedRegs){succ_edge->target(), {}}};
    UnorderedSet<cfg::Block*> visited;
    while (true) {
      auto& last_unconditional_target = unconditional_targets.back();
      auto* succ = last_unconditional_target.target;
      if (!visited.insert(succ).second) {
        // We found a loop; give up.
        return {};
      }
      // We'll have to add to the set of assigned regs, so we make an
      // intentional copy here
      auto assigned_regs = last_unconditional_target.assigned_regs;
      auto last_insn = succ->get_last_insn();
      for (auto& mie : InstructionIterable(succ)) {
        auto* insn = mie.insn;
        if (opcode::is_branch(insn->opcode())) {
          continue;
        }
        // TODO: Support side-effect-free instruction sequences involving
        // move-result(-pseudo), similar to what LocalDCE does
        if (opcode::has_side_effects(insn->opcode()) || !insn->has_dest() ||
            opcode::is_move_result_any(insn->opcode())) {
          TRACE(CONSTP, 5, "forward_targets cannot follow %s",
                SHOW(insn->opcode()));
          // We stop the analysis here.
          return unconditional_targets;
        }

        assigned_regs.insert(insn->dest());
        intra_cp.analyze_instruction(insn, &succ_env, insn == last_insn->insn);
        always_assert(!succ_env.is_bottom());
      }

      std::optional<std::pair<cfg::Block*, ConstantEnvironment>> only_feasible;
      for (auto* succ_succ_edge : cfg.get_succ_edges_if(succ, is_normal)) {
        auto succ_succ_env = intra_cp.analyze_edge(succ_succ_edge, succ_env);
        if (succ_succ_env.is_bottom()) {
          continue;
        }
        if (only_feasible) {
          // Found another one that's feasible, so there's not just a single
          // feasible successor. We stop the analysis here.
          return unconditional_targets;
        }
        only_feasible =
            std::make_pair(succ_succ_edge->target(), std::move(succ_succ_env));
      }
      if (!only_feasible) {
        // We have reached a spot where all further branches are bottom. This is
        // possible when, right here, a value equals bottom, but is not the
        // bottom element itself. For example, a SignedConstantDomain x can have
        // bounds of [1, 2] and bitset of third bit being 1. The existence of x
        // satisfies the requirement of a lattice: _|_ le x. Meanwhile, x =
        // _|_, but is not bottom.
        //
        // Give up if this happens.
        return {};
      }
      unconditional_targets.push_back(
          (TargetAndAssignedRegs){only_feasible->first, assigned_regs});
      succ_env = std::move(only_feasible->second);
      always_assert(!succ_env.is_bottom());
    }
  };

  // Helper to check if any assigned register is live at the target block
  auto is_any_assigned_reg_live_at_target =
      [&liveness_fixpoint_iter,
       &cfg](const TargetAndAssignedRegs& unconditional_target) {
        const auto& assigned_regs = unconditional_target.assigned_regs;
        if (assigned_regs.empty()) {
          return false;
        }
        if (!liveness_fixpoint_iter) {
          liveness_fixpoint_iter.reset(new LivenessFixpointIterator(cfg));
          liveness_fixpoint_iter->run(LivenessDomain());
        }
        const auto& live_in_vars = liveness_fixpoint_iter->get_live_in_vars_at(
            unconditional_target.target);
        if (live_in_vars.is_bottom()) {
          // Could happen after having applied other transformations already
          return true;
        }
        always_assert(!live_in_vars.is_top());
        const auto& elements = live_in_vars.elements();
        return unordered_any_of(assigned_regs, [&elements](reg_t reg) {
          return elements.contains(reg);
        });
      };

  // Helper function to find furthest feasible target block for which no
  // assigned regs are live-in
  auto get_furthest_target_without_live_assigned_regs =
      [&is_any_assigned_reg_live_at_target](
          const std::vector<TargetAndAssignedRegs>& unconditional_targets)
      -> cfg::Block* {
    // The first (if any) unconditional target isn't interesting, as that's the
    // one that's already currently on the cfg edge
    if (unconditional_targets.size() <= 1) {
      return nullptr;
    }

    // Find last successor where no assigned reg is live
    for (size_t i = unconditional_targets.size() - 1; i >= 1; --i) {
      const auto& unconditional_target = unconditional_targets.at(i);
      if (is_any_assigned_reg_live_at_target(unconditional_target)) {
        continue;
      }
      TRACE(CONSTP, 2,
            "forward_targets rewrites target, skipping %zu targets, discharged "
            "%zu assigned regs",
            i, unconditional_target.assigned_regs.size());
      return unconditional_target.target;
    }
    return nullptr;
  };

  // Main loop over, analyzing and potentially rewriting all normal successor
  // edges to the furthest unconditional feasible target
  for (auto* succ_edge : cfg.get_succ_edges_if(block, is_normal)) {
    auto unconditional_targets = get_unconditional_targets(succ_edge);
    auto* new_target =
        get_furthest_target_without_live_assigned_regs(unconditional_targets);
    if (new_target == nullptr) {
      continue;
    }
    // Computed BEFORE the retarget below: afterwards `block` is no longer a
    // predecessor of the first skipped target and its share of that block's
    // inflow is unrecoverable.
    //
    // `unconditional_targets.front()` is the block currently on this edge (it
    // is seeded from `succ_edge->target()`), so it is the only one that
    // actually loses a predecessor. The rest of the chain keeps its
    // predecessors -- but each link is the sole FEASIBLE successor of the one
    // before it, so all of the flow lost at the head propagates unchanged down
    // the chain. Shed the same ABSOLUTE amount from each, not the same
    // fraction: a later block with additional predecessors loses the same
    // executions but a smaller share of its own count.
    //
    // Estimate, not exact: `share_of` divides `block`'s outflow by the target's
    // predecessor total, and `block` may send only part of its flow here, so
    // this can over-shed. It cannot go negative -- shares are clamped to [0,1].
    const bool preserve_counts = g_redex->preserve_count_integrity;
    std::vector<double> departed_abs;
    if (preserve_counts && !unconditional_targets.empty()) {
      auto* head = unconditional_targets.front().target;
      auto* head_sb = source_blocks::get_first_source_block(head);
      const size_t n_slots = head_sb != nullptr ? head_sb->vals_size : 0;
      const auto pred_total =
          source_blocks::apportion::predecessor_totals(head, n_slots);
      departed_abs.reserve(n_slots);
      for (size_t i = 0; i < n_slots; ++i) {
        const double share =
            source_blocks::apportion::share_of(pred_total, block, i);
        // A negative share means no count evidence for this slot: shed nothing.
        departed_abs.push_back(
            share < 0.0 ? 0.0 : head_sb->get_val(i).value_or(0.0f) * share);
      }
    }

    // Found (last) successor where no assigned reg is live -- forward to
    // there
    cfg.set_edge_target(succ_edge, new_target);

    // When we apply this transformation, some blocks might have predecessors
    // removed In this case, the block's source block values should at most be
    // the maximum of the other predecessor blocks.

    // This is an optimization, if block wasn't hit, we don't need to fix up
    // source blocks
    auto* last_source_sb = source_blocks::get_last_source_block(block);
    bool block_was_hit = false;
    if (last_source_sb != nullptr) {
      block_was_hit = last_source_sb->foreach_val_early(
          [](const auto& v) { return v && v->val > 0; });
    }
    if (block_was_hit && !g_redex->disable_violation_fixes) {
      // Iterate over the chain of unconditional targets
      for (const auto& [target, _] : unconditional_targets) {
        if (target == new_target) {
          // If we get to the new_target we're done, just break
          break;
        }
        if (source_blocks::has_source_blocks(target)) {
          if (preserve_counts) {
            // Re-express the absolute departed flow as this block's own
            // fraction, so every SourceBlock in it -- they annotate the same
            // program point -- is scaled consistently.
            auto* t_sb = source_blocks::get_first_source_block(target);
            std::vector<double> leaving;
            leaving.reserve(departed_abs.size());
            size_t slot = 0;
            for (const double departed : departed_abs) {
              const double v =
                  t_sb != nullptr ? t_sb->get_val(slot).value_or(0.0f) : 0.0;
              leaving.push_back(v > 0.0 ? std::min(1.0, departed / v) : 0.0);
              ++slot;
            }
            source_blocks::apportion::shrink_by_departed(target, leaving);
          } else {
            source_blocks::scale_source_blocks(target);
          }
        }
      }
    }

    ++m_stats.branches_forwarded;
  }
  // TODO: Forwarding may leave behind trivial conditional branches that can
  // be folded.
}

bool Transform::has_problematic_return(cfg::ControlFlowGraph& cfg,
                                       bool is_static,
                                       DexType* declaring_type,
                                       DexProto* proto,
                                       const XStoreRefs* xstores) {
  static AccumulatingTimer s_timer(
      "constant_propagation::Transform::has_problematic_return");
  auto t = s_timer.scope();

  // Nothing to check without method information
  if ((declaring_type == nullptr) || (proto == nullptr)) {
    return false;
  }

  // No return issues when rtype is primitive
  auto* rtype = proto->get_rtype();
  if (type::is_primitive(rtype)) {
    return false;
  }

  // No return issues when there are no try/catch blocks
  auto blocks = cfg.blocks();
  bool has_catch =
      std::any_of(blocks.begin(), blocks.end(),
                  [](cfg::Block* block) { return block->is_catch(); });
  if (!has_catch) {
    return false;
  }

  auto is_relevant_def = [](auto* insn) {
    auto op = insn->opcode();
    return insn->has_type() || insn->has_method() || op == OPCODE_IGET_OBJECT ||
           op == OPCODE_SGET_OBJECT || op == OPCODE_AGET_OBJECT;
  };
  auto ii = InstructionIterable(cfg);
  auto has_relevant_def = std::any_of(ii.begin(), ii.end(), [&](auto& mie) {
    return is_relevant_def(mie.insn);
  });
  if (!has_relevant_def) {
    return false;
  }

  // For all return instructions, check whether the reaching definitions are of
  // a type that's unavailable/external, or defined in a different store.
  auto declaring_class_idx = xstores->get_store_idx(declaring_type);
  auto is_problematic_return_type = [&](const DexType* t, IRInstruction* insn) {
    t = type::make_element_type_if_array(t);
    if (type_class_internal(t) == nullptr) {
      // An unavailable or external class
      TRACE(CONSTP, 2,
            "Skipping {%s::%s} because {%s} is unavailable/external in {%s}",
            SHOW(declaring_type), SHOW(proto), SHOW(t), SHOW(insn));
      return true;
    }
    if (xstores == nullptr) {
      return false;
    }
    auto t_idx = xstores->get_store_idx(t);
    if (t_idx == declaring_class_idx) {
      return false;
    }
    TRACE(CONSTP, 2,
          "Skipping {%s::%s} because {%s} is from different store (%zu vs %zu) "
          "in "
          "{%s}",
          SHOW(declaring_type), SHOW(proto), SHOW(t), declaring_class_idx,
          t_idx, SHOW(insn));
    return true;
  };
  reaching_defs::MoveAwareFixpointIterator fp_iter(cfg, is_relevant_def);
  fp_iter.run({});
  std::unique_ptr<type_inference::TypeInference> ti;
  for (cfg::Block* block : blocks) {
    auto env = fp_iter.get_entry_state_at(block);
    if (env.is_bottom()) {
      continue;
    }
    for (auto& mie : InstructionIterable(block)) {
      IRInstruction* insn = mie.insn;
      if (opcode::is_a_return(insn->opcode())) {
        const auto& defs = env.get(insn->src(0));
        always_assert(!defs.is_bottom());
        always_assert(!defs.is_top());
        for (auto* def : defs.elements()) {
          auto op = def->opcode();
          if (def->has_type()) {
            if (is_problematic_return_type(def->get_type(), def)) {
              return true;
            }
          } else if (def->has_method()) {
            always_assert(opcode::is_an_invoke(op));
            if (is_problematic_return_type(
                    def->get_method()->get_proto()->get_rtype(), def)) {
              return true;
            }
          } else if (op == OPCODE_IGET_OBJECT || op == OPCODE_SGET_OBJECT) {
            if (is_problematic_return_type(def->get_field()->get_type(), def)) {
              return true;
            }
          } else if (op == OPCODE_AGET_OBJECT) {
            if (!ti) {
              ti.reset(new type_inference::TypeInference(cfg));
              ti->run(is_static, declaring_type, proto->get_args());
            }
            auto& type_environments = ti->get_type_environments();
            auto& type_environment = type_environments.at(def);
            auto dex_type = type_environment.get_dex_type(def->src(1));
            if (dex_type && type::is_array(*dex_type) &&
                is_problematic_return_type(
                    type::make_array_component_type(*dex_type), def)) {
              return true;
            }
          } else {
            not_reached();
          }
        }
      }
      fp_iter.analyze_instruction(insn, &env);
    }
  }
  return false;
}

void Transform::legacy_apply_forward_targets(
    const intraprocedural::FixpointIterator& intra_cp,
    cfg::ControlFlowGraph& cfg,
    bool is_static,
    DexType* declaring_type,
    DexProto* proto,
    const XStoreRefs* xstores) {
  cfg.calculate_exit_block();

  // The following is an attempt to avoid creating a control-flow structure that
  // triggers the Android bug described in T55782799, related to a return
  // statement in a try region when a type is unavailable/external, possibly
  // from a different store.
  // Besides that Android bug, it really shouldn't be necessary to do anything
  // special about unavailable types or cross-store references here.
  if (has_problematic_return(cfg, is_static, declaring_type, proto, xstores)) {
    return;
  }

  // Note that the given intra_cp might not be aware of all blocks that exist in
  // the cfg.
  std::unique_ptr<LivenessFixpointIterator> liveness_fixpoint_iter;
  for (auto* block : cfg.blocks()) {
    const auto& env = intra_cp.get_exit_state_at(block);
    if (env.is_bottom()) {
      // We found an unreachable block, or one that was added the cfg after
      // intra_cp has run; just ignore it.
      continue;
    }
    forward_targets(intra_cp, env, cfg, block, liveness_fixpoint_iter);
  }
}

void Transform::Stats::log_metrics(ScopedMetrics& sm, bool with_scope) const {
  using OptScope = std::optional<ScopedMetrics::Scope>;
  OptScope scope = with_scope ? OptScope(sm.scope("const_prop")) : std::nullopt;
  sm.set_metric("branches_forwarded", branches_forwarded);
  sm.set_metric("branch_propagated", branches_removed);
  sm.set_metric("materialized_consts", materialized_consts);
  sm.set_metric("throws", throws);
  sm.set_metric("null_checks", null_checks);
  sm.set_metric("null_checks_method_calls", null_checks_method_calls);
  sm.set_metric("unreachable_instructions_removed",
                unreachable_instructions_removed);
  sm.set_metric("redundant_puts_removed", redundant_puts_removed);
  TRACE(CONSTP, 3, "Null checks removed: %zu(%zu)", null_checks,
        null_checks_method_calls);
  sm.set_metric("added_param_const", added_param_const);
  sm.set_metric("class_isinstance_replaced", class_isinstance_replaced);
  sm.set_metric("class_cast_replaced", class_cast_replaced);
  sm.set_metric("kotlin_areequal_swapped", kotlin_areequal_swapped);
  sm.set_metric("kotlin_areequal_replaced", kotlin_areequal_replaced);
}

} // namespace constant_propagation
