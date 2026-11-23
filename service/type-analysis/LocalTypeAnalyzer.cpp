/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "LocalTypeAnalyzer.h"

#include "Debug.h"
#include "Resolver.h"
#include "Show.h"
#include "Trace.h"

using namespace type_analyzer;

namespace type_analyzer {

namespace local {

/*
 * For debugging only
 * void traceEnvironment(DexTypeEnvironment* env) {
 *   std::ostringstream out;
 *   out << *env;
 *   TRACE(TYPE, 9, "%s", out.str().c_str());
 * }
 */

void LocalTypeAnalyzer::analyze_instruction(const IRInstruction* insn,
                                            DexTypeEnvironment* env) const {
  TRACE(TYPE, 9, "Analyzing instruction: %s", SHOW(insn));
  m_insn_analyzer(insn, env);
}

bool RegisterTypeAnalyzer::analyze_default(const IRInstruction* insn,
                                           DexTypeEnvironment* env) {
  if (opcode::is_a_load_param(insn->opcode())) {
    return true;
  }
  if (insn->has_dest()) {
    env->set(insn->dest(), DexTypeDomain::top());
    if (insn->dest_is_wide()) {
      env->set(insn->dest() + 1, DexTypeDomain::top());
    }
  } else if (insn->has_move_result_any()) {
    env->set(RESULT_REGISTER, DexTypeDomain::top());
  }
  return true;
}

bool RegisterTypeAnalyzer::analyze_check_cast(const IRInstruction* insn,
                                              DexTypeEnvironment* env) {
  if (type::is_array(insn->get_type())) {
    env->set(RESULT_REGISTER, DexTypeDomain::top());
  } else {
    env->set(RESULT_REGISTER, env->get(insn->src(0)));
  }
  return true;
}

bool RegisterTypeAnalyzer::analyze_const(const IRInstruction* insn,
                                         DexTypeEnvironment* env) {
  if (insn->opcode() != OPCODE_CONST) {
    return false;
  }
  if (insn->get_literal() == 0) {
    env->set(insn->dest(), DexTypeDomain::null());
  } else {
    env->set(insn->dest(), DexTypeDomain::top());
  }
  return true;
}

bool RegisterTypeAnalyzer::analyze_const_string(const IRInstruction*,
                                                DexTypeEnvironment* env) {
  env->set(RESULT_REGISTER,
           DexTypeDomain::create_not_null(type::java_lang_String()));
  return true;
}

bool RegisterTypeAnalyzer::analyze_const_class(const IRInstruction*,
                                               DexTypeEnvironment* env) {
  env->set(RESULT_REGISTER,
           DexTypeDomain::create_not_null(type::java_lang_Class()));
  return true;
}

bool RegisterTypeAnalyzer::analyze_aget(const IRInstruction* insn,
                                        DexTypeEnvironment* env) {
  auto array_type = env->get(insn->src(0)).get_dex_type();
  if (!array_type || (*array_type == nullptr)) {
    env->set(RESULT_REGISTER, DexTypeDomain::top());
    return true;
  }

  always_assert_log(type::is_array(*array_type), "Wrong array type %s in %s",
                    SHOW(*array_type), SHOW(insn));
  auto* const ctype = type::make_array_component_type(*array_type);
  env->set(RESULT_REGISTER, DexTypeDomain::create_nullable(ctype));
  return true;
}

bool RegisterTypeAnalyzer::analyze_move(const IRInstruction* insn,
                                        DexTypeEnvironment* env) {
  env->set(insn->dest(), env->get(insn->src(0)));
  return true;
}

bool RegisterTypeAnalyzer::analyze_move_result(const IRInstruction* insn,
                                               DexTypeEnvironment* env) {
  env->set(insn->dest(), env->get(RESULT_REGISTER));
  return true;
}

bool RegisterTypeAnalyzer::analyze_move_exception(const IRInstruction* insn,
                                                  DexTypeEnvironment* env) {
  // We don't know where to grab the exact type of the just-caught exception,
  // so fall back to j.l.Throwable. The runtime never stores a null reference
  // into the handler register, so narrow the nullness. Note that
  // create_not_null cannot be used here: it would additionally record
  // j.l.Throwable as the *exact* runtime class in the SmallSetDexTypeDomain,
  // while the real class is a subclass.
  auto domain = DexTypeDomain::create_nullable(type::java_lang_Throwable());
  domain.apply<0>([](auto* val) { *val = NullnessDomain(Nullness::NOT_NULL); });
  env->set(insn->dest(), domain);
  return true;
}

bool RegisterTypeAnalyzer::analyze_new_instance(const IRInstruction* insn,
                                                DexTypeEnvironment* env) {
  env->set(RESULT_REGISTER, DexTypeDomain::create_not_null(insn->get_type()));
  return true;
}

bool RegisterTypeAnalyzer::analyze_new_array(const IRInstruction* insn,
                                             DexTypeEnvironment* env) {
  // Skip array element nullness domains.
  env->set(RESULT_REGISTER, DexTypeDomain::create_not_null(insn->get_type()));
  return true;
}

bool RegisterTypeAnalyzer::analyze_filled_new_array(const IRInstruction* insn,
                                                    DexTypeEnvironment* env) {
  env->set(RESULT_REGISTER, DexTypeDomain::create_not_null(insn->get_type()));
  return true;
}

bool RegisterTypeAnalyzer::analyze_invoke(const IRInstruction* insn,
                                          DexTypeEnvironment* env) {
  auto* method =
      resolve_method_deprecated(insn->get_method(), opcode_to_search(insn));
  if (method == nullptr) {
    return analyze_default(insn, env);
  }
  // Note we don't need to take care of the RESULT_REGISTER update from this
  // point. The remaining cases are already taken care by the
  // WholeProgramAwareAnalyzer::analyze_invoke.
  return false;
}

namespace {

// The access `insn` makes to a field of the class under construction.
const local_pointers::FieldAccess* get_field_access(
    const CtorFieldAnalyzer::State& state, const IRInstruction* insn) {
  if (state.accesses == nullptr) {
    return nullptr;
  }
  const auto& accesses = state.accesses->field_accesses();
  auto it = accesses.find(insn);
  return it == accesses.end() ? nullptr : &it->second;
}

} // namespace

bool CtorFieldAnalyzer::analyze_iget(const State& state,
                                     const IRInstruction* insn,
                                     DexTypeEnvironment* env) {
  const auto* access = get_field_access(state, insn);
  if (access == nullptr || access->receiver != local_pointers::Receiver::This) {
    return false;
  }
  if (access->after_escape &&
      state.constructor_only_fields->count(access->field) == 0u) {
    return false;
  }
  auto type = env->get(access->field);
  if (type.is_top()) {
    // The constructor has not stored a known type; let the whole-program
    // state answer.
    return false;
  }
  env->set(RESULT_REGISTER, type);
  return true;
}

bool CtorFieldAnalyzer::analyze_iput(const State& state,
                                     const IRInstruction* insn,
                                     DexTypeEnvironment* env) {
  const auto* access = get_field_access(state, insn);
  if (access == nullptr ||
      access->receiver == local_pointers::Receiver::Other) {
    return false;
  }
  auto type = env->get(insn->src(0));
  if (access->receiver == local_pointers::Receiver::MaybeThis) {
    type.join_with(env->get(access->field));
  }
  env->set(access->field, type);
  return true;
}

bool CtorFieldAnalyzer::analyze_invoke(const State& state,
                                       const IRInstruction* insn,
                                       DexTypeEnvironment* env) {
  if (state.accesses != nullptr &&
      state.accesses->get_delegating_call(insn) != nullptr) {
    env->clear_field_environment();
  }
  return false;
}

} // namespace local

} // namespace type_analyzer
