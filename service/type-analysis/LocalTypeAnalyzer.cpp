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

bool field_get_helper(const DexType* class_under_init,
                      const IRInstruction* insn,
                      DexTypeEnvironment* env) {
  auto* field = resolve_field(insn->get_field());
  if (field == nullptr) {
    return false;
  }
  if (field->get_class() == class_under_init) {
    env->set(RESULT_REGISTER, env->get(field));
    return true;
  }
  return false;
}

bool field_put_helper(const DexType* class_under_init,
                      const IRInstruction* insn,
                      DexTypeEnvironment* env) {
  auto* field = resolve_field(insn->get_field());
  if (field == nullptr) {
    return false;
  }
  if (field->get_class() == class_under_init) {
    env->set(field, env->get(insn->src(0)));
    return true;
  }
  return false;
}

} // namespace

bool CtorFieldAnalyzer::analyze_default(const DexType* class_under_init,
                                        const IRInstruction* insn,
                                        DexTypeEnvironment* env) {
  if (class_under_init == nullptr) {
    return false;
  }
  if (insn->has_dest()) {
    env->set_this_ptr(insn->dest(), IsDomain::top());
    if (insn->dest_is_wide()) {
      env->set_this_ptr(insn->dest() + 1, IsDomain::top());
    }
  } else if (insn->has_move_result_any()) {
    env->set_this_ptr(RESULT_REGISTER, IsDomain::top());
  }
  return false;
}

bool CtorFieldAnalyzer::analyze_load_param(const DexType* class_under_init,
                                           const IRInstruction* insn,
                                           DexTypeEnvironment* env) {
  if ((class_under_init == nullptr) ||
      insn->opcode() != IOPCODE_LOAD_PARAM_OBJECT) {
    return false;
  }
  if (env->get_this_ptr_environment().is_top()) {
    env->set_this_ptr(insn->dest(), IsDomain(true));
  }
  return false;
}

bool CtorFieldAnalyzer::analyze_iget(const DexType* class_under_init,
                                     const IRInstruction* insn,
                                     DexTypeEnvironment* env) {
  if (!env->is_this_ptr(insn->src(0))) {
    return false;
  }
  return field_get_helper(class_under_init, insn, env);
}

bool CtorFieldAnalyzer::analyze_iput(const DexType* class_under_init,
                                     const IRInstruction* insn,
                                     DexTypeEnvironment* env) {
  if (!env->is_this_ptr(insn->src(1))) {
    return false;
  }
  return field_put_helper(class_under_init, insn, env);
}

bool CtorFieldAnalyzer::analyze_move(const DexType* class_under_init,
                                     const IRInstruction* insn,
                                     DexTypeEnvironment* env) {
  if (class_under_init == nullptr) {
    return false;
  }
  env->set_this_ptr(insn->dest(), env->get_this_ptr(insn->src(0)));
  return false;
}

bool CtorFieldAnalyzer::analyze_move_result(const DexType* class_under_init,
                                            const IRInstruction* insn,
                                            DexTypeEnvironment* env) {
  if (class_under_init == nullptr) {
    return false;
  }
  env->set_this_ptr(insn->dest(), env->get_this_ptr(RESULT_REGISTER));
  return false;
}

bool CtorFieldAnalyzer::analyze_invoke(const DexType* class_under_init,
                                       const IRInstruction* insn,
                                       DexTypeEnvironment* env) {
  // Similar to the logic in constant_propagation::InitFieldAnalyzer, we try to
  // be conservative when the ctor invokes other virtual methods on the same
  // class, and reset the field environment.
  auto opcode = insn->opcode();
  if ((opcode == OPCODE_INVOKE_VIRTUAL || opcode == OPCODE_INVOKE_DIRECT) &&
      class_under_init == insn->get_method()->get_class()) {
    env->clear_field_environment();
  }
  return false;
}

} // namespace local

} // namespace type_analyzer
