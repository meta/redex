/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <functional>
#include <type_traits>
#include <utility>

#include "IRInstruction.h"
#include "TemplateUtil.h"

/*
 * This module provides a way to compose analyses over IRInstructions.
 *
 * Implementors should define sub-analyzers that inherit from
 * InstructionAnalyzerBase. These sub-analyzers can then be composed using
 * the InstructionAnalyzerCombiner.
 */

/* clang-format off */
// Opcodes are grouped on the basis that most analyses will want to handle all
// opcodes in a given group similarly.
#define OPCODE_GROUPS \
  X(load_param)       \
  X(nop)              \
  X(move)             \
  X(move_result)      \
  X(move_exception)   \
  X(return)           \
  X(monitor)          \
  X(const)            \
  X(const_string)     \
  X(const_class)      \
  X(check_cast)       \
  X(instance_of)      \
  X(array_length)     \
  X(new_instance)     \
  X(new_array)        \
  X(filled_new_array) \
  X(fill_array_data)  \
  X(throw)            \
  X(goto)             \
  X(switch)           \
  X(cmp)              \
  X(if)               \
  X(aget)             \
  X(aput)             \
  X(iget)             \
  X(iput)             \
  X(sget)             \
  X(sput)             \
  X(invoke)           \
  X(dynamic_invoke)   \
  X(unop)             \
  X(binop)            \
  X(binop_lit)        \
  X(init_class)       \
  X(r_const)          \
  X(injection_id)     \
  X(unreachable)      \
  X(write_barrier)

/* clang-format on */

/*
 * A sub-analyzer is simply a description of how to mutate an Environment given
 * an IRInstruction.
 *
 * Sub-analyzers should implement the analyze_* methods for the opcode groups
 * they are interested in. These methods should return `false` if they want
 * subsequent sub-analyzers to run, and `true` if the analysis for the given
 * instruction should terminate. In general, a sub-analysis should return
 * `true` if it believes subsequent analyses will not be able to further refine
 * the environment.
 *
 * All sub-analyzers should inherit from this class, which uses CRTP to mimic
 * virtual dispatch on static methods. It provides a default implementation for
 * all opcode group analyses, which is simply a dispatch to the analyze_default
 * method in the derived class.
 *
 * We use CRTP because we want each sub-analyzer to only comprise static
 * methods. That ensures that the compiler can inline and elide as many calls
 * as possible. This is important because most sub-analyzers will only define a
 * small number of nontrivial instruction analyses.
 *
 * Limiting ourselves to static methods means that we have no `this` object
 * to store state. State is instead passed as an explicit argument to each
 * method.
 */
template <typename Derived, typename Env_, typename State_ = std::nullptr_t>
class InstructionAnalyzerBase {
 public:
  using Env = Env_;
  using State = State_;

  static bool analyze_default(const State& /*state*/,
                              const IRInstruction* /*insn*/,
                              Env* /*env*/) {
    return false;
  }

#define X(opcode_group)                                          \
  static bool analyze_wrapper_##opcode_group(                    \
      const State& state, const IRInstruction* insn, Env* env) { \
    return Derived::analyze_##opcode_group(state, insn, env);    \
  }                                                              \
  static bool analyze_##opcode_group(                            \
      const State& state, const IRInstruction* insn, Env* env) { \
    return Derived::analyze_default(state, insn, env);           \
  }
  OPCODE_GROUPS
#undef X
};

/*
 * Some sub-analyzers have no need for state. This partial template
 * specialization makes them easier to write -- instead of passing an unused
 * nullptr around, the analyze_* methods can omit the state parameter entirely.
 */
template <typename Derived, typename Env_>
class InstructionAnalyzerBase<Derived, Env_, std::nullptr_t> {
 public:
  using State = std::nullptr_t;
  using Env = Env_;

  static bool analyze_default(const IRInstruction* /*insn*/, Env* /*env*/) {
    return false;
  }

  // Note that defining a static method in a subclass hides all methods in the
  // superclass of the same name, *regardless of signature*. As such, we
  // define analyze_wrapper_##opcode_group here instead of overloading the
  // signature of analyze_##opcode_group so that the analyze_wrapper methods
  // don't get hidden when the analyzer implementor defines its analyze_*
  // methods.
#define X(opcode_group)                                                     \
  static bool analyze_wrapper_##opcode_group(                               \
      std::nullptr_t, const IRInstruction* insn, Env* env) {                \
    return Derived::analyze_##opcode_group(insn, env);                      \
  }                                                                         \
  static bool analyze_##opcode_group(const IRInstruction* insn, Env* env) { \
    return Derived::analyze_default(insn, env);                             \
  }
  OPCODE_GROUPS
#undef X
};

/*
 * operator() of this class will run each sub-analyzer in the Analyzers
 * list from left to right on the given instruction.
 */
template <typename... Analyzers>
class InstructionAnalyzerCombiner final {
 public:
  // All Analyzers should have the same Env type.
  using Env = typename std::common_type<typename Analyzers::Env...>::type;

  static_assert(
      std::conjunction_v<
          std::is_base_of<InstructionAnalyzerBase<Analyzers,
                                                  typename Analyzers::Env,
                                                  typename Analyzers::State>,
                          Analyzers>...>,
      "Not all analyses inherit from the right instance of "
      "InstructionAnalyzerBase!");

  explicit InstructionAnalyzerCombiner(typename Analyzers::State... states)
      : m_states(std::make_tuple(states...)) {}

  // If all sub-analyzers have a default-constructible state, then this
  // combined analyzer is default-constructible.
  template <bool Enabled = std::conjunction_v<
                std::is_default_constructible<typename Analyzers::State>...>,
            typename = std::enable_if_t<Enabled>>
  InstructionAnalyzerCombiner()
      : m_states(std::make_tuple(typename Analyzers::State()...)) {}

  void operator()(const IRInstruction* insn, Env* env) const {
    auto op = insn->opcode();
    switch (op) {
    case IOPCODE_LOAD_PARAM:
    case IOPCODE_LOAD_PARAM_OBJECT:
    case IOPCODE_LOAD_PARAM_WIDE:
      return analyze_load_param(
          std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_NOP:
      return analyze_nop(std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_MOVE:
    case OPCODE_MOVE_WIDE:
    case OPCODE_MOVE_OBJECT:
      return analyze_move(std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_MOVE_RESULT:
    case OPCODE_MOVE_RESULT_WIDE:
    case OPCODE_MOVE_RESULT_OBJECT:
    case IOPCODE_MOVE_RESULT_PSEUDO:
    case IOPCODE_MOVE_RESULT_PSEUDO_OBJECT:
    case IOPCODE_MOVE_RESULT_PSEUDO_WIDE:
      return analyze_move_result(
          std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_MOVE_EXCEPTION:
      return analyze_move_exception(
          std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_RETURN_VOID:
    case OPCODE_RETURN:
    case OPCODE_RETURN_WIDE:
    case OPCODE_RETURN_OBJECT:
      return analyze_return(std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_MONITOR_ENTER:
    case OPCODE_MONITOR_EXIT:
      return analyze_monitor(
          std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_THROW:
      return analyze_throw(std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_GOTO:
      return analyze_goto(std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_NEG_INT:
    case OPCODE_NOT_INT:
    case OPCODE_NEG_LONG:
    case OPCODE_NOT_LONG:
    case OPCODE_NEG_FLOAT:
    case OPCODE_NEG_DOUBLE:
    case OPCODE_INT_TO_LONG:
    case OPCODE_INT_TO_FLOAT:
    case OPCODE_INT_TO_DOUBLE:
    case OPCODE_LONG_TO_INT:
    case OPCODE_LONG_TO_FLOAT:
    case OPCODE_LONG_TO_DOUBLE:
    case OPCODE_FLOAT_TO_INT:
    case OPCODE_FLOAT_TO_LONG:
    case OPCODE_FLOAT_TO_DOUBLE:
    case OPCODE_DOUBLE_TO_INT:
    case OPCODE_DOUBLE_TO_LONG:
    case OPCODE_DOUBLE_TO_FLOAT:
    case OPCODE_INT_TO_BYTE:
    case OPCODE_INT_TO_CHAR:
    case OPCODE_INT_TO_SHORT:
      return analyze_unop(std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_ARRAY_LENGTH:
      return analyze_array_length(
          std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_CMPL_FLOAT:
    case OPCODE_CMPG_FLOAT:
    case OPCODE_CMPL_DOUBLE:
    case OPCODE_CMPG_DOUBLE:
    case OPCODE_CMP_LONG:
      return analyze_cmp(std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_IF_EQ:
    case OPCODE_IF_NE:
    case OPCODE_IF_LT:
    case OPCODE_IF_GE:
    case OPCODE_IF_GT:
    case OPCODE_IF_LE:
    case OPCODE_IF_EQZ:
    case OPCODE_IF_NEZ:
    case OPCODE_IF_LTZ:
    case OPCODE_IF_GEZ:
    case OPCODE_IF_GTZ:
    case OPCODE_IF_LEZ:
      return analyze_if(std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_AGET:
    case OPCODE_AGET_WIDE:
    case OPCODE_AGET_OBJECT:
    case OPCODE_AGET_BOOLEAN:
    case OPCODE_AGET_BYTE:
    case OPCODE_AGET_CHAR:
    case OPCODE_AGET_SHORT:
      return analyze_aget(std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_APUT:
    case OPCODE_APUT_WIDE:
    case OPCODE_APUT_OBJECT:
    case OPCODE_APUT_BOOLEAN:
    case OPCODE_APUT_BYTE:
    case OPCODE_APUT_CHAR:
    case OPCODE_APUT_SHORT:
      return analyze_aput(std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_ADD_INT:
    case OPCODE_SUB_INT:
    case OPCODE_MUL_INT:
    case OPCODE_DIV_INT:
    case OPCODE_REM_INT:
    case OPCODE_AND_INT:
    case OPCODE_OR_INT:
    case OPCODE_XOR_INT:
    case OPCODE_SHL_INT:
    case OPCODE_SHR_INT:
    case OPCODE_USHR_INT:
    case OPCODE_ADD_LONG:
    case OPCODE_SUB_LONG:
    case OPCODE_MUL_LONG:
    case OPCODE_DIV_LONG:
    case OPCODE_REM_LONG:
    case OPCODE_AND_LONG:
    case OPCODE_OR_LONG:
    case OPCODE_XOR_LONG:
    case OPCODE_SHL_LONG:
    case OPCODE_SHR_LONG:
    case OPCODE_USHR_LONG:
    case OPCODE_ADD_FLOAT:
    case OPCODE_SUB_FLOAT:
    case OPCODE_MUL_FLOAT:
    case OPCODE_DIV_FLOAT:
    case OPCODE_REM_FLOAT:
    case OPCODE_ADD_DOUBLE:
    case OPCODE_SUB_DOUBLE:
    case OPCODE_MUL_DOUBLE:
    case OPCODE_DIV_DOUBLE:
    case OPCODE_REM_DOUBLE:
      return analyze_binop(std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_ADD_INT_LIT:
    case OPCODE_RSUB_INT_LIT:
    case OPCODE_MUL_INT_LIT:
    case OPCODE_DIV_INT_LIT:
    case OPCODE_REM_INT_LIT:
    case OPCODE_AND_INT_LIT:
    case OPCODE_OR_INT_LIT:
    case OPCODE_XOR_INT_LIT:
    case OPCODE_SHL_INT_LIT:
    case OPCODE_SHR_INT_LIT:
    case OPCODE_USHR_INT_LIT:
      return analyze_binop_lit(
          std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_CONST:
    case OPCODE_CONST_WIDE:
    case OPCODE_CONST_METHOD_HANDLE:
    case OPCODE_CONST_METHOD_TYPE:
      return analyze_const(std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_CONST_STRING:
      return analyze_const_string(
          std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_CONST_CLASS:
      return analyze_const_class(
          std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_FILL_ARRAY_DATA:
      return analyze_fill_array_data(
          std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_SWITCH:
      return analyze_switch(std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_IGET:
    case OPCODE_IGET_WIDE:
    case OPCODE_IGET_OBJECT:
    case OPCODE_IGET_BOOLEAN:
    case OPCODE_IGET_BYTE:
    case OPCODE_IGET_CHAR:
    case OPCODE_IGET_SHORT:
      return analyze_iget(std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_IPUT:
    case OPCODE_IPUT_WIDE:
    case OPCODE_IPUT_OBJECT:
    case OPCODE_IPUT_BOOLEAN:
    case OPCODE_IPUT_BYTE:
    case OPCODE_IPUT_CHAR:
    case OPCODE_IPUT_SHORT:
      return analyze_iput(std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_SGET:
    case OPCODE_SGET_WIDE:
    case OPCODE_SGET_OBJECT:
    case OPCODE_SGET_BOOLEAN:
    case OPCODE_SGET_BYTE:
    case OPCODE_SGET_CHAR:
    case OPCODE_SGET_SHORT:
      return analyze_sget(std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_SPUT:
    case OPCODE_SPUT_WIDE:
    case OPCODE_SPUT_OBJECT:
    case OPCODE_SPUT_BOOLEAN:
    case OPCODE_SPUT_BYTE:
    case OPCODE_SPUT_CHAR:
    case OPCODE_SPUT_SHORT:
      return analyze_sput(std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_INVOKE_VIRTUAL:
    case OPCODE_INVOKE_SUPER:
    case OPCODE_INVOKE_DIRECT:
    case OPCODE_INVOKE_STATIC:
    case OPCODE_INVOKE_INTERFACE:
      return analyze_invoke(std::index_sequence_for<Analyzers...>{}, insn, env);
    // These call whatever their method handle or call site links to, so there
    // is no callee to resolve.
    case OPCODE_INVOKE_POLYMORPHIC:
    case OPCODE_INVOKE_CUSTOM:
      return analyze_dynamic_invoke(
          std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_CHECK_CAST:
      return analyze_check_cast(
          std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_INSTANCE_OF:
      return analyze_instance_of(
          std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_NEW_INSTANCE:
      return analyze_new_instance(
          std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_NEW_ARRAY:
      return analyze_new_array(
          std::index_sequence_for<Analyzers...>{}, insn, env);
    case OPCODE_FILLED_NEW_ARRAY:
      return analyze_filled_new_array(
          std::index_sequence_for<Analyzers...>{}, insn, env);
    case IOPCODE_R_CONST:
      return analyze_r_const(
          std::index_sequence_for<Analyzers...>{}, insn, env);
    case IOPCODE_INIT_CLASS:
      return analyze_init_class(
          std::index_sequence_for<Analyzers...>{}, insn, env);
    case IOPCODE_INJECTION_ID:
      return analyze_injection_id(
          std::index_sequence_for<Analyzers...>{}, insn, env);
    case IOPCODE_UNREACHABLE:
      return analyze_unreachable(
          std::index_sequence_for<Analyzers...>{}, insn, env);
    case IOPCODE_WRITE_BARRIER:
      return analyze_write_barrier(
          std::index_sequence_for<Analyzers...>{}, insn, env);
    }
  }

 private:
// Fold expr over a parameter pack.
// See http://articles.emptycrate.com/2016/05/14/folds_in_cpp11_ish.html for
// details.
#define FOLD(expr) \
  std::initializer_list<int> { (expr, 0)... }

// Run the sub-analyzers in order, passing them their associated state.
// See
// http://aherrmann.github.io/programming/2016/02/28/unpacking-tuples-in-cpp14/
// for an explanation of how index_sequence is used to extract the correct
// state from the m_states tuple.
#define X(opcode_group)                                                        \
  template <size_t... Is>                                                      \
  void analyze_##opcode_group(                                                 \
      std::index_sequence<Is...>, const IRInstruction* insn, Env* env) const { \
    bool run_next{true};                                                       \
    FOLD(run_next = run_next && !Analyzers::analyze_wrapper_##opcode_group(    \
                                    std::get<Is>(m_states), insn, env));       \
  }
  OPCODE_GROUPS
#undef X

#undef FOLD

  std::tuple<typename Analyzers::State...> m_states;
};

#undef OPCODE_GROUPS

/*
 * An instance of InstructionAnalyzerCombiner can be type-erased using
 * std::function. We define this alias template for a convenient way to name
 * these types.
 */
template <typename Env>
using InstructionAnalyzer =
    std::function<void(const IRInstruction* insn, Env* env)>;
