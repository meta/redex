/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "LocalPointersAnalysis.h"

#include <ostream>

#include "Debug.h"
#include "Show.h"
#include "TypeUtil.h"
#include "Walkers.h"
#include "WorkQueue.h"

using namespace local_pointers;

namespace {

using namespace ir_analyzer;

/*
 * Whether the dest of an instruction may be a pointer value. The only time
 * there is an uncertainty as to whether the dest is a pointer or not is when
 * we have a `const 0` instruction, since that may be either a null pointer or
 * a zero integer.
 */
bool dest_may_be_pointer(const IRInstruction* insn) {
  auto op = insn->opcode();
  switch (op) {
  case OPCODE_NOP:
    not_reached_log("No dest");
  case OPCODE_MOVE:
  case OPCODE_MOVE_WIDE:
    return false;
  case OPCODE_MOVE_OBJECT:
    return true;
  case OPCODE_MOVE_RESULT:
  case OPCODE_MOVE_RESULT_WIDE:
    return false;
  case OPCODE_MOVE_RESULT_OBJECT:
  case OPCODE_MOVE_EXCEPTION:
    return true;
  case OPCODE_RETURN_VOID:
  case OPCODE_RETURN:
  case OPCODE_RETURN_WIDE:
  case OPCODE_RETURN_OBJECT:
    not_reached_log("No dest");
  case OPCODE_MONITOR_ENTER:
  case OPCODE_MONITOR_EXIT:
  case OPCODE_THROW:
  case OPCODE_GOTO:
    not_reached_log("No dest");
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
  case OPCODE_ARRAY_LENGTH:
  case OPCODE_CMPL_FLOAT:
  case OPCODE_CMPG_FLOAT:
  case OPCODE_CMPL_DOUBLE:
  case OPCODE_CMPG_DOUBLE:
  case OPCODE_CMP_LONG:
    return false;
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
    not_reached_log("No dest");
  case OPCODE_AGET:
  case OPCODE_AGET_WIDE:
    return false;
  case OPCODE_AGET_OBJECT:
    return true;
  case OPCODE_AGET_BOOLEAN:
  case OPCODE_AGET_BYTE:
  case OPCODE_AGET_CHAR:
  case OPCODE_AGET_SHORT:
    return false;
  case OPCODE_APUT:
  case OPCODE_APUT_WIDE:
  case OPCODE_APUT_OBJECT:
  case OPCODE_APUT_BOOLEAN:
  case OPCODE_APUT_BYTE:
  case OPCODE_APUT_CHAR:
  case OPCODE_APUT_SHORT:
    not_reached_log("No dest");
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
    return false;
  case OPCODE_CONST:
    return insn->get_literal() == 0;
  case OPCODE_FILL_ARRAY_DATA:
  case OPCODE_SWITCH:
    not_reached_log("No dest");
  case OPCODE_CONST_WIDE:
  case OPCODE_IGET:
  case OPCODE_IGET_WIDE:
    return false;
  case OPCODE_IGET_OBJECT:
    return true;
  case OPCODE_IGET_BOOLEAN:
  case OPCODE_IGET_BYTE:
  case OPCODE_IGET_CHAR:
  case OPCODE_IGET_SHORT:
    return false;
  case OPCODE_IPUT:
  case OPCODE_IPUT_WIDE:
  case OPCODE_IPUT_OBJECT:
  case OPCODE_IPUT_BOOLEAN:
  case OPCODE_IPUT_BYTE:
  case OPCODE_IPUT_CHAR:
  case OPCODE_IPUT_SHORT:
    not_reached_log("No dest");
  case OPCODE_SGET:
  case OPCODE_SGET_WIDE:
    return false;
  case OPCODE_SGET_OBJECT:
    return true;
  case OPCODE_SGET_BOOLEAN:
  case OPCODE_SGET_BYTE:
  case OPCODE_SGET_CHAR:
  case OPCODE_SGET_SHORT:
    return false;
  case OPCODE_SPUT:
  case OPCODE_SPUT_WIDE:
  case OPCODE_SPUT_OBJECT:
  case OPCODE_SPUT_BOOLEAN:
  case OPCODE_SPUT_BYTE:
  case OPCODE_SPUT_CHAR:
  case OPCODE_SPUT_SHORT:
    not_reached_log("No dest");
  case OPCODE_INVOKE_VIRTUAL:
  case OPCODE_INVOKE_SUPER:
  case OPCODE_INVOKE_DIRECT:
  case OPCODE_INVOKE_STATIC:
  case OPCODE_INVOKE_INTERFACE:
    return !type::is_primitive(insn->get_method()->get_proto()->get_rtype());
  case OPCODE_CONST_STRING:
  case OPCODE_CONST_CLASS:
  case OPCODE_CHECK_CAST:
    return true;
  case OPCODE_INSTANCE_OF:
    return false;
  case OPCODE_NEW_INSTANCE:
  case OPCODE_NEW_ARRAY:
  case OPCODE_FILLED_NEW_ARRAY:
    return true;
  case IOPCODE_LOAD_PARAM:
  case IOPCODE_LOAD_PARAM_WIDE:
  case IOPCODE_MOVE_RESULT_PSEUDO:
  case IOPCODE_MOVE_RESULT_PSEUDO_WIDE:
    return false;
  case IOPCODE_LOAD_PARAM_OBJECT:
  case IOPCODE_MOVE_RESULT_PSEUDO_OBJECT:
    return true;
  case IOPCODE_R_CONST:
  case IOPCODE_INJECTION_ID:
  case IOPCODE_UNREACHABLE:
    return false;
  default:
    not_reached_log("Unknown opcode %02x\n", op);
  }
}

void analyze_invoke_with_summary(const EscapeSummary& summary,
                                 const IRInstruction* insn,
                                 Environment* env) {
  for (auto src_idx : UnorderedIterable(summary.escaping_parameters)) {
    env->set_may_escape(insn->src(src_idx), insn);
  }

  if (!dest_may_be_pointer(insn)) {
    env->set_pointers(RESULT_REGISTER, PointerSet::top());
  }

  PointerSet returned_ptrs;
  for (auto src_idx : UnorderedIterable(summary.returned_parameters)) {
    if (src_idx == FRESH_RETURN) {
      returned_ptrs.add(insn);
    } else if (src_idx == ESCAPED_FRESH_RETURN) {
      returned_ptrs.add(insn);
      // escape just insn right here; we are going to override
      // RESULT_REGISTER in a moment with a more precise pointer set.
      escape_dest(insn, RESULT_REGISTER, env);
    } else {
      returned_ptrs.join_with(env->get_pointers(insn->src(src_idx)));
    }
  }
  // Note that returned_ptrs is empty initially
  env->set_pointers(RESULT_REGISTER, returned_ptrs);
}

/*
 * Analyze an invoke instruction in the absence of an available summary.
 */
void analyze_generic_invoke(const IRInstruction* insn,
                            EnvironmentWithStore* env) {
  escape_invoke_params(insn, env);
  escape_dest(insn, RESULT_REGISTER, env);
}

} // namespace

namespace local_pointers {

void escape_heap_referenced_objects(const IRInstruction* insn,
                                    EnvironmentWithStore* env) {
  auto op = insn->opcode();
  // Since we don't model instance fields / array elements, any pointers
  // written to them must be treated as escaping.
  if (op == OPCODE_APUT_OBJECT || op == OPCODE_SPUT_OBJECT ||
      op == OPCODE_IPUT_OBJECT) {
    env->set_may_escape(insn->src(0), insn);
  } else if (op == OPCODE_FILLED_NEW_ARRAY &&
             !type::is_primitive(
                 type::make_array_component_type(insn->get_type()))) {
    for (size_t i = 0; i < insn->srcs_size(); ++i) {
      env->set_may_escape(insn->src(i), insn);
    }
  }
}

void escape_dest(const IRInstruction* insn,
                 reg_t dest,
                 EnvironmentWithStore* env) {
  // While the analysis would still work if we treated all non-pointer-values
  // as escaping pointers, it would bloat the size of our abstract domain and
  // incur a runtime performance tax.
  if (dest_may_be_pointer(insn)) {
    env->set_may_escape_pointer(dest, insn, insn);
  } else {
    env->set_pointers(dest, PointerSet::top());
  }
}

void escape_invoke_params(const IRInstruction* insn,
                          EnvironmentWithStore* env) {
  size_t idx{0};
  if (insn->opcode() != OPCODE_INVOKE_STATIC) {
    env->set_may_escape(insn->src(0), insn);
    ++idx;
  }
  const auto* arg_types = insn->get_method()->get_proto()->get_args();
  for (const auto* arg : *arg_types) {
    if (!type::is_primitive(arg)) {
      env->set_may_escape(insn->src(idx), insn);
    }
    ++idx;
  }
}

void default_instruction_handler(const IRInstruction* insn,
                                 EnvironmentWithStore* env) {
  auto op = insn->opcode();
  if (opcode::is_an_invoke(op)) {
    analyze_generic_invoke(insn, env);
  } else if (opcode::is_a_move(op)) {
    env->set_pointers(insn->dest(), env->get_pointers(insn->src(0)));
  } else if (op == OPCODE_CHECK_CAST) {
    env->set_pointers(RESULT_REGISTER, env->get_pointers(insn->src(0)));
  } else if (opcode::is_move_result_any(op)) {
    env->set_pointers(insn->dest(), env->get_pointers(RESULT_REGISTER));
  } else if (insn->has_dest()) {
    escape_dest(insn, insn->dest(), env);
  } else if (insn->has_move_result_any()) {
    escape_dest(insn, RESULT_REGISTER, env);
  }
}

void FixpointIterator::analyze_instruction(const IRInstruction* insn,
                                           Environment* env) const {
  escape_heap_referenced_objects(insn, env);

  auto op = insn->opcode();
  if (opcode::is_an_invoke(op)) {
    auto* method = insn->get_method();
    // If the method is an init and the class is excluded, we label is as
    // escaping to prevent further optimizations.
    if (method::is_init(method) && (m_excluded_classes != nullptr) &&
        (m_excluded_classes->count(type_class(method->get_class())) != 0u)) {
      env->set_may_escape(insn->src(0), insn);
    } else if (m_invoke_to_summary_map.count(insn) != 0u) {
      const auto& summary = m_invoke_to_summary_map.at(insn);
      analyze_invoke_with_summary(summary, insn, env);
    } else {
      analyze_generic_invoke(insn, env);
    }
  } else if (may_alloc(op)) {
    env->set_fresh_pointer(RESULT_REGISTER, insn);
  } else if (op == IOPCODE_LOAD_PARAM_OBJECT) {
    env->set_fresh_pointer(insn->dest(), insn);
  } else {
    default_instruction_handler(insn, env);
    if (m_escape_check_cast && op == OPCODE_CHECK_CAST) {
      env->set_may_escape(insn->src(0), insn);
    }
  }
}

std::pair<std::unique_ptr<FixpointIterator>, EscapeSummary> analyze_method(
    const DexMethod* method,
    const call_graph::Graph& call_graph,
    const SummaryMap& summary_map,
    const UnorderedSet<DexClass*>* excluded_classes) {
  UnorderedMap<const IRInstruction*, EscapeSummary> invoke_to_summary_map;
  if (call_graph.has_node(method)) {
    const auto& callee_edges = call_graph.node(method)->callees();
    for (const auto& edge : callee_edges) {
      if (edge->callee() == call_graph.exit()) {
        continue;
      }
      auto* invoke_insn = edge->invoke_insn();
      auto& callee_summary = invoke_to_summary_map[invoke_insn];
      const auto* callee = edge->callee()->method();
      auto it = summary_map.find(callee);
      if (it != summary_map.end()) {
        callee_summary.join_with(it->second);
      } else if (callee == nullptr &&
                 is_array_clone(invoke_insn->get_method())) {
        // The array clone method doesn't escape or return any parameters; it
        // returns a new array.
        callee_summary.join_with(EscapeSummary(ParamSet{FRESH_RETURN}, {}));
      }
    }
  }

  const auto* code = method->get_code();
  const auto& cfg = code->cfg();
  auto fp_iter =
      std::make_unique<FixpointIterator>(cfg,
                                         std::move(invoke_to_summary_map),
                                         /* escape_check_cast */ false,
                                         excluded_classes);
  fp_iter->run(Environment());

  bool result_may_be_pointer =
      !type::is_primitive(method->get_proto()->get_rtype());
  auto summary = get_escape_summary(*fp_iter, *code, result_may_be_pointer);
  return std::make_pair(std::move(fp_iter), std::move(summary));
}

AnalyzeScopeResult analyze_scope(
    const Scope& scope,
    const call_graph::Graph& call_graph,
    SummaryMap* summary_map_ptr,
    const UnorderedSet<DexClass*>* excluded_classes) {
  FixpointIteratorMap fp_iter_map;
  SummaryMap summary_map;
  if (summary_map_ptr == nullptr) {
    summary_map_ptr = &summary_map;
  }
  summary_map_ptr->emplace(method::java_lang_Object_ctor(), EscapeSummary{});

  auto affected_methods = std::make_unique<ConcurrentSet<const DexMethod*>>();
  walk::parallel::code(scope, [&](const DexMethod* method, IRCode&) {
    affected_methods->insert(method);
  });

  size_t iterations = 0;
  while (!affected_methods->empty()) {
    ++iterations;
    InsertOnlyConcurrentMap<const DexMethod*, EscapeSummary>
        changed_effect_summaries;
    auto next_affected_methods =
        std::make_unique<ConcurrentSet<const DexMethod*>>();
    workqueue_run<const DexMethod*>(
        [&](const DexMethod* method) {
          auto p = analyze_method(method, call_graph, *summary_map_ptr,
                                  excluded_classes);
          auto& new_fp_iter = p.first;
          auto& new_summary = p.second;
          fp_iter_map.update(method, [&](auto*, auto& v, bool exists) {
            redex_assert(!(exists ^ (v != nullptr)));
            std::swap(new_fp_iter, v);
          });
          auto it = summary_map_ptr->find(method);
          if (it != summary_map_ptr->end()) {
            always_assert_log(it->second <= new_summary,
                              "Illegal summary transition for %s:\n  %s\nis "
                              "not less or equal to\n  %s\n",
                              SHOW(method), SHOW(it->second),
                              SHOW(new_summary));
            if (it->second == new_summary) {
              return;
            }
          }
          changed_effect_summaries.emplace(method, std::move(new_summary));
          const auto& callers = call_graph.get_callers(method);
          insert_unordered_iterable(*next_affected_methods, callers);
        },
        *affected_methods);
    for (auto&& [method, summary] :
         UnorderedIterable(changed_effect_summaries)) {
      (*summary_map_ptr)[method] = std::move(summary);
    }
    std::swap(next_affected_methods, affected_methods);
  }

  return AnalyzeScopeResult{std::move(fp_iter_map), iterations};
}

void collect_exiting_pointers(const FixpointIterator& fp_iter,
                              const IRCode& code,
                              PointerSet* returned_ptrs,
                              PointerSet* thrown_ptrs) {
  const auto& cfg = code.cfg();
  PointerSet rv = PointerSet::bottom();
  returned_ptrs->set_to_bottom();
  thrown_ptrs->set_to_bottom();
  for (auto* block : cfg.blocks()) {
    auto last_insn_it = block->get_last_insn();
    if (last_insn_it == block->end()) {
      continue;
    }
    auto* insn = last_insn_it->insn;
    const auto& state =
        fp_iter.get_exit_state_at(const_cast<cfg::Block*>(block));
    if (opcode::is_return_object(insn->opcode())) {
      returned_ptrs->join_with(state.get_pointers(insn->src(0)));
    } else if (insn->opcode() == OPCODE_THROW) {
      thrown_ptrs->join_with(state.get_pointers(insn->src(0)));
    }
  }
}

EscapeSummary get_escape_summary(const FixpointIterator& fp_iter,
                                 const IRCode& code,
                                 bool result_may_be_pointer) {
  EscapeSummary summary;

  PointerSet returned_ptrs;
  PointerSet thrown_ptrs;
  collect_exiting_pointers(fp_iter, code, &returned_ptrs, &thrown_ptrs);

  const auto& cfg = code.cfg();
  // FIXME: fix cfg's GraphInterface so this const_cast isn't necessary
  const auto& exit_state =
      fp_iter.get_exit_state_at(const_cast<cfg::Block*>(cfg.exit_block()));
  uint16_t idx{0};
  UnorderedMap<const IRInstruction*, uint16_t> param_indexes;
  boost::sub_range<IRList> param_instruction = cfg.get_param_instructions();
  for (auto& mie : InstructionIterable(param_instruction)) {
    auto* insn = mie.insn;
    if (insn->opcode() == IOPCODE_LOAD_PARAM_OBJECT) {
      param_indexes.emplace(insn, idx);

      // Unlike returned pointers, we don't model thrown pointers specially in
      // our EscapeSummary; they are treated as escaping pointers.
      if (exit_state.may_have_escaped(insn) || thrown_ptrs.contains(insn)) {
        summary.escaping_parameters.emplace(idx);
      }
    }
    ++idx;
  }

  switch (returned_ptrs.kind()) {
  case sparta::AbstractValueKind::Value: {
    always_assert(result_may_be_pointer);
    summary.returned_parameters = ParamSet();
    for (const auto* insn : returned_ptrs.elements()) {
      if (insn->opcode() == IOPCODE_LOAD_PARAM_OBJECT) {
        summary.returned_parameters.insert(param_indexes.at(insn));
      } else if (!exit_state.may_have_escaped(insn)) {
        summary.returned_parameters.insert(FRESH_RETURN);
      } else {
        // We are returning a possibly escaped pointer that did not originate
        // from an input parameter.
        summary.returned_parameters.insert(ESCAPED_FRESH_RETURN);
      }
    }
    break;
  }
  case sparta::AbstractValueKind::Top: {
    always_assert(!result_may_be_pointer);
    break;
  }
  case sparta::AbstractValueKind::Bottom: {
    always_assert_log(!result_may_be_pointer || cfg.return_blocks().empty(),
                      "Does the cfg contain unreachable blocks?\n%s",
                      SHOW(cfg));
    break;
  }
  }
  return summary;
}

std::ostream& operator<<(std::ostream& o, const EscapeSummary& summary) {
  o << "Escaping parameters: ";
  bool first{true};
  for (auto p_idx : UnorderedIterable(summary.escaping_parameters)) {
    if (!first) {
      o << ", ";
    }
    o << p_idx;
    first = false;
  }
  first = true;
  for (auto p_idx : UnorderedIterable(summary.returned_parameters)) {
    if (!first) {
      o << ", ";
    }
    o << p_idx;
    first = false;
  }
  return o;
}

sparta::s_expr to_s_expr(const EscapeSummary& summary) {
  std::vector<sparta::s_expr> escaping_params_s_exprs;
  auto escaping_parameters = unordered_to_ordered(summary.escaping_parameters);
  escaping_params_s_exprs.reserve(escaping_parameters.size());
  for (auto idx : escaping_parameters) {
    escaping_params_s_exprs.emplace_back(idx);
  }
  std::vector<sparta::s_expr> returned_params_s_exprs;
  auto returned_parameters = unordered_to_ordered(summary.returned_parameters);
  returned_params_s_exprs.reserve(returned_parameters.size());
  for (auto idx : returned_parameters) {
    returned_params_s_exprs.emplace_back(idx);
  }
  return sparta::s_expr{sparta::s_expr(escaping_params_s_exprs),
                        sparta::s_expr(returned_params_s_exprs)};
}

EscapeSummary EscapeSummary::from_s_expr(const sparta::s_expr& expr) {
  EscapeSummary summary;
  always_assert(expr.is_list() && expr.size() == 2);
  auto escaping_params_s_expr = expr[0];
  always_assert(escaping_params_s_expr.is_list());
  for (size_t i = 0; i < escaping_params_s_expr.size(); ++i) {
    summary.escaping_parameters.emplace(escaping_params_s_expr[i].get_int32());
  }
  auto returned_params_s_expr = expr[1];
  always_assert(returned_params_s_expr.is_list());
  for (size_t i = 0; i < returned_params_s_expr.size(); ++i) {
    summary.returned_parameters.emplace(returned_params_s_expr[i].get_int32());
  }
  return summary;
}

bool EscapeSummary::operator<=(const EscapeSummary& other) const {
  return unordered_all_of(
             escaping_parameters,
             [&](auto idx) { return other.escaping_parameters.count(idx); }) &&
         unordered_all_of(returned_parameters, [&](size_t idx) -> bool {
           if (idx == FRESH_RETURN &&
               (other.returned_parameters.count(ESCAPED_FRESH_RETURN) != 0u)) {
             // As more escaping parameters are discovered, previously apparent
             // unescaped fresh returns can become unrepresentable.
             return true;
           }
           return other.returned_parameters.count(idx) != 0u;
         });
}

void EscapeSummary::join_with(const EscapeSummary& other) {
  insert_unordered_iterable(escaping_parameters, other.escaping_parameters);
  insert_unordered_iterable(returned_parameters, other.returned_parameters);
}

bool may_be_overridden(const DexMethod* method) {
  return method->is_virtual() && !is_final(method) &&
         !is_final(type_class(method->get_class()));
}

bool is_array_clone(const DexMethodRef* mref) {
  return type::is_array(mref->get_class()) &&
         mref->get_name()->str() == "clone";
}

} // namespace local_pointers
