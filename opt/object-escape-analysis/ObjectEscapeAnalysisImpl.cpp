/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ObjectEscapeAnalysisImpl.h"
#include "Debug.h"
#include "Trace.h"

#include "TypeUtil.h"
#include "Walkers.h"

using namespace sparta;
namespace mog = method_override_graph;

namespace {
constexpr const IRInstruction* NO_ALLOCATION = nullptr;
const IRInstruction* ZERO = new IRInstruction(OPCODE_CONST);
} // namespace

namespace object_escape_analysis_impl {

bool Callees::operator==(const Callees& other) const {
  // with_code holds distinct methods in a non-deterministic order, so compare
  // it as a set.
  return any_unknown == other.any_unknown &&
         unordered_equal(with_code, other.with_code);
}

DexMethod* resolve_invoke_method_if_unambiguous(
    const method_override_graph::Graph& method_override_graph,
    const IRInstruction* insn,
    const DexMethod* caller) {
  auto* callee = resolve_invoke_method_deprecated(insn, caller);
  if ((callee == nullptr) || callee->is_external() ||
      (callee->get_code() == nullptr)) {
    return nullptr;
  }
  if (!callee->is_virtual() || insn->opcode() == OPCODE_INVOKE_SUPER ||
      is_final(callee) || is_final(type_class(callee->get_class())) ||
      !method_override_graph::any_overriding_methods(
          method_override_graph, callee, [](auto*) { return true; },
          /* include_interfaces*/ false, insn->get_method()->get_class())) {
    return callee;
  }
  return nullptr;
}

std::pair<const Callees*, bool> get_or_create_callees(
    const method_override_graph::Graph& method_override_graph,
    IROpcode op,
    DexMethod* resolved_callee,
    const DexType* static_base_type,
    CalleesCache* callees_cache) {
  auto no_overrides = opcode::is_invoke_static(op) ||
                      opcode::is_invoke_direct(op) ||
                      opcode::is_invoke_super(op);
  return (*callees_cache)[no_overrides].get_or_create_and_assert_equal(
      {resolved_callee, static_base_type}, [&](auto) {
        Callees res;
        if (!resolved_callee) {
          res.any_unknown = true;
        } else {
          auto visit_callee = [&](const auto* m) {
            if (m->get_code()) {
              res.with_code.push_back(const_cast<DexMethod*>(m));
            } else if (m->is_external() || is_native(m)) {
              res.any_unknown = true;
            } else {
              always_assert(is_abstract(m));
            }
            return true;
          };
          visit_callee(resolved_callee);
          if (!no_overrides && resolved_callee->is_virtual()) {
            always_assert(opcode::is_invoke_virtual(op) ||
                          opcode::is_invoke_interface(op));
            if (is_interface(type_class(resolved_callee->get_class())) &&
                (root(resolved_callee) || !can_rename(resolved_callee))) {
              res.any_unknown = true;
            }
            auto overriding_methods = mog::get_overriding_methods(
                method_override_graph, resolved_callee,
                /* include_interfaces */ false, static_base_type);
            for (const auto* overriding_method :
                 UnorderedIterable(overriding_methods)) {
              visit_callee(overriding_method);
            }
          }
        }
        return res;
      });
}

const Callees* resolve_invoke_callees(
    const method_override_graph::Graph& method_override_graph,
    const IRInstruction* insn,
    const DexMethod* caller,
    CalleesCache* callees_cache) {
  auto* callee = resolve_invoke_method_deprecated(insn, caller);
  auto [callees, _] =
      get_or_create_callees(method_override_graph, insn->opcode(), callee,
                            insn->get_method()->get_class(), callees_cache);
  return callees;
}

DexMethod* resolve_invoke_inlinable_callee(
    const method_override_graph::Graph& method_override_graph,
    const IRInstruction* insn,
    const DexMethod* caller,
    CalleesCache* callees_cache,
    const std::function<const DexType*()>&
        inlinable_type_at_src_index_0_getter) {
  const auto* callees = resolve_invoke_callees(method_override_graph, insn,
                                               caller, callees_cache);
  always_assert(!callees->any_unknown);
  if (callees->with_code.size() == 1) {
    return callees->with_code.front();
  }
  const auto* inlinable_type = inlinable_type_at_src_index_0_getter();
  if (inlinable_type == nullptr) {
    return nullptr;
  }

  auto* method_ref = insn->get_method();
  always_assert_log(
      type::check_cast(inlinable_type, method_ref->get_class()),
      "Inlinable type %s is compatible with declaring type of method in {%s}",
      SHOW(inlinable_type), SHOW(insn));
  auto* callee = resolve_method_deprecated(
      type_class(inlinable_type), method_ref->get_name(),
      method_ref->get_proto(), MethodSearch::Virtual, caller);
  always_assert_log(callee, "Could not resolve callee for %s in %s", SHOW(insn),
                    SHOW(inlinable_type));
  always_assert_log(callee->get_code(), "Callee %s for %s in %s has no code",
                    SHOW(callee), SHOW(insn), SHOW(inlinable_type));
  always_assert_log(
      std::find(callees->with_code.begin(), callees->with_code.end(), callee) !=
          callees->with_code.end(),
      "Callee %s for %s in %s is not in list", SHOW(callee), SHOW(insn),
      SHOW(inlinable_type));
  return callee;
}

src_index_t get_param_index(const DexMethod* callee,
                            const IRInstruction* load_param_insn) {
  src_index_t idx = 0;
  const auto& cfg = callee->get_code()->cfg();
  for (const auto& mie : InstructionIterable(cfg.get_param_instructions())) {
    if (mie.insn == load_param_insn) {
      return idx;
    }
    idx++;
  }
  not_reached();
}

// Collect all allocation and invoke instructions, as well as non-virtual
// invocation dependencies.
void analyze_scope(
    const Scope& scope,
    const mog::Graph& method_override_graph,
    ConcurrentMap<const DexType*, Locations>* new_instances,
    ConcurrentMap<DexMethod*, Locations>* single_callee_invokes,
    InsertOnlyConcurrentSet<DexMethod*>* multi_callee_invokes,
    ConcurrentMap<DexMethod*, UnorderedSet<DexMethod*>>* dependencies,
    CalleesCache* callees_cache) {
  Timer t("analyze_scope");
  walk::parallel::code(scope, [&](DexMethod* method, IRCode& code) {
    always_assert(code.cfg_built());
    using Map = UnorderedMap<CalleesKey, const Callees*, CalleesKeyHash>;
    std::array<Map, 2> local_callees_cache;
    auto resolve_invoke_callees = [&](auto* insn) {
      auto* resolved_callee = resolve_invoke_method_deprecated(insn, method);
      auto* static_base_type = insn->get_method()->get_class();
      auto op = insn->opcode();
      bool no_overrides = opcode::is_invoke_static(op) ||
                          opcode::is_invoke_direct(op) ||
                          opcode::is_invoke_super(op);
      auto key = std::make_pair(resolved_callee, static_base_type);
      auto it = local_callees_cache[no_overrides].find(key);
      if (it != local_callees_cache[no_overrides].end()) {
        return it->second;
      }
      auto [callees, created] =
          get_or_create_callees(method_override_graph, op, resolved_callee,
                                static_base_type, callees_cache);
      local_callees_cache[no_overrides].emplace(key, callees);
      if (created && (callees->any_unknown || callees->with_code.size() != 1)) {
        for (auto* callee : callees->with_code) {
          multi_callee_invokes->insert(callee);
        }
      }
      if (!callees->any_unknown) {
        for (auto* callee : callees->with_code) {
          dependencies->update(
              callee, [method](auto, auto& set, auto) { set.insert(method); });
        }
      }
      return callees;
    };
    for (auto& mie : InstructionIterable(code.cfg())) {
      auto* insn = mie.insn;
      if (insn->opcode() == OPCODE_NEW_INSTANCE) {
        auto* cls = type_class(insn->get_type());
        if ((cls != nullptr) && !cls->is_external()) {
          new_instances->update(insn->get_type(), [&](auto*, auto& vec, bool) {
            vec.emplace_back(method, insn);
          });
        }
      } else if (opcode::is_a_method_invoke(insn->opcode())) {
        const auto* callees = resolve_invoke_callees(insn);
        if (!callees->any_unknown && callees->with_code.size() == 1) {
          single_callee_invokes->update(
              callees->with_code.front(),
              [&](auto*, auto& vec, bool) { vec.emplace_back(method, insn); });
        }
      }
    }
  });
}

// A benign method invocation can be ignored during the escape analysis.
bool is_benign(const DexMethodRef* method_ref) {
  static const UnorderedSet<std::string_view> methods = {
      // clang-format off
      "Ljava/lang/Object;.<init>:()V",
      // clang-format on
  };

  // Deliberately the non-copying accessor: this runs for every invoke on every
  // fixpoint iteration, and _copy allocates a std::string each time.
  return method_ref->is_def() &&
         (methods.count(
              method_ref->as_def()->get_deobfuscated_name_or_empty()) != 0u);
}

const MethodSummary* get_or_create_method_summary(
    const MethodSummaries& method_summaries,
    const Callees* callees,
    MethodSummaryCache* method_summary_cache) {
  return method_summary_cache
      ->get_or_create_and_assert_equal(
          callees,
          [&](auto*) {
            if (callees->any_unknown || callees->with_code.empty()) {
              return MethodSummary();
            }
            auto it = method_summaries.find(callees->with_code.front());
            if (it == method_summaries.end()) {
              return MethodSummary();
            }
            auto res = it->second;
            for (size_t i = 1; i < callees->with_code.size() && !res.empty();
                 i++) {
              it = method_summaries.find(callees->with_code[i]);
              if (it == method_summaries.end()) {
                return MethodSummary();
              }
              unordered_erase_if(res.benign_params, [&](auto idx) {
                return !it->second.benign_params.count(idx);
              });
              if (res.returns != it->second.returns) {
                if (auto opt_idx = res.returned_param_index()) {
                  res.benign_params.erase(*opt_idx);
                }
                if (auto opt_idx = it->second.returned_param_index()) {
                  res.benign_params.erase(*opt_idx);
                }
                res.returns = std::monostate();
              }
            }
            if (callees->with_code.size() > 1) {
              unordered_erase_if(res.benign_params,
                                 [](auto idx) { return idx > 0; });
              if (res.returned_param_index() &&
                  !res.benign_params.count(*res.returned_param_index())) {
                res.returns = std::monostate();
              }
            }
            return res;
          })
      .first;
}

const MethodSummary* resolve_invoke_method_summary(
    const method_override_graph::Graph& method_override_graph,
    const MethodSummaries& method_summaries,
    const IRInstruction* insn,
    const DexMethod* caller,
    CalleesCache* callees_cache,
    MethodSummaryCache* method_summary_cache) {
  auto* callee = resolve_invoke_method_deprecated(insn, caller);
  auto [callees, _] =
      get_or_create_callees(method_override_graph, insn->opcode(), callee,
                            insn->get_method()->get_class(), callees_cache);
  return get_or_create_method_summary(method_summaries, callees,
                                      method_summary_cache);
}

Analyzer::Analyzer(const mog::Graph& method_override_graph,
                   const UnorderedSet<DexClass*>& excluded_classes,
                   const MethodSummaries& method_summaries,
                   DexMethodRef* incomplete_marker_method,
                   DexMethod* method,
                   CalleesCache* callees_cache,
                   MethodSummaryCache* method_summary_cache)
    : BaseIRAnalyzer(method->get_code()->cfg()),
      m_method_override_graph(method_override_graph),
      m_excluded_classes(excluded_classes),
      m_method_summaries(method_summaries),
      m_incomplete_marker_method(incomplete_marker_method),
      m_method(method),
      m_callees_cache(callees_cache),
      m_method_summary_cache(method_summary_cache) {
  MonotonicFixpointIterator::run(Environment::top());
}

template <class UnorderedCollection>
const IRInstruction* get_singleton_allocation_unordered_iterable(
    const UnorderedCollection& uc) {
  if (uc.empty()) {
    return nullptr;
  }
  auto ui = UnorderedIterable(uc);
  auto it = ui.begin();
  const IRInstruction* a = *it++;
  if (it == ui.end()) {
    return (a == NO_ALLOCATION || a == ZERO) ? nullptr : a;
  }
  const IRInstruction* b = *it++;
  if (it != ui.end() || a == NO_ALLOCATION || b == NO_ALLOCATION ||
      (a != ZERO && b != ZERO)) {
    return nullptr;
  }
  return a == ZERO ? b : a;
}

const IRInstruction* get_singleton_allocation(const Domain& domain) {
  always_assert(domain.kind() == AbstractValueKind::Value);
  const auto& elements = domain.elements();
  return get_singleton_allocation_unordered_iterable(elements);
}

void Analyzer::analyze_instruction(const IRInstruction* insn,
                                   Environment* current_state) const {

  const auto escape = [&](src_index_t src_idx) {
    auto reg = insn->src(src_idx);
    const auto& domain = current_state->get(reg);
    always_assert(domain.kind() == AbstractValueKind::Value);
    for (const auto* allocation_insn : domain.elements()) {
      if (allocation_insn != NO_ALLOCATION && allocation_insn != ZERO) {
        m_escapes[allocation_insn].insert(
            {const_cast<IRInstruction*>(insn), src_idx});
      }
    }
  };

  if (insn->opcode() == OPCODE_NEW_INSTANCE) {
    const auto* type = insn->get_type();
    auto* cls = type_class(type);
    if ((cls != nullptr) && !cls->is_external() &&
        (m_excluded_classes.count(cls) == 0u)) {
      m_escapes[insn];
      current_state->set(RESULT_REGISTER, Domain(insn));
      return;
    }
  } else if (insn->opcode() == IOPCODE_LOAD_PARAM_OBJECT) {
    m_escapes[insn];
    current_state->set(insn->dest(), Domain(insn));
    return;
  } else if (insn->opcode() == OPCODE_CONST && insn->get_literal() == 0) {
    current_state->set(insn->dest(), Domain(ZERO));
    return;
  } else if (insn->opcode() == OPCODE_RETURN_OBJECT) {
    const auto& domain = current_state->get(insn->src(0));
    always_assert(domain.kind() == AbstractValueKind::Value);
    m_returns.insert(domain.elements().begin(), domain.elements().end());
    return;
  } else if (insn->opcode() == OPCODE_MOVE_RESULT_OBJECT ||
             insn->opcode() == IOPCODE_MOVE_RESULT_PSEUDO_OBJECT) {
    const auto& domain = current_state->get(RESULT_REGISTER);
    current_state->set(insn->dest(), domain);
    return;
  } else if (insn->opcode() == OPCODE_MOVE_OBJECT) {
    const auto& domain = current_state->get(insn->src(0));
    current_state->set(insn->dest(), domain);
    return;
  } else if (insn->opcode() == OPCODE_CHECK_CAST) {
    const auto& domain = current_state->get(insn->src(0));
    current_state->set(RESULT_REGISTER, domain);
    return;
  } else if (insn->opcode() == OPCODE_INSTANCE_OF ||
             opcode::is_an_iget(insn->opcode())) {
    if (get_singleton_allocation(current_state->get(insn->src(0))) != nullptr) {
      current_state->set(RESULT_REGISTER, Domain(NO_ALLOCATION));
      return;
    }
  } else if (opcode::is_a_monitor(insn->opcode()) ||
             insn->opcode() == OPCODE_IF_EQZ ||
             insn->opcode() == OPCODE_IF_NEZ) {
    if (get_singleton_allocation(current_state->get(insn->src(0))) != nullptr) {
      return;
    }
  } else if (opcode::is_an_iput(insn->opcode())) {
    if (get_singleton_allocation(current_state->get(insn->src(1))) != nullptr) {
      escape(0);
      return;
    }
  } else if (opcode::is_a_method_invoke(insn->opcode())) {
    if (is_benign(insn->get_method()) || is_incomplete_marker(insn)) {
      current_state->set(RESULT_REGISTER, Domain(NO_ALLOCATION));
      return;
    }
    const auto* ms = resolve_invoke_method_summary(
        m_method_override_graph, m_method_summaries, insn, m_method,
        m_callees_cache, m_method_summary_cache);
    for (src_index_t i = 0; i < insn->srcs_size(); i++) {
      if ((ms->benign_params.count(i) == 0u) ||
          (get_singleton_allocation(current_state->get(insn->src(i))) ==
           nullptr)) {
        escape(i);
      }
    }

    Domain domain(NO_ALLOCATION);
    if (ms->allocation_insn() != nullptr) {
      m_escapes[insn];
      domain = Domain(insn);
    } else if (auto src_index = ms->returned_param_index()) {
      domain = current_state->get(insn->src(*src_index));
    }
    current_state->set(RESULT_REGISTER, domain);
    return;
  }

  for (src_index_t i = 0; i < insn->srcs_size(); i++) {
    escape(i);
  }

  if (insn->has_dest()) {
    current_state->set(insn->dest(), Domain(NO_ALLOCATION));
    if (insn->dest_is_wide()) {
      current_state->set(insn->dest() + 1, Domain::top());
    }
  } else if (insn->has_move_result_any()) {
    current_state->set(RESULT_REGISTER, Domain(NO_ALLOCATION));
  }
}

// Returns set of new-instance and invoke- allocating instructions that do not
// escape (or return).
UnorderedSet<IRInstruction*> Analyzer::get_inlinables() const {
  UnorderedSet<IRInstruction*> inlinables;
  for (auto&& [insn, uses] : UnorderedIterable(m_escapes)) {
    if (uses.empty() && insn->opcode() != IOPCODE_LOAD_PARAM_OBJECT &&
        (m_returns.count(insn) == 0u)) {
      auto op = insn->opcode();
      always_assert(op == OPCODE_NEW_INSTANCE ||
                    opcode::is_a_method_invoke(op));
      if (op == OPCODE_NEW_INSTANCE ||
          (resolve_invoke_method_if_unambiguous(m_method_override_graph, insn,
                                                m_method) != nullptr)) {
        inlinables.insert(const_cast<IRInstruction*>(insn));
      }
    }
  }
  return inlinables;
}

MethodSummaries compute_method_summaries(
    const Scope&,
    const ConcurrentMap<DexMethod*, UnorderedSet<DexMethod*>>& dependencies,
    const mog::Graph& method_override_graph,
    const UnorderedSet<DexClass*>& excluded_classes,
    size_t* analysis_iterations,
    CalleesCache* callees_cache,
    MethodSummaryCache* method_summary_cache) {
  Timer t("compute_method_summaries");

  UnorderedSet<DexMethod*> impacted_methods;
  for (auto&& [method, _] : UnorderedIterable(dependencies)) {
    impacted_methods.insert(method);
  }

  MethodSummaries method_summaries;
  *analysis_iterations = 0;
  while (!impacted_methods.empty()) {
    Timer t2("analysis iteration");
    (*analysis_iterations)++;
    TRACE(OEA, 2, "[object escape analysis] analysis_iteration %zu",
          *analysis_iterations);
    InsertOnlyConcurrentMap<DexMethod*, MethodSummary>
        recomputed_method_summaries;
    *method_summary_cache = MethodSummaryCache();
    workqueue_run<DexMethod*>(
        [&](DexMethod* method) {
          MethodSummary ms;
          Analyzer analyzer(method_override_graph, excluded_classes,
                            method_summaries,
                            /* incomplete_marker_method */ nullptr, method,
                            callees_cache, method_summary_cache);
          const auto& escapes = analyzer.get_escapes();
          const auto& returns = analyzer.get_returns();
          const auto* returned_insn =
              get_singleton_allocation_unordered_iterable(returns);
          if ((returned_insn != nullptr) && escapes.at(returned_insn).empty()) {
            if (returned_insn->opcode() == IOPCODE_LOAD_PARAM_OBJECT) {
              ms.returns = get_param_index(method, returned_insn);
            } else {
              auto op = returned_insn->opcode();
              always_assert(op == OPCODE_NEW_INSTANCE ||
                            opcode::is_a_method_invoke(op));
              if (op == OPCODE_NEW_INSTANCE ||
                  (resolve_invoke_method_if_unambiguous(method_override_graph,
                                                        returned_insn,
                                                        method) != nullptr)) {
                ms.returns = returned_insn;
              }
            }
          }
          auto& cfg = method->get_code()->cfg();
          src_index_t src_index = 0;
          for (const auto& mie :
               InstructionIterable(cfg.get_param_instructions())) {
            if (mie.insn->opcode() == IOPCODE_LOAD_PARAM_OBJECT &&
                escapes.at(mie.insn).empty() &&
                ((returns.count(mie.insn) == 0u) ||
                 ms.returned_param_index() == src_index)) {
              ms.benign_params.insert(src_index);
            }
            src_index++;
          }
          if (!ms.empty()) {
            recomputed_method_summaries.emplace(method, std::move(ms));
          }
        },
        impacted_methods);

    UnorderedSet<DexMethod*> changed_methods;
    // (Recomputed) summaries can only grow; assert that, update summaries when
    // necessary, and remember for which methods the summaries actually changed.
    for (auto&& [method, recomputed_summary] :
         UnorderedIterable(recomputed_method_summaries)) {
      auto& summary = method_summaries[method];
      for (auto src_index : UnorderedIterable(summary.benign_params)) {
        always_assert(recomputed_summary.benign_params.count(src_index));
      }
      if (recomputed_summary.benign_params.size() >
          summary.benign_params.size()) {
        summary.benign_params = std::move(recomputed_summary.benign_params);
        changed_methods.insert(method);
      } else {
        always_assert(summary.benign_params ==
                      recomputed_summary.benign_params);
      }
      if (recomputed_summary.returns_allocation_or_param()) {
        if (summary.returns_allocation_or_param()) {
          always_assert(summary.returns == recomputed_summary.returns);
        } else {
          summary.returns = recomputed_summary.returns;
          changed_methods.insert(method);
        }
      } else {
        always_assert(!summary.returns_allocation_or_param());
      }
    }
    impacted_methods.clear();
    for (auto* method : UnorderedIterable(changed_methods)) {
      auto it = dependencies.find(method);
      if (it != dependencies.end()) {
        insert_unordered_iterable(impacted_methods, it->second);
      }
    }
  }
  return method_summaries;
}

// For an inlinable new-instance or invoke- instruction, determine first
// resolved callee (if any), and (eventually) allocated type
std::pair<DexMethod*, const DexType*> resolve_inlinable(
    const MethodSummaries& method_summaries,
    DexMethod* method,
    const IRInstruction* insn) {
  always_assert(insn->opcode() == OPCODE_NEW_INSTANCE ||
                opcode::is_a_method_invoke(insn->opcode()));
  DexMethod* first_callee{nullptr};
  while (insn->opcode() != OPCODE_NEW_INSTANCE) {
    always_assert(opcode::is_a_method_invoke(insn->opcode()));
    method = resolve_invoke_method_deprecated(insn, method);
    if (first_callee == nullptr) {
      first_callee = method;
    }
    insn = method_summaries.at(method).allocation_insn();
  }
  return std::make_pair(first_callee, insn->get_type());
}

} // namespace object_escape_analysis_impl
