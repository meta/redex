/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "EvaluateTypeChecks.h"

#include <sstream>
#include <type_traits>

#include "CFGMutation.h"
#include "ConfigFiles.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexClass.h"
#include "DexUtil.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "InitClassesWithSideEffects.h"
#include "LiveRange.h"
#include "MethodUtil.h"
#include "PassManager.h"
#include "Trace.h"
#include "TypeInference.h"
#include "TypeUtil.h"
#include "Walkers.h"

namespace check_casts {

namespace {

using namespace cfg;
using namespace type_inference;

void print_type_chain(std::ostream& os, const DexType* type, size_t indent) {
  if (type == nullptr) {
    return;
  }
  for (size_t i = 0; i != indent; ++i) {
    os << ' ';
  }
  os << show(type);
  auto* kls = type_class(type);
  if (kls != nullptr) {
    if (kls->is_external()) {
      os << " (E)";
    }
    os << '\n';
    print_type_chain(os, kls->get_super_class(), indent + 1);
  } else {
    os << '\n';
  }
}

struct RemoveResult {
  size_t methods_w_instanceof{0};
  size_t overrides{0};
  size_t class_always_succeed_or_null{0};
  size_t class_always_succeed_or_null_repl{0};
  size_t class_always_fail{0};
  size_t def_use_loop{0};
  size_t multi_use{0};
  size_t multi_def{0};
  size_t non_branch{0};
  size_t non_supported_branch{0};
  ssize_t insn_delta{0};

  RemoveResult& operator+=(const RemoveResult& rhs) {
    methods_w_instanceof += rhs.methods_w_instanceof;
    overrides += rhs.overrides;
    class_always_succeed_or_null += rhs.class_always_succeed_or_null;
    class_always_succeed_or_null_repl += rhs.class_always_succeed_or_null_repl;
    class_always_fail += rhs.class_always_fail;
    def_use_loop += rhs.def_use_loop;
    multi_use += rhs.multi_use;
    multi_def += rhs.multi_def;
    non_branch += rhs.non_branch;
    non_supported_branch += rhs.non_supported_branch;
    insn_delta += rhs.insn_delta;
    return *this;
  }
};

namespace instance_of {

// If we know that an instance-of will always be true (if the value is not
// null), then it may be beneficial to rewrite the code. The instance-of is
// basically a null-check, which is computationally simpler.
//
// However, instance-of produces a boolean value, while a null-check is a
// conditional branch. If the boolean value is actually used for more than a
// branch, it is a tighter encoding (though more expensive at runtime).
//
// The simple approach here figures out if the output of the instance-of only
// flows into an if-eqz or if-nez directly, and if that is the only value
// flowing into the conditional branch, and in that case uses the value
// directly. The instance-of can then be eliminated, saving space (and
// increasing speed). Follow-up analyzes and optimizations might take advantage
// of the simpler code, e.g., when it can be shown that the receiver is (or is
// not) null.
void analyze_true_instance_ofs(
    ControlFlowGraph& cfg,
    CFGMutation& mutation,
    RemoveResult& res,
    const std::vector<const MethodItemEntry*>& true_modulo_nulls) {
  if (true_modulo_nulls.empty()) {
    return;
  }

  live_range::MoveAwareChains chains(cfg);
  auto du_chains = chains.get_def_use_chains();
  auto ud_chains = chains.get_use_def_chains();

  for (const auto* mie : true_modulo_nulls) {
    auto def_it = cfg.find_insn(mie->insn);
    auto move_it = cfg.move_result_of(def_it);
    if (move_it.is_end()) { // Should not happen.
      continue;
    }

    auto du_it = du_chains.find(mie->insn);
    if (du_it == du_chains.end()) {
      continue;
    }
    const auto* uses = &du_it->second;
    if (uses->empty()) {
      continue;
    }

    auto print_uses = [&uses]() {
      std::ostringstream oss;
      for (const auto& v : UnorderedIterable(*uses)) {
        oss << show(v.insn) << ",";
      }
      return oss.str();
    };

    bool any_multi_def =
        unordered_any_of(*uses, [&ud_chains, &mie](const auto& use) {
          auto it = ud_chains.find(use);
          if (it == ud_chains.end()) {
            // Weird, fail.
            return true;
          }
          if (it->second.size() != 1) {
            return true;
          }
          // Just an integrity check.
          // NOLINTNEXTLINE(bugprone-assert-side-effect) Can't figure this out.
          redex_assert(*it->second.begin() == mie->insn);
          return false;
        });
    if (any_multi_def) {
      TRACE(EVALTC, 3, "Not all single-def: %s", print_uses().c_str());
      ++res.multi_def;
      continue;
    }

    // Filter out moves.
    bool has_moves = unordered_any_of(*uses, [](const auto& use) {
      return opcode::is_a_move(use.insn->opcode());
    });
    std::remove_cv_t<std::remove_pointer_t<decltype(uses)>> filtered_uses;
    if (has_moves) {
      filtered_uses = *uses;
      unordered_erase_if(filtered_uses, [](const auto& u) {
        return opcode::is_a_move(u.insn->opcode());
      });
      uses = &filtered_uses;
    }

    bool non_branch_uses = unordered_any_of(*uses, [](const auto& use) {
      return !opcode::is_a_conditional_branch(use.insn->opcode()) &&
             !opcode::is_a_move(use.insn->opcode());
    });
    if (non_branch_uses) {
      TRACE(EVALTC, 3, "Not all a branch: %s", print_uses().c_str());
      ++res.non_branch;
      continue;
    }

    bool non_supp_branches = unordered_any_of(*uses, [](const auto& use) {
      auto opcode = use.insn->opcode();
      return opcode != OPCODE_IF_EQZ && opcode != OPCODE_IF_NEZ;
    });
    if (non_supp_branches) {
      TRACE(EVALTC, 2, "Unexpected branch types: %s", print_uses().c_str());
      ++res.non_supported_branch;
      continue;
    }

    // v1 := instance-of v0 == v0 != null.
    //  -> if-eqz v1 ~= if-eqz v0
    //  -> if-nez v1 ~= if-nez v0
    //
    // Need a temp to have access to unmodified v0.
    reg_t src_tmp = cfg.allocate_temp();
    {
      auto* copy_reg_insn = new IRInstruction(OPCODE_MOVE_OBJECT);
      copy_reg_insn->set_src(0, mie->insn->src(0));
      copy_reg_insn->set_dest(src_tmp);
      mutation.insert_before(def_it, {copy_reg_insn});
    }
    // Rewrite the conditionals' input.
    for (const auto& use : UnorderedIterable(*uses)) {
      use.insn->set_src(0, src_tmp);
      ++res.class_always_succeed_or_null_repl;
      ++res.overrides;
    }
  }
}

RemoveResult analyze_and_evaluate_instance_of(DexMethod* method) {
  auto& cfg = method->get_code()->cfg();
  CFGMutation mutation(cfg);

  RemoveResult res;
  std::vector<const MethodItemEntry*> true_modulo_nulls;

  // Figure out types. Find guaranteed-false checks.
  {
    TypeInference type_inf(cfg);
    type_inf.run(method);

    auto& type_envs = type_inf.get_type_environments();

    auto get_state = [&type_envs](auto insn) -> const TypeEnvironment* {
      auto it = type_envs.find(insn);
      if (it == type_envs.end()) {
        return nullptr;
      }
      return &it->second;
    };

    for (const MethodItemEntry& mie : cfg::InstructionIterable(cfg)) {
      auto* insn = mie.insn;
      if (insn->opcode() != OPCODE_INSTANCE_OF) {
        continue;
      }

      const auto* state = get_state(insn);
      if (state == nullptr) {
        continue;
      }

      auto* test_type = insn->get_type();

      auto src_type_state = state->get_dex_type(insn->src(0));
      if (!src_type_state) {
        continue;
      }

      auto eval = type::evaluate_type_check(*src_type_state, test_type);
      if (!eval) {
        continue;
      }

      if (traceEnabled(EVALTC, 2)) {
        std::ostringstream oss;
        oss << "Found instance-of that can be evaluated: " << show(mie) << '\n';

        oss << "Test type:\n";
        print_type_chain(oss, test_type, 1);
        oss << "Source type:\n";
        print_type_chain(oss, *src_type_state, 1);
        oss << "Evaluates to:\n " << *eval;

        TRACE(EVALTC, 1, "%s", oss.str().c_str());
      }

      if (*eval == 1) {
        true_modulo_nulls.push_back(&mie);
        ++res.class_always_succeed_or_null;
        continue;
      }
      redex_assert(*eval == 0);

      auto def_it = cfg.find_insn(insn);
      auto move_it = cfg.move_result_of(def_it);
      if (move_it.is_end()) { // Should not happen.
        continue;
      }
      reg_t trg_reg = move_it->insn->dest();

      // Schedule a bypass.
      auto* set_result = new IRInstruction(OPCODE_CONST);
      set_result->set_dest(trg_reg);
      set_result->set_literal(0);
      mutation.insert_after(move_it, {set_result});

      ++res.overrides;
      ++res.class_always_fail;
    }
  }

  // See whether the checks that will succeed if the value is not null
  // can be turned into a null check. If the result is used for more
  // than a branch, transformation is likely not beneficial at the moment.
  analyze_true_instance_ofs(cfg, mutation, res, true_modulo_nulls);

  mutation.flush();
  return res;
}

} // namespace instance_of

namespace check_cast {

void handle_false_case(IRInstruction* insn,
                       ControlFlowGraph& cfg,
                       CFGMutation& mutation,
                       RemoveResult& res) {
  auto def_it = cfg.find_insn(insn);
  auto move_it = cfg.move_result_of(def_it);
  if (move_it.is_end()) { // Should not happen.
    return;
  }

  reg_t trg_reg = move_it->insn->dest();

  // Check whether there's already a `const` with the same target just
  // following. This could be from `RemoveUninstantiables` or previous
  // runs of this pass.
  auto follow_it = std::next(move_it);
  if (!follow_it.is_end()) {
    if (follow_it->insn->opcode() == OPCODE_CONST &&
        follow_it->insn->dest() == trg_reg) {
      return;
    }
  }

  // Schedule a bypass.
  auto* set_result = new IRInstruction(OPCODE_CONST);
  set_result->set_dest(trg_reg);
  set_result->set_literal(0);
  mutation.insert_after(move_it, {set_result});

  ++res.overrides;
  ++res.class_always_fail;
}

RemoveResult analyze_and_evaluate(DexMethod* method) {
  always_assert(method->get_code()->cfg_built());
  auto& cfg = method->get_code()->cfg();
  CFGMutation mutation(cfg);

  RemoveResult res;

  // Figure out types.
  {
    TypeInference type_inf(cfg);
    type_inf.run(method);

    auto& type_envs = type_inf.get_type_environments();

    auto get_state = [&type_envs](auto insn) -> const TypeEnvironment* {
      auto it = type_envs.find(insn);
      if (it == type_envs.end()) {
        return nullptr;
      }
      return &it->second;
    };

    for (const MethodItemEntry& mie : cfg::InstructionIterable(cfg)) {
      auto* insn = mie.insn;
      if (insn->opcode() != OPCODE_CHECK_CAST) {
        continue;
      }

      const auto* state = get_state(insn);
      if (state == nullptr) {
        continue;
      }

      auto* test_type = insn->get_type();

      auto src_type_state = state->get_dex_type(insn->src(0));
      if (!src_type_state) {
        continue;
      }

      auto eval = type::evaluate_type_check(*src_type_state, test_type);
      if (!eval) {
        continue;
      }

      if (traceEnabled(EVALTC, 2)) {
        std::ostringstream oss;
        oss << "Found check-cast that can be evaluated: " << show(mie) << '\n';

        oss << "Test type:\n";
        print_type_chain(oss, test_type, 1);
        oss << "Source type:\n";
        print_type_chain(oss, *src_type_state, 1);
        oss << "Evaluates to:\n " << *eval;

        TRACE(EVALTC, 1, "%s", oss.str().c_str());
      }

      if (*eval == 0) {
        handle_false_case(insn, cfg, mutation, res);
        continue;
      }
      redex_assert(*eval == 1);

      // Successful check, can be eliminated.
      reg_t src_reg = insn->src(0);
      auto def_it = cfg.find_insn(insn);
      auto move_it = cfg.move_result_of(def_it);
      if (move_it.is_end()) { // Should not happen.
        continue;
      }
      reg_t trg_reg = move_it->insn->dest();

      // Schedule a bypass.
      auto* move_result = new IRInstruction(OPCODE_MOVE_OBJECT);
      move_result->set_src(0, src_reg);
      move_result->set_dest(trg_reg);
      mutation.replace(def_it, {move_result});

      ++res.overrides;
      ++res.class_always_succeed_or_null_repl;
    }
  }

  mutation.flush();
  return res;
}

} // namespace check_cast

size_t post_process(DexMethod* method,
                    size_t overrides,
                    shrinker::Shrinker& shrinker) {
  auto* code = method->get_code();
  size_t num_insns_before = code->count_opcodes() - overrides;

  shrinker.shrink_method(method);

  size_t num_insns_after = code->count_opcodes();
  return num_insns_before - num_insns_after;
}

RemoveResult optimize_impl(DexMethod* method,
                           bool has_instance_of,
                           bool has_check_cast,
                           shrinker::Shrinker& shrinker) {
  RemoveResult instance_of_res;
  if (has_instance_of) {
    instance_of_res = instance_of::analyze_and_evaluate_instance_of(method);

    if (instance_of_res.overrides != 0) {
      instance_of_res.insn_delta = static_cast<ssize_t>(
          post_process(method, instance_of_res.overrides, shrinker));
    }
  }

  RemoveResult check_cast_res;
  if (has_check_cast) {
    check_cast_res = check_cast::analyze_and_evaluate(method);

    if (check_cast_res.overrides != 0) {
      check_cast_res.insn_delta = static_cast<ssize_t>(
          post_process(method, check_cast_res.overrides, shrinker));
    }
  }

  instance_of_res += check_cast_res;
  return instance_of_res;
}

} // namespace

std::optional<int32_t> EvaluateTypeChecksPass::evaluate(
    const DexType* src_type, const DexType* test_type) {
  return type::evaluate_type_check(src_type, test_type);
}

void EvaluateTypeChecksPass::optimize(DexMethod* method,
                                      shrinker::Shrinker& shrinker) {
  optimize_impl(method, true, true, shrinker);
}

void EvaluateTypeChecksPass::run_pass(DexStoresVector& stores,
                                      ConfigFiles& conf,
                                      PassManager& mgr) {
  auto scope = build_class_scope(stores);
  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, conf.create_init_class_insns());

  shrinker::ShrinkerConfig shrinker_config;
  shrinker_config.run_const_prop = true;
  shrinker_config.run_copy_prop = true;
  shrinker_config.run_local_dce = true;
  shrinker_config.compute_pure_methods = false;
  int min_sdk = mgr.get_redex_options().min_sdk;
  shrinker::Shrinker shrinker(stores,
                              scope,
                              init_classes_with_side_effects,
                              conf,
                              shrinker_config,
                              min_sdk);

  auto stats = walk::parallel::methods<RemoveResult>(
      scope, [&shrinker](DexMethod* method) {
        auto* code = method->get_code();
        if (!method::is_optimizable(method)) {
          return RemoveResult{};
        }
        auto has_instance_of_check_cast = [&code]() {
          std::pair<bool, bool> res;
          always_assert(code->cfg_built());
          auto& cfg = code->cfg();
          for (const auto& mie : cfg::InstructionIterable(cfg)) {
            if (mie.type != MFLOW_OPCODE) {
              continue;
            }
            if (mie.insn->opcode() == OPCODE_INSTANCE_OF) {
              res.first = true;
              continue;
            }
            if (mie.insn->opcode() == OPCODE_CHECK_CAST) {
              res.second = true;
              continue;
            }
          }
          return res;
        };
        auto has_insns = has_instance_of_check_cast();
        if (!has_insns.first && !has_insns.second) {
          return RemoveResult();
        }

        auto res =
            optimize_impl(method, has_insns.first, has_insns.second, shrinker);
        res.methods_w_instanceof = 1;
        return res;
      });

  mgr.set_metric("num_methods_w_instance_of", stats.methods_w_instanceof);
  mgr.set_metric("num_overrides", stats.overrides);
  mgr.set_metric("num_insn_delta", stats.insn_delta);
  mgr.set_metric("num_class_always_succeed_or_null",
                 stats.class_always_succeed_or_null);
  mgr.set_metric("num_class_always_succeed_or_null_repl",
                 stats.class_always_succeed_or_null_repl);
  mgr.set_metric("num_class_always_fail", stats.class_always_fail);
  mgr.set_metric("num_def_use_loop", stats.def_use_loop);
  mgr.set_metric("num_multi_use", stats.multi_use);
  mgr.set_metric("num_multi_def", stats.multi_def);
  mgr.set_metric("num_non_branch", stats.non_branch);
  mgr.set_metric("num_not_supported_branch", stats.non_supported_branch);
}

static EvaluateTypeChecksPass s_pass;

} // namespace check_casts
