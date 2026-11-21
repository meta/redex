/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "SplitHugeSwitchPass.h"

#include <algorithm>
#include <iostream>
#include <optional>

#include <boost/regex.hpp>

#include "ConfigFiles.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "DexClass.h"
#include "DexLimits.h"
#include "DexStore.h"
#include "DexStructure.h"
#include "DexUtil.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "InterDexPassMetrics.h"
#include "Macros.h"
#include "MethodProfiles.h"
#include "MethodUtil.h"
#include "PassManager.h"
#include "ReachingDefinitions.h"
#include "ScopedCFG.h"
#include "Show.h"
#include "TypeUtil.h"
#include "Walkers.h"

// A simple split pass that splits whole methods with a large switch that is
// reachable "easily" from parameters.
//
// "Easily" here refers to a simple arithmetic chain. In that case there is
// no side effect and likely low overhead to redo the computation of the
// switch expression.
//
// Sample method:
//   LOAD_PARAM vX
//   [...]
//   ADD_INT_LIT vY, vX, #10
//   [...]
//   AND_INT_LIT vZ, vY, #8191
//   [...]
//   SWITCH vZ
//
// This will be changed to:
//   LOAD_PARAM vX
//   ADD_INT_LIT vY', vX, #10
//   AND_INT_LIT vZ', vY', #8181
//   CONST vLit, |FirstSplitValue|
//   IF_GT vZ', vLit :FirstSplitLabel
//   // Original code below here.
//   [...]
//   ADD_INT_LIT vY, vX, #10
//   [...]
//   AND_INT_LIT vZ, vY, #8191
//   [...]
//   SWITCH vZ  // Strip cases > |FirstSplitValue|
//   [...]
//   :FirstSplitLabel
//   CONST vLit, |SecondSplitValue|
//   IF_GT vZ', vLit :SecondSplitLabel
//   INVOKE {...} @ClonedMethodWithSwitchCasesFirstSplitValueToSecondSplitValue
//   (MOVE-RESULT vRes)
//   RETURN-(VOID|... vRes)
//   :SecondSplitValue
//   [...]
//
// Side-effect-free prefixes mean that the complete method can be duplicated
// and called, and the computation can be easily prepended (and possibly cleaned
// up by CSE).
//
// As future work, consider changing the signature of splits, and do not prepend
// a computation of the expression. That allows generic switch prefix
// instructions (including side-effectful ones).

using Stats = SplitHugeSwitchPass::Stats;

namespace {

bool has_switch(cfg::ControlFlowGraph& cfg) {
  for (auto* block : cfg.blocks()) {
    for (const auto& mie : InstructionIterable(block)) {
      auto opcode = mie.insn->opcode();
      if (opcode::is_switch(opcode)) {
        return true;
      }
    }
  }
  return false;
}

cfg::InstructionIterator find_large_switch(cfg::ControlFlowGraph& cfg,
                                           size_t case_threshold) {
  auto it = cfg::InstructionIterator(cfg, /*is_begin=*/true);
  for (; !it.is_end(); ++it) {
    if (!opcode::is_switch(it->insn->opcode())) {
      continue;
    }
    auto* block = it.block();
    redex_assert(it->insn == CONSTP(block)->get_last_insn()->insn);
    if (block->succs().size() >= case_threshold) {
      break;
    }
  }
  return it;
}

// Need to copy move instructions, so they need to be retained here.
class MoveResultAwareFixpointIterator final
    : public ir_analyzer::BaseIRAnalyzer<reaching_defs::Environment> {
 public:
  explicit MoveResultAwareFixpointIterator(const cfg::ControlFlowGraph& cfg)
      : ir_analyzer::BaseIRAnalyzer<reaching_defs::Environment>(cfg) {}

  void analyze_instruction(
      const IRInstruction* insn,
      reaching_defs::Environment* current_state) const override {
    if (opcode::is_move_result_any(insn->opcode())) {
      current_state->set(insn->dest(), current_state->get(RESULT_REGISTER));
      current_state->set(RESULT_REGISTER, reaching_defs::Domain::top());
    } else if (insn->has_move_result_any()) {
      current_state->set(
          RESULT_REGISTER,
          reaching_defs::Domain(const_cast<IRInstruction*>(insn)));
    } else if (insn->has_dest()) {
      current_state->set(
          insn->dest(),
          reaching_defs::Domain(const_cast<IRInstruction*>(insn)));
    }
  }
};

std::optional<IRInstruction*> find_def(
    const MoveResultAwareFixpointIterator& rdefs,
    const cfg::InstructionIterator& src_it,
    size_t src_index = 0) {
  auto defs = rdefs.get_entry_state_at(src_it.block());
  for (const auto& it : ir_list::InstructionIterable{src_it.block()}) {
    if (it.insn == src_it->insn) {
      break;
    }
    rdefs.analyze_instruction(it.insn, &defs);
  }

  auto defs_expr = defs.get(src_it->insn->src(src_index));
  if (defs_expr.is_top() || defs_expr.is_bottom()) {
    return std::nullopt;
  }
  if (defs_expr.elements().size() != 1) {
    return std::nullopt;
  }

  return *defs_expr.elements().begin();
}

using ParamChain = std::optional<std::vector<IRInstruction*>>;

ParamChain find_param_chain(cfg::ControlFlowGraph& cfg,
                            cfg::InstructionIterator cur) {
  MoveResultAwareFixpointIterator rdefs(cfg);
  rdefs.run(reaching_defs::Environment());

  std::vector<IRInstruction*> val;
  val.push_back(cur->insn);

  UnorderedSet<IRInstruction*> seen;
  seen.insert(cur->insn);

  for (;;) {
    auto src = find_def(rdefs, cur);
    if (!src) {
      return std::nullopt;
    }
    auto* src_insn = *src;

    val.push_back(src_insn);
    if (seen.count(src_insn) != 0) {
      return std::nullopt;
    }
    seen.insert(src_insn);

    auto opcode = src_insn->opcode();
    if (opcode::is_a_load_param(opcode)) {
      return val;
    }

    if (src_insn->srcs_size() == 0) {
      return val;
    }
    if (src_insn->srcs_size() >= 2) {
      return std::nullopt;
    }

    cur = cfg.find_insn(src_insn, cur.block());
  }
}

// Compute the switch range and split points.
// Output: Switch cases X min case X max case X vector(splits)
struct SwitchRange {
  size_t cases;
  int32_t min_case;
  int32_t max_case;
  std::vector<int32_t> mid_cases;
};
SwitchRange get_switch_range(const cfg::ControlFlowGraph& cfg,
                             cfg::Block* b,
                             size_t split_into) {
  redex_assert(CONSTP(b)->get_last_insn()->insn->opcode() == OPCODE_SWITCH);
  std::vector<int32_t> cases;
  for (const auto* e : cfg.get_succ_edges_of_type(b, cfg::EDGE_BRANCH)) {
    cases.push_back(*e->case_key());
  }
  std::sort(cases.begin(), cases.end());
  int32_t min_case = 0, max_case = 0;
  std::vector<int32_t> mid_cases;
  if (!cases.empty() && cases.size() > split_into) {
    min_case = cases.front();
    max_case = cases.back();
    for (size_t i = 1; i < split_into; ++i) {
      mid_cases.push_back(cases[(i * cases.size()) / split_into - 1]);
    }
    mid_cases.push_back(max_case);
  }
  return SwitchRange{cases.size(), min_case, max_case, std::move(mid_cases)};
}

DexMethod* create_dex_method(DexMethod* m, std::unique_ptr<IRCode>&& code) {
  const auto* clone_name = DexMethod::get_unique_name(
      m->get_class(),
      DexString::make_string(m->str() + "$split_switch_clone"),
      m->get_proto());

  auto* method_ref =
      DexMethod::make_method(m->get_class(), clone_name, m->get_proto());

  DexAccessFlags access_flags = DexAccessFlags::ACC_PRIVATE;
  if (is_static(m)) {
    access_flags |= DexAccessFlags::ACC_STATIC;
  }
  auto* cloned_method = method_ref->make_concrete(access_flags, std::move(code),
                                                  /* is_virtual */ false);
  cloned_method->set_deobfuscated_name(show_deobfuscated(cloned_method));

  cloned_method->rstate.set_dont_inline(); // Don't undo our work.

  return cloned_method;
}

DexMethod* create_split(DexMethod* orig_method,
                        IRCode* src,
                        size_t case_threshold,
                        int32_t from_excl,
                        int32_t to_incl) {
  auto cloned_code = std::make_unique<IRCode>(*src);

  {
    auto& cfg = cloned_code->cfg();
    auto cloned_switch_it = find_large_switch(cfg, case_threshold);
    redex_assert(!cloned_switch_it.is_end());

    cfg.delete_succ_edge_if(cloned_switch_it.block(),
                            [from_excl, to_incl](const cfg::Edge* e) {
                              if (e->type() != cfg::EDGE_BRANCH) {
                                return false;
                              }
                              int32_t key = *e->case_key();
                              return key <= from_excl || key > to_incl;
                            });

    // Simplify to remove unreachable blocks.
    cfg.simplify();
  }

  return create_dex_method(orig_method, std::move(cloned_code));
}

void maybe_split_entry(cfg::ControlFlowGraph& cfg) {
  auto load_param_insns = cfg.get_param_instructions();
  redex_assert(!load_param_insns.empty());
  always_assert(load_param_insns.begin()->type == MFLOW_OPCODE);
  always_assert_log(
      cfg.find_insn(load_param_insns.begin()->insn, cfg.entry_block())
              .block() == cfg.entry_block(),
      "Load instructions must be in the CFG's entry block");
  // TODO: Support load-param instruction in blocks other than the entry
  // block (not common)

  if (cfg.entry_block()->get_last_insn()->insn ==
      load_param_insns.back().insn) {
    return;
  }

  cfg.split_block(cfg.entry_block(), std::prev(load_param_insns.end()));
}

// Create a copy of the chain, with new registers. Insert new block(s) after
// the entry block, and return the final block and the final register.
std::pair<cfg::Block*, reg_t> clone_param_chain(
    cfg::ControlFlowGraph& cfg, const std::vector<IRInstruction*>& chain) {
  cfg::Block* new_block = nullptr;
  auto it = chain.rbegin(); // The LOAD_PARAM.
  reg_t new_reg = (*it)->dest();
  reg_t old_reg = new_reg;
  ++it;
  auto stop = std::prev(chain.rend()); // Skip switch.
  for (; it != stop; ++it) {
    if (new_block == nullptr) {
      new_block = cfg.create_block();
      redex_assert(cfg.entry_block()->succs().size() == 1);
      cfg.copy_succ_edges(cfg.entry_block(), new_block);
      cfg.set_edge_target(cfg.entry_block()->succs()[0], new_block);
    }
    auto* clone_insn = new IRInstruction(**it);
    // Replace old_reg with new_reg.
    for (size_t i = 0; i < clone_insn->srcs_size(); ++i) {
      if (clone_insn->src(i) == old_reg) {
        clone_insn->set_src(i, new_reg);
      }
    }
    // Allocate new temp reg.
    if (clone_insn->has_dest()) {
      new_reg = cfg.allocate_temp();
      old_reg = clone_insn->dest();
      clone_insn->set_dest(new_reg);
    }

    new_block->push_back(clone_insn);
  }
  return std::make_pair(new_block, new_reg);
}

void insert_dispatches(
    DexMethod* m,
    cfg::ControlFlowGraph& cfg,
    cfg::Block* last_block,
    reg_t value_reg,
    const std::vector<std::pair<int32_t, DexMethod*>>& splits) {
  // Note: Assume the split set is small. Binary search is likely not worth it.
  if (last_block == nullptr) {
    last_block = cfg.entry_block();
  }
  redex_assert(last_block->succs().size() == 1);
  auto* fallthrough = last_block->succs()[0]->target();

  // Create templates for the dispatch code, so it's easy to create a block.
  auto invoke_template = std::make_unique<IRInstruction>(
      is_static(m) ? OPCODE_INVOKE_STATIC : OPCODE_INVOKE_DIRECT);
  {
    auto params = cfg.get_param_instructions();
    size_t s = 0;
    for (const auto& i ATTRIBUTE_UNUSED : params) {
      ++s;
    }
    invoke_template->set_srcs_size(s);
    size_t i = 0;
    for (const auto& mie : params) {
      invoke_template->set_src(i, mie.insn->dest());
      ++i;
    }
  }
  std::unique_ptr<IRInstruction> move_result_template;
  if (!type::is_void(m->get_proto()->get_rtype())) {
    move_result_template =
        std::make_unique<IRInstruction>(opcode::move_result_for_invoke(m));
    reg_t ret_reg = type::is_wide_type(m->get_proto()->get_rtype())
                        ? cfg.allocate_wide_temp()
                        : cfg.allocate_temp();
    move_result_template->set_dest(ret_reg);
  }
  std::unique_ptr<IRInstruction> return_template;
  if (move_result_template) {
    return_template = std::make_unique<IRInstruction>(
        opcode::return_opcode(m->get_proto()->get_rtype()));
    return_template->set_src(0, move_result_template->dest());
  } else {
    return_template = std::make_unique<IRInstruction>(OPCODE_RETURN_VOID);
  }

  // First create the blocks, then connect them. The CFG code requires existing
  // blocks for both branches (and it's good to avoid empty blocks).
  struct BlockT {
    cfg::Block* condition_head;
    IRInstruction* branch_insn;
    cfg::Block* dispatch_block;
  };
  std::vector<BlockT> dispatch_blocks;
  reg_t lit_reg = cfg.allocate_temp();
  for (const auto& p : splits) {
    // Create condition head block.
    auto* condition_block = cfg.create_block();

    auto* literal_insn = new IRInstruction(OPCODE_CONST);
    literal_insn->set_literal(p.first);
    literal_insn->set_dest(lit_reg);
    condition_block->push_back(literal_insn);

    auto* ifgt_insn = new IRInstruction(OPCODE_IF_GT);
    ifgt_insn->set_src(0, value_reg);
    ifgt_insn->set_src(1, lit_reg);

    // Create invoke and return.
    auto* dispatch_block = cfg.create_block();
    auto* invoke = new IRInstruction(*invoke_template);
    invoke->set_method(p.second);
    dispatch_block->push_back(invoke);
    if (move_result_template) {
      dispatch_block->push_back(new IRInstruction(*move_result_template));
    }
    dispatch_block->push_back(new IRInstruction(*return_template));

    dispatch_blocks.push_back({condition_block, ifgt_insn, dispatch_block});
  }

  // Now assemble.
  auto* last_fallthrough = fallthrough;
  for (size_t i = 0; i != dispatch_blocks.size(); ++i) {
    const auto& b = dispatch_blocks[i];
    auto* next_block = i < dispatch_blocks.size() - 1
                           ? dispatch_blocks[i + 1].condition_head
                           : b.dispatch_block;
    cfg.create_branch(b.condition_head, b.branch_insn, last_fallthrough,
                      next_block);
    last_fallthrough = b.dispatch_block;
  }

  // Now insert after entry.
  cfg.set_edge_target(last_block->succs()[0],
                      dispatch_blocks[0].condition_head);
}

struct AnalysisData {
  std::optional<cfg::ScopedCFG> scoped_cfg = std::nullopt;
  std::optional<cfg::InstructionIterator> switch_it = std::nullopt;
  std::optional<ParamChain> param_chain = std::nullopt;
  std::optional<SwitchRange> switch_range = std::nullopt;

  DexMethod* m{nullptr};
  bool no_code{false};
  bool under_code_units_threshold{false};
  bool no_switch{false};
  bool no_large_switch{false};
  bool no_easy_expr{false};
  bool cannot_split{false};
  bool no_load_param_anchor{false};
  bool no_simple_chain{false};
  bool constructor{false};
  bool not_hot{false};

  AnalysisData() = default;
  AnalysisData(const AnalysisData&) = delete;
  AnalysisData(AnalysisData&&) = default;

  AnalysisData& operator=(const AnalysisData&) = delete;
  AnalysisData& operator=(AnalysisData&&) = default;
};

Stats analysis_data_to_stats(const AnalysisData& data, DexMethod* m) {
  Stats ret{};

  if (data.no_code) {
    return ret;
  }

  if (data.under_code_units_threshold) {
    return ret;
  }
  ret.large_methods_set.emplace(m);

  if (data.no_switch) {
    return ret;
  }
  ret.switch_methods_set.emplace(m);

  if (data.no_large_switch) {
    return ret;
  }
  ret.large_switches_set.emplace(m);

  if (data.no_easy_expr) {
    return ret;
  }
  ret.easy_expr_set.emplace(m);

  if (data.cannot_split || data.no_load_param_anchor) {
    return ret;
  }

  if (data.no_simple_chain) {
    ret.non_simple_chain = 1;
    return ret;
  }

  if (data.constructor) {
    ret.constructor = 1;
    return ret;
  }

  if (data.not_hot) {
    ret.not_hot = 1;
    return ret;
  }

  return ret;
}

AnalysisData analyze(DexMethod* m,
                     IRCode* code,
                     size_t code_units_threshold,
                     size_t case_threshold,
                     const method_profiles::MethodProfiles& method_profiles,
                     double hotness_threshold) {
  auto data = AnalysisData{};
  data.m = m;
  if (code == nullptr) {
    data.no_code = true;
    return data;
  }
  data.no_code = false;

  auto size = code->estimate_code_units();
  if (size <= code_units_threshold) {
    data.under_code_units_threshold = true;
    return data;
  }
  data.under_code_units_threshold = false;
  // stats.large_methods_set.emplace(m);

  cfg::ScopedCFG scoped_cfg(code);

  if (!has_switch(*scoped_cfg)) {
    data.no_switch = true;
    return data;
  }
  data.no_switch = false;
  // stats.switch_methods_set.emplace(m);

  auto switch_it = find_large_switch(*scoped_cfg, case_threshold);
  if (switch_it.is_end()) {
    data.no_large_switch = true;
    return data;
  }
  data.no_large_switch = false;
  // stats.large_switches_set.emplace(m);

  auto param_chain = find_param_chain(*scoped_cfg, switch_it);
  if (!param_chain) {
    data.no_easy_expr = true;
    return data;
  }
  data.no_easy_expr = false;

  auto nr_splits = static_cast<size_t>(std::ceil(
      static_cast<float>(size) / static_cast<float>(code_units_threshold)));
  redex_assert(nr_splits > 1);
  auto switch_range =
      get_switch_range(*scoped_cfg, switch_it.block(), nr_splits);
  if (switch_range.cases < nr_splits) {
    // Cannot split into the requested amount.
    data.cannot_split = true;
    return data;
  }
  data.cannot_split = false;
  redex_assert(!switch_range.mid_cases.empty());

  const IRInstruction* load_param = param_chain->back();
  if (!opcode::is_a_load_param(load_param->opcode())) {
    data.no_load_param_anchor = true;
    return data;
  }
  data.no_load_param_anchor = false;

  if (param_chain->size() > 2) {
    // Only support some trivial chains for now.
    for (size_t i = param_chain->size() - 2; i > 0; --i) {
      const IRInstruction* middle = param_chain->at(i);
      switch (middle->opcode()) {
      case OPCODE_ADD_INT_LIT:
      case OPCODE_AND_INT_LIT:
      case OPCODE_MOVE:
        continue;

      default:
        data.no_simple_chain = true;
        return data;
      }
    }
  }
  data.no_simple_chain = false;

  // Could support this, probably.
  if (method::is_any_init(m)) {
    data.constructor = true;
    return data;
  }
  data.constructor = false;

  // Filter out non-hot methods.
  if (hotness_threshold > 0 && method_profiles.has_stats()) {
    bool is_hot = std::ranges::any_of(
        method_profiles.all_interactions(), [&](const auto& interaction_stats) {
          const auto& stats_map = interaction_stats.second;
          return stats_map.count(m) != 0 &&
                 stats_map.at(m).call_count >= hotness_threshold;
        });
    if (!is_hot) {
      data.not_hot = true;
      return data;
    }
  }
  data.not_hot = false;

  data.scoped_cfg = std::move(scoped_cfg);
  data.switch_it = std::move(switch_it);
  data.param_chain = std::move(param_chain);
  data.switch_range = std::move(switch_range);

  return data;
}

// Actually split the method.
std::vector<DexMethod*> run_split(AnalysisData& analysis_data,
                                  DexMethod* m,
                                  IRCode* code,
                                  size_t case_threshold) {
  const auto& mid_cases = analysis_data.switch_range->mid_cases;
  // Create splits.
  std::vector<std::pair<int32_t, DexMethod*>> new_methods;
  new_methods.reserve(mid_cases.size() - 1);
  for (size_t i = 0; i < mid_cases.size() - 1; ++i) {
    int32_t above = mid_cases[i];
    int32_t to = mid_cases[i + 1];
    auto* cloned_method = create_split(m, code, case_threshold, above, to);
    new_methods.emplace_back(above, cloned_method);
  }

  auto& scoped_cfg = *analysis_data.scoped_cfg;

  // Cut down switch in the original.
  scoped_cfg->delete_succ_edge_if(
      analysis_data.switch_it->block(), [&mid_cases](const cfg::Edge* e) {
        return e->type() == cfg::EDGE_BRANCH && *e->case_key() > mid_cases[0];
      });
  scoped_cfg->simplify(); // Simplify to remove unreachable blocks.

  // Insert chain for dispatch.
  maybe_split_entry(*scoped_cfg);
  auto cloned_chain =
      clone_param_chain(*scoped_cfg, **analysis_data.param_chain);
  insert_dispatches(m, *scoped_cfg, cloned_chain.first, cloned_chain.second,
                    new_methods);

  std::vector<DexMethod*> ret;
  ret.reserve(new_methods.size());
  for (auto& p : new_methods) {
    ret.push_back(p.second);
  }
  return ret;
}

Stats run_split_dexes(DexStoresVector& stores,
                      std::vector<AnalysisData>& methods,
                      const method_profiles::MethodProfiles& method_profiles,
                      size_t case_threshold,
                      size_t reserved_mrefs) {
  UnorderedSet<DexType*> cset;
  UnorderedMap<DexType*, std::vector<AnalysisData>> mmap;
  for (auto& data : methods) {
    auto* t = data.m->get_class();
    cset.insert(t);
    mmap[t].emplace_back(std::move(data));
  }

  Stats result{};
  std::mutex mutex; // protecting result
  std::vector<const DexClasses*> dexes;
  for (const DexStore& store : stores) {
    for (const auto& dex : store.get_dexen()) {
      dexes.push_back(&dex);
    }
  }
  workqueue_run<const DexClasses*>(
      [&](const DexClasses* dex) {
        // Collect the candidates in this dex.
        std::vector<DexType*> dex_candidate_types;
        for (const auto* c : *dex) {
          if (cset.count(c->get_type()) != 0) {
            dex_candidate_types.push_back(c->get_type());
          }
        }
        if (dex_candidate_types.empty()) {
          return;
        }
        UnorderedSet<DexMethodRef*> method_refs;
        for (auto* cls : *dex) {
          cls->gather_methods(method_refs);
        }

        // Get the candidate methods.
        std::vector<AnalysisData> dex_candidate_methods;
        for (auto* t : dex_candidate_types) {
          dex_candidate_methods.insert(dex_candidate_methods.end(),
                                       std::make_move_iterator(mmap[t].begin()),
                                       std::make_move_iterator(mmap[t].end()));
        }

        // If hotness data is available, sort.
        if (method_profiles.has_stats()) {
          std::sort(
              dex_candidate_methods.begin(),
              dex_candidate_methods.end(),
              [&](const AnalysisData& lhs, const AnalysisData& rhs) {
                const auto& profile_stats =
                    method_profiles.method_stats(method_profiles::COLD_START);
                auto call_count = [&profile_stats](DexMethod* m) {
                  auto it = profile_stats.find(m);
                  return it != profile_stats.end() ? it->second.call_count : 0;
                };
                double lhs_hotness = call_count(lhs.m);
                double rhs_hotness = call_count(rhs.m);
                // Sort by hotness, descending.
                if (lhs_hotness > rhs_hotness) {
                  return true;
                }
                if (lhs_hotness < rhs_hotness) {
                  return false;
                }
                // Then greedily by size.
                size_t lhs_size = lhs.switch_range->mid_cases.size();
                size_t rhs_size = rhs.switch_range->mid_cases.size();
                if (lhs_size > rhs_size) {
                  return true;
                }
                if (lhs_size < rhs_size) {
                  return false;
                }
                // For determinism, compare by name.
                return compare_dexmethods(lhs.m, rhs.m);
              });
        }

        // Now go and apply.
        always_assert_log(method_refs.size() + reserved_mrefs <= kMaxMethodRefs,
                          "Method refs exceeded in a dex: %zu + %zu > %zu",
                          method_refs.size(), reserved_mrefs, kMaxMethodRefs);
        MethodRefRoom room(method_refs.size(), reserved_mrefs);
        for (auto& data : dex_candidate_methods) {
          size_t required = data.switch_range->mid_cases.size() - 1;
          if (!room.can_add(required)) {
            std::lock_guard<std::mutex> lock_guard(mutex);
            ++result.no_slots;
            continue;
          }
          room.add(required);
          always_assert(data.m->get_code());
          always_assert(data.m->get_code()->cfg_built());
          size_t orig_size = data.m->get_code()->cfg().estimate_code_units();
          auto new_methods =
              run_split(data, data.m, data.m->get_code(), case_threshold);
          size_t new_size = data.m->get_code()->cfg().estimate_code_units();
          for (DexMethod* m : new_methods) {
            type_class(m->get_class())->add_method(m);
            new_size += m->get_code()->cfg().estimate_code_units();
          }

          std::lock_guard<std::mutex> lock_guard(mutex);
          result.new_methods.insert(new_methods.begin(), new_methods.end());
          for (auto* m : new_methods) {
            result.orig_methods.emplace_back(m, data.m);
          }
          result.transformed_srcs.emplace(data.m,
                                          std::make_pair(orig_size, new_size));
        }
      },
      dexes);

  return result;
}

} // namespace

Stats& Stats::operator+=(const Stats& rhs) {
  constructor += rhs.constructor;
  non_simple_chain += rhs.non_simple_chain;
  split_sources += rhs.split_sources;
  not_hot += rhs.not_hot;
  no_slots += rhs.no_slots;
  insert_unordered_iterable(large_methods_set, rhs.large_methods_set);
  insert_unordered_iterable(switch_methods_set, rhs.switch_methods_set);
  insert_unordered_iterable(large_switches_set, rhs.large_switches_set);
  insert_unordered_iterable(easy_expr_set, rhs.easy_expr_set);
  insert_unordered_iterable(new_methods, rhs.new_methods);
  orig_methods.insert(orig_methods.end(), rhs.orig_methods.begin(),
                      rhs.orig_methods.end());
  insert_unordered_iterable(transformed_srcs, rhs.transformed_srcs);
  return *this;
}

Stats SplitHugeSwitchPass::run(
    DexMethod* m,
    IRCode* code,
    size_t code_units_threshold,
    size_t case_threshold,
    const method_profiles::MethodProfiles& method_profiles,
    double hotness_threshold) {
  AnalysisData data = analyze(m,
                              m->get_code(),
                              code_units_threshold,
                              case_threshold,
                              method_profiles,
                              hotness_threshold);

  Stats ret = analysis_data_to_stats(data, m);
  if (!data.scoped_cfg) {
    return ret;
  }

  auto new_methods = run_split(data, m, code, case_threshold);
  ret.new_methods.insert(new_methods.begin(), new_methods.end());
  for (auto* new_m : new_methods) {
    ret.orig_methods.emplace_back(new_m, m);
  }
  return ret;
}

void SplitHugeSwitchPass::bind_config() {
  bind("method_filter", "", m_method_filter, "Method filter regex");
  bind("consider_methods_too_large_for_inlining", false,
       m_consider_methods_too_large_for_inlining,
       "Whether to consider methods that have become too large to be inlined "
       "intoregardless of hotness");
  bind("hotness_threshold",
       5.0F,
       m_hotness_threshold,
       "Method hotness threshold");
  bind("method_size", 9000u, m_method_size, "Method size threshold");
  bind("method_size_when_too_large_for_inlining", 9000u,
       m_method_size_when_too_large_for_inlining,
       "Method size threshold for methods that were previously identified as "
       "too large to be inlined into");
  bind("switch_size", 100u, m_switch_size, "Switch case threshold");
  bind("debug", false, m_debug, "Debug output");
  bind("derive_stats", false, m_derive_stats, "Derive stats");
}

void SplitHugeSwitchPass::run_pass(DexStoresVector& stores,
                                   ConfigFiles& conf,
                                   PassManager& mgr) {
  // Don't run under instrumentation.
  if (mgr.get_redex_options().instrument_pass_enabled) {
    return;
  }

  auto& method_profiles = conf.get_method_profiles();
  mgr.set_metric("has_method_profiles", method_profiles.has_stats() ? 1 : 0);

  const boost::regex rx(m_method_filter.empty() ? "." : m_method_filter);

  // 1) Collect all methods that fit the constraints.

  // Move semantics does not work well with accumulator.
  std::vector<AnalysisData> candidates;
  std::mutex candidates_mutex;

  const auto& scope = build_class_scope(stores);
  auto stats = walk::parallel::methods<Stats>(scope, [&](DexMethod* m) {
    if (!boost::regex_search(show(m), rx)) {
      return Stats{};
    }

    auto method_size = m->rstate.too_large_for_inlining_into()
                           ? m_method_size_when_too_large_for_inlining
                           : m_method_size;
    auto hotness_threshold = (m_consider_methods_too_large_for_inlining &&
                              m->rstate.too_large_for_inlining_into())
                                 ? 0
                                 : m_hotness_threshold;
    AnalysisData data = analyze(m,
                                m->get_code(),
                                method_size,
                                m_switch_size,
                                method_profiles,
                                hotness_threshold);

    Stats ret = analysis_data_to_stats(data, m);
    if (!data.scoped_cfg) {
      return ret;
    }

    std::unique_lock<std::mutex> lock{candidates_mutex};
    candidates.emplace_back(std::move(data));
    return ret;
  });

  mgr.set_metric("large_methods", stats.large_methods_set.size());
  mgr.set_metric("switch_methods", stats.switch_methods_set.size());
  mgr.set_metric("large_switches", stats.large_switches_set.size());
  mgr.set_metric("constructor", stats.constructor);
  mgr.set_metric("non_simple_chain", stats.non_simple_chain);
  mgr.set_metric("split_sources", candidates.size());
  mgr.set_metric("not_hot", stats.not_hot);

  auto print_debug = [&](const Stats& stats, const Stats* result_stats) {
    auto print = [&](const auto& in, const std::string& header) {
      std::cerr << header << '\n';
      for (const DexMethod* m : unordered_to_ordered(in, compare_dexmethods)) {
        std::cerr << " * " << show(m) << '\n';
      }
    };
    print(stats.large_methods_set, "Large methods");
    print(stats.switch_methods_set, "Large methods with a switch");
    print(stats.large_switches_set, "Large methods with a large switch");
    std::cerr << stats.constructor << " constructors." << '\n';
    std::cerr << stats.non_simple_chain << " non-simple chains." << '\n';
    std::cerr << stats.not_hot << " non-hot methods." << '\n';
    if (result_stats != nullptr) {
      print(result_stats->new_methods, "Created methods");
    }
  };

  if (candidates.empty()) {
    if (m_debug) {
      print_debug(stats, nullptr);
    }
    return;
  }

  // 2) Prioritize and split the candidates per dex.

  Stats result_stats =
      run_split_dexes(stores, candidates, method_profiles, m_switch_size,
                      interdex::get_interdex_reserved_refs(mgr).mrefs);

  mgr.set_metric("created_methods", result_stats.new_methods.size());
  mgr.set_metric("no_slots", result_stats.no_slots);

  auto replace_chars = [](std::string& s) {
    for (auto& c : s) {
      if (isalnum(c) == 0) {
        c = '_';
      }
    }
  };
  for (auto* m : UnorderedIterable(result_stats.new_methods)) {
    std::string name = show(m);
    replace_chars(name);
    mgr.set_metric("method_created_" + name, 1);
  }
  if (m_derive_stats) {
    for (auto [m, orig_m] : result_stats.orig_methods) {
      method_profiles.derive_stats(m, {orig_m});
    }
    mgr.set_metric("derived_stats", result_stats.orig_methods.size());
  }
  for (const auto& p : UnorderedIterable(result_stats.transformed_srcs)) {
    std::string name = show(p.first);
    replace_chars(name);
    mgr.set_metric("method_size_orig_" + name, p.second.first);
    mgr.set_metric("method_size_split_" + name, p.second.second);
  }

  // Debug output.

  if (m_debug) {
    print_debug(stats, &result_stats);
  }
}

static SplitHugeSwitchPass s_pass;
