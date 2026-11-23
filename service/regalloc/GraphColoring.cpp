/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "GraphColoring.h"

#include <algorithm>
#include <boost/pending/disjoint_sets.hpp>
#include <boost/property_map/property_map.hpp>

#include "CFGMutation.h"
#include "Debug.h"
#include "DexOpcode.h"
#include "Dominators.h"
#include "Show.h"
#include "Trace.h"
#include "Transform.h"
#include "TypeUtil.h"
#include "VirtualRegistersFile.h"

namespace regalloc {

/*
 * Find the first instruction in a block (if any) that uses a given register.
 */
static IRList::iterator find_first_use_in_block(reg_t use, cfg::Block* block) {
  auto ii = InstructionIterable(block);
  auto it = ii.begin();
  for (; it != ii.end(); ++it) {
    auto* insn = it->insn;
    for (size_t i = 0; i < insn->srcs_size(); ++i) {
      if (insn->src(i) == use) {
        return it.unwrap();
      }
    }
  }
  return it.unwrap();
}

static void find_first_uses_dfs(
    reg_t reg,
    cfg::Block* block,
    std::vector<cfg::Block*>* blocks_with_uses,
    UnorderedSet<const cfg::Block*>* visited_blocks) {
  if (visited_blocks->count(block) != 0) {
    return;
  }
  visited_blocks->emplace(block);

  auto use_it = find_first_use_in_block(reg, block);
  if (use_it != block->end()) {
    blocks_with_uses->emplace_back(block);
    return;
  }
  for (const auto& s : block->succs()) {
    find_first_uses_dfs(reg, s->target(), blocks_with_uses, visited_blocks);
  }
}

/*
 * Search for the first uses of a register, starting from the entry block.
 */
static std::vector<cfg::Block*> find_first_uses(reg_t reg, cfg::Block* entry) {
  UnorderedSet<const cfg::Block*> visited_blocks;
  std::vector<cfg::Block*> blocks_with_uses;
  find_first_uses_dfs(reg, entry, &blocks_with_uses, &visited_blocks);
  return blocks_with_uses;
}

/*
 * Given an invoke opcode, returns the number of virtual registers that it
 * requires for its sources.
 */
static size_t sum_src_sizes(const IRInstruction* insn) {
  size_t size{0};
  if (insn->opcode() != OPCODE_INVOKE_STATIC) {
    // Account for the implicit `this` parameter
    ++size;
  }
  for (auto* type : *insn->get_method()->get_proto()->get_args()) {
    size += type::is_wide_type(type) ? 2 : 1;
  }
  return size;
}

/*
 * Gathers all the instructions that must be encoded in range form.
 */
RangeSet init_range_set(cfg::ControlFlowGraph& cfg) {
  RangeSet range_set;
  for (const auto& mie : InstructionIterable(cfg)) {
    const auto* insn = mie.insn;
    auto op = insn->opcode();
    bool is_range{false};
    if (op == OPCODE_FILLED_NEW_ARRAY) {
      is_range = insn->srcs_size() > dex_opcode::NON_RANGE_MAX;
    } else if (opcode::is_a_method_invoke(op)) {
      is_range = sum_src_sizes(insn) > dex_opcode::NON_RANGE_MAX;
    }
    if (is_range) {
      range_set.emplace(insn);
    }
  }
  return range_set;
}

namespace graph_coloring {

namespace {

/*
 * Given a node in the interference graph, mark all the vregs in the
 * register file that have been allocated to adjacent neighbors.
 */
void mark_adjacent(const interference::Graph& ig,
                   reg_t reg,
                   const transform::RegMap& reg_map,
                   VirtualRegistersFile* vreg_file) {
  for (auto adj : ig.get_node(reg).adjacent()) {
    auto it = reg_map.find(adj);
    if (it != reg_map.end()) {
      vreg_file->alloc_at(it->second, ig.get_node(adj).width());
    }
  }
}

constexpr int INVALID_SCORE = std::numeric_limits<int>::max();

/*
 * If :reg is mapped to something other than :vreg, then we'll need to insert a
 * move instruction to remap :reg.
 */
bool needs_remap(const transform::RegMap& reg_map, reg_t reg, vreg_t vreg) {
  auto it = reg_map.find(reg);
  return it != reg_map.end() && it->second != vreg;
}

/*
 * Count the number of vregs we would need to spill if we allocated a
 * contiguous range of vregs starting at :range_base.
 */
int score_range_fit(const interference::Graph& ig,
                    const boost::iterator_range<const reg_t*>& range_regs,
                    vreg_t range_base,
                    const UnorderedMap<reg_t, VirtualRegistersFile>& vreg_files,
                    const transform::RegMap& reg_map) {
  int score{0};
  auto vreg = range_base;
  for (size_t i = 0; i < range_regs.size(); ++i) {
    auto reg = range_regs[static_cast<ptrdiff_t>(i)];
    const auto& node = ig.get_node(reg);
    const auto& vreg_file = vreg_files.at(reg);
    if (!vreg_file.is_free(vreg, node.width())) {
      return INVALID_SCORE;
    }
    if (vreg > node.max_vreg() || needs_remap(reg_map, reg, vreg)) {
      ++score;
    }
    vreg += node.width();
  }
  return score;
}

/*
 * Searches between :range_base_start and :range_base_end, and returns the
 * range_base with the best score.
 */
vreg_t find_best_range_fit(
    const interference::Graph& ig,
    const boost::iterator_range<const reg_t*>& range_regs,
    vreg_t range_base_start,
    vreg_t range_base_end,
    const UnorderedMap<reg_t, VirtualRegistersFile>& vreg_files,
    const transform::RegMap& reg_map) {
  int min_score{INVALID_SCORE};
  vreg_t range_base = 0;
  for (vreg_t i = range_base_start; i <= range_base_end; ++i) {
    auto score = score_range_fit(ig, range_regs, i, vreg_files, reg_map);
    if (score < min_score) {
      min_score = score;
      range_base = i;
    }
    if (min_score == 0) {
      break;
    }
  }
  always_assert(min_score != INVALID_SCORE);
  return range_base;
}

/*
 * Map a range instruction such that it starts at :range_base. Insert spills
 * as necessary.
 */
void fit_range_instruction(
    const interference::Graph& ig,
    const IRInstruction* insn,
    vreg_t range_base,
    const UnorderedMap<reg_t, VirtualRegistersFile>& vreg_files,
    RegisterTransform* reg_transform,
    SpillPlan* spills) {
  auto vreg = range_base;
  for (size_t i = 0; i < insn->srcs_size(); ++i) {
    auto src = insn->src(i);
    const auto& node = ig.get_node(src);
    auto& reg_map = reg_transform->map;
    // If the vreg we're trying to map the node to is too large, or if the node
    // has been mapped to a different vreg already, we need to spill it.
    if (vreg > node.max_vreg() || needs_remap(reg_map, src, vreg)) {
      spills->range_spills[insn].emplace_back(i);
    } else {
      const auto& vreg_file = vreg_files.at(src);
      always_assert(vreg_file.is_free(vreg, node.width()));
      reg_map.emplace(src, vreg);
    }
    vreg += node.width();
  }
  reg_transform->size = std::max(reg_transform->size, vreg);
}

/*
 * Map the parameters such that they start at :param_base. Insert spills as
 * necessary.
 */
void fit_params(const interference::Graph& ig,
                const boost::sub_range<IRList>& param_insns,
                vreg_t params_base,
                const UnorderedMap<reg_t, VirtualRegistersFile>& vreg_files,
                RegisterTransform* reg_transform,
                SpillPlan* spills) {
  auto vreg = params_base;
  for (const auto& mie : InstructionIterable(param_insns)) {
    auto* insn = mie.insn;
    auto dest = insn->dest();
    const auto& node = ig.get_node(dest);
    auto& reg_map = reg_transform->map;
    // If the vreg we're trying to map the node to is too large, or if the node
    // has been mapped to a different vreg already, we need to spill it.
    if (vreg > node.max_vreg() || needs_remap(reg_map, dest, vreg)) {
      spills->param_spills.emplace(dest);
    } else {
      const auto& vreg_file = vreg_files.at(dest);
      always_assert(vreg_file.is_free(vreg, node.width()));
      reg_map.emplace(dest, vreg);
    }
    vreg += node.width();
  }
  reg_transform->size = std::max(reg_transform->size, vreg);
}

std::string show(const SpillPlan& spill_plan) {
  std::ostringstream ss;
  ss << "Global spills:\n";
  for (auto pair : UnorderedIterable(spill_plan.global_spills)) {
    ss << pair.first << " -> " << pair.second << "\n";
  }
  ss << "Param spills:\n";
  for (auto reg : UnorderedIterable(spill_plan.param_spills)) {
    ss << reg << "\n";
  }
  ss << "Range spills:\n";
  for (const auto& pair : UnorderedIterable(spill_plan.range_spills)) {
    const auto* insn = pair.first;
    ss << show(insn) << ": ";
    for (auto idx : pair.second) {
      ss << insn->src(idx) << " ";
    }
    ss << "\n";
  }
  return ss.str();
}

std::string show(const SplitPlan& split_plan) {
  std::ostringstream ss;
  ss << "split_around:\n";
  for (const auto& pair : UnorderedIterable(split_plan.split_around)) {
    ss << pair.first << ": ";
    for (auto reg : UnorderedIterable(pair.second)) {
      ss << reg << " ";
    }
    ss << "\n";
  }
  return ss.str();
}

std::string show(const interference::Graph& ig) {
  std::ostringstream ss;
  ig.write_dot_format(ss);
  return ss.str();
}

std::string show(const RegisterTransform& reg_transform) {
  std::ostringstream ss;
  ss << "size: " << reg_transform.size << "\n";
  for (auto pair : UnorderedIterable(reg_transform.map)) {
    ss << pair.first << " -> " << pair.second << "\n";
  }
  return ss.str();
}

} // namespace

Allocator::Stats& Allocator::Stats::operator+=(const Allocator::Stats& that) {
  reiteration_count += that.reiteration_count;
  param_spill_moves += that.param_spill_moves;
  range_spill_moves += that.range_spill_moves;
  global_spill_moves += that.global_spill_moves;
  split_moves += that.split_moves;
  split_check_cast_result_live_ranges_count +=
      that.split_check_cast_result_live_ranges_count;
  moves_coalesced += that.moves_coalesced;
  params_spill_early += that.params_spill_early;
  return *this;
}

static bool has_2addr_form(IROpcode op) {
  return op >= OPCODE_ADD_INT && op <= OPCODE_REM_DOUBLE;
}

/*
 * Coalesce symregs when there is potential for a more compact encoding. There
 * are 3 kinds of instructions that have this opportunity:
 *
 *   * move instructions whose src and dest don't interfere can be removed
 *
 *   * instructions like add-int whose src(0) and dest don't interfere may
 *     be encoded as add-int/2addr
 *
 *   * check-cast instructions with identical src and dest won't need to be
 *     preceded by a move opcode in the output
 *
 * Coalescing means that we combine the interference graph nodes. If we have a
 * move instruction, we remove it here. We shouldn't convert potentially
 * 2addr-eligible opcodes to that form here because they ultimately may need
 * the larger non-2addr encoding if their assigned vregs are larger than 4
 * bits. They will be handled in the post-regalloc instruction selection phase.
 *
 * Return a bool indicating whether any coalescing was done.
 *
 * This is fairly similar to the implementation in [Briggs92] section 8.6.
 */
bool Allocator::coalesce(interference::Graph* ig, cfg::ControlFlowGraph& cfg) {
  // XXX We could use something more compact than an unordered_map?
  using Rank = UnorderedMap<reg_t, size_t>;
  using Parent = UnorderedMap<reg_t, reg_t>;
  using RankPMap = boost::associative_property_map<Rank>;
  using ParentPMap = boost::associative_property_map<Parent>;
  using RegisterAliasSets = boost::disjoint_sets<RankPMap, ParentPMap>;

  // Every time we coalesce a pair of symregs, we put them into the same
  // union-find tree. At the end of the coalescing process, we will map all the
  // symregs in each set to the root of that tree.
  Rank rank_map;
  Parent parent_map;
  RegisterAliasSets aliases((RankPMap(rank_map)), (ParentPMap(parent_map)));
  for (reg_t i = 0; i < cfg.get_registers_size(); ++i) {
    aliases.make_set(i);
  }

  auto ii = InstructionIterable(cfg);
  auto old_coalesce_count = m_stats.moves_coalesced;
  cfg::CFGMutation m(cfg);
  bool any_linked{false};
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    auto* insn = it->insn;
    auto op = insn->opcode();
    if (!opcode::is_a_move(op) && !has_2addr_form(op) &&
        op != OPCODE_CHECK_CAST) {
      continue;
    }
    reg_t dest;
    if (insn->has_move_result_pseudo()) {
      auto move_result = cfg.move_result_of(it);
      always_assert(!move_result.is_end());
      dest = move_result->insn->dest();
    } else {
      dest = insn->dest();
    }
    dest = aliases.find_set(dest);
    auto src = aliases.find_set(insn->src(0));
    if (dest == src) {
      if (opcode::is_a_move(op)) {
        ++m_stats.moves_coalesced;
        m.remove(it);
      }
    } else if (ig->is_coalesceable(dest, src)) {
      // This unifies the two trees represented by dest and src
      aliases.link(dest, src);
      any_linked = true;
      // Since link() doesn't tell us whether dest or src is the root of the
      // newly merged trees, we have to use find_set() to figure that out.
      auto parent = dest;
      auto child = src;
      if (aliases.find_set(dest) != dest) {
        std::swap(parent, child);
      }
      // Merge the child's node into the parent's
      ig->combine(parent, child);
      TRACE(REG, 7, "Coalescing v%u and v%u because of %s", parent, child,
            SHOW(insn));
      if (opcode::is_a_move(op)) {
        ++m_stats.moves_coalesced;
        m.remove(it);
      }
    }
  }

  m.flush();

  if (any_linked) {
    transform::RegMap reg_map;
    for (reg_t i = 0; i < cfg.get_registers_size(); ++i) {
      reg_map.emplace(i, aliases.find_set(i));
    }
    transform::remap_registers(cfg, reg_map);
  }

  return m_stats.moves_coalesced != old_coalesce_count;
}

/*
 * Simplify the graph: remove nodes of low weight repeatedly until none are
 * left, then remove nodes of high weight (which will hopefully create more
 * nodes of low weight).
 *
 * Nodes that are used by load-param or range opcodes are ignored.
 *
 * Nodes that aren't constrained to < 16 bits are partitioned into a separate
 * stack so they can be colored later.
 *
 * This is fairly similar to section 8.8 in [Briggs92], except we are using
 * a weight as given by [Smith00] instead of just the node's degree.
 */
void Allocator::simplify(interference::Graph* ig,
                         std::stack<reg_t>* select_stack,
                         std::stack<reg_t>* spilled_select_stack) {
  // Nodes of low weight that we know are colorable. Note that even if all
  // the nodes in `low` have a max_vreg of 15, we can still have more than 16
  // of them here since some of them can have zero weight.
  std::set<reg_t> low;
  // Nodes that may not be colorable
  UnorderedSet<reg_t> high;

  for (auto&& [reg, node] : UnorderedIterable(ig->nodes())) {
    if (!node.is_active() || node.is_param() || node.is_range()) {
      continue;
    }
    if (node.definitely_colorable()) {
      low.emplace(reg);
    } else {
      high.emplace(reg);
    }
  }
  while (true) {
    while (!low.empty()) {
      auto reg = *low.begin();
      const auto& node = ig->get_node(reg);
      TRACE(REG, 6, "Removing %u", reg);
      if (node.max_vreg() < max_unsigned_value(16)) {
        select_stack->push(reg);
      } else {
        spilled_select_stack->push(reg);
      }
      ig->remove_node(reg);
      low.erase(reg);
      for (auto adj : node.adjacent()) {
        const auto& adj_node = ig->get_node(adj);
        if (!adj_node.is_active() || adj_node.is_param() ||
            adj_node.is_range()) {
          continue;
        }
        if (adj_node.definitely_colorable()) {
          low.emplace(adj);
          high.erase(adj);
        }
      }
    }
    if (high.empty()) {
      break;
    }
    // When picking the spill candidate, always prefer yet-unspilled nodes to
    // already-spilled ones. Spilling the same node twice won't make the graph
    // any easier to color.
    // In case of a tie, pick the node with the lowest ratio of
    // spill_cost / weight. For example, if we had to pick spill candidates in
    // the following code:
    //
    //   sget v0 LFoo;.a:LFoo;
    //   iget v2 v0 LFoo;.a:LBar;
    //   iget v3 v0 LFoo;.a:LBaz;
    //   iget v4 v0 LFoo;.a:LQux;
    //   sget v1 LFoo;.b:LFoo;
    //   iput v2 v1 LFoo;.a:LBar;
    //   iput v3 v1 LFoo;.a:LBaz;
    //   iput v4 v1 LFoo;.a:LQux;
    //
    // It would be preferable to spill v0 and v1 last because they have many
    // uses (high spill cost), and interfere with fewer live ranges (have lower
    // weight) compared to v2 and v3 (tying with v4, but v4 still has a lower
    // spill cost).
    auto spill_candidate_it =
        unordered_min_element(high, [ig](reg_t a, reg_t b) {
          const auto& node_a = ig->get_node(a);
          const auto& node_b = ig->get_node(b);
          if (node_a.is_spilt() != node_b.is_spilt()) {
            return !node_a.is_spilt() && node_b.is_spilt();
          }
          // Note that a / b < c / d <=> a * d < c * b.
          auto a_value = node_a.spill_cost() * node_b.weight();
          auto b_value = node_b.spill_cost() * node_a.weight();
          if (a_value != b_value) {
            return a_value < b_value;
          }
          // Among equivalent options, prefer lowest register number as tie
          // breaker.
          return a < b;
        });
    TRACE(REG, 6, "Potentially spilling %u", *spill_candidate_it);
    // Our spill candidate has too many neighbors for us to be certain that we
    // can color it. Instead of spilling it immediately, we put it into `low`,
    // which will ensure that it ends up on the stack before any of the
    // neighbors that cause it to have a high weight. Then when we're running
    // select(), by the time we re-encounter this node, we've colored all those
    // neighbors. If some of those neighbors share the same colors, we may be
    // able to color this node despite its weight. Briggs calls this
    // "optimistic coloring".
    low.emplace(*spill_candidate_it);
    high.erase(*spill_candidate_it);
  }
}

/*
 * Assign virtual registers to our symbolic registers, spilling where
 * necessary.
 *
 * Range- and param-related symregs are not handled here.
 */
void Allocator::select(const cfg::ControlFlowGraph& /*cfg*/,
                       const interference::Graph& ig,
                       std::stack<reg_t>* select_stack,
                       RegisterTransform* reg_transform,
                       SpillPlan* spill_plan) {
  vreg_t vregs_size = reg_transform->size;
  while (!select_stack->empty()) {
    auto reg = select_stack->top();
    select_stack->pop();
    const auto& node = ig.get_node(reg);
    VirtualRegistersFile vreg_file;
    mark_adjacent(ig, reg, reg_transform->map, &vreg_file);
    auto vreg = vreg_file.alloc(node.width());
    if (vreg <= node.max_vreg()) {
      reg_transform->map.emplace(reg, vreg);
      // A spilled register is never mapped, so its failed slot must not size
      // the frame: that would push the parameter window up and can spill a
      // parameter that fits.
      vregs_size = std::max(vregs_size, vreg_file.size());
    } else {
      spill_plan->global_spills.emplace(reg, vreg);
    }
  }
  reg_transform->size = vregs_size;
}

/*
 * Assign virtual registers to our symbolic range-related registers, spilling
 * where necessary. We try to align the various ranges to minimize spillage.
 *
 * Since range instructions can address operands of any size, we run this after
 * allocating non-range-related nodes, so that the non-range ones have priority
 * in consuming the low vregs.
 */
void Allocator::select_ranges(const cfg::ControlFlowGraph& /*cfg*/,
                              const interference::Graph& ig,
                              const RangeSet& range_set,
                              RegisterTransform* reg_transform,
                              SpillPlan* spill_plan) {
  for (auto* insn : range_set) {
    TRACE(REG, 5, "Allocating %s as range kind", SHOW(insn));
    UnorderedMap<reg_t, VirtualRegistersFile> vreg_files;
    for (size_t i = 0; i < insn->srcs_size(); ++i) {
      auto src = insn->src(i);
      VirtualRegistersFile& vreg_file = vreg_files[src];
      mark_adjacent(ig, src, reg_transform->map, &vreg_file);
    }

    vreg_t range_base =
        find_best_range_fit(ig, insn->srcs(), 0, reg_transform->size,
                            vreg_files, reg_transform->map);
    fit_range_instruction(ig, insn, range_base, vreg_files, reg_transform,
                          spill_plan);
  }
}

/*
 * Assign virtual registers to our symbolic param-related registers, spilling
 * where necessary.
 */
void Allocator::select_params(const cfg::ControlFlowGraph& cfg,
                              const interference::Graph& ig,
                              RegisterTransform* reg_transform,
                              SpillPlan* spill_plan) {
  UnorderedMap<reg_t, VirtualRegistersFile> vreg_files;
  std::vector<reg_t> param_regs;
  auto param_insns = cfg.get_param_instructions();
  size_t params_size{0};
  for (auto& mie : InstructionIterable(param_insns)) {
    auto dest = mie.insn->dest();
    const auto& node = ig.get_node(dest);
    params_size += node.width();
    param_regs.emplace_back(dest);
    VirtualRegistersFile& vreg_file = vreg_files[dest];
    mark_adjacent(ig, dest, reg_transform->map, &vreg_file);
  }

  auto min_param_reg =
      reg_transform->size < params_size ? 0 : reg_transform->size - params_size;
  auto params_base = find_best_range_fit(
      ig, IRInstruction::reg_range(param_regs), min_param_reg,
      reg_transform->size, vreg_files, reg_transform->map);
  fit_params(ig, param_insns, params_base, vreg_files, reg_transform,
             spill_plan);
}

// Find out if there exist a
//    invoke-xxx/fill-new-array v
//    move-result u
// if this exist then we can't split v around u, since splitting v around u
// will result in inserting move in between. Return true if there exist
// this situation for register u and v, false otherwise.
bool bad_move_result(reg_t u, reg_t v, const SplitCosts& split_costs) {
  for (auto* mei : UnorderedIterable(split_costs.get_write_result(u))) {
    auto* write_result_insn = mei->insn;
    for (size_t i = 0; i < write_result_insn->srcs_size(); ++i) {
      if (write_result_insn->src(i) == v) {
        return true;
      }
    }
  }
  return false;
}

// if reg was dead on the edge of try block to catch block,
// all the try block to this catch block should has reg died on their edge,
// otherwise avoid to split it. Return true if we should avoid split it,
// return false otherwise.
bool bad_catch(reg_t reg, const SplitCosts& split_costs) {
  const auto& death_at_catch = split_costs.death_at_catch(reg);
  for (auto pair : UnorderedIterable(death_at_catch)) {
    if (pair.first->preds().size() != pair.second) {
      return true;
    }
  }
  return false;
}

/*
 * Finding corresponding register that elements in spill_plan can split around
 * or be split around.
 */
void Allocator::find_split(const interference::Graph& ig,
                           const SplitCosts& split_costs,
                           RegisterTransform* reg_transform,
                           SpillPlan* spill_plan,
                           SplitPlan* split_plan) {
  UnorderedSet<reg_t> to_erase_spill;
  auto& reg_map = reg_transform->map;
  // Find best split/spill plan for all the global spill plan.
  auto global_spills_ui = UnorderedIterable(spill_plan->global_spills);
  auto spill_it = global_spills_ui.begin();
  while (spill_it != global_spills_ui.end()) {
    auto reg = spill_it->first;
    size_t best_cost = static_cast<size_t>(ig.get_node(reg).spill_cost());
    if (best_cost == 0) {
      ++spill_it;
      continue;
    }
    vreg_t best_vreg = 0;
    bool split_found = false;
    bool split_around_name = false;
    // Find all the vregs assigned to reg's neighbors.
    // Key is vreg, value is a set of registers that are mapped to this vreg.
    UnorderedMap<vreg_t, UnorderedSet<vreg_t>> mapped_neighbors;
    const auto& node = ig.get_node(reg);
    for (auto adj : node.adjacent()) {
      auto it = reg_map.find(adj);
      if (it != reg_map.end()) {
        mapped_neighbors[it->second].emplace(adj);
      }
    }
    auto max_reg_bound = ig.get_node(reg).max_vreg();
    // For each vreg(color).
    for (const auto& vreg_assigned : UnorderedIterable(mapped_neighbors)) {
      // We only want to check neighbors that has vreg assigned that
      // can be used by the reg.
      if (vreg_assigned.first > max_reg_bound) {
        continue;
      }

      // Try to split vreg around reg.
      bool split_OK = true;
      size_t cost = 0;
      for (auto neighbor : UnorderedIterable(vreg_assigned.second)) {
        if (bad_move_result(reg, neighbor, split_costs) ||
            ig.has_containment_edge(neighbor, reg)) {
          split_OK = false;
          break;
        } else {
          cost += split_costs.total_value_at(reg);
        }
      }
      if (split_OK && cost < best_cost) {
        if (!bad_catch(reg, split_costs)) {
          best_cost = cost;
          best_vreg = vreg_assigned.first;
          split_around_name = true;
          split_found = true;
        }
      }

      // Try to split reg around vreg.
      split_OK = true;
      cost = 0;
      for (auto neighbor : UnorderedIterable(vreg_assigned.second)) {
        if (bad_move_result(neighbor, reg, split_costs) ||
            ig.has_containment_edge(reg, neighbor)) {
          split_OK = false;
          break;
        } else {
          if (bad_catch(neighbor, split_costs)) {
            split_OK = false;
            break;
          }
          cost += split_costs.total_value_at(neighbor);
        }
      }
      if (split_OK && cost < best_cost) {
        best_cost = cost;
        best_vreg = vreg_assigned.first;
        split_around_name = false;
        split_found = true;
      }
    }

    if (split_found) {
      reg_map.emplace(reg, best_vreg);
      auto neighbors = mapped_neighbors.at(best_vreg);
      if (split_around_name) {
        for (auto neighbor : UnorderedIterable(neighbors)) {
          split_plan->split_around[reg].emplace(neighbor);
        }
      } else {
        for (auto neighbor : UnorderedIterable(neighbors)) {
          split_plan->split_around[neighbor].emplace(reg);
        }
      }
      spill_it = global_spills_ui.erase(spill_it);
    } else {
      ++spill_it;
    }
  }
}

UnorderedMap<reg_t, cfg::InstructionIterator> Allocator::find_param_splits(
    const UnorderedSet<reg_t>& orig_params, cfg::ControlFlowGraph& cfg) {
  UnorderedMap<reg_t, cfg::InstructionIterator> load_locations;
  if (orig_params.empty()) {
    return load_locations;
  }
  // Erase parameter from list if there exist instructions overwriting the
  // symreg.
  cfg::Block* first_block_with_insns = cfg.get_first_block_with_insns();
  auto pend = first_block_with_insns->get_first_non_param_loading_insn();
  UnorderedSet<reg_t> params = orig_params;
  auto ii = InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    auto* insn = it->insn;
    if (opcode::is_a_load_param(insn->opcode())) {
      continue;
    }
    if (insn->has_dest()) {
      auto dest = insn->dest();
      if (params.find(dest) != params.end()) {
        params.erase(dest);
        auto emplaced =
            load_locations
                .emplace(
                    dest,
                    first_block_with_insns->to_cfg_instruction_iterator(pend))
                .second;
        always_assert(emplaced);
        ++m_stats.params_spill_early;
      }
    }
  }
  if (params.empty()) {
    return load_locations;
  }

  cfg::Block* start_block = cfg.entry_block();
  auto doms = dominators::SimpleFastDominators<cfg::GraphInterface>(cfg);
  for (auto param : UnorderedIterable(params)) {
    auto block_uses = find_first_uses(param, start_block);
    // Since this function only gets called for param regs that need to be
    // spilled, they must be constrained by at least one use.
    always_assert(!block_uses.empty());
    if (block_uses.size() > 1) {
      // There are multiple use sites for this param register.
      // Find the immediate dominator of the blocks that contain those uses and
      // insert a load at its end.
      cfg::Block* idom = block_uses[0];
      for (size_t index = 1; index < block_uses.size(); ++index) {
        idom = doms.intersect(idom, block_uses[index]);
      }
      TRACE(REG, 5, "Inserting param load of v%u in B%zu", param, idom->id());
      // Record the param reload at the end of the immediate dominator, but
      // never past a terminator -- appending after one is illegal (asserts in
      // ControlFlowGraph::insert). Leaving `insn_it` pointing AT the
      // instruction makes split_params insert the load before it, the correct
      // dominating spot. An instruction that transfers control via a throw
      // (EDGE_THROW) edge -- a `throw`, or any `may_throw` insn -- can reach
      // catch-handler blocks that hold the param's uses, so the load must
      // precede it too. (This is why a throw block can legitimately be the idom
      // here: a try-region body whose param is used in its own catch handlers.)
      auto insn_it = idom->get_last_insn();
      if (insn_it != idom->end()) {
        auto last_op = insn_it->insn->opcode();
        // A `return` block has no real successors (only a ghost edge to the
        // synthetic exit), so it can never be the immediate dominator of the
        // >1 distinct use blocks this branch handles (find_first_uses dedups
        // blocks). Assert the invariant rather than silently guarding it: if it
        // ever fires, the CFG is malformed and a load placed here would not
        // dominate the uses.
        always_assert_log(!opcode::is_a_return(last_op),
                          "param-split idom B%zu of v%u ends in return",
                          idom->id(), param);
        // Advance past the last instruction only when appending after it is
        // safe -- not a terminator (`opcode::is_terminal`: branch/throw; return
        // is excluded by the assert above) and not a `may_throw` insn (see the
        // throw-edge note above).
        if (!opcode::is_terminal(last_op) && !opcode::may_throw(last_op)) {
          ++insn_it;
          always_assert(insn_it == idom->end());
        }
      }
      auto emplaced =
          load_locations
              .emplace(param, idom->to_cfg_instruction_iterator(insn_it))
              .second;
      always_assert(emplaced);
    } else {
      TRACE(REG, 5, "Inserting param load of v%u in B%zu", param,
            block_uses[0]->id());
      auto first_use_it = find_first_use_in_block(param, block_uses[0]);
      auto emplaced =
          load_locations
              .emplace(param,
                       block_uses[0]->to_cfg_instruction_iterator(first_use_it))
              .second;
      always_assert(emplaced);
    }
  }
  return load_locations;
}

/*
 * Split param-related live ranges. Since parameters must be at the end of the
 * register frame, but don't have any register-size limitations, we get good
 * results by splitting their live ranges -- the instructions that use the
 * parameter values are typically constrained to smaller registers.
 *
 * If the load-param opcode is the only one that has a def of that live range,
 * then we insert a load at the immediate dominator of all the uses of that
 * live range. This shortens the remaining live range.
 *
 * If there are other instructions that define that range, the analysis is a
 * bit more complicated, so we just insert a load at the start of the method.
 */
void Allocator::split_params(const interference::Graph& ig,
                             const UnorderedSet<reg_t>& param_spills,
                             cfg::ControlFlowGraph& cfg) {
  auto load_locations = find_param_splits(param_spills, cfg);
  if (load_locations.empty()) {
    return;
  }

  // Remap each load-param's dest to a fresh temp and emit its reload, walking
  // the load-param instructions in order.
  //
  // Several params routinely share one insertion point: every param overwritten
  // by a later instruction is recorded at the same `pend` in find_param_splits,
  // and params can also share an idom end or a first use. At a shared point,
  // whichever move is inserted first ends up first, so this walk decides the
  // emitted instruction order. The moves are mutually independent -- each dest
  // is a distinct param and each src a freshly allocated temp, so no move's src
  // is another's dest -- hence any fixed order is semantically equivalent, and
  // the load-param sequence is a deterministic one.
  //
  // The `pend` reloads land at the end boundary of the very range being walked,
  // so a move inserted here is visited by this loop. Its dest is the param
  // symreg, still a key in load_locations, so without the load-param guard it
  // would be remapped as if it were a param and emit another move, forever.
  auto params = cfg.get_param_instructions();
  auto param_insns = InstructionIterable(params);
  size_t emitted = 0;
  for (auto& mie : param_insns) {
    auto* insn = mie.insn;
    if (!opcode::is_a_load_param(insn->opcode())) {
      continue;
    }
    auto dest = insn->dest();
    auto it = load_locations.find(dest);
    if (it == load_locations.end()) {
      continue;
    }
    auto temp = cfg.allocate_temp();
    insn->set_dest(temp);
    cfg.insert_before(it->second,
                      gen_move(ig.get_node(dest).type(), dest, temp));
    ++m_stats.param_spill_moves;
    ++emitted;
  }
  // Every split's param is a load-param dest.
  always_assert(emitted == load_locations.size());
}

/*
 * Insert loads before every use of a globally spilled symreg, and stores
 * after a def.
 *
 * In order to minimize the number of spills, range-related symregs are spilled
 * by inserting loads just before the range instruction. Other instructions
 * that use those symregs will not be affected. This changes one range-related
 * symreg into one range-related and one normal one; if the normal symreg still
 * can't be allocated, it will get globally spilled on the next iteration of
 * the allocation loop.
 *
 * Param-related symregs are spilled by inserting loads just after the
 * block of parameter instructions.
 */
void Allocator::spill(const interference::Graph& ig,
                      const SpillPlan& spill_plan,
                      const RangeSet& range_set,
                      cfg::ControlFlowGraph& cfg) {
  // TODO: account for "close" defs and uses. See [Briggs92], section 8.7
  cfg::CFGMutation m(cfg);
  auto ii = cfg::InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); ++it) {
    auto* insn = it->insn;
    if (range_set.contains(insn)) {
      // Spill range symregs
      auto to_spill_it = spill_plan.range_spills.find(insn);
      if (to_spill_it != spill_plan.range_spills.end()) {
        const auto& to_spill = to_spill_it->second;
        for (auto idx : to_spill) {
          auto src = insn->src(idx);
          const auto& node = ig.get_node(src);
          auto temp = cfg.allocate_temp();
          insn->set_src(idx, temp);
          auto* mov = gen_move(node.type(), temp, src);
          m.insert_before(it, {mov});
          ++m_stats.range_spill_moves;
        }
      }
    } else {
      // Spill non-param, non-range symregs.
      // We do not need to worry about handling any new symregs introduced in
      // range/param splitting -- they will never appear in the global_spills
      // map.
      for (size_t i = 0; i < insn->srcs_size(); ++i) {
        auto src = insn->src(i);
        auto sp_it = spill_plan.global_spills.find(src);
        if (sp_it == spill_plan.global_spills.end()) {
          continue;
        }
        const auto& node = ig.get_node(src);
        auto max_value = max_value_for_src(insn, i, node.width() == 2);
        if (sp_it->second > max_value) {
          auto temp = cfg.allocate_temp();
          insn->set_src(i, temp);
          auto* mov = gen_move(node.type(), temp, src);
          m.insert_before(it, {mov});
          ++m_stats.global_spill_moves;
        }
      }
      if (insn->has_dest()) {
        auto dest = insn->dest();
        auto sp_it = spill_plan.global_spills.find(dest);
        if (sp_it != spill_plan.global_spills.end() &&
            sp_it->second > max_unsigned_value(dest_bit_width(it))) {
          auto temp = cfg.allocate_temp();
          insn->set_dest(temp);
          m.insert_after(it, {gen_move(ig.get_node(dest).type(), dest, temp)});
          ++m_stats.global_spill_moves;
        }
      }
    }
  }
  m.flush();
}

/*
 * Ensure that we have a symreg dedicated to holding the `this` pointer
 * throughout the entire method. If there is another instruction that writes to
 * the same live range, we split the `this` parameter into a separate one by
 * inserting a move instruction at the start of the method. For example, this
 * code:
 *
 *   load-param-object v0
 *   if-eqz ... :true-label
 *   sget-object v0 LFoo;
 *   :true-label
 *   return-object v0
 *
 * Becomes this:
 *
 *   load-param-object v1
 *   move-object v0 v1
 *   if-eqz ... :true-label
 *   sget-object v0 LFoo;
 *   :true-label
 *   return-object v0
 */
static void dedicate_this_register(cfg::ControlFlowGraph& cfg, bool is_static) {
  always_assert(!is_static);
  auto* this_insn = cfg.get_first_param_instruction();

  bool this_needs_split{false};
  for (const auto& mie : InstructionIterable(cfg)) {
    auto* insn = mie.insn;
    if (insn->has_dest() && insn->dest() == this_insn->dest() &&
        insn != this_insn) {
      this_needs_split = true;
      break;
    }
  }

  if (this_needs_split) {
    auto old_reg = this_insn->dest();
    this_insn->set_dest(cfg.allocate_temp());
    cfg::Block* first_block_with_insns = cfg.get_first_block_with_insns();
    auto insert_it = first_block_with_insns->get_first_non_param_loading_insn();
    cfg.insert_before(
        first_block_with_insns->to_cfg_instruction_iterator(insert_it),
        (new IRInstruction(OPCODE_MOVE_OBJECT))
            ->set_dest(old_reg)
            ->set_src(0, this_insn->dest()));
  }
}

/*
 * Main differences from the standard Chaitin-Briggs
 * build-coalesce-simplify-spill loop:
 *
 *   * We only coalesce the first time around, because our move instructions
 *     and our spill / reload instructions are one and the same. This is
 *     easily fixable, though I have yet to profile the performance tradeoff.
 *     We also don't rebuild the interference graph after coalescing; I'd
 *     like to do some performance work before enabling that.
 *
 *   * We have to handle range instructions and have the parameter vregs
 *     at the end of the frame, which the original algorithm doesn't quite
 *     account for. These are handled in select_ranges and select_params
 *     respectively.
 */
void Allocator::allocate(cfg::ControlFlowGraph& cfg, bool is_static) {
  // Any temp larger than this is the result of the spilling process
  auto initial_regs = cfg.get_registers_size();

  // The set of instructions that will be encoded in range form. This is a
  // monotonically increasing set, i.e. we only add and never remove from it
  // in the allocation loop below.
  auto range_set = init_range_set(cfg);
  range_set.prioritize();

  bool no_overwrite_this = m_config.no_overwrite_this && !is_static;
  if (no_overwrite_this) {
    dedicate_this_register(cfg, is_static);
  }
  bool first{true};
  while (true) {
    SplitCosts split_costs;
    SpillPlan spill_plan;
    SplitPlan split_plan;
    RegisterTransform reg_transform;

    cfg.calculate_exit_block();
    auto fixpoint_iter = std::make_unique<LivenessFixpointIterator>(cfg);
    fixpoint_iter->run(LivenessDomain());

    TRACE(REG, 5, "Allocating:\n%s", ::SHOW(cfg));
    auto ig = interference::build_graph(
        *fixpoint_iter, cfg, initial_regs, range_set,
        /* containment_edges */ m_config.use_splitting);

    // Make the `this` symreg conflict with every other one so that it never
    // gets overwritten in the method. See check_no_overwrite_this in
    // IRTypeChecker.h for the rationale.
    if (no_overwrite_this) {
      auto* this_insn = cfg.get_first_param_instruction();
      for (const auto& pair : UnorderedIterable(ig.nodes())) {
        ig.add_edge(this_insn->dest(), pair.first);
      }
    }

    TRACE(REG, 7, "IG:\n%s", SHOW(ig));
    if (first) {
      coalesce(&ig, cfg);
      first = false;
      // After coalesce the live_out and live_in of blocks may change, so run
      // LivenessFixpointIterator again.
      if (m_config.use_splitting) {
        fixpoint_iter->run(LivenessDomain());
      } else {
        fixpoint_iter = nullptr;
      }
      TRACE(REG, 5, "Post-coalesce:\n%s", ::SHOW(cfg));
    } else {
      // TODO we should coalesce here too, but we'll need to avoid removing
      // moves that were inserted by spilling

      // If we've hit this many iterations, it's very likely that we've hit
      // some bug that's causing us to loop infinitely.
      always_assert(m_stats.reiteration_count++ < 1000);
    }
    TRACE(REG, 7, "IG:\n%s", SHOW(ig));

    std::stack<reg_t> select_stack;
    std::stack<reg_t> spilled_select_stack;
    simplify(&ig, &select_stack, &spilled_select_stack);
    select(cfg, ig, &select_stack, &reg_transform, &spill_plan);

    TRACE(REG, 5, "Transform before range alloc:\n%s", SHOW(reg_transform));
    select_ranges(cfg, ig, range_set, &reg_transform, &spill_plan);
    // Select registers for symregs that can be addressed using all 16 bits.
    // These symregs are typically generated during the spilling and splitting
    // steps. We want to process them after the range-related symregs because
    // range-related symregs may also be constrained to use less than 16 bits.
    // Basically, the registers in `spilled_select_stack` are in the least
    // constrained category of registers, so it makes sense to allocate them
    // last.
    select(cfg, ig, &spilled_select_stack, &reg_transform, &spill_plan);
    select_params(cfg, ig, &reg_transform, &spill_plan);
    TRACE(REG, 5, "Transform after range alloc:\n%s", SHOW(reg_transform));

    if (!spill_plan.empty()) {
      TRACE(REG, 5, "Spill plan:\n%s", SHOW(spill_plan));
      if (m_config.use_splitting) {
        // TODO (T124893789): Live-range-splitting is known to be broken.
        fprintf(stderr,
                "WARNING: Live-range-splitting is known to be broken.\n");
        calc_split_costs(*fixpoint_iter, cfg, &split_costs);
        find_split(ig, split_costs, &reg_transform, &spill_plan, &split_plan);
      }
      split_params(ig, spill_plan.param_spills, cfg);
      spill(ig, spill_plan, range_set, cfg);

      if (!split_plan.split_around.empty()) {
        always_assert(m_config.use_splitting);
        TRACE(REG, 5, "Split plan:\n%s", SHOW(split_plan));
        m_stats.split_moves +=
            split(*fixpoint_iter, split_plan, split_costs, ig, cfg);
      }
    } else {
      transform::remap_registers(cfg, reg_transform.map);
      cfg.set_registers_size(reg_transform.size);
      break;
    }
  }

  TRACE(REG, 3, "Reiteration count: %zu", m_stats.reiteration_count);
  TRACE(REG, 3, "Spill count: %zu", m_stats.moves_inserted());
  TRACE(REG, 3, "  Param spills: %zu", m_stats.param_spill_moves);
  TRACE(REG, 3, "  Range spills: %zu", m_stats.range_spill_moves);
  TRACE(REG, 3, "  Global spills: %zu", m_stats.global_spill_moves);
  TRACE(REG, 3, "  splits: %zu", m_stats.split_moves);
  TRACE(REG, 3, "Coalesce count: %zu", m_stats.moves_coalesced);
  TRACE(REG, 3, "Params spilled too early: %zu", m_stats.params_spill_early);
  TRACE(REG, 3, "Net moves: %zu", m_stats.net_moves());
}

} // namespace graph_coloring

} // namespace regalloc
