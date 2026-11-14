/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "CFGInliner.h"

#include <memory>
#include <optional>

#include "Debug.h"
#include "DexPosition.h"
#include "IRList.h"
#include "IROpcode.h"
#include "Resolver.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "Trace.h"

namespace cfg {

const DexString* get_partial_inline_source() {
  return DexString::make_string("PartiallyInlinedSource");
}

// TODO:
//  * should this really be a friend class to ControlFlowGraph, Block, and Edge?

/*
 * Copy callee's blocks into caller
 */
void CFGInliner::inline_cfg(ControlFlowGraph* caller,
                            const InstructionIterator& callsite,
                            const DexType* needs_receiver_cast,
                            const DexType* needs_init_class,
                            const ControlFlowGraph& callee_orig,
                            size_t next_caller_reg,
                            DexMethod* rewrite_invoke_super_callee,
                            bool needs_constructor_fence) {
  CFGInlinerPlugin base_plugin;
  inline_cfg(caller, callsite, needs_receiver_cast, needs_init_class,
             callee_orig, next_caller_reg, base_plugin,
             rewrite_invoke_super_callee, needs_constructor_fence);
}

namespace {

void normalize_source_blocks(const InstructionIterator& inline_site,
                             ControlFlowGraph& callee_cfg) {
  auto* caller_block = inline_site.block();
  auto* caller_sb = source_blocks::get_last_source_block_before(
      caller_block, inline_site.unwrap());
  source_blocks::normalize::normalize(
      callee_cfg, caller_sb,
      source_blocks::normalize::num_interactions(callee_cfg, caller_sb));
}

void remove_dangling_partial_inline_dex_positions(
    const std::map<BlockId, Block*>& blocks) {
  const auto* partial_inline_source = get_partial_inline_source();

  for (const auto& entry : blocks) {
    Block* b = entry.second;
    auto it = b->begin();
    while (it != b->end()) {
      auto& mie = *it;
      if (mie.type == MFLOW_POSITION &&
          mie.pos->file == partial_inline_source) {
        TRACE(CFG, 1, "Found would-be-dangling partial-inline dex position!");
        it = b->remove_mie(it);
        continue;
      }
      ++it;
    }
  }
}

} // namespace

void CFGInliner::inline_cfg(ControlFlowGraph* caller,
                            InstructionIterator inline_site,
                            const DexType* needs_receiver_cast,
                            const DexType* needs_init_class,
                            const ControlFlowGraph& callee_orig,
                            size_t next_caller_reg,
                            CFGInlinerPlugin& plugin,
                            DexMethod* rewrite_invoke_super_callee,
                            bool needs_constructor_fence) {
  always_assert(&inline_site.cfg() == caller);

  // copy the callee because we're going to move its contents into the caller
  ControlFlowGraph callee;
  callee_orig.deep_copy(&callee);
  remove_ghost_exit_block(&callee);
  if (rewrite_invoke_super_callee != nullptr) {
    rewrite_invoke_supers(&callee, rewrite_invoke_super_callee);
  }

  normalize_source_blocks(inline_site, callee);

  cleanup_callee_debug(&callee);
  if ((needs_receiver_cast != nullptr) || (needs_init_class != nullptr)) {
    std::vector<IRInstruction*> new_insns;
    if (needs_receiver_cast != nullptr) {
      always_assert(!needs_init_class);
      auto param_insns = callee.get_param_instructions();
      auto* first_load_param_insn = param_insns.front().insn;
      auto first_param_reg = first_load_param_insn->dest();
      auto* check_cast_insn = (new IRInstruction(OPCODE_CHECK_CAST))
                                  ->set_type(needs_receiver_cast)
                                  ->set_src(0, first_param_reg);
      auto* move_result_insn =
          (new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT))
              ->set_dest(first_param_reg);
      new_insns.push_back(check_cast_insn);
      new_insns.push_back(move_result_insn);
    } else {
      always_assert(needs_init_class);
      auto* init_class_insn =
          (new IRInstruction(IOPCODE_INIT_CLASS))->set_type(needs_init_class);
      new_insns.push_back(init_class_insn);
    }
    auto* entry_block = callee.entry_block();
    auto last_param_insn_it = entry_block->get_last_param_loading_insn();
    if (last_param_insn_it == entry_block->end()) {
      entry_block->push_front(new_insns);
    } else {
      callee.insert_after(
          entry_block->to_cfg_instruction_iterator(last_param_insn_it),
          new_insns);
    }
  }

  TRACE(CFG, 3, "caller %s", SHOW(*caller));
  TRACE(CFG, 3, "callee %s", SHOW(callee));

  if (caller->get_succ_edge_of_type(inline_site.block(), EDGE_THROW) !=
      nullptr) {
    split_on_callee_throws(&callee);
  }

  // we save these blocks here because we're going to empty out the callee CFG
  const auto& callee_entry_block = callee.entry_block();
  const auto& callee_return_blocks = callee.return_blocks();

  bool inline_after = plugin.inline_after();

  // Find the closest dbg position for the inline site, if split before
  DexPosition* inline_site_dbg_pos =
      inline_after ? nullptr : inline_site.cfg().get_dbg_pos(inline_site);

  if (plugin.update_before_reg_remap(caller, &callee)) {
    next_caller_reg = caller->get_registers_size();
  }

  // make the invoke last of its block or first based on inline_after
  auto split = inline_after ? maybe_split_block(caller, inline_site)
                            : maybe_split_block_before(caller, inline_site);
  Block* split_on_inline = split.first;
  Block* callsite_blk = split.second;
  TRACE(CFG, 3, "split caller %s : %s", inline_after ? "after" : "before",
        SHOW(*caller));

  // Find the closest dbg position for the inline site, if split after
  inline_site_dbg_pos = inline_after
                            ? inline_site.cfg().get_dbg_pos(inline_site)
                            : inline_site_dbg_pos;

  if (inline_site_dbg_pos != nullptr) {
    set_dbg_pos_parents(&callee, inline_site_dbg_pos);
    // ensure that the caller's code after the inlined method retain their
    // original position
    const auto& first = split_on_inline->begin();
    // inserting debug insn before param load insn does not work
    if (split_on_inline != inline_site.cfg().entry_block() &&
        (first == split_on_inline->end() || first->type != MFLOW_POSITION)) {
      // but don't add if there's already a position at the front of this
      // block
      split_on_inline->m_entries.push_front(*(new MethodItemEntry(
          std::make_unique<DexPosition>(*inline_site_dbg_pos))));
    }
  } else {
    remove_dangling_partial_inline_dex_positions(callee.m_blocks);
  }

  // make sure the callee's registers don't overlap with the caller's
  auto callee_regs_size = callee.get_registers_size();
  auto old_caller_regs_size = caller->get_registers_size();
  always_assert(next_caller_reg <= old_caller_regs_size);
  remap_registers(&callee, static_cast<reg_t>(next_caller_reg));

  auto alt_srcs = plugin.inline_srcs();
  move_arg_regs(&callee, alt_srcs ? *alt_srcs : inline_site->insn->srcs_copy());

  auto return_reg = plugin.reg_for_return();

  if (inline_site->insn->has_move_result_any()) {
    const cfg::InstructionIterator& move_res =
        caller->move_result_of(inline_site);
    return_reg = return_reg
                     ? return_reg
                     : (move_res.is_end()
                            ? std::nullopt
                            : std::optional<reg_t>{move_res->insn->dest()});
    // delete the move-result if there is one to remove, before connecting the
    // cfgs because it's in a block that may be merged into another
    if (plugin.remove_inline_site() && !move_res.is_end()) {
      caller->remove_insn(move_res);
    }
  }
  move_return_reg(&callee, return_reg);
  TRACE(CFG, 3, "callee after remap %s", SHOW(callee));

  bool need_reg_size_recompute = plugin.update_after_reg_remap(caller, &callee);
  // redirect to callee
  const std::vector<Block*> callee_blocks = callee.blocks();
  steal_contents(caller, callsite_blk, &callee);
  connect_cfgs(inline_after, caller, callsite_blk, callee_blocks,
               callee_entry_block, callee_return_blocks, split_on_inline,
               needs_constructor_fence);
  if (need_reg_size_recompute) {
    caller->recompute_registers_size();
  } else {
    size_t needed_caller_regs_size = next_caller_reg + callee_regs_size;
    if (needed_caller_regs_size > old_caller_regs_size) {
      caller->set_registers_size(static_cast<reg_t>(needed_caller_regs_size));
    }
  }

  TRACE(CFG, 3, "caller after connect %s", SHOW(*caller));

  if (plugin.remove_inline_site()) {
    // delete the invoke after connecting the CFGs because remove_insn will
    // remove the outgoing throw if we remove the callsite
    caller->remove_insn(inline_site);
  }

  if (ControlFlowGraph::s_DEBUG) {
    caller->sanity_check();
  }
  TRACE(CFG, 3, "final %s", SHOW(*caller));
}

void CFGInliner::cleanup_callee_debug(ControlFlowGraph* cfg) {
  UnorderedSet<reg_t> valid_regs;
  for (auto* block_it : cfg->order()) {
    block_it->cleanup_debug(valid_regs);
  }
}

void CFGInliner::remove_ghost_exit_block(ControlFlowGraph* cfg) {
  auto* exit_block = cfg->exit_block();
  if ((exit_block != nullptr) &&
      (cfg->get_pred_edge_of_type(exit_block, EDGE_GHOST) != nullptr)) {
    cfg->remove_block(exit_block);
    cfg->set_exit_block(nullptr);
  }
}

void CFGInliner::rewrite_invoke_supers(ControlFlowGraph* cfg,
                                       DexMethod* method) {
  for (auto& mie : cfg::InstructionIterable(*cfg)) {
    auto* insn = mie.insn;
    if (opcode::is_invoke_super(insn->opcode())) {
      auto* callee = resolve_invoke_method_deprecated(insn, method);
      always_assert(callee);
      // Illegal combination; someone needs to clean this up.
      insn->set_opcode(OPCODE_INVOKE_DIRECT);
      insn->set_method(callee);
    }
  }
}

/*
 * If it isn't already, make `it` the last instruction of its block
 * return the block that should be run after the callee and blk containing
 * callsite as a pair.
 */
std::pair<Block*, Block*> CFGInliner::maybe_split_block(
    ControlFlowGraph* caller, const InstructionIterator& it) {
  always_assert(!it.block()->empty());

  const IRList::iterator& raw_it = it.unwrap();
  Block* old_block = it.block();
  if (raw_it != old_block->get_last_insn()) {
    caller->split_block(it);
  }

  // The call is already the last instruction of the block.
  // No need to change the code, just return the next block
  Block* goto_block = old_block->goes_to();
  always_assert(goto_block != nullptr);
  return std::make_pair(goto_block, old_block);
}

// Insert a new block if needed to make `it` the first instruction of a block.
// return the block that should be run before the callee and the block that
// should contain the callsite as a pair.
std::pair<Block*, Block*> CFGInliner::maybe_split_block_before(
    ControlFlowGraph* caller, InstructionIterator& it) {
  always_assert(!it.block()->empty());

  const IRList::iterator& raw_it = it.unwrap();
  Block* old_block = it.block();
  auto preds = old_block->preds();
  if (raw_it == old_block->get_first_insn() && preds.size() == 1) {
    Block* single_pred_block = preds.at(0)->src();
    if (single_pred_block->succs().size() == 1) {
      // If we already have a block.
      return std::make_pair(single_pred_block, old_block);
    }
  }

  auto* insn = it->insn;
  // Inject an instruction and then split so 'it' is first of block
  auto* dummy_end_instruction = new IRInstruction(OPCODE_NOP);
  caller->insert_before(it, dummy_end_instruction);
  auto* new_blk = caller->split_block(
      old_block, caller->find_insn(dummy_end_instruction).unwrap());
  auto new_it = new_blk->to_cfg_instruction_iterator(new_blk->get_first_insn());
  always_assert(insn == new_it->insn);
  it = new_it;
  return std::make_pair(old_block, new_blk);
}

/*
 * Change the register numbers to not overlap with caller.
 */
void CFGInliner::remap_registers(cfg::ControlFlowGraph* callee,
                                 reg_t next_caller_reg) {
  for (auto& mie : cfg::InstructionIterable(*callee)) {
    auto* insn = mie.insn;
    for (reg_t i = 0; i < insn->srcs_size(); ++i) {
      insn->set_src(i, insn->src(i) + next_caller_reg);
    }
    if (insn->has_dest()) {
      insn->set_dest(insn->dest() + next_caller_reg);
    }
  }
}

/*
 * Move ownership of blocks and edges from callee to caller
 */
void CFGInliner::steal_contents(ControlFlowGraph* caller,
                                Block* /*callsite*/,
                                ControlFlowGraph* callee) {
  always_assert(!caller->m_blocks.empty());
  for (auto& entry : callee->m_blocks) {
    Block* b = entry.second;
    b->m_parent = caller;
    size_t id = caller->m_blocks.rbegin()->first + 1;
    b->m_id = id;
    caller->m_blocks.emplace(id, b);
  }
  callee->m_blocks.clear();

  // transfer ownership of the edges
  caller->m_edges.reserve(caller->m_edges.size() + callee->m_edges.size());
  insert_unordered_iterable(caller->m_edges, callee->m_edges);
  callee->m_edges.clear();
}

/*
 * If `insert_after`, add edges from callsite to the entry point and back from
 * the exit points to to the block after the callsite. Otherwise add edges
 * into callsite to the entry point and from the exit points to the block
 * after.
 */
void CFGInliner::connect_cfgs(bool inline_after,
                              ControlFlowGraph* cfg,
                              Block* callsite,
                              const std::vector<Block*>& callee_blocks,
                              Block* callee_entry,
                              const std::vector<Block*>& callee_exits,
                              Block* callsite_split,
                              bool needs_constructor_fence) {

  // Add edges from callee throw sites to caller catch sites
  const auto& caller_throws = callsite->get_outgoing_throws_in_order();

  if (!caller_throws.empty()) {
    add_callee_throws_to_caller(cfg, callee_blocks, caller_throws);
  }

  auto connect = [&cfg](const std::vector<Block*>& preds, Block* succ) {
    for (Block* pred : preds) {
      TRACE(CFG, 4, "connecting %zu, %zu in %s", pred->id(), succ->id(),
            SHOW(*cfg));
      cfg->add_edge(pred, succ, EDGE_GOTO);
    }
  };

  if (inline_after) {
    // Remove the goto between the callsite and its successor
    cfg->delete_succ_edge_if(
        callsite, [](const Edge* e) { return e->type() == EDGE_GOTO; });
    connect({callsite}, callee_entry);
  } else {
    // Remove the preds into callsite, having moved them to entry
    cfg->delete_succ_edges(callsite_split);
    connect({callsite_split}, callee_entry);
  }
  // TODO: tail call optimization (if callsite_split is a return & inline_after)

  auto constructor_fence = [&](Block* b) {
    if (!needs_constructor_fence) {
      return b;
    }
    auto* c = cfg->create_block();
    c->push_back((new IRInstruction(IOPCODE_WRITE_BARRIER)));
    // Get this block its own source block and debug position
    // if this method has any.
    auto* template_sb = source_blocks::get_first_source_block(b);
    if (template_sb != nullptr) {
      auto new_sb = std::make_unique<SourceBlock>(*template_sb);
      new_sb->id = SourceBlock::kSyntheticId;
      new_sb->next = nullptr;
      auto c_it = c->get_first_insn();
      c->insert_before(c_it, std::move(new_sb));
    }

    auto last_insn = b->get_last_insn();
    if (last_insn != b->end()) {
      auto b_it = b->to_cfg_instruction_iterator(last_insn);
      auto* pos = cfg->get_dbg_pos(b_it);
      if (pos != nullptr) {
        cfg->insert_before(c, c->begin(), std::make_unique<DexPosition>(*pos));
      }
    }
    cfg->add_edge(c, b, EDGE_GOTO);
    return c;
  };

  if (inline_after) {
    connect(callee_exits, constructor_fence(callsite_split));
  } else {
    cfg->delete_pred_edges(callsite);
    connect(callee_exits, constructor_fence(callsite));
  }
}

/*
 * Convert load-params to moves.
 */
void CFGInliner::move_arg_regs(cfg::ControlFlowGraph* callee,
                               const std::vector<reg_t>& srcs) {
  auto param_insns = callee->get_param_instructions();

  reg_t i = 0;
  for (auto& mie : ir_list::InstructionIterable(param_insns)) {
    IRInstruction* load = mie.insn;
    IRInstruction* move =
        new IRInstruction(opcode::load_param_to_move(mie.insn->opcode()));
    move->set_src(0, srcs.at(i));
    move->set_dest(load->dest());
    // replace the load instruction with the new move instruction
    mie.insn = move;
    i++;
    delete load;
  }
}

/*
 * Convert returns to moves.
 */
void CFGInliner::move_return_reg(cfg::ControlFlowGraph* callee,
                                 const std::optional<reg_t>& ret_reg) {
  std::vector<cfg::InstructionIterator> to_delete;
  auto iterable = cfg::InstructionIterable(*callee);
  for (auto it = iterable.begin(); it != iterable.end(); ++it) {
    if (opcode::is_a_return(it->insn->opcode())) {
      IRInstruction* ret = it->insn;
      auto op = return_to_move(ret->opcode());

      if (op != OPCODE_NOP && ret_reg) {
        IRInstruction* move = new IRInstruction(op);
        move->set_src(0, ret->src(0));
        move->set_dest(*ret_reg);
        it->insn = move;
        delete ret;
      } else {
        // return-void is equivalent to nop
        // or the return register isn't used in the caller
        to_delete.push_back(it);
      }
    }
  }

  for (auto& it : to_delete) {
    callee->remove_insn(it);
  }
}

/*
 * Callees that were not in a try region when their CFGs were created, need to
 * have some blocks split because the callsite is in a try region. We do this
 * because we need to add edges from the throwing opcodes to the catch handler
 * of the caller's try region.
 *
 * Assumption: callsite is in a try region
 */
void CFGInliner::split_on_callee_throws(ControlFlowGraph* callee) {
  std::vector<Block*> work_list = callee->blocks();
  // iterate with an index instead of an iterator because we're adding to the
  // end while we iterate
  for (uint32_t i = 0; i < work_list.size(); ++i) {
    Block* b = work_list[i];
    // look for blocks we need to split
    IRList::iterator last = b->get_last_insn();
    const auto& iterable = ir_list::InstructionIterable(*b);
    for (auto it = iterable.begin(); it != iterable.end(); ++it) {
      const auto& mie = *it;
      auto* const insn = mie.insn;
      const auto op = insn->opcode();
      if (opcode::can_throw(op) && it.unwrap() != last) {
        const auto& cfg_it = b->to_cfg_instruction_iterator(it);
        Block* new_block = callee->split_block(cfg_it);
        work_list.push_back(new_block);
      }
    }
  }
}

/*
 * Add a throw edge from each may_throw to each catch that is thrown to from
 * the callsite
 *   * If there are already throw edges in callee, add this edge to the end
 *     of the list
 *
 * Assumption: caller_catches is sorted by catch index
 */
void CFGInliner::add_callee_throws_to_caller(
    ControlFlowGraph* cfg,
    const std::vector<Block*>& callee_blocks,
    const std::vector<Edge*>& caller_catches) {

  // There are two requirements about the catch indices here:
  //   1) New throw edges must be added to the end of a callee's existing
  //   throw chain. This is ensured by using the max index of the already
  //   existing throws 2) New throw edges must go to the callsite's catch
  //   blocks in the same order that the existing catch chain does. This is
  //   ensured by sorting caller_catches by their throw indices.

  // Add throw edges from callee_block to all the caller catches
  const auto& add_throw_edges =
      [&cfg, &caller_catches](Block* callee_block, uint32_t starting_index) {
        auto index = starting_index;
        for (Edge* caller_catch : caller_catches) {
          cfg->add_edge(callee_block, caller_catch->target(),
                        caller_catch->throw_info()->catch_type, index);
          ++index;
        }
      };

  for (Block* callee_block : callee_blocks) {
    const auto& existing_throws = callee_block->get_outgoing_throws_in_order();
    if (existing_throws.empty()) {
      // Blocks that end in a throwing instruction but don't have outgoing
      // throw instructions yet.
      //   * Instructions that can throw that were not in a try region before
      //   being inlined. These may have been created by
      //   split_on_callee_throws.
      //   * OPCODE_THROW instructions without any catch blocks before being
      //   inlined.
      IRList::iterator last = callee_block->get_last_insn();
      if (last != callee_block->end()) {
        const auto op = last->insn->opcode();
        if (opcode::can_throw(op)) {
          add_throw_edges(callee_block, /* starting_index */ 0);
        }
      }
    } else if (existing_throws.back()->throw_info()->catch_type != nullptr) {
      // Blocks that throw already
      //   * Instructions that can throw that were already in a try region
      //   with catch blocks
      //   * But don't add to the end of a throw list if there's a catchall
      //   already
      add_throw_edges(callee_block,
                      existing_throws.back()->throw_info()->index + 1);
    }
  }
}

void CFGInliner::set_dbg_pos_parents(ControlFlowGraph* callee,
                                     DexPosition* callsite_dbg_pos) {
  const auto* partial_inline_source = get_partial_inline_source();

  for (auto& entry : callee->m_blocks) {
    Block* b = entry.second;
    for (auto& mie : *b) {
      // Don't overwrite existing parent pointers because those are probably
      // methods that were inlined into callee before
      if (mie.type == MFLOW_POSITION && mie.pos->parent == nullptr) {
        // Deal with specially marked position that represents partially inlined
        // fallback invocation.
        if (mie.pos->file == partial_inline_source) {
          mie.pos = std::make_unique<DexPosition>(*callsite_dbg_pos);
        } else {
          // Share the callsite position rather than cloning it. A parent must
          // itself be a position present in this CFG --
          // `no_dangling_dex_positions` enforces exactly that -- and a clone
          // reachable only through this pointer is owned by nothing and present
          // nowhere, so it both leaks and trips the check during any later
          // inlining.
          //
          // Sharing does not blur provenance: `positions::mark_merged` mutates
          // only its survivor leaf, never a parent reached through this
          // pointer.
          mie.pos->parent = callsite_dbg_pos;
        }
      }
    }
  }
}

/*
 * Return the equivalent move opcode for the given return opcode
 */
IROpcode CFGInliner::return_to_move(IROpcode op) {
  switch (op) {
  case OPCODE_RETURN_VOID:
    return OPCODE_NOP;
  case OPCODE_RETURN:
    return OPCODE_MOVE;
  case OPCODE_RETURN_WIDE:
    return OPCODE_MOVE_WIDE;
  case OPCODE_RETURN_OBJECT:
    return OPCODE_MOVE_OBJECT;
  default:
    not_reached_log("Expected return op, got %s", SHOW(op));
  }
}

} // namespace cfg
