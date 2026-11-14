/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ControlFlow.h"

#include <iterator>
#include <queue>
#include <stack>
#include <utility>

#include "CppUtil.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexInstruction.h"
#include "DexPosition.h"
#include "IRList.h"
#include "InstructionLowering.h"
#include "RedexContext.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "Trace.h"

std::atomic<size_t> build_cfg_counter{0};
namespace {

bool edge_type_structural_equals(const cfg::CompactEdgeVector& e1,
                                 const cfg::CompactEdgeVector& e2) {
  if (e1.empty() && e2.empty()) {
    return true;
  }

  if (e1.empty() || e2.empty()) {
    return false;
  }

  if (e1.size() != e2.size()) {
    return false;
  }
  std::array<ssize_t, cfg::EDGE_TYPE_SIZE> edge_types{};
  for (size_t i = 0; i < e1.size(); i++) {
    edge_types[e1[i]->type()] += 1;
    edge_types[e2[i]->type()] -= 1;
  }

  return std::all_of(edge_types.begin(), edge_types.end(),
                     [](const ssize_t& count) { return count == 0; });
}

// return true if `it` should be the last instruction of this block
bool end_of_block(const IRList* ir, const IRList::iterator& it, bool in_try) {
  auto next = std::next(it);
  if (next == ir->end()) {
    return true;
  }

  // End the block before the first target in a contiguous sequence of targets.
  if (next->type == MFLOW_TARGET && it->type != MFLOW_TARGET) {
    return true;
  }

  // End the block before the first catch marker in a contiguous sequence of
  // catch markers.
  if (next->type == MFLOW_CATCH && it->type != MFLOW_CATCH) {
    return true;
  }

  // End the block before a TRY_START
  // and after a TRY_END
  if ((next->type == MFLOW_TRY && next->tentry->type == TRY_START) ||
      (it->type == MFLOW_TRY && it->tentry->type == TRY_END)) {
    return true;
  }

  if (in_try && it->type == MFLOW_OPCODE &&
      opcode::may_throw(it->insn->opcode())) {
    return true;
  }
  if (it->type != MFLOW_OPCODE) {
    return false;
  }
  if (opcode::is_branch(it->insn->opcode()) ||
      opcode::is_a_return(it->insn->opcode()) ||
      it->insn->opcode() == OPCODE_THROW) {
    return true;
  }

  return false;
}

bool ends_with_may_throw(cfg::Block* p) {
  for (auto last = p->rbegin(); last != p->rend(); ++last) {
    if (last->type != MFLOW_OPCODE) {
      continue;
    }
    return opcode::can_throw(last->insn->opcode());
  }
  return false;
}

/*
 * Given a method-item-entry ordering, delete positions that are...
 * - duplicates with the previous position, even across block boundaries
 *   (they will get reconstituted when the cfg is rebuilt)
 * - adjacent to an immediately following position, as the last position wins.
 * Parent positions are kept as needed.
 */
void remove_redundant_positions(IRList* ir) {
  // We build a set of duplicate positions.
  UnorderedSet<DexPosition*> duplicate_positions;
  UnorderedMap<DexPosition*, IRList::iterator> positions_to_remove;
  DexPosition* prev = nullptr;
  for (auto it = ir->begin(); it != ir->end(); it++) {
    if (it->type == MFLOW_POSITION) {
      DexPosition* curr = it->pos.get();
      positions_to_remove.emplace(curr, it);
      if (prev != nullptr && *curr == *prev) {
        duplicate_positions.insert(curr);
      }
      prev = curr;
    }
  }

  // Backward pass to find positions that are not adjacent to an immediately
  // following position and must be kept (including their parents).
  bool keep_prev = false;
  for (auto it = ir->rbegin(); it != ir->rend(); it++) {
    switch (it->type) {
    case MFLOW_OPCODE:
    case MFLOW_DEX_OPCODE:
    case MFLOW_TARGET:
    case MFLOW_TRY:
    case MFLOW_CATCH:
      keep_prev = true;
      break;
    case MFLOW_POSITION: {
      DexPosition* curr = it->pos.get();
      if (keep_prev && (duplicate_positions.count(curr) == 0u)) {
        for (auto* pos = curr;
             (pos != nullptr) && (positions_to_remove.erase(pos) != 0u);
             pos = pos->parent) {
        }
        keep_prev = false;
      }
      break;
    }
    case MFLOW_SOURCE_BLOCK:
    case MFLOW_REMARK:
    case MFLOW_DEBUG:
    case MFLOW_FALLTHROUGH:
      // ignore
      break;
    }
  }

  // Final pass to do the actual deletion.
  for (auto& p : UnorderedIterable(positions_to_remove)) {
    ir->erase_and_dispose(p.second);
  }
}

// Follow the catch entry linked list starting at `first_mie` and check if the
// throw edges (pointed to by `it`) are equivalent to the linked list. The throw
// edges should be sorted by their indices.
//
// This function is useful in avoiding generating multiple identical catch
// entries.
//
// Used while turning back into a linear representation.
bool catch_entries_equivalent_to_throw_edges(
    cfg::ControlFlowGraph* cfg,
    MethodItemEntry* first_mie,
    std::vector<cfg::Edge*>::iterator it,
    std::vector<cfg::Edge*>::iterator end,
    const UnorderedMap<MethodItemEntry*, cfg::Block*>&
        catch_to_containing_block) {
  for (auto* mie = first_mie; mie != nullptr; mie = mie->centry->next) {
    always_assert(mie->type == MFLOW_CATCH);
    if (it == end) {
      return false;
    }
    auto* edge = *it;

    if (mie->centry->catch_type != edge->throw_info()->catch_type) {
      return false;
    }

    const auto& search = catch_to_containing_block.find(mie);
    always_assert_log(search != catch_to_containing_block.end(),
                      "%s not found in %s", SHOW(*mie), SHOW(*cfg));
    if (search->second != edge->target()) {
      return false;
    }

    ++it;
  }
  return it == end;
}

} // namespace

namespace cfg {

namespace details {

std::string show_cfg(const ControlFlowGraph& cfg) { return show(cfg); }
std::string show_insn(const IRInstruction* insn) { return show(insn); }

} // namespace details

void Block::free() {
  for (auto& mie : *this) {
    switch (mie.type) {
    case MFLOW_OPCODE:
      delete mie.insn;
      mie.insn = nullptr;
      break;
    case MFLOW_DEX_OPCODE:
      delete mie.dex_insn;
      mie.dex_insn = nullptr;
      break;
    default:
      break;
    }
  }
}

void Block::cleanup_debug(UnorderedSet<reg_t>& valid_regs) {
  this->m_entries.cleanup_debug(valid_regs);
}

IRList::iterator Block::begin() { return m_entries.begin(); }

IRList::iterator Block::end() { return m_entries.end(); }

IRList::const_iterator Block::begin() const { return m_entries.begin(); }

IRList::const_iterator Block::end() const { return m_entries.end(); }

bool Block::is_catch() const {
  return m_parent->get_pred_edge_of_type(this, EDGE_THROW) != nullptr;
}

bool Block::same_try(const Block* other) const {
  always_assert(other->m_parent == this->m_parent);
  return m_parent->blocks_are_in_same_try(this, other);
}

void Block::remove_insn(const InstructionIterator& it) {
  m_parent->remove_insn(it);
}

void Block::remove_insn(const ir_list::InstructionIterator& it) {
  remove_insn(to_cfg_instruction_iterator(it));
}

void Block::remove_insn(const IRList::iterator& it) {
  remove_insn(to_cfg_instruction_iterator(it));
}

IRList::iterator Block::remove_mie(const IRList::iterator& it) {
  if (it->type == MFLOW_OPCODE) {
    m_parent->m_removed_insns.push_back(it->insn);
  }

  return m_entries.erase_and_dispose(it);
}

opcode::Branchingness Block::branchingness() const {
  const auto& last = get_last_insn();

  if (succs().empty() ||
      (succs().size() == 1 &&
       m_parent->get_succ_edge_of_type(this, EDGE_GHOST) != nullptr)) {
    if (last != end()) {
      auto op = last->insn->opcode();
      if (opcode::is_a_return(op)) {
        return opcode::BRANCH_RETURN;
      } else if (op == OPCODE_THROW) {
        return opcode::BRANCH_THROW;
      }
    }
    return opcode::BRANCH_NONE;
  }

  if (m_parent->get_succ_edge_of_type(this, EDGE_THROW) != nullptr) {
    return opcode::BRANCH_THROW;
  }

  if (m_parent->get_succ_edge_of_type(this, EDGE_BRANCH) != nullptr) {
    always_assert(last != end());
    auto br = opcode::branchingness(last->insn->opcode());
    always_assert(br == opcode::BRANCH_IF || br == opcode::BRANCH_SWITCH);
    return br;
  }

  if (m_parent->get_succ_edge_of_type(this, EDGE_GOTO) != nullptr) {
    return opcode::BRANCH_GOTO;
  }
  return opcode::BRANCH_NONE;
}

uint32_t Block::num_opcodes() const {
  return static_cast<uint32_t>(m_entries.count_opcodes());
}

uint32_t Block::sum_opcode_sizes() const {
  return static_cast<uint32_t>(m_entries.sum_opcode_sizes());
}

uint32_t Block::estimate_code_units() const {
  auto code_units = m_entries.estimate_code_units();
  auto it = get_last_insn();
  if (it != end() && opcode::is_switch(it->insn->opcode())) {
    instruction_lowering::CaseKeysExtentBuilder case_keys;
    for (auto* e : succs()) {
      if (e->type() == EDGE_BRANCH) {
        case_keys.insert(*e->case_key());
      }
    }
    code_units += case_keys->estimate_switch_payload_code_units();
  }
  return code_units;
}

bool Block::is_unreachable() const {
  UnorderedSet<const cfg::Block*> visited;
  for (const auto* block = this;
       (block != nullptr) && visited.insert(block).second;) {
    auto ii = ir_list::ConstInstructionIterable(block);
    for (auto it = ii.begin(); it != ii.end(); ++it) {
      if (opcode::is_unreachable(it->insn->opcode())) {
        return true;
      }
      if (opcode::is_a_load_param(it->insn->opcode())) {
        continue;
      }
      return false;
    }
    block = block->goes_to_only_edge();
  }
  // We hit a non-terminating loop; that doesn't make this unreachable.
  return false;
}

// shallowly copy pointers (edges and parent cfg)
// but deeply copy MethodItemEntries
Block::Block(const Block& b, MethodItemEntryCloner* cloner)
    : m_id(b.m_id),
      m_preds(b.m_preds),
      m_succs(b.m_succs),
      m_parent(b.m_parent) {
  for (const auto& mie : b.m_entries) {
    m_entries.push_back(*cloner->clone(&mie));
  }
}

bool Block::has_pred(Block* b, EdgeType t) const {
  const auto& edges = preds();
  return std::find_if(edges.begin(), edges.end(), [b, t](const Edge* edge) {
           return edge->src() == b &&
                  (t == EDGE_TYPE_SIZE || edge->type() == t);
         }) != edges.end();
}

bool Block::has_succ(Block* b, EdgeType t) const {
  const auto& edges = succs();
  return std::find_if(edges.begin(), edges.end(), [b, t](const Edge* edge) {
           return edge->target() == b &&
                  (t == EDGE_TYPE_SIZE || edge->type() == t);
         }) != edges.end();
}

IRList::iterator Block::get_conditional_branch() {
  for (auto it = rbegin(); it != rend(); ++it) {
    if (it->type == MFLOW_OPCODE) {
      auto op = it->insn->opcode();
      if (opcode::is_a_conditional_branch(op) || opcode::is_switch(op)) {
        return std::prev(it.base());
      }
    }
  }
  return end();
}

IRList::iterator Block::get_last_insn() {
  for (auto it = rbegin(); it != rend(); ++it) {
    if (it->type == MFLOW_OPCODE) {
      // Reverse iterators have a member base() which returns a corresponding
      // forward iterator. Beware that this isn't an iterator that refers to the
      // same object - it actually refers to the next object in the sequence.
      // This is so that rbegin() corresponds with end() and rend() corresponds
      // with begin(). Copied from https://stackoverflow.com/a/2037917
      return std::prev(it.base());
    }
  }
  return end();
}

IRList::const_iterator Block::get_last_insn() const {
  for (auto it = rbegin(); it != rend(); ++it) {
    if (it->type == MFLOW_OPCODE) {
      // Reverse iterators have a member base() which returns a corresponding
      // forward iterator. Beware that this isn't an iterator that refers to the
      // same object - it actually refers to the next object in the sequence.
      // This is so that rbegin() corresponds with end() and rend() corresponds
      // with begin(). Copied from https://stackoverflow.com/a/2037917
      return std::prev(it.base());
    }
  }
  return end();
}

IRList::iterator Block::get_first_insn() {
  for (auto it = begin(); it != end(); ++it) {
    if (it->type == MFLOW_OPCODE) {
      return it;
    }
  }
  return end();
}

IRList::const_iterator Block::get_first_insn() const {
  for (auto it = begin(); it != end(); ++it) {
    if (it->type == MFLOW_OPCODE) {
      return it;
    }
  }
  return end();
}

IRList::iterator Block::get_first_non_param_loading_insn() {
  for (auto it = begin(); it != end(); ++it) {
    if (it->type != MFLOW_OPCODE) {
      continue;
    }
    if (!opcode::is_a_load_param(it->insn->opcode())) {
      return it;
    }
  }
  return end();
}

IRList::const_iterator Block::get_first_non_param_loading_insn() const {
  for (auto it = begin(); it != end(); ++it) {
    if (it->type != MFLOW_OPCODE) {
      continue;
    }
    if (!opcode::is_a_load_param(it->insn->opcode())) {
      return it;
    }
  }
  return end();
}

IRList::iterator Block::get_last_param_loading_insn() {
  IRList::iterator res = end();
  for (auto it = begin(); it != end(); ++it) {
    if (it->type != MFLOW_OPCODE) {
      continue;
    }
    if (opcode::is_a_load_param(it->insn->opcode())) {
      res = it;
    } else {
      // There won't be another one.
      break;
    }
  }
  return res;
}

IRList::const_iterator Block::get_last_param_loading_insn() const {
  IRList::const_iterator res = end();
  for (auto it = begin(); it != end(); ++it) {
    if (it->type != MFLOW_OPCODE) {
      continue;
    }
    if (opcode::is_a_load_param(it->insn->opcode())) {
      res = it;
    } else {
      // There won't be another one.
      break;
    }
  }
  return res;
}

IRList::iterator Block::get_first_insn_before_position() {
  for (auto it = begin(); it != end(); ++it) {
    if (it->type == MFLOW_OPCODE) {
      auto op = it->insn->opcode();
      if (!opcode::is_move_result_any(op) && !opcode::is_goto(op)) {
        return it;
      }
    } else if (it->type == MFLOW_POSITION) {
      return end();
    }
  }
  return end();
}

IRList::const_iterator Block::get_first_insn_before_position() const {
  for (auto it = begin(); it != end(); ++it) {
    if (it->type == MFLOW_OPCODE) {
      auto op = it->insn->opcode();
      if (!opcode::is_move_result_any(op) && !opcode::is_goto(op)) {
        return it;
      }
    } else if (it->type == MFLOW_POSITION) {
      return end();
    }
  }
  return end();
}

bool Block::starts_with_move_result() const {
  auto first_it = get_first_insn();
  if (first_it != end()) {
    auto first_op = first_it->insn->opcode();
    if (opcode::is_move_result_any(first_op)) {
      return true;
    }
  }
  return false;
}

bool Block::starts_with_move_exception() const {
  auto first_it = get_first_insn();
  if (first_it != end()) {
    auto first_op = first_it->insn->opcode();
    if (opcode::is_move_exception(first_op)) {
      return true;
    }
  }
  return false;
}

bool Block::contains_opcode(IROpcode opcode) const {
  for (auto it = begin(); it != end(); ++it) {
    if (it->type != MFLOW_OPCODE) {
      continue;
    }
    if (it->insn->opcode() == opcode) {
      return true;
    }
  }
  return false;
}

bool Block::begins_with(Block* other) const {
  IRList::const_iterator self_it = this->begin();
  IRList::const_iterator other_it = other->begin();

  while (self_it != this->end() && other_it != other->end()) {
    if (*self_it != *other_it) {
      return false;
    }

    self_it++;
    other_it++;
  }

  return other_it == other->end();
}

Block* Block::goes_to() const {
  const Edge* e = m_parent->get_succ_edge_of_type(this, EDGE_GOTO);
  if (e != nullptr) {
    return e->target();
  }
  return nullptr;
}

Block* Block::goes_to_only_edge() const {
  const auto& s = succs();
  if (s.size() == 1) {
    const auto& e = s[0];
    if (e->type() == EDGE_GOTO) {
      return e->target();
    }
  }
  return nullptr;
}

bool Block::cannot_throw() const {
  for (const auto& mie : ir_list::ConstInstructionIterable(this)) {
    if (opcode::can_throw(mie.insn->opcode())) {
      return false;
    }
  }
  return true;
}

bool block_eventually_throws(Block* block) {
  UnorderedSet<Block*> visited{block};
  for (; block->goes_to_only_edge() != nullptr;
       block = block->goes_to_only_edge()) {
    if (!visited.insert(block->goes_to_only_edge()).second) {
      // non-terminating loop
      return false;
    }
  }
  auto last_insn_it = block->get_last_insn();
  return last_insn_it != block->end() &&
         last_insn_it->insn->opcode() == OPCODE_THROW;
}

std::vector<Edge*> Block::get_outgoing_throws_in_order() const {
  std::vector<Edge*> result =
      m_parent->get_succ_edges_of_type(this, EDGE_THROW);
  std::sort(result.begin(), result.end(), [](const Edge* e1, const Edge* e2) {
    return e1->throw_info()->index < e2->throw_info()->index;
  });
  return result;
}

std::vector<Edge*> Block::get_outgoing_branches_in_order() const {
  std::vector<Edge*> result =
      m_parent->get_succ_edges_of_type(this, EDGE_BRANCH);
  if (result.size() > 1) {
    std::sort(result.begin(), result.end(), [](const Edge* e1, const Edge* e2) {
      return e1->case_key() < e2->case_key();
    });
  }
  return result;
}

// These assume that the iterator is inside this block
cfg::InstructionIterator Block::to_cfg_instruction_iterator(
    const ir_list::InstructionIterator& list_it, bool next_on_end) {
  if (ControlFlowGraph::s_DEBUG && list_it.unwrap() != end()) {
    bool inside = false;
    auto needle = list_it.unwrap();
    for (auto it = begin(); it != end(); ++it) {
      if (it == needle) {
        inside = true;
      }
    }
    always_assert(inside);
  }
  auto it = cfg::InstructionIterator(*m_parent, this, list_it);
  if (next_on_end && list_it.unwrap() == end()) {
    ++it;
  }
  return it;
}

cfg::InstructionIterator Block::to_cfg_instruction_iterator(
    const IRList::iterator& list_it, bool next_on_end) {
  always_assert(list_it == this->end() || list_it->type == MFLOW_OPCODE);
  return to_cfg_instruction_iterator(
      ir_list::InstructionIterator(list_it, this->end()), next_on_end);
}

cfg::InstructionIterator Block::to_cfg_instruction_iterator(
    MethodItemEntry& mie) {
  return to_cfg_instruction_iterator(m_entries.iterator_to(mie));
}

// Forward the insertion methods to the parent CFG.
bool Block::insert_before(const InstructionIterator& position,
                          const std::vector<IRInstruction*>& insns) {
  always_assert(position.block() == this);
  return m_parent->insert_before(position, insns);
}
bool Block::insert_before(const InstructionIterator& position,
                          IRInstruction* insn) {
  always_assert(position.block() == this);
  return m_parent->insert_before(position, insn);
}
bool Block::insert_after(const InstructionIterator& position,
                         const std::vector<IRInstruction*>& insns) {
  always_assert(position.block() == this);
  return m_parent->insert_after(position, insns);
}
bool Block::insert_after(const InstructionIterator& position,
                         IRInstruction* insn) {
  always_assert(position.block() == this);
  return m_parent->insert_after(position, insn);
}
bool Block::push_front(const std::vector<IRInstruction*>& insns) {
  return m_parent->push_front(this, insns);
}
bool Block::push_front(IRInstruction* insn) {
  return m_parent->push_front(this, insn);
}
bool Block::push_back(const std::vector<IRInstruction*>& insns) {
  return m_parent->push_back(this, insns);
}
bool Block::push_back(IRInstruction* insn) {
  return m_parent->push_back(this, insn);
}
bool Block::structural_equals(const Block* other) const {
  return this->structural_equals(other, std::equal_to<const IRInstruction&>());
}

bool Block::structural_equals(
    const Block* other, const InstructionEquality& instruction_equals) const {
  auto iterable1 = ir_list::ConstInstructionIterable(this);
  auto iterable2 = ir_list::ConstInstructionIterable(other);
  auto it1 = iterable1.begin();
  auto it2 = iterable2.begin();

  for (; it1 != iterable1.end() && it2 != iterable2.end(); ++it1, ++it2) {
    const auto& mie1 = *it1;
    const auto& mie2 = *it2;

    if (!instruction_equals(*mie1.insn, *mie2.insn)) {
      return false;
    }
  }

  return it1 == iterable1.end() && it2 == iterable2.end();
}

bool Block::extended_structural_equals(
    const Block* other, const InstructionEquality& instruction_equals) const {
  if (!edge_type_structural_equals(this->preds(), other->preds()) ||
      !edge_type_structural_equals(this->succs(), other->succs())) {
    return false;
  }
  return this->structural_equals(other, instruction_equals);
}

std::ostream& operator<<(std::ostream& os, const Edge& e) {
  switch (e.type()) {
  case EDGE_GOTO:
    return os << "goto";

  case EDGE_BRANCH: {
    os << "branch";
    const auto& key = e.case_key();
    if (key) {
      os << " " << *key;
    }
    return os;
  }

  case EDGE_THROW: {
    auto* catch_type = e.throw_info()->catch_type;
    if (catch_type == nullptr) {
      return os << "throw";
    } else {
      return os << "throw " << show(catch_type);
    }
  }
  case EDGE_GHOST:
    return os << "ghost";

  case EDGE_TYPE_SIZE:
    break;
  }
  not_reached();
}

bool ControlFlowGraph::s_DEBUG = false;

ControlFlowGraph::ControlFlowGraph(IRList* ir, reg_t registers_size)
    : m_registers_size(registers_size) {
  always_assert_log(!ir->empty(), "IRList contains no instructions");
  build_cfg_counter++;

  BranchToTargets branch_to_targets;
  TryEnds try_ends;
  TryCatches try_catches;

  find_block_boundaries(ir, branch_to_targets, try_ends, try_catches);

  connect_blocks(branch_to_targets);
  add_catch_edges(try_ends, try_catches);

  remove_try_catch_markers();

  // Often, the `registers_size` parameter passed into this constructor is
  // incorrect. We recompute here to safeguard against this.
  // TODO: fix the optimizations that don't track registers size correctly.
  recompute_registers_size();

  TRACE_NO_LINE(CFG, 5, "before simplify:\n%s", SHOW(*this));
  simplify();
  TRACE_NO_LINE(CFG, 5, "after simplify:\n%s", SHOW(*this));

  TRACE_NO_LINE(CFG, 5, "%s", SHOW(*this));
}

void ControlFlowGraph::find_block_boundaries(IRList* ir,
                                             BranchToTargets& branch_to_targets,
                                             TryEnds& try_ends,
                                             TryCatches& try_catches) {
  // create the entry block
  auto* block = create_block();
  IRList::iterator block_begin = ir->begin();
  set_entry_block(block);

  bool in_try = false;
  IRList::iterator next;
  DexPosition* current_position = nullptr;
  DexPosition* last_pos_before_this_block = nullptr;
  for (auto it = ir->begin(); it != ir->end(); it = next) {
    next = std::next(it);
    if (it->type == MFLOW_TRY) {
      if (it->tentry->type == TRY_START) {
        // Assumption: TRY_STARTs are only at the beginning of blocks
        always_assert(it == block_begin);
        in_try = true;
      } else if (it->tentry->type == TRY_END) {
        try_ends.emplace_back(it->tentry, block);
        in_try = false;
      }
    } else if (it->type == MFLOW_CATCH) {
      try_catches[it->centry] = block;
    } else if (it->type == MFLOW_TARGET) {
      branch_to_targets[it->target->src].emplace_back(block, &*it);
    } else if (it->type == MFLOW_POSITION) {
      current_position = it->pos.get();
    }

    if (!end_of_block(ir, it, in_try)) {
      continue;
    }

    // End the current block.
    // Steal the code from the ir and put it into the block.
    // This is safe to do while iterating in ir because iterators in ir now
    // point to elements of block->m_entries (and we already computed next).
    block->m_entries.splice_selection(block->m_entries.end(), *ir, block_begin,
                                      next);
    if (last_pos_before_this_block != nullptr) {
      auto first_insn = block->get_first_insn_before_position();
      if (first_insn != block->end()) {
        // DexPositions apply to every instruction in the linear stream until
        // the next DexPosition. Because we're breaking up the linear stream
        // into many small blocks, we need to make sure that instructions stay
        // associated with the same DexPosition as they were in the input
        // IRList.
        //
        // This creates duplicate positions, but we will remove any extras at
        // linearize time.
        block->m_entries.insert_before(
            first_insn,
            std::make_unique<DexPosition>(*last_pos_before_this_block));
      }
    }

    if (next == ir->end()) {
      break;
    }

    // Start a new block at the next MethodItem.
    block = create_block();
    last_pos_before_this_block = current_position;
    block_begin = next;
  }
  TRACE(CFG, 5, "  build: boundaries found");
}

// Link the blocks together with edges. Also insert
// fallthrough goto instructions and delete MFLOW_TARGETs.
void ControlFlowGraph::connect_blocks(BranchToTargets& branch_to_targets) {
  for (auto it = m_blocks.begin(); it != m_blocks.end(); ++it) {
    // Set outgoing edge if last MIE falls through
    Block* b = it->second;
    auto rit = b->rbegin();
    auto* last_mie = rit == b->rend() ? nullptr : &*rit;
    bool fallthrough = true;
    if ((last_mie != nullptr) && last_mie->type == MFLOW_OPCODE) {
      auto last_op = last_mie->insn->opcode();
      if (opcode::is_branch(last_op)) {
        fallthrough = !opcode::is_goto(last_op);
        auto const& target_blocks = branch_to_targets[last_mie];

        for (const auto& p : target_blocks) {
          auto* target_block = p.first;
          auto& target_mie = *p.second;
          always_assert(target_mie.type == MFLOW_TARGET);
          always_assert(target_mie.target->src == last_mie);
          Edge::MaybeCaseKey case_key;
          if (target_mie.target->type == BRANCH_MULTI) {
            always_assert_log(opcode::is_switch(last_mie->insn->opcode()),
                              "block %zu in %s\n", target_block->id(),
                              SHOW(*this));
            case_key = target_mie.target->case_key;
          } else {
            always_assert(target_mie.target->type == BRANCH_SIMPLE);
          }
          // The branch information is stored in the edges, we don't need
          // the targets inside the blocks anymore
          target_block->m_entries.erase_and_dispose(
              target_block->m_entries.iterator_to(target_mie));

          if (case_key) {
            add_edge(b, target_block, *case_key);
            continue;
          }
          auto edge_type = opcode::is_goto(last_op) ? EDGE_GOTO : EDGE_BRANCH;
          add_edge(b, target_block, edge_type);
        }

        if (opcode::is_goto(last_op)) {
          // We don't need the gotos because the edges
          // fully encode that information
          delete last_mie->insn;
          b->m_entries.erase_and_dispose(b->m_entries.iterator_to(*last_mie));
        }

      } else if (opcode::is_a_return(last_op) || last_op == OPCODE_THROW) {
        fallthrough = false;
      }
    }

    auto next = std::next(it);
    if (fallthrough && next != m_blocks.end()) {
      Block* next_b = next->second;
      TRACE(CFG, 6, "adding fallthrough goto %zu -> %zu", b->id(),
            next_b->id());
      add_edge(b, next_b, EDGE_GOTO);
    }
  }
  TRACE(CFG, 5, "  build: edges added");
}

void ControlFlowGraph::add_catch_edges(TryEnds& try_ends,
                                       TryCatches& try_catches) {
  /*
   * Every block inside a try-start/try-end region
   * gets an edge to every catch block.  This simplifies dataflow analysis
   * since you can always get the exception state by looking at successors,
   * without any additional analysis.
   *
   * NB: This algorithm assumes that a try-start/try-end region will consist of
   * sequentially-numbered blocks, which is guaranteed because catch regions
   * are contiguous in the bytecode, and we generate blocks in bytecode order.
   */
  for (auto tep : try_ends) {
    auto* try_end = tep.first;
    auto* tryendblock = tep.second;
    size_t bid = tryendblock->id();
    while (true) {
      Block* block = m_blocks.at(bid);
      if (ends_with_may_throw(block)) {
        uint32_t i = 0;
        for (auto* mie = try_end->catch_start; mie != nullptr;
             mie = mie->centry->next) {
          auto* catchblock = try_catches.at(mie->centry);
          // Create a throw edge with the information from this catch entry
          add_edge(block, catchblock, mie->centry->catch_type, i);
          ++i;
        }
      }
      auto block_begin = block->begin();
      if (block_begin != block->end() && block_begin->type == MFLOW_TRY) {
        auto* tentry = block_begin->tentry;
        if (tentry->type == TRY_START) {
          always_assert_log(tentry->catch_start == try_end->catch_start, "%s",
                            SHOW(*this));
          break;
        }
      }
      always_assert_log(bid > 0, "No beginning of try region found");
      --bid;
    }
  }
  TRACE(CFG, 5, "  build: catch edges added");
}

BlockId ControlFlowGraph::next_block_id() const {
  // Choose the next largest id. Note that we can't use m_block.size() because
  // we may have deleted some blocks from the cfg.
  const auto& rbegin = m_blocks.rbegin();
  return (rbegin == m_blocks.rend()) ? 0 : (rbegin->first + 1);
}

void ControlFlowGraph::remove_unreachable_succ_edges() {
  // Remove edges between unreachable blocks and their succ blocks.
  if (m_blocks.empty()) {
    return;
  }

  const auto& visited = visit();
  if (visited.all()) {
    // All blocks are visited. No blocks need to have their succ edges removed.
    return;
  }

  for (auto it = m_blocks.begin(); it != m_blocks.end(); ++it) {
    Block* b = it->second;
    if (visited.test(b->id())) {
      continue;
    }

    TRACE(CFG, 5, "  build: removing succ edges from block %zu", b->id());
    delete_succ_edges(b);
  }
  TRACE(CFG, 5, "  build: unreachables removed");
}

/*
 * Traverse the graph, starting from the entry node. Return a bitset with IDs of
 * reachable blocks having 1 and IDs of unreachable blocks (or unused IDs)
 * having 0.
 */
boost::dynamic_bitset<> ControlFlowGraph::visit() const {
  std::stack<const cfg::Block*> to_visit;
  boost::dynamic_bitset<> visited{next_block_id()};
  to_visit.push(entry_block());
  while (!to_visit.empty()) {
    const cfg::Block* b = to_visit.top();
    to_visit.pop();

    if (visited.test_set(b->id())) {
      continue;
    }

    for (Edge* e : b->succs()) {
      to_visit.push(e->target());
    }
  }
  return visited;
}

uint32_t ControlFlowGraph::simplify() {
  auto [num_insns_removed, registers_size_possibly_reduced] =
      remove_unreachable_blocks();
  if (registers_size_possibly_reduced) {
    recompute_registers_size();
  }
  // FIXME: "Empty" blocks with only `DexPosition`s should be merged
  //        into their successors for consistency. Otherwise
  //        `remove_empty_blocks` will remove them, which it will not
  //        if they are at the head of a non-empty block.
  remove_empty_blocks();

  for (auto& p : m_blocks) {
    p.second->m_entries.chain_consecutive_source_blocks();
  }

  return num_insns_removed;
}

// remove blocks with no predecessors
std::pair<uint32_t, bool> ControlFlowGraph::remove_unreachable_blocks() {
  uint32_t num_insns_removed = 0;
  remove_unreachable_succ_edges();
  std::vector<std::unique_ptr<DexPosition>> dangling;
  bool registers_size_possibly_reduced = false;
  for (auto it = m_blocks.begin(); it != m_blocks.end();) {
    Block* b = it->second;
    const auto& preds = b->preds();
    if (preds.empty() && b != entry_block()) {
      if (b == exit_block()) {
        set_exit_block(nullptr);
      }
      for (auto& mie : *b) {
        if (mie.type == MFLOW_POSITION) {
          dangling.push_back(std::move(mie.pos));
        } else if (mie.type == MFLOW_OPCODE) {
          auto* insn = mie.insn;
          if (insn->has_dest()) {
            // +1 because registers start at zero
            auto size_required =
                insn->dest() + static_cast<unsigned int>(insn->dest_is_wide()) +
                1;
            if (size_required >= m_registers_size) {
              // We're deleting an instruction that may have been the max
              // register of the entire function.
              registers_size_possibly_reduced = true;
            }
          }
        }
      }
      num_insns_removed += b->num_opcodes();
      always_assert(b->succs().empty());
      always_assert(b->preds().empty());
      // Deletion of a block deletes MIEs, but MIEs do not delete instructions.
      // Gotta do this manually for now.
      b->free();
      delete b;
      it = m_blocks.erase(it);
    } else {
      ++it;
    }
  }

  fix_dangling_parents(std::move(dangling));

  return std::make_pair(num_insns_removed, registers_size_possibly_reduced);
}

void ControlFlowGraph::fix_dangling_parents(
    std::vector<std::unique_ptr<DexPosition>> dangling) {
  if (dangling.empty()) {
    return;
  }

  // We move all dangling positions into a map that allows us to quickly find a
  // position by its pointer value while maintaining ownership of the position
  // in the associated unique_ptr. We'll use this map later try to find parent
  // positions.
  UnorderedMap<DexPosition*, std::unique_ptr<DexPosition>> map;
  for (auto& pos : dangling) {
    auto* pos_ptr = pos.get();
    map.emplace(pos_ptr, std::move(pos));
  }

  // Helper function to insert parent positions, as
  // needed.
  std::function<void(cfg::Block*, const IRList::iterator&, DexPosition*)>
      materialize;
  materialize = [&](cfg::Block* block, const IRList::iterator& it,
                    DexPosition* pos) {
    if (pos == nullptr) {
      return;
    }
    auto it2 = map.find(pos);
    if (it2 == map.end()) {
      return;
    }
    materialize(block, it, pos->parent);
    insert_before(block, it, std::move(it2->second));
    map.erase(it2);
  };

  // Search for dangling parent pointers and fix them
  for (cfg::Block* block : blocks()) {
    for (auto it = block->begin(); it != block->end(); it++) {
      if (it->type != MFLOW_POSITION) {
        continue;
      }
      materialize(block, it, it->pos->parent);
    }
  }

  // Note that the memory of those mapped position that didn't get used up will
  // get released at this point
}

void ControlFlowGraph::remove_empty_blocks() {
  std::vector<std::unique_ptr<DexPosition>> dangling;
  for (auto it = m_blocks.begin(); it != m_blocks.end();) {
    Block* b = it->second;
    if (b->get_first_insn() != b->end() || b == exit_block()) {
      ++it;
      continue;
    }

    const auto& succs = get_succ_edges_if(
        b, [](const Edge* e) { return e->type() != EDGE_GHOST; });
    if (!succs.empty()) {
      always_assert_log(succs.size() == 1,
                        "too many successors for empty block %zu:\n%s",
                        it->first, SHOW(*this));
      const auto& succ_edge = succs[0];
      Block* succ = succ_edge->target();

      if (b == succ) { // `b` follows itself: an infinite loop
        ++it;
        continue;
      }

      // The successor is reached only through this block when it has a single
      // predecessor (this block) and is not the entry block (which carries a
      // virtual in-edge). Only then is it correct to move b's block-anchored
      // metadata (source blocks, remarks) onto succ; otherwise moving would
      // mis-attribute it to code reached via succ's other predecessors, so we
      // let it drop with the block instead.
      const bool succ_reached_only_via_b =
          succ->preds().size() == 1 && succ != m_entry_block;

      // Move source blocks forward when it is safe; if it is not but we are
      // instrumenting, keep the whole block instead so its source blocks
      // survive for coverage.
      bool move_source_blocks{false};
      if (source_blocks::has_source_blocks(b)) {
        if (succ_reached_only_via_b) {
          move_source_blocks = true;
        } else if (g_redex->instrument_mode) {
          ++it;
          continue;
        }
      }

      // b is empty and removable. Reorganize the edges so we can remove it

      // Remove the one goto edge from b to succ
      delete_edges_between(b, succ);

      // If b was a predecessor of the exit block (for example, part of an
      // infinite loop) we need to transfer that info to `succ` because `b` will
      // be made unreachable and deleted by simplify
      auto* ghost = get_succ_edge_of_type(b, EDGE_GHOST);
      if (ghost != nullptr) {
        set_edge_source(ghost, succ);
      }

      // Redirect from b's predecessors to b's successor (skipping b). We
      // can't move edges around while we iterate through the edge list
      // though.
      std::vector<Edge*> need_redirect(b->m_preds.begin(), b->m_preds.end());
      for (Edge* pred_edge : need_redirect) {
        set_edge_target(pred_edge, succ);
      }

      if (b == entry_block()) {
        m_entry_block = succ;
      }

      // Move positions if succ doesn't have any
      auto first_it = succ->get_first_insn_before_position();
      if (first_it != succ->end()) {
        always_assert(
            !opcode::is_a_move_result_pseudo(first_it->insn->opcode()));
        for (auto& mie : *b) {
          if (mie.type == MFLOW_POSITION) {
            succ->m_entries.insert_before(first_it, std::move(mie.pos));
          }
        }
      }

      // Move every block-anchored MIE of the given kind from b onto the head of
      // succ, preserving their order (`take` extracts the moved-out payload).
      // Advancing the insertion point matters: inserting each one after
      // succ->begin() would reverse all but the first.
      auto move_to_succ_head = [&](MethodItemType type, auto take) {
        auto pos = succ->begin();
        bool first = true;
        for (auto& mie : *b) {
          if (mie.type != type) {
            continue;
          }
          pos = first ? succ->m_entries.insert_before(succ->begin(), take(mie))
                      : succ->m_entries.insert_after(pos, take(mie));
          first = false;
        }
      };
      if (move_source_blocks) {
        move_to_succ_head(MFLOW_SOURCE_BLOCK, [](MethodItemEntry& mie) {
          return std::move(mie.src_block);
        });
      }
      if (succ_reached_only_via_b) {
        move_to_succ_head(MFLOW_REMARK, [](MethodItemEntry& mie) {
          return std::move(mie.remark);
        });
      }
    }
    if (b == m_entry_block) {
      // Don't delete the entry block. If it was empty and had a successor,
      // we'd have replaced it just above.
      ++it;
      continue;
    }

    for (auto& mie : *b) {
      if (mie.type == MFLOW_POSITION) {
        dangling.push_back(std::move(mie.pos));
      }
    }
    b->free();
    delete b;
    it = m_blocks.erase(it);
  }
  fix_dangling_parents(std::move(dangling));
}

void ControlFlowGraph::no_unreferenced_edges() const {
  EdgeSet referenced;
  for (const auto& entry : m_blocks) {
    Block* b = entry.second;
    for (Edge* e : b->preds()) {
      referenced.insert(e);
    }
    for (Edge* e : b->succs()) {
      referenced.insert(e);
    }
  }
  always_assert(referenced == m_edges);
}

// Verify that
//  * MFLOW_TARGETs are gone
//  * OPCODE_GOTOs are gone
//  * Correct number of outgoing edges
void ControlFlowGraph::sanity_check() const {
  for (const auto& entry : m_blocks) {
    Block* b = entry.second;
    if (ControlFlowGraph::s_DEBUG) {
      // No targets or gotos
      for (const auto& mie : *b) {
        always_assert_log(mie.type != MFLOW_TARGET,
                          "failed to remove all targets. block %zu in\n%s",
                          b->id(), SHOW(*this));
        if (mie.type == MFLOW_OPCODE) {
          always_assert_log(!opcode::is_goto(mie.insn->opcode()),
                            "failed to remove all gotos. block %zu in\n%s",
                            b->id(), SHOW(*this));
        }
      }
    }

    // Last instruction matches outgoing edges
    uint32_t num_goto_succs = 0;
    uint32_t num_succs = 0;
    for (const Edge* e : b->succs()) {
      if (e->type() == EDGE_GOTO) {
        ++num_goto_succs;
      }
      if (e->type() != EDGE_GHOST) {
        ++num_succs;
      }
    }
    auto last_it = b->get_last_insn();
    auto num_preds = b->preds().size();
    if (last_it != b->end()) {
      auto op = last_it->insn->opcode();

      if (opcode::is_a_conditional_branch(op)) {
        always_assert_log(num_succs == 2, "block %zu, %s", b->id(),
                          SHOW(*this));
      } else if (opcode::is_switch(op)) {
        always_assert_log(num_succs > 1, "block %zu, %s", b->id(), SHOW(*this));
      } else if (opcode::is_a_return(op)) {
        // Make sure we don't have any outgoing edges (except EDGE_GHOST)
        always_assert_log(num_succs == 0, "block %zu, %s", b->id(),
                          SHOW(*this));
      } else if (opcode::is_throw(op)) {
        // A throw could end the method or go to a catch handler.
        // Make sure this block has no outgoing non-throwing edges
        auto* non_throw_edge = get_succ_edge_if(b, [](const Edge* e) {
          return e->type() != EDGE_THROW && e->type() != EDGE_GHOST;
        });
        always_assert_log(non_throw_edge == nullptr, "block %zu, %s", b->id(),
                          SHOW(*this));
      }

      if (num_preds > 0 && !(opcode::is_a_return(op) || opcode::is_throw(op))) {
        // Control Flow shouldn't just fall off the end of a block, unless
        // it's an orphan block that's unreachable anyway
        always_assert_log(num_succs > 0, "block %zu, %s", b->id(), SHOW(*this));
        always_assert_log(num_goto_succs == 1, "block %zu, %s", b->id(),
                          SHOW(*this));
      }
    } else if (num_preds > 0 && b != exit_block()) {
      // no instructions in this block. Control Flow shouldn't just fall off
      // the end
      always_assert_log(num_succs > 0, "block %zu, %s", b->id(), SHOW(*this));
      always_assert_log(num_goto_succs == 1, "block %zu, %s", b->id(),
                        SHOW(*this));
    }

    always_assert_log(num_goto_succs < 2, "block %zu, %s", b->id(),
                      SHOW(*this));
  }

  // IRInstruction pointers must be unique.
  UnorderedSet<IRInstruction*> pointer_check;
  for (const auto& mie : ConstInstructionIterable(*this)) {
    auto* insn = mie.insn;
    always_assert_log(
        pointer_check.count(insn) == 0,
        "IRInstruction pointers must be unique. You have inserted the "
        "following IRInstruction* multiple times:\n >> %s",
        SHOW(*insn));
    pointer_check.insert(insn);
  }

  for (const auto& entry : m_blocks) {
    Block* b = entry.second;
    // make sure the edge list in both blocks agree
    for (auto* const e : b->succs()) {
      const auto& reverse_edges = e->target()->preds();
      always_assert_log(std::find(reverse_edges.begin(), reverse_edges.end(),
                                  e) != reverse_edges.end(),
                        "block %zu -> %zu, %s", b->id(), e->target()->id(),
                        SHOW(*this));
    }
    for (auto* const e : b->preds()) {
      const auto& forward_edges = e->src()->succs();
      always_assert_log(std::find(forward_edges.begin(), forward_edges.end(),
                                  e) != forward_edges.end(),
                        "block %zu -> %zu, %s", e->src()->id(), b->id(),
                        SHOW(*this));
    }

    {
      std::optional<uint32_t> first_null_index;
      std::optional<uint32_t> last_non_null_index;
      for (const auto* e : b->succs()) {
        if (e->type() != EDGE_THROW) {
          continue;
        }
        auto* info = e->throw_info();
        if (info->catch_type == nullptr) {
          first_null_index = first_null_index
                                 ? std::min(*first_null_index, info->index)
                                 : info->index;
        } else {
          last_non_null_index =
              last_non_null_index ? std::max(*last_non_null_index, info->index)
                                  : info->index;
        }
      }
      always_assert_log(!last_non_null_index || !first_null_index ||
                            (*last_non_null_index < *first_null_index),
                        "Can't have a catchall that isn't last. %s",
                        SHOW(*this));
    }
  }

  auto used_regs = compute_registers_size();
  always_assert_log(used_regs <= m_registers_size,
                    "used regs %u > registers size %u. %s", used_regs,
                    m_registers_size, SHOW(*this));

  no_dangling_dex_positions();
  if (ControlFlowGraph::s_DEBUG) {
    no_unreferenced_edges();
  }
}

reg_t ControlFlowGraph::compute_registers_size() const {
  reg_t num_regs = 0;
  for (const auto& mie : cfg::ConstInstructionIterable(*this)) {
    auto* insn = mie.insn;
    if (insn->has_dest()) {
      // +1 because registers start at v0
      reg_t size_required =
          insn->dest() + static_cast<unsigned int>(insn->dest_is_wide()) + 1;
      num_regs = std::max(size_required, num_regs);
    }
  }
  // We don't check the source registers because we shouldn't ever be using an
  // undefined register. If the input code is well-formed, there shouldn't be a
  // source register without an equivalent dest register. This is true for our
  // IR because of the load-param opcodes.
  return num_regs;
}

void ControlFlowGraph::recompute_registers_size() {
  m_registers_size = compute_registers_size();
}

void ControlFlowGraph::no_dangling_dex_positions() const {
  UnorderedMap<DexPosition*, bool> parents;
  for (const auto& entry : m_blocks) {
    Block* b = entry.second;
    for (const auto& mie : *b) {
      if (mie.type == MFLOW_POSITION && mie.pos->parent != nullptr) {
        parents.emplace(mie.pos->parent, false);
      }
    }
  }

  for (const auto& entry : m_blocks) {
    Block* b = entry.second;
    for (const auto& mie : *b) {
      if (mie.type == MFLOW_POSITION) {
        auto search = parents.find(mie.pos.get());
        if (search != parents.end()) {
          search->second = true;
        }
      }
    }
  }

  for (const auto& entry : UnorderedIterable(parents)) {
    always_assert_log(entry.second, "%p is a dangling parent pointer in %s",
                      entry.first, SHOW(*this));
  }
}

uint32_t ControlFlowGraph::num_opcodes() const {
  uint32_t result = 0;
  for (const auto& entry : m_blocks) {
    result += entry.second->num_opcodes();
  }
  return result;
}

uint32_t ControlFlowGraph::sum_opcode_sizes() const {
  uint32_t result = 0;
  for (const auto& entry : m_blocks) {
    result += entry.second->sum_opcode_sizes();
  }
  return result;
}

// similar to sum_opcode_sizes, but takes into account non-opcode payloads
uint32_t ControlFlowGraph::estimate_code_units() const {
  uint32_t code_units = 0;
  for (const auto& entry : m_blocks) {
    code_units += entry.second->estimate_code_units();
  }
  return code_units;
}

uint32_t ControlFlowGraph::get_size_adjustment(
    bool assume_no_unreachable_blocks) {
  auto ordering =
      order(/* custom_strategy */ nullptr, assume_no_unreachable_blocks);
  uint32_t adjustment{0};
  for (auto it = ordering.begin(); it != ordering.end(); ++it) {
    cfg::Block* b = *it;

    for (const cfg::Edge* edge : b->succs()) {
      if (edge->type() == cfg::EDGE_GOTO) {
        auto next_it = std::next(it);
        if (next_it != ordering.end()) {
          cfg::Block* next = *next_it;
          if (edge->target() == next) {
            // Don't need a goto because this will fall through to `next`
            continue;
          }
        }
        // We need a goto
        adjustment++;
      }
    }
  }
  return adjustment;
}

Block* ControlFlowGraph::get_first_block_with_insns() const {
  Block* block = entry_block();
  UnorderedSet<Block*> visited{block};
  while (block != nullptr &&
         (block->empty() || block->get_first_insn() == block->end())) {
    block = block->goes_to();
    if (!visited.insert(block).second) {
      // We found a loop, and no param instructions.
      block = nullptr;
      break;
    }
  }
  return block;
}

boost::sub_range<IRList> ControlFlowGraph::get_param_instructions() const {
  Block* block = get_first_block_with_insns();
  if (block == nullptr) {
    // Return an empty sub_range
    return boost::sub_range<IRList>();
  }
  return block->m_entries.get_param_instructions();
}

void ControlFlowGraph::gather_catch_types(
    std::vector<const DexType*>& types) const {
  UnorderedSet<DexType*> seen;
  // get the catch types of all the incoming edges to all the catch blocks
  for (const auto& entry : m_blocks) {
    const Block* b = entry.second;
    if (b->is_catch()) {
      for (const cfg::Edge* e : b->preds()) {
        if (e->type() == cfg::EDGE_THROW) {
          DexType* t = e->throw_info()->catch_type;
          if (t != nullptr) {
            const auto pair = seen.insert(t);
            bool insertion_occurred = pair.second;
            if (insertion_occurred) {
              types.push_back(t);
            }
          }
        }
      }
    }
  }
}

void ControlFlowGraph::gather_strings(
    std::vector<const DexString*>& strings) const {
  for (const auto& entry : m_blocks) {
    entry.second->m_entries.gather_strings(strings);
  }
}

void ControlFlowGraph::gather_types(std::vector<const DexType*>& types) const {
  gather_catch_types(types);
  for (const auto& entry : m_blocks) {
    entry.second->m_entries.gather_types(types);
  }
}

void ControlFlowGraph::gather_init_classes(
    std::vector<const DexType*>& types) const {
  for (const auto& entry : m_blocks) {
    entry.second->m_entries.gather_init_classes(types);
  }
}

void ControlFlowGraph::gather_fields(std::vector<DexFieldRef*>& fields) const {
  for (const auto& entry : m_blocks) {
    entry.second->m_entries.gather_fields(fields);
  }
}

void ControlFlowGraph::gather_methods(
    std::vector<DexMethodRef*>& methods) const {
  for (const auto& entry : m_blocks) {
    entry.second->m_entries.gather_methods(methods);
  }
}

void ControlFlowGraph::gather_callsites(
    std::vector<DexCallSite*>& callsites) const {
  for (const auto& entry : m_blocks) {
    entry.second->m_entries.gather_callsites(callsites);
  }
}

void ControlFlowGraph::gather_methodhandles(
    std::vector<DexMethodHandle*>& methodhandles) const {
  for (const auto& entry : m_blocks) {
    entry.second->m_entries.gather_methodhandles(methodhandles);
  }
}

cfg::InstructionIterator
ControlFlowGraph::primary_instruction_of_move_result_for_type_check(
    const cfg::InstructionIterator& it) {
  auto* move_result_insn = it->insn;
  always_assert(opcode::is_move_result_any(move_result_insn->opcode()));
  auto* block = it.block();
  if (block->get_first_insn()->insn == move_result_insn) {
    const auto& preds = block->preds();
    always_assert(preds.size() == 1);
    auto* previous_block = preds.front()->src();
    auto res = previous_block->to_cfg_instruction_iterator(
        previous_block->get_last_insn());
    return res;
  } else {
    auto res = std::prev(it);
    always_assert(res.block() == it.block());
    return res;
  }
}

cfg::InstructionIterator ControlFlowGraph::primary_instruction_of_move_result(
    const cfg::InstructionIterator& it) const {
  auto* move_result_insn = it->insn;
  always_assert(opcode::is_move_result_any(move_result_insn->opcode()));
  auto* block = it.block();
  if (block->get_first_insn()->insn == move_result_insn) {
    const auto& preds = block->preds();
    always_assert(preds.size() == 1);
    auto* previous_block = preds.front()->src();
    auto res = previous_block->to_cfg_instruction_iterator(
        previous_block->get_last_insn());
    auto* insn = res->insn;
    always_assert(insn->has_move_result_any());
    return res;
  } else {
    auto res = std::prev(it);
    always_assert(res.block() == it.block());
    auto* insn = res->insn;
    always_assert(insn->has_move_result_any());
    return res;
  }
}

cfg::InstructionIterator ControlFlowGraph::next_following_gotos(
    const cfg::InstructionIterator& it) const {
  auto next_it = std::next(it);
  if (!next_it.is_end() && next_it.block() == it.block()) {
    return next_it;
  }
  // We reached the end of the current block; let's look at the immediate
  // goto-target.
  auto* block = it.block()->goes_to();
  if (block == nullptr) {
    return InstructionIterable(it.cfg()).end();
  }
  auto first_insn_it = block->get_first_insn();
  if (first_insn_it != block->end()) {
    return block->to_cfg_instruction_iterator(first_insn_it);
  }
  // The immediate goto-target block was empty, so we have to continue our
  // chase. We have to check for non-terminating self-loops while doing that.
  UnorderedSet<cfg::Block*> visited{block};
  while (true) {
    block = block->goes_to();
    if ((block == nullptr) || !visited.insert(block).second) {
      // non-terminating empty self-loop
      return InstructionIterable(it.cfg()).end();
    }
    first_insn_it = block->get_first_insn();
    if (first_insn_it != block->end()) {
      return block->to_cfg_instruction_iterator(first_insn_it);
    }
  }
}

cfg::InstructionIterator ControlFlowGraph::move_result_of(
    const cfg::InstructionIterator& it) const {
  auto next_it = next_following_gotos(it);
  if (next_it.is_end()) {
    return next_it;
  }
  if (opcode::is_move_result_any(next_it->insn->opcode())) {
    always_assert(primary_instruction_of_move_result(next_it) == it);
    return next_it;
  }
  return InstructionIterable(it.cfg()).end();
}

/*
 * fill `new_cfg` with a copy of `this`
 */
void ControlFlowGraph::deep_copy(ControlFlowGraph* new_cfg) const {
  new_cfg->clear();
  new_cfg->set_registers_size(this->get_registers_size());

  UnorderedMap<const Edge*, Edge*> old_edge_to_new;
  size_t num_edges = this->m_edges.size();
  new_cfg->m_edges.reserve(num_edges);
  old_edge_to_new.reserve(num_edges);
  for (const Edge* old_edge : UnorderedIterable(this->m_edges)) {
    // this shallowly copies block pointers inside, then we patch them later
    Edge* new_edge = new Edge(*old_edge);
    new_cfg->m_edges.insert(new_edge);
    old_edge_to_new.emplace(old_edge, new_edge);
  }

  // copy the code itself
  MethodItemEntryCloner cloner;
  for (const auto& entry : this->m_blocks) {
    const Block* block = entry.second;
    // this shallowly copies edge pointers inside, then we patch them later
    Block* new_block = new Block(*block, &cloner);
    new_block->m_parent = new_cfg;
    new_cfg->m_blocks.emplace(new_block->id(), new_block);
  }
  // We need a second pass because parent position pointers may refer to
  // positions in a block that would be processed later.
  cloner.fix_parent_positions();

  // patch the edge pointers in the blocks to their new cfg counterparts
  for (auto& entry : new_cfg->m_blocks) {
    Block* b = entry.second;
    for (Edge*& e : b->m_preds) {
      e = old_edge_to_new.at(e);
    }
    for (Edge*& e : b->m_succs) {
      e = old_edge_to_new.at(e);
    }
  }

  // patch the block pointers in the edges to their new cfg counterparts
  for (Edge* e : UnorderedIterable(new_cfg->m_edges)) {
    e->set_src(new_cfg->m_blocks.at(e->src()->id()));
    e->set_target(new_cfg->m_blocks.at(e->target()->id()));
  }

  // update the entry and exit block pointers to their new cfg counterparts
  new_cfg->m_entry_block = new_cfg->m_blocks.at(this->m_entry_block->id());
  if (this->m_exit_block != nullptr) {
    new_cfg->m_exit_block = new_cfg->m_blocks.at(this->m_exit_block->id());
  }
}

InstructionIterator ControlFlowGraph::find_insn(const IRInstruction* insn,
                                                Block* hint) {
  if (hint != nullptr) {
    auto ii = ir_list::InstructionIterable(hint);
    for (auto it = ii.begin(); it != ii.end(); ++it) {
      if (it->insn == insn) {
        return hint->to_cfg_instruction_iterator(it);
      }
    }
  }

  auto iterable = InstructionIterable(*this);
  for (auto it = iterable.begin(); it != iterable.end(); ++it) {
    if (it->insn == insn) {
      return it;
    }
  }
  return iterable.end();
}

ConstInstructionIterator ControlFlowGraph::find_insn(const IRInstruction* insn,
                                                     Block* hint) const {
  if (hint != nullptr) {
    auto ii = ir_list::InstructionIterable(hint);
    for (auto it = ii.begin(); it != ii.end(); ++it) {
      if (it->insn == insn) {
        return hint->to_cfg_instruction_iterator(it);
      }
    }
  }

  auto iterable = ConstInstructionIterable(*this);
  for (auto it = iterable.begin(); it != iterable.end(); ++it) {
    if (it->insn == insn) {
      return it;
    }
  }
  return iterable.end();
}

std::vector<Block*> ControlFlowGraph::order(
    LinearizationStrategy* custom_strategy, bool assume_no_unreachable_blocks) {
  if (!assume_no_unreachable_blocks) {
    // We must simplify first to remove any unreachable blocks
    simplify();
  }

  // This is a modified Weak Topological Ordering (WTO). We create "chains" of
  // blocks that will be kept together, then feed these chains to WTO for it to
  // choose the ordering of the chains. Then, we deconstruct the chains to get
  // an ordering of the blocks.

  // hold the chains of blocks here, though they mostly will be accessed via the
  // map
  std::vector<std::unique_ptr<BlockChain>> chains;
  // keep track of which blocks are in each chain, for quick lookup.
  UnorderedMap<Block*, BlockChain*> block_to_chain;
  block_to_chain.reserve(m_blocks.size());

  build_chains(&chains, &block_to_chain);
  auto wto = build_wto(block_to_chain);
  auto result = custom_strategy != nullptr
                    ? custom_strategy->order(*this, std::move(wto))
                    : wto_chains(std::move(wto));

  always_assert_log(result.size() == m_blocks.size(),
                    "result has %zu blocks, m_blocks has %zu", result.size(),
                    m_blocks.size());

  // The entry block must always be first.
  redex_assert(m_entry_block == std::as_const(result).at(0));

  return result;
}

void ControlFlowGraph::build_chains(
    std::vector<std::unique_ptr<BlockChain>>* chains,
    UnorderedMap<Block*, BlockChain*>* block_to_chain) {
  auto handle_block = [&](Block* b) {
    if (block_to_chain->count(b) != 0) {
      return;
    }

    always_assert_log(!ControlFlowGraph::s_DEBUG ||
                          !b->starts_with_move_result(),
                      "%zu is wrong %s", b->id(), SHOW(*this));
    auto unique = std::make_unique<BlockChain>();
    BlockChain* chain = unique.get();
    chains->push_back(std::move(unique));

    chain->push_back(b);
    block_to_chain->emplace(b, chain);

    auto* goto_edge = get_succ_edge_of_type(b, EDGE_GOTO);
    while (goto_edge != nullptr) {
      // make sure we handle a chain of blocks that all start with move-results
      auto* goto_block = goto_edge->target();
      always_assert_log(!ControlFlowGraph::s_DEBUG ||
                            m_blocks.count(goto_block->id()) > 0,
                        "bogus block reference %zu -> %zu in %s",
                        goto_edge->src()->id(), goto_block->id(), SHOW(*this));
      if (goto_block->starts_with_move_result() || goto_block->same_try(b)) {
        // If the goto edge leads to a block with a move-result(-pseudo), then
        // that block must be placed immediately after this one because we can't
        // insert anything between an instruction and its move-result(-pseudo).
        //
        // We also add gotos that are in the same try because we can minimize
        // instructions (by using fallthroughs) without adding another try
        // region. This is not required, but empirical evidence shows that it
        // generates smaller dex files.
        const auto& pair = block_to_chain->emplace(goto_block, chain);
        bool was_already_there = !pair.second;
        if (was_already_there) {
          if (goto_block->starts_with_move_result() &&
              chain != block_to_chain->at(goto_block)) {
            // We cannot allow this to be in a separate chain. The WTO (and its
            // walk) cannot enforce the correct ordering, e.g., it might put a
            // throw block in the middle.
            TRACE(CFG, 5, "Need to collapse goto chain with move result!");
            auto* goto_chain = block_to_chain->at(goto_block);
            redex_assert(CONSTP(goto_chain)->at(0) == goto_block);
            for (auto* gcb : *goto_chain) {
              chain->push_back(gcb);
              (*block_to_chain)[gcb] = chain;
            }
            auto it = std::find_if(
                chains->begin(), chains->end(),
                [&](const auto& uptr) { return uptr.get() == goto_chain; });
            redex_assert(it != chains->cend());
            chains->erase(it);
          }
          break;
        }
        chain->push_back(goto_block);
        goto_edge = get_succ_edge_of_type(goto_block, EDGE_GOTO);
      } else {
        break;
      }
    }
  };

  // It is important to always start with the entry block. Otherwise it may
  // be incorrectly merged into a chain.
  redex_assert(m_entry_block != nullptr);
  if (ControlFlowGraph::s_DEBUG) {
    auto it = m_blocks.find(m_entry_block->id());
    redex_assert(it != m_blocks.cend());
    redex_assert(it->second == m_entry_block);
  }
  handle_block(m_entry_block);

  std::vector<Block*> move_result_blocks_out_of_order;

  for (const auto& entry : m_blocks) {
    // Must not handle blocks that start with a move-result. These need to go
    // into the same chain as the owner.
    if (entry.second->starts_with_move_result()) {
      if (ControlFlowGraph::s_DEBUG) {
        move_result_blocks_out_of_order.push_back(entry.second);
      }
      continue;
    }

    handle_block(entry.second);
  }

  // All postponed move-result blocks should be in a chain now, or they were
  // dangling and should have been removed.
  if (ControlFlowGraph::s_DEBUG) {
    for (auto* b : move_result_blocks_out_of_order) {
      always_assert_log(block_to_chain->count(b) > 0,
                        "Did not find B%zu in chains of\n%s", b->id(),
                        SHOW(*this));
    }
  }
}

sparta::WeakTopologicalOrdering<BlockChain*> ControlFlowGraph::build_wto(
    const UnorderedMap<Block*, BlockChain*>& block_to_chain) {
  return sparta::WeakTopologicalOrdering<BlockChain*>(
      block_to_chain.at(entry_block()),
      [&block_to_chain](BlockChain* const& chain) {
        // The chain successor function returns all the outgoing edges' target
        // chains. Where outgoing means that the edge does not go to this chain.
        //
        // FIXME: this algorithm ignores real infinite loops in the block graph
        std::vector<BlockChain*> result;
        result.reserve(chain->size());

        // TODO: Sort the outputs by edge type, case key, and throw index
        //  * We may be able to use fewer debug positions if we emit case blocks
        //    in the original order.
        //  * Right now, it seems the switches are being output in reverse
        //    order, which is annoying for writing tests.
        const auto& end = chain->end();
        for (auto it = chain->begin(); it != end;) {
          Block* b = *it;
          const auto& next_it = std::next(it);
          Block* next = (next_it == end) ? nullptr : *next_it;

          for (Edge* e : b->succs()) {
            if (e->target() == next) {
              // The most common intra-chain edge is a GOTO to the very next
              // block. Let's cheaply detect this case and filter it early,
              // before we have to do an expensive map lookup.
              continue;
            }
            const auto& succ_chain = block_to_chain.at(e->target());
            // Filter out any edges within this chain. We don't want to
            // erroneously create infinite loops in the chain graph that don't
            // exist in the block graph.
            if (succ_chain != chain) {
              result.push_back(succ_chain);
            }
          }
          it = next_it;
        }
        return result;
      });
}

std::vector<Block*> ControlFlowGraph::wto_chains(
    sparta::WeakTopologicalOrdering<BlockChain*> wto) {

  std::vector<Block*> main_order;
  main_order.reserve(this->num_blocks());

  auto chain_order = [&main_order](BlockChain* c) {
    for (Block* b : *c) {
      main_order.push_back(b);
    }
  };

  wto.visit_depth_first(chain_order);

  return main_order;
}

// Add an MFLOW_TARGET at the end of each edge.
// Insert GOTOs where necessary.
void ControlFlowGraph::insert_branches_and_targets(
    const std::vector<Block*>& ordering) {
  for (auto it = ordering.begin(); it != ordering.end(); ++it) {
    Block* b = *it;

    for (const Edge* edge : b->succs()) {
      if (edge->type() == EDGE_BRANCH) {
        auto branch_it = b->get_conditional_branch();
        always_assert_log(branch_it != b->end(), "block %zu %s", b->id(),
                          SHOW(*this));
        auto& branch_mie = *branch_it;

        BranchTarget* bt =
            edge->case_key() != std::nullopt
                ? new BranchTarget(&branch_mie, *edge->case_key())
                : new BranchTarget(&branch_mie);
        auto* target_mie = new MethodItemEntry(bt);
        edge->target()->m_entries.push_front(*target_mie);

      } else if (edge->type() == EDGE_GOTO) {
        auto next_it = std::next(it);
        if (next_it != ordering.end()) {
          Block* next = *next_it;
          if (edge->target() == next) {
            // Don't need a goto because this will fall through to `next`
            continue;
          }
        }
        auto* branch_mie = new MethodItemEntry(new IRInstruction(OPCODE_GOTO));
        auto* target_mie = new MethodItemEntry(new BranchTarget(branch_mie));
        edge->src()->m_entries.push_back(*branch_mie);
        edge->target()->m_entries.push_front(*target_mie);
      }
    }
  }
}

// remove all try and catch markers because we may reorder the blocks
void ControlFlowGraph::remove_try_catch_markers() {
  for (const auto& entry : m_blocks) {
    Block* b = entry.second;
    b->m_entries.remove_and_dispose_if([](const MethodItemEntry& mie) {
      return mie.type == MFLOW_TRY || mie.type == MFLOW_CATCH;
    });
  }
}

std::unique_ptr<IRList> ControlFlowGraph::linearize(
    LinearizationStrategy* custom_strategy) {
  sanity_check();
  auto result = std::make_unique<IRList>();

  TRACE_NO_LINE(CFG, 5, "before linearize:\n%s", SHOW(*this));

  auto ordering = this->order(custom_strategy);

  insert_branches_and_targets(ordering);
  insert_try_catch_markers(ordering);

  for (Block* b : ordering) {
    result->splice(result->end(), b->m_entries);
  }
  remove_redundant_positions(result.get());

  return result;
}

void ControlFlowGraph::insert_try_catch_markers(
    const std::vector<Block*>& ordering) {
  // add back the TRY START, TRY_ENDS, and, MFLOW_CATCHes

  const auto& insert_try_marker_between =
      [this](Block* prev, MethodItemEntry* new_try_marker, Block* b) {
        auto first_it = b->get_first_insn();
        if (first_it != b->end() &&
            opcode::is_a_move_result_pseudo(first_it->insn->opcode())) {
          // Make sure we don't split up a move-result-pseudo and its primary
          // instruction by placing the marker after the move-result-pseudo
          //
          // TODO: relax the constraint that move-result-pseudo must be
          // immediately after its partner, allowing non-opcode
          // MethodItemEntries between
          b->m_entries.insert_after(first_it, *new_try_marker);
        } else if (new_try_marker->tentry->type == TRY_START) {
          if (prev == nullptr && b == entry_block()) {
            // Parameter loading instructions come before a TRY_START
            auto params = b->m_entries.get_param_instructions();
            b->m_entries.insert_before(params.end(), *new_try_marker);
          } else {
            // TRY_START belongs at the front of a block
            b->m_entries.push_front(*new_try_marker);
          }
        } else {
          // TRY_END belongs at the end of a block
          prev->m_entries.push_back(*new_try_marker);
        }
      };

  UnorderedMap<MethodItemEntry*, Block*> catch_to_containing_block;
  Block* prev = nullptr;
  MethodItemEntry* active_catch = nullptr;
  for (auto it = ordering.begin(); it != ordering.end(); prev = *(it++)) {
    Block* b = *it;
    MethodItemEntry* new_catch = create_catch(b, &catch_to_containing_block);

    if (new_catch == nullptr && b->cannot_throw() && !b->is_catch()) {
      // Generate fewer try regions by merging blocks that cannot throw into the
      // previous try region.
      //
      // But, we have to be careful to not include the catch block of this try
      // region, which would create invalid Dex Try entries. For any given try
      // region, none of its catches may be inside that region.
      continue;
    }

    if (active_catch != new_catch) {
      // If we're switching try regions between these blocks, the TRY_END must
      // come first then the TRY_START. We insert the TRY_START earlier because
      // we're using `insert_after` which inserts things in reverse order
      if (new_catch != nullptr) {
        // Start a new try region before b
        auto* new_start = new MethodItemEntry(TRY_START, new_catch);
        insert_try_marker_between(prev, new_start, b);
      }
      if (active_catch != nullptr) {
        // End the current try region before b
        auto* new_end = new MethodItemEntry(TRY_END, active_catch);
        insert_try_marker_between(prev, new_end, b);
      }
      active_catch = new_catch;
    }
  }
  if (active_catch != nullptr) {
    always_assert_log(active_catch->centry->next != active_catch,
                      "Invalid cycle: %s", SHOW(active_catch));
    ordering.back()->m_entries.push_back(
        *new MethodItemEntry(TRY_END, active_catch));
  }
}

MethodItemEntry* ControlFlowGraph::create_catch(
    Block* block,
    UnorderedMap<MethodItemEntry*, Block*>* catch_to_containing_block) {
  using EdgeVector = std::vector<Edge*>;
  EdgeVector throws = get_succ_edges_of_type(block, EDGE_THROW);
  if (throws.empty()) {
    // No need to create a catch if there are no throws
    return nullptr;
  }

  std::sort(throws.begin(), throws.end(), [](const Edge* e1, const Edge* e2) {
    return e1->throw_info()->index < e2->throw_info()->index;
  });
  const auto& throws_end = throws.end();

  // recurse through `throws` adding catch entries to blocks at the ends of
  // throw edges and connecting the catch entry `next` pointers according to the
  // throw edge indices.
  //
  // We stop early if we find an equivalent linked list of catch entries
  return self_recursive_fn(
      [this, &throws_end, catch_to_containing_block](
          auto self, const EdgeVector::iterator& it) -> MethodItemEntry* {
        if (it == throws_end) {
          return nullptr;
        }
        auto* edge = *it;
        auto* catch_block = edge->target();
        for (auto& mie : *catch_block) {
          // Is there already a catch here that's equivalent to the catch we
          // would create?
          if (mie.type == MFLOW_CATCH &&
              catch_entries_equivalent_to_throw_edges(
                  this, &mie, it, throws_end, *catch_to_containing_block)) {
            // The linked list of catch entries starting at `mie` is equivalent
            // to the rest of `throws` from `it` to `end`. So we don't need to
            // create another one, use the existing list.
            return &mie;
          }
        }
        // We recurse and find the next catch before creating this catch because
        // otherwise, we could create a cycle of the catch entries.
        MethodItemEntry* next = self(self, std::next(it));

        // create a new catch entry and insert it into the bytecode
        auto* new_catch = new MethodItemEntry(edge->throw_info()->catch_type);
        new_catch->centry->next = next;
        catch_block->m_entries.push_front(*new_catch);
        catch_to_containing_block->emplace(new_catch, catch_block);
        return new_catch;
      },
      throws.begin());
}

std::vector<Block*> ControlFlowGraph::blocks() const {
  std::vector<Block*> result;
  result.reserve(m_blocks.size());
  for (const auto& entry : m_blocks) {
    Block* b = entry.second;
    result.emplace_back(b);
  }
  return result;
}

// Uses a standard depth-first search with a side table of already-visited
// nodes.
std::vector<Block*> ControlFlowGraph::blocks_reverse_post_deprecated() const {
  std::stack<Block*> stack;
  for (const auto& entry : m_blocks) {
    // include unreachable blocks too
    Block* b = entry.second;
    if (b != entry_block() && b->preds().empty()) {
      stack.push(b);
    }
  }
  stack.push(entry_block());

  std::vector<Block*> postorder;
  postorder.reserve(m_blocks.size());
  UnorderedSet<Block*> visited;
  visited.reserve(m_blocks.size());
  while (!stack.empty()) {
    const auto& curr = stack.top();
    visited.insert(curr);
    bool all_succs_visited = [&] {
      for (auto const& s : curr->succs()) {
        if (visited.count(s->target()) == 0u) {
          stack.push(s->target());
          return false;
        }
      }
      return true;
    }();
    if (all_succs_visited) {
      redex_assert(curr == std::as_const(stack).top());
      postorder.push_back(curr);
      stack.pop();
    }
  }
  std::reverse(postorder.begin(), postorder.end());
  return postorder;
}

ControlFlowGraph::~ControlFlowGraph() {
  free_all_blocks_and_edges_and_removed_insns();
}

Block* ControlFlowGraph::create_block() {
  size_t id = next_block_id();
  Block* b = new Block(this, id);
  m_blocks.emplace(id, b);
  return b;
}

Block* ControlFlowGraph::duplicate_block(Block* original) {
  Block* copy = create_block();
  MethodItemEntryCloner cloner;
  for (const auto& mie : *original) {
    copy->m_entries.push_back(*cloner.clone(&mie));
  }
  return copy;
}

std::vector<Block*> ControlFlowGraph::real_exit_blocks(
    bool include_infinite_loops) {
  std::vector<Block*> result;
  if (m_exit_block != nullptr && include_infinite_loops) {
    auto ghosts = get_pred_edges_of_type(m_exit_block, EDGE_GHOST);
    if (!ghosts.empty()) {
      // The exit block is a ghost block, ignore it and get the real exit
      // points.
      for (auto* e : ghosts) {
        result.push_back(e->src());
      }
    } else {
      // Empty ghosts means the method has a single exit point and
      // calculate_exit_block didn't add a ghost block.
      result.push_back(m_exit_block);
    }
  } else {
    always_assert_log(!include_infinite_loops,
                      "call calculate_exit_block first");
    for (const auto& entry : m_blocks) {
      Block* block = entry.second;
      const auto& b = block->branchingness();
      if (b == opcode::BRANCH_RETURN || b == opcode::BRANCH_THROW) {
        result.push_back(block);
      }
    }
  }
  return result;
}

std::vector<Block*> ControlFlowGraph::return_blocks() const {
  std::vector<Block*> result;
  for (const auto& entry : m_blocks) {
    Block* block = entry.second;
    const auto& b = block->branchingness();
    if (b == opcode::BRANCH_RETURN) {
      result.push_back(block);
    }
  }
  return result;
}

/*
 * Find all exit blocks. Note that it's not as simple as looking for Blocks with
 * return or throw opcodes; infinite loops are a valid way of terminating dex
 * bytecode too. As such, we need to find all strongly connected components
 * (SCCs) and vertices that lack successors. For SCCs that lack successors, any
 * one of its vertices can be treated as an exit block; this implementation
 * picks the head of the SCC.
 */
void ControlFlowGraph::calculate_exit_block() {
  reset_exit_block();
  always_assert(m_exit_block == nullptr);

  // The below code is iterative implementation of the
  // Tarjan algorithm for finding SCCs.

  uint32_t next_dfn{0};
  std::stack<const Block*> stack;

  // Depth-first number. Special values:
  //   0 - unvisited
  //   UINT32_MAX - visited and determined to be in a separate SCC
  UnorderedMap<const Block*, uint32_t> dfns;
  static constexpr uint32_t VISITED = std::numeric_limits<uint32_t>::max();

  auto collectExitBlocks = [&](Block* b) -> std::vector<Block*> {
    // This class stores the algorithm state between iterations.
    // Stack is used to push such objects in order to implement
    // algorithm iteratively.
    struct State {
      Block* b{nullptr};
      const CompactEdgeVector& succs;
      uint32_t element{0};
      uint32_t head{0};
      bool has_exit{false};
    };

    stack.push(b);

    uint32_t head = dfns[b] = ++next_dfn;
    // The head member (initialized with next_dfn tell us whether any
    // vertex in the current SCC has a successor edge that points
    // outside itself. Refer to the Tarjan algorithm for explanation.
    std::stack<State> state_stack;
    State new_state{b, b->succs(), 0, head};
    state_stack.push(new_state);
    std::vector<Block*> exit_blocks;

  continue_while:
    while (!state_stack.empty()) {
      State& top_state = state_stack.top();
      for (uint32_t i = top_state.element; i < top_state.succs.size(); i++) {
        Edge* e = top_state.succs[i];
        uint32_t& succ_dfn = dfns[e->target()];
        uint32_t min{std::numeric_limits<uint32_t>::max()};
        if (succ_dfn == 0) {
          stack.push(e->target());

          succ_dfn = ++next_dfn;
          State succState{e->target(), e->target()->succs(), 0, succ_dfn};
          top_state.element = i + 1;
          state_stack.push(succState);
          goto continue_while; // Recurse into the next child.
        }

        // Done recursing all the children
        top_state.has_exit |= succ_dfn == VISITED;
        min = succ_dfn;
        top_state.head = std::min(min, top_state.head);
      }
      if (top_state.head == dfns[top_state.b]) {
        const Block* top{nullptr};
        if (!top_state.has_exit) {
          exit_blocks.push_back(top_state.b);
          top_state.has_exit = true;
        }
        do {
          top = stack.top();
          stack.pop();
          dfns[top] = VISITED;
        } while (top != top_state.b);
      }

      // Save this "recursive call's" (from the recursive Tarjan
      // algorithm) state into local vars.
      uint32_t succ_head = top_state.head;
      uint32_t succ_has_exit = static_cast<uint32_t>(top_state.has_exit);

      // Pops a state in essence ending a recursive call in the
      // recursive Tarjan algorithm.
      state_stack.pop();
      // Now the topState is invalid.

      // After unwinding one of the recursive calls (see the recursive Tarjan
      // algorithm) and we have not unwound the full recursion update the
      // "current recursive state" with data from the previous "recursion". The
      // recursion state is the original recursive Tarjan algorithm. The State
      // struct keeps the recursive local state, so it can be implemented
      // iteratively.
      if (!state_stack.empty()) {
        State& parent_top_state = state_stack.top();
        parent_top_state.head = std::min(parent_top_state.head, succ_head);
        parent_top_state.has_exit |= succ_has_exit;
      }
      // This is the end of a recursive call from the original algorithm.
    }

    return exit_blocks;
  };

  std::vector<Block*> exit_blocks = collectExitBlocks(entry_block());

  if (exit_blocks.size() == 1) {
    m_exit_block = exit_blocks[0];
  } else {
    m_exit_block = create_block();
    for (Block* b : exit_blocks) {
      add_edge(b, m_exit_block, EDGE_GHOST);
    }
  }
}

void ControlFlowGraph::reset_exit_block() {
  if (m_exit_block == nullptr) {
    return;
  }
  if (get_pred_edge_of_type(m_exit_block, EDGE_GHOST) == nullptr) {
    m_exit_block = nullptr;
    return;
  }
  // If we get here, we have a "ghost" exit block, that was created to represent
  // multiple exit blocks. We need to remove that "ghost" exit block before
  // recomputing the exit of a CFG with multiple exit points.
  remove_block(m_exit_block);
  always_assert(m_exit_block == nullptr);
}

// public API edge removal functions
void ControlFlowGraph::delete_edge(Edge* edge) {
  remove_edge(edge);
  free_edge(edge);
}

void ControlFlowGraph::delete_succ_edges(Block* b) {
  free_edges(remove_succ_edges(b));
}

void ControlFlowGraph::delete_pred_edges(Block* b) {
  free_edges(remove_pred_edges(b));
}

// private edge removal functions
//   These are raw removal, they don't free the edge.
ControlFlowGraph::EdgeSet ControlFlowGraph::remove_edges_between(Block* p,
                                                                 Block* s,
                                                                 bool cleanup) {
  return remove_edge_if(p, s, [](const Edge*) { return true; }, cleanup);
}

void ControlFlowGraph::delete_edges_between(Block* p, Block* s) {
  free_edges(remove_edges_between(p, s));
}

void ControlFlowGraph::remove_edge(Edge* edge, bool cleanup) {
  remove_edge_if(
      edge->src(), edge->target(), [edge](const Edge* e) { return edge == e; },
      cleanup);
}

void ControlFlowGraph::free_all_blocks_and_edges_and_removed_insns() {
  if (m_owns_insns) {
    for (const auto& entry : m_blocks) {
      Block* b = entry.second;
      b->free();
      delete b;
    }
  } else {
    for (const auto& entry : m_blocks) {
      Block* b = entry.second;
      delete b;
    }
  }

  for (Edge* e : UnorderedIterable(m_edges)) {
    delete e;
  }

  if (m_owns_removed_insns) {
    for (auto* insn : m_removed_insns) {
      delete insn;
    }
    m_removed_insns.clear();
  }
}

void ControlFlowGraph::clear() {
  free_all_blocks_and_edges_and_removed_insns();

  m_blocks.clear();
  m_edges.clear();

  m_registers_size = 0;

  m_entry_block = nullptr;
  m_exit_block = nullptr;
}

namespace {

Edge* get_singleton_normal_forward_edge(Block* block) {
  Edge* singleton = nullptr;
  for (auto* succ : block->succs()) {
    if (succ->type() == EDGE_GOTO || succ->type() == EDGE_BRANCH) {
      if (singleton != nullptr) {
        return nullptr;
      }
      singleton = succ;
    }
  }
  return singleton;
}

} // namespace

// After `edges` have been removed from the graph,
//   * Turn BRANCHes/SWITCHes with one outgoing edge into GOTOs
void ControlFlowGraph::cleanup_deleted_edges(const EdgeSet& edges) {
  for (Edge* e : UnorderedIterable(edges)) {
    auto* pred_block = e->src();
    auto last_it = pred_block->get_last_insn();
    if (last_it != pred_block->end()) {
      auto* last_insn = last_it->insn;
      auto op = last_insn->opcode();
      if (!opcode::is_a_conditional_branch(op) && !opcode::is_switch(op)) {
        continue;
      }
      auto* fwd_edge = get_singleton_normal_forward_edge(pred_block);
      if (fwd_edge != nullptr) {
        m_removed_insns.push_back(last_insn);
        pred_block->m_entries.erase_and_dispose(last_it);
        fwd_edge->set_type(EDGE_GOTO);
        fwd_edge->set_case_key(std::nullopt);
      }
    }
  }
}

void ControlFlowGraph::free_edge(Edge* edge) {
  m_edges.erase(edge);
  delete edge;
}

void ControlFlowGraph::free_edges(const EdgeSet& edges) {
  for (Edge* e : UnorderedIterable(edges)) {
    free_edge(e);
  }
}

Edge* ControlFlowGraph::get_pred_edge_of_type(const Block* block,
                                              EdgeType type) const {
  return get_pred_edge_if(block,
                          [type](const Edge* e) { return e->type() == type; });
}

Edge* ControlFlowGraph::get_succ_edge_of_type(const Block* block,
                                              EdgeType type) const {
  return get_succ_edge_if(block,
                          [type](const Edge* e) { return e->type() == type; });
}

std::vector<Edge*> ControlFlowGraph::get_pred_edges_of_type(
    const Block* block, EdgeType type) const {
  return get_pred_edges_if(block,
                           [type](const Edge* e) { return e->type() == type; });
}

std::vector<Edge*> ControlFlowGraph::get_succ_edges_of_type(
    const Block* block, EdgeType type) const {
  return get_succ_edges_if(block,
                           [type](const Edge* e) { return e->type() == type; });
}

Block* ControlFlowGraph::split_block(Block* old_block,
                                     const IRList::iterator& raw_it) {
  always_assert(raw_it != old_block->end());

  // new_block will be the successor
  Block* new_block = create_block();

  // move the rest of the instructions after the split point into the new block
  new_block->m_entries.splice_selection(new_block->begin(),
                                        old_block->m_entries, std::next(raw_it),
                                        old_block->end());

  // make the outgoing edges come from the new block...
  std::vector<Edge*> to_move(old_block->succs().begin(),
                             old_block->succs().end());
  for (auto* e : to_move) {
    // ... except if we didn't move the branching/throwing instruction; in that
    // case, just rewire the goto, as we are going to create a new one
    if (new_block->empty() && e->type() != EDGE_GOTO) {
      continue;
    }
    set_edge_source(e, new_block);
  }

  // connect the halves of the block we just split up
  add_edge(old_block, new_block, EDGE_GOTO);
  return new_block;
}

Block* ControlFlowGraph::split_block(const cfg::InstructionIterator& it) {
  always_assert(!it.is_end());
  return split_block(it.block(), it.unwrap());
}

Block* ControlFlowGraph::split_block_before(Block* old_block,
                                            const IRList::iterator& raw_it) {
  // Do not split in front of special move-result instructions. This would
  // likely end up being illegal.
  always_assert(raw_it == old_block->end() || raw_it->type != MFLOW_OPCODE ||
                !opcode::is_move_result_any(raw_it->insn->opcode()));

  // new_block will be the predecessor.
  Block* new_block = create_block();

  // move the rest of the instructions after the split point into the new block
  new_block->m_entries.splice_selection(
      new_block->begin(), old_block->m_entries, old_block->begin(), raw_it);

  // make the incoming edges go to the new block...
  std::vector<Edge*> to_move(old_block->preds().begin(),
                             old_block->preds().end());
  for (auto* e : to_move) {
    set_edge_target(e, new_block);
  }

  // Copy outgoing throw edges.
  for (auto* e : old_block->succs()) {
    if (e->type() != EDGE_THROW) {
      continue;
    }
    auto* new_edge = new Edge(*e);
    new_edge->set_src(new_block);
    add_edge(new_edge);
  }

  // connect the halves of the block we just split up
  add_edge(new_block, old_block, EDGE_GOTO);
  return new_block;
}

Block* ControlFlowGraph::split_block_before(
    const cfg::InstructionIterator& it) {
  always_assert(!it.is_end());
  return split_block_before(it.block(), it.unwrap());
}

void ControlFlowGraph::merge_blocks(Block* pred, Block* succ) {
  const auto& not_throws = [](const Edge* e) {
    return e->type() != EDGE_THROW;
  };
  {
    const auto& forwards = get_succ_edges_if(pred, not_throws);
    always_assert(forwards.size() == 1);
    auto* forward_edge = forwards[0];
    always_assert(forward_edge->target() == succ);
    always_assert(forward_edge->type() == EDGE_GOTO);
    const auto& reverses = succ->preds();
    always_assert(reverses.size() == 1);
    auto* reverse_edge = reverses[0];
    always_assert(forward_edge == reverse_edge);
  }

  delete_edges_between(pred, succ);
  // move succ's code into pred
  pred->m_entries.splice(pred->m_entries.end(), succ->m_entries);

  // move succ's outgoing edges to pred.
  // Intentionally copy the vector of edges because set_edge_source edits the
  // edge vectors
  auto succs = get_succ_edges_if(succ, not_throws);
  for (auto* succ_edge : succs) {
    set_edge_source(succ_edge, pred);
  }

  // remove the succ block
  delete_pred_edges(succ);
  delete_succ_edges(succ);
  m_blocks.erase(succ->id());
  delete succ;
}

void ControlFlowGraph::insert_block(Block* pred,
                                    Block* succ,
                                    Block* inserted_block) {
  // Collected all edges between block pred and succ. All those edges should be
  // either EDGE_GOTO or EDGE_BRANCH.
  std::vector<Edge*> to_move;
  for (Edge* e : pred->succs()) {
    if (e->target() != succ) {
      continue;
    }
    always_assert_log(e->type() == EDGE_GOTO || e->type() == EDGE_BRANCH,
                      "invalid block insertion\n");
    to_move.push_back(e);
  }
  always_assert_log(!to_move.empty(),
                    "Can't insert a block between 2 disconnected blocks\n");
  // Redirect the edges from succ to inserted_block.
  for (auto* e : to_move) {
    set_edge_target(e, inserted_block);
  }
  // Add a GOTO
  add_edge(inserted_block, succ, EDGE_GOTO);
}

void ControlFlowGraph::set_edge_target(Edge* edge, Block* new_target) {
  move_edge(edge, nullptr, new_target);
}

void ControlFlowGraph::set_edge_source(Edge* edge, Block* new_source) {
  move_edge(edge, new_source, nullptr);
}

// Move this edge out of the vectors between its old blocks
// and into the vectors between the new blocks
void ControlFlowGraph::move_edge(Edge* edge,
                                 Block* new_source,
                                 Block* new_target) {
  // remove this edge from the graph temporarily but do not delete it because
  // we're going to move it elsewhere
  remove_edge(edge, /* cleanup */ false);

  if (new_source != nullptr) {
    edge->set_src(new_source);
  }
  if (new_target != nullptr) {
    edge->set_target(new_target);
  }

  edge->src()->m_succs.push_back(edge);
  edge->target()->m_preds.push_back(edge);
}

bool ControlFlowGraph::blocks_are_in_same_try(const Block* b1,
                                              const Block* b2) const {
  const auto& throws1 = b1->get_outgoing_throws_in_order();
  const auto& throws2 = b2->get_outgoing_throws_in_order();
  if (throws1.size() != throws2.size()) {
    return false;
  }
  auto it1 = throws1.begin();
  auto it2 = throws2.begin();
  for (; it1 != throws1.end(); ++it1, ++it2) {
    auto* e1 = *it1;
    auto* e2 = *it2;
    if (e1->target() != e2->target() ||
        e1->throw_info()->catch_type != e2->throw_info()->catch_type) {
      return false;
    }
  }
  return true;
}

bool ControlFlowGraph::replace_insns(const InstructionIterator& it,
                                     const std::vector<IRInstruction*>& insns) {
  return replace_insns(it, insns.begin(), insns.end());
}
bool ControlFlowGraph::replace_insn(const InstructionIterator& it,
                                    IRInstruction* insn) {
  return replace_insns(it, {insn});
}

void ControlFlowGraph::remove_insn(const InstructionIterator& it) {
  MethodItemEntry& mie = *it;
  auto* insn = mie.insn;
  auto op = insn->opcode();
  always_assert_log(op != OPCODE_GOTO,
                    "There are no GOTO instructions in the CFG");
  Block* block = it.block();

  auto last_it = block->get_last_insn();
  always_assert_log(last_it != block->end(), "cannot remove from empty block");
  if (insn == last_it->insn && (opcode::may_throw(op) || op == OPCODE_THROW)) {
    // We're deleting the last instruction that may throw, this block no longer
    // throws. We should remove the throw edges
    delete_succ_edge_if(block,
                        [](const Edge* e) { return e->type() == EDGE_THROW; });
  }

  if (opcode::is_a_conditional_branch(op) || opcode::is_switch(op)) {
    // Remove all outgoing EDGE_BRANCHes
    // leaving behind only an EDGE_GOTO (and maybe an EDGE_THROW?)
    //
    // Don't cleanup because we're deleting the instruction at the end of this
    // function
    singleton_iterable<Block*> iterable(block);
    free_edges(remove_succ_edge_if(
        iterable.begin(), iterable.end(),
        [](const Edge* e) { return e->type() == EDGE_BRANCH; },
        /* cleanup */ false));
  } else if (insn->has_move_result_any()) {
    // delete the move-result(-pseudo) too
    if (insn == last_it->insn) {
      // The move-result(-pseudo) is in the next (runtime) block, if any.
      // We follow the goto edge to the block that should have the
      // move-result(-pseudo).
      //
      // We can't use std::next because that goes to the next block in ID order,
      // which may not be the next runtime block.
      auto* move_result_block = block->goes_to();
      if (move_result_block != nullptr) {
        auto first_it = move_result_block->get_first_insn();
        if (first_it != move_result_block->end() &&
            opcode::is_move_result_any(first_it->insn->opcode())) {
          // We can safely delete this move-result(-pseudo) because it cannot be
          // the move-result(-pseudo) of more than one primary instruction. A
          // CFG with multiple edges to a block beginning with a
          // move-result(-pseudo) is a malformed CFG.
          always_assert_log(move_result_block->preds().size() == 1,
                            "Multiple edges to a move-result-pseudo in %zu. %s",
                            move_result_block->id(), SHOW(*this));
          m_removed_insns.push_back(first_it->insn);
          move_result_block->m_entries.erase_and_dispose(first_it);
        }
      }
    } else {
      // The move-result(-pseudo) is in the same block as this one.
      // This occurs when we're not in a try region.
      auto mrp_it = std::next(it);
      always_assert(mrp_it.block() == block);
      if (opcode::is_move_result_any(mrp_it->insn->opcode())) {
        m_removed_insns.push_back(mrp_it->insn);
        block->m_entries.erase_and_dispose(mrp_it.unwrap());
      }
    }
  }

  // delete the requested instruction
  m_removed_insns.push_back(it->insn);
  block->m_entries.erase_and_dispose(it.unwrap());
}

void ControlFlowGraph::insert_before(const InstructionIterator& it,
                                     std::unique_ptr<DexPosition> pos) {
  Block* block = it.block();
  block->m_entries.insert_before(it.unwrap(), std::move(pos));
}

void ControlFlowGraph::insert_after(const InstructionIterator& it,
                                    std::unique_ptr<DexPosition> pos) {
  Block* block = it.block();
  block->m_entries.insert_after(it.unwrap(), std::move(pos));
}

void ControlFlowGraph::insert_before(Block* block,
                                     const IRList::iterator& it,
                                     std::unique_ptr<DexPosition> pos) {
  block->m_entries.insert_before(it, std::move(pos));
}

void ControlFlowGraph::insert_after(Block* block,
                                    const IRList::iterator& it,
                                    std::unique_ptr<DexPosition> pos) {
  block->m_entries.insert_after(it, std::move(pos));
}

void Block::insert_before(const IRList::iterator& it,
                          std::unique_ptr<SourceBlock> sb) {
  m_entries.insert_before(it, std::move(sb));
}

void Block::insert_after(const IRList::iterator& it,
                         std::unique_ptr<SourceBlock> sb) {
  m_entries.insert_after(it, std::move(sb));
}

void Block::insert_before(const IRList::iterator& it,
                          std::unique_ptr<Remark> remark) {
  m_entries.insert_before(it, std::move(remark));
}

void Block::insert_after(const IRList::iterator& it,
                         std::unique_ptr<Remark> remark) {
  m_entries.insert_after(it, std::move(remark));
}

void ControlFlowGraph::insert_before(const InstructionIterator& it,
                                     std::unique_ptr<SourceBlock> sb) {
  Block* block = it.block();
  block->m_entries.insert_before(it.unwrap(), std::move(sb));
}

void ControlFlowGraph::insert_after(const InstructionIterator& it,
                                    std::unique_ptr<SourceBlock> sb) {
  Block* block = it.block();
  block->m_entries.insert_after(it.unwrap(), std::move(sb));
}

void ControlFlowGraph::insert_before(const InstructionIterator& it,
                                     std::unique_ptr<Remark> remark) {
  Block* block = it.block();
  block->m_entries.insert_before(it.unwrap(), std::move(remark));
}

void ControlFlowGraph::insert_after(const InstructionIterator& it,
                                    std::unique_ptr<Remark> remark) {
  Block* block = it.block();
  block->m_entries.insert_after(it.unwrap(), std::move(remark));
}

void ControlFlowGraph::create_branch(Block* b,
                                     IRInstruction* insn,
                                     Block* fls,
                                     Block* tru) {
  create_branch(b, insn, fls, {{1, tru}});
}

void ControlFlowGraph::create_branch(
    Block* b,
    IRInstruction* insn,
    Block* goto_block,
    const std::vector<std::pair<int32_t, Block*>>& case_to_block) {
  auto op = insn->opcode();
  always_assert_log(opcode::is_branch(op), "%s is not a branch instruction",
                    SHOW(op));
  always_assert_log(!opcode::is_goto(op),
                    "There are no gotos in the CFG. Use add_edge()");

  auto existing_last = b->get_last_insn();
  if (existing_last != b->end()) {
    auto last_op = existing_last->insn->opcode();
    always_assert_log(!(opcode::is_branch(last_op) ||
                        opcode::is_throw(last_op) ||
                        opcode::is_a_return(last_op)),
                      "Can't add branch after %s in Block %zu in %s",
                      SHOW(existing_last->insn), b->id(), SHOW(*this));
  }

  auto* existing_goto_edge = get_succ_edge_of_type(b, EDGE_GOTO);
  if (goto_block != nullptr) {
    if (existing_goto_edge != nullptr) {
      // redirect it
      set_edge_target(existing_goto_edge, goto_block);
    } else {
      add_edge(b, goto_block, EDGE_GOTO);
    }
  } else {
    always_assert_log(existing_goto_edge != nullptr,
                      "%s must have a false case", SHOW(insn));
  }

  b->m_entries.push_back(*new MethodItemEntry(insn));
  if (opcode::is_switch(op)) {
    for (const auto& entry : case_to_block) {
      add_edge(b, entry.second, entry.first);
    }
  } else {
    always_assert(opcode::is_a_conditional_branch(op));
    always_assert_log(case_to_block.size() == 1,
                      "Wrong number of non-goto cases (%zu) for %s",
                      case_to_block.size(), SHOW(op));
    const auto& entry = case_to_block[0];
    always_assert_log(entry.first == 1, "%s only has boolean case key values",
                      SHOW(op));
    add_edge(b, entry.second, EDGE_BRANCH);
  }
}

void ControlFlowGraph::copy_succ_edges(Block* from, Block* to) {
  copy_succ_edges_if(from, to, [](const Edge*) { return true; });
}

void ControlFlowGraph::copy_succ_edges_of_type(Block* from,
                                               Block* to,
                                               EdgeType type) {
  copy_succ_edges_if(from, to,
                     [type](const Edge* edge) { return edge->type() == type; });
}

template <typename EdgePredicate>
void ControlFlowGraph::copy_succ_edges_if(Block* from,
                                          Block* to,
                                          EdgePredicate edge_predicate) {
  const auto& edges = get_succ_edges_if(from, std::move(edge_predicate));

  for (auto e : edges) {
    Edge* copy = new Edge(*e);
    copy->set_src(to);
    add_edge(copy);
  }
}

bool ControlFlowGraph::insert_before(const InstructionIterator& position,
                                     const std::vector<IRInstruction*>& insns) {
  return insert_before(position, insns.begin(), insns.end());
}

bool ControlFlowGraph::insert_after(const InstructionIterator& position,
                                    const std::vector<IRInstruction*>& insns) {
  return insert_after(position, insns.begin(), insns.end());
}

bool ControlFlowGraph::push_front(Block* b,
                                  const std::vector<IRInstruction*>& insns) {
  return push_front(b, insns.begin(), insns.end());
}

bool ControlFlowGraph::push_back(Block* b,
                                 const std::vector<IRInstruction*>& insns) {
  return push_back(b, insns.begin(), insns.end());
}

bool ControlFlowGraph::insert_before(const InstructionIterator& position,
                                     IRInstruction* insn) {
  return insert_before(position, std::vector<IRInstruction*>{insn});
}

bool ControlFlowGraph::insert_after(const InstructionIterator& position,
                                    IRInstruction* insn) {
  return insert_after(position, std::vector<IRInstruction*>{insn});
}

bool ControlFlowGraph::push_front(Block* b, IRInstruction* insn) {
  return push_front(b, std::vector<IRInstruction*>{insn});
}

bool ControlFlowGraph::push_back(Block* b, IRInstruction* insn) {
  return push_back(b, std::vector<IRInstruction*>{insn});
}

uint32_t ControlFlowGraph::remove_blocks(const std::vector<Block*>& blocks) {
  std::vector<std::unique_ptr<DexPosition>> dangling;
  uint32_t insns_removed = 0;

  for (auto* block : blocks) {
    if (block == entry_block()) {
      always_assert(block->succs().size() == 1);
      set_entry_block(block->succs()[0]->target());
    }
    if (block == exit_block()) {
      set_exit_block(nullptr);
    }
    delete_pred_edges(block);
    delete_succ_edges(block);

    for (auto& mie : *block) {
      if (mie.type == MFLOW_OPCODE) {
        m_removed_insns.push_back(mie.insn);
        insns_removed++;
      } else if (mie.type == MFLOW_POSITION) {
        dangling.push_back(std::move(mie.pos));
      }
    }

    auto id = block->id();
    auto num_removed = m_blocks.erase(id);
    always_assert_log(num_removed == 1,
                      "Block %zu wasn't in CFG. Attempted double delete?", id);
    block->m_entries.clear_and_dispose();
    delete block;
  }

  fix_dangling_parents(std::move(dangling));
  return insns_removed;
}

// delete old_block and reroute its predecessors to new_block
uint32_t ControlFlowGraph::replace_blocks(
    const std::vector<std::pair<Block*, Block*>>& old_new_blocks) {
  std::vector<Block*> blocks_to_remove;
  for (const auto& p : old_new_blocks) {
    auto* old_block = p.first;
    auto* new_block = p.second;
    auto to_redirect = old_block->preds();
    for (auto* e : to_redirect) {
      set_edge_target(e, new_block);
    }
    blocks_to_remove.push_back(old_block);
  }
  return remove_blocks(blocks_to_remove);
}

std::ostream& ControlFlowGraph::write_dot_format(std::ostream& o) const {
  o << "digraph {\nnode [shape=box];\n";
  for (auto* block : blocks()) {
    o << "B" << block->id() << " [label=\"B" << block->id();
    if (block == entry_block()) {
      o << " (entry)";
    }
    if (block == exit_block()) {
      o << " (exit)";
    }
    for (auto& mie : *block) {
      o << "\\l" << show(mie);
    }
    o << "\\l\"];\n";
  }

  for (auto* block : blocks()) {
    for (const auto& succ : block->succs()) {
      o << "B" << block->id() << " -> B" << succ->target()->id();
      if (succ->type() != EDGE_GOTO) {
        o << " [label=\"";
        switch (succ->type()) {
        case EDGE_BRANCH:
          o << "br";
          if (succ->case_key() != std::nullopt) {
            o << " " << *succ->case_key();
          }
          break;
        case EDGE_THROW:
          o << "th";
          if (succ->throw_info() != nullptr) {
            o << " ";
            if (succ->throw_info()->catch_type != nullptr) {
              o << show(succ->throw_info()->catch_type);
            } else {
              o << "A";
            }
          }
          break;
        case EDGE_GHOST:
          o << "gh";
          break;

        // For completeness.
        case EDGE_GOTO:
        case EDGE_TYPE_SIZE:
          break;
        }
        o << "\"]";
      }
      o << ";\n";
    }
  }
  o << "}\n";
  return o;
}

ControlFlowGraph::EdgeSet ControlFlowGraph::remove_succ_edges(Block* b,
                                                              bool cleanup) {
  singleton_iterable<Block*> iterable(b);
  return remove_succ_edge_if(
      iterable.begin(), iterable.end(), [](const Edge*) { return true; },
      cleanup);
}

ControlFlowGraph::EdgeSet ControlFlowGraph::remove_pred_edges(Block* b,
                                                              bool cleanup) {
  singleton_iterable<Block*> iterable(b);
  return remove_pred_edge_if(
      iterable.begin(), iterable.end(), [](const Edge*) { return true; },
      cleanup);
}

bool ControlFlowGraph::structural_equals(const ControlFlowGraph& other) const {
  return this->structural_equals(other, std::equal_to<const IRInstruction&>());
}

bool ControlFlowGraph::structural_equals(
    const ControlFlowGraph& other,
    const InstructionEquality& instruction_equals) const {
  if (this->num_blocks() != other.num_blocks() ||
      this->num_edges() != other.num_edges()) {
    return false;
  }

  std::queue<Block*> this_blocks;
  std::queue<Block*> other_blocks;
  UnorderedSet<BlockId> block_visited;
  // Check entry block.
  if (!this->entry_block()->extended_structural_equals(other.entry_block(),
                                                       instruction_equals)) {
    return false;
  }

  // Check exit_block. Then no need to check EDGE_GHOST later.
  if (this->exit_block() != nullptr) {
    if (!this->exit_block()->extended_structural_equals(other.exit_block(),
                                                        instruction_equals)) {
      return false;
    }
  } else if (other.exit_block() != nullptr) {
    return false;
  }

  this_blocks.push(this->entry_block());
  other_blocks.push(other.entry_block());
  block_visited.emplace(this->entry_block()->id());
  while (!this_blocks.empty()) {
    always_assert(!other_blocks.empty());
    auto* b1 = this_blocks.front();
    auto* b2 = other_blocks.front();
    this_blocks.pop();
    other_blocks.pop();
    // Push b1, b2's GOTO successors into queue;
    auto* goto1 = b1->goes_to();
    auto* goto2 = b2->goes_to();
    if (goto1 != nullptr) {
      if (!goto1->extended_structural_equals(goto2, instruction_equals)) {
        return false;
      }
      if (block_visited.count(goto1->id()) == 0) {
        this_blocks.push(goto1);
        other_blocks.push(goto2);
        block_visited.emplace(goto1->id());
      }
    } else if (goto2 != nullptr) {
      return false;
    }

    // Push b1, b2's THROW successors into queue;
    auto throw1_edges = b1->get_outgoing_throws_in_order();
    auto throw2_edges = b2->get_outgoing_throws_in_order();
    if (throw1_edges.size() != throw2_edges.size()) {
      return false;
    }
    for (size_t i = 0; i < throw1_edges.size(); i++) {
      if (throw1_edges[i]->throw_info()->catch_type !=
          throw2_edges[i]->throw_info()->catch_type) {
        return false;
      }
      auto* throw1 = throw1_edges[i]->target();
      auto* throw2 = throw2_edges[i]->target();
      if (!throw1->extended_structural_equals(throw2, instruction_equals)) {
        return false;
      }
      if (block_visited.count(throw1->id()) == 0) {
        this_blocks.push(throw1);
        other_blocks.push(throw2);
        block_visited.emplace(throw1->id());
      }
    }

    // Push b1, b2's BRANCH into queue;
    auto branch1_edges = b1->get_outgoing_branches_in_order();
    auto branch2_edges = b2->get_outgoing_branches_in_order();
    if (branch1_edges.size() != branch2_edges.size()) {
      return false;
    }
    for (size_t i = 0; i < branch1_edges.size(); i++) {
      if (branch1_edges[i]->case_key() != branch2_edges[i]->case_key()) {
        return false;
      }
      auto* branch1 = branch1_edges[i]->target();
      auto* branch2 = branch2_edges[i]->target();
      if (!branch1->extended_structural_equals(branch2, instruction_equals)) {
        return false;
      }
      if (block_visited.count(branch1->id()) == 0) {
        this_blocks.push(branch1);
        other_blocks.push(branch2);
        block_visited.emplace(branch1->id());
      }
    }
  }

  return true;
}

DexPosition* ControlFlowGraph::get_dbg_pos(const cfg::InstructionIterator& it) {
  always_assert(&it.cfg() == this);
  auto search_block = [](Block* b,
                         IRList::iterator in_block_it) -> DexPosition* {
    // Search for an MFLOW_POSITION preceding this instruction within the
    // same block
    while (in_block_it->type != MFLOW_POSITION && in_block_it != b->begin()) {
      --in_block_it;
    }
    return in_block_it->type == MFLOW_POSITION ? in_block_it->pos.get()
                                               : nullptr;
  };
  auto* result = search_block(it.block(), it.unwrap());
  if (result != nullptr) {
    return result;
  }

  // TODO: Positions should be connected to instructions rather than preceding
  // them in the flow of instructions. Having the positions depend on the order
  // of instructions is a very linear way to encode the information which isn't
  // very amenable to the CFG.

  // while there's a single predecessor, follow that edge
  UnorderedSet<Block*> visited;
  std::function<DexPosition*(Block*)> check_prev_block;
  check_prev_block = [this, &visited, &check_prev_block,
                      &search_block](Block* b) -> DexPosition* {
    // Check for an infinite loop
    const auto& pair = visited.insert(b);
    bool already_there = !pair.second;
    if (already_there) {
      return nullptr;
    }

    const auto& reverse_gotos = this->get_pred_edges_of_type(b, EDGE_GOTO);
    if (b->preds().size() == 1 && !reverse_gotos.empty()) {
      Block* prev_block = reverse_gotos[0]->src();
      if (!prev_block->empty()) {
        auto* search_result =
            search_block(prev_block, std::prev(prev_block->end()));
        if (search_result != nullptr) {
          return search_result;
        }
      }
      // Didn't find any MFLOW_POSITIONs in `prev_block`, keep going.
      return check_prev_block(prev_block);
    }
    // This block has no solo predecessors anymore. Nowhere left to search.
    return nullptr;
  };
  return check_prev_block(it.block());
}

} // namespace cfg

namespace {
template <typename InternalIterator>
class IteratorMapper {
 public:
  using difference_type = IROpcode;
  using value_type = IROpcode;
  using pointer = IROpcode*;
  using reference = IROpcode&;
  using iterator_category = std::random_access_iterator_tag;

  explicit IteratorMapper(InternalIterator it) : m_internal_it(std::move(it)) {}
  IteratorMapper(const IteratorMapper<InternalIterator>& other)
      : m_internal_it(other.m_internal_it) {}
  ~IteratorMapper() {}
  IteratorMapper& operator=(const IteratorMapper<InternalIterator>& other) {
    m_internal_it = other.m_internal_it;
    return *this;
  }

  IteratorMapper& operator++() {
    m_internal_it++;
    return *this;
  }

  bool operator!=(const IteratorMapper<InternalIterator>& other) {
    return m_internal_it != other.m_internal_it;
  }

  IROpcode& operator*() {
    m_opcode = m_internal_it->insn->opcode();
    return m_opcode;
  }

 private:
  InternalIterator m_internal_it;
  IROpcode m_opcode;
};

} // namespace

namespace cfg {

std::size_t ControlFlowGraph::opcode_hash() const {
  auto ii = cfg::ConstInstructionIterable(*this);
  return boost::hash_range(IteratorMapper(ii.begin()),
                           IteratorMapper(ii.end()));
}

} // namespace cfg

UnorderedMap<const IRInstruction*, ParamIndex> get_load_param_map(
    const cfg::ControlFlowGraph& cfg) {
  UnorderedMap<const IRInstruction*, ParamIndex> map;
  const auto param_insns = InstructionIterable(cfg.get_param_instructions());
  ParamIndex index = 0;
  for (auto it = param_insns.begin(); it != param_insns.end(); it++) {
    auto* const insn = it->insn;
    always_assert(opcode::is_a_load_param(insn->opcode()));
    map.insert({insn, index++});
  }
  return map;
}
