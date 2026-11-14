/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <type_traits>
#include <utility>
#include <vector>

#include <boost/dynamic_bitset.hpp>
#include <boost/range/sub_range.hpp>
#include <optional>

#include <sparta/WeakTopologicalOrdering.h>

#include "CompactPointerVector.h"
#include "DeterministicContainers.h"
#include "DexPosition.h"
#include "IRCode.h"
#include "SingletonIterable.h"
#include "SourceBlocksUtils.h"
#include "StlUtil.h"

/**
 * A Control Flow Graph is a directed graph of Basic Blocks.
 *
 * Each `Block` has some number of successors and predecessors. `Block`s are
 * connected to their predecessors and successors by `Edge`s that specify
 * the type of connection.
 *
 * A CFG's blocks each own a small IRList (with MethodItemEntries
 * taken from IRCode)
 *
 * In the future, CFGs will replace
 * IRCode entirely as the primary code representation. To build a CFG,
 * call
 *
 * `code->build_cfg()`
 *
 * The CFG takes the MethodItemEntries from the IRCode object and moves
 * them into the blocks. The CFG steals the code out of the IRCode
 * object. After you've built the CFG, you should use the CFG,
 * not the IRCode. The IRCode is empty while the CFG exists.
 *
 * You can make all sorts of changes to the CFG and when
 * you're done, move it all back into an IRCode object with
 *
 * `code->clear_cfg()`
 *
 * It is easier to maintain the data structure when there is no unnecessary
 * information duplication. Therefore, MFLOW_TARGETs, OPCODE_GOTOs, MFLOW_TRYs,
 * and MFLOW_CATCHes are deleted and their information is moved to the edges of
 * the CFG.
 *
 * TODO: Add useful CFG editing methods
 * TODO: phase out edits to the IRCode and move them all to the CFG
 * TODO: remove non-CFG option
 *
 * TODO?: make MethodItemEntry's fields private?
 */

extern std::atomic<size_t> build_cfg_counter;
/*
 * An index into the list of load-param instructions.
 */
using ParamIndex = uint32_t;

/*
 * A helper function that computes the mapping of load param instructions
 * to their respective indices.
 */
UnorderedMap<const IRInstruction*, ParamIndex> get_load_param_map(
    const cfg::ControlFlowGraph& cfg);

namespace source_blocks {
namespace impl {
struct BlockAccessor;
} // namespace impl
} // namespace source_blocks

namespace cfg {

enum EdgeType : uint8_t {
  // The false branch of an if statement, default of a switch, or unconditional
  // goto
  EDGE_GOTO = 0,
  // The true branch of an if statement or non-default case of a switch
  EDGE_BRANCH = 1,
  // The edges to a catch block
  EDGE_THROW = 2,
  // A "fake" edge so that we can have a single exit block
  EDGE_GHOST = 3,
  EDGE_TYPE_SIZE = 4
};

class Block;
class ControlFlowGraph;
class CFGInliner;

namespace details {

// To avoid "Show.h" in the header.
std::string show_cfg(const ControlFlowGraph& cfg);
std::string show_insn(const IRInstruction* insn);

} // namespace details

struct ThrowInfo {
  // nullptr means catch all
  DexType* catch_type;
  // Index from the linked list of `CatchEntry`s in the IRCode. An index of 0
  // denotes the "primary" catch. At runtime, the primary catch is the first
  // block to be checked for equality with the runtime exception type, then onto
  // index 1, etc.
  uint32_t index;

  ThrowInfo(DexType* catch_type, uint32_t index)
      : catch_type(catch_type), index(index) {}

  bool operator==(const ThrowInfo& other) const {
    return catch_type == other.catch_type && index == other.index;
  }
};

class Edge final {
 public:
  using CaseKey = int32_t;
  using MaybeCaseKey = std::optional<CaseKey>;

 private:
  Block* m_src;
  Block* m_target;
  union {
    // If `m_type` is EDGE_THROW then this union points to a ThrowInfo
    // Edge owns this ThrowInfo and is responsible for deleting it.
    ThrowInfo* m_throw_info;
    // If `m_type` is not EDGE_THROW then this union is an optional case key.
    // If this edge is a non-default outgoing edge of an OPCODE_SWITCH, then
    // this is not `std::nullopt`.
    MaybeCaseKey m_case_key;
  };
  EdgeType m_type;

 public:
  Edge(Block* src, Block* target, EdgeType type)
      : m_src(src), m_target(target), m_case_key(std::nullopt), m_type(type) {
    always_assert_log(m_type != EDGE_THROW,
                      "Need a catch type and index to create a THROW edge");
  }
  Edge(Block* src, Block* target, CaseKey case_key)
      : m_src(src),
        m_target(target),
        m_case_key(case_key),
        m_type(EDGE_BRANCH) {}
  Edge(Block* src, Block* target, DexType* catch_type, uint32_t index)
      : m_src(src),
        m_target(target),
        m_throw_info(new ThrowInfo(catch_type, index)),
        m_type(EDGE_THROW) {}

  /*
   * Copy constructor.
   * Notice that this shallowly copies the block pointers!
   */
  Edge(const Edge& e) : m_src(e.m_src), m_target(e.m_target), m_type(e.m_type) {
    if (m_type == EDGE_THROW) {
      m_throw_info = new ThrowInfo(*e.throw_info());
    } else {
      m_case_key = e.case_key();
    }
  }

  ~Edge() {
    if (m_type == EDGE_THROW) {
      delete m_throw_info;
    }
  }

  bool operator==(const Edge& that) const {
    return m_src == that.m_src && m_target == that.m_target &&
           equals_ignore_source_and_target(that);
  }

  bool operator!=(const Edge& that) const { return !(*this == that); }

  bool equals_ignore_source(const Edge& that) const {
    return m_target == that.m_target && equals_ignore_source_and_target(that);
  }

  bool equals_ignore_target(const Edge& that) const {
    return m_src == that.m_src && equals_ignore_source_and_target(that);
  }

  bool equals_ignore_source_and_target(const Edge& that) const {
    if (m_type != that.m_type) {
      return false;
    } else if (m_type == EDGE_THROW) {
      return (throw_info() == nullptr && that.throw_info() == nullptr) ||
             *throw_info() == *that.throw_info();
    } else {
      return case_key() == that.case_key();
    }
  }

  // getters
  Block* src() const { return m_src; }
  Block* target() const { return m_target; }
  EdgeType type() const { return m_type; }
  ThrowInfo* throw_info() const {
    always_assert(m_type == EDGE_THROW);
    return m_throw_info;
  }
  const MaybeCaseKey& case_key() const {
    always_assert(m_type != EDGE_THROW);
    return m_case_key;
  }

  // setters
  void set_case_key(const MaybeCaseKey& k) {
    always_assert(m_type != EDGE_THROW);
    m_case_key = k;
  }
  void set_src(Block* b) { m_src = b; }
  void set_target(Block* b) { m_target = b; }
  void set_type(EdgeType new_type) {
    always_assert_log(!((m_type == EDGE_THROW) ^ (new_type == EDGE_THROW)),
                      "Can't convert to or from throw edge");
    m_type = new_type;
  }
};

std::ostream& operator<<(std::ostream& os, const Edge& e);

using CompactEdgeVector = CompactPointerVector<Edge*>;

using BlockId = size_t;

template <bool is_const>
class InstructionIteratorImpl;
using InstructionIterator = InstructionIteratorImpl</* is_const */ false>;
using ConstInstructionIterator = InstructionIteratorImpl</* is_const */ true>;

template <bool is_const>
class InstructionIterableImpl;
using InstructionIterable = InstructionIterableImpl</* is_const */ false>;
using ConstInstructionIterable = InstructionIterableImpl</* is_const */ true>;

// A piece of "straight-line" code. Targets are only at the beginning of a block
// and branches (throws, gotos, switches, etc) are only at the end of a block.
class Block final {
 public:
  explicit Block(ControlFlowGraph* parent, BlockId id)
      : m_id(id), m_parent(parent) {}

  ~Block() { m_entries.clear_and_dispose(); }
  // This is different from the destructor. It also frees MethodItemEntry
  // payload that is not deleted on MIE deletion.
  void free();

  // copy constructor
  Block(const Block& b, MethodItemEntryCloner* cloner);

  BlockId id() const { return m_id; }
  ControlFlowGraph& cfg() const {
    always_assert(m_parent != nullptr);
    return *m_parent;
  }
  const CompactEdgeVector& preds() const { return m_preds; }
  const CompactEdgeVector& succs() const { return m_succs; }

  bool operator<(const Block& other) const { return this->id() < other.id(); }

  // return true if `b` is a predecessor of this.
  // optionally supply a specific type of predecessor. The default,
  // EDGE_TYPE_SIZE, means any type
  bool has_pred(Block* b, EdgeType t = EDGE_TYPE_SIZE) const;

  // return true if `b` is a successor of this.
  // optionally supply a specific type of successor. The default,
  // EDGE_TYPE_SIZE, means any type
  bool has_succ(Block* b, EdgeType t = EDGE_TYPE_SIZE) const;

  IRList::iterator begin();
  IRList::iterator end();
  IRList::const_iterator begin() const;
  IRList::const_iterator end() const;
  IRList::reverse_iterator rbegin() { return IRList::reverse_iterator(end()); }
  IRList::reverse_iterator rend() { return IRList::reverse_iterator(begin()); }
  IRList::const_reverse_iterator rbegin() const {
    return IRList::const_reverse_iterator(end());
  }
  IRList::const_reverse_iterator rend() const {
    return IRList::const_reverse_iterator(begin());
  }

  bool is_catch() const;

  bool same_try(const Block* other) const;

  // Any removed instruction will be freed when the cfg is destroyed.
  void remove_insn(const InstructionIterator& it);

  // Any removed instruction will be freed when the cfg is destroyed.
  void remove_insn(const ir_list::InstructionIterator& it);

  // Will remove the first entry after it containing an MFLOW_OPCODE,
  // leaving the intervening instructions unmodified. If a non-MFLOW_OPCODE
  // instruction is to be removed, remove_mie should be used instead.
  // Any removed instruction will be freed when the cfg is destroyed.
  void remove_insn(const IRList::iterator& it);

  // Any removed instruction will be freed when the cfg is destroyed.
  IRList::iterator remove_mie(const IRList::iterator& it);

  // Removes a subset of MFLOW_DEBUG instructions from the block. valid_regs
  // is an accumulator set of registers used by either DBG_START_LOCAL
  // or DBG_START_LOCAL_EXTENDED. The DBG_END_LOCAL and DBG_RESTART_LOCAL
  // instructions are erased, unless valid_regs contains the registers they use.
  // Note: When iterating (WTO order) over the blocks of a CFG, if this method
  // is to be applied for each block, then the valid_regs accumulator should be
  // sequentially passed to each of the blocks to incorporate the "global"
  // information of the CFG. That is, if a block is an ancestor of another,
  // then the valid registers that the ancestor block defines should be
  // acknowledged by the descendant block.
  void cleanup_debug(UnorderedSet<reg_t>& valid_regs);

  opcode::Branchingness branchingness() const;

  // returns true if there are no MethodItemEntries (not IRInstructions)
  bool empty() const { return m_entries.empty(); }

  uint32_t num_opcodes() const;

  uint32_t sum_opcode_sizes() const;

  // similar to sum_opcode_sizes, but takes into account non-opcode payloads
  uint32_t estimate_code_units() const;

  bool is_unreachable() const;

  // return an iterator to the last MFLOW_OPCODE, or end() if there are none
  IRList::iterator get_last_insn();
  IRList::const_iterator get_last_insn() const;
  // return an iterator to the first MFLOW_OPCODE, or end() if there are none
  IRList::iterator get_first_insn();
  IRList::const_iterator get_first_insn() const;
  // return an iterator to the first non-param-loading MFLOW_OPCODE, or end() if
  // there are none.
  IRList::iterator get_first_non_param_loading_insn();
  IRList::const_iterator get_first_non_param_loading_insn() const;
  // return an iterator to the last param-loading MFLOW_OPCODE, or end() if
  // there are none.
  IRList::iterator get_last_param_loading_insn();
  IRList::const_iterator get_last_param_loading_insn() const;
  // return an iterator to the first instruction (except move-result* and goto)
  // if it occurs before the first position, or end() if there are none.
  IRList::iterator get_first_insn_before_position();
  IRList::const_iterator get_first_insn_before_position() const;

  // including move-result-pseudo
  bool starts_with_move_result() const;

  bool starts_with_move_exception() const;

  bool contains_opcode(IROpcode opcode) const;

  // returns true iff the block starts with the same MethodItemEntries as the
  // other block.
  bool begins_with(Block* other) const;

  // If this block has a single outgoing edge and it is a goto, return its
  // target. Otherwise, return nullptr
  Block* goes_to_only_edge() const;
  // If this block has an outgoing goto edge, return its target.
  // Otherwise, return nullptr
  Block* goes_to() const;

  // If this block contains no instructions that can throw.
  bool cannot_throw() const;

  // TODO?: Should we just always store the throws in index order?
  std::vector<Edge*> get_outgoing_throws_in_order() const;

  std::vector<Edge*> get_outgoing_branches_in_order() const;

  // These assume that the iterator is inside this block
  InstructionIterator to_cfg_instruction_iterator(
      const ir_list::InstructionIterator& list_it, bool next_on_end = false);
  InstructionIterator to_cfg_instruction_iterator(
      const IRList::iterator& list_it, bool next_on_end = false);
  InstructionIterator to_cfg_instruction_iterator(MethodItemEntry& mie);

  // These forward to implementations in ControlFlowGraph, See comment there
  template <class ForwardIt>
  bool insert_before(const InstructionIterator& position,
                     const ForwardIt& begin,
                     const ForwardIt& end);

  bool insert_before(const InstructionIterator& position,
                     const std::vector<IRInstruction*>& insns);

  bool insert_before(const InstructionIterator& position, IRInstruction* insn);

  template <class ForwardIt>
  bool insert_after(const InstructionIterator& position,
                    const ForwardIt& begin,
                    const ForwardIt& end);

  bool insert_after(const InstructionIterator& position,
                    const std::vector<IRInstruction*>& insns);

  bool insert_after(const InstructionIterator& position, IRInstruction* insn);

  template <class ForwardIt>
  bool push_front(const ForwardIt& begin, const ForwardIt& end);
  bool push_front(const std::vector<IRInstruction*>& insns);
  bool push_front(IRInstruction* insn);

  template <class ForwardIt>
  bool push_back(const ForwardIt& begin, const ForwardIt& end);
  bool push_back(const std::vector<IRInstruction*>& insns);
  bool push_back(IRInstruction* insn);

  void insert_before(const IRList::iterator& it,
                     std::unique_ptr<SourceBlock> sb);
  void insert_after(const IRList::iterator& it,
                    std::unique_ptr<SourceBlock> sb);

  void insert_before(const IRList::iterator& it,
                     std::unique_ptr<Remark> remark);
  void insert_after(const IRList::iterator& it, std::unique_ptr<Remark> remark);

  bool structural_equals(const Block* other) const;
  bool structural_equals(const Block* other,
                         const InstructionEquality& instruction_equals) const;

  bool extended_structural_equals(
      const Block* other, const InstructionEquality& instruction_equals) const;

 private:
  friend class ControlFlowGraph;
  friend class CFGInliner;
  friend class InstructionIteratorImpl<false>;
  friend class InstructionIteratorImpl<true>;
  friend struct ::source_blocks::impl::BlockAccessor;

  // return an iterator to the conditional branch (including switch) in this
  // block. If there is no such instruction, return end()
  IRList::iterator get_conditional_branch();

  BlockId m_id;

  // MethodItemEntries get moved from IRCode into here
  // otherwise, this is empty.
  IRList m_entries;

  CompactEdgeVector m_preds;
  CompactEdgeVector m_succs;

  // the graph that this block belongs to
  ControlFlowGraph* m_parent = nullptr;
};

struct DominatorInfo {
  Block* dom;
  size_t postorder;
};

using BlockChain = std::vector<Block*>;

struct LinearizationStrategy {
  virtual ~LinearizationStrategy() {}
  virtual std::vector<Block*> order(
      cfg::ControlFlowGraph& cfg,
      sparta::WeakTopologicalOrdering<BlockChain*> wto) = 0;
};

class ControlFlowGraph {

 public:
  static bool s_DEBUG;

  ControlFlowGraph() = default;
  ControlFlowGraph(const ControlFlowGraph&) = delete;

  ControlFlowGraph(IRList* ir, reg_t registers_size);
  ~ControlFlowGraph();

  /*
   * convert from the graph representation to a list of MethodItemEntries
   * Using custom_strategy allows custom order linearization of the CFG.
   */
  std::unique_ptr<IRList> linearize(
      LinearizationStrategy* custom_strategy = nullptr);

  // Return the blocks of this CFG in an arbitrary order.
  //
  // NOTE: this function copies pointers to blocks from m_blocks.
  // If a block is created or destroyed while we're iterating on a copy, the
  // copy is now stale. That stale copy may have a pointer to a deleted block or
  // it may be incomplete (not iterating over the newly created block).
  //
  // TODO: We should probably have an API to offer iterators into the blocks map
  // instead for reads or some mutations since insertion and erasure of elements
  // stored in std::map will not invalidate the iterators referencing other
  // elements.
  std::vector<Block*> blocks() const;

  auto blocks_view() const { return std23::map_values(m_blocks); }

  // Return vector of blocks in reverse post order (RPO). If there is a path
  // from Block A to Block B, then A appears before B in this vector.
  //
  //
  // DEPRECATED: Use graph::postorder_sort instead, which is faster. The only
  // functional difference is that the new version doesn't include unreachable
  // blocks in the sorted output.
  std::vector<Block*> blocks_reverse_post_deprecated() const;

  Block* create_block();

  // Create a new block (with a unique ID) that has a copy of the code inside
  // `original` The edges are not copied. The new block has no incoming or
  // outgoing edges
  Block* duplicate_block(Block* original);

  Block* entry_block() const { return m_entry_block; }
  Block* exit_block() const { return m_exit_block; }
  void set_entry_block(Block* b) { m_entry_block = b; }
  void set_exit_block(Block* b) { m_exit_block = b; }
  void reset_exit_block();

  /*
   * If there is a single method exit point, this returns a vector holding the
   * exit block. If there are multiple method exit points, this returns a vector
   * of them, ignoring the "ghost" exit block introduced by
   * `calculate_exit_block()`.
   */
  std::vector<Block*> real_exit_blocks(bool include_infinite_loops = false);

  std::vector<Block*> return_blocks() const;

  /*
   * Determine where the exit block is. If there is more than one, create a
   * "ghost" block that is the successor to all of them.
   *
   * The exit blocks are not computed upon creation. It is left up to the user
   * to call this method if they plan to use the exit block. If you make
   * significant changes to this CFG that affect the exit
   * points of the method, you need to call this method again.
   * TODO: detect changes and recompute when necessary.
   */
  void calculate_exit_block();

  // args are arguments to an Edge constructor
  template <class... Args>
  void add_edge(Args&&... args) {
    add_edge(new Edge(std::forward<Args>(args)...));
  }

  void add_edge(Edge* e) {
    m_edges.insert(e);
    e->src()->m_succs.push_back(e);
    e->target()->m_preds.push_back(e);
  }

  // copies all edges from one block to another
  void copy_succ_edges(Block* from, Block* to);

  // copies all edges of a certain type from one block to another
  void copy_succ_edges_of_type(Block* from, Block* to, EdgeType type);

  // copies all edges that match the predicate from one block to another
  template <typename EdgePredicate>
  void copy_succ_edges_if(Block* from, Block* to, EdgePredicate edge_predicate);

  using EdgeSet = UnorderedSet<Edge*>;

  // Make `e` point to a new target block.
  // The source block is unchanged.
  void set_edge_target(Edge* e, Block* new_target);

  // Make `e` come from a new source block
  // The target block is unchanged.
  void set_edge_source(Edge* e, Block* new_source);

  // return the first edge for which predicate returns true
  // or nullptr if no such edge exists
  template <typename EdgePredicate>
  Edge* get_pred_edge_if(const Block* block, EdgePredicate predicate) const {
    for (Edge* e : block->preds()) {
      if (predicate(e)) {
        return e;
      }
    }
    return nullptr;
  }

  template <typename EdgePredicate>
  Edge* get_succ_edge_if(const Block* block, EdgePredicate predicate) const {
    for (Edge* e : block->succs()) {
      if (predicate(e)) {
        return e;
      }
    }
    return nullptr;
  }

  // return all edges for which predicate returns true
  template <typename EdgePredicate>
  std::vector<Edge*> get_pred_edges_if(const Block* block,
                                       EdgePredicate predicate) const {
    const auto& preds = block->preds();
    std::vector<Edge*> result;
    for (Edge* e : preds) {
      if (predicate(e)) {
        result.push_back(e);
      }
    }
    return result;
  }

  template <typename EdgePredicate>
  std::vector<Edge*> get_succ_edges_if(const Block* block,
                                       EdgePredicate predicate) const {
    const auto& succs = block->succs();
    std::vector<Edge*> result;
    for (Edge* e : succs) {
      if (predicate(e)) {
        result.push_back(e);
      }
    }
    return result;
  }

  // return the first edge of the given type
  // or nullptr if no such edge exists
  Edge* get_pred_edge_of_type(const Block* block, EdgeType type) const;
  Edge* get_succ_edge_of_type(const Block* block, EdgeType type) const;

  // return all edges of the given type
  std::vector<Edge*> get_pred_edges_of_type(const Block* block,
                                            EdgeType type) const;
  std::vector<Edge*> get_succ_edges_of_type(const Block* block,
                                            EdgeType type) const;

  // delete_..._edge:
  //   * These functions remove edges from the graph and free the memory
  //   * the `_if` functions take a predicate to decide which edges to delete
  void delete_edge(Edge* edge);
  void delete_succ_edges(Block* b);
  void delete_pred_edges(Block* b);
  void delete_edges_between(Block* p, Block* s);

  template <class ForwardIt>
  void delete_edges(const ForwardIt& begin, const ForwardIt& end) {
    UnorderedSet<cfg::Edge*> edges;
    UnorderedSet<cfg::Block*> srcs;
    for (auto it = begin; it != end; it++) {
      auto e = *it;
      edges.insert(e);
      srcs.insert(e->src());
    }
    auto&& srcs_ui = UnorderedIterable(srcs);
    delete_succ_edge_if(srcs_ui.begin(), srcs_ui.end(),
                        [&](Edge* e) { return edges.count(e); });
  }

  template <typename EdgePredicate>
  void delete_edge_if(Block* source, Block* target, EdgePredicate predicate) {
    free_edges(remove_edge_if(source, target, std::move(predicate)));
  }

  template <typename EdgePredicate>
  void delete_succ_edge_if(cfg::Block* b, EdgePredicate predicate) {
    singleton_iterable<Block*> iterable(b);
    delete_succ_edge_if(iterable.begin(), iterable.end(), std::move(predicate));
  }

  template <class ForwardIt, typename EdgePredicate>
  void delete_succ_edge_if(const ForwardIt& begin,
                           const ForwardIt& end,
                           EdgePredicate predicate) {
    free_edges(remove_succ_edge_if(begin, end, std::move(predicate)));
  }

  template <typename EdgePredicate>
  void delete_pred_edge_if(cfg::Block* b, EdgePredicate predicate) {
    singleton_iterable<Block*> iterable(b);
    delete_pred_edge_if(iterable.begin(), iterable.end(), std::move(predicate));
  }

  template <class ForwardIt, typename EdgePredicate>
  void delete_pred_edge_if(const ForwardIt& begin,
                           const ForwardIt& end,
                           EdgePredicate predicate) {
    free_edges(remove_pred_edge_if(begin, end, std::move(predicate)));
  }

  bool blocks_are_in_same_try(const Block* b1, const Block* b2) const;

  /*
   * Split this block into two blocks. After this call, `it` will be the last
   * instruction in the predecessor block.
   *
   * The existing block will become the predecessor. All code after `it` will be
   * moved into the new block (the successor). Return the (new) successor.
   */
  Block* split_block(const cfg::InstructionIterator& it);
  Block* split_block(Block* block, const IRList::iterator& it);

  // Same as above, splits so that `it` will be the first instruction in the
  // successor block. The new block is the predecessor and will be returned.
  //
  // Note: Incoming edges are changed. Outgoing edges of type EDGE_THROW are
  //       duplicated.
  Block* split_block_before(const cfg::InstructionIterator& it);
  Block* split_block_before(Block* block, const IRList::iterator& it);

  // Merge `succ` into `pred` and delete `succ`
  //
  // `pred` must be the only predecessor of `succ`
  // `succ` must be the only successor of `pred`
  // `pred` and `succ` must be in the same try region
  void merge_blocks(Block* pred, Block* succ);

  // Insert \p inserted_block between \p pred and \p succ, where there are only
  // EDGE_GOTO or EDGE_BRANCH between \p pred and \p succ. After insertion, all
  // edges from \p pred to \p succ will be redirected to \p inserted_block, and
  // there will be a GOTO edge added from inserted_block to succ.
  void insert_block(Block* pred, Block* succ, Block* inserted_block);

  // remove the IRInstruction that `it` points to.
  //
  // If `it` points to a branch instruction, remove the corresponding outgoing
  // edges.
  //
  // Any removed instruction will be freed when the cfg is destroyed.
  void remove_insn(const InstructionIterator& it);

  void insert_before(const InstructionIterator& it,
                     std::unique_ptr<DexPosition> pos);
  void insert_after(const InstructionIterator& it,
                    std::unique_ptr<DexPosition> pos);

  void insert_before(Block* block,
                     const IRList::iterator& it,
                     std::unique_ptr<DexPosition> pos);
  void insert_after(Block* block,
                    const IRList::iterator& it,
                    std::unique_ptr<DexPosition> pos);

  void insert_before(const InstructionIterator& it,
                     std::unique_ptr<SourceBlock> sb);
  void insert_after(const InstructionIterator& it,
                    std::unique_ptr<SourceBlock> sb);

  void insert_before(const InstructionIterator& it,
                     std::unique_ptr<Remark> remark);
  void insert_after(const InstructionIterator& it,
                    std::unique_ptr<Remark> remark);

  // Insertion Methods (insert_before/after and push_front/back):
  //  * These methods add instructions to the CFG
  //  * They do not add branch (if-*, switch-*) instructions to the cfg (use
  //    create_branch for that)
  //  * If the inserted instruction requires a block boundary after it, the
  //    block will be split, instructions will be moved to the next
  //    (non-exceptional) block and the next insertion from `insns` will also
  //    occur in the next block. This invalidates iterators into the CFG.
  //  * If the inserted instruction could end the method (return-* or throw),
  //    then instructions after the insertion point will be removed and
  //    successor edges will be removed from the block. When inserting a return
  //    or throw, it must be the last in `insns`. This invalidates
  //    iterators into the CFG.
  //
  // insert insns before position
  // return a boolean:
  //   true means that iterators into the CFG are now invalid
  //   false means that iterators are still valid
  bool insert_before(const InstructionIterator& position,
                     const std::vector<IRInstruction*>& insns);

  // The iterator variants support iterators of the following types:
  // * IRInstruction*
  // * std::unique_ptr<SourceBlock>
  // * std::unique_ptr<DexPosition>
  // * std::unique_ptr<Remark>
  // * InsertVariant, std::variant of the previous types
  using InsertVariant = std::variant<IRInstruction*,
                                     std::unique_ptr<SourceBlock>,
                                     std::unique_ptr<DexPosition>,
                                     std::unique_ptr<Remark>>;

  template <class ForwardIt>
  bool insert_before(const InstructionIterator& position,
                     const ForwardIt& begin,
                     const ForwardIt& end) {
    return insert(position, begin, end, /* before */ true);
  }
  // insert insns after position
  bool insert_after(const InstructionIterator& position,
                    const std::vector<IRInstruction*>& insns);

  template <class ForwardIt>
  bool insert_after(const InstructionIterator& position,
                    const ForwardIt& begin,
                    const ForwardIt& end) {
    return insert(position, begin, end, /* before */ false);
  }

  // insert insns at the beginning of block b
  bool push_front(Block* b, const std::vector<IRInstruction*>& insns);

  template <class ForwardIt>
  bool push_front(Block* b, const ForwardIt& begin, const ForwardIt& end);

  // insert insns at the end of block b
  bool push_back(Block* b, const std::vector<IRInstruction*>& insns);

  template <class ForwardIt>
  bool push_back(Block* b, const ForwardIt& begin, const ForwardIt& end);

  // Convenience functions that add just one instruction.
  bool insert_before(const InstructionIterator& position, IRInstruction* insn);
  bool insert_after(const InstructionIterator& position, IRInstruction* insn);
  bool push_front(Block* b, IRInstruction* insn);
  bool push_back(Block* b, IRInstruction* insn);

  // Replace one IRInstruction with some number of new instructions
  // * None of the new instructions can be an if or goto
  // * Returns a boolean indicating whether or not InstructionIterators were
  //   invalidated (see insertion methods for more details)
  // * The throw edges of the block that contains `it` are copied and used as
  //   the throw edges of any new `may_throw` instructions
  // * If the old instruction has a move-result(-pseudo) it will also be
  //   removed. When adding instructions that may-throw, you should include
  //   move-result(-pseudo)s for them.
  // Any removed instruction will be freed when the cfg is destroyed.
  bool replace_insn(const InstructionIterator& it, IRInstruction* insn);
  template <class ForwardIt>
  bool replace_insns(const InstructionIterator& it,
                     const ForwardIt& begin,
                     const ForwardIt& end);
  bool replace_insns(const InstructionIterator& it,
                     const std::vector<IRInstruction*>& insns);

  // Create a conditional branch, which consists of:
  // * inserting an `if` instruction at the end of b
  // * Possibly add an EDGE_GOTO to the false block (`fls` may be null if b
  //   already has a goto leaving it)
  // * add an EDGE_BRANCH to the true block
  void create_branch(Block* b, IRInstruction* insn, Block* fls, Block* tru);

  // Create an `if` or `switch`, which consists of:
  // * insert an `if` or `switch` instruction at the end of b
  // * Possibly add an EDGE_GOTO to the default block (`goto_block` may be null
  //   if b already has a goto leaving it)
  // * add EDGE_BRANCHes to the other blocks based on the `case_to_block`
  //   vector.
  void create_branch(
      Block* b,
      IRInstruction* insn,
      Block* goto_block,
      const std::vector<std::pair<int32_t, Block*>>& case_to_block);

  // delete old blocks and reroute its predecessors to new blocks
  // Returns number of removed instructions.
  // May reset exit_block if it is replaced.
  uint32_t replace_blocks(
      const std::vector<std::pair<Block*, Block*>>& old_new_blocks);

  // delete old_block and reroute its predecessors to new_block
  // Note that replacing blocks is relatively expensive as it scans and fixes up
  // dangling parent positions in all other blocks; consider calling
  // remove_blocks to remove multiple blocks at once.
  // May reset exit_block if it is replaced.
  // Returns number of removed instructions.
  uint32_t replace_block(Block* old_block, Block* new_block) {
    return replace_blocks({{old_block, new_block}});
  }

  // Remove blocks from the graph and release associated memory.
  // Remove all incoming and outgoing edges.
  // May reset exit_block if it is removed.
  // Returns number of removed instructions.
  uint32_t remove_blocks(const std::vector<Block*>& blocks);

  // Remove this block from the graph and release associated memory.
  // Remove all incoming and outgoing edges.
  // Note that removing blocks is relatively expensive as it scans and fixes up
  // dangling parent positions in all other blocks; consider calling
  // remove_blocks to remove multiple blocks at once.
  // May reset exit_block if it is removed.
  // Returns number of removed instructions.
  uint32_t remove_block(Block* block) { return remove_blocks({block}); }

  /*
   * Print the graph in the DOT graph description language.
   */
  std::ostream& write_dot_format(std::ostream&) const;

  size_t num_blocks() const { return m_blocks.size(); }
  size_t num_edges() const { return m_edges.size(); }

  /*
   * Traverse the graph, starting from the entry node. Return a bitset with IDs
   * of reachable blocks having 1 and IDs of unreachable blocks (or unused IDs)
   * having 0.
   */
  boost::dynamic_bitset<> visit() const;

  cfg::Block* get_block(BlockId id) const { return m_blocks.at(id); }

  // Returns the block with the highest block id.
  cfg::Block* get_last_block() const {
    const auto& rbegin = m_blocks.rbegin();
    return rbegin == m_blocks.rend() ? nullptr : rbegin->second;
  }

  // remove blocks with no predecessors
  // returns pair of 1) the number of instructions removed, and 2) whether an
  // instruction with the destination of the last register was removed, and thus
  // a call to recompute_registers_size might be beneficial.
  std::pair<uint32_t, bool> remove_unreachable_blocks();

  // transform the CFG to an equivalent but more canonical state
  // returns the number of instructions removed
  uint32_t simplify();

  // SIGABORT if the internal state of the CFG is invalid
  void sanity_check() const;

  // SIGABORT if there are dangling parent pointers to deleted DexPositions
  void no_dangling_dex_positions() const;

  uint32_t num_opcodes() const;

  uint32_t sum_opcode_sizes() const;

  // similar to sum_opcode_sizes, but takes into account non-opcode payloads
  uint32_t estimate_code_units() const;

  // The cfg is missing plain OPCODE_GOTOs; this function computes a
  // size adjustment to account for that.
  uint32_t get_size_adjustment(bool assume_no_unreachable_blocks = false);

  reg_t allocate_temp() { return m_registers_size++; }

  reg_t allocate_wide_temp() {
    reg_t new_reg = m_registers_size;
    m_registers_size += 2;
    return new_reg;
  }

  reg_t get_registers_size() const { return m_registers_size; }

  void set_registers_size(reg_t sz) { m_registers_size = sz; }

  // Find the highest register in use and set m_registers_size
  //
  // Call this function after removing instructions that may have been the only
  // use of the highest numbered register, or any other significant changes to
  // the instructions.
  void recompute_registers_size();

  // Only used in cfg. \returns the first block that has instructions
  // if there is any. Otherwise, \returns null.
  Block* get_first_block_with_insns() const;

  // by default, start at the entry block
  boost::sub_range<IRList> get_param_instructions() const;

  void gather_catch_types(std::vector<const DexType*>& types) const;
  void gather_strings(std::vector<const DexString*>& strings) const;
  void gather_types(std::vector<const DexType*>& types) const;
  void gather_init_classes(std::vector<const DexType*>& types) const;
  void gather_fields(std::vector<DexFieldRef*>& fields) const;
  void gather_methods(std::vector<DexMethodRef*>& methods) const;
  void gather_callsites(std::vector<DexCallSite*>& callsites) const;
  void gather_methodhandles(std::vector<DexMethodHandle*>& methodhandles) const;

  // Different from primary_instruction_of_move_result(), this method is only
  // used for IR type check.
  cfg::InstructionIterator primary_instruction_of_move_result_for_type_check(
      const cfg::InstructionIterator& it);

  cfg::InstructionIterator primary_instruction_of_move_result(
      const cfg::InstructionIterator& it) const;

  cfg::InstructionIterator move_result_of(
      const cfg::InstructionIterator& it) const;

  /*
   * Gets the next instruction, following gotos if the end of blocks are
   * reached. In case of an infinite loop, `InstructionIterable(*this).end()` is
   * returned.
   */
  cfg::InstructionIterator next_following_gotos(
      const cfg::InstructionIterator& it) const;

  /*
   * clear and fill `new_cfg` with a copy of `this`. Copies of all instructions
   * will be made, and are owned by the caller. Consider calling
   * set_insn_ownership on the new cfg to have it own the instructions.
   */
  void deep_copy(ControlFlowGraph* new_cfg) const;

  /*
   * Set whether this cfg holds the memory ownership of the contained
   * instructions, deleting them when the cfg is destroyed. (The default is
   * false.)
   */
  void set_insn_ownership(bool owns_insns) { m_owns_insns = owns_insns; }

  /*
   * Set whether this cfg holds the memory ownership of instructions that are
   * removed. (The default is true.)
   */
  void set_removed_insn_ownership(bool owns_removed_insns) {
    m_owns_removed_insns = owns_removed_insns;
  }

  // Search all the instructions in this CFG for the given one. Return an
  // iterator to it, or end, if it isn't in the graph.
  InstructionIterator find_insn(const IRInstruction* insn,
                                Block* hint = nullptr);
  ConstInstructionIterator find_insn(const IRInstruction* insn,
                                     Block* hint = nullptr) const;

  // choose an order of blocks for output; note that unless
  // assume_no_unreachable_blocks is set to true, this function may mutate the
  // cfg by simplifying it
  std::vector<Block*> order(LinearizationStrategy* custom_strategy = nullptr,
                            bool assume_no_unreachable_blocks = false);

  /*
   * Find the first debug position preceding an instruction
   */
  DexPosition* get_dbg_pos(const cfg::InstructionIterator& it);

  std::size_t opcode_hash() const;

  std::vector<IRInstruction*> release_removed_instructions() {
    return std::move(m_removed_insns);
  }

  bool structural_equals(const ControlFlowGraph& other) const;

  bool structural_equals(const ControlFlowGraph& other,
                         const InstructionEquality& instruction_equals) const;

  using BlockPairing = UnorderedMap<const Block*, const Block*>;

  // When this graph and `other` are structurally equal, maps each block
  // reachable from this graph's entry to its counterpart in `other`.
  std::optional<BlockPairing> structural_block_pairing(
      const ControlFlowGraph& other) const;

  std::optional<BlockPairing> structural_block_pairing(
      const ControlFlowGraph& other,
      const InstructionEquality& instruction_equals) const;

  template <class ForwardIt>
  bool insert(const InstructionIterator& position,
              const ForwardIt& begin_index,
              const ForwardIt& end_index,
              bool before);

 private:
  friend class Block;

  using BranchToTargets =
      UnorderedMap<MethodItemEntry*,
                   std::vector<std::pair<Block*, MethodItemEntry*>>>;
  using TryEnds = std::vector<std::pair<TryEntry*, Block*>>;
  using TryCatches = UnorderedMap<CatchEntry*, Block*>;
  using Blocks = std::map<BlockId, Block*>;
  friend class InstructionIteratorImpl<false>;
  friend class InstructionIteratorImpl<true>;
  friend class CFGInliner;

  // Find block boundaries in IRCode and create the blocks
  // For use by the constructor. You probably don't want to call this from
  // elsewhere
  void find_block_boundaries(IRList* ir,
                             BranchToTargets& branch_to_targets,
                             TryEnds& try_ends,
                             TryCatches& try_catches);

  // Add edges between blocks created by `find_block_boundaries`
  // For use by the constructor. You probably don't want to call this from
  // elsewhere
  void connect_blocks(BranchToTargets& branch_to_targets);

  // Add edges from try blocks to their catch handlers.
  // For use by the constructor. You probably don't want to call this from
  // elsewhere
  void add_catch_edges(TryEnds& try_ends, TryCatches& try_catches);

  // For use by the constructor. You probably don't want to call this from
  // elsewhere
  void remove_unreachable_succ_edges();

  // remove all MFLOW_TRY and MFLOW_CATCH markers because that information is
  // moved into the edges.
  void remove_try_catch_markers();

  // helper functions
  void build_chains(std::vector<std::unique_ptr<BlockChain>>* chains,
                    UnorderedMap<Block*, BlockChain*>* block_to_chain);
  sparta::WeakTopologicalOrdering<BlockChain*> build_wto(
      const UnorderedMap<Block*, BlockChain*>& block_to_chain);
  std::vector<Block*> wto_chains(
      sparta::WeakTopologicalOrdering<BlockChain*> wto);

  // Materialize target instructions and gotos corresponding to control-flow
  // edges. Used while turning back into a linear representation.
  void insert_branches_and_targets(const std::vector<Block*>& ordering);

  // Create MFLOW_CATCH entries for each EDGE_THROW. returns the primary
  // MFLOW_CATCH (first element in linked list of CatchEntries) on a block that
  // can throw. returns nullptr on a block without outgoing throw edges. This
  // function is used while turning back into a linear representation.
  //
  // Example: For a block with outgoing edges
  //
  // Edge(block, catch_block_1, FooException, 1)
  // Edge(block, catch_block_2, BarException, 2)
  // Edge(block, catch_block_3, BazException, 3)
  //
  // This generates CatchEntries (linked list)
  //
  // CatchEntry(FooException) ->
  //   CatchEntry(BarException) ->
  //     CatchEntry(BazException)
  MethodItemEntry* create_catch(
      Block* block,
      UnorderedMap<MethodItemEntry*, Block*>* catch_to_containing_block);

  // Materialize TRY_STARTs, TRY_ENDs, and MFLOW_CATCHes
  // Used while turning back into a linear representation.
  void insert_try_catch_markers(const std::vector<Block*>& ordering);

  // remove blocks with no entries
  void remove_empty_blocks();

  // Re-insert any parent pointer that got deleted. This is a useful
  // method to invoke just after removing positions to avoid leaving
  // behind dangling parents.
  void fix_dangling_parents(std::vector<std::unique_ptr<DexPosition>>);

  // Assert if there are edges that are never a predecessor or successor of a
  // block
  void no_unreferenced_edges() const;

  // Remove all edges and blocks of the CFG, free the memory and
  // set all fields to their defaults.
  // NOTE: this will result in an empty CFG, same as if the default
  // constructor has been called.
  void clear();

  // remove_..._edge:
  //   * These functions remove edges from the graph.
  //   * They do not free the memory of the edge. `free_edge` does that.
  //   * The cleanup flag controls whether or not `cleanup_deleted_edges` is
  //     called. See that function for more documentation.
  //   * the `_if` functions take a predicate to decide which edges to delete
  //   * They return which edges were removed (with the exception of
  //     `remove_edge`)
  void remove_edge(Edge* edge, bool cleanup = true);
  EdgeSet remove_succ_edges(Block* b, bool cleanup = true);
  EdgeSet remove_pred_edges(Block* b, bool cleanup = true);
  EdgeSet remove_edges_between(Block* p, Block* s, bool cleanup = true);

  template <typename EdgePredicate>
  EdgeSet remove_edge_if(Block* source,
                         Block* target,
                         EdgePredicate predicate,
                         bool cleanup = true) {
    auto& forward_edges = source->m_succs;
    EdgeSet to_remove;
    forward_edges.erase(
        std::remove_if(forward_edges.begin(),
                       forward_edges.end(),
                       [&target, &predicate, &to_remove](Edge* e) {
                         if (e->target() == target && predicate(e)) {
                           to_remove.insert(e);
                           return true;
                         }
                         return false;
                       }),
        forward_edges.end());

    auto& reverse_edges = target->m_preds;
    reverse_edges.erase(std::remove_if(reverse_edges.begin(),
                                       reverse_edges.end(),
                                       [&to_remove](Edge* e) {
                                         return to_remove.count(e) > 0;
                                       }),
                        reverse_edges.end());

    if (cleanup) {
      cleanup_deleted_edges(to_remove);
    }
    return to_remove;
  }

  template <class ForwardIt, typename EdgePredicate>
  EdgeSet remove_pred_edge_if(const ForwardIt& begin,
                              const ForwardIt& end,
                              EdgePredicate predicate,
                              bool cleanup = true) {
    UnorderedSet<Block*> source_blocks;
    EdgeSet to_remove;
    for (auto it = begin; it != end; it++) {
      auto& reverse_edges = (*it)->m_preds;
      reverse_edges.erase(
          std::remove_if(reverse_edges.begin(),
                         reverse_edges.end(),
                         [&source_blocks, &to_remove, &predicate](Edge* e) {
                           if (predicate(e)) {
                             source_blocks.insert(e->src());
                             to_remove.insert(e);
                             return true;
                           }
                           return false;
                         }),
          reverse_edges.end());
    }

    for (Block* source_block : UnorderedIterable(source_blocks)) {
      auto& forward_edges = source_block->m_succs;
      forward_edges.erase(
          std::remove_if(
              forward_edges.begin(), forward_edges.end(),
              [&to_remove](Edge* e) { return to_remove.count(e) > 0; }),
          forward_edges.end());
    }

    if (cleanup) {
      cleanup_deleted_edges(to_remove);
    }
    return to_remove;
  }

  template <class ForwardIt, typename EdgePredicate>
  EdgeSet remove_succ_edge_if(const ForwardIt& begin,
                              const ForwardIt& end,
                              EdgePredicate predicate,
                              bool cleanup = true) {
    UnorderedSet<Block*> target_blocks;
    UnorderedSet<Edge*> to_remove;
    for (auto it = begin; it != end; it++) {
      auto& forward_edges = (*it)->m_succs;
      forward_edges.erase(
          std::remove_if(forward_edges.begin(),
                         forward_edges.end(),
                         [&target_blocks, &to_remove, &predicate](Edge* e) {
                           if (predicate(e)) {
                             target_blocks.insert(e->target());
                             to_remove.insert(e);
                             return true;
                           }
                           return false;
                         }),
          forward_edges.end());
    }

    for (Block* target_block : UnorderedIterable(target_blocks)) {
      auto& reverse_edges = target_block->m_preds;
      reverse_edges.erase(
          std::remove_if(
              reverse_edges.begin(), reverse_edges.end(),
              [&to_remove](Edge* e) { return to_remove.count(e) > 0; }),
          reverse_edges.end());
    }

    if (cleanup) {
      cleanup_deleted_edges(to_remove);
    }
    return to_remove;
  }

  // Assumes the edge is already removed.
  void free_edge(Edge* edge);

  // Assumes the edge is already removed.
  void free_edges(const EdgeSet& edges);

  // The `cleanup` boolean flag on the edge removal functions controls whether
  // or not to call this function afterwards.
  //   * `cleanup` false means only remove the edges
  //   * `cleanup` true means remove the edges and edit the instructions to
  //      match the edge state. For example, delete branch/switch with only one
  //      outgoing edge instructions.
  void cleanup_deleted_edges(const EdgeSet& edges);

  // free all allocated and owned memory of the CFG
  void free_all_blocks_and_edges_and_removed_insns();

  // Move edge between new_source and new_target.
  // If either new_source or new_target is null, don't change that field of the
  // edge
  void move_edge(Edge* edge, Block* new_source, Block* new_target);

  reg_t compute_registers_size() const;

  // Return the next unused block identifier
  BlockId next_block_id() const;

  std::vector<Block*> blocks_post_helper(bool reverse) const;

  // The memory of all blocks and edges in this graph are owned here
  Blocks m_blocks;
  EdgeSet m_edges;

  Block* m_entry_block{nullptr};
  Block* m_exit_block{nullptr};
  reg_t m_registers_size{0};
  bool m_owns_insns{false};
  bool m_owns_removed_insns{true};
  std::vector<IRInstruction*> m_removed_insns;
};

// A static-method-only API for use with the monotonic fixpoint iterator.
class GraphInterface {

 public:
  using Graph = ControlFlowGraph;
  using NodeId = Block*;
  using EdgeId = Edge*;
  static NodeId entry(const Graph& graph) { return graph.entry_block(); }
  static NodeId exit(const Graph& graph) { return graph.exit_block(); }
  static const CompactEdgeVector& predecessors(const Graph&, const NodeId& b) {
    return b->preds();
  }
  static const CompactEdgeVector& successors(const Graph&, const NodeId& b) {
    return b->succs();
  }
  static NodeId source(const Graph&, const EdgeId& e) { return e->src(); }
  static NodeId target(const Graph&, const EdgeId& e) { return e->target(); }
};

template <bool is_const>
class InstructionIteratorImpl {
  using Cfg = typename std::
      conditional<is_const, const ControlFlowGraph, ControlFlowGraph>::type;
  using Mie = typename std::
      conditional<is_const, const MethodItemEntry, MethodItemEntry>::type;
  using Iterator = typename std::
      conditional<is_const, IRList::const_iterator, IRList::iterator>::type;
  using IRListInstructionIterable = ir_list::InstructionIterableImpl<is_const>;

  // Use a pointer so that we can be copy constructible
  Cfg* m_cfg;
  ControlFlowGraph::Blocks::const_iterator m_block;

  // Depends on C++14 Null Forward Iterators
  // Assuming the default constructed InstructionIterator compares equal
  // to other default constructed InstructionIterator
  //
  // boost.org/doc/libs/1_58_0/doc/html/container/Cpp11_conformance.html
  ir_list::InstructionIteratorImpl<is_const> m_it;

  // go to beginning of next block, skipping empty blocks
  void to_next_block() {
    while (m_block != m_cfg->m_blocks.end() &&
           m_it.unwrap() == m_block->second->m_entries.end()) {
      ++m_block;
      if (m_block != m_cfg->m_blocks.end()) {
        Block* b = m_block->second;
        m_it = ir_list::InstructionIteratorImpl<is_const>(b->m_entries.begin(),
                                                          b->m_entries.end());
      } else {
        m_it = ir_list::InstructionIteratorImpl<is_const>();
      }
    }
  }

  friend class ControlFlowGraph;
  friend class Block;
  InstructionIteratorImpl(Cfg& cfg,
                          Block* b,
                          const ir_list::InstructionIterator& it)
      : m_cfg(&cfg), m_block(m_cfg->m_blocks.find(b->id())), m_it(it) {}

 public:
  using reference = Mie&;
  using difference_type = long;
  using value_type = Mie&;
  using pointer = Mie*;
  using iterator_category = std::bidirectional_iterator_tag;

  // TODO: Is it possible to recover a valid state of iterators into the CFG
  // after an insertion operation?
  //
  // The goal is to maintain a valid state within the CFG at all times. If the
  // user wants to insert an instruction that ends the block (return, can_throw,
  // if, switch, etc.), the block needs to split. When you split a block into
  // two parts, you're moving code from one block to another. When code is moved
  // `InstructionIterator`s may be left in an invalid state because their `m_it`
  // is pointing into a different block than `m_block`.

  InstructionIteratorImpl() = delete;

  explicit InstructionIteratorImpl(Cfg& cfg, bool is_begin) : m_cfg(&cfg) {
    if (is_begin) {
      m_block = m_cfg->m_blocks.begin();
      if (m_block != m_cfg->m_blocks.end()) {
        auto iterable = IRListInstructionIterable(m_block->second);
        m_it = iterable.begin();
        if (m_it == iterable.end()) {
          to_next_block();
        }
      }
    } else {
      m_block = m_cfg->m_blocks.end();
    }
  }

  // NOLINTNEXTLINE(google-explicit-constructor)
  InstructionIteratorImpl(const InstructionIteratorImpl<false>& rhs)
      : m_cfg(rhs.m_cfg), m_block(rhs.m_block), m_it(rhs.m_it) {}

  InstructionIteratorImpl& operator=(
      const InstructionIteratorImpl<false>& rhs) {
    m_cfg = rhs.m_cfg;
    m_block = rhs.m_block;
    m_it = rhs.m_it;
    return *this;
  }

  InstructionIteratorImpl<is_const>& operator++() {
    assert_not_end();
    ++m_it;
    to_next_block();
    return *this;
  }

  InstructionIteratorImpl<is_const> operator++(int) {
    auto result = *this;
    ++(*this);
    return result;
  }

  InstructionIteratorImpl<is_const>& operator--() {
    assert_not_begin();
    // as long as we are at the beginning of the current block, keep going back
    // to the end of the previous block
    while (m_block == m_cfg->m_blocks.end() ||
           m_it == IRListInstructionIterable(m_block->second).begin()) {
      m_it = IRListInstructionIterable((--m_block)->second).end();
    }
    --m_it;
    return *this;
  }

  InstructionIteratorImpl<is_const> operator--(int) {
    auto result = *this;
    --(*this);
    return result;
  }

  reference operator*() const {
    assert_not_end();
    return *m_it;
  }

  pointer operator->() const { return &(this->operator*()); }

  bool operator==(const InstructionIteratorImpl& other) const {
    return this->m_block == other.m_block && this->m_it == other.m_it;
  }

  bool operator!=(const InstructionIteratorImpl& other) const {
    return !(*this == other);
  }

  void assert_not_begin() const {
    if (!ControlFlowGraph::s_DEBUG) {
      return;
    }
    auto begin = InstructionIteratorImpl<is_const>(*m_cfg, true);
    always_assert_log(*this != begin, "%s", details::show_cfg(*m_cfg).c_str());
  }

  void assert_not_end() const {
    if (!ControlFlowGraph::s_DEBUG) {
      return;
    }
    always_assert_log(m_block != m_cfg->m_blocks.end(), "%s",
                      details::show_cfg(*m_cfg).c_str());
    always_assert_log(m_it != ir_list::InstructionIteratorImpl<is_const>(),
                      "%s", details::show_cfg(*m_cfg).c_str());
  }

  bool is_end() const {
    return m_block == m_cfg->m_blocks.end() &&
           m_it == ir_list::InstructionIteratorImpl<is_const>();
  }

  // \returns true if current iterator is at the end of current block.
  bool is_end_in_block() const {
    return m_it.unwrap() == m_block->second->m_entries.end();
  }

  // Move the current iterator and this move must be in the same block.
  InstructionIteratorImpl<is_const>& move_next_in_block() {
    always_assert(!is_end_in_block());
    ++m_it;
    return *this;
  }

  Iterator unwrap() const { return m_it.unwrap(); }

  Block* block() const {
    assert_not_end();
    return m_block->second;
  }

  Cfg& cfg() const { return *m_cfg; }

  template <bool kConst>
  friend class InstructionIteratorImpl;
};

// Iterate through all IRInstructions in the CFG.
// Instructions in the same block are processed in order.
// Blocks are iterated in an undefined order
template <bool is_const>
class InstructionIterableImpl {
  using Cfg = typename std::
      conditional<is_const, const ControlFlowGraph, ControlFlowGraph>::type;
  using Iterator = typename std::
      conditional<is_const, IRList::const_iterator, IRList::iterator>::type;
  Cfg& m_cfg;

 public:
  InstructionIterableImpl() = delete;
  explicit InstructionIterableImpl(Cfg& cfg) : m_cfg(cfg) {}

  InstructionIteratorImpl<is_const> begin() {
    return InstructionIteratorImpl<is_const>(m_cfg, true);
  }
  InstructionIteratorImpl<true> begin() const {
    return InstructionIteratorImpl<true>(m_cfg, true);
  }

  InstructionIteratorImpl<is_const> end() {
    return InstructionIteratorImpl<is_const>(m_cfg, false);
  }
  InstructionIteratorImpl<true> end() const {
    return InstructionIteratorImpl<true>(m_cfg, false);
  }

  bool empty() const { return begin() == end(); }
};

template <class ForwardIt>
bool ControlFlowGraph::replace_insns(const InstructionIterator& it,
                                     const ForwardIt& begin,
                                     const ForwardIt& end) {
  // Save these values before we insert in case the insertion causes iterator
  // invalidation.
  auto* insn_to_del = it->insn;

  bool invalidated = insert(it, begin, end, true /* before */);
  if (invalidated) {
    const auto& found = find_insn(insn_to_del);
    if (!found.is_end()) {
      remove_insn(found);
    }
    // If find_insn can't find `insn_to_del` it was most likely removed by
    // `insert`. This happens when a throw or return is added to the block
    // because the remaining code in the block is removed.
  } else {
    remove_insn(it);
  }
  return invalidated;
}

template <class ForwardIt>
bool ControlFlowGraph::insert(const InstructionIterator& position,
                              const ForwardIt& begin_index,
                              const ForwardIt& end_index,
                              bool before) {
  // Convert to the before case by moving the position forward one.
  Block* b = position.block();
  if (position.unwrap() == b->end()) {
    always_assert_log(before, "can't insert after the end");
  }
  IRList::iterator pos =
      before ? position.unwrap() : std::next(position.unwrap());

  // We might need to propagate source blocks if we create a block.
  // Find the latest source block in the current block in case.
  // NOTE: when `pos` is `b->end()` we must not dereference it; treat that
  // case as "no matching position MIE in this block" and scan the entire
  // block for the latest source block.
  const bool pos_is_end = (pos == b->end());
  SourceBlock* last_src_block = nullptr;
  for (const auto& mie : *b) {
    if (!pos_is_end && mie.pos == pos->pos) {
      break;
    }
    if (mie.type == MFLOW_SOURCE_BLOCK) {
      last_src_block = mie.src_block.get();
    }
  }

  bool invalidated_its = false;
  bool insert_source_block = false;
  bool insn_has_move = false;
  for (auto insns_it = begin_index; insns_it != end_index; insns_it++) {
    // Coercing everything to a variant allows us to handle the complicated
    // case easily. The compiler should be able to optimize this back for
    // a simple type.
    auto v = InsertVariant(std::move(*insns_it));
    insn_has_move = false;

    if (std::holds_alternative<IRInstruction*>(v)) {
      IRInstruction* insn = std::get<IRInstruction*>(v);
      bool throws = get_succ_edge_of_type(b, EDGE_THROW) != nullptr;
      auto op = insn->opcode();
      insn_has_move = insn->has_move_result_pseudo();

      if (insert_source_block && !opcode::is_move_result_any(op)) {
        if (last_src_block != nullptr) {
          b->m_entries.insert_before(
              pos, source_blocks::clone_as_synthetic(last_src_block));
        }
        insert_source_block = false;
      }

      // Certain types of blocks cannot have instructions added to the end.
      // Disallow that case here.
      if (pos == b->end()) {
        auto existing_last = b->get_last_insn();
        if (existing_last != b->end()) {
          // This will abort if someone tries to insert after a returning or
          // throwing instruction.
          auto existing_last_op = existing_last->insn->opcode();
          always_assert_log(
              !opcode::is_branch(existing_last_op) &&
                  !opcode::is_throw(existing_last_op) &&
                  !opcode::is_a_return(existing_last_op),
              "Can't add instructions after %s in Block %zu in %s",
              details::show_insn(existing_last->insn).c_str(), b->id(),
              details::show_cfg(*this).c_str());

          // When inserting after an instruction that may throw, we need to
          // start a new block. We also copy over all throw-edges. See FIXME
          // below for a discussion about try-regions in general.
          if (throws) {
            always_assert_log(
                !existing_last->insn->has_move_result_any(),
                "Can't add instructions after throwing instruction "
                "%s with move-result in Block %zu in %s",
                details::show_insn(existing_last->insn).c_str(), b->id(),
                details::show_cfg(*this).c_str());
            Block* new_block = create_block();
            if (opcode::may_throw(op)) {
              copy_succ_edges_of_type(b, new_block, EDGE_THROW);
            }
            const auto& existing_goto_edge =
                get_succ_edge_of_type(b, EDGE_GOTO);
            set_edge_source(existing_goto_edge, new_block);
            add_edge(b, new_block, EDGE_GOTO);
            // Continue inserting in the new block.
            b = new_block;
            pos = new_block->begin();

            // In the case where the next instruction would create a new block
            // by throwing, We want to also want to try inserting a source block
            // at the beginning of this new block because we won't get the
            // chance to do it after.
            insert_source_block = true;
            auto next_it = std::next(insns_it);
            if (next_it != end_index) {
              auto next_v = InsertVariant(std::move(*next_it));
              if (std::holds_alternative<IRInstruction*>(next_v)) {
                if (opcode::may_throw(op) && last_src_block != nullptr) {
                  always_assert(!opcode::is_move_result_any(op));
                  b->m_entries.insert_before(
                      pos, source_blocks::clone_as_synthetic(last_src_block));
                  insert_source_block = false;
                }
              }
            }
          }
        }
      }

      always_assert_log(!opcode::is_branch(op),
                        "insert() does not support branch opcodes. Use "
                        "create_branch() instead");

      IRList::iterator new_inserted_it = b->m_entries.insert_before(pos, insn);
      if (opcode::is_throw(op) || opcode::is_a_return(op)) {
        // Stop adding instructions when we understand that op
        // is the end of the block.
        insns_it = std::prev(end_index);
        std::vector<std::unique_ptr<DexPosition>> dangling;
        for (auto it = pos; it != b->m_entries.end();) {
          switch (it->type) {
          case MFLOW_POSITION:
            dangling.push_back(std::move(it->pos));
            break;
          case MFLOW_OPCODE:
            m_removed_insns.push_back(it->insn);
            break;
          default:
            break;
          }
          it = b->m_entries.erase_and_dispose(it);
          invalidated_its = true;
        }
        fix_dangling_parents(std::move(dangling));

        if (opcode::is_a_return(op)) {
          // This block now ends in a return, it must have no successors.
          delete_succ_edge_if(
              b, [](const Edge* e) { return e->type() != EDGE_GHOST; });
        } else {
          always_assert(opcode::is_throw(op));
          // The only valid way to leave this block is via a throw edge.
          delete_succ_edge_if(b, [](const Edge* e) {
            return e->type() != EDGE_THROW && e->type() != EDGE_GHOST;
          });
        }
        // If this created unreachable blocks, they will be removed by simplify.
      } else if (opcode::may_throw(op) && throws) {
        insert_source_block = true;
        invalidated_its = true;
        // FIXME: Copying the outgoing throw edges isn't enough.
        // When the CFG is constructed, we transform the try regions
        // into throw edges. We only add these edges to blocks that may throw,
        // thus losing the knowledge of which blocks were originally inside a
        // try region. If we add a new throwing instruction here. It may be
        // added to a block that was originally inside a try region, but we lost
        // that information already.
        //
        // Possible Solutions:
        // * Rework throw representation to regions instead of duplicated edges?
        // * User gives a block that we want to copy the throw edges from?
        // * User specifies which throw edges they want and to which blocks?

        // Split the block after the new instruction.
        // b has become the predecessor of the new split pair
        Block* succ =
            split_block(b->to_cfg_instruction_iterator(new_inserted_it));

        if (!succ->empty()) {
          // Copy the outgoing throw edges of the new block back into the
          // original block
          copy_succ_edges_of_type(succ, b, EDGE_THROW);
        }

        // Continue inserting in the successor block.
        b = succ;
        pos = succ->begin();
      }
    } else if (std::holds_alternative<std::unique_ptr<SourceBlock>>(v)) {
      last_src_block =
          b->m_entries
              .insert_before(
                  pos, std::get<std::unique_ptr<SourceBlock>>(std::move(v)))
              ->src_block.get();
      insert_source_block = false;
    } else if (std::holds_alternative<std::unique_ptr<DexPosition>>(v)) {
      if (insert_source_block) {
        if (last_src_block != nullptr) {
          b->m_entries.insert_before(
              pos, source_blocks::clone_as_synthetic(last_src_block));
        }
        insert_source_block = false;
      }
      b->m_entries.insert_before(
          pos, std::get<std::unique_ptr<DexPosition>>(std::move(v)));
    } else if (std::holds_alternative<std::unique_ptr<Remark>>(v)) {
      // Block-anchored metadata; insert in place, no cross-split propagation.
      b->m_entries.insert_before(
          pos, std::get<std::unique_ptr<Remark>>(std::move(v)));
    } else {
      not_reached();
    }
  }
  // We might need to insert a source block at the end, but not if the
  // last instruction we inserted could be followed by a move instruction.
  if (insert_source_block && last_src_block != nullptr && !insn_has_move) {
    b->m_entries.insert_before(
        pos, source_blocks::clone_as_synthetic(last_src_block));
  }
  return invalidated_its;
}

template <class ForwardIt>
bool ControlFlowGraph::push_front(Block* b,
                                  const ForwardIt& begin,
                                  const ForwardIt& end) {
  const auto& block_begin = ir_list::InstructionIterable(b).begin();
  return insert(b->to_cfg_instruction_iterator(block_begin), begin, end,
                /* before */ true);
}

template <class ForwardIt>
bool ControlFlowGraph::push_back(Block* b,
                                 const ForwardIt& begin,
                                 const ForwardIt& end) {
  const auto& block_end = ir_list::InstructionIterable(b).end();
  return insert(b->to_cfg_instruction_iterator(block_end), begin, end,
                /* before */ true);
}

template <class ForwardIt>
bool Block::insert_before(const InstructionIterator& position,
                          const ForwardIt& begin,
                          const ForwardIt& end) {
  return m_parent->insert_before(position, begin, end);
}

template <class ForwardIt>
bool Block::insert_after(const InstructionIterator& position,
                         const ForwardIt& begin,
                         const ForwardIt& end) {
  return m_parent->insert_after(position, begin, end);
}

template <class ForwardIt>
bool Block::push_front(const ForwardIt& begin, const ForwardIt& end) {
  return m_parent->push_front(this, begin, end);
}

template <class ForwardIt>
bool Block::push_back(const ForwardIt& begin, const ForwardIt& end) {
  return m_parent->push_back(this, begin, end);
}

/**
 * Check whether, possibly at the end of a chain of gotos, the block will
 * unconditionally throw.
 */
bool block_eventually_throws(Block* block);

} // namespace cfg

inline cfg::InstructionIterable InstructionIterable(
    cfg::ControlFlowGraph& cfg) {
  return cfg::InstructionIterable(cfg);
}

inline cfg::ConstInstructionIterable InstructionIterable(
    const cfg::ControlFlowGraph& cfg) {
  return cfg::ConstInstructionIterable(cfg);
}
