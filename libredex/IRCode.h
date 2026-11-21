/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "DexClass.h"
#include "DexDebugInstruction.h"
#include "IRInstruction.h"
#include "IRList.h"

namespace cfg {
class ControlFlowGraph;
struct LinearizationStrategy;
} // namespace cfg

// TODO(jezng): IRCode currently contains too many methods that shouldn't
// belong there... I'm going to move them out soon
class IRCode {
 private:
  /* try_sync() is the work-horse of sync.  It's intended such that it can fail
   * in the event that an opcode needs to be resized.  In that instance, it
   * changes the opcode in question, and returns false.  It's intended to be
   * called multiple times until it returns true.
   */
  bool try_sync(DexCode*,
                UnorderedMap<const MethodItemEntry*, uint32_t>*
                    entry_addresses = nullptr);

  void split_and_insert_try_regions(
      uint32_t start,
      uint32_t end,
      const DexCatches& catches,
      std::vector<std::unique_ptr<DexTryItem>>* tries);

  std::unique_ptr<IRList> m_ir_list;
  std::unique_ptr<cfg::ControlFlowGraph> m_cfg;

  reg_t m_registers_size{0};
  bool m_cfg_serialized_with_custom_strategy = false;

  // Hack: in general the IRCode is not handled as owning instructions, as they
  //       might be shared. Toggle to true via `set_insn_ownership` to destruct
  //       instructions on delete.
  bool m_owns_insns{true};

  // TODO(jezng): we shouldn't be storing / exposing the DexDebugItem... just
  // exposing the param names should be enough
  std::unique_ptr<DexDebugItem> m_dbg;

  IRList::iterator make_if_block(const IRList::iterator& cur,
                                 IRInstruction* insn,
                                 IRList::iterator* if_block) {
    return m_ir_list->make_if_block(cur, insn, if_block);
  }
  IRList::iterator make_if_else_block(const IRList::iterator& cur,
                                      IRInstruction* insn,
                                      IRList::iterator* if_block,
                                      IRList::iterator* else_block) {
    return m_ir_list->make_if_else_block(cur, insn, if_block, else_block);
  }
  IRList::iterator make_switch_block(
      const IRList::iterator& cur,
      IRInstruction* insn,
      IRList::iterator* default_block,
      std::map<SwitchIndices, IRList::iterator>& cases) {
    return m_ir_list->make_switch_block(cur, insn, default_block, cases);
  }

  friend struct MethodCreator;

 public:
  // This creates an "empty" IRCode, one that contains no load-param opcodes or
  // debug info. If you attach it to a method, you need to insert the
  // appropriate load-param opcodes yourself. Mostly used for testing purposes.
  IRCode();

  explicit IRCode(DexMethod*);

  // Same as constructor above but better for error-handling purposes. New
  // code should use this method.
  static std::unique_ptr<IRCode> for_method(DexMethod* method);

  explicit IRCode(std::unique_ptr<cfg::ControlFlowGraph>);

  /*
   * Construct an IRCode for a DexMethod that has no DexCode (that is, a new
   * method that we are creating instead of something from an input dex file.)
   * In the absence of a register allocator, we need the parameters to be
   * loaded at the end of the register frame. Since we don't have a DexCode
   * object, we need to specify the frame size ourselves, hence the extra
   * parameter.
   *
   * Once we have an allocator we should be able to deprecate this.
   */
  explicit IRCode(DexMethod*, size_t temp_regs);

  IRCode(const IRCode& code);

  ~IRCode();

  void set_insn_ownership(bool owns_insns) { m_owns_insns = owns_insns; }

  bool structural_equals(const IRCode& other) const {
    return m_ir_list->structural_equals(*other.m_ir_list,
                                        std::equal_to<const IRInstruction&>());
  }

  bool structural_equals(const IRCode& other,
                         const InstructionEquality& instruction_equals) const {
    return m_ir_list->structural_equals(*other.m_ir_list, instruction_equals);
  }

  void cleanup_debug();

  reg_t get_registers_size() const;

  void set_registers_size(reg_t sz);

  reg_t allocate_temp();

  reg_t allocate_wide_temp();

  /*
   * Find the subrange of load-param instructions. These instructions should
   * always be at the beginning of the method.
   */
  boost::sub_range<IRList> get_param_instructions() const;

  void set_debug_item(std::unique_ptr<DexDebugItem> dbg) {
    m_dbg = std::move(dbg);
  }
  const DexDebugItem* get_debug_item() const { return m_dbg.get(); }
  DexDebugItem* get_debug_item() { return m_dbg.get(); }
  std::unique_ptr<DexDebugItem> release_debug_item() {
    return std::move(m_dbg);
  }

  void gather_catch_types(std::vector<const DexType*>& ltype) const;
  void gather_strings(std::vector<const DexString*>& lstring) const;
  void gather_types(std::vector<const DexType*>& ltype) const;
  void gather_fields(std::vector<DexFieldRef*>& lfield) const;
  void gather_methods(std::vector<DexMethodRef*>& lmethod) const;
  void gather_callsites(std::vector<DexCallSite*>& lcallsite) const;
  void gather_protos(std::vector<DexProto*>& lproto) const;
  void gather_methodhandles(std::vector<DexMethodHandle*>& lmethodhandle) const;

  void gather_init_classes(std::vector<const DexType*>& ltype) const;

  /* Return the control flow graph of this method as a vector of blocks. */
  cfg::ControlFlowGraph& cfg() { return *m_cfg; }

  const cfg::ControlFlowGraph& cfg() const { return *m_cfg; }

  // Build a Control Flow Graph
  //  * A CFG's blocks each own a small IRList (with
  //    MethodItemEntries taken from IRCode)
  // Changes to a CFG are reflected in IRCode after `clear_cfg` is
  // called. For cfg, it is only rebuilt when the flag
  // rebuild_even_if_already_built is true. Otherwise, the current
  // cfg will be kept.
  void build_cfg(bool rebuild_even_if_already_built = true);

  // Linearize CFG back into m_ir_list
  // custom_strategy controls the linearization of the CFG.
  //
  // The CFG may have stored instructions that were removed. If deleted_insns is
  // not null, the instructions are moved into the given vector. It is then the
  // caller's responsibility to free them.
  void clear_cfg(cfg::LinearizationStrategy* custom_strategy = nullptr,
                 std::vector<IRInstruction*>* deleted_insns = nullptr);

  bool cfg_built() const { return m_cfg != nullptr; }

  /* Generate DexCode from IRCode */
  std::unique_ptr<DexCode> sync(const DexMethod*);

  /* DEPRECATED! Use the version below that passes in the iterator instead,
   * which is O(1) instead of O(n). */
  /* Passes memory ownership of "from" to callee.  It will delete it. */
  void replace_opcode(IRInstruction* from, IRInstruction* to) {
    m_ir_list->replace_opcode(from, to);
  }

  /* DEPRECATED! Use the version below that passes in the iterator instead,
   * which is O(1) instead of O(n). */
  /* Passes memory ownership of "from" to callee.  It will delete it. */
  void replace_opcode(IRInstruction* to_delete,
                      const std::vector<IRInstruction*>& replacements) {
    m_ir_list->replace_opcode(to_delete, replacements);
  }

  /* Passes memory ownership of "from" to callee.  It will delete it. */
  void replace_opcode(const IRList::iterator& it,
                      const std::vector<IRInstruction*>& replacements) {
    m_ir_list->replace_opcode(it, replacements);
  }

  /*
   * Does exactly what it says and you SHOULD be afraid. This is mainly useful
   * to appease the compiler in various scenarios of unreachable code.
   */
  void replace_opcode_with_infinite_loop(IRInstruction* from) {
    m_ir_list->replace_opcode_with_infinite_loop(from);
  }

  /* Like replace_opcode, but both :from and :to must be branch opcodes.
   * :to will end up jumping to the same destination as :from. */
  void replace_branch(IRInstruction* from, IRInstruction* to) {
    m_ir_list->replace_branch(from, to);
  }

  template <class... Args>
  void push_back(Args&&... args) {
    m_ir_list->push_back(*(new MethodItemEntry(std::forward<Args>(args)...)));
  }

  /* Passes memory ownership of "mie" to callee. */
  void push_back(MethodItemEntry& mie) { m_ir_list->push_back(mie); }

  /*
   * Insert after instruction :position.
   *
   * position = nullptr means we insert at the head
   *
   * If position is an instruction that has a move-result-pseudo suffix, we
   * will do the insertion after the move-result-pseudo.
   */
  void insert_after(IRInstruction* position,
                    const std::vector<IRInstruction*>& opcodes) {
    m_ir_list->insert_after(position, opcodes);
  }

  IRList::iterator insert_before(const IRList::iterator& position,
                                 MethodItemEntry& mie) {
    return m_ir_list->insert_before(position, mie);
  }

  IRList::iterator insert_after(const IRList::iterator& position,
                                MethodItemEntry& mie) {
    return m_ir_list->insert_after(position, mie);
  }

  template <class... Args>
  IRList::iterator insert_before(const IRList::iterator& position,
                                 Args&&... args) {
    return m_ir_list->insert_before(
        position, *(new MethodItemEntry(std::forward<Args>(args)...)));
  }

  template <class... Args>
  IRList::iterator insert_after(const IRList::iterator& position,
                                Args&&... args) {
    always_assert(position != m_ir_list->end());
    return m_ir_list->insert_after(
        position, *(new MethodItemEntry(std::forward<Args>(args)...)));
  }

  /* DEPRECATED! Use the version below that passes in the iterator instead,
   * which is O(1) instead of O(n). */
  /* Memory ownership of "insn" passes to callee, it will delete it. */
  void remove_opcode(IRInstruction* insn) { m_ir_list->remove_opcode(insn); }

  /*
   * Remove the instruction that :it points to.
   *
   * If :it points to an instruction that has a move-result-pseudo suffix, we
   * remove both that instruction and the move-result-pseudo that follows.
   */
  void remove_opcode(const IRList::iterator& it) {
    m_ir_list->remove_opcode(it);
  }

  /*
   * Returns an estimate of the number of 2-byte code units needed to encode
   * all the instructions.
   */
  size_t sum_opcode_sizes() const;

  // similar to sum_opcode_sizes, but takes into account non-opcode payloads
  uint32_t estimate_code_units() const;

  /*
   * Returns the number of instructions.
   */
  size_t count_opcodes() const;

  void sanity_check() const { m_ir_list->sanity_check(); }

  bool has_try_blocks() const;

  bool is_unreachable() const;

  IRList::iterator begin() { return m_ir_list->begin(); }
  IRList::iterator end() { return m_ir_list->end(); }
  IRList::const_iterator begin() const { return m_ir_list->begin(); }
  IRList::const_iterator end() const { return m_ir_list->end(); }
  IRList::const_iterator cbegin() const { return m_ir_list->cbegin(); }
  IRList::const_iterator cend() const { return m_ir_list->cend(); }
  IRList::reverse_iterator rbegin() { return m_ir_list->rbegin(); }
  IRList::reverse_iterator rend() { return m_ir_list->rend(); }
  IRList::const_reverse_iterator rbegin() const { return m_ir_list->rbegin(); }
  IRList::const_reverse_iterator rend() const { return m_ir_list->rend(); }

  IRList::iterator main_block() { return m_ir_list->main_block(); }

  IRList::iterator erase(const IRList::iterator& it) {
    return m_ir_list->erase(it);
  }
  IRList::iterator erase_and_dispose(const IRList::iterator& it) {
    if (m_owns_insns) {
      return m_ir_list->insn_erase_and_dispose(it);
    } else {
      return m_ir_list->erase_and_dispose(it);
    }
  }

  IRList::iterator iterator_to(MethodItemEntry& mie) {
    return m_ir_list->iterator_to(mie);
  }

  void chain_consecutive_source_blocks() {
    m_ir_list->chain_consecutive_source_blocks();
  }

  friend std::string show(const IRCode*, bool code_only);

  friend class MethodSplicer;
};
