/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "IRList.h"

#include <iterator>
#include <sstream>
#include <vector>

#include "Debug.h"
#include "DexClass.h"
#include "DexDebugInstruction.h"
#include "DexInstruction.h"
#include "DexPosition.h"
#include "IRInstruction.h"
#include "Show.h"

bool TryEntry::operator==(const TryEntry& other) const {
  return type == other.type && *catch_start == *other.catch_start;
}

bool CatchEntry::operator==(const CatchEntry& other) const {
  if (catch_type != other.catch_type) {
    return false;
  }
  if (next == other.next) {
    return true;
  }
  if (next == nullptr || other.next == nullptr) {
    return false;
  }
  return *next == *other.next;
}

bool BranchTarget::operator==(const BranchTarget& other) const {
  if (type != other.type) {
    return false;
  }
  if (src == other.src) {
    return true;
  }
  if (src == nullptr || other.src == nullptr) {
    return false;
  }
  return *src == *other.src;
}

std::ostream& operator<<(std::ostream& os, const MethodItemType& type) {
  switch (type) {
  case MFLOW_TRY:
    os << "try";
    return os;
  case MFLOW_CATCH:
    os << "catch";
    return os;
  case MFLOW_OPCODE:
    os << "opcode";
    return os;
  case MFLOW_DEX_OPCODE:
    os << "dex-opcode";
    return os;
  case MFLOW_TARGET:
    os << "target";
    return os;
  case MFLOW_DEBUG:
    os << "debug";
    return os;
  case MFLOW_POSITION:
    os << "position";
    return os;
  case MFLOW_SOURCE_BLOCK:
    os << "source-block";
    return os;
  case MFLOW_REMARK:
    os << "remark";
    return os;
  case MFLOW_FALLTHROUGH:
    os << "fallthrough";
    return os;
  }
  os << "unknown type " << (uint32_t)type;
  return os;
}

MethodItemEntry::MethodItemEntry(std::unique_ptr<DexDebugInstruction> dbgop)
    : type(MFLOW_DEBUG), dbgop(std::move(dbgop)) {}

MethodItemEntry::MethodItemEntry(std::unique_ptr<DexPosition> pos)
    : type(MFLOW_POSITION), pos(std::move(pos)) {}

MethodItemEntry::MethodItemEntry(std::unique_ptr<SourceBlock> src_block)
    : type(MFLOW_SOURCE_BLOCK), src_block(std::move(src_block)) {}

MethodItemEntry::MethodItemEntry(std::unique_ptr<Remark> remark)
    : type(MFLOW_REMARK), remark(std::move(remark)) {}

MethodItemEntry::MethodItemEntry(const MethodItemEntry& that)
    : type(that.type) {
  switch (type) {
  case MFLOW_TRY:
    tentry = that.tentry;
    break;
  case MFLOW_CATCH:
    centry = that.centry;
    break;
  case MFLOW_OPCODE:
    insn = that.insn;
    break;
  case MFLOW_DEX_OPCODE:
    dex_insn = that.dex_insn;
    break;
  case MFLOW_TARGET:
    target = that.target;
    break;
  case MFLOW_DEBUG:
    new (&dbgop) std::unique_ptr<DexDebugInstruction>(that.dbgop->clone());
    break;
  case MFLOW_POSITION:
    new (&pos) std::unique_ptr<DexPosition>(new DexPosition(*that.pos));
    break;
  case MFLOW_SOURCE_BLOCK:
    new (&src_block)
        std::unique_ptr<SourceBlock>(new SourceBlock(*that.src_block));
    break;
  case MFLOW_REMARK:
    new (&remark) std::unique_ptr<Remark>(new Remark(*that.remark));
    break;
  case MFLOW_FALLTHROUGH:
    break;
  }
}

namespace {

void free_mie_contents(MethodItemEntry& mie) {
  switch (mie.type) {
  case MFLOW_TRY:
    delete mie.tentry;
    break;
  case MFLOW_CATCH:
    delete mie.centry;
    break;
  case MFLOW_TARGET:
    delete mie.target;
    break;
  case MFLOW_DEBUG:
    mie.dbgop.~unique_ptr<DexDebugInstruction>();
    break;
  case MFLOW_POSITION:
    mie.pos.~unique_ptr<DexPosition>();
    break;
  case MFLOW_SOURCE_BLOCK:
    mie.src_block.~unique_ptr<SourceBlock>();
    break;
  case MFLOW_REMARK:
    mie.remark.~unique_ptr<Remark>();
    break;
  case MFLOW_DEX_OPCODE:
    delete mie.dex_insn;
    break;
  case MFLOW_OPCODE:
  case MFLOW_FALLTHROUGH:
    /* nothing to delete */
    break;
  }
}

} // namespace

MethodItemEntry& MethodItemEntry::operator=(const MethodItemEntry& that) {
  if (this == &that) {
    return *this;
  }
  free_mie_contents(*this);
  type = that.type;
  switch (type) {
  case MFLOW_TRY:
    tentry = that.tentry;
    break;
  case MFLOW_CATCH:
    centry = that.centry;
    break;
  case MFLOW_OPCODE:
    insn = that.insn;
    break;
  case MFLOW_DEX_OPCODE:
    dex_insn = that.dex_insn;
    break;
  case MFLOW_TARGET:
    target = that.target;
    break;
  case MFLOW_DEBUG:
    new (&dbgop) std::unique_ptr<DexDebugInstruction>(that.dbgop->clone());
    break;
  case MFLOW_POSITION:
    new (&pos) std::unique_ptr<DexPosition>(new DexPosition(*that.pos));
    break;
  case MFLOW_SOURCE_BLOCK:
    new (&src_block)
        std::unique_ptr<SourceBlock>(new SourceBlock(*that.src_block));
    break;
  case MFLOW_REMARK:
    new (&remark) std::unique_ptr<Remark>(new Remark(*that.remark));
    break;
  case MFLOW_FALLTHROUGH:
    break;
  }
  return *this;
}

MethodItemEntry::~MethodItemEntry() { free_mie_contents(*this); }

void MethodItemEntry::replace_ir_with_dex(DexInstruction* dex_insn) {
  always_assert(type == MFLOW_OPCODE);
  delete this->insn;
  this->type = MFLOW_DEX_OPCODE;
  this->dex_insn = dex_insn;
}

void MethodItemEntry::gather_strings(
    std::vector<const DexString*>& lstring) const {
  switch (type) {
  case MFLOW_TRY:
    break;
  case MFLOW_CATCH:
    break;
  case MFLOW_OPCODE:
    insn->gather_strings(lstring);
    break;
  case MFLOW_DEX_OPCODE:
    dex_insn->gather_strings(lstring);
    break;
  case MFLOW_TARGET:
    break;
  case MFLOW_DEBUG:
    dbgop->gather_strings(lstring);
    break;
  case MFLOW_POSITION:
    // although DexPosition contains strings, these strings don't find their
    // way into the APK
    break;
  case MFLOW_SOURCE_BLOCK:
  // A Remark's strings (producer and val_str) are redex-internal and MUST NOT
  // be interned into the dex string pool -- deliberately not gathered (see
  // struct Remark).
  case MFLOW_REMARK:
  case MFLOW_FALLTHROUGH:
    break;
  }
}

void MethodItemEntry::gather_methods(
    std::vector<DexMethodRef*>& lmethod) const {
  switch (type) {
  case MFLOW_TRY:
  case MFLOW_CATCH:
  case MFLOW_POSITION:
  case MFLOW_FALLTHROUGH:
  case MFLOW_TARGET:
  // SourceBlock does not keep the method reachable.
  case MFLOW_SOURCE_BLOCK:
  // Remark does not keep the method reachable.
  case MFLOW_REMARK:
  // DexDebugInstruction does not have method reference.
  case MFLOW_DEBUG:
    break;
  case MFLOW_OPCODE:
    insn->gather_methods(lmethod);
    break;
  case MFLOW_DEX_OPCODE:
    dex_insn->gather_methods(lmethod);
    break;
  }
}

void MethodItemEntry::gather_protos(std::vector<DexProto*>& lproto) const {
  switch (type) {
  case MFLOW_TRY:
  case MFLOW_CATCH:
  case MFLOW_POSITION:
  case MFLOW_FALLTHROUGH:
  case MFLOW_TARGET:
  case MFLOW_SOURCE_BLOCK:
  case MFLOW_REMARK:
  case MFLOW_DEBUG:
    break;
  case MFLOW_OPCODE:
    insn->gather_protos(lproto);
    break;
  case MFLOW_DEX_OPCODE:
    dex_insn->gather_protos(lproto);
    break;
  }
}

void MethodItemEntry::gather_callsites(
    std::vector<DexCallSite*>& lcallsite) const {
  switch (type) {
  case MFLOW_TRY:
  case MFLOW_CATCH:
  case MFLOW_POSITION:
  case MFLOW_FALLTHROUGH:
  case MFLOW_TARGET:
  case MFLOW_SOURCE_BLOCK:
  case MFLOW_REMARK:
    break;
  case MFLOW_OPCODE:
    insn->gather_callsites(lcallsite);
    break;
  case MFLOW_DEX_OPCODE:
    dex_insn->gather_callsites(lcallsite);
    break;
  case MFLOW_DEBUG:
    dbgop->gather_callsites(lcallsite);
    break;
  }
}

void MethodItemEntry::gather_methodhandles(
    std::vector<DexMethodHandle*>& lmethodhandle) const {
  switch (type) {
  case MFLOW_TRY:
    break;
  case MFLOW_CATCH:
    break;
  case MFLOW_OPCODE:
    insn->gather_methodhandles(lmethodhandle);
    break;
  case MFLOW_DEX_OPCODE:
    dex_insn->gather_methodhandles(lmethodhandle);
    break;
  case MFLOW_TARGET:
    break;
  case MFLOW_DEBUG:
    dbgop->gather_methodhandles(lmethodhandle);
    break;
  case MFLOW_POSITION:
    break;
  case MFLOW_SOURCE_BLOCK:
    break;
  case MFLOW_REMARK:
    break;
  case MFLOW_FALLTHROUGH:
    break;
  }
}

void MethodItemEntry::gather_fields(std::vector<DexFieldRef*>& lfield) const {
  switch (type) {
  case MFLOW_TRY:
    break;
  case MFLOW_CATCH:
    break;
  case MFLOW_OPCODE:
    insn->gather_fields(lfield);
    break;
  case MFLOW_DEX_OPCODE:
    dex_insn->gather_fields(lfield);
    break;
  case MFLOW_TARGET:
    break;
  case MFLOW_DEBUG:
    dbgop->gather_fields(lfield);
    break;
  case MFLOW_POSITION:
    break;
  case MFLOW_SOURCE_BLOCK:
    break;
  case MFLOW_REMARK:
    break;
  case MFLOW_FALLTHROUGH:
    break;
  }
}

void MethodItemEntry::gather_types(std::vector<const DexType*>& ltype) const {
  switch (type) {
  case MFLOW_TRY:
    break;
  case MFLOW_CATCH:
    if (centry->catch_type != nullptr) {
      ltype.push_back(centry->catch_type);
    }
    break;
  case MFLOW_OPCODE:
    insn->gather_types(ltype);
    break;
  case MFLOW_DEX_OPCODE:
    dex_insn->gather_types(ltype);
    break;
  case MFLOW_TARGET:
    break;
  case MFLOW_DEBUG:
    dbgop->gather_types(ltype);
    break;
  case MFLOW_POSITION:
    break;
  case MFLOW_SOURCE_BLOCK:
    break;
  case MFLOW_REMARK:
    break;
  case MFLOW_FALLTHROUGH:
    break;
  }
}

void MethodItemEntry::gather_init_classes(
    std::vector<const DexType*>& ltype) const {
  if (type == MFLOW_OPCODE) {
    insn->gather_init_classes(ltype);
  }
}

opcode::Branchingness MethodItemEntry::branchingness() const {
  switch (type) {
  case MFLOW_OPCODE:
    return opcode::branchingness(insn->opcode());
  case MFLOW_DEX_OPCODE:
    not_reached_log("Not expecting dex instructions here");
  default:
    return opcode::BRANCH_NONE;
  }
}

MethodItemEntryCloner::MethodItemEntryCloner() {
  m_entry_map[nullptr] = nullptr;
  m_pos_map[nullptr] = nullptr;
}

MethodItemEntry* MethodItemEntryCloner::clone(const MethodItemEntry* mie) {

  const auto& pair = m_entry_map.emplace(mie, nullptr);
  const auto& it = pair.first;
  bool was_already_there = !pair.second;
  if (was_already_there) {
    return it->second;
  }
  auto* cloned_mie = new MethodItemEntry(*mie);
  it->second = cloned_mie;

  switch (cloned_mie->type) {
  case MFLOW_TRY:
    cloned_mie->tentry = new TryEntry(*cloned_mie->tentry);
    cloned_mie->tentry->catch_start = clone(cloned_mie->tentry->catch_start);
    return cloned_mie;
  case MFLOW_CATCH:
    cloned_mie->centry = new CatchEntry(*cloned_mie->centry);
    cloned_mie->centry->next = clone(cloned_mie->centry->next);
    return cloned_mie;
  case MFLOW_OPCODE: {
    auto* insn = cloned_mie->insn;
    if (insn->has_data()) {
      cloned_mie->insn = new IRInstruction(insn->opcode());
      always_assert(!insn->has_dest());
      always_assert(insn->srcs_size() <= 1);
      if (insn->srcs_size() == 1) {
        cloned_mie->insn->set_src(0, insn->src(0));
      }
      cloned_mie->insn->set_data(insn->get_data()->clone_as_unique_ptr());
    } else {
      cloned_mie->insn = new IRInstruction(*insn);
    }
    return cloned_mie;
  }
  case MFLOW_TARGET:
    cloned_mie->target = new BranchTarget(*cloned_mie->target);
    cloned_mie->target->src = clone(cloned_mie->target->src);
    return cloned_mie;
  case MFLOW_DEBUG:
    return cloned_mie;
  case MFLOW_POSITION:
    m_pos_map[mie->pos.get()] = cloned_mie->pos.get();
    m_positions_to_fix.push_back(cloned_mie->pos.get());
    return cloned_mie;
  case MFLOW_FALLTHROUGH:
    return cloned_mie;
  case MFLOW_SOURCE_BLOCK:
    return cloned_mie;
  case MFLOW_REMARK:
    // The MethodItemEntry copy ctor already deep-copied the payload; unlike
    // MFLOW_POSITION, a block-anchored Remark has no parent chain to remap.
    return cloned_mie;
  case MFLOW_DEX_OPCODE:
    not_reached_log("DexInstructions not expected here");
  }
}

void MethodItemEntryCloner::fix_parent_positions(
    const DexPosition* ignore_pos) {
  // When the DexPosition was copied, the parent pointer was shallowly copied
  for (DexPosition* pos : m_positions_to_fix) {
    if (pos->parent != ignore_pos) {
      pos->parent = m_pos_map.at(pos->parent);
    }
  }
}

bool MethodItemEntry::operator==(const MethodItemEntry& that) const {
  if (type != that.type) {
    return false;
  }

  switch (type) {
  case MFLOW_TRY:
    return *tentry == *that.tentry;
  case MFLOW_CATCH:
    return *centry == *that.centry;
  case MFLOW_OPCODE:
    return *insn == *that.insn;
  case MFLOW_DEX_OPCODE:
    return *dex_insn == *that.dex_insn;
  case MFLOW_TARGET:
    return *target == *that.target;
  case MFLOW_DEBUG:
    return *dbgop == *that.dbgop;
  case MFLOW_POSITION:
    return *pos == *that.pos;
  case MFLOW_SOURCE_BLOCK: {
    const SourceBlock* cur = src_block.get();
    const SourceBlock* other_cur = that.src_block.get();
    while (true) {
      // If both are null, they are equivalent and we are done
      if (cur == nullptr && other_cur == nullptr) {
        return true;
      }
      // If only one is null, they are not equivalent
      if (cur == nullptr || other_cur == nullptr) {
        return false;
      }
      // If they are not equal, return false
      if (*cur != *other_cur) {
        return false;
      }
      cur = cur->next.get();
      other_cur = other_cur->next.get();
    }
  }
  case MFLOW_REMARK:
    return *remark == *that.remark;
  case MFLOW_FALLTHROUGH:
    return true;
  };

  not_reached();
}

// TODO: T62185151 - better way of applying this on CFGs
void IRList::cleanup_debug(UnorderedSet<reg_t>& valid_regs) {
  auto it = m_list.begin();
  while (it != m_list.end()) {
    auto next = std::next(it);
    if (it->type == MFLOW_DEBUG) {
      switch (it->dbgop->opcode()) {
      case DBG_SET_PROLOGUE_END:
        this->erase_and_dispose(it);
        break;
      case DBG_START_LOCAL:
      case DBG_START_LOCAL_EXTENDED: {
        auto reg = it->dbgop->uvalue();
        valid_regs.insert(reg);
        break;
      }
      case DBG_END_LOCAL:
      case DBG_RESTART_LOCAL: {
        auto reg = it->dbgop->uvalue();
        if (valid_regs.find(reg) == valid_regs.end()) {
          this->erase_and_dispose(it);
        }
        break;
      }
      default:
        break;
      }
    }
    it = next;
  }
}

void IRList::cleanup_debug() {
  UnorderedSet<reg_t> valid_regs;
  cleanup_debug(valid_regs);
}

void IRList::replace_opcode(IRInstruction* to_delete,
                            const std::vector<IRInstruction*>& replacements) {
  auto it = m_list.begin();
  for (; it != m_list.end(); it++) {
    if (it->type == MFLOW_OPCODE && it->insn == to_delete) {
      break;
    }
  }
  always_assert_log(it != m_list.end(),
                    "No match found while replacing '%s'",
                    SHOW(to_delete));
  replace_opcode(it, replacements);
}

void IRList::replace_opcode(const IRList::iterator& it,
                            const std::vector<IRInstruction*>& replacements) {
  always_assert(it->type == MFLOW_OPCODE);
  for (auto* insn : replacements) {
    insert_before(it, insn);
  }
  remove_opcode(it);
}

void IRList::replace_opcode(IRInstruction* from, IRInstruction* to) {
  always_assert_log(!opcode::is_branch(to->opcode()),
                    "You may want replace_branch instead");
  replace_opcode(from, std::vector<IRInstruction*>{to});
}

void IRList::replace_opcode_with_infinite_loop(IRInstruction* from) {
  IRInstruction* to = new IRInstruction(OPCODE_GOTO);
  auto miter = m_list.begin();
  for (; miter != m_list.end(); miter++) {
    MethodItemEntry* mentry = &*miter;
    if (mentry->type == MFLOW_OPCODE && mentry->insn == from) {
      if (opcode::is_branch(from->opcode())) {
        remove_branch_targets(from);
      }
      mentry->insn = to;
      delete from;
      break;
    }
  }
  always_assert_log(miter != m_list.end(),
                    "No match found while replacing '%s' with '%s'",
                    SHOW(from),
                    SHOW(to));
  auto* target = new BranchTarget(&*miter);
  m_list.insert(miter, *(new MethodItemEntry(target)));
}

void IRList::replace_branch(IRInstruction* from, IRInstruction* to) {
  always_assert(opcode::is_branch(from->opcode()));
  always_assert(opcode::is_branch(to->opcode()));
  for (auto& mentry : m_list) {
    if (mentry.type == MFLOW_OPCODE && mentry.insn == from) {
      mentry.insn = to;
      delete from;
      return;
    }
  }
  not_reached_log("No match found while replacing '%s' with '%s'", SHOW(from),
                  SHOW(to));
}

void IRList::insert_after(IRInstruction* position,
                          const std::vector<IRInstruction*>& opcodes) {
  /* The nullptr case handling is strange-ish..., this will not work as expected
   * if a method has a branch target as its first instruction.
   *
   * To handle this case sanely, we'd need to export an interface based on
   * MEI's probably.
   */
  for (auto const& mei : m_list) {
    if (mei.type == MFLOW_OPCODE &&
        (position == nullptr || mei.insn == position)) {
      auto insert_at = m_list.iterator_to(mei);
      if (position != nullptr) {
        insert_at++;
        if (position->has_move_result_pseudo()) {
          insert_at++;
        }
      }
      for (auto* opcode : opcodes) {
        MethodItemEntry* mentry = new MethodItemEntry(opcode);
        m_list.insert(insert_at, *mentry);
      }
      return;
    }
  }
  not_reached_log("No match found");
}

IRList::iterator IRList::insert_before(const IRList::iterator& position,
                                       MethodItemEntry& mie) {
  return m_list.insert(position, mie);
}

IRList::iterator IRList::insert_after(const IRList::iterator& position,
                                      MethodItemEntry& mie) {
  always_assert(position != m_list.end());
  return m_list.insert(std::next(position), mie);
}

void IRList::remove_opcode(const IRList::iterator& it) {
  always_assert(it->type == MFLOW_OPCODE);
  auto* insn = it->insn;
  always_assert(!opcode::is_a_move_result_pseudo(insn->opcode()));
  if (insn->has_move_result_pseudo()) {
    auto move_it = std::next(it);
    always_assert_log(
        move_it->type == MFLOW_OPCODE &&
            opcode::is_a_move_result_pseudo(move_it->insn->opcode()),
        "No move-result-pseudo found for %s",
        SHOW(insn));
    delete move_it->insn;
    move_it->type = MFLOW_FALLTHROUGH;
    move_it->insn = nullptr;
  }
  if (opcode::is_branch(insn->opcode())) {
    remove_branch_targets(insn);
  }
  it->type = MFLOW_FALLTHROUGH;
  it->insn = nullptr;
  delete insn;
}

void IRList::remove_opcode(IRInstruction* insn) {
  for (auto& mei : m_list) {
    if (mei.type == MFLOW_OPCODE && mei.insn == insn) {
      auto it = m_list.iterator_to(mei);
      remove_opcode(it);
      return;
    }
  }
  not_reached_log("No match found while removing '%s' from method", SHOW(insn));
}

size_t IRList::sum_opcode_sizes() const {
  uint32_t size{0};
  for (const auto& mie : m_list) {
    if (mie.type == MFLOW_OPCODE) {
      size += mie.insn->size();
    }
  }
  return size;
}

uint32_t IRList::estimate_code_units() const {
  uint32_t code_units{0};
  for (const auto& mie : m_list) {
    if (mie.type == MFLOW_OPCODE) {
      code_units += mie.insn->size();
      if (opcode::is_fill_array_data(mie.insn->opcode())) {
        // DexOpcodeData::size() is the size of the entire
        // fill-array-data-payload, already including its four header code
        // units (ident, element_width, and the two size words).
        auto* data = mie.insn->get_data();
        code_units += data->size();
      }
    }
  }
  return code_units;
}

size_t IRList::count_opcodes() const {
  size_t count{0};
  for (const auto& mie : m_list) {
    if (mie.type == MFLOW_OPCODE &&
        !opcode::is_an_internal(mie.insn->opcode())) {
      ++count;
    }
  }
  return count;
}

void IRList::sanity_check() const {
  UnorderedSet<const MethodItemEntry*> entries;
  for (const auto& mie : m_list) {
    entries.insert(&mie);
  }
  for (const auto& mie : m_list) {
    if (mie.type == MFLOW_TARGET) {
      always_assert(entries.count(mie.target->src) > 0);
    }
  }
}

/*
 * This method fixes the goto branches when the instruction is removed or
 * replaced by another instruction.
 */
void IRList::remove_branch_targets(IRInstruction* branch_inst) {
  always_assert_log(opcode::is_branch(branch_inst->opcode()),
                    "Instruction is not a branch instruction.");
  for (auto miter = m_list.begin(); miter != m_list.end(); miter++) {
    MethodItemEntry* mentry = &*miter;
    if (mentry->type == MFLOW_TARGET) {
      BranchTarget* bt = mentry->target;
      auto* btmei = bt->src;
      if (btmei->insn == branch_inst) {
        mentry->type = MFLOW_FALLTHROUGH;
        delete mentry->target;
      }
    }
  }
}

bool IRList::structural_equals(
    const IRList& other, const InstructionEquality& instruction_equals) const {
  auto it1 = m_list.begin();
  auto it2 = other.begin();

  UnorderedMap<const MethodItemEntry*, const MethodItemEntry*> matches;
  UnorderedMap<const MethodItemEntry*, const MethodItemEntry*> delayed_matches;
  auto may_match = [&](const MethodItemEntry* mie1,
                       const MethodItemEntry* mie2) {
    always_assert(mie1 && !is_metadata(mie1->type));
    always_assert(mie2 && !is_metadata(mie2->type));
    auto it = matches.find(mie1);
    if (it != matches.end()) {
      return it->second == mie2;
    }
    auto p = delayed_matches.emplace(mie1, mie2);
    return p.second || p.first->second == mie2;
  };
  for (; it1 != m_list.end() && it2 != other.end();) {
    always_assert(it1->type != MFLOW_DEX_OPCODE);
    always_assert(it2->type != MFLOW_DEX_OPCODE);
    // Skip metadata (debug, position, source block, remark).
    if (is_metadata(it1->type)) {
      ++it1;
      continue;
    }

    if (is_metadata(it2->type)) {
      ++it2;
      continue;
    }

    if (it1->type != it2->type) {
      return false;
    }

    auto it = delayed_matches.find(&*it1);
    if (it != delayed_matches.end()) {
      if (it->second != &*it2) {
        return false;
      }
      delayed_matches.erase(it);
    }
    matches.emplace(&*it1, &*it2);

    if (it1->type == MFLOW_OPCODE) {
      if (!instruction_equals(*it1->insn, *it2->insn)) {
        return false;
      }
    } else if (it1->type == MFLOW_TARGET) {
      auto* target1 = it1->target;
      auto* target2 = it2->target;

      if (target1->type != target2->type) {
        return false;
      }

      if (target1->type == BRANCH_MULTI &&
          target1->case_key != target2->case_key) {
        return false;
      }

      // Do these targets point back to the same branch instruction?
      if (!may_match(target1->src, target2->src)) {
        return false;
      }

    } else if (it1->type == MFLOW_TRY) {
      auto* try1 = it1->tentry;
      auto* try2 = it2->tentry;

      if (try1->type != try2->type) {
        return false;
      }

      // Do these `try`s correspond to the same catch block?
      if (!may_match(try1->catch_start, try2->catch_start)) {
        return false;
      }
    } else if (it1->type == MFLOW_CATCH) {
      auto* catch1 = it1->centry;
      auto* catch2 = it2->centry;

      if (catch1->catch_type != catch2->catch_type) {
        return false;
      }

      if ((catch1->next == nullptr && catch2->next != nullptr) ||
          (catch1->next != nullptr && catch2->next == nullptr)) {
        return false;
      }

      // Do these `catch`es have the same catch after them?
      if (catch1->next != nullptr && !may_match(catch1->next, catch2->next)) {
        return false;
      }
    }
    ++it1;
    ++it2;
  }

  if (it1 == this->end() && it2 == other.end()) {
    always_assert(delayed_matches.empty());
    return true;
  }
  return false;
}

boost::sub_range<IRList> IRList::get_param_instructions() {
  auto params_end = std::find_if_not(
      m_list.begin(), m_list.end(), [&](const MethodItemEntry& mie) {
        return mie.type == MFLOW_FALLTHROUGH ||
               (mie.type == MFLOW_OPCODE &&
                opcode::is_a_load_param(mie.insn->opcode()));
      });
  return boost::sub_range<IRList>(m_list.begin(), params_end);
}

void IRList::gather_catch_types(std::vector<const DexType*>& ltype) const {
  for (const auto& mie : m_list) {
    if (mie.type != MFLOW_CATCH) {
      continue;
    }
    if (mie.centry->catch_type != nullptr) {
      ltype.push_back(mie.centry->catch_type);
    }
  }
}

void IRList::gather_types(std::vector<const DexType*>& ltype) const {
  for (const auto& mie : m_list) {
    mie.gather_types(ltype);
  }
}

void IRList::gather_init_classes(std::vector<const DexType*>& ltype) const {
  for (const auto& mie : m_list) {
    mie.gather_init_classes(ltype);
  }
}

void IRList::gather_strings(std::vector<const DexString*>& lstring) const {
  for (const auto& mie : m_list) {
    mie.gather_strings(lstring);
  }
}

void IRList::gather_fields(std::vector<DexFieldRef*>& lfield) const {
  for (const auto& mie : m_list) {
    mie.gather_fields(lfield);
  }
}

void IRList::gather_methods(std::vector<DexMethodRef*>& lmethod) const {
  for (const auto& mie : m_list) {
    mie.gather_methods(lmethod);
  }
}

void IRList::gather_callsites(std::vector<DexCallSite*>& lcallsite) const {
  for (const auto& mie : m_list) {
    mie.gather_callsites(lcallsite);
  }
}

void IRList::gather_protos(std::vector<DexProto*>& lproto) const {
  for (const auto& mie : m_list) {
    mie.gather_protos(lproto);
  }
}

void IRList::gather_methodhandles(
    std::vector<DexMethodHandle*>& lmethodhandle) const {
  for (const auto& mie : m_list) {
    mie.gather_methodhandles(lmethodhandle);
  }
}

IRList::iterator IRList::main_block() {
  return std::prev(get_param_instructions().end());
}

IRList::iterator IRList::make_if_block(const IRList::iterator& cur,
                                       IRInstruction* insn,
                                       IRList::iterator* false_block) {
  auto* if_entry = new MethodItemEntry(insn);
  *false_block = m_list.insert(cur, *if_entry);
  auto* bt = new BranchTarget(if_entry);
  auto* bentry = new MethodItemEntry(bt);
  return m_list.insert(m_list.end(), *bentry);
}

IRList::iterator IRList::make_if_else_block(const IRList::iterator& cur,
                                            IRInstruction* insn,
                                            IRList::iterator* false_block,
                                            IRList::iterator* true_block) {
  // if block
  auto* if_entry = new MethodItemEntry(insn);
  *false_block = m_list.insert(cur, *if_entry);

  // end of else goto
  auto* goto_entry = new MethodItemEntry(new IRInstruction(OPCODE_GOTO));
  auto goto_it = m_list.insert(m_list.end(), *goto_entry);

  // main block
  auto* main_bt = new BranchTarget(goto_entry);
  auto* mb_entry = new MethodItemEntry(main_bt);
  auto main_block = m_list.insert(goto_it, *mb_entry);

  // else block
  auto* else_bt = new BranchTarget(if_entry);
  auto* eb_entry = new MethodItemEntry(else_bt);
  *true_block = m_list.insert(goto_it, *eb_entry);

  return main_block;
}

IRList::iterator IRList::make_switch_block(
    const IRList::iterator& cur,
    IRInstruction* insn,
    IRList::iterator* default_block,
    std::map<SwitchIndices, IRList::iterator>& cases) {
  auto* switch_entry = new MethodItemEntry(insn);
  *default_block = m_list.insert(cur, *switch_entry);
  IRList::iterator main_block = *default_block;
  for (auto case_it = cases.begin(); case_it != cases.end(); ++case_it) {
    auto* goto_entry = new MethodItemEntry(new IRInstruction(OPCODE_GOTO));
    auto goto_it = m_list.insert(m_list.end(), *goto_entry);

    auto* main_bt = new BranchTarget(goto_entry);
    auto* mb_entry = new MethodItemEntry(main_bt);
    main_block = m_list.insert(++main_block, *mb_entry);

    // Insert all the branch targets jumping from the switch entry.
    // Keep updating the iterator of the case block to point right before the
    // GOTO going back to the end of the switch.
    for (auto idx : case_it->first) {
      auto* case_bt = new BranchTarget(switch_entry, idx);
      auto* eb_entry = new MethodItemEntry(case_bt);
      case_it->second = m_list.insert(goto_it, *eb_entry);
    }
  }
  return main_block;
}

namespace ir_list {

IRInstruction* primary_instruction_of_move_result_pseudo(IRList::iterator it) {
  --it;
  always_assert_log(it->type == MFLOW_OPCODE &&
                        it->insn->has_move_result_pseudo(),
                    "%s does not have a move result pseudo", SHOW(*it));
  return it->insn;
}

IRInstruction* primary_instruction_of_move_result(IRList::iterator it) {
  // There may be debug info between primary insn and move-result*?
  do {
    --it;
  } while (it->type != MFLOW_OPCODE);
  always_assert_log(it->insn->has_move_result(),
                    "%s does not have a move result", SHOW(*it));
  return it->insn;
}

IRInstruction* move_result_pseudo_of(IRList::iterator it) {
  ++it;
  always_assert(it->type == MFLOW_OPCODE &&
                opcode::is_a_move_result_pseudo(it->insn->opcode()));
  return it->insn;
}

} // namespace ir_list

IRList::iterator IRList::insn_erase_and_dispose(const IRList::iterator& it) {
  return m_list.erase_and_dispose(it, [](auto* mie) {
    if (mie->type == MFLOW_OPCODE) {
      delete mie->insn;
    }
    delete mie;
  });
}

void IRList::insn_clear_and_dispose() {
  m_list.clear_and_dispose([](auto* mie) {
    if (mie->type == MFLOW_OPCODE) {
      delete mie->insn;
    }
    delete mie;
  });
}

SourceBlock& SourceBlock::operator=(const SourceBlock& other) {
  if (this == &other) {
    return *this;
  }
  src = other.src;
  next = std::unique_ptr<SourceBlock>(
      other.next == nullptr ? nullptr : new SourceBlock(*other.next));
  id = other.id;
  always_assert(vals_size == other.vals_size);
  m_storage = make_storage(other.m_storage.get());
  return *this;
}

std::unique_ptr<SourceBlock::Storage, SourceBlock::FreeDeleter>
SourceBlock::make_storage(size_t vals_size, const Val& val) {
  if (vals_size == 0) {
    return nullptr;
  }

  always_assert(vals_size <= InteractionBitSet::MAX_SIZE);
  size_t bytes = sizeof(Storage) + sizeof(Val) * (vals_size - 1);
  auto* res = (Storage*)malloc(bytes);
  always_assert(res);
  res->bits = InteractionBitSet::all(vals_size);
  std::fill_n(res->data, vals_size, val);
  return std::unique_ptr<Storage, FreeDeleter>(res);
}

std::unique_ptr<SourceBlock::Storage, SourceBlock::FreeDeleter>
SourceBlock::make_storage(const Storage* other) {
  if (other == nullptr) {
    return nullptr;
  }
  InteractionBitSet bits;
  auto other_bits = other->bits;
  for (size_t i = 0; other_bits; other_bits.remove_first(), i++) {
    if (!other->data[i].is_default_value()) {
      bits.add(other_bits.first());
    }
  }
  if (!bits) {
    return nullptr;
  }
  size_t bytes = sizeof(Storage) + sizeof(Val) * (bits.count() - 1);
  auto* res = (Storage*)malloc(bytes);
  always_assert(res);
  res->bits = bits;
  other_bits = other->bits;
  for (size_t i = 0, j = 0; other_bits; other_bits.remove_first(), i++) {
    if (bits.contains(other_bits.first())) {
      res->data[j++] = other->data[i];
    }
  }
  return std::unique_ptr<Storage, FreeDeleter>(res);
}

std::unique_ptr<SourceBlock::Storage, SourceBlock::FreeDeleter>
SourceBlock::make_storage(const std::vector<Val>& vals) {
  InteractionBitSet bits;
  always_assert(vals.size() <= InteractionBitSet::MAX_SIZE);
  for (size_t i = 0; i < vals.size(); i++) {
    if (!vals[i].is_default_value()) {
      bits.add(InteractionBitSet::from_index(i));
    }
  }
  if (!bits) {
    return nullptr;
  }
  size_t bytes = sizeof(Storage) + sizeof(Val) * (bits.count() - 1);
  auto* res = (Storage*)malloc(bytes);
  always_assert(res);
  res->bits = bits;
  for (size_t i = 0; bits; bits.remove_first(), i++) {
    res->data[i] = vals[bits.first_index()];
  }
  return std::unique_ptr<Storage, FreeDeleter>(res);
}

bool SourceBlock::has_all_default_values(const Storage* storage) {
  if (storage == nullptr) {
    return true;
  }
  size_t count = storage->bits.count();
  for (size_t i = 0; i < count; i++) {
    if (!storage->data[i].is_default_value()) {
      return false;
    }
  }
  return true;
}

bool SourceBlock::has_default_value(const Storage* storage) {
  if (storage == nullptr) {
    return false;
  }
  size_t count = storage->bits.count();
  for (size_t i = 0; i < count; i++) {
    if (storage->data[i].is_default_value()) {
      return true;
    }
  }
  return false;
}

bool SourceBlock::operator==(const SourceBlock& other) const {
  if (src != other.src || id != other.id || vals_size != other.vals_size) {
    return false;
  }

  if (!m_storage || !other.m_storage) {
    return has_all_default_values(m_storage.get()) &&
           has_all_default_values(other.m_storage.get());
  }

  // Check whether this has entries the other doesn't have, and whether they are
  // all the default value
  auto bits = m_storage->bits;
  bits.remove(other.m_storage->bits);
  for (; bits; bits.remove_first()) {
    size_t idx = m_storage->bits.count_before(bits.first());
    if (!m_storage->data[idx].is_default_value()) {
      return false;
    }
  }

  // Check whether all common entries are equal
  bits = m_storage->bits;
  bits.intersect_with(other.m_storage->bits);
  for (; bits; bits.remove_first()) {
    auto bit = bits.first();
    size_t idx = m_storage->bits.count_before(bit);
    size_t other_idx = other.m_storage->bits.count_before(bit);
    if (m_storage->data[idx] != other.m_storage->data[other_idx]) {
      return false;
    }
  }

  // Check whether the other has entries this doesn't have, and whether they are
  // all the default value
  bits = other.m_storage->bits;
  bits.remove(m_storage->bits);
  for (; bits; bits.remove_first()) {
    size_t other_idx = other.m_storage->bits.count_before(bits.first());
    if (!other.m_storage->data[other_idx].is_default_value()) {
      return false;
    }
  }

  return true;
}

size_t SourceBlock::hash_ids() const {
  std::size_t hash = id;
  auto* cur = this->next.get();
  while (true) {
    if (cur == nullptr) {
      break;
    }
    boost::hash_combine(hash, cur->id);
    cur = cur->next.get();
  }

  return hash;
}

const SourceBlock::Val SourceBlock::default_value =
    SourceBlock::Val::default_value();

void SourceBlock::fill(const Val& val) {
  if (val.is_default_value()) {
    m_storage.reset();
    return;
  }
  if (is_storage_expanded()) {
    if (vals_size > 0) {
      std::fill_n(m_storage->data, vals_size, val);
    }
    return;
  }
  m_storage = make_storage(vals_size, val);
}

void SourceBlock::max(const SourceBlock& other) {
  size_t len = std::min(vals_size, other.vals_size);
  auto max_val = [](Val& val, const Val& other_val) {
    if (!val) {
      val = other_val;
    } else if (other_val) {
      val->val = std::max(val->val, other_val->val);
      val->appear100 = std::max(val->appear100, other_val->appear100);
    }
  };
  for (size_t i = 0; i != len; ++i) {
    apply_at(i, [&](auto& val) { max_val(val, other.get_at(i)); });
  }
}

void SourceBlock::add(const SourceBlock& other) {
  size_t len = std::min(vals_size, other.vals_size);
  auto add_val = [](Val& val, const Val& other_val) {
    if (!val) {
      val = other_val;
    } else if (other_val) {
      val->val += other_val->val;
      // appear100 is an appearance probability in [0,100]: max, never sum.
      val->appear100 = std::max(val->appear100, other_val->appear100);
    }
  };
  for (size_t i = 0; i != len; ++i) {
    apply_at(i, [&](auto& val) { add_val(val, other.get_at(i)); });
  }
}

void SourceBlock::min(const SourceBlock& other) {
  size_t len = std::min(vals_size, other.vals_size);
  auto min_val = [](Val& val, const Val& other_val) {
    if (!val) {
      val = other_val;
    } else if (other_val) {
      val->val = std::min(val->val, other_val->val);
      val->appear100 = std::min(val->appear100, other_val->appear100);
    }
  };
  for (size_t i = 0; i != len; ++i) {
    apply_at(i, [&](auto& val) { min_val(val, other.get_at(i)); });
  }
}

bool SourceBlock::normalize(size_t* elided_vals, size_t* unelided_vals) {
  if (has_default_value(m_storage.get())) {
    m_storage = make_storage(m_storage.get());
  }
  if (!m_storage) {
    return true;
  }
  size_t count = m_storage->bits.count();
  *elided_vals += vals_size - count;
  *unelided_vals += count;
  return m_storage == nullptr;
}

void SourceBlock::expand_storage() {
  if (is_storage_expanded()) {
    return;
  }
  auto expanded_storage = make_storage(vals_size);
  if (m_storage) {
    auto bits = m_storage->bits;
    for (size_t i = 0; bits; bits.remove_first(), i++) {
      expanded_storage->data[bits.first_index()] = m_storage->data[i];
    }
  }
  m_storage = std::move(expanded_storage);
}

std::string SourceBlock::show(bool quoted_src) const {
  std::ostringstream o;

  for (const auto* cur = this; cur != nullptr; cur = cur->next.get()) {
    if (cur != this) {
      o << " ";
    }
    if (quoted_src) {
      o << "\"";
    }
    o << ::show(cur->src);
    if (quoted_src) {
      o << "\"";
    }
    o << "@" << cur->id;
    o << "(";
    cur->foreach_val([&o](const auto& val) {
      if (val) {
        o << val->val << ":" << val->appear100;
      } else {
        o << "x";
      }
      o << "|";
    });
    o << ")";
  }
  return o.str();
}

IRList::ConsecutiveStyle IRList::CONSECUTIVE_STYLE =
    IRList::ConsecutiveStyle::kMax;

void IRList::chain_consecutive_source_blocks(ConsecutiveStyle style) {
  std::optional<IRList::iterator> last_it = std::nullopt;
  for (auto it = begin(); it != end(); ++it) {
    if (it->type == MFLOW_POSITION || it->type == MFLOW_DEBUG ||
        it->type == MFLOW_REMARK) {
      // We can move over debug info and remarks. Otherwise, reset.
      continue;
    }
    if (it->type != MFLOW_SOURCE_BLOCK) {
      last_it = std::nullopt;
      continue;
    }

    if (last_it) {
      switch (style) {
      case ConsecutiveStyle::kChain:
        (*last_it)->src_block->append(std::move(it->src_block));
        break;
      case ConsecutiveStyle::kDrop:
        break;
      case ConsecutiveStyle::kMax:
        (*last_it)->src_block->max(*it->src_block);
        break;
      }

      auto prev = std::prev(it);
      erase_and_dispose(it);
      it = prev;
    } else {
      last_it = it;
    }
  }
}
