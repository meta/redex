/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "PositionAmbiguity.h"

#include <optional>
#include <utility>
#include <vector>

#include <boost/functional/hash.hpp>

#include "ControlFlow.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexClass.h"
#include "IROpcode.h"
#include "RedexContext.h"

namespace positions {

namespace {

// The position governing each throwing instruction in `block`, in order.
// `get_dbg_pos` resolves what the block inherits from a unique predecessor;
// the walk then follows the block's own position entries.
std::vector<DexPosition*> throwing_positions(cfg::ControlFlowGraph& cfg,
                                             cfg::Block* block) {
  std::vector<DexPosition*> result;
  auto instructions = ir_list::InstructionIterable(block);
  if (instructions.begin() == instructions.end()) {
    return result;
  }
  auto* position =
      cfg.get_dbg_pos(block->to_cfg_instruction_iterator(instructions.begin()));
  for (auto& mie : *block) {
    if (mie.type == MFLOW_POSITION) {
      position = mie.pos.get();
    } else if (mie.type == MFLOW_OPCODE &&
               opcode::can_throw(mie.insn->opcode())) {
      result.push_back(position);
    }
  }
  return result;
}

// Each throwing position of `cfg` paired with the corresponding one of
// `victim_cfg`, or std::nullopt when the two graphs do not correspond or a pair
// of corresponding blocks differs in its number of throwing instructions.
// Blocks are visited in `cfg`'s block order, so the pairs come out in an order
// that does not depend on how the pairing is stored; a block the pairing does
// not cover (one not reachable from the entry block) contributes nothing.
std::optional<std::vector<std::pair<DexPosition*, const DexPosition*>>>
paired_throwing_positions(cfg::ControlFlowGraph& cfg,
                          cfg::ControlFlowGraph& victim_cfg) {
  auto pairing = cfg.structural_block_pairing(victim_cfg);
  if (!pairing) {
    return std::nullopt;
  }
  std::vector<std::pair<DexPosition*, const DexPosition*>> pairs;
  for (auto* block : cfg.blocks()) {
    auto it = pairing->find(block);
    if (it == pairing->end()) {
      continue;
    }
    auto positions = throwing_positions(cfg, block);
    auto victim_positions =
        throwing_positions(victim_cfg, victim_cfg.get_block(it->second->id()));
    if (positions.size() != victim_positions.size()) {
      return std::nullopt;
    }
    for (size_t i = 0; i < positions.size(); ++i) {
      pairs.emplace_back(positions[i], victim_positions[i]);
    }
  }
  return pairs;
}

// Calls `f` with the position governing each throwing instruction of `cfg`.
// A block can inherit its governing position from a unique predecessor, so the
// position is resolved per instruction instead of carrying state across block
// iteration order.
template <typename F>
void for_each_throwing_position(cfg::ControlFlowGraph& cfg, F f) {
  auto instructions = cfg::InstructionIterable(cfg);
  for (auto it = instructions.begin(); it != instructions.end(); ++it) {
    if (opcode::can_throw(it->insn->opcode())) {
      f(cfg.get_dbg_pos(it));
    }
  }
}

void mark_or_count_gap(JoinStats* join_stats, DexPosition* survivor) {
  if (survivor == nullptr) {
    if (join_stats != nullptr) {
      join_stats->count_unrecorded();
    }
    return;
  }
  auto change = mark_merged(survivor);
  if (join_stats != nullptr) {
    join_stats->account(change);
  }
}

// The victim positions folded into each surviving position, gathered across
// all victims so that every surviving position is recorded in one place. Kept
// in the order the surviving positions are first seen, which is deterministic.
class FoldedPositions {
 public:
  void add_or_count_gap(JoinStats* join_stats,
                        DexPosition* survivor,
                        const DexPosition* victim) {
    if (survivor == nullptr) {
      if (join_stats != nullptr) {
        join_stats->count_unrecorded();
      }
      return;
    }
    auto [it, emplaced] = m_index.emplace(survivor, m_folded.size());
    if (emplaced) {
      m_folded.emplace_back(survivor, std::vector<const DexPosition*>());
    }
    m_folded.at(it->second).second.push_back(victim);
  }

  // Records, for each surviving position, every folded position that makes a
  // different source claim, in one call. Recording victim by victim would
  // register a growing set per victim, all of them retained.
  //
  // Every comparison is made, and every record worked out, before anything is
  // recorded. A surviving position can be the inlined caller of another
  // surviving position, and `same_source_claim` treats an unreliable caller as
  // disagreeing, so recording as we go would let one record from this join
  // flip a later comparison of exact lines.
  void record_all(JoinStats* join_stats) const {
    std::vector<std::pair<DexPosition*, std::vector<const DexPosition*>>>
        records;
    for (const auto& [survivor, victims] : m_folded) {
      std::vector<const DexPosition*> differing;
      for (const auto* victim : victims) {
        if (victim == nullptr || !same_source_claim(survivor, victim)) {
          differing.push_back(victim);
        }
      }
      if (!differing.empty()) {
        records.emplace_back(survivor, std::move(differing));
      }
    }
    auto changes = g_redex->get_position_pattern_switch_manager()
                       ->record_candidates_jointly(records);
    if (join_stats != nullptr) {
      for (auto change : changes) {
        join_stats->account(change);
      }
    }
  }

 private:
  std::vector<std::pair<DexPosition*, std::vector<const DexPosition*>>>
      m_folded;
  UnorderedMap<DexPosition*, size_t> m_index;
};

// Folds a victim whose throwing instructions cannot be paired with the
// survivor's: every surviving throwing position stands for it too, at a site
// nobody can name.
void fold_against_unnamed_sites(cfg::ControlFlowGraph& cfg,
                                FoldedPositions* folded,
                                JoinStats* join_stats) {
  if (join_stats != nullptr) {
    join_stats->count_uncorresponded();
  }
  for_each_throwing_position(cfg, [&](DexPosition* position) {
    folded->add_or_count_gap(join_stats, position, nullptr);
  });
}

// A throwing instruction's opcode and the member it refers to, which pairs it
// with its counterpart in an equivalent body whose instructions are ordered
// differently.
using MemberKey = std::pair<IROpcode, const void*>;

MemberKey member_key(const IRInstruction* insn) {
  const void* member = nullptr;
  if (insn->has_field()) {
    member = insn->get_field();
  } else if (insn->has_method()) {
    member = insn->get_method();
  } else if (insn->has_type()) {
    member = insn->get_type();
  }
  return {insn->opcode(), member};
}

// The position governing each throwing instruction, keyed by `member_key`, in
// instruction order.
class MemberPositions {
 public:
  // Returns false if `key` is already present: two throwing instructions with
  // one key cannot be paired by it.
  bool add(MemberKey key, DexPosition* position) {
    if (!m_index.emplace(key, m_entries.size()).second) {
      return false;
    }
    m_entries.emplace_back(key, position);
    return true;
  }
  bool contains(MemberKey key) const { return m_index.count(key) != 0; }
  DexPosition* at(MemberKey key) const {
    return m_entries.at(m_index.at(key)).second;
  }
  size_t size() const { return m_entries.size(); }
  auto begin() const { return m_entries.begin(); }
  auto end() const { return m_entries.end(); }

 private:
  std::vector<std::pair<MemberKey, DexPosition*>> m_entries;
  UnorderedMap<MemberKey, size_t, boost::hash<MemberKey>> m_index;
};

std::optional<MemberPositions> throwing_positions_by_member(
    cfg::ControlFlowGraph& cfg) {
  MemberPositions result;
  auto instructions = cfg::InstructionIterable(cfg);
  for (auto it = instructions.begin(); it != instructions.end(); ++it) {
    if (opcode::can_throw(it->insn->opcode()) &&
        !result.add(member_key(it->insn), cfg.get_dbg_pos(it))) {
      return std::nullopt;
    }
  }
  return result;
}

} // namespace

void mark_ambiguous_throwing_positions(DexMethod* survivor,
                                       JoinStats* join_stats) {
  auto* code = survivor->get_code();
  if (code == nullptr) {
    return;
  }
  always_assert(code->cfg_built());
  // No source position corresponds one-to-one with a body reused for another
  // method, so record uncertainty without inventing a candidate.
  for_each_throwing_position(code->cfg(), [&](DexPosition* position) {
    mark_or_count_gap(join_stats, position);
  });
}

void join_throwing_positions(DexMethod* survivor,
                             const std::vector<DexMethod*>& victims,
                             JoinStats* join_stats) {
  auto* code = survivor->get_code();
  if (code == nullptr) {
    return;
  }
  always_assert(code->cfg_built());
  auto& cfg = code->cfg();
  FoldedPositions folded;
  for (auto* victim : victims) {
    auto* victim_code = victim->get_code();
    std::optional<std::vector<std::pair<DexPosition*, const DexPosition*>>>
        correspondence;
    if (victim_code != nullptr) {
      always_assert(victim_code->cfg_built());
      correspondence = paired_throwing_positions(cfg, victim_code->cfg());
    }
    if (!correspondence) {
      fold_against_unnamed_sites(cfg, &folded, join_stats);
      continue;
    }
    for (const auto& [position, victim_position] : *correspondence) {
      folded.add_or_count_gap(join_stats, position, victim_position);
    }
  }
  folded.record_all(join_stats);
}

void join_throwing_positions_by_member(DexMethod* survivor,
                                       const std::vector<DexMethod*>& victims,
                                       JoinStats* join_stats) {
  auto* code = survivor->get_code();
  if (code == nullptr) {
    return;
  }
  always_assert(code->cfg_built());
  auto& cfg = code->cfg();
  auto survivor_positions = throwing_positions_by_member(cfg);
  FoldedPositions folded;
  for (auto* victim : victims) {
    auto* victim_code = victim->get_code();
    std::optional<MemberPositions> victim_positions;
    if (victim_code != nullptr) {
      always_assert(victim_code->cfg_built());
      victim_positions = throwing_positions_by_member(victim_code->cfg());
    }
    const bool paired =
        survivor_positions && victim_positions &&
        victim_positions->size() == survivor_positions->size() &&
        std::all_of(survivor_positions->begin(), survivor_positions->end(),
                    [&](const auto& entry) {
                      return victim_positions->contains(entry.first);
                    });
    if (!paired) {
      fold_against_unnamed_sites(cfg, &folded, join_stats);
      continue;
    }
    for (const auto& [key, position] : *survivor_positions) {
      folded.add_or_count_gap(join_stats, position, victim_positions->at(key));
    }
  }
  folded.record_all(join_stats);
}

} // namespace positions
