/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "PositionAmbiguity.h"

#include <algorithm>
#include <optional>
#include <vector>

#include "ControlFlow.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexClass.h"
#include "IROpcode.h"

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
// all victims so that every surviving position is joined in one place. Kept in
// the order the surviving positions are first seen, which is deterministic.
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

  // Every verdict is taken before anything is marked. A surviving position can
  // be the inlined caller of another surviving position, and
  // `same_source_claim` treats an unreliable caller as disagreeing, so marking
  // as we go would let one mark from this join flip a later verdict that
  // compared exact lines.
  void join_all(JoinStats* join_stats) const {
    std::vector<DexPosition*> disagreeing;
    for (const auto& [survivor, victims] : m_folded) {
      const bool disagrees =
          std::any_of(victims.begin(), victims.end(),
                      [kept = survivor](const DexPosition* victim) {
                        return !same_source_claim(kept, victim);
                      });
      if (disagrees) {
        disagreeing.push_back(survivor);
      }
    }
    for (auto* survivor : disagreeing) {
      auto change = mark_merged(survivor);
      if (join_stats != nullptr) {
        join_stats->account(change);
      }
    }
  }

 private:
  std::vector<std::pair<DexPosition*, std::vector<const DexPosition*>>>
      m_folded;
  UnorderedMap<DexPosition*, size_t> m_index;
};

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
      if (join_stats != nullptr) {
        join_stats->count_uncorresponded();
      }
      // Every surviving throwing position stands for this victim too, at a
      // site nobody can name.
      for_each_throwing_position(cfg, [&](DexPosition* position) {
        folded.add_or_count_gap(join_stats, position, nullptr);
      });
      continue;
    }
    for (const auto& [position, victim_position] : *correspondence) {
      folded.add_or_count_gap(join_stats, position, victim_position);
    }
  }
  folded.join_all(join_stats);
}

} // namespace positions
