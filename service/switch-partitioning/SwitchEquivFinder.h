/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <boost/variant/get.hpp>
#include <boost/variant/variant.hpp>
#include <map>
#include <optional>
#include <ostream>

#include "ConstantPropagationAnalysis.h"
#include "ControlFlow.h"
#include "DeterministicContainers.h"
#include "InstructionAnalyzer.h"
#include "SignedConstantDomain.h"

/**
 * The purpose of this class is to find control flow structures that are
 * equivalent to a switch statement. They can be any combination of ifs and
 * switches as long as the only intervening instructions are const loads that do
 * not overwrite the switching register.
 */
class SwitchEquivFinder {
 public:
  using Analyzer = InstructionAnalyzerCombiner<
      constant_propagation::ConstantClassObjectAnalyzer,
      constant_propagation::StringAnalyzer,
      constant_propagation::PrimitiveAnalyzer>;

  using DefUseBlocks = UnorderedMap<IRInstruction*, UnorderedSet<cfg::Block*>>;
  static DefUseBlocks GetDefUseBlocks(cfg::ControlFlowGraph& cfg);

  static constexpr uint32_t NO_LEAF_DUPLICATION = 0;

  // Token to denote the default case/last else block.
  struct DefaultCase {};

  // Types represented in the key to block mapping, with a special carve out for
  // the else/default. More types can be added here as necessary as this becomes
  // more capable.
  enum class KeyKind { DEFAULT, INT, CLASS };

  using SwitchingKey = boost::variant<DefaultCase, int32_t, const DexType*>;

  static bool is_default_case(const SwitchingKey& k) {
    return k.which() == static_cast<int>(KeyKind::DEFAULT);
  }

  struct key_comparator {
    bool operator()(const SwitchingKey& l, const SwitchingKey& r) const {
      auto class_kind = static_cast<int>(KeyKind::CLASS);
      if (l.which() == class_kind && r.which() == class_kind) {
        return compare_dextypes(boost::get<const DexType*>(l),
                                boost::get<const DexType*>(r));
      }
      return l < r;
    }
  };

  using KeyToCase = std::map<SwitchingKey, cfg::Block*, key_comparator>;
  using InstructionSet = std::map<reg_t, IRInstruction*>;
  using ExtraLoads = UnorderedMap<cfg::Block*, InstructionSet>;

  // Specify how the finder should behave when encountering redundant equals
  // check on the same key.
  enum DuplicateCaseStrategy { NOT_ALLOWED, EXECUTION_ORDER };

  SwitchEquivFinder(
      cfg::ControlFlowGraph* cfg,
      const cfg::InstructionIterator& root_branch,
      reg_t switching_reg,
      uint32_t leaf_duplication_threshold = NO_LEAF_DUPLICATION,
      std::shared_ptr<constant_propagation::intraprocedural::FixpointIterator>
          fixpoint_iterator = {},
      DuplicateCaseStrategy duplicates_strategy = NOT_ALLOWED,
      std::shared_ptr<DefUseBlocks> def_use_blocks = {});

  SwitchEquivFinder() = delete;
  SwitchEquivFinder(const SwitchEquivFinder&) = delete;
  SwitchEquivFinder& operator=(const SwitchEquivFinder&) = delete;

  // After construction, call `success()`, to find out if a control flow
  // structure equivalent to a switch has been found
  bool success() const { return m_success; }
  const KeyToCase& key_to_case() const { return m_key_to_case; }
  const ExtraLoads& extra_loads() const { return m_extra_loads; }
  bool duplicate_case_keys() const { return m_duplicate_case_keys; }
  // Returns if the keys in the cases are only of the specific kind or default
  // case. A method with only the default case will not be considered to be
  // uniform for other types (that is ambiguous).
  bool are_keys_uniform(KeyKind kind) const {
    bool found = false;
    auto desired_kind = static_cast<int>(kind);
    for (const auto& [key, v] : m_key_to_case) {
      if (is_default_case(key)) {
        continue;
      }
      if (key.which() == desired_kind) {
        found = true;
      } else {
        return false;
      }
    }
    return found;
  }
  // Returns the block representing the default case, if a default case is
  // present.
  std::optional<cfg::Block*> default_case() const {
    DefaultCase d;
    auto search = m_key_to_case.find(d);
    if (search == m_key_to_case.end()) {
      return std::nullopt;
    }
    return search->second;
  }

  // Return all the blocks traversed by the finder, including leaves and
  // non-leaves.
  UnorderedBag<cfg::Block*> visited_blocks() const;

 private:
  std::vector<cfg::Edge*> find_leaves();
  void normalize_extra_loads(
      const UnorderedMap<cfg::Block*, bool>& block_to_is_leaf);
  bool move_edges(
      const std::vector<std::pair<cfg::Edge*, cfg::Block*>>& edges_to_move);
  void find_case_keys(const std::vector<cfg::Edge*>& leaves);
  constant_propagation::intraprocedural::FixpointIterator& get_analyzed_cfg();
  DefUseBlocks& get_def_use_blocks();

  cfg::ControlFlowGraph* m_cfg;
  // The top-most branch instruction of the tree
  const cfg::InstructionIterator m_root_branch;
  // The register that holds the value that we're "switching" on, even if this
  // is an if-else chain and not a switch statement
  reg_t m_switching_reg;
  // When D8 converts a switch statement into an if-else chain (and constant
  // loads are lifted), then a case block may be deduplicated. The deduplicated
  // case block can have multiple incoming edges with different program states
  // on each edge. This situation is impossible to represent with a switch
  // statement because there is no place to change the state of the program
  // between a switch statment and its case blocks (where there is for an
  // if-else chain).
  //
  // The SwitchEquivFinder could represent this situation as a switch if case
  // blocks like this are duplicated. Each different program state is directed
  // to a different copy of the block. This way, each block has a separate set
  // of extra_loads. If a block has fewer than `m_leaf_duplication_threshold`
  // opcodes the SwitchEquivFinder may duplicate that block. If this flag is
  // zero, the SwitchEquivFinder will not edit the CFG.
  uint32_t m_leaf_duplication_threshold{0};
  // Analyzer for the given cfg; will be lazily constructed if not passed from
  // above.
  std::shared_ptr<constant_propagation::intraprocedural::FixpointIterator>
      m_fixpoint_iterator;
  // Specify what the finder should do if it encounters a if/else series in
  // which duplicated cases are encountered. Default behavior is for the finder
  // to not succeed, but other option can be enabled to represent only the first
  // block that would be encountered at runtime, if all later duplicates have no
  // extra loads.
  DuplicateCaseStrategy m_duplicates_strategy;
  // Def-use-blocks for the given cfg; will be lazily constructed if not passed
  // from above.
  std::shared_ptr<DefUseBlocks> m_def_use_blocks;
  // If a switch equivalent cannot be found starting from `m_root_branch` this
  // flag will be false, otherwise true.
  bool m_success{false};

  // A map from case keys to leaf blocks. The case key is the value held in
  // `m_switching_reg` upon reaching this leaf. `std::nullopt` represents the
  // fallthrough block.
  KeyToCase m_key_to_case;

  // This map represents the state of the registers upon entering a leaf block.
  // Any constant loads that occurred on all paths to a given leaf after the
  // root branch block are added to its InstructionSet. We use an ordered map
  // keyed by the destination register so that values can be overwritten and
  // iterated in a deterministic order
  ExtraLoads m_extra_loads;

  // This stores the blocks visited and how many times in building m_key_to_case
  // Note that this does not include the root branch.
  UnorderedMap<cfg::Block*, uint16_t> m_visit_count;

  bool m_duplicate_case_keys{false};
};

std::ostream& operator<<(std::ostream& os,
                         const SwitchEquivFinder::DefaultCase&);
bool operator<(const SwitchEquivFinder::DefaultCase&,
               const SwitchEquivFinder::DefaultCase&);

class SwitchEquivEditor {
 public:
  static size_t copy_extra_loads_to_leaf_block(
      const SwitchEquivFinder::ExtraLoads& extra_loads,
      cfg::ControlFlowGraph* cfg,
      cfg::Block* leaf);
  // if-else chains will load constants to compare against. Sometimes the leaves
  // will use these values so transformations may have to copy those values to
  // the beginning of the leaf blocks. Returns the number of instructions added
  // to the beginning of leaf.
  static size_t copy_extra_loads_to_leaf_blocks(const SwitchEquivFinder& finder,
                                                cfg::ControlFlowGraph* cfg);
  // Undo the effect of CSE which would emit moves for const-class objects that
  // are used later. Replace such a move with a duplicated const-class/move
  // result pseudo to make the logic in SwitchEquivFinder less complicated.
  static size_t simplify_moves(IRCode* code);
  // SwitchEquivFinder needs to be able to understand all ways to reach a leaf
  // block to do its job safely. In some rare situations however, a leaf block
  // could exist, with no instructions that gotos another leaf. Such a block is
  // hereby called a sled and to support this gracefully, the sled block will be
  // turned into a duplicate of its successor (attaching its successor's
  // successors onto itself, etc). This is meant to ensure ExtraLoads state is
  // accurate.
  static size_t normalize_sled_blocks(
      cfg::ControlFlowGraph* cfg, const uint32_t leaf_duplication_threshold);
};
