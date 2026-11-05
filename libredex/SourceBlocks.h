/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <functional>
#include <limits>
#include <memory>
#include <optional>
#include <vector>

#include "ControlFlow.h"
#include "CppUtil.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "IRCode.h"
#include "IRList.h"
#include "SourceBlocksUtils.h"

class DexClass;
class DexMethod;
class DexStore;

// Must match DexStore.
using DexStoresVector = std::vector<DexStore>;

namespace call_graph {
class Graph;
} // namespace call_graph

namespace source_blocks {

using namespace cfg;

namespace impl {

struct BlockAccessor {
  static void push_source_block(Block* b,
                                std::unique_ptr<SourceBlock> src_block) {
    auto it = b->get_first_non_param_loading_insn();
    if (it != b->end() &&
        (opcode::is_a_move_result_pseudo(it->insn->opcode()) ||
         opcode::is_a_move_result(it->insn->opcode()))) {
      ++it;
    }
    auto* mie = new MethodItemEntry(std::move(src_block));
    if (it == b->end()) {
      b->m_entries.push_back(*mie);
    } else {
      b->m_entries.insert_before(it, *mie);
    }
  }

  static IRList::iterator insert_source_block_after(
      Block* b,
      const IRList::iterator& it,
      std::unique_ptr<SourceBlock> src_block) {
    auto* mie = new MethodItemEntry(std::move(src_block));
    return b->m_entries.insert_after(it, *mie);
  }
};

inline std::vector<Edge*> get_sorted_edges(Block* b) {
  auto succs = b->succs().to_vector();
  std::sort(succs.begin(), succs.end(), [](const Edge* lhs, const Edge* rhs) {
    if (lhs->type() != rhs->type()) {
      return lhs->type() < rhs->type();
    }
    switch (lhs->type()) {
    case EDGE_GOTO:
      redex_assert(lhs == rhs);
      return false;
    case EDGE_BRANCH: {
      auto lhs_case = lhs->case_key();
      auto rhs_case = rhs->case_key();
      if (!lhs_case) {
        redex_assert(!rhs_case);
        redex_assert(lhs == rhs);
        return false;
      }
      redex_assert(rhs_case);
      return *lhs_case < *rhs_case;
    }
    case EDGE_THROW: {
      auto* lhs_info = lhs->throw_info();
      auto* rhs_info = rhs->throw_info();
      redex_assert(lhs_info != nullptr);
      redex_assert(rhs_info != nullptr);
      auto* lhs_catch = lhs_info->catch_type;
      auto* rhs_catch = rhs_info->catch_type;
      if (lhs_catch == nullptr) {
        if (rhs_catch == nullptr) {
          redex_assert(lhs == rhs);
          return false;
        }
        return true;
      }
      if (rhs_catch == nullptr) {
        return false;
      }
      return compare_dextypes(lhs_catch, rhs_catch);
    }
    case EDGE_GHOST:
      return false;
    case EDGE_TYPE_SIZE:
      not_reached();
    }
    not_reached(); // For GCC.
  });
  return succs;
}

// This is the technical source-of-truth recursive implementation.
template <typename BlockStartFn, typename EdgeFn, typename BlockEndFn>
void visit_in_order_rec(const ControlFlowGraph* cfg,
                        const BlockStartFn& block_start_fn,
                        const EdgeFn& edge_fn,
                        const BlockEndFn& block_end_fn) {
  // Do not rely on `blocks()`, as there are no ordering guarantees. For now,
  // do a simple DFS with explicitly ordered edges.

  UnorderedSet<Block*> visited;
  self_recursive_fn(
      [&](auto self, Block* cur) {
        if (!visited.insert(cur).second) {
          return;
        }

        block_start_fn(cur);

        for (const auto* e : get_sorted_edges(cur)) {
          if (e->type() == EDGE_GHOST) {
            continue;
          }
          edge_fn(cur, e);
          self(self, e->target());
        }

        block_end_fn(cur);
      },
      cfg->entry_block());

  redex_assert(visited.size() == cfg->num_blocks());
}

// This is the iterative implementation for stack-size reasons. It is
// compared in a test against the recursive version.
template <typename BlockStartFn, typename EdgeFn, typename BlockEndFn>
void visit_in_order(const ControlFlowGraph* cfg,
                    const BlockStartFn& block_start_fn,
                    const EdgeFn& edge_fn,
                    const BlockEndFn& block_end_fn) {
  UnorderedSet<Block*> visited;

  struct StackFrame {
    Block* cur{nullptr}; // The handled block.
    Edge* edge{nullptr}; // Edge to use for edge_fn.
    bool initial{true}; // Is this the start of the recursive call?
    StackFrame(Block* cur, Edge* edge, bool initial)
        : cur(cur), edge(edge), initial(initial) {}
  };
  std::stack<StackFrame> stack;
  stack.emplace(cfg->entry_block(), nullptr, true);

  while (!stack.empty()) {
    auto* cur = stack.top().cur;

    if (stack.top().initial) {
      if (!visited.insert(cur).second) {
        stack.pop();
        continue;
      }

      block_start_fn(cur);

      stack.top().initial = false;

      auto sorted = get_sorted_edges(cur);
      for (auto it = sorted.rbegin(); it != sorted.rend(); ++it) {
        auto edge = *it;
        if (edge->type() == EDGE_GHOST) {
          continue;
        }
        stack.emplace(edge->target(), nullptr, true);
        stack.emplace(cur, edge, false);
      }
    } else {
      auto* edge = stack.top().edge;
      stack.pop();
      if (edge != nullptr) {
        edge_fn(cur, edge);
      } else {
        block_end_fn(cur);
      }
    }
  }

  assert_log(visited.size() == cfg->num_blocks(),
             "%zu vs %zu",
             visited.size(),
             cfg->num_blocks());
}

} // namespace impl

struct InsertResult {
  size_t block_count;
  std::string serialized;
  std::string serialized_idom_map;
  bool profile_success;
  size_t normalized_count;
  size_t denormalized_count;
  size_t elided_vals;
  size_t unelided_vals;
};

// Source data for a profile = interaction. Three options per interactions:
// * Nothing (std::nullopt)
// * A string that denotes a serialized profile, and an error value, in case
//   the profile does not match the CFG.
// * A general default value.
using ProfileData =
    std::variant<std::nullopt_t,
                 std::pair<std::string, std::optional<SourceBlock::Val>>,
                 SourceBlock::Val>;

InsertResult insert_source_blocks(const DexString* method,
                                  ControlFlowGraph* cfg,
                                  const std::vector<ProfileData>& profiles = {},
                                  bool serialize = true,
                                  bool insert_after_excs = false);

InsertResult insert_source_blocks(DexMethod* method,
                                  ControlFlowGraph* cfg,
                                  const std::vector<ProfileData>& profiles = {},
                                  bool serialize = true,
                                  bool insert_after_excs = false);

InsertResult insert_custom_source_blocks(
    const DexString* method,
    ControlFlowGraph* cfg,
    const std::vector<ProfileData>& profiles = {},
    bool serialize = true,
    bool insert_after_excs = false,
    bool enable_fuzzing = false,
    bool must_be_cold = false);

UnorderedMap<Block*, uint32_t> insert_custom_source_blocks_get_indegrees(
    const DexString* method,
    ControlFlowGraph* cfg,
    const std::vector<ProfileData>& profiles = {},
    bool serialize = true,
    bool insert_after_excs = false,
    bool enable_fuzzing = false);

struct SourceBlockMetric {
  size_t hot_block_count{0};
  size_t cold_block_count{0};
  size_t hot_throw_cold_count{0};
};

SourceBlockMetric gather_source_block_metrics(ControlFlowGraph* cfg);

bool has_source_block_positive_val(const SourceBlock* sb);

bool has_source_block_undefined_val(const SourceBlock* sb);

// Whether two source blocks carry the same profile data, ignoring src, id and
// next. SourceBlock::operator== leads with src and id, so it answers "are these
// the same block", which is not the same question and is always false for
// blocks of differing identity -- for example an original block and a synthetic
// clone of it, which always carries kSyntheticId.
inline bool vals_equal(const SourceBlock& lhs, const SourceBlock& rhs) {
  if (lhs.vals_size != rhs.vals_size) {
    return false;
  }
  for (size_t i = 0; i != lhs.vals_size; i++) {
    if (lhs.get_at(i) != rhs.get_at(i)) {
      return false;
    }
  }
  return true;
}

// Overwrite dst's profile data with from's, leaving dst's src, id and next
// alone. SourceBlock::operator= copies the identity as well and replaces the
// next chain, which loses the ids instrumentation resolves and, mid-traversal,
// frees the chain still being walked.
inline void set_vals(SourceBlock& dst, const SourceBlock& from) {
  always_assert(dst.vals_size == from.vals_size);
  for (size_t i = 0; i != dst.vals_size; i++) {
    dst.set_at(i, from.get_at(i));
  }
}

void scale_source_blocks(cfg::Block* block);

inline bool has_source_blocks(const cfg::Block* b) {
  for (const auto& mie : *b) {
    if (mie.type == MFLOW_SOURCE_BLOCK) {
      return true;
    }
  }
  return false;
}

inline std::vector<const SourceBlock*> gather_source_blocks(
    const cfg::Block* b) {
  std::vector<const SourceBlock*> ret;
  for (const auto& mie : *b) {
    if (mie.type != MFLOW_SOURCE_BLOCK) {
      continue;
    }
    for (auto* sb = mie.src_block.get(); sb != nullptr; sb = sb->next.get()) {
      ret.push_back(sb);
    }
  }
  return ret;
}

inline std::vector<SourceBlock*> gather_source_blocks(cfg::Block* b) {
  std::vector<SourceBlock*> ret;
  for (const auto& mie : *b) {
    if (mie.type != MFLOW_SOURCE_BLOCK) {
      continue;
    }
    for (auto* sb = mie.src_block.get(); sb != nullptr; sb = sb->next.get()) {
      ret.push_back(sb);
    }
  }
  return ret;
}

// Whether `a` and `b` carry the same number of source blocks, so that
// `add_source_blocks_pairwise` can pair them up.
bool have_same_source_block_counts(const cfg::Block* a, const cfg::Block* b);

/**
 * Adds each source block of `from` to the source block at the same position in
 * `into` (see `SourceBlock::add`), as when `into` takes over the executions of
 * an identical block. Returns false, changing nothing, when the two blocks
 * carry different numbers of source blocks.
 */
bool add_source_blocks_pairwise(cfg::Block* into, const cfg::Block* from);

template <typename Fn>
inline void foreach_source_block(cfg::Block* b, const Fn& fn) {
  for (const auto& mie : *b) {
    if (mie.type != MFLOW_SOURCE_BLOCK) {
      continue;
    }
    for (auto* sb = mie.src_block.get(); sb != nullptr; sb = sb->next.get()) {
      fn(sb);
    }
  }
}
template <typename Fn>
inline void foreach_source_block(const cfg::Block* b, const Fn& fn) {
  for (const auto& mie : *b) {
    if (mie.type != MFLOW_SOURCE_BLOCK) {
      continue;
    }
    for (auto* sb = mie.src_block.get(); sb != nullptr; sb = sb->next.get()) {
      fn(sb);
    }
  }
}

// Sets every primary SourceBlock entry's values across `cfg` to `val`.
// Deliberately does not traverse SourceBlock::next chains: this helper
// preserves the behavior of the hand-written clone-zeroing loops it replaces.
inline void fill_source_block_entry_values(cfg::ControlFlowGraph& cfg,
                                           const SourceBlock::Val& val) {
  for (auto* block : cfg.blocks()) {
    for (auto& mie : *block) {
      if (mie.type == MFLOW_SOURCE_BLOCK) {
        mie.src_block->fill(val);
      }
    }
  }
}

inline SourceBlock* get_first_source_block(cfg::Block* b) {
  for (const auto& mie : *b) {
    if (mie.type != MFLOW_SOURCE_BLOCK) {
      continue;
    }
    return mie.src_block.get();
  }
  return nullptr;
}
inline const SourceBlock* get_first_source_block(const cfg::Block* b) {
  for (const auto& mie : *b) {
    if (mie.type != MFLOW_SOURCE_BLOCK) {
      continue;
    }
    return mie.src_block.get();
  }
  return nullptr;
}

inline bool is_not_cold(cfg::Block* b) {
  auto* sb = get_first_source_block(b);
  if (sb == nullptr) {
    // Conservatively assume that missing SBs mean no profiling data.
    return true;
  }
  return sb->foreach_val_early([](const auto& v) { return v && v->val > 0; });
}

inline bool maybe_hot(cfg::Block* b, float threshold = 0.0f) {
  auto* sb = get_first_source_block(b);
  if (sb == nullptr) {
    // Conservatively assume that missing SBs mean no profiling data.
    return true;
  }
  return sb->foreach_val_early([&](const auto& v) {
    return !v || (v->val > 0 && v->appear100 >= threshold);
  });
}

inline bool is_hot(cfg::Block* b, float threshold = 0.0f) {
  auto* sb = get_first_source_block(b);
  if (sb == nullptr) {
    // Conservatively assume that missing SBs mean no profiling data.
    return false;
  }
  return sb->foreach_val_early([threshold](const auto& v) {
    return v && v->val > 0 && v->appear100 >= threshold;
  });
}

// If a method's entry block is hot, consider this method is hot.
inline bool method_is_hot(const DexMethod* method, float threshold = 0.0f) {
  const auto& cfg = method->get_code()->cfg();
  return is_hot(cfg.entry_block(), threshold);
}

// If a method's entry block may be hot, consider this method may be hot.
inline bool method_maybe_hot(const DexMethod* method, float threshold = 0.0f) {
  const auto& cfg = method->get_code()->cfg();
  return maybe_hot(cfg.entry_block(), threshold);
}

// If a method's entry block is not cold, consider this method is not cold.
inline bool method_is_not_cold(const DexMethod* method) {
  const auto& cfg = method->get_code()->cfg();
  return is_not_cold(cfg.entry_block());
}

// The execution count a consumer reads from a single source block: the max over
// interactions of its `val` (nullopt when `sb` is null or records no vals).
// Callers wanting a plain float use `.value_or(0.0f)`. Intended as the single
// definition of "a block's count" for the count-guided passes (outliner,
// inliner, ArtProfileWriter) to share, so they can't drift apart.
inline std::optional<float> max_val_over_interactions(const SourceBlock* sb) {
  if (sb == nullptr) {
    return std::nullopt;
  }
  std::optional<float> max_val;
  for (size_t i = 0; i < sb->vals_size; i++) {
    auto v = sb->get_val(i);
    if (v && (!max_val || *v > *max_val)) {
      max_val = v;
    }
  }
  return max_val;
}

// Two ways to pick a count cutoff from a set of block counts. They answer
// DIFFERENT questions, so they are separate, named helpers -- don't mix them
// up:
//
//   rank_cutoff_for_percentile(counts, p) = "the hottest (100 - p)% OF THE
//     ITEMS." A rank percentile p in [0, 100], high = hot (LLVM convention):
//     p = 95 keeps items at or above the 95th-percentile count -- the hottest
//     5% of callsites. Every item counts once, no matter how big; a rarely-run
//     callsite and a red-hot one each count as one. Test with `count >=
//     cutoff`. Used by the inliner and ArtProfileWriter.
//
//   mass_coverage_cutoff(vals, c) = "the blocks that do c OF THE WORK."
//     Items are weighted by their count, so a few very hot blocks can make up
//     the fraction c -- e.g. the blocks where 90% of execution actually
//     happens. Test with `val > cutoff` (boundary excluded: blocks exactly at
//     the cutoff are NOT kept, so realized coverage can dip below c if many
//     counts tie on it). Used by the outliner.
//
// In short: rank = "the hottest (100 - p)% of items"; mass = "the items that
// do X% of the work."
//
// `counts` is sorted in place. Returns +inf when empty or p >= 100 (nothing is
// "top") and -inf when p <= 0 (everything is).
inline float rank_cutoff_for_percentile(std::vector<float>& counts,
                                        int percentile) {
  const float fraction = static_cast<float>(100 - percentile) / 100.0f;
  if (counts.empty() || fraction <= 0.0f) {
    return std::numeric_limits<float>::infinity();
  }
  if (fraction >= 1.0f) {
    return -std::numeric_limits<float>::infinity();
  }
  std::sort(counts.begin(), counts.end());
  auto idx = static_cast<size_t>((1.0f - fraction) *
                                 static_cast<float>(counts.size()));
  if (idx >= counts.size()) {
    idx = counts.size() - 1;
  }
  return counts[idx];
}

// The execution-mass counterpart of rank_cutoff_for_percentile (see the
// comparison above it). `vals` is sorted in place. Returns 0 when empty or
// coverage >= 1 (protect every covered block) and max(vals) when coverage <= 0
// (protect nothing).
inline float mass_coverage_cutoff(std::vector<float>& vals, float coverage) {
  if (vals.empty() || coverage >= 1.0f) {
    return 0.0f;
  }
  // Sort hottest-first and walk down until the accumulated mass reaches the
  // covered fraction; the count where we cross is the gate.
  std::sort(vals.begin(), vals.end(), [](float a, float b) { return a > b; });
  if (coverage <= 0.0f) {
    return vals.front();
  }
  double total = 0.0;
  for (float v : vals) {
    total += v;
  }
  double target = coverage * total;
  double acc = 0.0;
  float gate = vals.back();
  for (float v : vals) {
    acc += v;
    if (acc >= target) {
      gate = v;
      break;
    }
  }
  return gate;
}

// Parallel gather of every block's execution count (its first source block's
// max-over-interactions `val`), kept only when > 0, across `scope` --
// optionally filtered by a per-(method, block) predicate (a null `include`
// keeps every covered block). The pooled vector is ready to feed
// `rank_cutoff_for_percentile` or `mass_coverage_cutoff`. Definition in
// SourceBlocks.cpp (needs Walkers).
std::vector<float> gather_block_counts(
    const std::vector<DexClass*>& scope,
    const std::function<bool(DexMethod*, cfg::Block*)>& include = {});

template <typename Iterator>
inline SourceBlock* find_between(const Iterator& start, const Iterator& end) {
  auto it = std::find_if(start, end,
                         [](auto& e) { return e.type == MFLOW_SOURCE_BLOCK; });
  return it != end ? it->src_block.get() : nullptr;
}

inline SourceBlock* get_last_source_block_before(cfg::Block* b,
                                                 const IRList::iterator& it) {
  auto* sb = find_between(IRList::reverse_iterator(it), b->rend());
  return sb != nullptr ? sb->get_last_in_chain() : nullptr;
}
inline const SourceBlock* get_last_source_block_before(
    const cfg::Block* b, const IRList::const_iterator& it) {
  auto* sb = find_between(IRList::const_reverse_iterator(it), b->rend());
  return sb != nullptr ? sb->get_last_in_chain() : nullptr;
}

inline SourceBlock* get_first_source_block_after(cfg::Block* b,
                                                 const IRList::iterator& it) {
  auto* sb = find_between(it, b->end());
  return sb != nullptr ? sb : nullptr;
}
inline const SourceBlock* get_first_source_block_after(
    const cfg::Block* b, const IRList::const_iterator& it) {
  auto* sb = find_between(it, b->end());
  return sb != nullptr ? sb : nullptr;
}

inline SourceBlock* get_first_source_block(cfg::ControlFlowGraph* cfg) {
  for (auto* b : cfg->blocks()) {
    auto* sb = get_first_source_block(b);
    if (sb != nullptr) {
      return sb;
    }
  }
  return nullptr;
}

inline SourceBlock* get_first_source_block(IRCode* code) {
  if (code->cfg_built()) {
    return get_first_source_block(&code->cfg());
  } else {
    for (const auto& mie : *code) {
      if (mie.type != MFLOW_SOURCE_BLOCK) {
        continue;
      }
      return mie.src_block.get();
    }
    return nullptr;
  }
}

inline void get_hot_cold_units(cfg::ControlFlowGraph& cfg,
                               uint32_t& hot,
                               uint32_t& cold) {
  hot = 0;
  cold = 0;
  for (auto* block : cfg.blocks()) {
    if (is_hot(block)) {
      hot += block->estimate_code_units();
    } else {
      cold += block->estimate_code_units();
    }
  }
}

template <typename BlockType, typename SourceBlockType>
inline SourceBlockType* get_last_source_block_impl(BlockType* b) {
  static_assert(
      std::is_same_v<std::remove_const_t<BlockType>, cfg::Block> &&
      std::is_same_v<std::remove_const_t<SourceBlockType>, SourceBlock>);

  auto rit = std::find_if(b->rbegin(), b->rend(), [](const auto& mie) {
    return mie.type == MFLOW_SOURCE_BLOCK;
  });

  if (rit == b->rend()) {
    return nullptr;
  }

  return rit->src_block.get();
}

inline SourceBlock* get_last_source_block(cfg::Block* b) {
  return get_last_source_block_impl<cfg::Block, SourceBlock>(b);
}
inline const SourceBlock* get_last_source_block(const cfg::Block* b) {
  return get_last_source_block_impl<const cfg::Block, const SourceBlock>(b);
}

// This helper gets the last source block in a block if it is after a throw,
// otherwise returns a nullptr
inline SourceBlock* get_last_source_block_if_after_throw(cfg::Block* b) {
  for (auto it = b->rbegin(); it != b->rend(); it++) {
    if (it->type == MFLOW_OPCODE && opcode::is_throw(it->insn->opcode())) {
      return nullptr;
    }
    if (it->type == MFLOW_SOURCE_BLOCK) {
      return it->src_block.get();
    }
  }
  return nullptr;
}

IRList::iterator find_first_block_insert_point(cfg::Block* b);

namespace normalize {

size_t num_interactions(const cfg::ControlFlowGraph& cfg,
                        const SourceBlock* sb);

inline float get_factor(SourceBlock* dominating,
                        SourceBlock* dominated,
                        size_t idx) {
  float caller_val;
  {
    if (dominating == nullptr) {
      return NAN;
    }
    auto val = dominating->get_val(idx);
    if (!val) {
      return NAN;
    }
    caller_val = *val;
  }
  if (caller_val == 0) {
    return 0.0f;
  }

  float callee_val;
  {
    if (dominated == nullptr) {
      return NAN;
    }
    auto val = dominated->get_val(idx);
    if (!val) {
      return NAN;
    }
    callee_val = *val;
  }
  if (callee_val == 0) {
    return 0.0f;
  }

  // Expectation would be that callee_val >= caller_val. But tracking might
  // not be complete.

  // This will normalize to the value at the dominating source block.
  return caller_val / callee_val;
}

inline void normalize(SourceBlock* sb, size_t idx, float factor) {
  sb->apply_at(idx, [&](auto& val) {
    if (val) {
      // Captured BEFORE the multiply: the product of two positives can flush
      // to exactly 0.0f (1e-30 * 1e-20 == 1e-50, unrepresentable), and a `> 0`
      // test on the RESULT cannot tell that underflow apart from a genuine
      // zero. Guarding on the result is what the old 1e-3 floor did, which is
      // why it never actually prevented an underflow.
      const bool was_positive = val->val > 0.0f;
      val->val *= factor;
      // A NaN `factor` (e.g. an unprofiled/none dominating block) turns `val`
      // into "none" here, flipping `operator bool()` to false; re-guard before
      // dereferencing again so the guard below never trips Val's operator->
      // assertion.
      //
      // Underflow guard only: a positive val scaled by a positive factor must
      // stay positive, or a hot block is silently reclassified as cold. A zero
      // factor still yields a hard zero (cold caller zeroes the inlined body),
      // and a NaN factor still yields "none" -- `factor > 0` excludes both.
      if (val && was_positive && factor > 0.0f &&
          val->val < kMinPositiveCount) {
        val->val = kMinPositiveCount;
      }
    }
  });
}

inline void normalize(SourceBlock* dominating,
                      SourceBlock* dominated,
                      size_t interactions) {
  for (size_t i = 0; i != interactions; ++i) {
    auto sb_factor = get_factor(dominating, dominated, i);
    normalize(dominated, i, sb_factor);
  }
}

inline void normalize(ControlFlowGraph& cfg,
                      SourceBlock* dominating,
                      SourceBlock* dominated,
                      size_t interactions) {
  if (interactions == 0) {
    return;
  }
  std::vector<float> factors;
  factors.reserve(interactions);
  for (size_t i = 0; i != interactions; ++i) {
    // Whole-CFG scaling (the inlining path): `dominating` is the callsite and
    // `dominated` the callee entry, so the factor is this callsite's SHARE of
    // the callee's executions and is at most 1. Two things push it above 1 --
    // incomplete tracking, which get_factor already anticipates, and a
    // denominator sitting on a positive-magnitude floor, which turns an
    // ordinary numerator into a large multiplier on EVERY block of the inlined
    // body. Clamp it; this also absorbs an overflow-to-inf quotient.
    //
    // Deliberately NOT inside get_factor: the two-SourceBlock overload uses
    // that same helper for `dominated := dominating` assignment semantics,
    // where a factor above 1 is meaningful and must not be clamped.
    //
    // NaN is passed through rather than collapsed by std::min's ordering, so
    // an unprofiled dominating block still yields "no data" instead of 1.
    const float f = get_factor(dominating, dominated, i);
    factors.push_back(std::isnan(f) ? f : std::min(f, 1.0f));
  }
  for (auto* b : cfg.blocks()) {
    source_blocks::foreach_source_block(b, [&](auto* sb) {
      for (size_t i = 0; i != interactions; ++i) {
        normalize(sb, i, factors[i]);
      }
    });
  }
}

inline void normalize(ControlFlowGraph& cfg,
                      SourceBlock* dominating,
                      size_t interactions) {
  // Assume that integrity is guaranteed, so that val at entry is
  // dominating all blocks.
  normalize(cfg, dominating, get_first_source_block(cfg.entry_block()),
            interactions);
}

} // namespace normalize

namespace apportion {

// Count-conserving apportionment, shared by every transform that duplicates a
// block or drops one of its predecessors.
//
// Needs only PREDECESSOR counts, never edge counts: Redex does not track edge
// hotness, and a predecessor's share of a block's inflow is the standard
// estimate when block counts are known and edge counts are not. It is an
// estimate -- a predecessor with branch successors does not send all its flow
// to one successor -- but it never invents mass.
//
// `appear100` is never scaled by any of these: it is an appearance
// probability, MAX-unioned across copies, so a verbatim carry is right for it.

// Per-interaction sum of the LAST SourceBlock val over every predecessor of
// `b` -- the last one, because that is a predecessor's outflow, which is what
// its successors receive.
//
// A predecessor with no SourceBlock contributes nothing, so it also does not
// widen the denominator: the shares below describe the inflow we have evidence
// for, not all of it. Where some predecessors are unprofiled the remaining
// shares are correspondingly larger, which errs towards moving too much count
// onto a copy rather than leaving mass stranded on a block that no longer
// receives it.
std::vector<double> predecessor_totals(const cfg::Block* b, size_t n_slots);

// Share of `b`'s inflow attributable to `src`, given `b`'s predecessor totals.
// Returns -1.0 for "no count evidence for this slot", which callers must treat
// as "leave alone": a predecessor whose SourceBlock reads 0 IS evidence (it
// correctly yields a cold share), whereas a predecessor with no SourceBlock is
// absence. Conflating the two turns copies of unprofiled predecessors cold.
double share_of(const std::vector<double>& pred_total,
                const cfg::Block* src,
                size_t i);

// sb->val[i] *= f. Leaves a `none` val and appear100 untouched.
void scale_val(SourceBlock* sb, size_t i, double f);

// Scale every SourceBlock of `b` -- chain included, since they annotate the
// same program point and so describe the same execution count -- by
// clamp(1 - leaving_share[i], 0, 1). The counterpart to handing
// `leaving_share` to the copies that took it.
void shrink_by_departed(cfg::Block* b,
                        const std::vector<double>& leaving_share);

} // namespace apportion

class SourceBlockConsistencyCheck;
SourceBlockConsistencyCheck& get_sbcc();

SourceBlock* get_first_source_block_of_method(const DexMethod* m);

SourceBlock* get_any_first_source_block_of_methods(
    const std::vector<const DexMethod*>& methods);

void insert_synthetic_source_blocks_in_method(
    DexMethod* method,
    const std::function<std::unique_ptr<SourceBlock>()>& source_block_creator);

void adjust_block_hits_with_appear100_threshold(
    ControlFlowGraph* cfg, int32_t block_appear100_threshold);

} // namespace source_blocks
