/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

/*
 * This service removes blocks that are duplicates in a method.
 *
 * If a method has multiple blocks with the same code and the same successors,
 * delete all but one of the blocks. Naming one of them the canonical block.
 *
 * Then, reroute all the predecessors of all the blocks to that canonical block.
 *
 * Merging these blocks will make some debug line numbers incorrect.
 * Here's an example
 *
 * Bar getBar() {
 *   if (condition1) {
 *     Bar bar = makeBar();
 *     if (condition2) {
 *       return bar;
 *     }
 *     cleanup();
 *   } else if (condition3) {
 *     cleanup();
 *   }
 *   return null;
 * }
 *
 * The blocks that call `cleanup()` will be merged.
 *
 * No matter which branch we took to call `cleanup()`, a stack trace will always
 * report the same line number (probably the first one in this example, because
 * it will have a lower block id).
 *
 * We could delete the line number information inside the canonical block, but
 * arguably, having stack traces that point to similar looking code (in a
 * different location) is better than having stack traces point to the nearest
 * line of source code before or after the merged block.
 *
 * Deleting the line info would also make things complicated if `cleanup()` is
 * inlined into `getBar()`. We would be unable to reconstruct the inlined stack
 * frame if we deleted the callsite's line number.
 *
 * So the line is kept, and the survivor records that it represents more than
 * one source site. Consumers can use that fidelity instead of treating the
 * retained line as uniquely identifying the branch. See `PositionJoin.h`.
 */

#include "DedupBlocks.h"
#include "Debug.h"
#include "DedupBlockValueNumbering.h"

#include <algorithm>
#include <map>
#include <optional>

#include "DexPosition.h"
#include "Lazy.h"
#include "LiveRange.h"
#include "MethodUtil.h"
#include "OutlinedMethods.h"
#include "PositionJoin.h"
#include "RedexContext.h"
#include "Resolver.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "Trace.h"
#include "TypeInference.h"

namespace {

constexpr bool kDebugForceInstrumentMode = false;

using hash_t = std::size_t;

bool is_instrument_mode() {
  return g_redex->instrument_mode || kDebugForceInstrumentMode;
}

static bool is_branch_or_goto(const cfg::Edge* edge) {
  auto type = edge->type();
  return type == cfg::EDGE_BRANCH || type == cfg::EDGE_GOTO;
}

static std::vector<cfg::Edge*> get_branch_or_goto_succs(
    const cfg::Block* block) {
  std::vector<cfg::Edge*> succs;
  for (auto* edge : block->succs()) {
    if (is_branch_or_goto(edge)) {
      succs.push_back(edge);
    }
  }
  return succs;
}

// Describe a successor target independently of which block we reached it from:
// a self-edge becomes a sentinel, anything else stays the target itself.
//
// Must be canonical, not a pairwise "…or both point at themselves" test.
// `collect_duplicates` uses successor equality as the key equality of a hash
// map, so it must be a true equivalence relation. The pairwise form is not
// transitive: with three identical-code blocks where A and B self-loop and C
// branches to A, A~B holds (both self-loop) and A~C holds (targets are both A),
// but B~C does not. Under a non-transitive equality, which group a block joins
// depends on the order the map compares it against representatives -- not part
// of the container's contract, and it shifts with the hash function.
//
// Two self-looping blocks still match. Mixed self-loop/branch-to-it pairs do
// not, so equivalence classes can only shrink: this never admits a merge that
// stricter matching would reject.
static const cfg::Block* canonical_succ_target(const cfg::Block* owner,
                                               const cfg::Block* target) {
  return target == owner ? nullptr : target;
}

// The blocks must also have the exact same branch and goto successors.
static bool same_branch_and_goto_successors(const cfg::Block* b1,
                                            const cfg::Block* b2) {
  auto b1_succs = get_branch_or_goto_succs(b1);
  auto b2_succs = get_branch_or_goto_succs(b2);
  if (b1_succs.size() != b2_succs.size()) {
    return false;
  }

  // For small succs numbers sort the vectors and compare that way.
  if (b1_succs.size() < 10) {
    auto cmp = [](const cfg::Edge* a, const cfg::Edge* b) {
      if (a->type() != b->type()) {
        return a->type() < b->type();
      }
      return a->case_key().value_or(0) < b->case_key().value_or(0);
    };
    std::sort(b1_succs.begin(), b1_succs.end(), cmp);
    std::sort(b2_succs.begin(), b2_succs.end(), cmp);
    for (size_t i = 0; i < b1_succs.size(); i++) {
      auto* b1_succ = b1_succs[i];
      auto* b2_succ = b2_succs[i];
      if (b1_succ->type() != b2_succ->type() ||
          b1_succ->case_key().value_or(0) != b2_succ->case_key().value_or(0)) {
        return false;
      }
      if (canonical_succ_target(b1, b1_succ->target()) !=
          canonical_succ_target(b2, b2_succ->target())) {
        return false;
      }
    }
    return true;
  }

  using Key = std::pair<cfg::EdgeType, cfg::Edge::CaseKey>;
  UnorderedMap<Key, const cfg::Block*, boost::hash<Key>> b2_succs_map;
  for (auto* b2_succ : b2_succs) {
    b2_succs_map.emplace(
        std::make_pair(b2_succ->type(), b2_succ->case_key().value_or(0)),
        canonical_succ_target(b2, b2_succ->target()));
  }
  for (auto* b1_succ : b1_succs) {
    // For successors being the same, we need to find a matching entry for
    // b1_succ in the b2_succs_map map.
    auto it = b2_succs_map.find(
        std::make_pair(b1_succ->type(), b1_succ->case_key().value_or(0)));
    if (it == b2_succs_map.end()) {
      return false;
    }
    if (canonical_succ_target(b1, b1_succ->target()) != it->second) {
      return false;
    }
  }
  return true;
}

struct SuccBlocksInSameGroup {
  bool operator()(const cfg::Block* a, const cfg::Block* b) const {
    return same_branch_and_goto_successors(a, b) && a->same_try(b) &&
           a->is_catch() == b->is_catch();
  }
};

struct BlockAndBlockValuePair {
  cfg::Block* block;
  const DedupBlkValueNumbering::BlockValue* block_value;
};

const cfg::Block& operator*(const BlockAndBlockValuePair& p) {
  return *p.block;
}

struct BlockAndBlockValuePairInSameGroup {
  bool operator()(const BlockAndBlockValuePair& p,
                  const BlockAndBlockValuePair& q) const {
    return SuccBlocksInSameGroup{}(p.block, q.block) &&
           *p.block_value == *q.block_value;
  }
};

struct BlockAndBlockValuePairHasher {
  hash_t operator()(const BlockAndBlockValuePair& p) const {
    return DedupBlkValueNumbering::BlockValueHasher()(*p.block_value);
  }
};

struct BlockCompare {
  bool operator()(const cfg::Block* a, const cfg::Block* b) const {
    // This assumes that cfg::Block::operator<() is based on block ids
    return *a < *b;
  }
};

struct BlockSuccHasher {
  hash_t operator()(cfg::Block* b) const {
    hash_t result = 0;
    for (const auto& succ : b->succs()) {
      if (is_branch_or_goto(succ) && b == succ->target()) {
        result ^= 27277 * (hash_t)succ->type();
      } else {
        result ^= succ->target()->id();
      }
    }
    return result;
  }
};

struct MIEHasher {
  hash_t operator()(MethodItemEntry* mie) const {
    if (mie->type == MFLOW_OPCODE) {
      return mie->insn->hash();
    }
    always_assert(mie->type == MFLOW_SOURCE_BLOCK);
    return mie->src_block->hash_ids();
  }
};
struct MIEEquals {
  bool operator()(MethodItemEntry* a, MethodItemEntry* b) const {
    return *a == *b;
  }
};

// Choose an iteration order based on block ids for determinism. This returns a
// vector of pointers to the entries of the Map.
//
// * If the map is const, the vector has const pointers to the entries.
// * If the map is not const, the vector has non-const pointers to the entries.
//   * If you edit them, do so with extreme care. Changing the keys or the
//     results of the key hash/equality functions could be disastrous.
template <class UnorderedMap,
          class Entry =
              mimic_const_t<UnorderedMap, typename UnorderedMap::value_type>>
std::vector<Entry*> get_id_order(UnorderedMap& umap) {
  std::vector<Entry*> order;
  order.reserve(umap.size());
  for (Entry& entry : UnorderedIterable(umap)) {
    order.push_back(&entry);
  }
  std::sort(order.begin(), order.end(),
            [](Entry* e1, Entry* e2) { return *(e1->first) < *(e2->first); });
  return order;
}

// Will the split block have a position before the first
// instruction, or do we need to insert one?
bool needs_pos(const IRList::iterator& begin, const IRList::iterator& end) {
  for (auto it = begin; it != end; it++) {
    switch (it->type) {
    case MFLOW_OPCODE: {
      auto op = it->insn->opcode();
      if (opcode::may_throw(op) || opcode::is_throw(op)) {
        return true;
      }
      continue;
    }
    case MFLOW_POSITION:
      return false;
    default:
      continue;
    }
  }
  return true;
}

} // namespace

namespace dedup_blocks_impl {

// Returns the deobfuscated class descriptor for a method ref, surviving
// RenameClassesPass (which mutates DexType names in place). Falls back to the
// current type name when no deobfuscated name is available (e.g. before rename
// passes run, or for types that were not renamed).
static std::string_view get_deobfuscated_class_name(const DexMethodRef* m) {
  auto* cls_def = type_class(m->get_class());
  if (cls_def != nullptr) {
    auto deob = cls_def->get_deobfuscated_name_or_empty();
    if (!deob.empty()) {
      return deob;
    }
  }
  return m->get_class()->str();
}

// Returns true if this invoke-static targets a helper method whose body
// is "throw new SomeThrowable(...)". Collapsing multiple callsites of such
// helpers mis-attributes runtime exceptions — the callsite PC is what
// symbolicates in the stack trace.
//
// Uses deobfuscated names so the check survives RenameClassesPass (which
// makes DexType::get_type("Lkotlin/...") return nullptr) and ObfuscatePass
// (which renames method names, e.g. "throwFoo" → "A0O").
//
// Known producers:
//   - kotlin.jvm.internal.Intrinsics.throw* — Kotlin compiler (!!,
//     lateinit, contract, parameter null-checks).
//   - com.redex.UnreachableException.createAndThrow — Redex synthetic.
static bool check_throw_helper_names(std::string_view cls_name,
                                     std::string_view method_name) {
  if (cls_name == "Lkotlin/jvm/internal/Intrinsics;" &&
      method_name.starts_with("throw")) {
    return true;
  }
  if (cls_name == "Lcom/redex/UnreachableException;" &&
      method_name == "createAndThrow") {
    return true;
  }
  return false;
}

static bool is_throw_delegating_helper(const DexMethodRef* m) {
  // Try the def's fully-deobfuscated name first (works after both
  // RenameClassesPass + ObfuscatePass; set on method defs including
  // external methods loaded from JARs like kotlin-stdlib).
  const DexMethod* def = m->is_def() ? m->as_def() : nullptr;
  if (def == nullptr) {
    def = resolve_method_deprecated(const_cast<DexMethodRef*>(m),
                                    MethodSearch::Static);
  }
  if (def != nullptr) {
    auto deob = def->get_deobfuscated_name_or_empty();
    if (!deob.empty()) {
      if (deob.find("Lkotlin/jvm/internal/Intrinsics;.throw") !=
          std::string_view::npos) {
        return true;
      }
      if (deob.find("Lcom/redex/UnreachableException;.createAndThrow:") !=
          std::string_view::npos) {
        return true;
      }
      return false;
    }
    // Def exists but has no deobfuscated name (pre-rename). Use the def's
    // simple deobfuscated name for the method part.
    auto simple = def->get_simple_deobfuscated_name();
    if (!simple.empty()) {
      return check_throw_helper_names(get_deobfuscated_class_name(m), simple);
    }
  }
  // Final fallback: deobfuscated class name + current method name.
  // Only correct before ObfuscatePass renames method names.
  auto cls_name = get_deobfuscated_class_name(m);
  const auto* name = m->get_name();
  if (name == nullptr) {
    return false;
  }
  return check_throw_helper_names(cls_name, name->str());
}

bool is_ineligible_because_of_fill_in_stack_trace(const IRInstruction* insn) {
  auto op = insn->opcode();
  DexMethod* resolved_method{nullptr};
  // Direct call to a constructor whose class derives from Throwable?
  // (It would indirectly call java.lang.Throwable.fillInStackTrace.)
  // These pointer comparisons are rename-safe: type::java_lang_Throwable()
  // returns the stable DexType* whose identity persists through rename.
  if (opcode::is_invoke_direct(op) && method::is_init(insn->get_method()) &&
      type::is_subclass(type::java_lang_Throwable(),
                        insn->get_method()->get_class())) {
    return true;
  }
  // Explicit virtual call to Throwable.fillInStackTrace?
  // (Pointer comparison — rename-safe.)
  if (opcode::is_invoke_virtual(op)) {
    resolved_method =
        resolve_method_deprecated(insn->get_method(), MethodSearch::Virtual);
    if (resolved_method == method::java_lang_Throwable_fillInStackTrace()) {
      return true;
    }
  }
  // An outlined method might invoke one of the above, so we are being
  // conservative here. Also catch static throw-delegating helpers
  // (Kotlin Intrinsics.throw*, Redex UnreachableException.createAndThrow)
  // whose body throws but whose callsite PC is what symbolicates.
  if (opcode::is_invoke_static(op) &&
      (outliner::is_outlined_method(insn->get_method()) ||
       is_throw_delegating_helper(insn->get_method()))) {
    return true;
  }
  // We should not collapse the callsites of methods marked as dont-inline to
  // preserve their stack traces more accurately.
  if (opcode::is_an_invoke(op)) {
    if (resolved_method == nullptr) {
      if (opcode::is_invoke_super(op)) {
        // We don't have the caller method available, and thus cannot resolve an
        // invoke-super. We are conservative.
        return true;
      }
      resolved_method =
          resolve_method_deprecated(insn->get_method(), opcode_to_search(insn));
    }
    if ((resolved_method != nullptr) && resolved_method->rstate.dont_inline()) {
      return true;
    }
  }
  return false;
}

namespace {

class DedupBlocksImpl {
 public:
  DedupBlocksImpl(const Config* config, Stats& stats)
      : m_config(config), m_stats(stats) {
    always_assert(m_config);
  }

  // Dedup blocks that are exactly the same
  bool dedup(bool is_static,
             DexType* declaring_type,
             DexTypeList* args,
             cfg::ControlFlowGraph& cfg) {
    cfg.calculate_exit_block();
    LivenessFixpointIterator liveness_fixpoint_iter(cfg);
    liveness_fixpoint_iter.run({});
    DedupBlkValueNumbering::BlockValues block_values(liveness_fixpoint_iter);
    Duplicates dups = collect_duplicates(is_static, declaring_type, args, cfg,
                                         block_values, liveness_fixpoint_iter);
    if (!dups.empty()) {
      if (m_config->debug) {
        check_inits(cfg);
      }
      record_stats(dups);
      bool res = deduplicate(dups, cfg);
      if (m_config->debug) {
        check_inits(cfg);
      }
      return res;
    }

    return false;
  }

  /*
   * Split blocks that share postfix of instructions (that ends with the same
   * set of instructions).
   *
   * TODO: Some split blocks might not actually get dedup, as deduping checks
   * additional type constraints that splitting ignores. Either perfectly line
   * line up the splitting logic with the deduping logic (and install asserts
   * that they agree), or re-merge left-over block pairs, either explicitly,
   * or by running another RemoveGotos pass.
   *
   * TODO(T132664146): DedupBlocks's splitting algorithm unfortunately only
   * splits out one subtree level per iteration, which could probably be
   * improved with a better algorithm.
   */
  void split_postfix(cfg::ControlFlowGraph& cfg) {
    PostfixSplitGroupMap dups = collect_postfix_duplicates(cfg);
    if (!dups.empty()) {
      if (m_config->debug) {
        check_inits(cfg);
      }
      split_postfix_blocks(dups, cfg);
      if (m_config->debug) {
        check_inits(cfg);
      }
    }
  }

 private:
  // Be careful using `.at()` (or similar) on this map. We use a very broad
  // equality function that can lead to unexpected results. The key equality
  // function of this map is actually a check that they are duplicates, not that
  // they're the same block.
  //
  // Because `BlocksInSameGroup` depends on the CFG, modifications to the CFG
  // invalidate this map.
  using BlockSet = std::set<cfg::Block*, BlockCompare>;
  using Duplicates = UnorderedMap<BlockAndBlockValuePair,
                                  BlockSet,
                                  BlockAndBlockValuePairHasher,
                                  BlockAndBlockValuePairInSameGroup>;
  struct PostfixSplitGroup {
    BlockSet postfix_blocks;
    std::map<cfg::Block*, IRList::reverse_iterator, BlockCompare>
        postfix_block_its;
    size_t insn_count;
  };

  // Be careful using `.at()` on this map for the same reason as on `Duplicates`
  using PostfixSplitGroupMap = UnorderedMap<cfg::Block*,
                                            PostfixSplitGroup,
                                            BlockSuccHasher,
                                            SuccBlocksInSameGroup>;
  const Config* m_config;
  Stats& m_stats;

  // Find blocks with the same exact code
  Duplicates collect_duplicates(
      bool is_static,
      DexType* declaring_type,
      DexTypeList* args,
      cfg::ControlFlowGraph& cfg,
      DedupBlkValueNumbering::BlockValues& block_values,
      LivenessFixpointIterator& liveness_fixpoint_iter) {
    const auto& blocks = cfg.blocks();
    Duplicates duplicates;

    Lazy<live_range::LazyLiveRanges> live_ranges(
        [&]() { return std::make_unique<live_range::LazyLiveRanges>(cfg); });

    for (cfg::Block* block : blocks) {
      if (is_eligible(block, cfg)) {
        // Find a group that matches this one. The key equality function of this
        // map is actually a check that they are duplicates, not that they're
        // the same block.
        //
        // For example, if Block A and Block A' are duplicates, we will
        // populate this map as such:
        //   * after the first iteration (inserted A)
        //       A -> [A]
        //   * after the second iteration (inserted A')
        //       A -> [A, A']
        auto& dups = duplicates[{block, block_values.get_block_value(block)}];
        dups.insert(block);
        ++m_stats.eligible_blocks;
      }
    }

    Lazy<type_inference::TypeInference> type_inference([&]() {
      auto res = std::make_unique<type_inference::TypeInference>(cfg);
      res->run(is_static, declaring_type, args);
      return res;
    });
    remove_if(duplicates, [&](auto& blocks) {
      return is_singleton_or_inconsistent(
          blocks, live_ranges, liveness_fixpoint_iter, type_inference);
    });
    return duplicates;
  }

  // `src_block` is a reference because the caller has already filtered out
  // canon blocks without one; passing it as a raw pointer forced the
  // nullability analysis to re-prove that across the call boundary, which it
  // cannot do.
  static size_t remove_instructions(SourceBlock& src_block,
                                    cfg::Block* block,
                                    const cfg::ControlFlowGraph& cfg) {
    always_assert(block != nullptr);
    size_t cnt{0};

    auto it = block->begin();
    while (it != block->end()) {
      auto cur_it = it;
      ++it;

      switch (cur_it->type) {
      // Remove.
      case MFLOW_OPCODE: {
        block->remove_mie(cur_it);
        ++cnt;
      } break;

      case MFLOW_SOURCE_BLOCK: {
        // This block is a duplicate being folded into the survivor `src_block`;
        // both ran independently, so their counts accumulate (appear100 maxes).
        src_block.add(*cur_it->src_block);
        block->remove_mie(cur_it);
        ++cnt;
      } break;

      // Remarks are block-anchored metadata with no merge op; drop the
      // duplicate block's remarks (never blocks a legitimate merge).
      case MFLOW_REMARK: {
        block->remove_mie(cur_it);
        ++cnt;
      } break;
      // Keep.
      case MFLOW_POSITION:
      case MFLOW_DEBUG:
        break;

      // Shouldn't be here.
      case MFLOW_TARGET:
      case MFLOW_CATCH:
      case MFLOW_TRY:
      case MFLOW_DEX_OPCODE:
      case MFLOW_FALLTHROUGH:
        always_assert_log(false, "Found unsupported mie %s\n%s", SHOW(*cur_it),
                          SHOW(cfg));
      }
    }

    return cnt;
  }

  // The positions governing the instructions that can throw, in order. Those
  // are the only positions a stack trace can land on, so a merge anywhere else
  // cannot misattribute a crash and recording it would be noise.
  //
  // Collected per instruction, never per MethodItemEntry: block equality
  // ignores positions -- MIEHasher hashes only MFLOW_OPCODE and
  // MFLOW_SOURCE_BLOCK -- so two blocks in a group legally carry different
  // numbers of position entries in different places.
  //
  // A null position means no position precedes the instruction within the
  // block, or that position has no source file. On the survivor's side the
  // caller counts a gap; on the folded side it compares against nothing.
  // Neither reaches back outside the block for a position.
  struct ThrowingPosition {
    DexPosition* position;
    IROpcode opcode;
  };

  static std::vector<ThrowingPosition> throwing_positions(cfg::Block* block) {
    std::vector<ThrowingPosition> result;
    DexPosition* pos{nullptr};
    for (auto& mie : *block) {
      if (mie.type == MFLOW_POSITION) {
        pos = mie.pos.get();
      } else if (mie.type == MFLOW_OPCODE &&
                 opcode::can_throw(mie.insn->opcode())) {
        result.push_back(
            {pos != nullptr && pos->file != nullptr ? pos : nullptr,
             mie.insn->opcode()});
      }
    }
    return result;
  }

  // The surviving positions one round of folding found disagreeing with code
  // folded into them, in the order first found. They are marked together once
  // every fold of the round has been compared: a surviving position can be the
  // inlined caller of another, and `same_source_claim` treats an unreliable
  // caller as disagreeing, so marking fold by fold would let one fold's mark
  // flip another fold's comparison of exact lines.
  class PendingMarks {
   public:
    void add(DexPosition* survivor) {
      if (m_seen.insert(survivor).second) {
        m_order.push_back(survivor);
      }
    }

    const std::vector<DexPosition*>& survivors() const { return m_order; }

   private:
    std::vector<DexPosition*> m_order;
    UnorderedSet<DexPosition*> m_seen;
  };

  // Folds `victim` into `survivor`, counting the merge that could not be
  // recorded when there is no surviving position to record on.
  // `throwing_positions` yields a null entry when there is no usable survivor,
  // and this is where that absence is discovered, so this is where it is
  // counted -- `mark_merged` requires a survivor precisely so the gap cannot
  // be silently dropped.
  void join_or_count_gap(DexPosition* survivor,
                         const DexPosition* victim,
                         PendingMarks* pending) {
    if (survivor == nullptr) {
      m_stats.join_stats.count_unrecorded();
      return;
    }
    if (!positions::same_source_claim(survivor, victim)) {
      pending->add(survivor);
    }
  }

  void mark_pending(const PendingMarks& pending) {
    for (auto* survivor : pending.survivors()) {
      m_stats.join_stats.account(positions::mark_merged(survivor));
    }
  }

  // Records, on canon's positions, that `dup`'s code is being folded into it.
  // Call this where the merge is actually committed, not once per candidate
  // group: a group that is examined and then left alone must not come out of it
  // marked.
  void record_merged_positions(cfg::Block* canon,
                               cfg::Block* dup,
                               PendingMarks* pending) {
    auto canon_positions = throwing_positions(canon);
    auto dup_positions = throwing_positions(dup);

    bool has_correspondence = canon_positions.size() == dup_positions.size();
    if (has_correspondence) {
      auto canon_it = canon_positions.begin();
      auto dup_it = dup_positions.begin();
      for (; canon_it != canon_positions.end() && dup_it != dup_positions.end();
           ++canon_it, ++dup_it) {
        if (canon_it->opcode != dup_it->opcode) {
          has_correspondence = false;
          break;
        }
      }
    }
    if (has_correspondence) {
      auto canon_it = canon_positions.begin();
      auto dup_it = dup_positions.begin();
      for (; canon_it != canon_positions.end() && dup_it != dup_positions.end();
           ++canon_it, ++dup_it) {
        join_or_count_gap(canon_it->position, dup_it->position, pending);
      }
      return;
    }

    // Blocks are grouped by value numbering, not by instruction equality
    // (`BlockAndBlockValuePairInSameGroup` compares `BlockValue`s), so two
    // blocks that fold together can compute the same values with different
    // throwing instruction counts or opcodes. There is then no correspondence
    // to pair up, and guessing one would mark arbitrary positions. Joining each
    // survivor against "no position" says only what is actually known -- the
    // marking covers a site that cannot be lined up -- and over-marks rather
    // than inventing a specific pairing.
    ++m_stats.positions_merged_without_correspondence;
    for (const auto& throwing_position : canon_positions) {
      join_or_count_gap(throwing_position.position, nullptr, pending);
    }
  }

  // remove all but one of a duplicate set. Reroute the predecessors to the
  // canonical block
  bool deduplicate(const Duplicates& dups, cfg::ControlFlowGraph& cfg) {
    // Copy the BlockSets into a vector so that we're not reading the map while
    // editing the CFG.
    std::vector<BlockSet> order;
    for (const Duplicates::value_type* entry : get_id_order(dups)) {
      order.push_back(entry->second);
    }

    size_t cnt{0}; // Removed blocks.
    PendingMarks pending;

    if (is_instrument_mode()) {
      for (const BlockSet& group : order) {
        // canon is block with lowest id.
        cfg::Block* canon = *group.begin();
        SourceBlock* src_block = source_blocks::get_first_source_block(canon);
        if (src_block == nullptr) {
          continue;
        }

        for (cfg::Block* block : group) {
          if (block == canon) {
            continue;
          }

          always_assert(canon->id() < block->id());

          // If there is an incoming exception edge, forwarding does *not*
          // work. This should have been filtered before.
          auto exc_check_fn = [&]() {
            if (cfg.get_pred_edge_of_type(block, cfg::EdgeType::EDGE_THROW) ==
                nullptr) {
              return true;
            }
            auto it = block->get_first_insn();
            if (it == block->end()) {
              return true;
            }
            return !opcode::is_move_exception(it->insn->opcode());
          };
          redex_assert(exc_check_fn());

          // Don't remove directly. Just remove everything but dex positions.
          // Then remove all outgoing edges and make a goto
          // to the replacement.
          //
          // This will not deal correctly with exceptions.
          // Ahead of `remove_instructions`, which strips this block's opcodes.
          // The pairing is derived from the throwing instructions on both
          // sides, so a stripped block reports none: every merge whose survivor
          // throws would take the no-correspondence path and mark that survivor
          // against nothing at all, rather than against the position it
          // actually folded.
          record_merged_positions(canon, block, &pending);

          cfg.delete_edges(block->succs().begin(), block->succs().end());

          // Undercounts branch instructions.
          m_stats.insns_removed +=
              static_cast<int>(remove_instructions(*src_block, block, cfg));

          cfg.add_edge(block, canon, cfg::EDGE_GOTO);

          ++cnt;
        }
      }
      mark_pending(pending);
      cfg.simplify();
    } else {
      // Replace duplicated blocks with the "canon" (block with lowest ID).
      std::vector<std::pair<cfg::Block*, cfg::Block*>> blocks_to_replace;
      for (const BlockSet& group : order) {
        // canon is block with lowest id.
        cfg::Block* canon = *group.begin();
        std::vector<SourceBlock*> canon_source_blocks =
            source_blocks::gather_source_blocks(canon);
        auto num_canon_sb = canon_source_blocks.size();

        for (cfg::Block* block : group) {
          // canon's own counts are already the starting values in
          // `canon_source_blocks`; skip it so we don't add it to itself (the
          // old `max` was idempotent on canon, but `add` is not). This mirrors
          // the instrument path, which also skips canon.
          if (block == canon) {
            continue;
          }
          always_assert(canon->id() < block->id());

          record_merged_positions(canon, block, &pending);
          blocks_to_replace.emplace_back(block, canon);
          ++cnt;

          // Each duplicate block ran independently; folding it into canon means
          // canon is now reached by the union of predecessors, so the counts
          // accumulate (SUM). `add` also maxes `appear100` (a probability,
          // never summed).
          std::vector<SourceBlock*> source_blocks =
              source_blocks::gather_source_blocks(block);
          auto num_sb = source_blocks.size();
          if (num_sb == num_canon_sb) {
            for (size_t source_blk_idx = 0; source_blk_idx < num_sb;
                 source_blk_idx++) {
              canon_source_blocks[source_blk_idx]->add(
                  *source_blocks[source_blk_idx]);
            }
          } else if (num_sb >= 1 && num_canon_sb >= 1) {
            // Rare defensive fallback for a structural mismatch: identical
            // blocks normally carry the same NUMBER of source blocks (identical
            // instruction sequences get identical SB structure), so the paired
            // branch above is the norm. Here the two counts differ, so we can't
            // pair 1:1 -- add the duplicate's first SB to canon's first, then
            // broadcast its last SB across canon's remaining tail (approximate,
            // inherited from the prior `max` code).
            source_blocks::get_first_source_block(canon)->add(
                *source_blocks::get_first_source_block(block));
            auto last_source_block =
                *source_blocks::get_last_source_block(block);
            for (size_t source_blk_idx = 1; source_blk_idx < num_canon_sb;
                 source_blk_idx++) {
              canon_source_blocks[source_blk_idx]->add(last_source_block);
            }
          }
        }
      }

      mark_pending(pending);

      // Note that replace_blocks also fixes any arising dangling parents.
      m_stats.insns_removed +=
          static_cast<int>(cfg.replace_blocks(blocks_to_replace));
    }

    m_stats.blocks_removed += static_cast<int>(cnt);

    return cnt > 0;
  }

  void next_opcode_or_srcblk(IRList::reverse_iterator& block_it,
                             cfg::Block* block) {
    if (is_instrument_mode()) {
      while (block_it != block->rend() && block_it->type != MFLOW_OPCODE &&
             block_it->type != MFLOW_SOURCE_BLOCK) {
        ++block_it;
      }
    } else {
      while (block_it != block->rend() && block_it->type != MFLOW_OPCODE) {
        ++block_it;
      }
    }
  }

  // The algorithm below identifies the best groups of blocks that share the
  // same postfix of instructions (ends with the same set of instructions),
  // as well as the best place to split the blocks so as to create new blocks
  // that are identical and can be dedup with the subsequent dedup process.
  //
  // The highlevel flow of the algorithm works as follows:
  // 1. Partition blocks into groups that share the same successors. Note the
  // current implementation assumes one successor but we can easily improve
  // the partition algorithm to partition for same *set* of sucessor.
  // 2. For each block group that share the same successors, start the
  // instruction comparing process by keeping a reverse iterator for each block
  // within the group.
  // 3. In each iteration, partition the groups further by comparing the exact
  // instruction at the current reverse iterator - that is, the ones with the
  // same instruction at the current location share the same group, and we keep
  // a count of how many blocks are within the same group.
  // 4. Now that we have the groups, pick the biggest group. This means you are
  // effectively being greedy and choose the one that achieves the most sharing
  // in current level. The rest of the groups are discarded. In the future,
  // we can consider keeping all groups and simply eliminate the groups that
  // no longer share any instructions from further iteration, but don't throw
  // away those eliminated groups - we can still split them later (as opposed to
  // only the potentially best group).
  // 5. However, note that being greedy isn't necessarily the best choice, we
  // calculate the potential savings by calculating the "rectangle" of current
  // instruction "depth" * (number of blocks - 1), and keep track the best we
  // have seen so far, including the blocks and the reverse iterators.
  // 6. Keep iterating the groups that are being tracked until there are no more
  // sharing can be achieved.
  // 7. Split the blocks as indicated by the reverse iterator based on the best
  // saving we've seen so far.
  //
  // Example:
  //
  // Assuming you start with 5 groups (instructions are simplified for brievity
  // purposes)
  // A: (add, const v0, const v1, add, add, add)
  // B: (mul, const v0, const v1, add, add, add)
  // C: (div, const v0, const v1, add, add, add)
  // D: (const v2, add, add)
  // E: (const v3, add, add)
  //
  // All of them have the same successor.
  // 1. Start with (A, B, C, D, E) in the same group as they share the same
  // successor.
  // 2. Reverse iterator of A, B, C, D, E are at (5, 5, 5, 2, 2) (index starting
  // from 0).
  // 3. Iteration #1: Looking at the add instruction, given that all the
  // iterators pointing to identical add instruction, the group is still
  // (A, B, C, D, E), and the iterators are (4, 4, 4, 1, 1). The current saving
  // is 1 * (5-1) = 4.
  // 4. Iteration #2: Still the same add instruction. The group is still
  // (A, B, C, D, E), and the iterators are (3, 3, 3, 0, 0). The current saving
  // is 2 * (5-1) = 8.
  // 5. Iteration #3: group (A, B, C) share the same (add) instruction,
  // while (D), (E) are their own groups. (A, B, C) gets selected and rest is
  // discarded. The current saving is 3 * (3-1) = 6.
  // 6. Iteration #4: group (A, B, C) share the same (const v1) instruction.
  // The current saving is 4 * (3-1) = 8.
  // 7. Iteration #5: group (A, B, C) share the same (const v0) instruction.
  // The current saving is 5 * (3-1) = 10.
  // 8. Iteration #6. group (A), (B), (C) are their own groups since they all
  // have unique instruction. Given the biggest group is size 1, we terminate
  // the algorithm. The best saving is 10 with group (A, B, C) and split at
  // (1, 1, 1).
  // @TODO - Instead of keeping track of just one group, in the future we can
  // consider maintaining multiple groups and split them.
  PostfixSplitGroupMap collect_postfix_duplicates(cfg::ControlFlowGraph& cfg) {
    const auto& blocks = cfg.blocks();
    PostfixSplitGroupMap splitGroupMap;

    // Group by successors if blocks share a single successor block.
    for (cfg::Block* block : blocks) {
      if (block->num_opcodes() >= m_config->block_split_min_opcode_count) {
        // Insert into other blocks that share the same successors
        splitGroupMap[block].postfix_blocks.insert(block);
      }
    }

    TRACE(DEDUP_BLOCKS, 4,
          "split_postfix: partitioned %zu blocks into %zu groups",
          blocks.size(), splitGroupMap.size());

    struct CountGroup {
      size_t count = 0;
      BlockSet blocks;
    };

    // For each ([succs], [blocks]) pair
    for (PostfixSplitGroupMap::value_type* entry :
         get_id_order(splitGroupMap)) {
      const cfg::Block* b = entry->first;
      auto& split_group = entry->second;
      auto& succ_blocks = split_group.postfix_blocks;
      if (succ_blocks.size() <= 1) {
        continue;
      }

      TRACE(DEDUP_BLOCKS, 4,
            "split_postfix: current group (succs=%zu, blocks=%zu)",
            b->succs().size(), succ_blocks.size());

      // Keep track of best we've seen so far.
      BlockSet best_blocks;
      std::map<cfg::Block*, IRList::reverse_iterator, BlockCompare>
          best_block_its;
      size_t best_insn_count = 0;
      size_t best_saved_insn = 0;

      // Get (reverse) iterators for all blocks.
      std::map<cfg::Block*, IRList::reverse_iterator, BlockCompare>
          block_iterator_map;
      for (auto* block : succ_blocks) {
        block_iterator_map[block] = block->rbegin();
      }

      // Find the best common blocks
      size_t cur_insn_index = 0;
      while (true) {
        TRACE(DEDUP_BLOCKS, 4, "split_postfix: scanning instruction at %zu",
              cur_insn_index);

        // For each "iteration" - we count the distinct instructions and select
        // the instruction with highest count - the majority.
        // We do remember the instructions saved and select the best
        // combination at the end.
        size_t majority = 0;
        MethodItemEntry* majority_mie = nullptr;

        // For each (Block, iterator) - advance the iterator and partition
        // the current set of blocks into two groups:
        // 1) the group with the most shared instructions (majority).
        // 2) the rest.
        // The following insn_count map maintains the (insn -> count) mapping
        // so that we can group the blocks based on the current instruction.
        // For example, if you have A, B, C, D, E blocks, and (A, B, C) share
        // the same instruction I1, while (D, E) share the same instruction I2,
        // you would end up with (I1 : (A, B, C), 3, and I2 : (D, E), 2).
        // With the above map, you can select I1 group (A, B, C) as the current
        // group to track (current implementation).
        // @TODO - Instead of only keeping one group and calculate best savings
        // based on just one group, maintain multiple groups at the same time
        // and split/dedup those groups.
        UnorderedMap<MethodItemEntry*, CountGroup, MIEHasher, MIEEquals>
            mie_count;

        for (auto& block_iterator_pair : block_iterator_map) {
          auto* const block = block_iterator_pair.first;
          auto& it = block_iterator_pair.second;

          // When instrumenting, do not deduplicate catch handler head blocks.
          // If the handlers are similar, splitting should make this a minimal
          // block of `move-exception` + `goto`.
          if (!dedup_catch_handler_head_block(cfg, block)) {
            continue;
          }

          next_opcode_or_srcblk(it, block);

          if (it == block->rend()) {
            continue;
          }

          MethodItemEntry* mie = [&]() {
            switch (it->type) {
            case MFLOW_OPCODE: {
              return &*it;
            }
            case MFLOW_SOURCE_BLOCK: {
              redex_assert(is_instrument_mode());
              return &*it;
            }
            default:
              not_reached_log(
                  "the iterator type should always be either an "
                  "opcode or source block");
            }
          }();
          // Count the MIEs and locate the majority
          auto& count_group = mie_count[mie];
          count_group.count++;
          count_group.blocks.insert(block);
          if (count_group.count > majority) {
            majority = count_group.count;
            majority_mie = mie;
          }
          // Move to next instruction or source block.
          // IMPORTANT: in non-instrumentation mode, we should always land on
          // instructions otherwise you can get subtle errors when converting
          // between different instruction iterators.
          ++it;
          next_opcode_or_srcblk(it, block);
        }

        // No group to count or no one group has more than 1 item in common.
        // In either case we are done.
        if (majority_mie == nullptr || majority <= 1) {
          break;
        }

        cur_insn_index++;
        auto& majority_count_group = mie_count[majority_mie];

        // Remove the iterators
        std::erase_if(block_iterator_map, [&](auto& p) {
          return majority_count_group.blocks.find(p.first) ==
                 majority_count_group.blocks.end();
        });

        // Is this the best saving we've seen so far?
        // Note we only want at least block_split_min_opcode_count deep (config)
        size_t cur_saved_mie =
            cur_insn_index * (majority_count_group.blocks.size() - 1);
        if (cur_saved_mie >= best_saved_insn &&
            cur_insn_index >= m_config->block_split_min_opcode_count) {
          // Save it
          best_saved_insn = cur_saved_mie;
          best_insn_count = cur_insn_index;
          best_block_its = block_iterator_map;
          best_blocks = std::move(majority_count_group.blocks);
        }
      }

      // Update the current group with the best savings
      TRACE(DEDUP_BLOCKS, 4,
            "split_postfix: best block group.size() = %zu, instruction at %zu",
            best_blocks.size(), best_insn_count);
      split_group.postfix_block_its = std::move(best_block_its);
      split_group.postfix_blocks = std::move(best_blocks);
      split_group.insn_count = best_insn_count;
    }

    remove_if(splitGroupMap,
              [&](auto& entry) { return entry.postfix_blocks.size() <= 1; });

    TRACE(DEDUP_BLOCKS, 4, "split_postfix: total split groups = %zu",
          splitGroupMap.size());
    return splitGroupMap;
  }

  // The first entry that is not a redex-internal remark. Remarks are stripped
  // before dex emission and must stay transparent to dedup, so a remark at a
  // block's head must not hide the source block (or move-result) behind it.
  IRList::iterator first_non_remark(cfg::Block* b) {
    auto it = b->begin();
    while (it != b->end() && it->type == MFLOW_REMARK) {
      ++it;
    }
    return it;
  }

  // copy over the last source block of the main block to the commmon block
  void copy_last_source_block(cfg::Block* block, cfg::Block* split_block) {
    SourceBlock* last_src_blk = source_blocks::get_last_source_block(block);
    if (last_src_blk == nullptr) {
      return;
    }
    auto new_sb = std::make_unique<SourceBlock>(*last_src_blk);
    new_sb->id = SourceBlock::kSyntheticId;
    new_sb->next = nullptr;
    auto it = first_non_remark(split_block);
    if (it != split_block->end() && it->type == MFLOW_OPCODE &&
        opcode::is_move_result_any(it->insn->opcode())) {
      split_block->insert_after(it, std::move(new_sb));
    } else {
      split_block->insert_before(it, std::move(new_sb));
    }
  }

  // When the first entry moved to the split block is a source block, it was
  // originally in the predecessor block covering a throw-delineated segment.
  // Clone it back into the original block so both blocks retain the original
  // source block id and values.
  void copy_first_source_block(cfg::Block* block, cfg::Block* split_block) {
    auto* sb = source_blocks::get_first_source_block(split_block);
    if (sb == nullptr) {
      return;
    }
    auto last_insn_it = block->get_last_insn();
    if (last_insn_it == block->end()) {
      return;
    }
    // Put a faithful copy (original id and values) in the original block.
    auto original_copy = std::make_unique<SourceBlock>(*sb);
    source_blocks::impl::BlockAccessor::insert_source_block_after(
        block, last_insn_it, std::move(original_copy));
    // The split block's copy becomes a synthetic marker.
    sb->id = SourceBlock::kSyntheticId;
    sb->next = nullptr;
  }

  // After a postfix split, keep a source block in both halves for coverage.
  // A leading remark is transparent, so skip it when checking whether the
  // split block already begins with a source block.
  void restore_source_blocks_after_split(cfg::Block* block,
                                         cfg::Block* split_block) {
    auto head = first_non_remark(split_block);
    if (head == split_block->end() || head->type != MFLOW_SOURCE_BLOCK) {
      copy_last_source_block(block, split_block);
    } else {
      copy_first_source_block(block, split_block);
    }
  }

  // When instrumenting, do not deduplicate catch handler head blocks. If
  // the handlers are similar, splitting should make this a minimal block
  // of `move-exception` + `goto`.
  bool dedup_catch_handler_head_block(cfg::ControlFlowGraph& cfg,
                                      cfg::Block* block) {
    if (is_instrument_mode() &&
        (cfg.get_pred_edge_of_type(block, cfg::EdgeType::EDGE_THROW) !=
         nullptr)) {
      auto first = block->get_first_insn();
      if (first != block->end() &&
          opcode::is_move_exception(first->insn->opcode())) {
        return false;
      }
    }
    return true;
  }

  // For each group, split the blocks in the group where the reverse iterator
  // is located and dedup the common block created from split.
  void split_postfix_blocks(const PostfixSplitGroupMap& dups,
                            cfg::ControlFlowGraph& cfg) {
    for (const PostfixSplitGroupMap::value_type* entry : get_id_order(dups)) {
      const auto& group = entry->second;
      TRACE(DEDUP_BLOCKS, 4,
            "split_postfix: splitting blocks.size() = %zu, instruction at %zu",
            group.postfix_blocks.size(), group.insn_count);

      // Split the blocks at the reverse iterator where we determine to be
      // the best location.
      for (const auto& block_it_pair : group.postfix_block_its) {
        auto* block = block_it_pair.first;
        auto it = block_it_pair.second;

        // This means we are to split the entire block, which is essentially a
        // no-op and will be handled by dedup later.
        if (it == block->rend()) {
          continue;
        }

        // To convert reverse_iterator to iterator, we need to call .base() but
        // that points to the previous item. So we need to account for that.
        auto fwd_it =
            ir_list::InstructionIterator(std::prev(it.base()), block->end());
        auto fwd_it_end = ir_list::InstructionIterable(*block).end();

        if (is_instrument_mode() && it->type == MFLOW_SOURCE_BLOCK) {
          // If the first instruction after the source block is a move
          // instruction then split the block after the first non-move
          // instruction
          bool skipped_instruction = false;
          cfg::Block* split_block;
          while (fwd_it != fwd_it_end) {
            if (opcode::is_move_result_any(fwd_it->insn->opcode())) {
              fwd_it++;
              skipped_instruction = true;
              continue;
            }
            break;
          }
          if (skipped_instruction) {
            fwd_it--;
            split_block =
                cfg.split_block(block->to_cfg_instruction_iterator(fwd_it));
          } else {
            // use IRList::iterator because it can iterate through source
            // blocks,
            // unlike ir_list::InstructionIterator
            auto fwd_ir_it = IRList::iterator(std::prev(it.base()));
            split_block = cfg.split_block(block, fwd_ir_it);
          }
          // add a source block in the beginning if there isn't one already
          restore_source_blocks_after_split(block, split_block);
          continue;
        }

        // If we are splitting at the boundary of following iget/sget/invoke/
        // filled-new-array we should skip to the next instruction. Otherwise
        // splitting would generate a goto in between and lead to invalid
        // instruction.
        while (fwd_it != fwd_it_end) {
          auto fwd_it_next = fwd_it;
          fwd_it_next++;
          if (fwd_it_next != fwd_it_end) {
            auto opcode = fwd_it_next->insn->opcode();
            if (opcode::is_move_result_any(opcode)) {
              fwd_it = fwd_it_next;
              continue;
            }
          }

          break;
        }

        if (fwd_it == fwd_it_end || fwd_it.unwrap() == block->get_last_insn()) {
          continue;
        }

        auto cfg_it = block->to_cfg_instruction_iterator(fwd_it);
        // Split the block and add a source block in the beginning if there
        // isn't one already
        auto* split_block = cfg.split_block(cfg_it);
        restore_source_blocks_after_split(block, split_block);

        TRACE(DEDUP_BLOCKS, 4,
              "split_postfix: split block : old = %zu, new = %zu", block->id(),
              split_block->id());

        // Position of first instruction of split-off successor block
        if (needs_pos(split_block->begin(), split_block->end())) {
          auto* pos = cfg.get_dbg_pos(cfg_it);
          if (pos != nullptr) {
            // Make sure new block gets proper position
            cfg.insert_before(split_block, split_block->begin(),
                              std::make_unique<DexPosition>(*pos));
            ++m_stats.positions_inserted;
          }
        }

        ++m_stats.blocks_split;
      }
    }
  }

  bool is_eligible(cfg::Block* block, cfg::ControlFlowGraph& cfg) {
    // We can't split up move-result(-pseudo) instruction pairs
    if (begins_with_move_result(block)) {
      return false;
    }

    // For debugability, we don't want to dedup blocks involved direct or
    // indirect calls to Throwable.fillInStackTrace
    if (is_ineligible_because_of_fill_in_stack_trace(block)) {
      return false;
    }

    // Empty blocks are possibly necessary for profiling markers, or will
    // be cleaned up by CFG deconstruction.
    if (is_instrument_mode() && block->get_first_insn() == block->end()) {
      return false;
    }

    if (!dedup_catch_handler_head_block(cfg, block)) {
      return false;
    }

    // TODO: It's not worth the goto to merge return-only blocks. What size is
    // the minimum?

    return true;
  }

  static bool begins_with_move_result(cfg::Block* block) {
    const auto first_mie_it = block->get_first_insn();
    if (first_mie_it == block->end()) {
      return false;
    }
    auto first_op = first_mie_it->insn->opcode();
    return opcode::is_move_result_any(first_op);
  }

  bool is_ineligible_because_of_fill_in_stack_trace(cfg::Block* block) {
    if (m_config->dedup_fill_in_stack_trace) {
      return false;
    }
    auto ii = InstructionIterable(block);
    return std::any_of(ii.begin(), ii.end(), [](auto& mie) {
      return dedup_blocks_impl::is_ineligible_because_of_fill_in_stack_trace(
          mie.insn);
    });
  }

  // Deal with a verification error like this
  //
  // A: new-instance v0
  //    add-int v1, v2, v3       (this is here to clarify that A != C)
  // B: v0 <init>
  //
  //    ...
  //
  // C: new-instance v0
  // D: v0 <init>
  //
  // B == D. Coalesce!
  //
  // A: new-instance v0
  //    add-int v1, v2, v3
  // B: v0 <init>
  //
  // C: new-instance v0
  //    goto B
  //
  // But the verifier doesn't like this. When it merges v0 on B,
  // it declares it to be a conflict because they were instantiated
  // on different lines.
  // See androidxref.com/6.0.1_r10/xref/art/runtime/verifier/reg_type.cc#684
  //
  // It would be impossible to write this in java, but if you tried it would
  // look like this
  //
  // if (someCondition) {
  //   Foo a;
  // } else {
  //   Foo b;
  // }
  // (a or b) = new Foo();
  //
  // We avoid this situation by skipping blocks that contain an init
  // invocation to an object that didn't come from a unique instruction.
  static std::optional<std::vector<IRInstruction*>>
  get_init_receiver_instructions_defined_outside_of_block(
      cfg::Block* block, Lazy<live_range::LazyLiveRanges>& live_ranges) {
    std::vector<IRInstruction*> res;
    UnorderedSet<IRInstruction*> block_insns;
    for (auto& mie : InstructionIterable(block)) {
      auto* insn = mie.insn;
      if (opcode::is_invoke_direct(insn->opcode()) &&
          method::is_init(insn->get_method())) {
        TRACE(DEDUP_BLOCKS, 5, "[dedup blocks] found init invocation: %s",
              SHOW(insn));
        auto& defs = (*live_ranges->use_def_chains)[live_range::Use{insn, 0}];
        always_assert(!defs.empty());
        if (defs.size() > 1) {
          // should never happen, but we are not going to fight that here
          TRACE(DEDUP_BLOCKS, 5, "[dedup blocks] defs.size() = %zu",
                defs.size());
          return std::nullopt;
        }
        auto* def = *defs.begin();
        auto def_opcode = def->opcode();
        always_assert(opcode::is_new_instance(def_opcode) ||
                      opcode::is_a_load_param(def_opcode));
        // Log def instruction if it is not an earlier instruction from the
        // current block.
        if (block_insns.count(def) == 0u) {
          res.push_back(def);
        } else {
          TRACE(DEDUP_BLOCKS, 5, "[dedup blocks] defined in block");
        }
      }
      block_insns.insert(insn);
    }
    return res;
  }

  void check_inits(cfg::ControlFlowGraph& cfg) {
    reaching_defs::MoveAwareFixpointIterator fixpoint_iter(cfg);
    fixpoint_iter.run(reaching_defs::Environment());
    for (cfg::Block* block : cfg.blocks()) {
      auto env = fixpoint_iter.get_entry_state_at(block);
      for (auto& mie : InstructionIterable(block)) {
        IRInstruction* insn = mie.insn;
        if (opcode::is_invoke_direct(insn->opcode()) &&
            method::is_init(insn->get_method())) {
          auto defs = env.get(insn->src(0));
          always_assert(!defs.is_top());
          always_assert(defs.elements().size() == 1);
        }
        fixpoint_iter.analyze_instruction(insn, &env);
      }
    }
  }

  void record_stats(const Duplicates& duplicates) {
    // avoid the expensive lock if we won't actually print the information
    if (traceEnabled(DEDUP_BLOCKS, 2)) {
      for (const auto& entry : UnorderedIterable(duplicates)) {
        const auto& blocks = entry.second;
        // all blocks have the same number of opcodes
        cfg::Block* block = *blocks.begin();
        m_stats.dup_sizes[num_opcodes(block)] += blocks.size();
      }
    }
  }

  // remove sets with only one block
  template <typename TKey,
            typename TValue,
            typename THash,
            typename TPred,
            typename NeedToRemove>
  static void remove_if(UnorderedMap<TKey, TValue, THash, TPred>& duplicates,
                        NeedToRemove need_to_remove) {
    unordered_erase_if(duplicates,
                       [&](auto& p) { return need_to_remove(p.second); });
  }

  static bool is_singleton_or_inconsistent(
      const BlockSet& blocks,
      Lazy<live_range::LazyLiveRanges>& live_ranges,
      LivenessFixpointIterator& liveness_fixpoint_iter,
      Lazy<type_inference::TypeInference>& type_inference) {
    if (blocks.size() <= 1) {
      return true;
    }

    // Next we check if there are disagreeing init-receiver instructions.
    // TODO: Instead of just dropping all blocks in this case, do
    // finer-grained partitioning.
    std::optional<std::vector<IRInstruction*>> insns;
    for (cfg::Block* block : blocks) {
      auto other_insns =
          get_init_receiver_instructions_defined_outside_of_block(block,
                                                                  live_ranges);
      if (!other_insns) {
        return true;
      } else if (!insns) {
        insns = std::move(other_insns);
      } else if (*insns != *other_insns) {
        always_assert(insns->size() == other_insns->size());
        return true;
      }
    }

    // Next we check if there are inconsistently typed incoming registers.
    // TODO: Instead of just dropping all blocks in this case, do
    // finer-grained partitioning.

    // Initializing stuff...
    const auto& live_in_vars =
        liveness_fixpoint_iter.get_live_in_vars_at(*blocks.begin());
    always_assert(!live_in_vars.is_top());
    if (live_in_vars.is_bottom()) {
      // should never happen, but we are not going to fight that here
      return true;
    }
    // Join together all initial type environments of the the blocks; this
    // corresponds to what will happen when we dedup the blocks.
    auto joined_env = type_inference::TypeEnvironment::bottom();
    for (cfg::Block* block : blocks) {
      joined_env.join_with(type_inference->get_entry_state_at(block));
    }
    if (joined_env.is_bottom()) {
      // shouldn't happen, but we are not going to fight that here
      return true;
    }
    // Let's see if any of the type environments of the existing blocks
    // match, considering the live-in registers. If so, we know that things will
    // verify after deduping.
    for (auto reg : live_in_vars.elements()) {
      auto joined_type = joined_env.get_type(reg);
      if (!type_inference::is_safely_usable_in_ifs(joined_type.element())) {
        return true;
      }
      if (joined_type.element() != IRType::REFERENCE) {
        continue;
      }
      // If any of the reference types we joined might have been of an array
      // type...
      auto joined_type_domain = DexTypeDomain::bottom();
      auto common_dex_type = joined_env.get_dex_type(reg);
      bool maybe_array{false};
      bool maybe_array_of_object{false};
      for (cfg::Block* block : blocks) {
        auto type_domain =
            type_inference->get_entry_state_at(block).get_type_domain(reg);
        auto dex_type = type_domain.get_dex_type();
        if (type_domain.is_top() || !dex_type) {
          maybe_array = true;
          maybe_array_of_object = true;
        } else if (type::is_array(*dex_type)) {
          maybe_array = true;
          if (type::is_object(type::get_array_component_type(*dex_type))) {
            maybe_array_of_object = true;
          }
        }
        joined_type_domain.join_with(type_domain);
        if (common_dex_type && dex_type && *common_dex_type != *dex_type) {
          common_dex_type = std::nullopt;
        }
      }
      always_assert(!joined_type_domain.is_bottom());
      always_assert(!maybe_array_of_object || maybe_array);
      if (!maybe_array) {
        continue;
      }
      if (common_dex_type) {
        // Trivial join. This is fine.
        continue;
      }
      auto reaching_defs = reaching_defs::Domain::bottom();
      auto init_reaching_defs = [&blocks, &live_ranges, &reaching_defs, reg]() {
        if (reaching_defs.is_bottom()) {
          const auto& fp_iter = live_ranges->chains.get_fp_iter();
          for (cfg::Block* block : blocks) {
            reaching_defs.join_with(fp_iter.get_entry_state_at(block).get(reg));
          }
          always_assert(!reaching_defs.is_bottom());
        }
      };
      if (maybe_array_of_object) {
        // Android's verifier has shortcomings around arrays of interface types,
        // so if there's any use of the register in such a context, we give up.
        // TODO: This is very conservative. Right now, we give up by just
        // looking at the use-instructions. We can be more precise by analyzing
        // the type demand of the instruction, and only give up if it involves
        // an array of an interface type.
        init_reaching_defs();
        for (auto* reaching_def : reaching_defs.elements()) {
          for (const auto& use : UnorderedIterable(
                   (*live_ranges->def_use_chains)[reaching_def])) {
            auto op = use.insn->opcode();
            if (opcode::is_an_aget(op) || opcode::is_an_iput(op) ||
                opcode::is_an_sput(op) || opcode::is_an_invoke(op) ||
                opcode::is_a_return(op)) {
              return true;
            }
          }
        }
      }
      // ...but didn't join to an array type...
      if (!joined_type_domain.is_top()) {
        auto joined_dex_type = joined_type_domain.get_dex_type();
        if (joined_dex_type && type::is_array(*joined_dex_type)) {
          continue;
        }
      }
      // ...then we need to make sure that register is not used with an
      // instruction that expects *some* array type.
      init_reaching_defs();
      for (auto* reaching_def : reaching_defs.elements()) {
        for (const auto& use :
             UnorderedIterable((*live_ranges->def_use_chains)[reaching_def])) {
          auto op = use.insn->opcode();
          if (opcode::is_array_length(op) || opcode::is_an_aget(op) ||
              opcode::is_an_aput(op) || opcode::is_fill_array_data(op)) {
            return true;
          }
        }
      }
    }
    return false;
  }

  static size_t num_opcodes(cfg::Block* block) {
    const auto& iterable = InstructionIterable(block);
    return std::distance(iterable.begin(), iterable.end());
  }

  [[maybe_unused]] void print_dups(const Duplicates& dups) {
    TRACE(DEDUP_BLOCKS, 4, "duplicate blocks set: {");
    for (const auto& entry : UnorderedIterable(dups)) {
      TRACE(
          DEDUP_BLOCKS, 4, "  hash = %zu",
          DedupBlkValueNumbering::BlockValueHasher{}(*entry.first.block_value));
      for (cfg::Block* b : entry.second) {
        TRACE(DEDUP_BLOCKS, 4, "    block %zu", b->id());
        for (const MethodItemEntry& mie : *b) {
          TRACE(DEDUP_BLOCKS, 4, "      %s", SHOW(mie));
        }
      }
    }
    TRACE(DEDUP_BLOCKS, 4, "} end duplicate blocks set");
  }
};

} // namespace

DedupBlocks::DedupBlocks(const Config* config, DexMethod* method)
    : DedupBlocks(config,
                  method->get_code(),
                  is_static(method),
                  method->get_class(),
                  method->get_proto()->get_args()) {}

DedupBlocks::DedupBlocks(const Config* config,
                         IRCode* code,
                         bool is_static,
                         DexType* declaring_type,
                         DexTypeList* args)
    : m_config(config),
      m_code(code),
      m_is_static(is_static),
      m_declaring_type(declaring_type),
      m_args(args) {
  always_assert(m_config);
}

void DedupBlocks::run() {
  DedupBlocksImpl impl(m_config, m_stats);
  auto& cfg = m_code->cfg();
  uint32_t iteration = 0;
  do {
    ++iteration;
    if (m_config->split_postfix) {
      impl.split_postfix(cfg);
    }
  } while (impl.dedup(m_is_static, m_declaring_type, m_args, cfg) &&
           iteration < m_config->max_iteration);
}

Stats& Stats::operator+=(const Stats& that) {
  eligible_blocks += that.eligible_blocks;
  blocks_removed += that.blocks_removed;
  insns_removed += that.insns_removed;
  blocks_split += that.blocks_split;
  positions_inserted += that.positions_inserted;
  join_stats += that.join_stats;
  positions_merged_without_correspondence +=
      that.positions_merged_without_correspondence;
  for (const auto& p : UnorderedIterable(that.dup_sizes)) {
    dup_sizes[p.first] += p.second;
  }
  return *this;
}

} // namespace dedup_blocks_impl
