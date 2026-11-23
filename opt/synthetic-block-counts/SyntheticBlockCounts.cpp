/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "SyntheticBlockCounts.h"

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <functional>
#include <limits>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include <sparta/WeakTopologicalOrdering.h>

#include "CallGraph.h"
#include "ConcurrentContainers.h"
#include "ConfigFiles.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexClass.h"
#include "DexStore.h"
#include "DexUtil.h"
#include "GraphUtil.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "IROpcode.h"
#include "LoopInfo.h"
#include "MethodOverrideGraph.h"
#include "MethodProfiles.h"
#include "PassManager.h"
#include "RedexContext.h"
#include "Resolver.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "Walkers.h"

// ============================================================================
// ALGORITHM
// ============================================================================
// This pass turns the boolean coverage on SourceBlocks into per-block execution
// COUNTS. The entry block of a method is assumed to run `call_count` times (a
// number from the profile); every other block runs some fraction or multiple of
// that, decided by the branches and loops between it and the entry.
//
// ----------------------------------------------------------------------------
// SECTION A -- Per-method estimate (the default path; `process_method`)
// ----------------------------------------------------------------------------
// The per-block frequencies are computed with a standard two-step control-flow
// frequency propagation (the "Wu-Larus" scheme; Wu & Larus, "Static Branch
// Frequency and Program Profile Analysis," MICRO-27, 1994):
//
// The two-step split -- edge probabilities first, then block frequencies --
// mirrors the architecture of LLVM's `BranchProbabilityInfo` /
// `BlockFrequencyInfo` (`BlockFrequencyInfoImpl`): assign edge probabilities,
// then derive relative block frequencies. This is an architectural analogy, not
// a port -- LLVM carries far richer static branch heuristics and general
// cyclic-region handling, whereas here SourceBlock coverage supplies the
// primary support constraint and reducible loops use a bounded geometric
// approximation.
//
// STEP 1 -- edge probabilities. For each block, split its outgoing flow across
// its successor edges, layered:
//   * structural default: one successor gets all the flow; a multi-way split
//     (if/else or switch) divides evenly across its successors. An if/else is
//     NOT biased by branch direction -- which arm is the fall-through vs. the
//     explicit target is an invertible compiler artifact that carries no
//     signal.
//   * appear100 nudge: multiply an edge's weight by the target block's
//     `appear100` (the fraction of profiled runs the target appeared in), so a
//     rarely-seen successor gets less flow.
//   * exception edges (thrown-exception successors) get a tiny weight
//     (`handler_cold_factor`), since handlers rarely run.
//   * coverage pin: a successor whose boolean coverage is 0 for this
//   interaction
//     (it never ran) gets NO flow. This keeps the estimate consistent with what
//     was actually observed.
// Each block's out-edge weights are then normalized to sum to 1.
//
// The exception-cold default above is a static prior in the tradition of Ball &
// Larus, "Branch Prediction for Free," PLDI 1993 -- a guess, not a measurement.
// Among ordinary covered successors we make NO directional guess: SourceBlock
// support constrains WHICH successors may receive flow, and where it does not
// reveal the split we divide uniformly (maximum entropy) rather than invent a
// bias the edge encoding cannot justify.
//
// STEP 2 -- forward propagation. Visit blocks in reverse-post-order (each block
// after all of its non-loop predecessors). A block's frequency is the sum over
// its incoming forward edges of (source frequency * edge probability), starting
// from entry = `call_count`.
//   * Loops: a reducible (well-formed) loop header is amplified by the
//     closed-form geometric factor 1/(1 - p_back), where p_back is the
//     back-edge probability, capped at `loop_iteration_cap` -- so an estimated
//     loop can multiply a block's count by at most that cap.
//   * Odd loop shapes (irreducible / multi-entry) are treated as plain merges
//     (no amplification) rather than guessed at.
//
// WRITE-BACK. The solved frequency is written to `val` only for blocks already
// covered (`val > 0`); 0 and NaN are left untouched. The result is floored to
// `epsilon` (kept strictly > 0) and kept as a float. `appear100` is never
// written. A block with no profile for an interaction keeps its boolean value.
//
// EXAMPLE. A method called 1000 times, with a covered if/else and a covered
// loop inside one arm:
//     entry             -> 1000
//     if-then / if-else -> ~500 each (0.5 split)
//     loop body         -> ~500 * (loop factor, capped)
// If the else-arm block had boolean coverage 0 (never observed), it gets no
// flow and its `val` stays 0.
//
// LIMITATION -- this estimate is purely LOCAL. Each method is anchored to its
// OWN `call_count`, with no reconciliation across method boundaries. So the
// count this pass gives a caller's invoke block (an estimate of how many times
// that call site fires) and the count it independently gives the callee method
// (anchored to the callee's own `call_count`) can disagree -- the two are
// solved separately and need not add up. The inter-method engine (SECTION B,
// added by a later commit) propagates counts to unprofiled methods (and bounds
// a caller by an exact profiled callee's `call_count`), but does NOT fully
// reconcile a caller's invoke count with a profiled callee's own `call_count`
// -- that gap persists even with the engine on.
// ----------------------------------------------------------------------------
// SECTION B -- Inter-method estimate (`intermethod=true`; `run_intermethod*`)
// ----------------------------------------------------------------------------
// The per-method estimate can only heat a method that has its own profile. Many
// methods have no `call_count` of their own -- they were fully inlined or
// otherwise transformed away in the instrumentation build that produced the
// profile, so no per-method counter was ever recorded for them. Per-method
// leaves such methods cold even when their callers are red-hot. Section B lets
// counts flow across the call graph.
//
// The per-method solve is LINEAR in its entry anchor: solving at anchor 1.0
// yields a per-block "shape" (each block's frequency relative to entry). So
// each method is solved ONCE at anchor 1.0 (this is why `solve_block_freq`
// takes the anchor as a parameter) and the shape is cached and scaled. Per
// interaction slot (each slot is independent):
//
// 1. SHAPE. For every relevant method, solve the shape once and cache it.
//    Record, for every call instruction, k = shape[block containing the call] =
//    how many times that call fires per one entry to its method.
// 2. PIN. A method WITH a profile is pinned: its scale is its own `call_count`,
//    and it is a pure source -- it never takes inflow and is never adjusted. On
//    pinned methods the result equals the per-method result, so turning the
//    engine on cannot regress any method that already has ground truth.
// 3. FORWARD FLOW. A method WITHOUT a profile gets scale(M) = sum over
//    callers C of scale(C) * k(C->M): if C runs scale(C) times and the call
//    site to M runs k times per entry to C, then M is invoked scale(C)*k times
//    from C.
//    Solved by repeated sweeps in caller-before-callee order (a bounded
//    relaxation): the acyclic majority settles in one sweep; recursion cycles
//    re-iterate until the per-sweep change falls below
//    `intermethod_converge_eps` or a fixed sweep cap.
//    This is call-graph propagation of synthetic entry counts in the spirit of
//    LLVM's `SyntheticCountsUtils`, solved as standard worklist dataflow
//    iteration (Kildall, "A Unified Approach to Global Program Optimization,"
//    POPL 1973): caller-before-callee order settles the acyclic majority in one
//    sweep, and dirty propagation confines later sweeps to the recursive
//    frontier. It differs in that measured methods are immutable pins, each
//    call edge is weighted by the caller's unit-entry shape k(C->M), and an
//    exact profiled callee imposes a backward upper bound (step 4).
// 4. UPPER BOUND. An exact (single-target) call C->T to a PROFILED callee T can
//    fire at most call_count(T) times, so scale(C) <= call_count(T)/k(C->T).
//    Each scale is clamped to the smallest such bound; where no exact profiled
//    callee constrains a method (unprofiled recursion), the bound defaults to
//    the per-interaction data-derived ceiling
//    `intermethod_max_scale_factor * max(usable call_count)`, which keeps
//    cycles bounded. This is a sound cap: it can lower a fabricated
//    over-estimate but never mislabels a hot method cold.
// 5. VIRTUAL CALLS. A call with several possible targets splits its
//    contribution evenly across them. A call with more than
//    `kBigOverrideThreshold` targets (megamorphic) is dropped from the graph
//    entirely -- it behaves as a sink and contributes nothing, rather than
//    inventing a wide fan-out.
//    Possible targets come from class-hierarchy analysis (Dean, Grove &
//    Chambers, "Optimization of Object-Oriented Programs Using Static Class
//    Hierarchy Analysis," ECOOP 1995): CHA yields which targets are POSSIBLE,
//    not the receiver-type distribution, so the even 1/N split is an explicit
//    structural prior, not a measured dispatch frequency. This is a known
//    limitation: when the true receiver distribution is skewed (one dominant
//    target), 1/N materially misattributes flow -- over-heating the rare
//    targets and under-heating the hot one. Refining it with receiver-type
//    profiles is left for future work.
// 6. WRITE-BACK. Each block's count is scale(M) * shape[block], written with
//    the same support-preserving guard and `epsilon` floor as Section A, as a
//    float (no representation ceiling). A method that ends with scale 0
//    (unprofiled and unreached) is skipped, leaving its boolean coverage
//    untouched.
//
// Only methods reachable from a profiled method can ever get a nonzero count,
// so the expensive shape solve runs only for that "relevance set"; every other
// method's write is a guaranteed no-op and is skipped. The per-method phases
// (shape, write-back) run in parallel across methods; the cross-method flow
// (step 3) is a single sequential pass because it walks the call graph.
//
// EXAMPLE. `caller` runs 1,000,000 times and calls unprofiled `log()` once per
// entry (k = 1). Per-method leaves `log()` cold (no profile). Inter-method
// gives it scale ~1,000,000, so a size pass can see `log()` is actually hot and
// avoid hoisting it out of line.
//
// NOT a conservation solve. This engine only ADDS counts to unprofiled methods;
// a profiled method stays pinned to its own `call_count` and is never adjusted.
// The sum of caller invoke counts flowing into a profiled callee is therefore
// NOT reconciled with that callee's `call_count` -- the two can disagree, and
// this engine does not close that gap. The backward bound (step 4) only caps
// unprofiled callers on exact edges; it does not make callsite sums equal
// callee totals.
// ----------------------------------------------------------------------------
// SECTION C -- Callsite-cap reconciliation (`reflow_block_freq`)
// ----------------------------------------------------------------------------
// Sections A and B can hand a call block more executions than an exact profiled
// callee's `call_count` permits. Reconciling block/edge counts, observations,
// and flow conservation is, in full generality, a global constrained-flow
// optimization; LLVM's `SampleProfileInference` is a production example of that
// approach.
//
// This pass deliberately takes a cheaper route: collapse CFG cycles into their
// SCC condensation DAG, bound each SCC's downstream capacity in one reverse
// sweep, then place the pinned entry flow in one forward sweep -- preserving
// the producer's prior split wherever capacity allows and metering the
// remainder as spill. It is deterministic and O(V+E), NOT a max-flow /
// min-cost-flow solve: reconvergent paths can double-count shared downstream
// capacity, so the result is an approximation, not a globally consistent flow.
//
// EXAMPLE. A capped reconvergent diamond:
//     void caller() {           // profiled, so pinned at 1000 entries
//       if (cond) foo();
//       else      bar();
//       log();                  // both arms reconverge here; log()'s own
//     }                         // call_count caps this merge at 600
// The profile is internally contradictory: 1000 entries must funnel through the
// merge, but it caps at 600 -- no flow satisfies both. The one-sweep capacity
// DP also credits the merge's 600 to BOTH arms (shared downstream is double-
// counted), so cap_eff upstream is only an upper bound. Re-flow places the 600
// it can and SPILLS the remaining 400 to the return sink (metered as
// `sink_spill`) instead of fabricating a consistent 1000 through a 600 merge.
// A global min-cost flow would resolve it; we deliberately did not build one.

namespace {

// Closed-form geometric loop amplification for a reducible natural-loop
// header: `1/(1-p_back)`, clamped to `[1, loop_iteration_cap]`. `p_back` is the
// summed back-edge probability into the header; a covered header with no
// measured back-edge falls back to `default_backedge_prob`. The `p_back` clamp
// to `cap_pb = 1 - 1/cap` keeps `1-p_back >= 1/cap > 0`, so the reciprocal is
// never a divide-by-~0 (no inf/negative multiplier). Shared by the forward
// solve and the re-flow allocation.
double loop_geometric_mult(double p_back,
                           bool covered_hot,
                           float loop_iteration_cap,
                           float default_backedge_prob) {
  if (p_back <= 0.0 && covered_hot) {
    p_back = default_backedge_prob;
  }
  const double cap = (double)loop_iteration_cap;
  const double cap_pb = 1.0 - 1.0 / cap;
  if (p_back > cap_pb) {
    p_back = cap_pb;
  }
  if (p_back >= 1.0) {
    return cap;
  }
  return std::clamp(1.0 / (1.0 - p_back), 1.0, cap);
}

// (2) Per-out-edge probability estimation for interaction slot `i`. Each edge's
// weight combines a structural backbone (uniform split over forward
// successors), the target's appear100 prior, a coverage pin (cold targets get
// no flow), and exception-handler coldness on throw edges.
// Shape-only (independent of the entry anchor), so it can be computed once and
// reused by both the forward solve and the re-flow allocation.
UnorderedMap<const cfg::Edge*, double> compute_edge_prob(
    cfg::ControlFlowGraph& cfg,
    size_t i,
    float handler_cold_factor,
    size_t* zero_outflow_sinks) {
  UnorderedMap<const cfg::Edge*, double> edge_prob;
  for (auto* b : cfg.blocks_view()) {
    const auto& succs = b->succs();
    if (succs.empty()) {
      continue;
    }
    // Number of ordinary forward successors (GOTO/BRANCH); throw and ghost
    // edges are handled separately below and excluded from the uniform split.
    size_t n_flow = 0;
    for (auto* e : succs) {
      const auto t = e->type();
      if (t == cfg::EDGE_GOTO || t == cfg::EDGE_BRANCH) {
        n_flow++;
      }
    }

    double sum = 0.0;
    std::vector<std::pair<cfg::Edge*, double>> ws;
    ws.reserve(succs.size());
    for (auto* e : succs) {
      const auto t = e->type();
      double w = 0.0;
      auto* tsb = source_blocks::get_first_source_block(e->target());
      const auto tval = (tsb != nullptr) ? tsb->get_val(i) : std::nullopt;
      if (t == cfg::EDGE_GHOST) {
        w = 0.0; // fake exit edge
      } else if (t == cfg::EDGE_THROW) {
        w = handler_cold_factor; // throw edge: fixed exception-handler coldness
      } else {
        // Structural backbone: every forward successor gets an equal
        // share; a lone successor gets 1.0 (== 1.0 / n_flow at n_flow == 1).
        // Branch direction is an invertible encoding artifact, so we never bias
        // one arm over another.
        w = 1.0 / (double)n_flow;
        // Scale by the target's appear100 prior.
        const auto tappear =
            (tsb != nullptr) ? tsb->get_appear100(i) : std::nullopt;
        if (tappear && *tappear > 0.0f) {
          w *= (double)*tappear;
        }
      }
      // Coverage pin: a target that is cold for THIS interaction
      // receives no flow.
      if (t != cfg::EDGE_GHOST && tval && *tval == 0.0f) {
        w = 0.0;
      }
      ws.emplace_back(e, w);
      sum += w;
    }
    if (sum > 0.0) {
      for (auto& [e, w] : ws) {
        if (w > 0.0) {
          edge_prob[e] = w / sum;
        }
      }
    } else {
      (*zero_outflow_sinks)++;
    }
  }
  return edge_prob;
}

// (3) Forward block-frequency solve over reverse-postorder, given precomputed
// `edge_prob`. Result is LINEAR in `entry_anchor`. Reducible loop headers get
// the closed-form geometric multiplier; irreducible headers are treated as
// ordinary merges (and counted).
UnorderedMap<const cfg::Block*, double> forward_propagate(
    size_t i,
    double entry_anchor,
    loop_impl::LoopInfo& loops,
    const std::vector<cfg::Block*>& rpo,
    const UnorderedMap<const cfg::Block*, size_t>& rpo_index,
    cfg::Block* entry,
    const UnorderedMap<const cfg::Edge*, double>& edge_prob,
    float loop_iteration_cap,
    float default_backedge_prob,
    size_t* irreducible) {
  const size_t entry_idx = rpo_index.at(entry);

  // Loops innermost-first (deepest depth first) so an inner loop's multiplier
  // is known before an enclosing loop's local propagation crosses it.
  std::vector<loop_impl::Loop*> loops_inner_first;
  for (auto& loop : loops) {
    loops_inner_first.push_back(&loop);
  }
  std::stable_sort(loops_inner_first.begin(), loops_inner_first.end(),
                   [](loop_impl::Loop* a, loop_impl::Loop* b) {
                     return a->get_loop_depth() > b->get_loop_depth();
                   });

  // (2.5) Per-loop cyclic multiplier. p_back is the header-anchored probability
  // of taking a back-edge:
  //   p_back = Σ_latch freq_local(latch) · edge_prob(latch→header),
  // where freq_local is the intra-loop frequency with the header pinned to 1
  // (inner loops collapsed via their already-computed multiplier). Summing the
  // RAW back-edge probability alone (ignoring freq_local) over-counts any loop
  // whose exit is at the header (e.g. `while (cond)`), which is the common
  // case.
  UnorderedMap<const cfg::Block*, double> loop_mult; // header -> multiplier
  for (loop_impl::Loop* loop : loops_inner_first) {
    auto* header = loop->get_header();
    auto header_it = rpo_index.find(header);
    if (header_it == rpo_index.end()) {
      // Loop unreachable from entry: it never contributes to the forward solve
      // (the forward pass iterates rpo, which excludes it). This pass is a pure
      // annotator and does not prune unreachable blocks, so such loops can be
      // present; skip cheaply.
      loop_mult[header] = 1.0;
      continue;
    }
    const size_t header_idx = header_it->second;
    // A loop entered at more than one block has no header to anchor a
    // geometric multiplier on, so its head is treated as an ordinary merge.
    if (!loop->is_reducible()) {
      (*irreducible)++;
      loop_mult[header] = 1.0;
      continue;
    }
    // Local header-anchored acyclic propagation over ONLY the loop's own blocks
    // in RPO order. Iterating the loop body (not the whole method) keeps total
    // work at O(Σ_loops |loop|·log|loop|) rather than O(#loops · #blocks) --
    // the latter is quadratic on methods with many loops and was the dominant
    // cost.
    std::vector<cfg::Block*> loop_blocks;
    for (auto* b : loop->get_blocks()) {
      loop_blocks.push_back(b);
    }
    std::sort(loop_blocks.begin(), loop_blocks.end(),
              [&](cfg::Block* a, cfg::Block* c) {
                return rpo_index.at(a) < rpo_index.at(c);
              });
    UnorderedMap<const cfg::Block*, double> fl;
    fl[header] = 1.0;
    for (auto* b : loop_blocks) {
      if (b == header) {
        continue;
      }
      const size_t b_idx = rpo_index.at(b);
      double in = 0.0;
      for (auto* pe : b->preds()) {
        auto* u = pe->src();
        if (!loop->contains(u)) {
          continue; // only intra-loop forward edges build freq_local
        }
        auto uit = rpo_index.find(u);
        const size_t u_idx = uit != rpo_index.end() ? uit->second : entry_idx;
        if (u_idx >= b_idx) {
          continue; // back-edge (into an inner header): carried by its mult
        }
        auto epit = edge_prob.find(pe);
        const double ep = epit != edge_prob.end() ? epit->second : 0.0;
        const double uf = (fl.count(u) != 0u) ? fl[u] : 0.0;
        in += uf * ep;
      }
      auto lmit = loop_mult.find(b);
      if (lmit != loop_mult.end()) {
        in *= lmit->second; // b is an inner loop header
      }
      fl[b] = in;
    }
    // p_back over back-edges into the header (source inside the loop).
    double p_back = 0.0;
    for (auto* pe : header->preds()) {
      auto* u = pe->src();
      if (!loop->contains(u)) {
        continue;
      }
      auto uit = rpo_index.find(u);
      const size_t u_idx = uit != rpo_index.end() ? uit->second : entry_idx;
      if (u_idx < header_idx) {
        continue; // forward pred inside the loop (not a back-edge)
      }
      auto epit = edge_prob.find(pe);
      const double ep = epit != edge_prob.end() ? epit->second : 0.0;
      const double uf = (fl.count(u) != 0u) ? fl[u] : 0.0;
      p_back += uf * ep;
    }
    auto* hsb = source_blocks::get_first_source_block(header);
    const auto hval = (hsb != nullptr) ? hsb->get_val(i) : std::nullopt;
    const bool covered_hot = hval && *hval > 0.0f;
    loop_mult[header] = loop_geometric_mult(
        p_back, covered_hot, loop_iteration_cap, default_backedge_prob);
  }

  // (3) Forward block-frequency solve over reverse-postorder, applying the
  // precomputed loop multiplier at each header.
  UnorderedMap<const cfg::Block*, double> block_freq;
  block_freq[entry] = entry_anchor;
  for (auto* b : rpo) {
    if (b == entry) {
      continue;
    }
    const size_t b_idx = rpo_index.at(b);
    double inflow = 0.0;
    for (auto* e : b->preds()) {
      auto* u = e->src();
      auto it = rpo_index.find(u);
      const size_t u_idx = it != rpo_index.end() ? it->second : entry_idx;
      if (u_idx >= b_idx) {
        continue; // back-edge: not part of forward inflow
      }
      auto epit = edge_prob.find(e);
      const double ep = (epit != edge_prob.end()) ? epit->second : 0.0;
      const double src_freq = (block_freq.count(u) != 0u) ? block_freq[u] : 0.0;
      inflow += src_freq * ep;
    }
    auto lmit = loop_mult.find(b);
    block_freq[b] = (lmit != loop_mult.end()) ? inflow * lmit->second : inflow;
  }
  return block_freq;
}

// Wu-Larus reverse-post-order block-frequency solve for interaction slot `i`,
// with the entry block anchored to `entry_anchor` (steps 2 and 3 of the
// per-method solve). The result is LINEAR in `entry_anchor`: passing 1.0 yields
// a per-method "shape" (relative per-block frequency) that a caller can cache
// once and scale by any entry count -- this is what the inter-method engine
// consumes as shape_M(b) / k_C(invoke). `epsilon` flooring is intentionally NOT
// applied here (it belongs at the write site).
UnorderedMap<const cfg::Block*, double> solve_block_freq(
    cfg::ControlFlowGraph& cfg,
    size_t i,
    double entry_anchor,
    loop_impl::LoopInfo& loops,
    const std::vector<cfg::Block*>& rpo,
    const UnorderedMap<const cfg::Block*, size_t>& rpo_index,
    cfg::Block* entry,
    float handler_cold_factor,
    float loop_iteration_cap,
    float default_backedge_prob,
    size_t* zero_outflow_sinks,
    size_t* irreducible) {
  const auto edge_prob =
      compute_edge_prob(cfg, i, handler_cold_factor, zero_outflow_sinks);
  return forward_propagate(i, entry_anchor, loops, rpo, rpo_index, entry,
                           edge_prob, loop_iteration_cap, default_backedge_prob,
                           irreducible);
}

// Reverse-postorder of `cfg` plus a block -> rpo-position index. Shared solve
// scaffolding for the per-method frequency solves.
void build_rpo(cfg::ControlFlowGraph& cfg,
               std::vector<cfg::Block*>& rpo,
               UnorderedMap<const cfg::Block*, size_t>& rpo_index) {
  rpo = graph::postorder_sort<cfg::GraphInterface>(cfg);
  std::reverse(rpo.begin(), rpo.end());
  rpo_index.reserve(rpo.size());
  for (size_t idx = 0; idx < rpo.size(); ++idx) {
    rpo_index[rpo[idx]] = idx;
  }
}

// Diagnostic counters for the callsite cap, accumulated by the clamp post-pass.
// (The re-flow post-pass calls the shared cap helpers but passes cc=nullptr, so
// it does not accumulate these.) Atomic so a parallel per-method walk can
// accumulate them.
struct CapCounters {
  std::atomic<size_t> exact_invokes_seen{0};
  std::atomic<size_t> unresolved_invokes{0}; // exact opcode, target
                                             // unresolvable
  std::atomic<size_t> unprofiled_callees{0}; // resolved callee, no row (per
                                             // i)
  std::atomic<size_t> throw_gated_invokes{0}; // invoke not counted: a
                                              // may-throw insn precedes it in
                                              // the block
};

// Distinct EXACT single-target callees of a block, mapped to the
// number of GUARANTEED invokes of each -- calls that every entry to the block
// is certain to execute. Fills `mult` (cleared first) so callers can reuse
// one map across the blocks of a method instead of allocating per block.
// Interaction- independent -- computed once per block.
// invoke-static/-direct/-super only; virtual/interface need a call graph to
// resolve and are skipped.
//
// Multiplicity underpins the cap `call_count(M) / mult`: a block that is
// certain to call M `mult` times can run at most call_count(M)/mult times.
// "Certain" matters -- the bound is an UPPER bound on the block frequency
// only if every entry completes all `mult` calls. A may-throw instruction can
// abort the block early, so an invoke is counted only while no earlier
// instruction in the block could throw. Because an invoke can itself throw, a
// repeated call to the same M contributes just its first (guaranteed)
// occurrence; the trailing ones are throw-gated. Counting guaranteed calls
// only keeps `call_count(M)/mult` an upper bound instead of the lower bound a
// raw invoke count would give -- best-effort, not strictly sound, since the
// guaranteed invoke can still throw before entering M (see
// callsite_cap_for_interaction).
void exact_callee_multiplicity(const cfg::Block* b,
                               DexMethod* caller,
                               CapCounters* cc,
                               UnorderedMap<DexMethod*, uint32_t>& mult) {
  mult.clear();
  bool blocked = false; // an earlier instruction in this block could throw
  for (const auto& mie : *b) {
    if (mie.type != MFLOW_OPCODE) {
      continue;
    }
    const IROpcode op = mie.insn->opcode();
    if (opcode::is_invoke_static(op) || opcode::is_invoke_direct(op) ||
        opcode::is_invoke_super(op)) {
      if (cc != nullptr) {
        cc->exact_invokes_seen.fetch_add(1, std::memory_order_relaxed);
      }
      // `caller` is required for correct invoke-super resolution.
      DexMethod* callee = resolve_invoke_method(mie.insn, caller);
      if (callee == nullptr) {
        if (cc != nullptr) {
          cc->unresolved_invokes.fetch_add(1, std::memory_order_relaxed);
        }
      } else if (blocked) {
        // A prior may-throw means not every entry reaches this invoke, so it
        // cannot raise the callee's guaranteed multiplicity (metered only).
        if (cc != nullptr) {
          cc->throw_gated_invokes.fetch_add(1, std::memory_order_relaxed);
        }
      } else {
        mult[callee]++;
      }
    }
    // The invoke's own call still executes before the invoke can throw, so
    // only instructions AFTER a may-throw are unguaranteed: update `blocked`
    // once the current instruction has been accounted for.
    if (opcode::can_throw(op)) {
      blocked = true;
    }
  }
}

// Best-effort upper bound on how often a block can run in interaction
// `interaction`, from its exact callees: min over DISTINCT profiled callees
// of floor(call_count / multiplicity). Returns +inf when no exact profiled
// callee bounds the block (fail-open, counted). min is commutative, so map
// iteration order does not affect the result -> deterministic.
//
// NOT strictly sound: it assumes reaching an exact invoke implies one entry
// to the resolved callee, but a dex invoke can throw BEFORE the callee is
// entered (class-init failure / NoClassDefFoundError for invoke-static; a
// null receiver for invoke-direct/-super), so a block can execute more often
// than its callee's `call_count`. Treated as a heuristic cap: it may
// under-count such a block down to epsilon. `MethodProfiles::call_count` is a
// method-ENTRY count, not an attempted-callsite count, so no strictly-sound
// block bound is available.
double callsite_cap_for_interaction(
    const UnorderedMap<DexMethod*, uint32_t>& callee_mult,
    const std::string& interaction,
    const method_profiles::MethodProfiles& profiles,
    CapCounters* cc) {
  double u = std::numeric_limits<double>::infinity();
  bool have = false;
  for (const auto& [callee, mult] : UnorderedIterable(callee_mult)) {
    auto cstat = profiles.get_method_stat(interaction, callee);
    if (!cstat) {
      if (cc != nullptr) {
        cc->unprofiled_callees.fetch_add(1, std::memory_order_relaxed);
      }
      continue;
    }
    const double cc_val = cstat->call_count;
    if (!std::isfinite(cc_val) || cc_val < 0.0) {
      // A non-finite (NaN/inf) or negative call_count is invalid profile
      // data, not a usable bound: a negative `per` would clamp covered blocks
      // down to epsilon. (cc_val == 0 stays usable -- a callee that never ran
      // caps the block at 0, which floors to epsilon.)
      continue;
    }
    const double per = std::floor(cc_val / (double)mult);
    u = have ? std::min(u, per) : per;
    have = true;
  }
  return have ? u : std::numeric_limits<double>::infinity();
}

// Per-method result of the two-sweep capacity DP.
struct ReflowMethodStats {
  size_t blocks_capped{0}; // blocks in an SCC whose flow was routed down (cap
                           // bit)
  double sink_spill{0.0}; // flow no successor could absorb (metered, not
                          // placed)
};

// A block "exits" the method here (return/throw terminal), so
// its SCC can shed flow to the return sink -> escape=+inf in the capacity DP.
bool block_exits(const cfg::Block* b) {
  auto it = b->get_last_insn();
  if (it == b->end()) {
    return false;
  }
  const IROpcode op = it->insn->opcode();
  return opcode::is_a_return(op) || opcode::is_throw(op);
}

// Two-sweep capacity DP on the SCC condensation. Returns the
// per-block frequency: baseline forward solve rescaled per-SCC by how much flow
// the DP could route into that SCC given the callsite caps. The entry is PINNED
// to `anchor` (never truncated); a block's own value is never truncated by
// cap_eff (the clamp post-pass is the hard per-block backstop). Deterministic:
// SCCs come from the WTO in topological order; condensation successors are kept
// in stable first-encounter order.
UnorderedMap<const cfg::Block*, double> reflow_block_freq(
    cfg::ControlFlowGraph& cfg,
    size_t i,
    DexMethod* method,
    double anchor,
    loop_impl::LoopInfo& loops,
    const std::vector<cfg::Block*>& rpo,
    const UnorderedMap<const cfg::Block*, size_t>& rpo_index,
    cfg::Block* entry,
    const method_profiles::MethodProfiles& profiles,
    const std::string& interaction,
    float handler_cold_factor,
    float loop_iteration_cap,
    float default_backedge_prob,
    size_t* zero_outflow_sinks,
    size_t* irreducible,
    ReflowMethodStats* out) {
  constexpr double kInf = std::numeric_limits<double>::infinity();
  const auto edge_prob =
      compute_edge_prob(cfg, i, handler_cold_factor, zero_outflow_sinks);
  const auto baseline =
      forward_propagate(i, anchor, loops, rpo, rpo_index, entry, edge_prob,
                        loop_iteration_cap, default_backedge_prob, irreducible);

  // ---- SCC condensation via WTO (component order == topological order) ----
  // Cycles collapse into the standard SCC condensation DAG (Tarjan,
  // "Depth-First Search and Linear Graph Algorithms," SIAM J. Comput. 1(2),
  // 1972, is the classic linear-time SCC construction). This does not run
  // Tarjan directly: it uses Sparta's Bourdoncle-style
  // `WeakTopologicalOrdering` (Bourdoncle, "Efficient Chaotic Iteration
  // Strategies with Widenings," FMPA 1993), whose nested components give both
  // the SCC grouping and a deterministic acyclic schedule for the two sweeps
  // below.
  UnorderedMap<const cfg::Block*, size_t> scc_id;
  std::vector<std::vector<const cfg::Block*>> scc_blocks;
  sparta::WeakTopologicalOrdering<cfg::Block*> wto(entry, [](cfg::Block* b) {
    std::vector<cfg::Block*> out;
    UnorderedSet<cfg::Block*> seen;
    for (auto* e : b->succs()) {
      auto* t = e->target();
      if (t != nullptr && t != b && seen.insert(t).second) {
        out.push_back(t);
      }
    }
    return out;
  });
  for (const auto& comp : wto) {
    const size_t id = scc_blocks.size();
    scc_blocks.emplace_back();
    std::function<void(const sparta::WtoComponent<cfg::Block*>&)> collect =
        [&](const sparta::WtoComponent<cfg::Block*>& w) {
          if (scc_id.emplace(w.head_node(), id).second) {
            scc_blocks[id].push_back(w.head_node());
          }
          if (w.is_scc()) {
            for (const auto& inner : w) {
              collect(inner);
            }
          }
        };
    collect(comp);
  }
  const size_t n_scc = scc_blocks.size();

  // ---- per-SCC caps, escape, condensation successors + baseline inflow ----
  std::vector<double> node_cap(n_scc, kInf);
  // Per-SCC min of (block cap / block baseline freq); scaled by baseline_inflow
  // into node_cap once inflow is known (see below). Kept separate because a raw
  // block-execution cap is in the wrong units to compare against SCC entry
  // flow.
  std::vector<double> inv_cap(n_scc, kInf);
  std::vector<bool> escape(n_scc, false);
  std::vector<std::vector<std::pair<size_t, double>>> cond_succ(n_scc);
  std::vector<double> baseline_inflow(n_scc, 0.0);
  UnorderedMap<DexMethod*, uint32_t> mult; // reused across blocks
  for (size_t s = 0; s < n_scc; ++s) {
    bool has_cond_succ = false;
    bool has_exit = false;
    for (const auto* b : scc_blocks[s]) {
      const double bf = (baseline.count(b) != 0u) ? baseline.at(b) : 0.0;
      exact_callee_multiplicity(b, method, /*cc=*/nullptr, mult);
      if (!mult.empty() && bf > 0.0) {
        const double c = callsite_cap_for_interaction(mult, interaction,
                                                      profiles, /*cc=*/nullptr);
        // Convert the per-block execution cap `c` into an SCC-ENTRY cap: block
        // b runs bf / baseline_inflow[s] times per entry to its SCC, so the
        // entry count is bounded by c * baseline_inflow[s] / bf -- not by `c`
        // directly (they are equal only for an acyclic singleton).
        // baseline_inflow[s] is not final until this loop ends, so accumulate
        // the unit-carrying min(c / bf) now and scale by baseline_inflow[s]
        // afterward. A zero-baseline block (bf == 0) never runs in baseline and
        // imposes no entry constraint, so it is skipped.
        inv_cap[s] = std::min(inv_cap[s], c / bf);
      }
      if (block_exits(b)) {
        has_exit = true;
      }
      for (auto* e : b->succs()) {
        auto* t = e->target();
        if (t == nullptr) {
          continue;
        }
        auto tit = scc_id.find(t);
        if (tit == scc_id.end() || tit->second == s) {
          continue; // intra-SCC (or unreachable) edge
        }
        has_cond_succ = true;
        auto epit = edge_prob.find(e);
        const double flow =
            bf * ((epit != edge_prob.end()) ? epit->second : 0.0);
        // accumulate into cond_succ[s] in stable first-encounter order
        auto& succs = cond_succ[s];
        bool found = false;
        for (auto& pr : succs) {
          if (pr.first == tit->second) {
            pr.second += flow;
            found = true;
            break;
          }
        }
        if (!found) {
          succs.emplace_back(tit->second, flow);
        }
        baseline_inflow[tit->second] += flow;
      }
    }
    // Escape (flow can leave the method here) if the SCC returns/throws OR is a
    // condensation sink. Over-estimating escape only loosens caps (the clamp
    // still backstops); under-estimating would wrongly zero a sink SCC.
    escape[s] = has_exit || !has_cond_succ;
  }
  const size_t entry_scc = scc_id.at(entry);
  baseline_inflow[entry_scc] = anchor; // entry inflow is the pinned anchor

  // Finalize node_cap in SCC-entry-flow units now that baseline_inflow is
  // known: node_cap[s] = min over capped blocks b of c(b) * baseline_inflow[s]
  // / baseline[b]. An SCC with no capped block (inv_cap == +inf) stays
  // uncapped; guarding on that also avoids 0 * +inf when an SCC has zero
  // baseline inflow.
  for (size_t s = 0; s < n_scc; ++s) {
    if (inv_cap[s] != kInf) {
      node_cap[s] = baseline_inflow[s] * inv_cap[s];
    }
  }

  // ---- reverse sweep: effective downstream capacity (UPPER BOUND) ----
  std::vector<double> cap_eff(n_scc, kInf);
  for (size_t s = n_scc; s-- > 0;) {
    double down = escape[s] ? kInf : 0.0;
    if (!escape[s]) {
      for (const auto& [t, flow] : cond_succ[s]) {
        down += cap_eff[t];
        if (down == kInf) {
          break;
        }
      }
    }
    cap_eff[s] = std::min(node_cap[s], down);
  }

  // ---- forward sweep: allocate inflow per SCC; entry pinned; route by prior
  //      capped at successor headroom; spill the remainder ----
  std::vector<double> alloc_inflow(n_scc, 0.0);
  std::vector<double> sfac(n_scc, 0.0);
  alloc_inflow[entry_scc] = anchor;
  double sink_spill = 0.0;
  for (size_t s = 0; s < n_scc; ++s) {
    const double bin = baseline_inflow[s];
    // bin == 0 means no condensation predecessor routed baseline flow into this
    // SCC, so every block in it has baseline bf == 0 (and alloc_inflow[s] == 0
    // too) -- the write below is bf * sfac == 0 regardless. The guard only
    // avoids 0/0; it drops no flow. The entry SCC always has bin == anchor > 0.
    sfac[s] = (bin > 0.0) ? (alloc_inflow[s] / bin) : 0.0;
    double want_total = 0.0;
    for (const auto& [t, flow] : cond_succ[s]) {
      want_total += flow * sfac[s];
    }
    // pass 1: prior split, each successor capped at remaining headroom.
    double routed = 0.0;
    for (const auto& [t, flow] : cond_succ[s]) {
      const double want = flow * sfac[s];
      const double headroom = std::max(0.0, cap_eff[t] - alloc_inflow[t]);
      const double give = std::min(want, headroom);
      alloc_inflow[t] += give;
      routed += give;
    }
    // pass 2: spill leftover to successors that still have headroom, weighted
    // by
    //         remaining headroom (route toward genuine absorbers). Any block
    //         with unbounded (escape) downstream soaks the rest.
    double leftover = want_total - routed;
    if (leftover > 1e-9) {
      double rem_finite = 0.0;
      bool has_inf = false;
      for (const auto& [t, flow] : cond_succ[s]) {
        if (!std::isfinite(cap_eff[t])) {
          has_inf = true;
        } else {
          rem_finite += std::max(0.0, cap_eff[t] - alloc_inflow[t]);
        }
      }
      if (has_inf) {
        for (const auto& [t, flow] : cond_succ[s]) {
          if (!std::isfinite(cap_eff[t])) {
            alloc_inflow[t] += leftover;
            leftover = 0.0;
            break;
          }
        }
      } else if (rem_finite > 0.0) {
        // Split the leftover across finite headroom in proportion to each
        // successor's headroom. Use the ORIGINAL leftover as the numerator, not
        // the running one: decrementing `leftover` while keeping the fixed
        // `rem_finite` denominator would under-allocate later successors and
        // falsely spill flow that the combined headroom could absorb. `give` is
        // still clamped to `h`, and rem_finite > 0 rules out the divide.
        const double orig_leftover = leftover;
        for (const auto& [t, flow] : cond_succ[s]) {
          const double h = std::max(0.0, cap_eff[t] - alloc_inflow[t]);
          if (h <= 0.0) {
            continue;
          }
          const double give = std::min(h, orig_leftover * (h / rem_finite));
          alloc_inflow[t] += give;
          leftover -= give;
        }
      }
    }
    if (leftover > 1e-9) {
      sink_spill += leftover;
    }
  }

  // ---- write per-block freq = baseline * per-SCC rescale ----
  UnorderedMap<const cfg::Block*, double> out_freq;
  out_freq.reserve(baseline.size());
  size_t blocks_capped = 0;
  for (size_t s = 0; s < n_scc; ++s) {
    if (sfac[s] < 1.0 - 1e-9) {
      blocks_capped += scc_blocks[s].size();
    }
    for (const auto* b : scc_blocks[s]) {
      const double bf = (baseline.count(b) != 0u) ? baseline.at(b) : 0.0;
      out_freq[b] = bf * sfac[s];
    }
  }
  out->blocks_capped += blocks_capped;
  out->sink_spill += sink_spill;
  return out_freq;
}

} // namespace

std::string SyntheticBlockCountsPass::get_config_doc() {
  return trim(R"(
Simulation/testing pass that rewrites boolean-ish SourceBlock `val` magnitudes
into flow-consistent synthetic per-block counts via a per-method,
entry-anchored Wu-Larus reverse-post-order solve (entry anchored to the
method's `call_count`, branch probabilities from coverage + loop/exception
heuristics). It pins the coverage support -- it never turns a 0 into >0 or a
covered block into 0 -- and never touches `appear100`, so enabling it is
No-Functional-Change for every existing optimization decision (all of which
test only `val > 0`). It is a pure SourceBlock annotator -- it never edits the
CFG (reducibility is decided by a single-entry loop test, so no dominator solve
and no dead-block removal are needed), so it is safe over `no_optimizations`
classes and leaves unprofiled methods byte-identical. It is gated off via a
`.disabled(True)` pass-list entry.
  )");
}

void SyntheticBlockCountsPass::bind_config() {
  bind("handler_cold_factor",
       m_handler_cold_factor,
       m_handler_cold_factor,
       "Probability mass placed on EDGE_THROW edges.");
  bind("loop_iteration_cap",
       m_loop_iteration_cap,
       m_loop_iteration_cap,
       "Maximum geometric loop multiplier per loop level.");
  bind("default_backedge_prob",
       m_default_backedge_prob,
       m_default_backedge_prob,
       "Assumed back-edge probability when coverage doesn't pin it.");
  bind("epsilon",
       m_epsilon,
       m_epsilon,
       "Floor for a covered block whose solved frequency underflowed; keeps "
       "covered blocks strictly > 0.");
  bind("intermethod",
       m_intermethod,
       m_intermethod,
       "Enable the inter-method call-graph engine: profiled methods are "
       "pinned to their own call_count and unprofiled methods are heated by "
       "forward propagation of caller invoke-block frequencies over the call "
       "graph. When false, the per-method solve runs unchanged.");
  bind("intermethod_max_sweeps",
       m_intermethod_max_sweeps,
       m_intermethod_max_sweeps,
       "Max forward relaxation sweeps for the inter-method solve.");
  bind("intermethod_max_scale_factor",
       m_intermethod_max_scale_factor,
       m_intermethod_max_scale_factor,
       "Multiplier for the widening-to-hi cap on any forward-filled scale: the "
       "per-interaction ceiling is factor * max(usable call_count), bounding "
       "recursion/SCC cycles (then tightened by the step-4 backward callee "
       "bound).");
  bind("intermethod_converge_eps",
       m_intermethod_converge_eps,
       m_intermethod_converge_eps,
       "Relative convergence tolerance for the inter-method Gauss-Seidel "
       "solve.");

  // Validate config values HERE, never in the bind_config() body above:
  // bind_config() is also run for config reflection (doc generation), where the
  // fields still hold their defaults and an assert would spuriously abort. This
  // callback runs only when a real config is consumed, after every bind().
  after_configuration([this] {
    // `loop_iteration_cap` is an upper bound on a multiplier, so it must be
    // >= 1.0; below 1.0 it becomes the `hi` of `std::clamp(mult, 1.0, cap)`
    // with lo > hi in the loop-header solve, which is undefined behavior.
    always_assert_log(m_loop_iteration_cap >= 1.0f,
                      "loop_iteration_cap must be >= 1.0, got %f",
                      m_loop_iteration_cap);
    // The floor exists only to keep a covered block strictly positive, so the
    // bound is representability, not any consumer's threshold. See
    // source_blocks::kMinPositiveCount for why the old
    // "must dominate min_block_hits" sizing no longer applies.
    always_assert_log(m_epsilon >= source_blocks::kMinPositiveCount,
                      "epsilon (%f) must be at least the smallest normal float "
                      "to keep covered blocks strictly > 0",
                      m_epsilon);
    // `default_backedge_prob` is used as the fallback back-edge probability
    // p_back; outside [0, 1] it makes `1-p_back` a non-positive divisor (or
    // yields >1 flow). Validate up front rather than clamping silently.
    always_assert_log(m_default_backedge_prob >= 0.0f &&
                          m_default_backedge_prob <= 1.0f,
                      "default_backedge_prob (%f) must be in [0, 1]",
                      m_default_backedge_prob);
    // Handler weight scales exception-edge flow; a non-finite or negative
    // factor would poison every downstream count with NaN/negative flow.
    always_assert_log(std::isfinite(m_handler_cold_factor) &&
                          m_handler_cold_factor >= 0.0f,
                      "handler_cold_factor (%f) must be finite and >= 0",
                      m_handler_cold_factor);
  });
}

SyntheticBlockCountsPass::MethodResult SyntheticBlockCountsPass::process_method(
    DexMethod* method,
    cfg::ControlFlowGraph& cfg,
    const method_profiles::MethodProfiles& profiles,
    const std::vector<std::string>& inv_slot) {
  MethodResult res;
  res.methods_seen = 1;

  // Bind a const reference to select the read-only LoopInfo ctor; the
  // non-const ctor mutates the CFG by inserting preheaders.
  const cfg::ControlFlowGraph& ccfg = cfg;
  loop_impl::LoopInfo loops(ccfg);
  std::vector<cfg::Block*> rpo;
  UnorderedMap<const cfg::Block*, size_t> rpo_index;
  build_rpo(cfg, rpo, rpo_index);
  auto* entry = cfg.entry_block();

  {
    auto* eloop = loops.get_loop_for(entry);
    if (eloop != nullptr && eloop->get_header() == entry) {
      res.solve_fallback_entry_is_header++;
    }
  }

  // (method, interaction) sparsity: count covered vs uncovered
  // pairs (covered = >=1 val>0 block for that interaction). Uncovered pairs
  // write nothing (support pinned) and are the skippable set. One scan over all
  // interactions.
  {
    std::vector<bool> covered(inv_slot.size(), false);
    for (auto* b : cfg.blocks_view()) {
      source_blocks::foreach_source_block(b, [&](SourceBlock* sb) {
        for (size_t i = 0; i < inv_slot.size(); ++i) {
          auto v = sb->get_val(i);
          if (v && *v > 0.0f) {
            covered.at(i) = true;
          }
        }
      });
    }
    for (size_t i = 0; i < inv_slot.size(); ++i) {
      res.pairs_total++;
      if (covered.at(i)) {
        res.pairs_covered++;
      } else {
        res.pairs_uncovered++;
      }
    }
  }

  bool any_slot_used = false;
  uint64_t written_mask = 0; // interaction slots this method actually wrote

  for (size_t i = 0; i < inv_slot.size(); ++i) {
    auto stat = profiles.get_method_stat(inv_slot[i], method);
    if (!stat) {
      // No numeric seed for this interaction -- leave the boolean vals as-is.
      res.solve_fallback_no_profile++;
      continue;
    }
    const double call_count = stat->call_count;
    if (!std::isfinite(call_count) || call_count < 0.0) {
      // A non-finite (NaN/inf) or negative call_count is not a usable anchor --
      // treat it like no profile (leave the boolean vals as-is for this
      // interaction), rather than propagating NaN/inf into every block or
      // collapsing every covered block to epsilon from a garbage negative
      // anchor. (call_count == 0 is usable: it correctly floors to epsilon.)
      res.solve_fallback_no_profile++;
      continue;
    }
    any_slot_used = true;

    // Anchor the entry to `call_count`; because the solve is linear in the
    // anchor this is identical to scaling a unit-anchored shape by call_count.
    auto block_freq = solve_block_freq(cfg,
                                       i,
                                       /*entry_anchor=*/call_count,
                                       loops,
                                       rpo,
                                       rpo_index,
                                       entry,
                                       m_handler_cold_factor,
                                       m_loop_iteration_cap,
                                       m_default_backedge_prob,
                                       &res.zero_outflow_sinks,
                                       &res.solve_fallback_irreducible);

    // (4) Write magnitude only; the write guard is the sole enforcer of
    // support preservation.
    for (auto* b : cfg.blocks_view()) {
      auto freq_it = block_freq.find(b);
      if (freq_it == block_freq.end()) {
        // The block is unreachable from entry in the solve (this pass is a pure
        // annotator and does not prune unreachable blocks, so a
        // covered-but-unreachable block can exist). We have no frequency
        // estimate for it, so leave its existing
        // val untouched rather than flooring a genuine covered count to
        // epsilon.
        continue;
      }
      const double f = freq_it->second;
      source_blocks::foreach_source_block(b, [&](SourceBlock* sb) {
        sb->apply_at(i, [&](SourceBlock::Val& v) {
          if (!v || !(v->val > 0.0f)) {
            // preserve 0 / NaN; never resurrect the support. Written as
            // `!(val > 0)` rather than `val <= 0` so a NaN val (for which every
            // ordered compare is false) also takes this skip path.
            return;
          }
          float m = (float)f;
          if (m < m_epsilon) {
            m = m_epsilon; // keep covered blocks strictly > 0
            res.epsilon_clamped_blocks++;
          }
          // Only `val` is written, only for already-covered blocks (guarded
          // above), and only to a strictly-positive m >= epsilon -- so the
          // coverage support and appear100 are preserved by construction. A
          // post-write "did support change?" check here is vacuous (it can
          // never fire), so it is intentionally omitted.
          v->val = m;
          res.blocks_written++;
          written_mask |= (uint64_t{1} << i);
        });
      });
    }
  }

  if (written_mask != 0) {
    // Record what this producer path wrote so the callsite clamp only caps
    // these (method, interaction) slots, not the boolean vals of skipped ones.
    m_producer_written.update(method,
                              [written_mask](const DexMethod*, uint64_t& mask,
                                             bool) { mask |= written_mask; });
  }
  if (any_slot_used) {
    res.methods_with_usable_profile = 1;
  }
  return res;
}

size_t SyntheticBlockCountsPass::count_non_unit_covered_vals(
    const Scope& scope, size_t num_interactions) {
  return walk::parallel::methods<size_t>(scope, [&](DexMethod* m) -> size_t {
    auto* code = m->get_code();
    if (code == nullptr || !code->cfg_built()) {
      return 0;
    }
    size_t count = 0;
    for (auto* b : code->cfg().blocks()) {
      source_blocks::foreach_source_block(b, [&](SourceBlock* sb) {
        for (size_t i = 0; i < num_interactions; ++i) {
          const auto v = sb->get_val(i);
          if (v && *v > 0.0f && *v != 1.0f) {
            count++;
          }
        }
      });
    }
    return count;
  });
}

// Per interaction, count methods that ARE covered (>=1 SourceBlock val > 0) yet
// have NO usable call_count anchor -- no profile row, or a non-finite /
// negative call_count (a call_count of 0 counts as a usable anchor, per
// `usable_call_count`). This is the covered-but-unprofiled population the
// inter-method forward-fill exists to heat -- often produced by inlining a hot
// callee into a method with no profile of its own. Pure: no pass state, writes
// nothing; run_pass emits the values as metrics.
std::vector<int64_t> SyntheticBlockCountsPass::count_missing_hit_methods(
    const Scope& scope,
    const method_profiles::MethodProfiles& profiles,
    const std::vector<std::string>& inv_slot) {
  const size_t n = inv_slot.size();
  // Array (not vector) of atomics: std::vector<std::atomic<>> is ill-formed
  // (atomics are not movable). make_unique<T[]> value-initializes to 0.
  auto counts = std::make_unique<std::atomic<size_t>[]>(n);
  walk::parallel::methods(scope, [&](DexMethod* m) {
    auto* code = m->get_code();
    if (code == nullptr || !code->cfg_built()) {
      return;
    }
    auto& cfg = code->cfg();
    // A (method, interaction) is "covered" if any block's representative
    // SourceBlock has val > 0 for that interaction (the coverage notion the
    // solve uses). One scan over blocks fills every interaction.
    std::vector<bool> covered(n, false);
    for (auto* b : cfg.blocks()) {
      // Covered if ANY source block in the block ran for this interaction --
      // the same `foreach_source_block` predicate the write-back uses, so this
      // metric measures the exact population the solve writes to (a block may
      // carry several source blocks after inlining, not just a representative).
      source_blocks::foreach_source_block(b, [&](SourceBlock* sb) {
        for (size_t i = 0; i < n; ++i) {
          if (covered[i]) {
            continue;
          }
          const auto v = sb->get_val(i);
          if (v && *v > 0.0f) {
            covered[i] = true;
          }
        }
      });
    }
    for (size_t i = 0; i < n; ++i) {
      if (!covered[i]) {
        continue;
      }
      auto stat = profiles.get_method_stat(inv_slot[i], m);
      // Covered but no usable anchor: absent row, or a non-finite / negative
      // call_count. A call_count of exactly 0 IS usable (a genuinely cold but
      // profiled method, which the solve floors to epsilon), matching
      // `usable_call_count` -- so it is a real anchor, not a "missing hit".
      if (!stat || !std::isfinite(stat->call_count) || stat->call_count < 0.0) {
        counts[i].fetch_add(1, std::memory_order_relaxed);
      }
    }
  });
  std::vector<int64_t> out(n);
  for (size_t i = 0; i < n; ++i) {
    out[i] = (int64_t)counts[i].load(std::memory_order_relaxed);
  }
  return out;
}

void SyntheticBlockCountsPass::run_pass(DexStoresVector& stores,
                                        ConfigFiles& conf,
                                        PassManager& mgr) {
  const auto& profiles = conf.get_method_profiles();
  const auto& slot_map = g_redex->get_sb_interaction_indices();
  const size_t n = g_redex->num_sb_interaction_indices();
  std::vector<std::string> inv_slot(n);
  for (const auto& kv : UnorderedIterable(slot_map)) {
    always_assert(kv.second < n);
    inv_slot[kv.second] = kv.first;
  }

  // The callsite clamp gates on a per-method uint64_t bitmask of producer-
  // written interaction slots; cap the slot count at 64 and reset the map.
  always_assert(n <= 64);
  m_producer_written.clear();

  auto scope = build_class_scope(stores);

  // A counting profile already has measured per-block magnitudes, which the
  // solve below would replace with estimates.
  if (const size_t counted = count_non_unit_covered_vals(scope, n);
      counted > 0) {
    mgr.set_metric("skipped_profile_has_counts", (int64_t)counted);
    return;
  }

  // Per-phase wall-clock timers, emitted as `*_ms` metrics into the redex stats
  // (same shape as the inter-method engine's p1_ms/phase_b_ms/phase_c_ms). The
  // PassManager already records the pass's total runtime; these attribute it to
  // the producer solve and each callsite post-pass so the cost stays
  // observable.
  using clk = std::chrono::steady_clock;
  auto ms_since = [](clk::time_point t0) {
    return (int64_t)std::chrono::duration<double, std::milli>(clk::now() - t0)
        .count();
  };

  // Emitted before the producer branch so it lands on
  // BOTH the per-method and inter-method paths. Metric-only, NFC.
  {
    const auto missing_hit =
        count_missing_hit_methods(scope, profiles, inv_slot);
    int64_t total = 0;
    for (size_t i = 0; i < inv_slot.size(); ++i) {
      mgr.set_metric("missing_hit_methods_" + inv_slot[i], missing_hit[i]);
      total += missing_hit[i];
    }
    mgr.set_metric("missing_hit_methods_total", total);
  }

  // Producer step: fill per-block counts on ONE of the two paths. No early
  // return -- the post-passes below run over whichever output was produced.
  if (m_intermethod) {
    const auto t0 = clk::now();
    run_intermethod(stores, profiles, inv_slot, mgr);
    mgr.set_metric("intermethod_solve_ms", ms_since(t0));
  } else {
    const auto t0 = clk::now();
    auto res = walk::parallel::methods<MethodResult>(
        scope, [&](DexMethod* m) -> MethodResult {
          auto* code = m->get_code();
          if (code == nullptr || !code->cfg_built()) {
            return MethodResult{};
          }
          return process_method(m, code->cfg(), profiles, inv_slot);
        });

    mgr.set_metric("methods_seen", (int64_t)res.methods_seen);
    mgr.set_metric("methods_with_usable_profile",
                   (int64_t)res.methods_with_usable_profile);
    mgr.set_metric("blocks_written", (int64_t)res.blocks_written);
    mgr.set_metric("solve_fallback_no_profile",
                   (int64_t)res.solve_fallback_no_profile);
    mgr.set_metric("solve_fallback_irreducible",
                   (int64_t)res.solve_fallback_irreducible);
    mgr.set_metric("solve_fallback_entry_is_header",
                   (int64_t)res.solve_fallback_entry_is_header);
    mgr.set_metric("epsilon_clamped_blocks",
                   (int64_t)res.epsilon_clamped_blocks);
    mgr.set_metric("zero_outflow_sinks", (int64_t)res.zero_outflow_sinks);
    mgr.set_metric("pairs_total", (int64_t)res.pairs_total);
    mgr.set_metric("pairs_covered", (int64_t)res.pairs_covered);
    mgr.set_metric("pairs_uncovered", (int64_t)res.pairs_uncovered);
    mgr.set_metric("permethod_solve_ms", ms_since(t0));
  }

  // Tier-1 callsite reconciliation, as post-passes over whatever the producer
  // wrote (per-method OR inter-method). Re-flow ROUTES flow away from
  // over-capped blocks toward siblings with headroom (best-effort); the clamp
  // then TRUNCATES each covered block at the best-effort cap. Order matters:
  // reflow reads the un-clamped producer anchor, and the clamp must run LAST as
  // the hard per-block backstop for whatever reflow could only upper-bound.
  if (m_callsite_reflow) {
    const auto t0 = clk::now();
    reflow_post_pass(scope, profiles, inv_slot, mgr);
    mgr.set_metric("callsite_reflow_ms", ms_since(t0));
  }
  if (m_callsite_clamp) {
    const auto t0 = clk::now();
    clamp_post_pass(scope, profiles, inv_slot, mgr);
    mgr.set_metric("callsite_clamp_ms", ms_since(t0));
  }
}

// Tier-1 callsite-count clamp (post-pass over both producers): cap each covered
// block's synthesized `val` at the best-effort bound
// `callsite_cap_for_interaction`
// -- the min over the block's distinct exact profiled callees of
// floor(call_count / multiplicity). Only lowers already-covered blocks, never
// below epsilon (cap==0 -> epsilon, support pin wins). No re-solve: it reads
// and rewrites the vals the producer already wrote. Deterministic; per-method
// parallel with order-independent atomic counters.
SyntheticBlockCountsPass::ClampStats
SyntheticBlockCountsPass::clamp_post_pass_core(
    const Scope& scope,
    const method_profiles::MethodProfiles& profiles,
    const std::vector<std::string>& inv_slot) {
  const size_t n = inv_slot.size();
  std::atomic<size_t> clamp_vals_lowered{0};
  // Accumulate the removed magnitude in double: individual (old-new) drops are
  // often < 1.0 and would each truncate to 0 in an integer counter.
  std::atomic<double> clamp_val_removed_total{0.0};
  CapCounters cc;
  const float epsilon = m_epsilon;
  walk::parallel::methods(scope, [&](DexMethod* method) {
    auto* code = method->get_code();
    if (code == nullptr || !code->cfg_built()) {
      return;
    }
    auto& cfg = code->cfg();
    // Only clamp (method, interaction) slots the producer actually wrote; a
    // method/interaction the producer skipped keeps its original boolean vals.
    //
    // The mask is (method, interaction)-granular, NOT per block: it is set as
    // soon as the producer wrote ANY block of the slot. So a covered block the
    // producer deliberately left alone -- e.g. one unreachable from the entry
    // in `solve_block_freq`, which `process_method` skips rather than floor --
    // is still clamped if it shares a written slot. That is intentional: the
    // cap is a sound bound on how often the block can run (it is derived from
    // the block's own exact callees' call_counts), so it holds whether or not
    // the producer synthesized that block, and the epsilon floor below keeps
    // the coverage support intact either way.
    const uint64_t written_mask = m_producer_written.get(method, 0);
    if (written_mask == 0) {
      return;
    }
    UnorderedMap<DexMethod*, uint32_t> callee_mult; // reused across blocks
    for (auto* b : cfg.blocks()) {
      exact_callee_multiplicity(b, method, &cc, callee_mult);
      if (callee_mult.empty()) {
        continue;
      }
      for (size_t i = 0; i < n; ++i) {
        if (((written_mask >> i) & 1) == 0) {
          continue; // producer left this interaction boolean; don't clamp it
        }
        const double u = callsite_cap_for_interaction(callee_mult, inv_slot[i],
                                                      profiles, &cc);
        if (!std::isfinite(u)) {
          continue; // no exact profiled callee bounds this block -> no-op
        }
        const float cap = (float)u;
        source_blocks::foreach_source_block(b, [&](SourceBlock* sb) {
          sb->apply_at(i, [&](SourceBlock::Val& v) {
            // Only lower already-covered vals; never resurrect support, never
            // write below epsilon (cap==0 -> epsilon: support pin wins). A NaN
            // val takes the skip path (every ordered compare is false).
            if (!v || !(v->val > 0.0f)) {
              return;
            }
            const float capped = std::max(epsilon, std::min(v->val, cap));
            if (capped < v->val) {
              clamp_val_removed_total.fetch_add((double)(v->val - capped),
                                                std::memory_order_relaxed);
              clamp_vals_lowered.fetch_add(1, std::memory_order_relaxed);
              v->val = capped;
            }
          });
        });
      }
    }
  });
  ClampStats st;
  st.clamp_vals_lowered = clamp_vals_lowered.load();
  st.clamp_val_removed_total = clamp_val_removed_total.load();
  st.clamp_exact_invokes_seen = cc.exact_invokes_seen.load();
  st.clamp_unresolved_invokes = cc.unresolved_invokes.load();
  st.clamp_unprofiled_callees = cc.unprofiled_callees.load();
  st.clamp_throw_gated_invokes = cc.throw_gated_invokes.load();
  return st;
}

void SyntheticBlockCountsPass::clamp_post_pass(
    const Scope& scope,
    const method_profiles::MethodProfiles& profiles,
    const std::vector<std::string>& inv_slot,
    PassManager& mgr) {
  const ClampStats st = clamp_post_pass_core(scope, profiles, inv_slot);
  mgr.set_metric("clamp_vals_lowered", (int64_t)st.clamp_vals_lowered);
  mgr.set_metric("clamp_val_removed_total",
                 (int64_t)std::llround(st.clamp_val_removed_total));
  mgr.set_metric("clamp_exact_invokes_seen",
                 (int64_t)st.clamp_exact_invokes_seen);
  mgr.set_metric("clamp_unresolved_invokes",
                 (int64_t)st.clamp_unresolved_invokes);
  mgr.set_metric("clamp_unprofiled_callees",
                 (int64_t)st.clamp_unprofiled_callees);
  mgr.set_metric("clamp_throw_gated_invokes",
                 (int64_t)st.clamp_throw_gated_invokes);
}

// Scope-scoped core (no PassManager), directly drivable from
// unit tests. Per method, per interaction: anchor on the WRITTEN entry count,
// run the two-sweep capacity DP, and overwrite covered blocks with the routed
// per-block frequency (support pin + epsilon floor; non-positive/NaN rejected).
// The clamp still runs after this as the hard per-block backstop.
SyntheticBlockCountsPass::ReflowStats
SyntheticBlockCountsPass::reflow_post_pass_core(
    const Scope& scope,
    const method_profiles::MethodProfiles& profiles,
    const std::vector<std::string>& inv_slot) {
  const size_t n = inv_slot.size();
  const float epsilon = m_epsilon;
  const float handler_cold_factor = m_handler_cold_factor;
  const float loop_iteration_cap = m_loop_iteration_cap;
  const float default_backedge_prob = m_default_backedge_prob;
  return walk::parallel::methods<ReflowStats>(
      scope, [&](DexMethod* method) -> ReflowStats {
        auto* code = method->get_code();
        if (code == nullptr || !code->cfg_built()) {
          return ReflowStats{};
        }
        // Gate on the producer-written slots exactly as the clamp post-pass
        // does. Without this, a slot the producer never synthesized still has
        // boolean coverage on its entry block, and `*av > 0` below would accept
        // that 1.0 as if it were a real execution count -- re-flowing, and
        // overwriting, the very coverage values this pass promises to leave
        // alone on unsynthesized slots.
        const uint64_t written_mask = m_producer_written.get(method, 0);
        if (written_mask == 0) {
          return ReflowStats{};
        }
        auto& cfg = code->cfg();
        // Same solve scaffolding as process_method.
        const cfg::ControlFlowGraph& ccfg = cfg;
        loop_impl::LoopInfo loops(ccfg);
        std::vector<cfg::Block*> rpo;
        UnorderedMap<const cfg::Block*, size_t> rpo_index;
        build_rpo(cfg, rpo, rpo_index);
        auto* entry = cfg.entry_block();

        ReflowStats st;
        bool spilled = false;
        size_t zero_outflow_sinks =
            0; // discarded (already counted by producer)
        size_t irreducible = 0; // discarded (already counted by producer)
        for (size_t i = 0; i < n; ++i) {
          if (((written_mask >> i) & 1) == 0) {
            continue; // producer left this interaction boolean; don't reflow it
          }
          // Anchor on the WRITTEN entry count (recovers the producer's
          // scale_M).
          auto* esb = source_blocks::get_first_source_block(entry);
          const auto av = (esb != nullptr) ? esb->get_val(i) : std::nullopt;
          // DeMorgan-expanded; keep `!(x > 0)` (NOT `x <= 0`) so a NaN anchor
          // is also rejected (NaN <= 0 is false, which would let NaN through).
          if (!av || !(*av > 0.0f)) {
            continue; // entry uncovered / no anchor for this interaction
          }
          const double anchor = *av;
          ReflowMethodStats ms;
          const auto freq = reflow_block_freq(
              cfg, i, method, anchor, loops, rpo, rpo_index, entry, profiles,
              inv_slot[i], handler_cold_factor, loop_iteration_cap,
              default_backedge_prob, &zero_outflow_sinks, &irreducible, &ms);
          for (auto* b : cfg.blocks()) {
            auto fit = freq.find(b);
            if (fit == freq.end()) {
              continue;
            }
            const double f = fit->second;
            source_blocks::foreach_source_block(b, [&](SourceBlock* sb) {
              sb->apply_at(i, [&](SourceBlock::Val& v) {
                // Support pin: only rewrite already-covered blocks. Reject a
                // non-positive/NaN routed value (keep the producer's value).
                if (!v || !(v->val > 0.0f)) {
                  return;
                }
                if (!(f > 0.0)) {
                  return;
                }
                v->val = std::max(epsilon, (float)f);
              });
            });
          }
          st.reflow_blocks_capped += ms.blocks_capped;
          if (ms.sink_spill > 0.0) {
            st.reflow_sink_spill_total += ms.sink_spill;
            spilled = true;
          }
        }
        if (spilled) {
          st.reflow_methods_spilled = 1;
        }
        return st;
      });
}

void SyntheticBlockCountsPass::reflow_post_pass(
    const Scope& scope,
    const method_profiles::MethodProfiles& profiles,
    const std::vector<std::string>& inv_slot,
    PassManager& mgr) {
  const ReflowStats st = reflow_post_pass_core(scope, profiles, inv_slot);
  mgr.set_metric("reflow_blocks_capped", (int64_t)st.reflow_blocks_capped);
  mgr.set_metric("reflow_sink_spill_total",
                 (int64_t)std::floor(st.reflow_sink_spill_total));
  mgr.set_metric("reflow_methods_spilled", (int64_t)st.reflow_methods_spilled);
}

void SyntheticBlockCountsPass::run_intermethod(
    DexStoresVector& stores,
    const method_profiles::MethodProfiles& profiles,
    const std::vector<std::string>& inv_slot,
    PassManager& mgr) {
  auto scope = build_class_scope(stores);
  auto st = run_intermethod_core(scope, profiles, inv_slot);
  mgr.set_metric("intermethod_enabled", 1);
  mgr.set_metric("pairs_pinned", (int64_t)st.pairs_pinned);
  mgr.set_metric("pairs_forward_filled", (int64_t)st.pairs_forward_filled);
  mgr.set_metric("pairs_skipped_zero_scale", (int64_t)st.pairs_skipped);
  mgr.set_metric("intermethod_blocks_written", (int64_t)st.blocks_written);
  mgr.set_metric("intermethod_forward_blocks_written",
                 (int64_t)st.forward_blocks_written);
  mgr.set_metric("pairs_hit_ceiling", (int64_t)st.pairs_hit_ceiling);
  mgr.set_metric("methods_not_in_graph", (int64_t)st.methods_not_in_graph);
  mgr.set_metric("intermethod_pairs_total", (int64_t)st.pairs_total);
  mgr.set_metric("intermethod_pairs_covered", (int64_t)st.pairs_covered);
  mgr.set_metric("intermethod_pairs_uncovered", (int64_t)st.pairs_uncovered);
  mgr.set_metric("intermethod_shape_solves", (int64_t)st.shape_solves);
  mgr.set_metric("intermethod_shape_cache_misses",
                 (int64_t)st.shape_cache_misses);
  mgr.set_metric("intermethod_shape_cache_entries",
                 (int64_t)st.shape_cache_entries);
  mgr.set_metric("intermethod_relevance_set_size",
                 (int64_t)st.relevance_set_size);
  mgr.set_metric("intermethod_zero_outflow_sinks",
                 (int64_t)st.zero_outflow_sinks);
  mgr.set_metric("intermethod_irreducible", (int64_t)st.irreducible);
  mgr.set_metric("intermethod_sweeps_total", (int64_t)st.sweeps_total);
  mgr.set_metric("intermethod_sweeps_max", (int64_t)st.sweeps_max);
  mgr.set_metric("intermethod_interactions_hit_cap",
                 (int64_t)st.interactions_hit_cap);
  mgr.set_metric("intermethod_methods_unconverged",
                 (int64_t)st.methods_unconverged);
  // Worst final-sweep relative change, in parts-per-million (converge_eps is
  // 1e-4 == 100 ppm): ~100 means barely-unconverged drift, a large value means
  // a cycle is genuinely oscillating.
  mgr.set_metric("intermethod_final_rel_max_ppm",
                 (int64_t)(st.final_rel_max * 1e6));
  mgr.set_metric("intermethod_p1_ms", (int64_t)st.p1_ms);
  mgr.set_metric("intermethod_phase_b_ms", (int64_t)st.phase_b_ms);
  mgr.set_metric("intermethod_phase_c_ms", (int64_t)st.phase_c_ms);
  mgr.set_metric("intermethod_forward_methods_mutated",
                 (int64_t)st.forward_methods_mutated);
  // Name-carrying metrics: the biggest forward-mutated methods, keyed by rank +
  // deobfuscated signature, value = dex code units. (The metric key is abused
  // to communicate the method name, as SourceBlocksViolations does for
  // top_changes.)
  for (size_t i = 0; i < st.top_forward_mutated.size(); ++i) {
    const auto& [m, sz] = st.top_forward_mutated[i];
    mgr.set_metric("intermethod_top_forward_mutated." + std::to_string(i) +
                       "." + show_deobfuscated(m),
                   (int64_t)sz);
  }
}

// Deterministic solve order: call-graph BFS (callers before callees) so the
// acyclic majority settles in ~one sweep. `visit_by_levels` is non-recursive
// (stack-safe at whole-app scale, unlike a recursive WTO build) and
// deterministic (FIFO queue over already-sorted callees()). Methods with a
// built CFG but unreachable from the call-graph entry are appended in stable id
// order. `id_of` maps method -> dense id; `nm` is the id count.
static std::vector<size_t> compute_sweep_order(
    const call_graph::Graph& cg,
    const UnorderedMap<const DexMethod*, size_t>& id_of,
    size_t nm) {
  std::vector<size_t> sweep_order;
  sweep_order.reserve(nm);
  std::vector<bool> in_order(nm, false); // scratch: dedups the level walk
  cg.visit_by_levels([&](const call_graph::Node* n) {
    const DexMethod* cm = n->method();
    if (cm == nullptr) {
      return; // ghost entry/exit
    }
    auto it = id_of.find(cm);
    if (it != id_of.end() && !in_order[it->second]) {
      in_order[it->second] = true;
      sweep_order.push_back(it->second);
    }
  });
  for (size_t idx = 0; idx < nm; ++idx) {
    if (!in_order[idx]) {
      sweep_order.push_back(idx);
    }
  }
  return sweep_order;
}

// Dense, deterministic method ids over all methods with a built CFG, ordered by
// a stable key (never pointer identity). Fills `methods` (id -> method) and
// `id_of` (method -> id).
static void build_method_ids(const Scope& scope,
                             std::vector<DexMethod*>& methods,
                             UnorderedMap<const DexMethod*, size_t>& id_of) {
  walk::code(scope, [&](DexMethod* m, IRCode& code) {
    if (code.cfg_built()) {
      methods.push_back(m);
    }
  });
  std::sort(methods.begin(), methods.end(), compare_dexmethods);
  id_of.reserve(methods.size());
  for (size_t idx = 0; idx < methods.size(); ++idx) {
    id_of[methods[idx]] = idx;
  }
}

// ntargets(insn) = number of resolved call-graph targets for each invoke on a
// cg edge. Call-graph-structural (interaction-independent), so it is resolved
// once and reused across interactions and sweeps.
static UnorderedMap<const IRInstruction*, size_t> compute_invoke_target_counts(
    const call_graph::Graph& cg) {
  UnorderedMap<const IRInstruction*, size_t> ntargets_by_insn;
  cg.visit_by_levels([&](const call_graph::Node* n) {
    for (const auto* e : n->callees()) {
      auto* insn = e->invoke_insn();
      if (insn != nullptr && ntargets_by_insn.count(insn) == 0u) {
        ntargets_by_insn.emplace(
            insn, call_graph::resolve_callees_in_graph(cg, insn).size());
      }
    }
  });
  return ntargets_by_insn;
}

// A profiled call_count usable as an anchor or bound: present, finite, and
// non-negative. A NaN/inf/negative row is invalid profile data (it would seed
// NaN/inf or a negative scale into the flow), so it reads as "no usable count".
// (call_count == 0 is usable: a genuinely cold anchor.)
static std::optional<double> usable_call_count(
    const method_profiles::MethodProfiles& profiles,
    const std::string& interaction,
    const DexMethod* m) {
  auto stat = profiles.get_method_stat(interaction, m);
  if (!stat || !std::isfinite(stat->call_count) || stat->call_count < 0.0) {
    return std::nullopt;
  }
  return stat->call_count;
}

// Backward upper bound (Phase 1.5): an exact call C->T fires at most
// call_count(T) times, so scale_C <= call_count(T) / k(C->T) for every exact
// out-edge to a profiled callee T -- a SOUND cap a forward over-estimate can
// never legitimately exceed. Defaults to `max_scale` (the widening safety net),
// refined downward by exact-callee bounds; keeps cycles bounded. Only relevant,
// non-pinned methods get a meaningful bound.
static std::vector<double> compute_hi_scale(
    const std::vector<DexMethod*>& methods,
    const std::vector<bool>& pinned,
    const std::vector<bool>& relevant,
    const call_graph::Graph& cg,
    const method_profiles::MethodProfiles& profiles,
    const std::string& interaction,
    const UnorderedMap<const IRInstruction*, size_t>& ntargets_by_insn,
    const InsertOnlyConcurrentMap<const IRInstruction*, double>& k_by_insn,
    double max_scale) {
  const size_t nm = methods.size();
  std::vector<double> hi_scale(nm, max_scale);
  for (size_t idx = 0; idx < nm; ++idx) {
    if (pinned[idx] || !relevant[idx]) {
      continue; // non-relevant scale stays 0 -> hi_scale[idx] unused
    }
    DexMethod* m = methods[idx];
    if (!cg.has_node(m)) {
      continue;
    }
    double hi = max_scale;
    for (const auto* e : cg.node(m)->callees()) {
      const DexMethod* t = e->callee()->method();
      auto* insn = e->invoke_insn();
      if (t == nullptr || insn == nullptr) {
        continue; // ghost exit edge
      }
      auto tcc = usable_call_count(profiles, interaction, t);
      if (!tcc) {
        continue; // only a finite, non-negative profiled callee yields a sound
                  // backward bound (see usable_call_count)
      }
      // Sound only for exact (single-target) invokes; a true-virtual invoke's
      // bound needs the sum over ALL its targets' counts (deferred), so skip.
      auto ntit = ntargets_by_insn.find(insn);
      if (ntit == ntargets_by_insn.end() || ntit->second != 1) {
        continue;
      }
      const double* kp = k_by_insn.get(insn);
      const double k = (kp != nullptr) ? *kp : 0.0;
      if (k > 0.0) {
        hi = std::min(hi, *tcc / k);
      }
    }
    hi_scale[idx] = hi;
  }
  return hi_scale;
}

// Rank forward-mutated methods by dex size (desc), stable tie-break by method
// key for determinism; keep at most `top_n` for name-carrying metrics.
static std::vector<std::pair<const DexMethod*, uint32_t>>
rank_top_forward_mutated(
    const InsertOnlyConcurrentMap<const DexMethod*, uint32_t>&
        forward_mutated_sizes,
    size_t top_n) {
  auto forward_mutated =
      unordered_to_ordered(forward_mutated_sizes,
                           [](const std::pair<const DexMethod*, uint32_t>& a,
                              const std::pair<const DexMethod*, uint32_t>& b) {
                             if (a.second != b.second) {
                               return a.second > b.second;
                             }
                             return compare_dexmethods(a.first, b.first);
                           });
  if (forward_mutated.size() > top_n) {
    forward_mutated.resize(top_n);
  }
  return forward_mutated;
}

// Pins + RelevanceSet for one interaction. A method WITH a usable profiled
// call_count is PINNED: seeded to its own count and treated as a pure source.
// RelevanceSet = pinned UNION their forward-callee closure over the call graph
// -- the only methods PASS B can give scale > 0, so PASS 0a can skip the rest.
// Fills scale/pinned/relevant (assumed sized to nm, zero/false-initialized).
static void compute_pins_and_relevance(
    const std::vector<DexMethod*>& methods,
    const UnorderedMap<const DexMethod*, size_t>& id_of,
    const call_graph::Graph& cg,
    const method_profiles::MethodProfiles& profiles,
    const std::string& interaction,
    std::vector<double>& scale,
    std::vector<bool>& pinned,
    std::vector<bool>& relevant) {
  const size_t nm = methods.size();
  redex_assert(scale.size() == nm && pinned.size() == nm &&
               relevant.size() == nm);
  for (size_t idx = 0; idx < nm; ++idx) {
    if (auto cc = usable_call_count(profiles, interaction, methods[idx])) {
      scale[idx] = *cc;
      pinned[idx] = true;
    }
  }
  std::vector<size_t> stk;
  for (size_t idx = 0; idx < nm; ++idx) {
    if (pinned[idx]) {
      relevant.at(idx) = true;
      stk.push_back(idx);
    }
  }
  while (!stk.empty()) {
    const size_t idx = stk.back();
    stk.pop_back();
    DexMethod* m = methods[idx];
    if (!cg.has_node(m)) {
      continue;
    }
    for (const auto* e : cg.node(m)->callees()) {
      const DexMethod* t = e->callee()->method();
      if (t == nullptr) {
        continue;
      }
      auto it = id_of.find(t);
      if (it != id_of.end() && !relevant.at(it->second)) {
        relevant.at(it->second) = true;
        stk.push_back(it->second);
      }
    }
  }
}

SyntheticBlockCountsPass::InterStats
SyntheticBlockCountsPass::run_intermethod_core(
    const Scope& scope,
    const method_profiles::MethodProfiles& profiles,
    const std::vector<std::string>& inv_slot) {
  auto mog = method_override_graph::build_graph(scope);
  // Multiple-callee graph: exact single edges for static/direct/super/
  // non-true-virtual, plus base+overrider edges for true virtuals. Megamorphic
  // sites (> kBigOverrideThreshold overriders) get NO fan-out edges, so they
  // contribute nothing -> they behave as the metered sink.
  constexpr uint32_t kBigOverrideThreshold = 5;
  auto cg =
      call_graph::multiple_callee_graph(*mog, scope, kBigOverrideThreshold);

  std::vector<DexMethod*> methods;
  UnorderedMap<const DexMethod*, size_t> id_of;
  build_method_ids(scope, methods, id_of);
  const size_t nm = methods.size();

  const std::vector<size_t> sweep_order = compute_sweep_order(cg, id_of, nm);

  const float hcf = m_handler_cold_factor, lic = m_loop_iteration_cap,
              dbp = m_default_backedge_prob;
  const float epsilon = m_epsilon;
  const double max_scale_factor = m_intermethod_max_scale_factor;
  const double converge_eps = m_intermethod_converge_eps;

  std::atomic<size_t> pairs_pinned{0}, pairs_forward_filled{0},
      pairs_skipped{0}, blocks_written{0}, pairs_hit_ceiling{0},
      forward_blocks_written{0}; // blocks written to forward-filled
                                 // (unprofiled) methods == the delta over the
                                 // per-method path
  // distinct forward-filled methods actually mutated (>=1 block written),
  // deduped across interactions, paired with dex size so the biggest few can be
  // emitted as name-carrying metrics. Recorded in PASS C (a per-method event,
  // not per-block) and ranked single-threaded afterward. The dex size is
  // computed by the first-insert `creator` OUTSIDE the map's slot lock (and
  // only once per method), so the O(n) `estimate_code_units()` never runs under
  // a lock.
  InsertOnlyConcurrentMap<const DexMethod*, uint32_t> forward_mutated_sizes;
  // (method, interaction) sparsity counters.
  std::atomic<size_t> im_pairs_total{0}, im_pairs_covered{0};
  // engine-cost + parity counters.
  std::atomic<size_t> im_shape_solves{0}, im_shape_cache_misses{0},
      im_zero_outflow{0}, im_irreducible{0};
  size_t im_relevance_set_size = 0, im_shape_cache_entries = 0,
         im_sweeps_total = 0, im_interactions_hit_cap = 0,
         im_methods_unconverged = 0;
  uint32_t im_sweeps_max = 0;
  double im_final_rel_max = 0.0; // worst final-sweep relative change, any slot
  double p1_ms = 0.0, phaseB_ms = 0.0, phaseC_ms = 0.0;
  using clk = std::chrono::steady_clock;
  auto ms_since = [](clk::time_point t0) {
    return std::chrono::duration<double, std::milli>(clk::now() - t0).count();
  };

  const UnorderedMap<const IRInstruction*, size_t> ntargets_by_insn =
      compute_invoke_target_counts(cg);

  // Parity check: profiled-but-call-graph-unreachable methods are still pinned
  // + instantiated over the full method list (NFC); they just get no
  // relaxation.
  size_t methods_not_in_graph = 0;
  for (size_t idx = 0; idx < nm; ++idx) {
    if (!cg.has_node(methods[idx])) {
      methods_not_in_graph++;
    }
  }

  // Interaction-outer loop. PASS 0a (shape) and PASS C (write) are parallel
  // over methods; PASS B (cross-method scale propagation) is a single
  // sequential call-graph sweep. Each interaction touches only its own
  // SourceBlock slot, so the interactions are independent.
  for (size_t i = 0; i < inv_slot.size(); ++i) {
    const std::string& interaction = inv_slot[i];

    // Pins + RelevanceSet, computed BEFORE the solve so PASS 0a can skip every
    // method that can never receive scale. See compute_pins_and_relevance.
    std::vector<double> scale(nm, 0.0);
    std::vector<bool> pinned(nm, false);
    std::vector<bool> relevant(nm, false);
    compute_pins_and_relevance(methods, id_of, cg, profiles, interaction, scale,
                               pinned, relevant);
    // Data-derived recursion-widening ceiling for this interaction: pins hold
    // the usable call_count (others 0), so this is factor * max(call_count).
    // All-cold (max 0) is benign -- inflow is 0, so every non-pinned scale
    // stays 0; step-4 (compute_hi_scale) then tightens this per method.
    // `scale` is sized by `nm`, so an empty method list would make
    // `max_element` return `end()`; 0 is the same benign all-cold ceiling.
    const double max_scale =
        scale.empty()
            ? 0.0
            : max_scale_factor * *std::max_element(scale.begin(), scale.end());
    std::vector<bool> hit_ceiling(nm, false); // value limited by max_scale
    for (size_t idx = 0; idx < nm; ++idx) {
      im_relevance_set_size += relevant[idx] ? 1 : 0;
    }

    // PASS 0a: per-method shape (unit anchor); record k = shape[block(invoke)]
    // for every invoke. The cheap coverage scan runs for all methods (metric +
    // PASS C cache-miss canary); the expensive geometry+Wu-Larus solve runs
    // ONLY for RelevanceSet members, whose covered shapes are cached so PASS C
    // reads them instead of re-solving (kills the 0a/C double-solve).
    // Per-method independent -> parallel.
    InsertOnlyConcurrentMap<const IRInstruction*, double> k_by_insn;
    InsertOnlyConcurrentMap<const DexMethod*,
                            UnorderedMap<const cfg::Block*, double>>
        shape_cache;
    InsertOnlyConcurrentSet<const DexMethod*> covered_methods;
    auto t_p1 = clk::now();
    walk::parallel::methods(scope, [&](DexMethod* m) {
      auto* code = m->get_code();
      if (code == nullptr || !code->cfg_built()) {
        return;
      }
      auto& cfg = code->cfg();
      // Annotation-only: never mutate the CFG (this is why the pass is safe
      // over `no_optimizations` and leaves bytecode byte-identical). The shape
      // solve visits only reachable blocks (RPO from entry) and PASS C skips
      // any block absent from the shape, so unreachable blocks need no removal.
      // Cached Block* keys stay valid because the CFG is not rebuilt before
      // PASS C.
      bool covered_i = false;
      for (auto* b : cfg.blocks()) {
        source_blocks::foreach_source_block(b, [&](SourceBlock* sb) {
          auto v = sb->get_val(i);
          if (v && *v > 0.0f) {
            covered_i = true;
          }
        });
        if (covered_i) {
          break;
        }
      }
      im_pairs_total.fetch_add(1, std::memory_order_relaxed);
      if (covered_i) {
        im_pairs_covered.fetch_add(1, std::memory_order_relaxed);
        covered_methods.insert(m);
      }
      auto iit = id_of.find(m);
      if (iit == id_of.end() || !relevant[iit->second]) {
        return; // scale stays 0 -> no k contribution, write-skipped. Byte-safe.
      }
      const cfg::ControlFlowGraph& ccfg = cfg;
      loop_impl::LoopInfo loops(ccfg);
      std::vector<cfg::Block*> rpo;
      UnorderedMap<const cfg::Block*, size_t> rpo_index;
      build_rpo(cfg, rpo, rpo_index);
      auto* entry = cfg.entry_block();
      size_t z = 0, ir = 0;
      auto shape = solve_block_freq(cfg, i, /*entry_anchor=*/1.0, loops, rpo,
                                    rpo_index, entry, hcf, lic, dbp, &z, &ir);
      im_shape_solves.fetch_add(1, std::memory_order_relaxed);
      im_zero_outflow.fetch_add(z, std::memory_order_relaxed);
      im_irreducible.fetch_add(ir, std::memory_order_relaxed);
      for (auto* b : cfg.blocks()) {
        const double bf = (shape.count(b) != 0u) ? shape[b] : 0.0;
        for (const auto& mie : *b) {
          if (mie.type == MFLOW_OPCODE &&
              opcode::is_a_method_invoke(mie.insn->opcode())) {
            k_by_insn.emplace(mie.insn, bf);
          }
        }
      }
      if (covered_i) {
        shape_cache.emplace(m, std::move(shape));
      }
    });
    p1_ms += ms_since(t_p1);
    im_shape_cache_entries =
        std::max(im_shape_cache_entries, shape_cache.size());

    // Backward upper bound (Phase 1.5) -- see compute_hi_scale. Timed together
    // with the forward sweep below as phase B.
    auto t_b = clk::now();
    const std::vector<double> hi_scale =
        compute_hi_scale(methods, pinned, relevant, cg, profiles, interaction,
                         ntargets_by_insn, k_by_insn, max_scale);

    // Worklist over the BFS `sweep_order`. Sweep 0 seeds every relevant
    // non-pinned method, so the acyclic majority settles in that one caller-
    // before-callee pass; afterwards a method is re-evaluated only when one of
    // its callers actually moved (by more than converge_eps), which it signals
    // by marking its callees dirty for the next sweep. Same fixpoint as a full
    // Gauss-Seidel sweep, but sweeps past the first touch only the shrinking
    // non-converged frontier (recursion cycles) instead of all ~N methods --
    // this is what keeps the inter-method solve off an O(sweeps · N) floor.
    uint32_t sweeps_used = 0;
    bool converged = false;
    double last_max_rel = 0.0;
    size_t last_changed = 0;
    // Worklist over the same BFS `sweep_order`. Sweep 0 seeds every relevant
    // non-pinned method, so the acyclic majority settles in that one caller-
    // before-callee pass; afterwards a method is re-evaluated only when one of
    // its callers actually moved (by more than converge_eps), which it signals
    // by marking its callees dirty for the next sweep. Same fixpoint as a full
    // Gauss-Seidel sweep, but sweeps past the first touch only the shrinking
    // non-converged frontier (recursion cycles) instead of all ~N methods --
    // this is what keeps the inter-method solve off an O(sweeps · N) floor.
    std::vector<bool> dirty(nm, false);
    std::vector<bool> next_dirty(nm, false);
    for (size_t idx = 0; idx < nm; ++idx) {
      dirty[idx] = !pinned[idx] && relevant[idx];
    }
    for (uint32_t sweep = 0; sweep < m_intermethod_max_sweeps; ++sweep) {
      sweeps_used = sweep + 1;
      double max_rel = 0.0;
      size_t changed = 0; // methods still moving by more than converge_eps
      std::fill(next_dirty.begin(), next_dirty.end(), false);
      for (size_t oi = 0; oi < sweep_order.size(); ++oi) {
        const size_t idx = sweep_order[oi];
        if (pinned[idx] || !relevant[idx] || !dirty[idx]) {
          continue; // pinned read-only; non-relevant stay 0; clean == settled
        }
        DexMethod* m = methods[idx];
        if (!cg.has_node(m)) {
          continue;
        }
        double s = 0.0;
        // NOTE: this cross-method sum is deterministic only because callers()
        // is a stable, compare_dexmethods-ordered vector (CallGraph invariant).
        for (const auto* e : cg.node(m)->callers()) {
          const DexMethod* c = e->caller()->method();
          auto* insn = e->invoke_insn();
          if (c == nullptr || insn == nullptr) {
            continue; // ghost entry edge
          }
          auto cit = id_of.find(c);
          if (cit == id_of.end()) {
            continue;
          }
          const double* kp = k_by_insn.get(insn);
          const double k = (kp != nullptr) ? *kp : 0.0;
          // True-virtual split: divide the caller's contribution uniformly
          // among the invoke's resolved targets (structural prior). Exact
          // (static/direct/super/non-true-virtual) invokes have N==1.
          auto ntit = ntargets_by_insn.find(insn);
          const size_t ntargets =
              ntit != ntargets_by_insn.end() ? ntit->second : 0;
          const double share = ntargets > 0 ? k / (double)ntargets : 0.0;
          s += scale[cit->second] * share;
        }
        // Fold the sound backward upper bound into the iteration (box clamp).
        const double raw = s;
        s = std::min(s, hi_scale[idx]);
        // Flag ONLY the overall-ceiling case (hi_scale untightened by any exact
        // callee bound): there the true fixpoint exceeded the ceiling and the
        // magnitude is fabricated. A reduction to a *backward* bound
        // (hi_scale < max_scale) is a SOUND cap, not fabricated -- don't flag
        // it.
        if (s < raw && hi_scale[idx] >= max_scale) {
          hit_ceiling[idx] = true;
        }
        const double prev = scale[idx];
        if (s != prev) {
          const double denom =
              std::max((double)epsilon, std::max(std::abs(prev), std::abs(s)));
          const double rel = std::abs(s - prev) / denom;
          if (rel > converge_eps) {
            changed++;
            // This method moved: its callees' inflow changed, so they must be
            // re-evaluated next sweep. (Callees earlier than `idx` in the BFS
            // order -- i.e. cycle back-edges -- are precisely why we iterate.)
            for (const auto* e : cg.node(m)->callees()) {
              const DexMethod* t = e->callee()->method();
              if (t == nullptr) {
                continue;
              }
              auto tit = id_of.find(t);
              if (tit != id_of.end()) {
                next_dirty[tit->second] = true;
              }
            }
          }
          max_rel = std::max(max_rel, rel);
          scale[idx] = s;
        }
      }
      last_max_rel = max_rel;
      last_changed = changed;
      if (changed == 0) {
        // No method moved by more than converge_eps: fixpoint reached (this is
        // exactly the old `max_rel <= converge_eps` stop).
        converged = true;
        break;
      }
      dirty.swap(next_dirty);
    }
    im_sweeps_total += sweeps_used;
    im_sweeps_max = std::max(im_sweeps_max, sweeps_used);
    // Convergence diagnostics: the worst final-sweep relative change across all
    // interactions, and how many methods were still moving when the sweep cap
    // was hit (breadth of non-convergence -- a few cycles vs broad drift).
    im_final_rel_max = std::max(im_final_rel_max, last_max_rel);
    if (!converged) {
      im_interactions_hit_cap++;
      im_methods_unconverged += last_changed;
    }
    for (size_t idx = 0; idx < nm; ++idx) {
      if (hit_ceiling[idx]) {
        pairs_hit_ceiling.fetch_add(1, std::memory_order_relaxed);
      }
    }
    phaseB_ms += ms_since(t_b);

    // PASS C: instantiate val = scale_M * shape_M(b) from the cached shape (NO
    // re-solve; CFG frozen since PASS 0a). Parallel per method; profiled
    // methods reproduce the per-method magnitude, scale==0 is skipped (NFC).
    auto t_c = clk::now();
    walk::parallel::methods(scope, [&](DexMethod* m) {
      auto iit = id_of.find(m);
      if (iit == id_of.end()) {
        return;
      }
      const size_t idx = iit->second;
      const double s = scale[idx];
      if (s <= 0.0) {
        pairs_skipped.fetch_add(1, std::memory_order_relaxed);
        return; // NFC: leave the boolean support untouched
      }
      if (pinned[idx]) {
        pairs_pinned.fetch_add(1, std::memory_order_relaxed);
      } else {
        pairs_forward_filled.fetch_add(1, std::memory_order_relaxed);
      }
      // A cache miss means this method is uncovered for `i` (every write below
      // is a no-op under the support guard) -- unless it is covered, which
      // would be a RelevanceSet gap (canary metric, must stay 0).
      const auto* shape = shape_cache.get(m);
      if (shape == nullptr) {
        if (covered_methods.count(m) != 0u) {
          im_shape_cache_misses.fetch_add(1, std::memory_order_relaxed);
        }
        return;
      }
      auto* code = m->get_code();
      auto& cfg = code->cfg();
      size_t local_forward_writes = 0; // this method's forward-fill writes
      bool wrote_slot = false; // wrote >=1 block for this interaction
      for (auto* b : cfg.blocks()) {
        const double f = s * (shape->count(b) != 0u ? shape->at(b) : 0.0);
        source_blocks::foreach_source_block(b, [&](SourceBlock* sb) {
          sb->apply_at(i, [&](SourceBlock::Val& v) {
            if (!v || !(v->val > 0.0f)) {
              // preserve 0 / NaN; never resurrect the support. `!(val > 0)`
              // (not `val <= 0`) so a NaN val also takes the skip path.
              return;
            }
            float mval = (float)f;
            if (mval < epsilon) {
              mval = epsilon; // keep covered blocks strictly > 0
            }
            v->val = mval;
            wrote_slot = true;
            blocks_written.fetch_add(1, std::memory_order_relaxed);
            if (!pinned[idx]) {
              forward_blocks_written.fetch_add(1, std::memory_order_relaxed);
              local_forward_writes++;
            }
          });
        });
      }
      if (wrote_slot) {
        // Record this (method, interaction) as producer-written so the callsite
        // clamp caps it, not the boolean slots this producer left untouched.
        m_producer_written.update(m, [i](const DexMethod*, uint64_t& mask,
                                         bool) { mask |= (uint64_t{1} << i); });
      }
      // Record the method the FIRST time a forward-fill mutates it (a
      // per-method event; deduped across interactions by the map key). The
      // creator computes the dex size only on first insert and OUTSIDE the
      // map's slot lock, so the O(n) estimate_code_units() never runs under a
      // lock.
      if (!pinned[idx] && local_forward_writes > 0) {
        forward_mutated_sizes.get_or_create_and_assert_equal(
            m, [&cfg](const DexMethod*) { return cfg.estimate_code_units(); });
      }
    });
    phaseC_ms += ms_since(t_c);
  }

  constexpr size_t kTopMutated = 10;
  auto forward_mutated =
      rank_top_forward_mutated(forward_mutated_sizes, kTopMutated);

  InterStats st;
  st.forward_methods_mutated = forward_mutated_sizes.size();
  st.top_forward_mutated = std::move(forward_mutated);
  st.pairs_pinned = pairs_pinned.load();
  st.pairs_forward_filled = pairs_forward_filled.load();
  st.pairs_skipped = pairs_skipped.load();
  st.blocks_written = blocks_written.load();
  st.pairs_hit_ceiling = pairs_hit_ceiling.load();
  st.methods_not_in_graph = methods_not_in_graph;
  st.pairs_total = im_pairs_total.load();
  st.pairs_covered = im_pairs_covered.load();
  st.pairs_uncovered = st.pairs_total - st.pairs_covered;
  st.shape_solves = im_shape_solves.load();
  st.shape_cache_misses = im_shape_cache_misses.load();
  st.zero_outflow_sinks = im_zero_outflow.load();
  st.irreducible = im_irreducible.load();
  st.relevance_set_size = im_relevance_set_size;
  st.shape_cache_entries = im_shape_cache_entries;
  st.sweeps_total = im_sweeps_total;
  st.sweeps_max = im_sweeps_max;
  st.interactions_hit_cap = im_interactions_hit_cap;
  st.forward_blocks_written = forward_blocks_written.load();
  st.methods_unconverged = im_methods_unconverged;
  st.final_rel_max = im_final_rel_max;
  st.p1_ms = p1_ms;
  st.phase_b_ms = phaseB_ms;
  st.phase_c_ms = phaseC_ms;
  return st;
}

static SyntheticBlockCountsPass s_pass;
