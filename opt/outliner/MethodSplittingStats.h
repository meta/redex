/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <algorithm>
#include <array>
#include <atomic>
#include <mutex>
#include <optional>
#include <string_view>
#include <utility>
#include <vector>

#include "AtomicStatCounter.h"
#include "Debug.h"
#include "DexClass.h"
#include "MethodClosures.h"
#include "SplitNetSaving.h"

class PassManager;

namespace method_splitting_impl {

// Discriminates the two kinds of splits produced by this pass.
// Tests prefer this enum over name-substring matching to avoid the
// `$hot$` / `$hot_cold$` substring overlap trap.
enum class SplitKind {
  Suffix,
  Region,
};

// Plain-data copy of `FateCounters`.
struct FateSnapshot {
  size_t candidates{0};
  std::array<size_t, kCandidateFateCount> n{};
  std::array<size_t, kCandidateFateCount> code_units{};

  size_t operator[](CandidateFate fate) const {
    return n[static_cast<size_t>(fate)];
  }
  // The number of candidates recorded at any fate. Once a run is over, it
  // equals `candidates`, because every candidate is recorded exactly once.
  size_t recorded() const {
    size_t sum = 0;
    for (auto count : n) {
      sum += count;
    }
    return sum;
  }
};

// The fates a suffix candidate can reach.
inline constexpr std::array kSuffixFates{
    CandidateFate::Evaluation_EmptyHead,
    CandidateFate::Evaluation_TooManyLiveIns,
    CandidateFate::Evaluation_LiveInUntypable,
    CandidateFate::Evaluation_ArgTypeIllegal,
    CandidateFate::Evaluation_LiveInUninitialized,
    CandidateFate::Evaluation_NetNotPositive,
    CandidateFate::Selection_Displaced,
    CandidateFate::Emission_DexLimit,
    CandidateFate::Emitted,
};

// Whether a candidate of `kind` can end at `fate`.
inline bool can_reach(SplitKind kind, CandidateFate fate) {
  return kind == SplitKind::Region ||
         std::ranges::find(kSuffixFates, fate) != kSuffixFates.end();
}

// How many candidates of one kind a run considered, and how many ended at each
// fate, with the code units they carried: the code a split would take or took.
struct FateCounters {
  explicit FateCounters(SplitKind kind) : kind(kind) {}

  using PerFate = std::array<AtomicStatCounter<size_t>, kCandidateFateCount>;

  const SplitKind kind;
  AtomicStatCounter<size_t> candidates{0};
  PerFate n{zeroes(std::make_index_sequence<kCandidateFateCount>())};
  PerFate code_units{zeroes(std::make_index_sequence<kCandidateFateCount>())};

  void record(CandidateFate fate, size_t units) {
    const bool reachable = can_reach(kind, fate);
    redex_assert(reachable);
    const auto i = static_cast<size_t>(fate);
    n[i]++;
    code_units[i] += units;
  }

  FateSnapshot snapshot() const {
    FateSnapshot s;
    s.candidates = candidates.load();
    for (size_t i = 0; i < kCandidateFateCount; ++i) {
      s.n[i] = n[i].load();
      s.code_units[i] = code_units[i].load();
    }
    return s;
  }

  // `<kind>_candidates`, and `<kind>_<fate>` and `<kind>_<fate>_code_units`
  // for every fate a candidate of the kind can reach.
  void export_metrics(PassManager& mgr) const;

 private:
  template <size_t... I>
  static PerFate zeroes(std::index_sequence<I...> /* fates */) {
    return {{((void)I, AtomicStatCounter<size_t>(0))...}};
  }
};

// What became of one candidate, for tests: its kind, its heads, the net saving
// a net gate computed for it, if any, its fate, the iteration that decided it,
// and the split emitted for it.
struct CandidateEvaluation {
  SplitKind kind;
  std::vector<cfg::BlockId> heads;
  std::optional<ClosureNetTerms> terms;
  CandidateFate fate;
  size_t iteration;
  const DexMethod* split{nullptr};
};

// Test-only sink for evaluation records, in the order they were made.
class EvaluationLog {
 public:
  void add(CandidateEvaluation evaluation) {
    std::lock_guard<std::mutex> lock(m_mutex);
    m_records.push_back(std::move(evaluation));
  }
  std::vector<CandidateEvaluation> records() const {
    std::lock_guard<std::mutex> lock(m_mutex);
    return m_records;
  }

 private:
  mutable std::mutex m_mutex;
  std::vector<CandidateEvaluation> m_records;
};

// Plain-data snapshot of Stats. Returned by `Stats::snapshot()` so
// tests can read counter values by value without touching atomics.
struct StatsSnapshot {
  size_t split_count;
  size_t split_count_simple;
  size_t split_count_switches;
  size_t split_count_switch_cases;
  size_t hot_split_count;
  size_t hot_cold_split_count;
  size_t cold_split_count;
  size_t dex_limits_hit;
  size_t added_code_size;
  size_t split_code_size;
  size_t kept_large_packed_switches;
  size_t created_large_sparse_switches;
  size_t destroyed_large_packed_switches;
  size_t excluded_methods;
  size_t iterations;
  FateSnapshot suffix_fates;
};

struct Stats {
  std::atomic<size_t> split_count_simple{0};
  std::atomic<size_t> split_count_switches{0};
  std::atomic<size_t> split_count_switch_cases{0};
  std::atomic<size_t> hot_split_count{0};
  std::atomic<size_t> hot_cold_split_count{0};
  std::atomic<size_t> cold_split_count{0};
  std::atomic<size_t> dex_limits_hit{0};
  std::atomic<size_t> added_code_size{0};
  std::atomic<size_t> split_code_size{0};
  std::atomic<size_t> kept_large_packed_switches{0};
  std::atomic<size_t> created_large_sparse_switches{0};
  std::atomic<size_t> destroyed_large_packed_switches{0};
  // Each newly-emitted split, tagged with its kind. Append-only;
  // deterministically ordered by `compare_dexmethods` when transferred
  // from the per-iteration concurrent collection.
  std::vector<std::pair<DexMethod*, SplitKind>> added_methods;
  std::atomic<size_t> excluded_methods{0};
  // During a run, the index of the iteration in progress, which every
  // evaluation record carries. After the run, the number of iterations run.
  size_t iterations{0};

  FateCounters suffix_fates{SplitKind::Suffix};

  // Test-only sink; null in production. A record for every candidate that
  // reached scoring.
  EvaluationLog* evaluations{nullptr};

  // Records the final fate of a candidate: the only way a fate is counted.
  // `head_ids` returns the candidate's head-block ids; it is called only when
  // a log is attached, so a production run builds no head list.
  template <typename HeadIds>
  void record(SplitKind kind,
              const HeadIds& head_ids,
              std::optional<ClosureNetTerms> terms,
              CandidateFate fate,
              size_t code_units,
              const DexMethod* split = nullptr) {
    suffix_fates.record(fate, code_units);
    if (evaluations != nullptr) {
      evaluations->add(CandidateEvaluation{.kind = kind,
                                           .heads = head_ids(),
                                           .terms = terms,
                                           .fate = fate,
                                           .iteration = iterations,
                                           .split = split});
    }
  }

  // Every metric of the pass that the splitter counts.
  void export_metrics(PassManager& mgr) const;

  StatsSnapshot snapshot() const {
    return StatsSnapshot{
        .split_count = added_methods.size(),
        .split_count_simple = split_count_simple.load(),
        .split_count_switches = split_count_switches.load(),
        .split_count_switch_cases = split_count_switch_cases.load(),
        .hot_split_count = hot_split_count.load(),
        .hot_cold_split_count = hot_cold_split_count.load(),
        .cold_split_count = cold_split_count.load(),
        .dex_limits_hit = dex_limits_hit.load(),
        .added_code_size = added_code_size.load(),
        .split_code_size = split_code_size.load(),
        .kept_large_packed_switches = kept_large_packed_switches.load(),
        .created_large_sparse_switches = created_large_sparse_switches.load(),
        .destroyed_large_packed_switches =
            destroyed_large_packed_switches.load(),
        .excluded_methods = excluded_methods.load(),
        .iterations = iterations,
        .suffix_fates = suffix_fates.snapshot(),
    };
  }
};

} // namespace method_splitting_impl
