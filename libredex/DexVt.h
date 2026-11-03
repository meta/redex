/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include <boost/functional/hash.hpp>

#include "ConcurrentContainers.h"
#include "DeterministicContainers.h"
#include "DexStore.h"

struct ConfigFiles;
class DexField;
class DexMethod;
struct enhanced_dex_stats_t;

namespace dexvt {

/*
 * Sparse per-basic-block hotness sample from a SourceBlock, for one
 * interaction. interaction_idx indexes the SourceBlock interaction-index space
 * (Exporter::m_sb_interaction_names) -- a DIFFERENT axis from the
 * MethodProfiles interaction ids below, so the two are always joined by
 * interaction name.
 */
struct BlockHotness {
  uint32_t block_id{0};
  uint32_t interaction_idx{0};
  float val{0.f};
  float appear100{0.f};
};

/*
 * Per-method MethodProfiles "deep data" for one interaction, keyed by the
 * MethodProfiles interaction id string.
 */
struct MethodPgoStat {
  std::string interaction;
  double appear_percent{0.0}; // appear100
  double call_count{0.0}; // avg_call
  double order_percent{0.0}; // avg_rank100
};

/*
 * One loop of a method's CFG (a libredex/LoopInfo loop). `parent` is the index
 * of the immediately enclosing loop in MethodRecord::loops, or -1 for an
 * outermost loop.
 */
struct LoopRecord {
  uint32_t header_blk{0};
  int32_t parent{-1};
};

/*
 * Everything captured for a single method. Assembled pre-lowering (disasm,
 * block hotness, PGO) and completed at emit time with the authoritative
 * code_item size and symbolication. Keyed by the interned DexMethod*.
 */
struct MethodRecord {
  uint32_t id{0};
  std::string disasm; // show(cfg, code_only=true)
  std::vector<BlockHotness> blocks; // sparse; default (0,0) omitted
  // Loops, outermost first (a parent always precedes its children), and each
  // looping block's innermost loop as (cfg block id, index into `loops`),
  // block id ascending. Both empty for a method without loops.
  std::vector<LoopRecord> loops;
  std::vector<std::pair<uint32_t, uint32_t>> block_loop;
  std::vector<MethodPgoStat> pgo;
  // Betamap coldstart order position of the owning class (-1 if absent); coarse
  // InterDex group (-1 if grouping disabled/absent); ART baseline membership.
  int64_t betamap_rank{-1};
  int64_t interdex_group{-1};
  bool baseline_hot{false};
  bool baseline_startup{false};
  bool baseline_post_startup{false};
  // Ids of methods that call this method (virtual/interface callers included
  // via the MethodOverrideGraph-resolved call graph); sorted for stable output.
  // Methods with the same callers share one list, owned by the Exporter;
  // nullptr when nothing calls this method.
  const std::vector<uint32_t>* callers{nullptr};
  // Containing dex after the InterDex split ("<store>/<dex_index>"), so the
  // read-side can group methods by dex file. Empty if the class wasn't found in
  // any store's dexen.
  std::string dex;
};

struct CallerIdsHash {
  size_t operator()(const std::vector<uint32_t>& ids) const {
    return boost::hash_range(ids.begin(), ids.end());
  }
};

/*
 * A single field (static or instance). Fields have no code, so this is minimal:
 * an id in the same space as methods, the containing dex, and (at emit time)
 * the symbolicated names + access. Captured serially in capture_pre_lowering.
 */
struct FieldRecord {
  const DexField* field{nullptr};
  uint32_t id{0};
  std::string dex;
};

/*
 * A class's inheritance edges: its (deobfuscated) name, direct superclass, and
 * directly-implemented interfaces. Emitted as kind:"class" records so the
 * read-side can answer super/interfaces queries and derive subclasses /
 * implementors by inverting these edges (they are not emitted). Captured
 * serially in capture_pre_lowering over the class scope.
 */
struct ClassRecord {
  std::string name;
  std::string super; // empty when the class has no super (e.g. Object,
                     // interfaces)
  std::vector<std::string> interfaces;
};

/*
 * Build-side, two-phase DEX disassembly + PGO exporter. Enabled by
 * RedexOptions::emit_dexvt and driven from redex_backend:
 *
 *   - capture_pre_lowering() runs BEFORE instruction_lowering::run. The CFG has
 *     been cleared by PassManager before the backend, so this phase builds one
 *     per method, on a copy of its code so the code itself is left exactly as
 *     it was, to read per-block SourceBlocks, and assigns each method a stable
 *     monotonic id reused by emit().
 *   - emit() runs AFTER the dex write loop with the accumulated output_totals,
 *     joins the authoritative sizes onto the captured records, and streams the
 *     NDJSON artifact. When the write loop filled `method_to_id` (it does for
 *     builds that write redex-debug-line-map-v2), emit() also records each
 *     method's index in its dex and each dex's signature, the two halves of
 *     the key that map files the method under.
 */
class Exporter {
 public:
  void capture_pre_lowering(DexStoresVector& stores, ConfigFiles& conf);
  void emit(ConfigFiles& conf,
            const enhanced_dex_stats_t& output_totals,
            const UnorderedMap<DexMethod*, uint64_t>* method_to_id = nullptr);

  // Read-only inspection accessors (used by tests).
  size_t num_captured() const { return m_records.size(); }
  size_t num_fields() const { return m_fields.size(); }
  const MethodRecord* get_record(const DexMethod* m) const {
    return m_records.get(m);
  }

 private:
  // interned DexMethod* -> stable monotonic id, assigned deterministically
  // before the parallel capture and reused by emit().
  UnorderedMap<const DexMethod*, uint32_t> m_ids;
  InsertOnlyConcurrentMap<const DexMethod*, MethodRecord> m_records;
  // The distinct caller lists MethodRecord::callers points into. Methods share
  // a list whenever they inherit their callers from the same virtual call
  // sites: every override of an interface method has the callers of that
  // interface method.
  InsertOnlyConcurrentSet<std::vector<uint32_t>, CallerIdsHash> m_caller_sets;
  // SourceBlock interaction index -> name (for the manifest / block labelling).
  std::vector<std::string> m_sb_interaction_names;
  // MethodProfiles interaction ids (the pgo{} axis), recorded for the manifest.
  std::vector<std::string> m_pgo_interactions;
  // Whether baseline-profile configs were present. Recorded in the manifest so
  // a missing per-method `baseline` block reads as "not in profile" rather than
  // "no baseline configured".
  bool m_baseline_available{false};
  // Fields (static + instance) across all classes, id-ordered; emitted as
  // kind:"field" records alongside methods so the read-side can list them.
  std::vector<FieldRecord> m_fields;
  // Class inheritance edges (super + interfaces), scope-ordered; emitted as
  // kind:"class" records so the read-side can query the hierarchy.
  std::vector<ClassRecord> m_classes;
};

} // namespace dexvt
