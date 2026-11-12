/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <boost/functional/hash.hpp>

#include <atomic>
#include <cstdint>
#include <fstream>
#include <map>
#include <memory>
#include <mutex>
#include <optional>
#include <queue>
#include <string>
#include <utility>
#include <vector>

#include "ConcurrentContainers.h"
#include "Debug.h"
#include "DeterministicContainers.h"

class DexClass;
class DexMethod;
class DexString;
class DexDebugItem;

namespace positions {
// Defined in PositionJoin.h.
enum class FidelityChange : uint8_t;
} // namespace positions

struct DexPosition final {
  const DexString* method{nullptr};
  const DexString* file{nullptr};
  uint32_t line;

 private:
  // Provenance occupies the four bytes of padding already present between
  // `line` and `parent`:
  //   bit 0        unreliable source identity
  //   bits [31:1]  alt_id
  //
  // It does not participate in position identity;
  // `positions::same_source_claim` compares source claims separately.
  //
  // Not atomic. A position has exactly one owning MethodItemEntry, and
  // `PositionPatternSwitchManager::record_candidates` serializes updates to a
  // shared survivor.
  uint32_t m_prov{0};

  static constexpr uint32_t kUnreliableBit = uint32_t{1};
  static constexpr uint32_t kProvenanceBits = 1;
  static constexpr uint32_t kProvenanceMask =
      (uint32_t{1} << kProvenanceBits) - 1;

  friend class PositionPatternSwitchManager;
  // Canonical interner keys are identity-only.
  void clear_provenance() { m_prov = 0; }
  // Ambiguity whose candidate sites were not captured. Any set the position
  // carried is dropped: it is no longer the complete membership, and the line
  // map cannot express a partial one, so presenting it would overstate what is
  // known. This is the absorbing state -- see
  // `PositionPatternSwitchManager::record_candidates`.
  void mark_unreliable_without_candidates() {
    m_prov = (m_prov & kProvenanceMask) | kUnreliableBit;
  }

 public:
  // when a function gets inlined for the first time, all its DexPositions will
  // have the DexPosition of the callsite as their parent.
  DexPosition* parent{nullptr};
  explicit DexPosition(const DexString* file, uint32_t line);
  DexPosition(const DexString* method, const DexString* file, uint32_t line);

  void bind(const DexString* method_, const DexString* file_);
  void bind(const DexString* method_);
  bool operator==(const DexPosition&) const;

  static std::unique_ptr<DexPosition> make_synthetic_entry_position(
      const DexMethod* method);
  static std::unique_ptr<DexPosition> make_synthetic_position(
      const DexString* method_name);

  // Whether a producer has recorded that this position stopped uniquely
  // identifying the source location of the code it governs. A position that is
  // not unreliable is not proven exact: no producer recorded a loss, so
  // consumers treat it as an ordinary position. There is no "exact"
  // state, because this records known loss, not proof that every earlier
  // transformation preserved a unique source location.
  bool is_unreliable() const { return (m_prov & kUnreliableBit) != 0; }
  // A position on line 0: Redex made it up for code with no source line (for
  // example `make_synthetic_entry_position`), or the input carried no line.
  // Java prints such a frame without a line number.
  //
  // Synthetic and unreliable are independent: code on line 0 can later be
  // folded with another source location. Because `line` is part of position
  // identity, being synthetic survives copying, interning and outlining.
  //
  // Outliner pattern and switch records (see `PositionPatternSwitchManager`)
  // keep their pattern or switch id in `line`, so one with id 0 also reads as
  // synthetic. Callers that can meet such records check `is_pattern_position`
  // and `is_switch_position` first.
  bool is_synthetic() const { return line == 0; }
  // Source claims only lose certainty. There is deliberately no mutator back:
  // later agreement cannot prove earlier transforms kept one origin.
  void mark_unreliable() { m_prov |= kUnreliableBit; }
  // Identifier of the interned set of candidate source positions this position
  // stands for, or 0 when no set was recorded. Together with the unreliable bit
  // this gives three states: clean, ambiguous with a complete set, and
  // ambiguous with the sites uncaptured (`is_unreliable() && alt_id() == 0`).
  // The line map has no encoding for a partial set, so the last state is
  // absorbing.
  uint32_t alt_id() const { return m_prov >> kProvenanceBits; }
  // Recording a candidate set makes a position unreliable.
  void set_alt_id(uint32_t alt_id);

  static constexpr uint32_t max_alt_id() {
    return (uint32_t{1} << (32 - kProvenanceBits)) - 1;
  }
  // Compares this level only; see `same_position_and_provenance` for chains.
  bool same_provenance(const DexPosition& that) const {
    return m_prov == that.m_prov;
  }
};

/*
 * Whether one of two position entries can be dropped in favor of the other
 * without losing anything: same identity and same provenance at every level of
 * the inlining chain. A copy that a producer has since marked is not redundant
 * with the unmarked original, because the two govern different instructions.
 */
inline bool same_position_and_provenance(const DexPosition& a,
                                         const DexPosition& b) {
  if (!(a == b)) {
    return false;
  }
  const DexPosition* pa = &a;
  const DexPosition* pb = &b;
  for (; pa != nullptr && pb != nullptr; pa = pa->parent, pb = pb->parent) {
    if (pa == pb) {
      return true;
    }
    if (!pa->same_provenance(*pb)) {
      return false;
    }
  }
  return pa == nullptr && pb == nullptr;
}
// Identity of an interned position. Keep these two adjacent: they are a pair,
// and a hash that stops agreeing with its equality is the bug this replaced.
// A parent is interned before its child, so a whole inlining chain is
// identified by one pointer and neither of these recurses.
struct InternedPositionHash {
  size_t operator()(const DexPosition& pos) const {
    size_t h = reinterpret_cast<size_t>(pos.method);
    boost::hash_combine(h, reinterpret_cast<size_t>(pos.file));
    boost::hash_combine(h, pos.line);
    boost::hash_combine(h, reinterpret_cast<size_t>(pos.parent));
    return h;
  }
};
struct InternedPositionEqual {
  bool operator()(const DexPosition& a, const DexPosition& b) const {
    return a.method == b.method && a.file == b.file && a.line == b.line &&
           a.parent == b.parent;
  }
};
struct CandidatePositionHash {
  size_t operator()(const DexPosition& pos) const {
    size_t h = InternedPositionHash{}(pos);
    boost::hash_combine(h, pos.alt_id());
    boost::hash_combine(h, pos.is_unreliable());
    return h;
  }
};
struct CandidatePositionEqual {
  bool operator()(const DexPosition& a, const DexPosition& b) const {
    return InternedPositionEqual{}(a, b) && a.alt_id() == b.alt_id() &&
           a.is_unreliable() == b.is_unreliable();
  }
};
static_assert(sizeof(DexPosition) == 32,
              "DexPosition provenance must stay inside the existing padding "
              "between `line` and `parent`; growing the struct multiplies "
              "across millions of live positions.");
// Provenance reaches cloned positions because copying a DexPosition copies its
// bytes. A user-declared copy constructor here could keep compiling while
// silently stopping propagation through clone sites, so pin the property.
static_assert(std::is_trivially_copyable_v<DexPosition>,
              "DexPosition must stay trivially copyable: provenance propagates "
              "through the implicit copy constructor at every clone site.");

using PositionPattern = std::vector<DexPosition*>;
using PositionPatternHasher = boost::hash<PositionPattern>;

enum class PositionAlternativesSelection : uint8_t {
  ByPattern,
  All,
};

struct PositionAlternative {
  std::optional<uint32_t> pattern_id;
  DexPosition* position;
  bool operator==(const PositionAlternative& other) const {
    return pattern_id == other.pattern_id && position == other.position;
  }
};
inline size_t hash_value(const PositionAlternative& alternative) {
  size_t h = alternative.pattern_id.has_value() ? 1 : 0;
  boost::hash_combine(h, alternative.pattern_id.value_or(0));
  boost::hash_combine(h, reinterpret_cast<size_t>(alternative.position));
  return h;
}

struct PositionAlternatives {
  PositionAlternativesSelection selection;
  std::vector<PositionAlternative> entries;
  bool operator==(const PositionAlternatives& other) const {
    return selection == other.selection && entries == other.entries;
  }
};
inline size_t hash_value(const PositionAlternatives& alternatives) {
  size_t h = static_cast<uint8_t>(alternatives.selection);
  boost::hash_combine(h, alternatives.entries);
  return h;
}
using PositionAlternativesHasher = boost::hash<PositionAlternatives>;

// Outliner-facing name for alternatives selected by a call-site pattern.
using PositionSwitch = std::vector<PositionAlternative>;

/*
 * This manager class maintains state representing patterns and position
 * switches that can be used when outlining. It can be accessed via the
 * RedexContext.
 */
class PositionPatternSwitchManager {
 public:
  PositionPatternSwitchManager();

  // TODO: Enable the following flag. It's off for now to ensure that the
  // inliner and outliner never produce an outlined method that invokes an
  // outlined method, a limitation imposed by symbolication infrastructure.
  static constexpr bool CAN_OUTLINED_METHOD_INVOKE_OUTLINED_METHOD = false;

  // Returns a value that uniquely identifies the pattern.
  uint32_t make_pattern(PositionPattern pos_pattern);

  // Returns a value that uniquely identifies a switch selected by pattern id.
  uint32_t make_switch(PositionSwitch pos_switch);

  /*
   * Records that `survivor` no longer identifies a unique source location, and
   * adds `candidates` to the sites it stands for.
   *
   * Outliner switches and candidate sets are distinct semantic clients of one
   * alternatives representation: a switch selects one entry by pattern id,
   * while a candidate set enumerates every entry. Both serialize through the
   * same count/case record path.
   *
   * Additive, because a survivor can be merged into repeatedly and because a
   * clone inherits the ambiguity of the position it came from. The complete,
   * canonically ordered membership is retained even when emission is capped,
   * so later additions and duplicates keep the exact total.
   *
   * Each member is one source place: a candidate that already stands for a
   * set contributes its own place and that set's members, and members with
   * one identity (method, file, line and parent chain) are joined into one by
   * `join_chains`, so what each knew about its callers is kept. A candidate
   * on line 0 names its method at an unknown line.
   *
   * The survivor's own place is not one of its candidates, but copies of it
   * can know more about its callers than the survivor's own callers say --
   * say, that an inlined caller line was itself merged. Those callers are
   * shared with other code and are never changed here, so the survivor's
   * place then joins the set, its callers joined level by level with every
   * copy's.
   *
   * A candidate that cannot be named -- absent, without a file, in a method
   * Redex generated, an outliner switch or pattern record (a throw under a
   * pattern position comes from any slot of the outlined method it calls),
   * or itself ambiguous with its own sites uncaptured -- leaves the survivor
   * in the absorbing uncaptured state instead, because a set missing one
   * member is not the complete membership and the line map cannot say so. An
   * empty `candidates` reports one such site.
   *
   * Candidates that, once the survivor's own place and duplicates are
   * dropped, name no place at all add nothing the survivor does not already
   * present, so the survivor is left unchanged.
   *
   * Returns whether the survivor became unreliable. A survivor that already
   * was and merely grew its set has not made that transition, and counting
   * it again would double-count one position.
   *
   * Pass every candidate of one fold in one call: each call that changes the
   * set registers a new one, and registered sets are never freed.
   */
  static constexpr size_t kMaxCandidates = 8;
  positions::FidelityChange record_candidates(
      DexPosition* survivor, const std::vector<const DexPosition*>& candidates);

  // `record_candidates` for several distinct survivors, each worked out from
  // the positions as they stand before any of them changes. One survivor can
  // be the inlined caller of another, and what a survivor records depends on
  // its callers, so recording them one after another would let an earlier
  // record change a later one. Returns each record's change, in order.
  std::vector<positions::FidelityChange> record_candidates_jointly(
      const std::vector<
          std::pair<DexPosition*, std::vector<const DexPosition*>>>& records);

  // What an `alt_id` on a position refers to. Members are candidate snapshots
  // whose own level carries no provenance.
  struct AltSet {
    uint32_t alternatives_id;
    PositionPattern members;

    uint32_t total_candidates() const {
      return static_cast<uint32_t>(members.size());
    }
  };
  // Thread-safe. A registered set is immutable and owned by the manager for
  // its lifetime, so the reference stays valid while other threads register
  // more sets; the lock covers only finding it.
  const AltSet& get_alt_set(uint32_t alt_id) const {
    std::lock_guard<std::mutex> lock(m_registration_mutex);
    always_assert(alt_id != 0 && alt_id <= m_alt_sets.size());
    return *m_alt_sets[alt_id - 1];
  }

  // A position that can be used at an outlined method call-site to indicate
  // that a particular position pattern in the outlined method should be
  // selected. For example, for pattern-id 12345, this will produce the
  // following position:
  //
  // method Lredex/$Position;.pattern:()V, line 12345 (no parent)
  std::unique_ptr<DexPosition> make_pattern_position(uint32_t pattern_id) const;

  // A position that can be used in an outlined method to indicate a choice
  // between different positions, dependent on a particular call-site pattern.
  // For example, for switch-id 99991, this will produce the following position:
  //
  // method Lredex/$Position;.switch:()V, line 99991 (no parent)
  //
  // Note that later, when a v2-map file is created, the line number will be
  // replaced with an offset to a switch-case table, so the switch-ids used
  // while Redex is running won't be found in the map file.
  std::unique_ptr<DexPosition> make_switch_position(uint32_t switch_id) const;

  bool is_pattern_position(const DexPosition* pos) const {
    return pos->method == m_pattern_string;
  }
  bool is_switch_position(const DexPosition* pos) const {
    return pos->method == m_switch_string;
  }

  bool empty() const {
    return m_positions.empty() && m_patterns.empty() && m_alternatives.empty();
  }

  const std::vector<PositionPattern>& get_patterns() const {
    return m_patterns;
  }

  const std::vector<PositionAlternatives>& get_alternatives() const {
    return m_alternatives;
  }

  // How many positions `internalize` was asked for, and how many distinct ones
  // it kept. The gap between them is the clone the interning avoided; when the
  // interning was broken the two were equal.
  size_t get_num_internalize_calls() const {
    return m_internalize_calls.load();
  }
  size_t get_num_interned_positions() const { return m_positions.size(); }

  // How many distinct candidate sets are registered.
  size_t get_num_alt_sets() const {
    std::lock_guard<std::mutex> lock(m_registration_mutex);
    return m_alt_sets.size();
  }

 private:
  DexPosition* internalize(DexPosition* pos);
  // An immutable copy of `pos` and its inlining chain, provenance included,
  // except that `clear_own_provenance` drops it from `pos`'s own level, as a
  // set member needs.
  DexPosition* snapshot_candidate(const DexPosition* pos,
                                  bool clear_own_provenance = false);
  // A snapshot of `kept`'s chain in which every level stands for every place
  // that level and `other`'s level at the same depth stand for: merged with
  // sites nobody captured if either is, or if `other` names a different place
  // there or has no such level; otherwise the union of their candidate sets.
  // Commutative for chains of one identity. Every join of what two copies of
  // one place know -- set members, the survivor's own place -- goes through
  // this.
  DexPosition* join_chains(const DexPosition* kept, const DexPosition* other);
  // `members` ordered by identity, with members of one identity joined.
  PositionPattern canonical_members(const std::vector<DexPosition*>& members);
  // Registers the canonically ordered complete membership of a set and returns
  // its alt id.
  uint32_t register_alt_set(PositionPattern members);
  // Whether a position, or anything it was inlined into, names no source
  // method: it has no file, belongs to a method Redex generated, or is an
  // outliner pattern or switch record. Such a position is not a site a stack
  // trace can be explained by. Line 0 still names its method.
  bool names_no_source(const DexPosition* pos) const;
  uint32_t make_alternatives(PositionAlternatives alternatives);
  // What `record_candidates` makes of a survivor: whether it becomes
  // unreliable, and its new provenance when it changes at all.
  struct CandidateRecord {
    bool became_unreliable{false};
    std::optional<uint32_t> provenance;
  };
  // Changes no position. The caller holds the survivor's mutex.
  CandidateRecord compute_candidate_record(
      const DexPosition* survivor,
      const std::vector<const DexPosition*>& candidates);
  static void apply_candidate_record(DexPosition* survivor,
                                     const CandidateRecord& record);
  size_t survivor_stripe(const DexPosition* survivor) const {
    constexpr size_t kLockCount = 64;
    static_assert(kLockCount ==
                  std::tuple_size_v<decltype(m_survivor_mutexes)>);
    return (reinterpret_cast<uintptr_t>(survivor) >> 4) % kLockCount;
  }
  std::mutex& survivor_mutex(DexPosition* survivor) {
    return m_survivor_mutexes[survivor_stripe(survivor)];
  }

  // The element IS the manager's immutable, identity-only copy of the position.
  // Provenance is cleared before insertion because it is not part of the key;
  // allowing a first inserter's metadata to survive would make equal source
  // positions inherit whichever thread arrived first. Nothing is ever erased
  // and elements are pinned for the container's lifetime, so a pointer to one
  // stays valid for the run. Do not mutate an interned position: it is its own
  // key.
  InsertOnlyConcurrentSet<DexPosition,
                          InternedPositionHash,
                          InternedPositionEqual>
      m_positions;
  InsertOnlyConcurrentSet<DexPosition,
                          CandidatePositionHash,
                          CandidatePositionEqual>
      m_candidate_positions;
  std::atomic<size_t> m_internalize_calls{0};

  // Serializes updates that union candidates into the same survivor. Different
  // survivors remain independent, and expensive interning stays outside the
  // global registration lock.
  std::array<std::mutex, 64> m_survivor_mutexes;

  // Guards the alternatives and alt-set id tables. Pattern registration is
  // sequential (the outliner only), so `make_pattern` stays unlocked.
  mutable std::mutex m_registration_mutex;

  // Alt sets retain complete membership even though only the first
  // `kMaxCandidates` entries are emitted. This makes later union cardinality
  // exact and lets different full sets share the same capped records.
  //
  // Each set's members are stored once, in `m_alt_sets`; the index keys view
  // those stored members and carries their precomputed hash, so a lookup under
  // the lock hashes nothing.
  struct AltSetMembersKey {
    size_t hash;
    const PositionPattern* members;
  };
  struct AltSetMembersKeyHash {
    size_t operator()(const AltSetMembersKey& key) const { return key.hash; }
  };
  struct AltSetMembersKeyEqual {
    bool operator()(const AltSetMembersKey& a,
                    const AltSetMembersKey& b) const {
      return a.hash == b.hash && *a.members == *b.members;
    }
  };
  UnorderedMap<AltSetMembersKey,
               uint32_t,
               AltSetMembersKeyHash,
               AltSetMembersKeyEqual>
      m_alt_set_ids;
  std::vector<std::unique_ptr<const AltSet>> m_alt_sets;
  UnorderedMap<PositionPattern, uint32_t, PositionPatternHasher> m_patterns_map;
  std::vector<PositionPattern> m_patterns;
  UnorderedMap<PositionAlternatives, uint32_t, PositionAlternativesHasher>
      m_alternatives_map;
  std::vector<PositionAlternatives> m_alternatives;

  const DexString* m_pattern_string;
  const DexString* m_switch_string;
  const DexString* m_unknown_source_string;
  const DexString* m_redex_generated_string;
};

class PositionMapper {
 public:
  virtual ~PositionMapper() {}
  virtual const DexString* get_source_file(const DexClass*) = 0;
  virtual uint32_t position_to_line(DexPosition*) = 0;
  virtual void register_position(DexPosition* pos) = 0;
  virtual void write_map() = 0;
  virtual uint32_t size() const = 0;
  static PositionMapper* make(const std::string& map_filename_v2);
};

/*
 * Optional extension layout:
 *
 *   [v2 body][section payloads][section directory][Trailer]
 *
 * Known count-driven readers stop after the declared positions array. New
 * readers find a possible trailer at EOF, but magic is necessary rather than
 * sufficient: exact suffix accounting, section bounds, whole entries, sorted
 * record indices, and index ranges must all validate. Truncated maps are an
 * ordinary storage failure mode, so offsets and lengths are checked before use.
 *
 * `record_index` is zero-based. `alt_record_index == 0` means no alternate;
 * a nonzero value points to the emitted count/case records. `total_candidates`
 * is nonzero only when the emitted alternatives were capped. Integers use the
 * host byte order, matching the existing line-map body.
 */
namespace position_map {

// Line-map extension trailer magic. This is deliberately distinct from the v2
// body magic (`0xfaceb000`) and IODI metadata magic (`0xfaceb001`).
constexpr uint32_t kTrailerMagic = 0xfaceb002;

enum class SectionTag : uint32_t {
  // Sparse and sorted by record index; only unreliable positions are emitted.
  Provenance = 0x564f5250, // 'PROV'
};

struct SectionEntry {
  uint32_t tag;
  uint32_t reserved;
  uint64_t offset;
  uint64_t length;
};

struct Trailer {
  uint64_t directory_offset;
  uint32_t section_count;
  uint32_t magic;
};

// One entry per known-unreliable source-position record. `record_index` is
// zero-based; zero in `alt_record_index` means no alternate. A nonzero
// `total_candidates` preserves the pre-cap cardinality.
struct ProvenanceEntry {
  uint32_t record_index;
  uint32_t alt_record_index;
  uint32_t total_candidates;
};

// These are written to the file verbatim, so their layout is the format.
static_assert(sizeof(SectionEntry) == 24);
static_assert(sizeof(Trailer) == 16);
static_assert(sizeof(ProvenanceEntry) == 12);

} // namespace position_map

/*
 * This allows us to recover the original file names and line numbers from
 * runtime stack traces of Dex files that have undergone inlining. The
 * PositionMapper produces a text file with this data, and the line numbers in
 * the Dex debug info indicate the line in this text file at which the real
 * position can be found. See `position_map` above for the appended provenance
 * format.
 */
class RealPositionMapper : public PositionMapper {
  std::string m_filename_v2;
  std::vector<DexPosition*> m_positions;
  UnorderedMap<DexPosition*, int64_t> m_pos_line_map;
  std::queue<DexPosition*> m_possibly_incomplete_positions;
  std::vector<std::unique_ptr<DexPosition>> m_owned_auxiliary_positions;
  // alternatives id -> index of the `count` record introducing its cases,
  // filled in by `process_position_alternatives` and read when writing the
  // trailer.
  UnorderedMap<uint32_t, uint32_t> m_alternatives_record_indices;

  void process_position_alternatives();
  // Writes nothing when no position in the map carries provenance.
  void write_provenance_trailer(std::ofstream& ofs);

 protected:
  int64_t add_position(DexPosition* pos);
  uint32_t get_line(DexPosition*);
  void write_map_v2();

 public:
  explicit RealPositionMapper(std::string filename_v2)
      : m_filename_v2(std::move(filename_v2)) {}
  const DexString* get_source_file(const DexClass*) override;
  uint32_t position_to_line(DexPosition*) override;
  void register_position(DexPosition* pos) override;
  void write_map() override;
  uint32_t size() const override;
};

class NoopPositionMapper : public PositionMapper {
 public:
  const DexString* get_source_file(const DexClass*) override;
  uint32_t position_to_line(DexPosition* pos) override { return pos->line; }
  void register_position(DexPosition*) override {}
  void write_map() override {}
  uint32_t size() const override { return 0; }
};
