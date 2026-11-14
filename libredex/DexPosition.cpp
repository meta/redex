/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <algorithm>
#include <fstream>
#include <functional>
#include <limits>
#include <tuple>
#include <type_traits>

#include "ConcurrentContainers.h"
#include "Debug.h"
#include "DexClass.h"
#include "DexPosition.h"
#include "DexUtil.h"
#include "PositionJoin.h"
#include "RedexContext.h"
#include "Show.h"
#include "Trace.h"
#include "WorkQueue.h"

DexPosition::DexPosition(const DexString* file, uint32_t line)
    : file(file), line(line) {
  always_assert(file != nullptr);
}

DexPosition::DexPosition(const DexString* method,
                         const DexString* file,
                         uint32_t line)
    : method(method), file(file), line(line) {
  always_assert(file != nullptr);
}

void DexPosition::bind(const DexString* method_, const DexString* file_) {
  always_assert(file_ != nullptr);
  this->method = method_;
  this->file = file_;
}

void DexPosition::bind(const DexString* method_) { this->method = method_; }

void DexPosition::set_alt_id(uint32_t alt_id) {
  always_assert(alt_id != 0);
  always_assert_log(alt_id <= max_alt_id(),
                    "alt-set id %u exceeds the %u encodable in DexPosition",
                    alt_id, max_alt_id());
  m_prov =
      (alt_id << kProvenanceBits) | (m_prov & kProvenanceMask) | kUnreliableBit;
}
bool DexPosition::operator==(const DexPosition& that) const {
  return method == that.method && file == that.file && line == that.line &&
         (parent == that.parent ||
          (parent != nullptr && that.parent != nullptr &&
           *parent == *that.parent));
}

std::unique_ptr<DexPosition> DexPosition::make_synthetic_entry_position(
    const DexMethod* method) {
  const auto* method_str = DexString::make_string(show_deobfuscated(method));

  // For source, see if the class has a source.
  const DexString* source = nullptr;
  auto* cls = type_class(method->get_class());
  if (cls != nullptr) {
    source = cls->get_source_file();
  }
  // Fall back to "UnknownSource".
  if (source == nullptr) {
    source = DexString::make_string("UnknownSource");
  }

  return std::make_unique<DexPosition>(method_str, source, 0);
}

std::unique_ptr<DexPosition> DexPosition::make_synthetic_position(
    const DexString* method_name) {
  return std::make_unique<DexPosition>(
      method_name, DexString::make_string("UnknownSource"), 0);
}

PositionPatternSwitchManager::PositionPatternSwitchManager()
    : m_pattern_string(DexString::make_string("Lredex/$Position;.pattern:()V")),
      m_switch_string(DexString::make_string("Lredex/$Position;.switch:()V")),
      m_unknown_source_string(DexString::make_string("UnknownSource")),
      m_redex_generated_string(DexString::make_string("RedexGenerated")) {}

DexPosition* PositionPatternSwitchManager::internalize(DexPosition* pos) {
  always_assert(pos);
  // An interned position is its own hash key, so it must never be mutated
  // afterwards -- and `process_position_alternatives` does rewrite the line
  // of every switch position it emits. That is safe only because a pattern or
  // switch position never reaches here, which is what this checks. Enabling
  // CAN_OUTLINED_METHOD_INVOKE_OUTLINED_METHOD is what would break it.
  always_assert_log(!is_pattern_position(pos) && !is_switch_position(pos),
                    "interning a synthetic pattern/switch position; its line "
                    "is rewritten at output time, which would corrupt the key "
                    "it is stored under");
  m_internalize_calls.fetch_add(1, std::memory_order_relaxed);
  // Copy ctor, not the (method, file, line) ctor: that one always_asserts a
  // non-null file, and a parent in the chain may legitimately have none.
  DexPosition probe(*pos);
  probe.clear_provenance();
  if (pos->parent != nullptr) {
    // Bottom-up, so the probe's parent is already canonical when it is hashed.
    probe.parent = internalize(pos->parent);
  }
  // No `std::move`: DexPosition is trivially copyable -- a static_assert here
  // keeps it that way -- so moving is a copy and clang-tidy flags it.
  return m_positions.insert_unsafe(probe).first;
}

DexPosition* PositionPatternSwitchManager::snapshot_candidate(
    const DexPosition* pos, bool clear_own_provenance) {
  always_assert(pos);
  always_assert_log(!is_pattern_position(pos) && !is_switch_position(pos),
                    "snapshotting a synthetic pattern/switch position");
  DexPosition snapshot(*pos);
  if (clear_own_provenance) {
    snapshot.clear_provenance();
  }
  if (pos->parent != nullptr) {
    snapshot.parent = snapshot_candidate(pos->parent);
  }
  return m_candidate_positions.insert_unsafe(snapshot).first;
}

// A fileless position (a class without a SourceFile attribute) names no site,
// and the line map cannot emit it as a candidate record. The `RedexGenerated`
// position at the start of a method Redex created (an outlined or split-out
// method, a `MethodCreator` method) names no source method. Pattern and switch
// positions are wire records whose lines are ids. Any of these anywhere in the
// inlining chain disqualifies the chain.
bool PositionPatternSwitchManager::names_no_source(
    const DexPosition* pos) const {
  for (; pos != nullptr; pos = pos->parent) {
    if (pos->file == nullptr || pos->file == m_redex_generated_string ||
        is_pattern_position(pos) || is_switch_position(pos)) {
      return true;
    }
  }
  return false;
}

namespace {

// Synthetic is not unreliable: a slot on line 0 names no source line, but it
// does not stand for several either.
bool chain_is_unreliable(const DexPosition* pos) {
  for (; pos != nullptr; pos = pos->parent) {
    if (pos->is_unreliable()) {
      return true;
    }
  }
  return false;
}

} // namespace

uint32_t PositionPatternSwitchManager::make_pattern(
    PositionPattern pos_pattern, std::vector<DexPosition*>* slot_provenance) {
  if (slot_provenance != nullptr) {
    slot_provenance->clear();
    slot_provenance->reserve(pos_pattern.size());
  }
  for (auto& pos : pos_pattern) {
    always_assert(pos);
    always_assert(pos->file);
    // Read before interning, which keeps identity only.
    auto* provenance =
        chain_is_unreliable(pos) ? snapshot_candidate(pos) : nullptr;
    if (slot_provenance != nullptr) {
      slot_provenance->push_back(provenance);
    }
    pos = internalize(pos);
  }
  auto it = m_patterns_map.find(pos_pattern);
  if (it == m_patterns_map.end()) {
    it = m_patterns_map.emplace(pos_pattern, m_patterns.size()).first;
    m_patterns.push_back(std::move(pos_pattern));
  }
  return it->second;
}

uint32_t PositionPatternSwitchManager::make_switch(PositionSwitch pos_switch) {
  return make_alternatives(PositionAlternatives{
      PositionAlternativesSelection::ByPattern, std::move(pos_switch)});
}

uint32_t PositionPatternSwitchManager::make_alternatives(
    PositionAlternatives alternatives) {
  const bool by_pattern =
      alternatives.selection == PositionAlternativesSelection::ByPattern;
  for (auto& alternative : alternatives.entries) {
    always_assert(alternative.position);
    always_assert(alternative.position->file);
    always_assert_log(
        alternative.pattern_id.has_value() == by_pattern,
        "a ByPattern alternative needs a discriminator and an All alternative "
        "has none");
    if (!by_pattern) {
      always_assert_log(alternative.provenance == nullptr,
                        "a candidate set member carries no slot provenance");
      alternative.position = snapshot_candidate(alternative.position);
      continue;
    }
    // A caller may hand over the slot's original position instead of its
    // provenance snapshot; what that position knows is kept all the same.
    if (alternative.provenance == nullptr &&
        chain_is_unreliable(alternative.position)) {
      alternative.provenance = alternative.position;
    }
    if (alternative.provenance != nullptr) {
      // Idempotent on a snapshot, so the pointer stays canonical.
      alternative.provenance = snapshot_candidate(alternative.provenance);
      redex_assert(*alternative.provenance == *alternative.position);
    }
    alternative.position = internalize(alternative.position);
  }
  std::lock_guard<std::mutex> lock(m_registration_mutex);
  auto it = m_alternatives_map.find(alternatives);
  if (it == m_alternatives_map.end()) {
    it = m_alternatives_map.emplace(alternatives, m_alternatives.size()).first;
    m_alternatives.push_back(std::move(alternatives));
  }
  return it->second;
}

namespace {

struct PositionNodeKey {
  std::string_view file;
  uint32_t line;
  std::string_view method;
  bool unreliable;
  std::vector<std::vector<PositionNodeKey>> alternatives;

  bool operator==(const PositionNodeKey& other) const {
    return std::tie(file, line, method, unreliable, alternatives) ==
           std::tie(other.file, other.line, other.method, other.unreliable,
                    other.alternatives);
  }
  bool operator<(const PositionNodeKey& other) const {
    return std::tie(file, line, method, unreliable, alternatives) <
           std::tie(other.file, other.line, other.method, other.unreliable,
                    other.alternatives);
  }
};
using PositionKey = std::vector<PositionNodeKey>;

enum class KeyContent : uint8_t {
  // Method, file and line at every level of the inlining chain.
  Identity,
  // Identity plus provenance, including the content of any alternatives
  // nested on the chain.
  IdentityAndProvenance,
};

// What a position says, all the way up its inlining chain. The recursive
// content, rather than the registration-time alt id, keeps ordering
// deterministic.
PositionKey position_key(
    const PositionPatternSwitchManager& manager,
    const DexPosition* pos,
    KeyContent content = KeyContent::IdentityAndProvenance) {
  const bool with_provenance = content == KeyContent::IdentityAndProvenance;
  PositionKey key;
  for (; pos != nullptr; pos = pos->parent) {
    PositionNodeKey node{
        pos->file == nullptr ? std::string_view() : pos->file->str(),
        pos->line,
        pos->method == nullptr ? std::string_view() : pos->method->str(),
        with_provenance && pos->is_unreliable(),
        {}};
    if (with_provenance && pos->alt_id() != 0) {
      const auto& alt_set = manager.get_alt_set(pos->alt_id());
      node.alternatives.reserve(alt_set.members.size());
      for (auto* member : alt_set.members) {
        node.alternatives.push_back(position_key(manager, member));
      }
      std::sort(node.alternatives.begin(), node.alternatives.end());
    }
    key.push_back(std::move(node));
  }
  return key;
}

// What one alternatives group says, including how its entries are selected.
using AlternativesKey = std::pair<
    uint8_t,
    std::vector<std::tuple<std::optional<uint32_t>, PositionKey, PositionKey>>>;

AlternativesKey alternatives_key(
    const PositionPatternSwitchManager& manager,
    const std::vector<PositionAlternatives>& alternatives,
    uint32_t alternatives_id) {
  const auto& group = alternatives.at(alternatives_id);
  AlternativesKey key;
  key.first = static_cast<uint8_t>(group.selection);
  key.second.reserve(group.entries.size());
  for (const auto& entry : group.entries) {
    // `provenance` is part of the group's identity, so it has to be part of
    // its order too: two groups differing only there would otherwise compare
    // equal and be emitted in whatever order registration happened to assign.
    key.second.emplace_back(entry.pattern_id,
                            entry.provenance == nullptr
                                ? PositionKey()
                                : position_key(manager, entry.provenance),
                            position_key(manager, entry.position));
  }
  return key;
}

} // namespace

PositionPattern PositionPatternSwitchManager::canonical_members(
    const std::vector<DexPosition*>& members) {
  std::vector<std::pair<PositionKey, DexPosition*>> keyed;
  keyed.reserve(members.size());
  for (auto* member : members) {
    keyed.emplace_back(position_key(*this, member, KeyContent::Identity),
                       member);
  }
  std::sort(keyed.begin(), keyed.end(),
            [](const auto& a, const auto& b) { return a.first < b.first; });
  PositionPattern result;
  result.reserve(keyed.size());
  for (size_t i = 0; i < keyed.size();) {
    auto* member = keyed[i].second;
    size_t end = i + 1;
    // The join is commutative, so the order of equal keys does not matter.
    for (; end < keyed.size() && keyed[end].first == keyed[i].first; ++end) {
      if (keyed[end].second != member) {
        member = join_chains(member, keyed[end].second);
      }
    }
    result.push_back(member);
    i = end;
  }
  return result;
}

DexPosition* PositionPatternSwitchManager::join_chains(
    const DexPosition* kept, const DexPosition* other) {
  always_assert(kept);
  DexPosition joined(*kept);
  if (kept->parent != nullptr) {
    joined.parent =
        join_chains(kept->parent, other == nullptr ? nullptr : other->parent);
  }
  // A level `other` does not have, or has with callers `kept` does not show,
  // is a different place too.
  const bool same_place = other != nullptr && other->method == kept->method &&
                          other->file == kept->file &&
                          other->line == kept->line &&
                          (kept->parent != nullptr || other->parent == nullptr);
  auto uncaptured = [](const DexPosition* pos) {
    return pos->is_unreliable() && pos->alt_id() == 0;
  };
  if (!same_place || uncaptured(kept) || uncaptured(other)) {
    joined.mark_unreliable_without_candidates();
  } else if (other->alt_id() != 0 && other->alt_id() != kept->alt_id()) {
    if (kept->alt_id() == 0) {
      joined.m_prov = other->m_prov;
    } else {
      auto members = get_alt_set(kept->alt_id()).members;
      const auto& more = get_alt_set(other->alt_id()).members;
      members.insert(members.end(), more.begin(), more.end());
      joined.set_alt_id(register_alt_set(canonical_members(members)));
    }
  }
  return m_candidate_positions.insert_unsafe(joined).first;
}

positions::FidelityChange PositionPatternSwitchManager::record_candidates(
    DexPosition* survivor, const std::vector<const DexPosition*>& candidates) {
  always_assert(survivor != nullptr);
  std::lock_guard<std::mutex> survivor_lock(survivor_mutex(survivor));
  auto record = compute_candidate_record(survivor, candidates);
  apply_candidate_record(survivor, record);
  return record.became_unreliable ? positions::FidelityChange::BecameUnreliable
                                  : positions::FidelityChange::Unchanged;
}

std::vector<positions::FidelityChange>
PositionPatternSwitchManager::record_candidates_jointly(
    const std::vector<std::pair<DexPosition*, std::vector<const DexPosition*>>>&
        records) {
  // Every survivor's mutex is held for the whole batch, taken in stripe order
  // so that two batches cannot wait on each other.
  std::vector<size_t> stripes;
  stripes.reserve(records.size());
  UnorderedSet<const DexPosition*> survivors;
  for (const auto& [survivor, candidates] : records) {
    always_assert(survivor != nullptr);
    always_assert_log(survivors.insert(survivor).second,
                      "a survivor recorded twice in one batch would lose one "
                      "of its records");
    stripes.push_back(survivor_stripe(survivor));
  }
  std::sort(stripes.begin(), stripes.end());
  stripes.erase(std::unique(stripes.begin(), stripes.end()), stripes.end());
  std::vector<std::unique_lock<std::mutex>> locks;
  locks.reserve(stripes.size());
  for (auto stripe : stripes) {
    locks.emplace_back(m_survivor_mutexes[stripe]);
  }

  std::vector<CandidateRecord> computed;
  computed.reserve(records.size());
  for (const auto& [survivor, candidates] : records) {
    computed.push_back(compute_candidate_record(survivor, candidates));
  }
  std::vector<positions::FidelityChange> changes;
  changes.reserve(records.size());
  for (size_t i = 0; i < records.size(); ++i) {
    apply_candidate_record(records[i].first, computed[i]);
    changes.push_back(computed[i].became_unreliable
                          ? positions::FidelityChange::BecameUnreliable
                          : positions::FidelityChange::Unchanged);
  }
  return changes;
}

void PositionPatternSwitchManager::apply_candidate_record(
    DexPosition* survivor, const CandidateRecord& record) {
  if (record.provenance) {
    survivor->m_prov = *record.provenance;
  }
}

PositionPatternSwitchManager::CandidateRecord
PositionPatternSwitchManager::compute_candidate_record(
    const DexPosition* survivor,
    const std::vector<const DexPosition*>& candidates) {
  // Absorbing: a survivor that already stands for a site nobody captured can
  // never present a complete set again, and there is no partial encoding.
  if (survivor->is_unreliable() && survivor->alt_id() == 0) {
    return {};
  }
  // Every path below that changes the survivor leaves it unreliable.
  const bool became_unreliable = !survivor->is_unreliable();

  // Merging with nothing nameable is itself a loss of fidelity, so an empty
  // request is a report of an uncaptured site rather than a no-op.
  auto names_nothing = [&](const DexPosition* candidate) {
    return candidate == nullptr || names_no_source(candidate) ||
           (candidate->is_unreliable() && candidate->alt_id() == 0);
  };
  DexPosition updated(*survivor);
  if (candidates.empty() ||
      std::any_of(candidates.begin(), candidates.end(), names_nothing)) {
    updated.mark_unreliable_without_candidates();
    return {became_unreliable, updated.m_prov};
  }

  // The places the candidates stand for. A candidate is its own place -- its
  // provenance is not, since whatever set it carried is added here as well.
  // Candidate snapshots preserve provenance further up the chain immutably; the
  // ordinary interner clears it because it is not part of source identity.
  std::vector<DexPosition*> sites;
  sites.reserve(candidates.size());
  for (const auto* candidate : candidates) {
    sites.push_back(
        snapshot_candidate(candidate, /* clear_own_provenance */ true));
    if (auto alt_id = candidate->alt_id()) {
      const auto& inherited = get_alt_set(alt_id);
      sites.insert(sites.end(), inherited.members.begin(),
                   inherited.members.end());
    }
  }
  // The survivor already presents its own place, so a copy of it is not
  // another place. What the copies know about its callers can be more than the
  // survivor's own callers say, and those are shared with other code, so the
  // survivor's place then joins the set itself, its callers joined level by
  // level with every copy's.
  std::vector<DexPosition*> other_places;
  other_places.reserve(sites.size());
  DexPosition* callers = nullptr;
  for (auto* site : sites) {
    if (!(*site == *survivor)) {
      other_places.push_back(site);
    } else if (survivor->parent != nullptr) {
      callers = join_chains(callers != nullptr ? callers : survivor->parent,
                            site->parent);
    }
  }
  sites = std::move(other_places);
  if (callers != nullptr &&
      !same_position_and_provenance(*callers, *survivor->parent)) {
    DexPosition own_place(*survivor);
    own_place.clear_provenance();
    own_place.parent = callers;
    sites.push_back(m_candidate_positions.insert_unsafe(own_place).first);
  }
  if (sites.empty()) {
    // Nothing beyond what the survivor already presents, and nothing went
    // uncaptured, so the survivor makes exactly the claim it made before.
    return {};
  }

  // Preserve the complete membership, not only the capped records. Otherwise a
  // later unique member cannot be distinguished from one dropped by the cap.
  if (auto alt_id = survivor->alt_id()) {
    const auto& inherited = get_alt_set(alt_id);
    sites.insert(sites.end(), inherited.members.begin(),
                 inherited.members.end());
  }
  updated.set_alt_id(register_alt_set(canonical_members(sites)));
  return {became_unreliable, updated.m_prov};
}

uint32_t PositionPatternSwitchManager::register_alt_set(
    PositionPattern members) {
  std::vector<PositionAlternative> entries;
  entries.reserve(std::min(members.size(), kMaxCandidates));
  for (auto* member : members) {
    if (entries.size() == kMaxCandidates) {
      break;
    }
    entries.push_back(PositionAlternative{std::nullopt, member});
  }
  auto alternatives_id = make_alternatives(PositionAlternatives{
      PositionAlternativesSelection::All, std::move(entries)});

  const size_t members_hash = boost::hash_range(members.begin(), members.end());
  std::lock_guard<std::mutex> lock(m_registration_mutex);
  auto it = m_alt_set_ids.find(AltSetMembersKey{members_hash, &members});
  if (it == m_alt_set_ids.end()) {
    auto alt_set = std::make_unique<const AltSet>(
        AltSet{alternatives_id, std::move(members)});
    it = m_alt_set_ids
             .emplace(AltSetMembersKey{members_hash, &alt_set->members},
                      static_cast<uint32_t>(m_alt_sets.size()))
             .first;
    m_alt_sets.push_back(std::move(alt_set));
  }
  return it->second + 1;
}

DexPosition* PositionPatternSwitchManager::join_slot_provenance(
    DexPosition* first, DexPosition* second) {
  if (first == nullptr || first == second) {
    return second;
  }
  if (second == nullptr) {
    return first;
  }
  auto* joined = join_chains(first, second);
  return chain_is_unreliable(joined) ? joined : nullptr;
}

DexPosition* PositionPatternSwitchManager::mark_slot_uncaptured(
    const DexPosition* pos) {
  always_assert(pos);
  DexPosition leaf(*pos);
  leaf.parent =
      pos->parent != nullptr ? snapshot_candidate(pos->parent) : nullptr;
  leaf.mark_unreliable_without_candidates();
  return m_candidate_positions.insert_unsafe(leaf).first;
}

std::unique_ptr<DexPosition>
PositionPatternSwitchManager::make_pattern_position(uint32_t pattern_id) const {
  always_assert(pattern_id < m_patterns.size());
  return std::make_unique<DexPosition>(m_pattern_string,
                                       m_unknown_source_string, pattern_id);
}

std::unique_ptr<DexPosition> PositionPatternSwitchManager::make_switch_position(
    uint32_t switch_id) const {
  always_assert(switch_id < m_alternatives.size());
  return std::make_unique<DexPosition>(m_switch_string, m_unknown_source_string,
                                       switch_id);
}

void RealPositionMapper::register_position(DexPosition* pos) {
  always_assert(pos->file);
  auto [_, emplaced] = m_pos_line_map.emplace(pos, -1);
  if (emplaced) {
    m_possibly_incomplete_positions.push(pos);
  }
}

int64_t RealPositionMapper::add_position(DexPosition* pos) {
  auto [it, _] = m_pos_line_map.emplace(pos, -1);
  if (it->second == -1) {
    it->second = static_cast<int64_t>(m_positions.size());
    m_positions.push_back(pos);
  }
  return it->second;
}

uint32_t RealPositionMapper::get_line(DexPosition* pos) {
  return static_cast<uint32_t>(m_pos_line_map.at(pos) + 1);
}

uint32_t RealPositionMapper::position_to_line(DexPosition* pos) {
  return static_cast<uint32_t>(add_position(pos) + 1);
}

void RealPositionMapper::write_map() {
  if (!m_filename_v2.empty()) {
    write_map_v2();
  }
}

void RealPositionMapper::process_position_alternatives() {
  auto* manager = g_redex->get_position_pattern_switch_manager();
  if (manager->empty()) {
    return;
  }

  // Registration is complete before map writing starts, so this snapshot stays
  // immutable while the parallel reachability walk reads it.
  auto alternatives = manager->get_alternatives();
  // The patterns whose call sites code still refers to, and the groups code or
  // a candidate set refers to.
  InsertOnlyConcurrentSet<uint32_t> reachable_patterns;
  InsertOnlyConcurrentSet<uint32_t> reachable_alternatives;
  InsertOnlyConcurrentSet<DexPosition*> visited;
  std::function<void(DexPosition*)> visit;
  visit = [&](DexPosition* pos) {
    always_assert(pos);
    for (; (pos != nullptr) && visited.insert(pos).second; pos = pos->parent) {
      if (pos->alt_id() != 0) {
        const auto& alt_set = manager->get_alt_set(pos->alt_id());
        if (reachable_alternatives.insert(alt_set.alternatives_id).second) {
          const auto& group = alternatives.at(alt_set.alternatives_id);
          always_assert(group.selection == PositionAlternativesSelection::All);
          for (const auto& entry : group.entries) {
            visit(entry.position);
          }
        }
      }

      if (manager->is_pattern_position(pos)) {
        reachable_patterns.insert(pos->line);
      } else if (manager->is_switch_position(pos)) {
        always_assert(alternatives.at(pos->line).selection ==
                      PositionAlternativesSelection::ByPattern);
        reachable_alternatives.insert(pos->line);
      }
    }
  };

  // First everything code refers to, which settles which patterns are still
  // called. A switch can outlive the call site of one of its patterns, and that
  // pattern's case is then dead.
  workqueue_run<DexPosition*>(visit, m_positions);
  // Then the cases of the called patterns. A case's chain is interned or a
  // snapshot, never a pattern or switch position, so this reaches no further
  // pattern or switch, only candidate sets, whose reachability `visit` closes:
  // emitted records can add no group this walk has not already visited.
  std::vector<DexPosition*> cases;
  for (uint32_t alternatives_id = 0; alternatives_id < alternatives.size();
       ++alternatives_id) {
    const auto& group = alternatives[alternatives_id];
    if (group.selection != PositionAlternativesSelection::ByPattern ||
        reachable_alternatives.count(alternatives_id) == 0u) {
      continue;
    }
    for (const auto& entry : group.entries) {
      always_assert(entry.pattern_id.has_value());
      if (reachable_patterns.count(*entry.pattern_id) != 0u) {
        cases.push_back(entry.emitted_position());
      }
    }
  }
  workqueue_run<DexPosition*>(visit, cases);

  const auto* count_string =
      DexString::make_string("Lredex/$Position;.count:()V");
  const auto* case_string =
      DexString::make_string("Lredex/$Position;.case:()V");
  const auto* unknown_source_string = DexString::make_string("UnknownSource");

  std::vector<std::pair<AlternativesKey, uint32_t>> emission_order;
  for (uint32_t alternatives_id = 0; alternatives_id < alternatives.size();
       ++alternatives_id) {
    if (reachable_alternatives.count(alternatives_id) != 0u) {
      emission_order.emplace_back(
          alternatives_key(*manager, alternatives, alternatives_id),
          alternatives_id);
    }
  }
  std::sort(emission_order.begin(), emission_order.end(),
            [](const auto& a, const auto& b) { return a.first < b.first; });

  UnorderedMap<uint32_t, uint32_t> alternatives_line_map;
  for (const auto& [_, alternatives_id] : emission_order) {
    const auto& group = alternatives.at(alternatives_id);
    const bool by_pattern =
        group.selection == PositionAlternativesSelection::ByPattern;
    std::vector<PositionAlternative> reachable_entries;
    for (const auto& entry : group.entries) {
      always_assert(entry.pattern_id.has_value() == by_pattern);
      if (by_pattern && reachable_patterns.count(*entry.pattern_id) == 0u) {
        continue;
      }
      // The selected position is interned and identity-only, and its record
      // is shared by every switch that selects it. An entry that knows more
      // emits its provenance snapshot instead: a record chain of its own that
      // carries each level's candidate set or uncaptured mark, which the
      // trailer then reports.
      PositionAlternative emitted = entry;
      emitted.position = entry.emitted_position();
      for (auto* pos = emitted.position;
           (pos != nullptr) && (pos->file != nullptr);
           pos = pos->parent) {
        auto [it, emplaced] = m_pos_line_map.emplace(pos, m_positions.size());
        if (emplaced) {
          m_positions.push_back(pos);
        } else {
          always_assert(it->second != -1);
        }
      }
      reachable_entries.push_back(emitted);
    }
    if (by_pattern) {
      std::sort(reachable_entries.begin(), reachable_entries.end(),
                [](const PositionAlternative& a, const PositionAlternative& b) {
                  return *a.pattern_id < *b.pattern_id;
                });
    }

    alternatives_line_map.emplace(alternatives_id, m_positions.size());
    {
      auto* count_pos = new DexPosition(count_string, unknown_source_string,
                                        reachable_entries.size());
      m_owned_auxiliary_positions.emplace_back(count_pos);
      add_position(count_pos);
    }
    for (const auto& entry : reachable_entries) {
      auto* case_pos =
          new DexPosition(case_string, unknown_source_string,
                          by_pattern ? *entry.pattern_id : uint32_t{0});
      m_owned_auxiliary_positions.emplace_back(case_pos);
      always_assert(entry.position);
      always_assert(entry.position->file);
      case_pos->parent = entry.position;
      add_position(case_pos);
    }
  }

  // Only outliner switch positions carry an alternatives id in their line;
  // candidate sets are referenced from the trailer instead.
  for (auto* pos : m_positions) {
    if (manager->is_switch_position(pos)) {
      pos->line = alternatives_line_map.at(pos->line);
    }
  }

  m_alternatives_record_indices = std::move(alternatives_line_map);
}

uint32_t RealPositionMapper::size() const { return m_positions.size(); }

void RealPositionMapper::write_map_v2() {
  // to ensure that the line numbers in the Dex are as compact as possible,
  // we put the emitted positions at the start of the list and rest at the end
  while (!m_possibly_incomplete_positions.empty()) {
    auto* pos = m_possibly_incomplete_positions.front();
    m_possibly_incomplete_positions.pop();
    auto& line = m_pos_line_map[pos];
    if (line == -1) {
      auto idx = m_positions.size();
      m_positions.emplace_back(pos);
      line = static_cast<int64_t>(idx);
    }
  }

  process_position_alternatives();

  /*
   * Map file layout:
   * 0xfaceb000 (magic number)
   * version (4 bytes)
   * string_pool_size (4 bytes)
   * string_pool[string_pool_size]
   * positions_size (4 bytes)
   * positions[positions_size] -- the positions code refers to, followed by
   *   the `count`/`case` records of outliner switches and candidate sets
   * optionally, the provenance trailer -- see `namespace position_map`. Known
   * count-driven readers stop after the declared positions array and ignore the
   * optional suffix.
   *
   * Each member of the string pool is encoded as follows:
   * string_length (4 bytes)
   * char[string_length]
   */

  // We initially build a somewhat dense mapping of strings to ids; the exact
  // ids are not deterministic, and there might be some skipped ids due to
  // races.
  InsertOnlyConcurrentMap<std::string_view, uint32_t> semi_dense_string_ids;
  InsertOnlyConcurrentMap<uint32_t, std::unique_ptr<std::string>> string_pool;
  std::atomic<uint32_t> next_semi_dense_string_id{0};
  auto semi_dense_id_of_string = [&](std::string_view s) -> uint32_t {
    // Fast path
    const uint32_t* opt_id = semi_dense_string_ids.get(s);
    if (opt_id != nullptr) {
      return *opt_id;
    }

    // Slow path
    auto id = next_semi_dense_string_id.fetch_add(1);
    always_assert(id < std::numeric_limits<uint32_t>::max());
    auto p = std::make_unique<std::string>(s);
    auto [id_ptr, emplaced] = semi_dense_string_ids.emplace(*p, id);
    if (emplaced) {
      string_pool.emplace(id, std::move(p));
    } // else, we wasted a string-id. Oh well... We'll renumber densely later.
    return *id_ptr;
  };

  // Many DexPositions refer to the same method. We cache its class and method
  // string ids.
  struct MethodInfo {
    uint32_t class_id;
    uint32_t method_id;
    bool operator==(const MethodInfo& other) const {
      return class_id == other.class_id && method_id == other.method_id;
    }
  };
  InsertOnlyConcurrentMap<const DexString*, MethodInfo> method_infos;
  auto get_method_info = [&](const DexString* method) -> const MethodInfo& {
    return *method_infos
                .get_or_create_and_assert_equal(
                    method,
                    [&semi_dense_id_of_string](auto* m) {
                      // of the form
                      // "class_name.method_name:(arg_types)return_type"
                      const auto full_method_name = m->str();
                      // strip out the args and return type
                      const auto qualified_method_name =
                          full_method_name.substr(0,
                                                  full_method_name.find(':'));
                      auto class_name = java_names::internal_to_external(
                          qualified_method_name.substr(
                              0, qualified_method_name.rfind('.')));
                      auto method_name = qualified_method_name.substr(
                          qualified_method_name.rfind('.') + 1);
                      auto class_id = semi_dense_id_of_string(class_name);
                      auto method_id = semi_dense_id_of_string(method_name);
                      return MethodInfo{class_id, method_id};
                    })
                .first;
  };

  std::atomic<size_t> unregistered_parent_positions{0};

  static_assert(std::is_same<decltype(m_positions[0]->line), uint32_t>::value);
  static_assert(
      std::is_same<decltype(semi_dense_id_of_string("")), uint32_t>::value);
  std::vector<uint32_t> pos_data(5 * m_positions.size());

  // We process positions in parallel in batches to benefit from cache locality.
  const size_t BATCH_SIZE = 100;
  workqueue_run_for<size_t>(
      0, (m_positions.size() + BATCH_SIZE - 1) / BATCH_SIZE, [&](size_t batch) {
        auto end = std::min(m_positions.size(), (batch + 1) * BATCH_SIZE);
        for (size_t idx = batch * BATCH_SIZE; idx < end; ++idx) {
          auto* pos = m_positions[idx];
          uint32_t parent_line = 0;
          try {
            parent_line = pos->parent == nullptr ? 0 : get_line(pos->parent);
          } catch (std::out_of_range&) {
            ++unregistered_parent_positions;
            TRACE(OPUT, 1, "Parent position %s of %s was not registered",
                  SHOW(pos->parent), SHOW(pos));
          }
          auto [class_id, method_id] = get_method_info(pos->method);
          auto file_id = semi_dense_id_of_string(pos->file->str());
          pos_data[5 * idx + 0] = class_id;
          pos_data[5 * idx + 1] = method_id;
          pos_data[5 * idx + 2] = file_id;
          pos_data[5 * idx + 3] = pos->line;
          pos_data[5 * idx + 4] = parent_line;
        }
      });
  always_assert(pos_data.size() == 5 * m_positions.size());
  always_assert(semi_dense_string_ids.size() == string_pool.size());

  if (unregistered_parent_positions.load() > 0 && !traceEnabled(OPUT, 1)) {
    TRACE(OPUT, 0,
          "%zu parent positions had not been registered. Run with TRACE=OPUT:1 "
          "to list them.",
          unregistered_parent_positions.load());
  }

  std::ofstream ofs(m_filename_v2.c_str(),
                    std::ofstream::out | std::ofstream::binary |
                        std::ofstream::trunc);
  uint32_t magic = 0xfaceb000; // serves as endianness check
  ofs.write(reinterpret_cast<const char*>(&magic), sizeof(magic));
  uint32_t version = 2;
  ofs.write(reinterpret_cast<const char*>(&version), sizeof(version));
  uint32_t spool_count = static_cast<uint32_t>(string_pool.size());
  ofs.write(reinterpret_cast<const char*>(&spool_count), sizeof(spool_count));
  always_assert(string_pool.size() < std::numeric_limits<uint32_t>::max());

  // Finally, rewrite the string-ids following the deterministic ordering of the
  // positions.
  auto map = std::make_unique<uint32_t[]>(next_semi_dense_string_id.load());
  const uint32_t unmapped = 0;
  const uint32_t first_mapped = 1;
  uint32_t next_mapped = first_mapped;
  auto order = [&](uint32_t& string_id) {
    auto& mapped = map[string_id];
    if (mapped == unmapped) {
      const auto& s = string_pool.at(string_id);
      uint32_t ssize = static_cast<uint32_t>(s->size());
      ofs.write(reinterpret_cast<const char*>(&ssize), sizeof(ssize));
      ofs.write(s->data(), static_cast<std::streamsize>(ssize * sizeof(char)));
      mapped = next_mapped++;
    }
    string_id = mapped - first_mapped;
  };
  for (size_t idx = 0; idx < m_positions.size(); ++idx) {
    order(pos_data[5 * idx + 0]); // class_id
    order(pos_data[5 * idx + 1]); // method_id
    order(pos_data[5 * idx + 2]); // file_id
  }
  always_assert(next_mapped - first_mapped == string_pool.size());
  uint32_t pos_count = static_cast<uint32_t>(m_positions.size());
  ofs.write(reinterpret_cast<const char*>(&pos_count), sizeof(pos_count));
  ofs.write(reinterpret_cast<const char*>(pos_data.data()),
            static_cast<std::streamsize>(sizeof(uint32_t) * pos_data.size()));

  write_provenance_trailer(ofs);
  ofs.flush();
  always_assert_log(ofs.good(), "failed to write the line-number map to disk");

  TRACE(OPUT, 2,
        "positions: %zu, string pool size: %zu, semi-dense string ids: %u",
        m_positions.size(), string_pool.size(),
        next_semi_dense_string_id.load());
}

void RealPositionMapper::write_provenance_trailer(std::ofstream& ofs) {
  // `m_positions` is walked in index order, so the entries come out sorted by
  // record index without a sort, and identically on every run.
  std::vector<position_map::ProvenanceEntry> entries;
  for (size_t idx = 0; idx < m_positions.size(); ++idx) {
    auto* pos = m_positions[idx];
    always_assert(idx <= std::numeric_limits<uint32_t>::max());
    if (!pos->is_unreliable()) {
      continue;
    }

    uint32_t alt_record_index = 0;
    uint32_t total_candidates = 0;
    if (pos->alt_id() != 0) {
      const auto& alt_set =
          g_redex->get_position_pattern_switch_manager()->get_alt_set(
              pos->alt_id());
      auto it = m_alternatives_record_indices.find(alt_set.alternatives_id);
      // A dangling index would be silent: the entry would point into the
      // positions array at whatever record happens to sit there. This is the
      // check that the seeding above actually reached this set.
      always_assert_log(it != m_alternatives_record_indices.end(),
                        "alt set %u for position record %zu has no emitted "
                        "candidate records",
                        pos->alt_id(), idx);
      alt_record_index = it->second;
      // Index 0 is always one of the positions registered from code, because
      // candidate records are appended only here, after all of those. So 0 can
      // never be a real candidate record, which is what lets it mean "the sites
      // this line stands for were not captured".
      always_assert(alt_record_index != 0);
      // Only reported when the list was actually cut down. Otherwise the reader
      // can count the records it was given, and saying so again would put a
      // second copy of the same number on every ambiguous row.
      total_candidates = alt_set.total_candidates() >
                                 PositionPatternSwitchManager::kMaxCandidates
                             ? alt_set.total_candidates()
                             : 0;
    }
    entries.push_back(position_map::ProvenanceEntry{
        static_cast<uint32_t>(idx), alt_record_index, total_candidates});
  }

  if (entries.empty()) {
    // With no unreliable positions, the declared v2 body ends at EOF; even an
    // empty trailer would add bytes without carrying information.
    return;
  }

  auto current_offset = [&](const char* description) {
    always_assert_log(ofs.good(),
                      "failed to determine line-map output offset before %s",
                      description);
    const auto offset = ofs.tellp();
    always_assert_log(offset != std::streampos(-1),
                      "failed to determine line-map output offset before %s",
                      description);
    return static_cast<uint64_t>(static_cast<std::streamoff>(offset));
  };
  const auto section_offset = current_offset("provenance section offset");
  const auto section_length =
      static_cast<uint64_t>(entries.size() * sizeof(entries[0]));
  ofs.write(reinterpret_cast<const char*>(entries.data()),
            static_cast<std::streamsize>(section_length));

  const auto directory_offset = current_offset("provenance directory offset");
  position_map::SectionEntry entry{
      static_cast<uint32_t>(position_map::SectionTag::Provenance),
      /* reserved */ 0, section_offset, section_length};
  ofs.write(reinterpret_cast<const char*>(&entry), sizeof(entry));

  position_map::Trailer trailer{directory_offset, /* section_count */ 1,
                                position_map::kTrailerMagic};
  ofs.write(reinterpret_cast<const char*>(&trailer), sizeof(trailer));

  TRACE(OPUT, 2, "provenance: %zu of %zu positions are unreliable",
        entries.size(), m_positions.size());
}

PositionMapper* PositionMapper::make(const std::string& map_filename_v2) {
  if (map_filename_v2.empty()) {
    // If no path is provided for the map, just pass the original line numbers
    // through to the output. This does mean that the line numbers will be
    // incorrect for inlined code.
    return new NoopPositionMapper();
  } else {
    return new RealPositionMapper(map_filename_v2);
  }
}

const DexString* RealPositionMapper::get_source_file(const DexClass*) {
  // Note: When remapping line numbers, we don't simply emit DEX_NO_INDEX for
  // the source_file_idx because that would cause stack traces to print
  // "at com.foo.bar (Unknown source)" even when line number data is
  // available. So we make the source_file_idx point at an empty string
  // instead.
  return DexString::make_string("");
}

const DexString* NoopPositionMapper::get_source_file(const DexClass* clz) {
  return clz->get_source_file();
}
