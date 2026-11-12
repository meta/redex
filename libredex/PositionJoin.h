/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <cstdint>

#include "Debug.h"
#include "DexPosition.h"

/*
 * When a pass folds several pieces of code into one, the surviving code keeps
 * one position and the others are dropped. A stack trace landing on the
 * survivor then reports that one line no matter which original site the crash
 * came from. A pass compares each folded position with the survivor's
 * (`same_source_claim`) and, where they differ, records with `mark_merged`
 * that the surviving line no longer identifies a unique source location.
 *
 * Only merges at instructions that can throw are observable in Java stack
 * traces. Callers apply that filter before comparing.
 *
 * Threading: `mark_merged` mutates the survivor through its owning
 * MethodItemEntry. Parallel walkers hand out whole methods, so one owner is
 * reached from one thread at a time. Writing through a non-owning alias needs
 * separate synchronization.
 *
 * Compositional invariant (inlining): marks on surviving entries copy bytewise,
 * and comparisons cover complete parent chains. `mark_merged` mutates only the
 * survivor pointer it receives and never follows `parent`.
 */
namespace positions {

// What a merge did to the survivor, so callers can count one canonical set of
// metrics.
enum class FidelityChange : uint8_t {
  Unchanged,
  BecameUnreliable,
};

/*
 * Whether two position chains make the same source claim. Position identity
 * deliberately ignores provenance, so this comparison is separate from
 * `DexPosition::operator==` and checks every level of the inlining chain.
 *
 * A null chain makes the same claim only as another null chain: code with no
 * position would have inherited a different position from its predecessor, so
 * folding it into a positioned survivor is still ambiguous.
 *
 * A synthetic level is on line 0, so the line comparison matches it only
 * against an identical synthetic level: two copies of one method's synthetic
 * entry position make the same claim, so code inlined beneath them is not
 * ambiguous. A synthetic victim under any other claim is the same kind of
 * uncertainty as a missing one: it is not a source site, but its code came
 * from somewhere.
 *
 * Two distinct levels never match when either is unreliable; folding against
 * one has to carry its loss of certainty into the survivor.
 */
inline bool same_source_claim(const DexPosition* first,
                              const DexPosition* second) {
  for (; first != nullptr && second != nullptr;
       first = first->parent, second = second->parent) {
    if (first == second) {
      // One shared object: the rest of the chain, and any loss of certainty
      // on it, is already the survivor's own.
      return true;
    }
    if (first->is_unreliable() || second->is_unreliable()) {
      return false;
    }
    if (first->method != second->method || first->file != second->file ||
        first->line != second->line) {
      return false;
    }
  }
  return first == nullptr && second == nullptr;
}

/*
 * Records that code making a different source claim was folded into code
 * governed by `survivor`, which must be non-null. Returns whether that made
 * the survivor unreliable: a survivor that already was has not made the
 * transition again, so counting it would double-count one position.
 * Replacing a sentinel without folding code must not call this.
 *
 * Only the owned survivor leaf is marked. Parent pointers can be shared by
 * every frame beneath an inlined callsite, so this never mutates through those
 * aliases.
 *
 * Any candidate set the survivor carried is dropped, leaving it merged with
 * sites nobody captured: without the folded site the set is no longer the
 * complete membership, and the line map cannot express a partial one. Out of
 * line because candidate sets belong to the manager, which hangs off
 * `RedexContext`.
 */
FidelityChange mark_merged(DexPosition* survivor);

// Accumulates merges and gaps using one vocabulary shared by every producer.
struct JoinStats {
  size_t marked_unreliable{0};
  size_t not_recorded{0};
  // Folds whose throwing instructions could not be paired at all, so every
  // surviving position was joined against nothing rather than against the
  // position it actually folded.
  size_t merged_without_correspondence{0};

  void account(FidelityChange change) {
    if (change == FidelityChange::BecameUnreliable) {
      ++marked_unreliable;
    }
  }

  void count_unrecorded() { ++not_recorded; }

  void count_uncorresponded() { ++merged_without_correspondence; }

  JoinStats& operator+=(const JoinStats& that) {
    marked_unreliable += that.marked_unreliable;
    not_recorded += that.not_recorded;
    merged_without_correspondence += that.merged_without_correspondence;
    return *this;
  }
};

namespace metrics {
constexpr const char* kMarkedUnreliable = "positions_marked_unreliable";
constexpr const char* kNotRecorded = "merges_not_recorded";
constexpr const char* kMergedWithoutCorrespondence =
    "positions_merged_without_correspondence";
} // namespace metrics

} // namespace positions
