/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <vector>

#include "DeterministicContainers.h"
#include "PositionJoin.h"

class DexMethod;

namespace positions {

// Marks positions governing throwing instructions in a survivor whose body now
// represents another source method as well. The CFG must already be built.
// Marking is independent of stats; callers that count missing positions must
// invoke this once per survivor.
//
// This says only that attribution is ambiguous. A caller holding victims whose
// throwing instructions correspond to the survivor's wants
// `join_throwing_positions` instead, which compares the actual lines.
void mark_ambiguous_throwing_positions(DexMethod* survivor,
                                       JoinStats* join_stats);

// Joins each position governing a throwing instruction in `survivor` with the
// position governing the corresponding throwing instruction in each victim, so
// a line the victims agree on keeps identifying its source. The victim
// positions folded into one surviving position are gathered across all victims
// first, so each surviving position is joined in one place.
//
// The victims must be instruction-identical to `survivor` and must still hold
// their code with a built CFG: their positions are read here. A victim that
// turns out not to correspond falls back to marking the whole survivor.
void join_throwing_positions(DexMethod* survivor,
                             const std::vector<DexMethod*>& victims,
                             JoinStats* join_stats);

// `join_throwing_positions` for the members of `group`, other than `survivor`,
// that are not yet in `already_joined` -- the victims already joined into
// `survivor` -- and adds them there. A survivor can be retained again by a
// later round of deduplication, bringing victims an earlier round did not;
// keying on the pair joins those later victims while joining no pair twice.
template <typename Group>
void join_new_throwing_positions(DexMethod* survivor,
                                 const Group& group,
                                 UnorderedSet<DexMethod*>* already_joined,
                                 JoinStats* join_stats) {
  std::vector<DexMethod*> victims;
  for (auto* victim : group) {
    if (victim != survivor && already_joined->insert(victim).second) {
      victims.push_back(victim);
    }
  }
  if (!victims.empty()) {
    join_throwing_positions(survivor, victims, join_stats);
  }
}

} // namespace positions
