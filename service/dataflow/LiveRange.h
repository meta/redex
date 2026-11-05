/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <cstdint>
#include <optional>

#include <boost/functional/hash.hpp>

#include <sparta/PatriciaTreeSet.h>

#include "ControlFlow.h"
#include "DeterministicContainers.h"
#include "IRInstruction.h"
#include "Lazy.h"
#include "ReachingDefinitions.h"

class IRCode;

/*
 * This module renumbers registers so that they represent live ranges. Live
 * ranges are the union of use-def chains that share defs in common. See e.g.
 * Muchnick's Advanced Compiler Design & Implementation, Section 16.3.3 for
 * details.
 */

namespace live_range {

// Every IRInstruction has at most one def, so we can represent defs by
// instructions
using Def = IRInstruction*;

struct Use {
  IRInstruction* insn;
  src_index_t src_index;
  bool operator==(const Use&) const;
};

} // namespace live_range

namespace std {

template <>
struct hash<live_range::Use> {
  size_t operator()(const live_range::Use& use) const {
    size_t seed = boost::hash<IRInstruction*>()(use.insn);
    boost::hash_combine(seed, use.src_index);
    return seed;
  }
};

} // namespace std

namespace live_range {

using UseDefChains = UnorderedMap<Use, sparta::PatriciaTreeSet<Def>>;
using Uses = UnorderedSet<Use>;
using DefUseChains = UnorderedMap<Def, UnorderedSet<Use>>;

class Chains {
 public:
  explicit Chains(const cfg::ControlFlowGraph& cfg,
                  bool ignore_unreachable = false,
                  reaching_defs::Filter filter = nullptr);
  UseDefChains get_use_def_chains() const;
  DefUseChains get_def_use_chains() const;
  const reaching_defs::FixpointIterator& get_fp_iter() const {
    return m_fp_iter;
  }

 private:
  const cfg::ControlFlowGraph& m_cfg;
  reaching_defs::FixpointIterator m_fp_iter;
  bool m_ignore_unreachable;
};

class MoveAwareChains {
 public:
  explicit MoveAwareChains(const cfg::ControlFlowGraph& cfg,
                           bool ignore_unreachable = false,
                           reaching_defs::Filter filter = nullptr);
  UseDefChains get_use_def_chains() const;
  DefUseChains get_def_use_chains() const;
  const reaching_defs::MoveAwareFixpointIterator& get_fp_iter() const {
    return m_fp_iter;
  }

 private:
  const cfg::ControlFlowGraph& m_cfg;
  reaching_defs::MoveAwareFixpointIterator m_fp_iter;
  bool m_ignore_unreachable;
};

struct LazyLiveRanges {
  live_range::MoveAwareChains chains;
  Lazy<live_range::DefUseChains> def_use_chains;
  Lazy<live_range::UseDefChains> use_def_chains;
  explicit LazyLiveRanges(cfg::ControlFlowGraph& cfg)
      : chains(cfg),
        def_use_chains([this] { return chains.get_def_use_chains(); }),
        use_def_chains([this] { return chains.get_use_def_chains(); }) {}
};

/*
 * width_aware means that the renumbering process will allocate 2 slots per
 * wide register. In general, callers should use the default (true) value.
 */
void renumber_registers(IRCode*, bool width_aware = true);

/*
 * The type that `use` requires of the register it reads, given the return type
 * of the method the instruction is in. Returns nullptr when the demand cannot
 * be determined.
 */
const DexType* get_type_demand(DexType* method_rtype, const Use& use);

/*
 * The types that the uses of the receiver of non-static `method` require, or
 * nullopt when one of them cannot be determined.
 */
std::optional<UnorderedSet<const DexType*>> get_receiver_type_demands(
    const DexMethod* method);

/*
 * The one type among `type_demands` that satisfies all of them, or nullptr when
 * there is none.
 */
const DexType* reduce_type_demands(
    const UnorderedSet<const DexType*>& type_demands);

} // namespace live_range
