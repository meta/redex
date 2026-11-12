/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

/*
 * This pass outlines common instruction sequences within a basic block,
 * and across tree-shaped control-flow structures for size wins. The notion of
 * instruction sequence equivalence is modulo register names.
 *
 * At its core is a rather naive approach: check if any subsequence of
 * instructions in a block occurs sufficiently often. The average complexity is
 * held down by filtering out instruction sequences where adjacent sequences of
 * abstracted instructions ("cores") of fixed lengths never occur twice anywhere
 * in the scope (seems good enough, even without a suffix tree).
 *
 * When reaching a conditional branch or switch instruction, different control-
 * paths are explored as well, as long as they eventually all arrive at a common
 * block. Thus, outline candidates are in fact instruction sequence trees.
 *
 * At its core is a rather naive approach: check if any subsequence of
 * instructions in a block occurs sufficiently often. The average complexity is
 * held down by filtering out instruction sequences where adjacent sequences of
 * abstracted instructions ("cores") of fixed lengths never occur twice anywhere
 * in the scope (seems good enough, even without a suffix tree).
 *
 * We gather existing method/type references in a dex and make sure that we
 * don't go beyond the limits when adding methods/types, effectively filling up
 * the available ref space created by IntraDexInline (minus other reservations).
 *
 * The pass assumes that it runs after InterDex, but before RegAlloc, and
 * ideally before DedupStrings.
 *
 * There are some concessions to reduce the potential of negative runtime
 * performance impact:
 * - Performance sensitive methods (those that are popular in method-profiles,
 *   and loopy code in cold-start classes) are not outlined from
 * - Outlining happens per dex to reduce performance impact (but then later
 *   dexes in the same store can point to outlined code in an earlier dex)
 * - Outlined methods are preferably placed in the same class if all outlined
 *   sequences come from methods of a single class, or a common base class (the
 *   first one in the dex); otherwise, they are placed in a new shared helper
 *   classes (placed at the beginning of the dex)
 * - DedupStrings pass will prefer to also use the same helper class
 *
 * Safety considerations:
 * - Methods with non-minimum api levels are not outlined from.
 * - Code involving cross-store refs is not outlined.
 * - Many other technical limitations, similar in effect to inliner's technical
 *   limitations
 *
 * Ideas for future work:
 * - Retain dex positions
 * - More sophisticated normalization (commutative operations, re-ordering of
 *   independent instructions)
 * - Make outlining a bit fuzzy (e.g. pulling out constants)
 * - More aggressive cross-dex outlining
 * - Other minor TODO ideas in the code
 * - Outline beyond control-flow trees, e.g. DAGs, or even arbitrary
 *   control-flow with try/catches
 */

#include "InstructionSequenceOutliner.h"

#include <algorithm>
#include <map>
#include <memory>
#include <optional>
#include <string>
#include <vector>

#include <boost/format.hpp> // NOLINT

#include "BigBlocks.h"
#include "CFGMutation.h"
#include "ConcurrentContainers.h"
#include "ConfigFiles.h"
#include "Creators.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexClass.h"
#include "DexInstruction.h"
#include "DexLimits.h"
#include "DexPosition.h"
#include "DexStoreUtil.h"
#include "DexUtil.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "InitClassesWithSideEffects.h"
#include "InterDexPassMetrics.h"
#include "Lazy.h"
#include "Liveness.h"
#include "MethodProfiles.h"
#include "MutablePriorityQueue.h"
#include "ObfuscateUtils.h"
#include "OutlinedMethods.h"
#include "OutlinerTypeAnalysis.h"
#include "OutliningProfileGuidanceImpl.h"
#include "PartialCandidates.h"
#include "PassManager.h"
#include "ReachingInitializeds.h"
#include "RedexContext.h"
#include "RefChecker.h"
#include "Resolver.h"
#include "Show.h"
#include "Trace.h"
#include "Walkers.h"

using namespace outliner;

namespace {

using namespace outliner_impl;

constexpr const char* OUTLINED_CLASS_NAME_PREFIX = "Lcom/redex/Outlined$";

// Minimum number of instructions to be outlined in a sequence, used in
// definition of cores
const size_t MIN_INSNS_SIZE = 3;

////////////////////////////////////////////////////////////////////////////////
// "Candidate instructions" with hashes, equality, and stable hashes
////////////////////////////////////////////////////////////////////////////////

// Here, the "core" of an instruction is its opcode and associated data such as
// method/field/string/type/data/literal. This "core" concept is used for
// pruning which instruction sequences occur multiple times. Used or defined
// registers are explicitly left out as those are getting normalized.
struct CandidateInstructionCore {
  IROpcode opcode;
  union {
    DexMethodRef* method;
    DexFieldRef* field;
    const DexString* string;
    const DexType* type;
    DexOpcodeData* data;
    int64_t literal{0};
  };
};
static size_t hash_value(const CandidateInstructionCore& cic) {
  size_t hash = cic.opcode;
  boost::hash_combine(hash, cic.literal);
  return hash;
}
// We define "stable hashes" for instruction sequences to create rather unique
// and stable name string for the outlined methods --- essentially, the outlined
// method name characterizes the outlined instruction sequence. We want these
// names to be stable across Redex runs, and across different Redex (and there-
// fore also boost) versions, so that name-dependent PGO remains relatively
// meaningful even with outlining enabled.
using StableHash = uint64_t;
static StableHash stable_hash_value(const std::string& s) {
  StableHash stable_hash{s.size()};
  for (auto c : s) {
    stable_hash = stable_hash * 3 + c;
  }
  return stable_hash;
}
static StableHash stable_hash_value(const CandidateInstructionCore& cic) {
  StableHash stable_hash{cic.opcode};
  switch (opcode::ref(cic.opcode)) {
  case opcode::Ref::Method:
    return stable_hash * 41 + stable_hash_value(show(cic.method));
  case opcode::Ref::Field:
    return stable_hash * 43 + stable_hash_value(show(cic.field));
  case opcode::Ref::String:
    return stable_hash * 47 + stable_hash_value(show(cic.string));
  case opcode::Ref::Type:
    return stable_hash * 53 + stable_hash_value(show(cic.type));
  case opcode::Ref::Data:
    return stable_hash * 59 + cic.data->size();
  case opcode::Ref::Literal:
    return stable_hash * 61 + cic.literal;
  default:
    return stable_hash;
  }
}
using CandidateInstructionCoreHasher = boost::hash<CandidateInstructionCore>;
bool operator==(const CandidateInstructionCore& a,
                const CandidateInstructionCore& b) {
  return a.opcode == b.opcode && a.literal == b.literal;
}

struct CandidateInstruction {
  CandidateInstructionCore core;
  std::vector<reg_t> srcs;
  std::optional<reg_t> dest;
};
static size_t hash_value(const CandidateInstruction& ci) {
  size_t hash = hash_value(ci.core);
  boost::hash_combine(hash, boost::hash_range(ci.srcs.begin(), ci.srcs.end()));
  if (ci.dest) {
    boost::hash_combine(hash, *ci.dest);
  }
  return hash;
}
static StableHash stable_hash_value(const CandidateInstruction& ci) {
  StableHash stable_hash = stable_hash_value(ci.core);
  for (auto src : ci.srcs) {
    stable_hash = stable_hash * 3 + src;
  }
  return stable_hash;
}
using CandidateInstructionHasher = boost::hash<CandidateInstruction>;
bool operator==(const CandidateInstruction& a, const CandidateInstruction& b) {
  return a.core == b.core && a.srcs == b.srcs && a.dest == b.dest;
}

struct CandidateEdgeLabel {
  cfg::EdgeType type;
  cfg::Edge::MaybeCaseKey case_key;
};
bool operator==(const CandidateEdgeLabel& a, const CandidateEdgeLabel& b) {
  return a.type == b.type && a.case_key == b.case_key;
}
bool operator!=(const CandidateEdgeLabel& a, const CandidateEdgeLabel& b) {
  return !(a == b);
}

struct CandidateNode {
  std::vector<CandidateInstruction> insns;
  std::optional<reg_t> res_reg;
  std::vector<std::pair<CandidateEdgeLabel, std::shared_ptr<CandidateNode>>>
      succs;
};
static size_t hash_value(const CandidateNode& cn) {
  size_t hash = cn.insns.size();
  if (cn.res_reg) {
    boost::hash_combine(hash, *cn.res_reg);
  }
  boost::hash_combine(hash,
                      boost::hash_range(cn.insns.begin(), cn.insns.end()));
  for (const auto& p : cn.succs) {
    boost::hash_combine(hash, *p.second);
  }
  return hash;
}
static StableHash stable_hash_value(const CandidateNode& cn) {
  StableHash stable_hash{cn.insns.size()};
  for (const auto& csi : cn.insns) {
    stable_hash = stable_hash * 73 + stable_hash_value(csi);
  }
  if (cn.res_reg) {
    stable_hash = stable_hash * 79 + *cn.res_reg;
  }
  for (const auto& p : cn.succs) {
    stable_hash = stable_hash * 199 + stable_hash_value(*p.second);
  }
  return stable_hash;
}

using CandidateNodeHasher = boost::hash<CandidateNode>;
bool operator!=(const CandidateNode& a, const CandidateNode& b);
bool operator==(const CandidateNode& a, const CandidateNode& b) {
  if (a.insns != b.insns || a.res_reg != b.res_reg ||
      a.succs.size() != b.succs.size()) {
    return false;
  }
  for (size_t i = 0; i < a.succs.size(); i++) {
    const auto& p = a.succs.at(i);
    const auto& q = b.succs.at(i);
    if (p.first != q.first || *p.second != *q.second) {
      return false;
    }
  }
  return true;
}
bool operator!=(const CandidateNode& a, const CandidateNode& b) {
  return !(a == b);
}

struct Candidate {
  std::vector<const DexType*> arg_types;
  CandidateNode root;
  const DexType* res_type{nullptr};
  size_t size;
  reg_t temp_regs;
};
static size_t hash_value(const Candidate& c) {
  size_t hash = c.size;
  boost::hash_combine(hash, c.root);
  for (const auto* arg_type : c.arg_types) {
    boost::hash_combine(hash, reinterpret_cast<size_t>(arg_type));
  }
  boost::hash_combine(hash, reinterpret_cast<size_t>(c.res_type));
  return hash;
}
static StableHash stable_hash_value(const Candidate& c) {
  StableHash stable_hash{c.arg_types.size()};
  for (const auto* t : c.arg_types) {
    stable_hash = stable_hash * 71 + stable_hash_value(show(t));
  }
  if (c.res_type != nullptr) {
    stable_hash = stable_hash * 73 + stable_hash_value(show(c.res_type));
  }
  stable_hash = stable_hash * 79 + stable_hash_value(c.root);
  return stable_hash;
}

using CandidateHasher = boost::hash<Candidate>;
bool operator==(const Candidate& a, const Candidate& b) {
  if (a.arg_types != b.arg_types || a.root != b.root ||
      a.res_type != b.res_type) {
    return false;
  }

  always_assert(a.size == b.size);
  always_assert(a.temp_regs == b.temp_regs);
  return true;
}

static CandidateInstructionCore to_core(IRInstruction* insn) {
  CandidateInstructionCore core;
  core.opcode = insn->opcode();
  if (insn->has_method()) {
    core.method = insn->get_method();
  } else if (insn->has_field()) {
    core.field = insn->get_field();
  } else if (insn->has_string()) {
    core.string = insn->get_string();
  } else if (insn->has_type()) {
    core.type = insn->get_type();
  } else if (insn->has_literal()) {
    core.literal = insn->get_literal();
  } else if (insn->has_data()) {
    core.data = insn->get_data();
  }
  return core;
}

using CandidateInstructionCores =
    std::array<CandidateInstructionCore, MIN_INSNS_SIZE>;
using CandidateInstructionCoresHasher = boost::hash<CandidateInstructionCores>;
using CandidateInstructionCoresSet =
    UnorderedSet<CandidateInstructionCores, CandidateInstructionCoresHasher>;

// The cores builder efficiently keeps track of the last MIN_INSNS_SIZE many
// instructions.
class CandidateInstructionCoresBuilder {
 public:
  void push_back(IRInstruction* insn) {
    m_buffer[m_start] = to_core(insn);
    m_start = (m_start + 1) % MIN_INSNS_SIZE;
    m_size = m_size < MIN_INSNS_SIZE ? m_size + 1 : MIN_INSNS_SIZE;
  }

  void clear() { m_size = 0; }

  bool has_value() const { return m_size == MIN_INSNS_SIZE; }

  CandidateInstructionCores get_value() {
    always_assert(m_size == MIN_INSNS_SIZE);
    CandidateInstructionCores res;
    for (size_t i = 0; i < MIN_INSNS_SIZE; i++) {
      res[i] = m_buffer.at((m_start + i) % MIN_INSNS_SIZE);
    }
    return res;
  }

 private:
  std::array<CandidateInstructionCore, MIN_INSNS_SIZE> m_buffer;
  size_t m_start{0};
  size_t m_size{0};
};

////////////////////////////////////////////////////////////////////////////////
// Normalization of partial candidate sequence to candidate sequence
////////////////////////////////////////////////////////////////////////////////

using LazyReachingInitializedsEnvironments =
    Lazy<reaching_initializeds::ReachingInitializedsEnvironments>;
using OptionalReachingInitializedsEnvironments =
    std::optional<reaching_initializeds::ReachingInitializedsEnvironments>;

static std::vector<cfg::Edge*> get_ordered_goto_and_branch_succs(
    cfg::Block* block) {
  std::vector<cfg::Edge*> succs =
      block->cfg().get_succ_edges_if(block, [](cfg::Edge* e) {
        return e->type() == cfg::EDGE_GOTO || e->type() == cfg::EDGE_BRANCH;
      });
  std::sort(succs.begin(), succs.end(), [](cfg::Edge* a, cfg::Edge* b) {
    if (a->type() != b->type()) {
      return a->type() < b->type();
    }
    return a->case_key() && *a->case_key() < *b->case_key();
  });
  return succs;
}

static CandidateEdgeLabel normalize(cfg::Edge* e) {
  return CandidateEdgeLabel{e->type(), e->case_key()};
}

// This method turns a tree of actual instructions into a normalized
// candidate instruction tree. The main purpose of normalization is to
// determine a canonical register assignment. Normalization also identifies the
// list and types of incoming arguments. Normalized temporary registers start
// at zero, and normalized argument registers follow after temporary registers
// in the order in which they are referenced by the instructions when walking
// the tree in order.
static Candidate normalize(
    OutlinerTypeAnalysis& type_analysis,
    const PartialCandidate& pc,
    const std::optional<std::pair<reg_t, bool>>& out_reg) {
  UnorderedMap<reg_t, reg_t> map;
  reg_t next_arg{pc.temp_regs};
  reg_t next_temp{0};
  Candidate c;
  c.size = pc.size;
  c.temp_regs = pc.temp_regs;
  std::vector<reg_t> arg_regs;
  auto normalize_use = [&map, &next_arg, &arg_regs](reg_t reg, bool wide) {
    auto it = map.find(reg);
    if (it != map.end()) {
      return it->second;
    }
    reg_t mapped_reg = next_arg;
    next_arg += wide ? 2 : 1;
    map.emplace(reg, mapped_reg);
    arg_regs.push_back(reg);
    return mapped_reg;
  };
  // We keep track of temp registers only needed along some
  // (conditional) control-flow paths.
  using UndoMap = UnorderedMap<reg_t, std::optional<reg_t>>;
  auto normalize_def = [&map, &next_temp](reg_t reg, bool wide,
                                          UndoMap* undo_map) {
    if (undo_map->count(reg) == 0u) {
      auto it = map.find(reg);
      undo_map->emplace(reg, it == map.end()
                                 ? std::nullopt
                                 : std::optional<reg_t>(it->second));
    }
    reg_t mapped_reg = next_temp;
    next_temp += wide ? 2 : 1;
    map[reg] = mapped_reg;
    return mapped_reg;
  };
  std::function<void(const PartialCandidateNode&, CandidateNode* cn,
                     IRInstruction* last_out_reg_assignment_insn)>
      walk;
  UnorderedSet<const IRInstruction*> out_reg_assignment_insns;
  walk = [&map, &normalize_use, &normalize_def, &out_reg,
          &out_reg_assignment_insns,
          &walk](const PartialCandidateNode& pcn, CandidateNode* cn,
                 IRInstruction* last_out_reg_assignment_insn) {
    UndoMap undo_map;
    cn->insns.reserve(pcn.insns.size());
    for (auto* insn : pcn.insns) {
      CandidateInstruction ci;
      ci.core = to_core(insn);

      ci.srcs.reserve(insn->srcs_size());
      for (size_t i = 0; i < insn->srcs_size(); i++) {
        ci.srcs.push_back(normalize_use(insn->src(i), insn->src_is_wide(i)));
      }
      if (insn->has_dest()) {
        ci.dest = normalize_def(insn->dest(), insn->dest_is_wide(), &undo_map);
        if (out_reg && insn->dest() == out_reg->first) {
          last_out_reg_assignment_insn = insn;
        }
      }
      cn->insns.push_back(ci);
    }
    if (pcn.succs.empty() && out_reg) {
      out_reg_assignment_insns.insert(last_out_reg_assignment_insn);
      cn->res_reg = normalize_use(out_reg->first, out_reg->second);
    }
    for (const auto& p : pcn.succs) {
      auto succ_cn = std::make_shared<CandidateNode>();
      cn->succs.emplace_back(normalize(p.first), succ_cn);
      walk(*p.second, succ_cn.get(), last_out_reg_assignment_insn);
    }
    for (auto& p : UnorderedIterable(undo_map)) {
      if (p.second) {
        map[p.first] = *p.second;
      } else {
        map.erase(p.first);
      }
    }
  };
  walk(pc.root, &c.root, nullptr);
  always_assert(next_temp == pc.temp_regs);
  always_assert(!pc.root.insns.empty());
  auto* anchor = pc.root.insns.front();
  Lazy<UnorderedSet<IRInstruction*>> candidate_insns([&pc]() {
    auto res = std::make_unique<UnorderedSet<IRInstruction*>>();
    std::function<void(const PartialCandidateNode&)> gather_insns;
    gather_insns = [&](const PartialCandidateNode& pcn) {
      res->insert(pcn.insns.begin(), pcn.insns.end());
      for (const auto& p : pcn.succs) {
        gather_insns(*p.second);
      }
    };
    gather_insns(pc.root);
    return res;
  });
  auto in_candidate = [&candidate_insns](IRInstruction* insn) {
    return candidate_insns->count(insn) != 0u;
  };
  if (out_reg) {
    always_assert(!out_reg_assignment_insns.empty());
    bool unknown_candidate_type_skip{false};
    std::optional<art::Value> incoming;
    if (out_reg_assignment_insns.count(nullptr) != 0u) {
      // There is a control-flow path where the out-reg is not assigned;
      // fall-back to its value at the beginning of the partial candidate.
      c.res_type =
          art::declare_result(type_analysis.value_at(anchor, out_reg->first));
      // If we still don't know the type, we be conservative and skip this
      // candidate.
      unknown_candidate_type_skip = (c.res_type == nullptr);
      incoming = art::Value::of_type(c.res_type);
      out_reg_assignment_insns.erase(nullptr);
    }
    if (!unknown_candidate_type_skip && !out_reg_assignment_insns.empty()) {
      c.res_type = art::declare_result(type_analysis.value_of_assignments(
          out_reg_assignment_insns, incoming, in_candidate));
    }
  }
  std::optional<std::pair<reg_t, const DexType*>> result;
  if (out_reg) {
    result.emplace(out_reg->first, c.res_type);
  }
  c.arg_types.reserve(arg_regs.size());
  for (auto reg : arg_regs) {
    c.arg_types.push_back(art::declare_parameter(
        type_analysis.demand_in_candidate(pc, reg, result),
        [&]() { return type_analysis.value_at(anchor, reg); }));
  }
  return c;
}

////////////////////////////////////////////////////////////////////////////////
// find_method_candidate_sequences
////////////////////////////////////////////////////////////////////////////////

// A non-empty (ordered) map of range start positions to range sizes.
using Ranges = std::map<size_t, size_t>;

struct CandidateMethodLocation {
  IRInstruction* first_insn;
  cfg::Block* hint_block;
  std::optional<reg_t> out_reg;
  // We use a linear instruction indexing scheme within a method to identify
  // ranges, which we use later to invalidate other overlapping candidates
  // while incrementally processing the most beneficial candidates using a
  // priority queue.
  Ranges ranges;
};

static bool ranges_overlap(const Ranges& a, const Ranges& b) {
  auto range_begin = [](const Ranges::const_iterator& it) { return it->first; };
  auto range_end = [](const Ranges::const_iterator& it) {
    return it->first + it->second;
  };
  for (auto a_it = a.begin(), b_it = b.begin();
       a_it != a.end() && b_it != b.end();) {
    if (range_end(a_it) <= range_begin(b_it)) {
      a_it++;
    } else if (range_end(b_it) <= range_begin(a_it)) {
      b_it++;
    } else {
      return true;
    }
  }
  return false;
}

static bool can_outline_opcode(IROpcode opcode, bool outline_control_flow) {
  switch (opcode) {
  case IOPCODE_LOAD_PARAM:
  case IOPCODE_LOAD_PARAM_OBJECT:
  case IOPCODE_LOAD_PARAM_WIDE:
  case IOPCODE_UNREACHABLE:
  case OPCODE_GOTO:
  case OPCODE_INVOKE_SUPER:
  case OPCODE_MONITOR_ENTER:
  case OPCODE_MONITOR_EXIT:
  case OPCODE_MOVE_EXCEPTION:
  case OPCODE_RETURN:
  case OPCODE_RETURN_OBJECT:
  case OPCODE_RETURN_VOID:
  case OPCODE_RETURN_WIDE:
  case OPCODE_THROW:
  case OPCODE_CMPL_FLOAT:
  case OPCODE_CMPG_FLOAT:
  case OPCODE_CMPL_DOUBLE:
  case OPCODE_CMPG_DOUBLE:
  case OPCODE_CMP_LONG:
    // While the CMP instructions could formally be part of an outlined methods,
    // we ran into issues in the past with the CSE pass, where breaking up
    // CMP and IF instructions caused some obscure issues on some Android
    // versions. So we rather avoid that. It's not a big loss.
    return false;

  default:
    return outline_control_flow || (!opcode::is_a_conditional_branch(opcode) &&
                                    !opcode::is_switch(opcode));
  }
}

// Attempts to append an instruction to a partial candidate sequence. Result
// indicates whether attempt was successful. If not, then the partial
// candidate sequence should be abandoned.
static bool append_to_partial_candidate(
    LazyReachingInitializedsEnvironments& reaching_initialized_new_instances,
    IRInstruction* insn,
    PartialCandidate* pc,
    PartialCandidateNode* pcn,
    const Config& config) {
  auto opcode = insn->opcode();
  if (opcode == OPCODE_INVOKE_DIRECT && method::is_init(insn->get_method())) {
    auto it = pcn->defined_regs.find(insn->src(0));
    if (it == pcn->defined_regs.end()) {
      return false;
    }
    it->second = {/* wide */ false, RegState::INITIALIZED};
  }
  for (size_t i = 0; i < insn->srcs_size(); i++) {
    auto src = insn->src(i);
    if (pcn->defined_regs.count(src) == 0u) {
      pc->in_regs.insert(src);
      if (insn->src_is_wide(i)) {
        pc->in_regs.insert(src + 1);
      }
      if (pc->in_regs.size() > config.max_args) {
        return false;
      }
    }
  }
  if (insn->has_dest()) {
    DefinedReg defined_reg{insn->dest_is_wide(), RegState::INITIALIZED};
    if (insn->opcode() == OPCODE_MOVE_OBJECT) {
      auto it = pcn->defined_regs.find(insn->src(0));
      if (it != pcn->defined_regs.end()) {
        defined_reg = it->second;
      } else {
        auto initialized =
            reaching_initialized_new_instances->at(insn).get(insn->src(0));
        if (!initialized.get_constant() || !*initialized.get_constant()) {
          return false;
        }
      }
    } else if (opcode == IOPCODE_MOVE_RESULT_PSEUDO_OBJECT) {
      always_assert(!pcn->insns.empty());
      auto last_opcode = pcn->insns.back()->opcode();
      if (last_opcode == OPCODE_NEW_INSTANCE) {
        defined_reg.state = RegState::UNINITIALIZED;
      }
    }
    pcn->defined_regs[insn->dest()] = defined_reg;
    pc->temp_regs += insn->dest_is_wide() ? 2 : 1;
  }
  pcn->insns.push_back(insn);
  pc->insns_size++;
  if (!opcode::is_a_move(opcode)) {
    // Moves are likely still eliminated by reg-alloc or other opts
    if (insn->opcode() == IOPCODE_INIT_CLASS) {
      pc->size += 2;
    } else {
      pc->size += insn->size();
    }
  }
  return true;
}

static bool can_outline_insn(const RefChecker& ref_checker,
                             const OptionalReachingInitializedsEnvironments&
                                 reaching_initialized_init_first_param,
                             IRInstruction* insn,
                             bool outline_control_flow) {
  if (!can_outline_opcode(insn->opcode(), outline_control_flow)) {
    return false;
  }
  if (insn->has_method()) {
    auto* method =
        resolve_method_deprecated(insn->get_method(), opcode_to_search(insn));
    if (method == nullptr || method != insn->get_method()) {
      return false;
    }
    if (!is_public(method) && method->is_external()) {
      return false;
    }
    if (!ref_checker.check_method(method)) {
      return false;
    }
    if (!PositionPatternSwitchManager::
            CAN_OUTLINED_METHOD_INVOKE_OUTLINED_METHOD &&
        insn->opcode() == OPCODE_INVOKE_STATIC && is_outlined_method(method)) {
      // TODO: Remove this limitation imposed by symbolication infrastructure.
      return false;
    }
    if (method->rstate.should_not_outline()) {
      return false;
    }
  } else if (insn->has_field()) {
    auto* field = resolve_field(insn->get_field());
    if (field == nullptr || field != insn->get_field()) {
      return false;
    }
    if (!is_public(field) && field->is_external()) {
      return false;
    }
    if (!ref_checker.check_field(field)) {
      return false;
    }
    if (is_final(field) && (opcode::is_an_iput(insn->opcode()) ||
                            opcode::is_an_sput(insn->opcode()))) {
      return false;
    }
  } else if (insn->has_type()) {
    auto* cls = type_class(insn->get_type());
    if (cls != nullptr) {
      if (!is_public(cls) && cls->is_external()) {
        return false;
      }
      if (!ref_checker.check_type(insn->get_type())) {
        return false;
      }
    }
  }
  if (reaching_initialized_init_first_param) {
    // In a constructor, we cannot outline instructions that access the first
    // parameter before the base constructor was called on it.
    const auto& env = reaching_initialized_init_first_param->at(insn);
    for (size_t i = 0; i < insn->srcs_size(); i++) {
      auto reg = insn->src(i);
      const auto& initialized = env.get(reg);
      if (!initialized.get_constant() || !*initialized.get_constant()) {
        return false;
      }
    }
  }
  return true;
}

static bool is_uniquely_reached_via_pred(cfg::Block* block) {
  const auto& pred_edges = block->preds();
  return pred_edges.size() == 1 && block != block->cfg().entry_block();
}

// Check if starting from the given iterator, we have a tree-shaped
// branching structure, and gather a common eventual target block where
// the leaf blocks would unconditionally go to.
static UnorderedSet<cfg::Block*> get_eventual_targets_after_outlining(
    cfg::Block* first_block, const cfg::InstructionIterator& it) {
  always_assert(opcode::is_a_conditional_branch(it->insn->opcode()) ||
                opcode::is_switch(it->insn->opcode()));
  auto get_targets =
      [first_block](cfg::Block* start_block) -> UnorderedSet<cfg::Block*> {
    // The target could be the start block itself, if we don't find any other
    // eligible targets, or the target(s) we find at the end of further
    // conditional control-flow.
    UnorderedSet<cfg::Block*> targets{start_block};
    if (is_uniquely_reached_via_pred(start_block)) {
      auto big_block = big_blocks::get_big_block(start_block);
      if (big_block && big_block->same_try(first_block)) {
        auto* last_block = big_block->get_last_block();
        auto last_insn_it = last_block->get_last_insn();
        if (last_insn_it != last_block->end() &&
            (opcode::is_a_conditional_branch(last_insn_it->insn->opcode()) ||
             opcode::is_switch(last_insn_it->insn->opcode()))) {
          auto last_insn_cfg_it =
              last_block->to_cfg_instruction_iterator(last_insn_it);
          auto more_targets = get_eventual_targets_after_outlining(
              start_block, last_insn_cfg_it);
          insert_unordered_iterable(targets, more_targets);
        } else {
          auto* goes_to = last_block->goes_to();
          if (goes_to != nullptr) {
            targets.insert(goes_to);
          }
        }
      }
    }
    return targets;
  };
  auto* block = it.block();
  auto succs = get_ordered_goto_and_branch_succs(block);
  if (succs.empty()) {
    return UnorderedSet<cfg::Block*>();
  }
  // We start with the targets of the first successor, and narrow them down
  // with all other successor targets.
  auto succs_it = succs.begin();
  auto targets = get_targets((*succs_it)->target());
  for (succs_it++; succs_it != succs.end() && !targets.empty(); succs_it++) {
    auto other_targets = get_targets((*succs_it)->target());
    unordered_erase_if(targets,
                       [&](auto* b) { return !other_targets.count(b); });
  }
  return targets;
}

using MethodCandidates = UnorderedMap<Candidate,
                                      std::vector<CandidateMethodLocation>,
                                      CandidateHasher>;

// Callback invoked when either...
// - one more instruction was successfully appended to the partial candidate,
// and a point was reached that could potentially mark the end of an outlined
// instruction sequence (in this case, there is no next_block), or
// - the end of a converged fully explored conditional control-flow fork has
// been reached (in this case, the iterator is at the end, and next_block
// indicates the block at which the converged control-flow will continue).
using ExploredCallback =
    std::function<void(PartialCandidate& pc,
                       cfg::Block* first_block,
                       const big_blocks::InstructionIterator& it,
                       cfg::Block* next_block)>;

// Look for and add entire candidate sequences starting at a
// particular point in a big block.
// Result indicates whether the big block was successfully explored to the end.
static bool explore_candidates_from(
    LazyReachingInitializedsEnvironments& reaching_initialized_new_instances,
    const OptionalReachingInitializedsEnvironments&
        reaching_initialized_init_first_param,
    const Config& config,
    const RefChecker& ref_checker,
    const CandidateInstructionCoresSet& recurring_cores,
    PartialCandidate* pc,
    PartialCandidateNode* pcn,
    big_blocks::InstructionIterator it,
    const big_blocks::InstructionIterator& end,
    const ExploredCallback* explored_callback = nullptr) {
  std::optional<IROpcode> prev_opcode;
  CandidateInstructionCoresBuilder cores_builder;
  auto* first_block = it.block();
  auto& cfg = first_block->cfg();
  for (; it != end; prev_opcode = it->insn->opcode(), it++) {
    if (pc->insns_size >= config.max_insns_size) {
      return false;
    }
    auto* insn = it->insn;
    if (!can_outline_insn(ref_checker, reaching_initialized_init_first_param,
                          insn, config.outline_control_flow)) {
      return false;
    }
    cores_builder.push_back(insn);
    if (cores_builder.has_value() &&
        (recurring_cores.count(cores_builder.get_value()) == 0u)) {
      return false;
    }
    if (!append_to_partial_candidate(reaching_initialized_new_instances, insn,
                                     pc, pcn, config)) {
      return false;
    }
    if (opcode::is_a_conditional_branch(insn->opcode()) ||
        opcode::is_switch(insn->opcode())) {
      // If the branching structure is such that there's a tree where all
      // leaves nodes unconditionally goto a common block, then we'll attempt
      // to gather a partial candidate tree.
      // TODO: Handle not just conditional trees, but DAGs or even arbitrary
      // control-flow.
      auto targets =
          get_eventual_targets_after_outlining(first_block, it.unwrap());
      always_assert(targets.size() <= 1);
      TRACE(ISO, 3, "[invoke sequence outliner] %zu eventual targets",
            targets.size());
      if (targets.size() != 1) {
        return false;
      }
      auto* block = it.block();
      auto succs = get_ordered_goto_and_branch_succs(block);
      auto defined_regs_copy = pcn->defined_regs;
      pcn->defined_regs.clear();
      auto* next_block = *unordered_any(targets);
      for (auto* succ_edge : succs) {
        auto succ_pcn = std::make_shared<PartialCandidateNode>();
        pcn->succs.emplace_back(succ_edge, succ_pcn);
        succ_pcn->defined_regs = defined_regs_copy;
        if (succ_edge->target() != next_block) {
          auto succ_big_block = big_blocks::get_big_block(succ_edge->target());
          always_assert(succ_big_block);
          always_assert(succ_big_block->same_try(first_block));
          always_assert(
              is_uniquely_reached_via_pred(succ_big_block->get_first_block()));
          auto succ_ii = big_blocks::InstructionIterable(*succ_big_block);
          if (!explore_candidates_from(reaching_initialized_new_instances,
                                       reaching_initialized_init_first_param,
                                       config, ref_checker, recurring_cores, pc,
                                       succ_pcn.get(), succ_ii.begin(),
                                       succ_ii.end())) {
            return false;
          }
        }
        for (auto& q : UnorderedIterable(succ_pcn->defined_regs)) {
          auto defined_regs_it = pcn->defined_regs.find(q.first);
          if (defined_regs_it == pcn->defined_regs.end()) {
            pcn->defined_regs.insert(q);
          } else if (q.second.wide != defined_regs_it->second.wide) {
            defined_regs_it->second.state = RegState::INCONSISTENT;
          } else if (q.second.state < defined_regs_it->second.state) {
            defined_regs_it->second.state = q.second.state;
          }
        }
      }
      if (explored_callback != nullptr) {
        (*explored_callback)(*pc, first_block, end, next_block);
      }
      return true;
    }
    // We cannot consider partial candidate sequences when they are
    // missing their move-result piece
    if (insn->has_move_result_any() &&
        !cfg.move_result_of(it.unwrap()).is_end()) {
      continue;
    }
    // We prefer not to consider sequences ending in const instructions.
    // (Experiments have shown that outlining the overlapping candidate without
    // a trailing consts tends to lead to better results and a faster outliner.)
    if (insn->opcode() == OPCODE_CONST || insn->opcode() == OPCODE_CONST_WIDE ||
        (insn->opcode() == IOPCODE_MOVE_RESULT_PSEUDO_OBJECT && prev_opcode &&
         opcode::is_a_const(*prev_opcode))) {
      continue;
    }
    if (explored_callback != nullptr) {
      (*explored_callback)(*pc, first_block, it, /* next_block */ nullptr);
    }
  }
  return true;
}

#define STATS                                   \
  FOR_EACH(live_out_to_throw_edge)              \
  FOR_EACH(live_out_multiple)                   \
  FOR_EACH(live_out_initialized_not)            \
  FOR_EACH(arg_type_not_computed)               \
  FOR_EACH(arg_type_illegal)                    \
  FOR_EACH(res_type_not_computed)               \
  FOR_EACH(res_type_illegal)                    \
  FOR_EACH(overlap)                             \
  FOR_EACH(loop)                                \
  FOR_EACH(block_warm_loop_exceeds_thresholds)  \
  FOR_EACH(block_warm_loop_no_source_blocks)    \
  FOR_EACH(block_throughput)                    \
  FOR_EACH(block_throughput_exceeds_thresholds) \
  FOR_EACH(block_throughput_no_source_blocks)   \
  FOR_EACH(block_hot)                           \
  FOR_EACH(block_hot_exceeds_thresholds)        \
  FOR_EACH(block_hot_no_source_blocks)

struct FindCandidatesStats {
// NOLINTNEXTLINE(bugprone-macro-parentheses)
#define FOR_EACH(name) std::atomic<size_t> name{0};
  STATS
#undef FOR_EACH
};

// For a single method, identify possible beneficial outlinable candidates.
// For each candidate, gather information about where exactly in the
// given method it is located.
static MethodCandidates find_method_candidates(
    const Config& config,
    const RefChecker& ref_checker,
    const OutlineabilityContext& outlineability,
    DexMethod* method,
    cfg::ControlFlowGraph& cfg,
    const CandidateInstructionCoresSet& recurring_cores,
    FindCandidatesStats* stats) {
  MethodCandidates candidates;
  Lazy<LivenessFixpointIterator> liveness_fp_iter([&cfg] {
    auto res = std::make_unique<LivenessFixpointIterator>(cfg);
    res->run({});
    return res;
  });
  LazyUnorderedMap<cfg::Block*, UnorderedMap<IRInstruction*, LivenessDomain>>
      live_outs([&liveness_fp_iter](cfg::Block* block) {
        UnorderedMap<IRInstruction*, LivenessDomain> res;
        auto live_out = liveness_fp_iter->get_live_out_vars_at(block);
        for (auto& mie : InstructionIterable(block).reversed()) {
          res.emplace(mie.insn, live_out);
          liveness_fp_iter->analyze_instruction(mie.insn, &live_out);
        }
        return res;
      });
  // Variables that flow into a throw block, if any
  LazyUnorderedMap<cfg::Block*, LivenessDomain> throw_live_out(
      [&cfg, &liveness_fp_iter](cfg::Block* block) {
        auto res = LivenessDomain::bottom();
        for (auto* e : cfg.get_succ_edges_of_type(block, cfg::EDGE_THROW)) {
          res.join_with(liveness_fp_iter->get_live_in_vars_at(e->target()));
        }
        return res;
      });
  LazyReachingInitializedsEnvironments reaching_initialized_new_instances(
      [&cfg]() {
        return reaching_initializeds::get_reaching_initializeds(
            cfg, reaching_initializeds::Mode::NewInstances);
      });
  OptionalReachingInitializedsEnvironments
      reaching_initialized_init_first_param;
  if (method::is_init(method)) {
    reaching_initialized_init_first_param =
        reaching_initializeds::get_reaching_initializeds(
            cfg, reaching_initializeds::Mode::FirstLoadParam);
  }
  OutlinerTypeAnalysis type_analysis(method);
  auto big_blocks = big_blocks::get_big_blocks(cfg);
  // Along big blocks, we are assigning consecutive indices to instructions.
  // We'll use this to manage ranges of instructions that need to get
  // invalidated when overlapping ranges of instructions are outlined.
  Lazy<UnorderedMap<const IRInstruction*, size_t>> insn_idxes([&big_blocks]() {
    UnorderedMap<const IRInstruction*, size_t> res;
    for (auto& big_block : big_blocks) {
      for (const auto& mie : big_blocks::InstructionIterable(big_block)) {
        res.emplace(mie.insn, res.size());
      }
    }
    return res;
  });

  struct {
#define FOR_EACH(name) size_t name{0};
    STATS
#undef FOR_EACH
  } lstats;

  // We are visiting the instructions in this method in "big block" chunks:
  // - The big blocks cover all blocks.
  // - It is safe to do so as they all share the same throw-edges, and any
  //   outlined method invocation will be placed in the first block of the big
  //   block, with the appropriate throw edges.
  for (auto& big_block : big_blocks) {
    ExploredCallback explored_callback =
        [&](PartialCandidate& pc,
            cfg::Block* first_block,
            const big_blocks::InstructionIterator& it,
            cfg::Block* next_block) {
          // At this point, we can consider the current candidate for
          // normalization and outlining, adding it to the set of outlining
          // candidates for this method
          if (pc.insns_size < config.min_insns_size) {
            // Code is below minimum configured size
            return;
          }
          if (pc.size <= config.cost_invoke_without_result) {
            // Partial candidate is not longer than the replacement invoke
            // instruction would be
            return;
          }
          std::vector<std::pair<reg_t, IRInstruction*>> live_out_consts;
          std::optional<std::pair<reg_t, bool>> out_reg;
          if (!pc.root.defined_regs.empty()) {
            const auto& live_out =
                next_block != nullptr
                    ? liveness_fp_iter->get_live_in_vars_at(next_block)
                    : live_outs[it.block()].at(it->insn);
            auto first_block_throw_live_out = throw_live_out[first_block];
            // Visit registers in a fixed order. The three bail-outs below are
            // competing reasons to reject this candidate, and whichever
            // register is reached first decides which one is charged: with one
            // live-out register uninitialized and another initialized, seeing
            // the initialized one first yields live_out_multiple, seeing the
            // other first yields live_out_initialized_not. The outcome is the
            // same either way -- every branch returns, so the candidate is
            // rejected regardless, which is why this never affected the emitted
            // code -- but the counters land in redex-stats.txt, and a metric
            // that varies between runs makes stats comparisons flaky.
            for (auto reg : unordered_to_ordered_keys(pc.root.defined_regs)) {
              const auto& defined_reg = pc.root.defined_regs.at(reg);
              if (first_block_throw_live_out.contains(reg)) {
                TRACE(ISO, 4,
                      "[invoke sequence outliner] [bail out] Cannot return "
                      "value that's live-in to a throw edge");
                lstats.live_out_to_throw_edge++;
                return;
              }
              if (live_out.contains(reg)) {
                always_assert(defined_reg.state != RegState::INCONSISTENT);
                if (out_reg) {
                  TRACE(ISO, 4,
                        "[invoke sequence outliner] [bail out] Cannot have "
                        "more than one out-reg");
                  lstats.live_out_multiple++;
                  return;
                }
                if (defined_reg.state == RegState::UNINITIALIZED) {
                  TRACE(ISO, 4,
                        "[invoke sequence outliner] [bail out] Cannot return "
                        "uninitialized");
                  lstats.live_out_initialized_not++;
                  return;
                }
                always_assert(defined_reg.state == RegState::INITIALIZED);
                out_reg = std::make_pair(reg, defined_reg.wide);
              }
            }
          }
          if (out_reg && pc.size <= config.cost_invoke_with_result) {
            // Code to outline is not longer than the replacement invoke
            // instruction would be
            return;
          }
          auto c = normalize(type_analysis, pc, out_reg);
          if (std::find(c.arg_types.begin(), c.arg_types.end(), nullptr) !=
              c.arg_types.end()) {
            TRACE(ISO, 4,
                  "[invoke sequence outliner] [bail out] Could not infer "
                  "argument type");
            lstats.arg_type_not_computed++;
            return;
          }
          if (std::find_if(c.arg_types.begin(), c.arg_types.end(),
                           [&](const DexType* t) {
                             return !ref_checker.check_type(t);
                           }) != c.arg_types.end()) {
            TRACE(ISO, 4,
                  "[invoke sequence outliner] [bail out] Illegal argument "
                  "type");
            lstats.arg_type_illegal++;
            return;
          }
          if (out_reg && c.res_type == nullptr) {
            TRACE(ISO, 4,
                  "[invoke sequence outliner] [bail out] Could not infer "
                  "result type");
            lstats.res_type_not_computed++;
            return;
          }
          if (out_reg && !ref_checker.check_type(c.res_type)) {
            TRACE(ISO, 4,
                  "[invoke sequence outliner] [bail out] Illegal result type");
            lstats.res_type_illegal++;
            return;
          }
          auto result =
              outlineability.can_outline_from_big_block(method, big_block);
          if (result != OutlineabilityContext::Result::CanOutline) {
            // We could bail out on this way earlier, but doing it last gives us
            // better statistics on what the damage really is
            switch (result) {
            case OutlineabilityContext::Result::WarmLoop:
              lstats.loop++;
              return;
            case OutlineabilityContext::Result::WarmLoopExceedsThresholds:
              lstats.block_warm_loop_exceeds_thresholds++;
              return;
            case OutlineabilityContext::Result::WarmLoopNoSourceBlocks:
              lstats.block_warm_loop_no_source_blocks++;
              return;
            case OutlineabilityContext::Result::Throughput:
              lstats.block_throughput++;
              return;
            case OutlineabilityContext::Result::ThroughputExceedsThresholds:
              lstats.block_throughput_exceeds_thresholds++;
              return;
            case OutlineabilityContext::Result::ThroughputNoSourceBlocks:
              lstats.block_throughput_no_source_blocks++;
              return;
            case OutlineabilityContext::Result::Hot:
              lstats.block_hot++;
              return;
            case OutlineabilityContext::Result::HotExceedsThresholds:
              lstats.block_hot_exceeds_thresholds++;
              return;
            case OutlineabilityContext::Result::HotNoSourceBlocks:
              lstats.block_hot_no_source_blocks++;
              return;
            default:
              not_reached();
            }
          }
          auto& cmls = candidates[c];
          std::map<size_t, size_t> ranges;
          std::function<void(const PartialCandidateNode&)> insert_ranges;
          insert_ranges = [&insert_ranges, &ranges,
                           &insn_idxes](const PartialCandidateNode& pcn) {
            if (!pcn.insns.empty()) {
              auto start = insn_idxes->at(pcn.insns.front());
              auto size = pcn.insns.size();
              ranges.emplace(start, size);
            }
            for (const auto& p : pcn.succs) {
              insert_ranges(*p.second);
            }
          };
          insert_ranges(pc.root);
          if (std::find_if(cmls.begin(), cmls.end(),
                           [&ranges](const CandidateMethodLocation& cml) {
                             return ranges_overlap(cml.ranges, ranges);
                           }) != cmls.end()) {
            lstats.overlap++;
          } else {
            cmls.push_back((CandidateMethodLocation){
                pc.root.insns.front(), first_block,
                out_reg ? std::optional<reg_t>(out_reg->first) : std::nullopt,
                ranges});
          }
        };
    auto ii = big_blocks::InstructionIterable(big_block);
    for (auto it = ii.begin(), end = ii.end(); it != end; it++) {
      if (opcode::is_move_result_any(it->insn->opcode())) {
        // We cannot start a sequence at a move-result-any instruction
        continue;
      }
      PartialCandidate pc;
      explore_candidates_from(reaching_initialized_new_instances,
                              reaching_initialized_init_first_param, config,
                              ref_checker, recurring_cores, &pc, &pc.root, it,
                              end, &explored_callback);
    }
  }

#define FOR_EACH(name) \
  if (lstats.name) stats->name += lstats.name;
  STATS
#undef FOR_EACH
  return candidates;
}

////////////////////////////////////////////////////////////////////////////////
// get_recurring_cores
////////////////////////////////////////////////////////////////////////////////

static bool can_outline_from_method(DexMethod* method) {
  return !(method->rstate.no_optimizations() ||
           method->rstate.should_not_outline() || method->rstate.outlined());
}

// Gather set of recurring small (MIN_INSNS_SIZE) adjacent instruction
// sequences that are outlinable. Note that all longer recurring outlinable
// instruction sequences must be comprised of shorter recurring ones.
static void get_recurring_cores(const Config& config,
                                PassManager& mgr,
                                const Scope& scope,
                                const OutlineabilityContext& outlineability,
                                const RefChecker& ref_checker,
                                CandidateInstructionCoresSet* recurring_cores) {
  AtomicMap<CandidateInstructionCores, size_t, CandidateInstructionCoresHasher>
      concurrent_cores;
  walk::parallel::code(
      scope,
      [&config, &ref_checker, &outlineability,
       &concurrent_cores](DexMethod* method, IRCode& code) {
        if (!can_outline_from_method(method)) {
          return;
        }
        always_assert(code.cfg_built());
        code.cfg().calculate_exit_block();
        auto& cfg = code.cfg();
        OptionalReachingInitializedsEnvironments
            reaching_initialized_init_first_param;
        if (method::is_init(method)) {
          reaching_initialized_init_first_param =
              reaching_initializeds::get_reaching_initializeds(
                  cfg, reaching_initializeds::Mode::FirstLoadParam);
        }
        for (auto& big_block : big_blocks::get_big_blocks(cfg)) {
          if (outlineability.can_outline_from_big_block(method, big_block) !=
              OutlineabilityContext::Result::CanOutline) {
            continue;
          }
          CandidateInstructionCoresBuilder cores_builder;
          for (auto& mie : big_blocks::InstructionIterable(big_block)) {
            auto* insn = mie.insn;
            if (!can_outline_insn(ref_checker,
                                  reaching_initialized_init_first_param, insn,
                                  config.outline_control_flow)) {
              cores_builder.clear();
              continue;
            }
            cores_builder.push_back(insn);
            if (cores_builder.has_value()) {
              concurrent_cores.fetch_add(cores_builder.get_value(), 1);
            }
          }
        }
      });
  size_t singleton_cores{0};
  for (auto& p : UnorderedIterable(concurrent_cores)) {
    auto count = p.second.load();
    always_assert(count > 0);
    if (count > 1) {
      recurring_cores->insert(p.first);
    } else {
      singleton_cores++;
    }
  }
  mgr.incr_metric("num_singleton_cores", singleton_cores);
  mgr.incr_metric("num_recurring_cores", recurring_cores->size());
  TRACE(ISO, 2,
        "[invoke sequence outliner] %zu singleton cores, %zu recurring "
        "cores",
        singleton_cores, recurring_cores->size());
}

////////////////////////////////////////////////////////////////////////////////
// get_beneficial_candidates
////////////////////////////////////////////////////////////////////////////////

struct CandidateInfo {
  UnorderedMap<DexMethod*, std::vector<CandidateMethodLocation>> methods;
  size_t count{0};
};

// What the occurrences of ONE outlined method know about each slot of a
// registered pattern beyond its identity: the provenance snapshot
// `make_pattern` reports per slot, or null. Pattern ids are content-interned
// and shared between outlined methods, so this cannot live beside the pattern:
// it belongs to the registration that observed it.
using PatternSlotProvenance = UnorderedMap<uint32_t, std::vector<DexPosition*>>;

DexPosition* slot_provenance(const PatternSlotProvenance& slots,
                             uint32_t pattern_id,
                             size_t position_index) {
  auto it = slots.find(pattern_id);
  if (it == slots.end() || position_index >= it->second.size()) {
    return nullptr;
  }
  return it->second[position_index];
}

// Folds one registration's observations into what the outlined method has seen
// across its own occurrences so far.
void merge_slot_provenance(PatternSlotProvenance* slots,
                           uint32_t pattern_id,
                           const std::vector<DexPosition*>& observed) {
  always_assert(slots != nullptr);
  auto [it, emplaced] = slots->emplace(pattern_id, observed);
  if (emplaced) {
    return;
  }
  auto& recorded = it->second;
  always_assert(recorded.size() == observed.size());
  auto* manager = g_redex->get_position_pattern_switch_manager();
  for (size_t i = 0; i < recorded.size(); ++i) {
    recorded[i] = manager->join_slot_provenance(recorded[i], observed[i]);
  }
}

// We keep track of outlined methods that reside in earlier dexes of the current
// store. Order vector is used for keeping the track of the order of each
// candidate stored.
struct ReusableOutlinedMethods {
  struct OutlinedMethod {
    const DexStore* store;
    DexMethod* method;
    std::set<uint32_t> pattern_ids;
    PatternSlotProvenance slot_provenance;
  };
  UnorderedMap<Candidate, std::deque<OutlinedMethod>, CandidateHasher> map;
  std::vector<Candidate> order;
};

UnorderedSet<const DexType*> get_declaring_types(const CandidateInfo& ci) {
  UnorderedSet<const DexType*> types;
  for (const auto& p : UnorderedIterable(ci.methods)) {
    types.insert(p.first->get_class());
  }
  return types;
}

// Helper function that enables quickly determinining if a class is a common
// base class of a set of class. To this end, it builds up a map that
// includes all transitive super classes associated with a count of how many of
// the original types share this ancestor. If the count is equal to the number
// of the original types, then it must be a common base class.
UnorderedSet<const DexType*> get_common_super_classes(
    const UnorderedSet<const DexType*>& types) {
  UnorderedMap<const DexType*, size_t> counted_super_classes;
  UnorderedSet<const DexType*> common_super_classes;
  for (const auto* t : UnorderedIterable(types)) {
    do {
      if (++counted_super_classes[t] == types.size()) {
        common_super_classes.insert(t);
      }
      auto* cls = type_class(t);
      if (cls == nullptr) {
        break;
      }
      t = cls->get_super_class();
    } while (t != nullptr);
  }
  return common_super_classes;
}

UnorderedSet<const DexType*> get_super_classes(
    const UnorderedSet<const DexType*>& types) {
  UnorderedSet<const DexType*> super_classes;
  for (const auto* t : UnorderedIterable(types)) {
    do {
      if (!super_classes.insert(t).second) {
        break;
      }
      auto* cls = type_class(t);
      if (cls == nullptr) {
        break;
      }
      t = cls->get_super_class();
    } while (t != nullptr);
  }
  return super_classes;
}

// Given a candidate, find all referenced types which will get get
// unconditionally initialized when the instructions run. In case of multiple
// successors, only types in common by all successors are considered. The result
// may include super types.
UnorderedSet<const DexType*> get_referenced_types(const Candidate& c) {
  std::function<UnorderedSet<const DexType*>(const CandidateNode& cn)>
      gather_types;
  gather_types = [&gather_types](const CandidateNode& cn) {
    UnorderedSet<const DexType*> types;
    auto insert_internal_type = [&types](const DexType* t) {
      auto* cls = type_class(t);
      if ((cls != nullptr) && !cls->is_external()) {
        types.insert(t);
      }
    };

    for (const auto& csi : cn.insns) {
      const auto& cic = csi.core;
      switch (opcode::ref(cic.opcode)) {
      case opcode::Ref::Method:
        insert_internal_type(cic.method->get_class());
        break;
      case opcode::Ref::Field:
        insert_internal_type(cic.field->get_class());
        break;
      case opcode::Ref::Type:
        // in particular, let's exclude const-class here, as that doesn't ensure
        // that the static initializer will run
        if (cic.opcode == OPCODE_NEW_INSTANCE) {
          insert_internal_type(cic.type);
        }
        break;
      default:
        break;
      }
    }
    if (!cn.succs.empty()) {
      UnorderedMap<const DexType*, size_t> successor_types;
      for (const auto& p : cn.succs) {
        auto super_classes = get_super_classes(gather_types(*p.second));
        for (const auto* type : UnorderedIterable(super_classes)) {
          if (++successor_types[type] == cn.succs.size()) {
            types.insert(type);
          }
        }
      }
    }
    return types;
  };
  return gather_types(c.root);
}

// Finds an outlined method that either resides in an outlined helper class, or
// a common base class, or is co-located with its references.
static DexMethod* find_reusable_method(
    const DexStore* store,
    const DexStoreDependencies& store_dependencies,
    const Candidate& c,
    const CandidateInfo& ci,
    const ReusableOutlinedMethods& outlined_methods,
    bool reuse_outlined_methods_across_dexes) {
  if (!reuse_outlined_methods_across_dexes) {
    // reuse_outlined_methods_across_dexes is disabled
    return nullptr;
  }
  auto it = outlined_methods.map.find(c);
  if (it == outlined_methods.map.end()) {
    return nullptr;
  }
  DexMethod* helper_class_method{nullptr};
  for (const auto& outlined : it->second) {
    const auto* other_store = outlined.store;
    auto* method = outlined.method;
    if (store != other_store && (store_dependencies.count(other_store) == 0u)) {
      continue;
    }
    auto* cls = type_class(method->get_class());
    if (cls->rstate.outlined()) {
      helper_class_method = method;
      continue;
    }
    auto declaring_types = get_declaring_types(ci);
    auto common_super_classes = get_common_super_classes(declaring_types);
    if (common_super_classes.count(method->get_class()) != 0u) {
      return method;
    }
    auto referenced_types = get_referenced_types(c);
    auto super_classes = get_super_classes(referenced_types);
    if (super_classes.count(method->get_class()) != 0u) {
      return method;
    }
  }
  return helper_class_method;
}

static size_t get_savings(const Config& config,
                          const DexStore* store,
                          const DexStoreDependencies& store_dependencies,
                          const Candidate& c,
                          const CandidateInfo& ci,
                          const ReusableOutlinedMethods& outlined_methods) {
  size_t cost = c.size * ci.count;
  size_t outlined_cost =
      config.cost_method_metadata + (c.res_type != nullptr
                                         ? config.cost_invoke_with_result
                                         : config.cost_invoke_without_result) *
                                        ci.count;
  if (find_reusable_method(store, store_dependencies, c, ci, outlined_methods,
                           config.reuse_outlined_methods_across_dexes) ==
      nullptr) {
    outlined_cost += config.cost_method_body + c.size;
  }

  return (outlined_cost + config.savings_threshold) < cost
             ? (cost - outlined_cost)
             : 0;
}

using CandidateId = uint32_t;
struct CandidateWithInfo {
  Candidate candidate;
  CandidateInfo info;
};

// Find beneficial candidates across all methods. Beneficial candidates are
// those that occur often enough so that there would be a net savings (in terms
// of code units / bytes) when outlining them.
//
// We distinguish three kinds of methods:
// - "hot" methods are known to get invoked many times, and we do not outline
//   from them.
// - "warm" methods are known to get invoked only a few times, and we will not
//   outline from loops within them.
// - all other methods are considered to be cold, and every outlining
//   opportunity in them will be considered.
//
// Candidates are identified by numerical candidate ids to make things
// deterministic (as opposed to a pointer) and provide an efficient
// identification mechanism.
static void get_beneficial_candidates(
    const Config& config,
    PassManager& mgr,
    const DexStore* store,
    const DexStoreDependencies& store_dependencies,
    const Scope& dex,
    const RefChecker& ref_checker,
    const CandidateInstructionCoresSet& recurring_cores,
    const OutlineabilityContext& outlineability,
    const ReusableOutlinedMethods* outlined_methods,
    std::vector<CandidateWithInfo>* candidates_with_infos,
    UnorderedMap<DexMethod*, UnorderedSet<CandidateId>>*
        candidate_ids_by_methods) {
  ConcurrentMap<Candidate, CandidateInfo, CandidateHasher>
      concurrent_candidates;
  FindCandidatesStats stats;
  walk::parallel::code(dex, [&config, &ref_checker, &recurring_cores,
                             &concurrent_candidates, &outlineability,
                             &stats](DexMethod* method, IRCode& code) {
    if (!can_outline_from_method(method)) {
      return;
    }
    auto method_candidates =
        find_method_candidates(config, ref_checker, outlineability, method,
                               code.cfg(), recurring_cores, &stats);
    for (auto& p : UnorderedIterable(method_candidates)) {
      std::vector<CandidateMethodLocation>& cmls = p.second;
      concurrent_candidates.update(p.first,
                                   [method, &cmls](const Candidate&,
                                                   CandidateInfo& info,
                                                   bool /* exists */) {
                                     info.methods.emplace(method, cmls);
                                     info.count += cmls.size();
                                   });
    }
  });
#define FOR_EACH(name) mgr.incr_metric("num_candidate_" #name, stats.name);
  STATS
#undef FOR_EACH
  using CandidateSet = UnorderedSet<Candidate, CandidateHasher>;
  std::map<DexMethod*, CandidateSet, dexmethods_comparator>
      candidates_by_methods;
  size_t beneficial_count{0}, maleficial_count{0};
  for (auto& p : UnorderedIterable(concurrent_candidates)) {
    if (get_savings(config, store, store_dependencies, p.first, p.second,
                    *outlined_methods) > 0) {
      beneficial_count += p.second.count;
      for (auto& q : UnorderedIterable(p.second.methods)) {
        candidates_by_methods[q.first].insert(p.first);
      }
    } else {
      maleficial_count += p.second.count;
    }
  }
  TRACE(ISO, 2,
        "[invoke sequence outliner] %zu beneficial candidates, %zu "
        "maleficial candidates",
        beneficial_count, maleficial_count);
  mgr.incr_metric("num_beneficial_candidates", beneficial_count);
  mgr.incr_metric("num_maleficial_candidates", maleficial_count);
  // Deterministically compute unique candidate ids
  UnorderedMap<Candidate, CandidateId, CandidateHasher> candidate_ids;
  for (auto& p : candidates_by_methods) {
    auto& method_candidate_ids = (*candidate_ids_by_methods)[p.first];
    auto&& ui = UnorderedIterable(p.second);
    using CandidateSetIterator =
        std::remove_reference_t<decltype(ui)>::iterator;
    std::vector<std::pair<CandidateMethodLocation, CandidateSetIterator>>
        ordered;
    for (auto it = ui.begin(); it != ui.end(); it++) {
      const auto& c = *it;
      auto id_it = candidate_ids.find(c);
      if (id_it != candidate_ids.end()) {
        method_candidate_ids.insert(id_it->second);
        continue;
      }
      const auto& ci = concurrent_candidates.at_unsafe(c);
      for (const auto& cml : ci.methods.at(p.first)) {
        ordered.emplace_back(cml, it);
      }
    }
    std::sort(
        ordered.begin(), ordered.end(),
        [](const std::pair<CandidateMethodLocation, CandidateSetIterator>& a,
           const std::pair<CandidateMethodLocation, CandidateSetIterator>& b) {
          const auto& a_ranges = a.first.ranges;
          const auto& b_ranges = b.first.ranges;
          if (a_ranges.size() != b_ranges.size()) {
            return a_ranges.size() < b_ranges.size();
          }
          for (auto a_it = a_ranges.begin(), b_it = b_ranges.begin();
               a_it != a_ranges.end(); a_it++, b_it++) {
            if (a_it->first != b_it->first) {
              return a_it->first < b_it->first;
            }
            if (a_it->second != b_it->second) {
              return a_it->second < b_it->second;
            }
          }
          always_assert(a.first.first_insn == b.first.first_insn);
          always_assert(a.first.hint_block == b.first.hint_block);
          always_assert(a.second == b.second);
          return false;
        });
    for (auto& q : ordered) {
      const auto& c = *q.second;
      if (candidate_ids.count(c) == 0u) {
        always_assert(candidate_ids.size() < (1ULL << 32));
        CandidateId candidate_id =
            static_cast<CandidateId>(candidate_ids.size());
        method_candidate_ids.insert(candidate_id);
        candidate_ids.emplace(c, candidate_id);
        candidates_with_infos->push_back(
            {c, concurrent_candidates.at_unsafe(c)});
      }
    }
  }
}

////////////////////////////////////////////////////////////////////////////////
// outline
////////////////////////////////////////////////////////////////////////////////

static bool has_non_init_invoke_directs(const CandidateNode& cn) {
  for (const auto& ci : cn.insns) {
    if (ci.core.opcode == OPCODE_INVOKE_DIRECT &&
        !method::is_init(ci.core.method)) {
      return true;
    }
  }
  for (const auto& p : cn.succs) {
    if (has_non_init_invoke_directs(*p.second)) {
      return true;
    }
  }
  return false;
}

static bool has_non_init_invoke_directs(const Candidate& c) {
  return has_non_init_invoke_directs(c.root);
}

// A name generator for outlined methods
class MethodNameGenerator {
 private:
  PassManager& m_mgr;
  UnorderedMap<StableHash, size_t> m_unique_method_ids;
  size_t m_max_unique_method_id{0};
  size_t m_iteration;
  size_t short_id_counter{0};

 public:
  MethodNameGenerator() = delete;
  MethodNameGenerator(const MethodNameGenerator&) = delete;
  MethodNameGenerator& operator=(const MethodNameGenerator&) = delete;
  explicit MethodNameGenerator(PassManager& mgr, size_t iteration)
      : m_mgr(mgr), m_iteration(iteration) {}

  // Compute the name of the outlined method in a way that tends to be stable
  // across Redex runs.
  // obfuscated_name argument allows to generate obfuscate name instead of names
  // with a long hashed string, by default hashed names are returned.
  const DexString* get_name(const Candidate& c, bool obfuscated_name = false) {
    StableHash stable_hash = stable_hash_value(c);
    auto unique_method_id = m_unique_method_ids[stable_hash]++;
    m_max_unique_method_id = std::max(m_max_unique_method_id, unique_method_id);
    std::string name;
    if (obfuscated_name) {
      name += OUTLINED_METHOD_SHORT_NAME_PREFIX;
      std::string identifier_name;
      obfuscate_utils::compute_identifier(static_cast<int>(short_id_counter++),
                                          &identifier_name);
      name += identifier_name;
    } else {
      name += OUTLINED_METHOD_NAME_PREFIX;
      name += std::to_string(m_iteration) + "$";
      name += (boost::format("%08x") % stable_hash).str();
    }
    if (unique_method_id > 0) {
      name += std::string("$") + std::to_string(unique_method_id);
      TRACE(ISO, 5,
            "[invoke sequence outliner] name with non-unique stable id: %s",
            name.c_str());
    }
    return DexString::make_string(name);
  }

  ~MethodNameGenerator() {
    m_mgr.incr_metric("max_unique_method_id", m_max_unique_method_id);
    TRACE(ISO, 2, "[invoke sequence outliner] %zu max unique method id",
          m_max_unique_method_id);
  }
};

// This mimics what generate_debug_instructions(DexClass.cpp) does eventually:
// ignoring positions that don't have a file.
static DexPosition* skip_fileless(DexPosition* pos) {
  for (; (pos != nullptr) && (pos->file == nullptr); pos = pos->parent) {
  }
  return pos;
}

using CallSitePatternIds = UnorderedMap<IRInstruction*, uint32_t>;

class OutlinedMethodCreator {
 private:
  const Config& m_config;
  PassManager& m_mgr;
  MethodNameGenerator& m_method_name_generator;
  size_t m_outlined_methods{0};
  CallSitePatternIds m_call_site_pattern_ids;
  UnorderedMap<DexMethod*, std::unique_ptr<DexPosition>>
      m_unique_entry_positions;

  // Gets the set of unique dbg-position patterns.
  std::set<uint32_t> get_outlined_dbg_positions_patterns(
      const Candidate& c,
      const CandidateInfo& ci,
      PatternSlotProvenance* slots) {
    always_assert(slots != nullptr);
    std::set<uint32_t> pattern_ids;
    add_outlined_dbg_position_patterns(c, ci, &pattern_ids, slots);
    always_assert(!pattern_ids.empty());
    if (!m_config.full_dbg_positions) {
      // Keep the most detailed pattern for display, but do not let that choice
      // erase disagreements with the other occurrences it represents.
      uint32_t best_pattern_id = *pattern_ids.begin();
      size_t best_unique_positions{0};
      auto* manager = g_redex->get_position_pattern_switch_manager();
      const auto& all_managed_patterns = manager->get_patterns();
      for (auto pattern_id : pattern_ids) {
        UnorderedSet<DexPosition*> unique_positions;
        for (auto* pos : all_managed_patterns.at(pattern_id)) {
          unique_positions.insert(pos);
        }
        if (unique_positions.size() > best_unique_positions) {
          best_pattern_id = pattern_id;
          best_unique_positions = unique_positions.size();
        }
      }
      const auto& best_pattern = all_managed_patterns.at(best_pattern_id);
      std::vector<DexPosition*> selected(best_pattern.size(), nullptr);
      for (size_t i = 0; i < best_pattern.size(); ++i) {
        // Every occurrence's slot is joined into the kept one level by level,
        // so a level where an occurrence names a different place is merged
        // with a site nobody captured, and the levels where it names the same
        // place keep what it knew.
        DexPosition* joined = best_pattern.at(i);
        bool every_occurrence_has_the_slot = true;
        for (auto pattern_id : pattern_ids) {
          const auto& pattern = all_managed_patterns.at(pattern_id);
          if (pattern.size() != best_pattern.size()) {
            every_occurrence_has_the_slot = false;
            continue;
          }
          auto* observed = slot_provenance(*slots, pattern_id, i);
          auto* next = manager->join_slot_provenance(
              joined, observed != nullptr ? observed : pattern.at(i));
          if (next != nullptr) {
            joined = next;
          }
        }
        if (!every_occurrence_has_the_slot) {
          joined = manager->mark_slot_uncaptured(joined);
        }
        selected.at(i) = joined != best_pattern.at(i) ? joined : nullptr;
      }
      // The discarded patterns are not this method's any more, and the slots
      // kept are the selection's own verdict rather than any registration's.
      slots->clear();
      slots->emplace(best_pattern_id, std::move(selected));
      return {best_pattern_id};
    }
    return pattern_ids;
  }

 public:
  OutlinedMethodCreator() = delete;
  OutlinedMethodCreator(const OutlinedMethodCreator&) = delete;
  OutlinedMethodCreator& operator=(const OutlinedMethodCreator&) = delete;
  explicit OutlinedMethodCreator(const Config& config,
                                 PassManager& mgr,
                                 MethodNameGenerator& method_name_generator)
      : m_config(config),
        m_mgr(mgr),
        m_method_name_generator(method_name_generator) {}

  // Infers outlined pattern ids.
  void add_outlined_dbg_position_patterns(const Candidate& c,
                                          const CandidateInfo& ci,
                                          std::set<uint32_t>* pattern_ids,
                                          PatternSlotProvenance* slots) {
    always_assert(slots != nullptr);
    auto* manager = g_redex->get_position_pattern_switch_manager();
    // Order methods to make sure we get deterministic pattern-ids.
    auto ordered_methods =
        unordered_to_ordered_keys(ci.methods, compare_dexmethods);
    for (auto* method : ordered_methods) {
      const auto& cmls = ci.methods.at(method);
      for (const auto& cml : cmls) {
        // if the current method is reused then the call site
        // didn't have the pattern id. Need to create and add pattern_id
        auto positions = get_outlined_dbg_positions(c, cml, method);
        std::vector<DexPosition*> provenance;
        auto pattern_id = manager->make_pattern(positions, &provenance);
        merge_slot_provenance(slots, pattern_id, provenance);
        if (m_config.full_dbg_positions) {
          m_call_site_pattern_ids.emplace(cml.first_insn, pattern_id);
        }
        pattern_ids->insert(pattern_id);
      }
    }
  }

  // Obtain outlined method for a candidate.
  DexMethod* create_outlined_method(const Candidate& c,
                                    const CandidateInfo& ci,
                                    const DexType* host_class,
                                    std::set<uint32_t>* pattern_ids,
                                    PatternSlotProvenance* slots) {
    const auto* name =
        m_method_name_generator.get_name(c, m_config.obfuscate_method_names);
    DexTypeList::ContainerType arg_types;
    arg_types.reserve(c.arg_types.size());
    for (const auto* t : c.arg_types) {
      arg_types.push_back(t->to_mutable());
    }
    const auto* rtype = c.res_type != nullptr ? c.res_type : type::_void();
    auto* type_list = DexTypeList::make_type_list(std::move(arg_types));
    auto* proto = DexProto::make_proto(rtype, type_list);
    auto* outlined_method = DexMethod::make_method(host_class, name, proto)
                                ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
    // get pattern ids
    *pattern_ids = get_outlined_dbg_positions_patterns(c, ci, slots);
    always_assert(!(*pattern_ids).empty());
    // not setting method body here
    outlined_method->set_deobfuscated_name(show(outlined_method));
    outlined_method->rstate.set_dont_inline();
    outlined_method->rstate.set_outlined();
    // not setting visibility here
    type_class(host_class)->add_method(outlined_method);
    TRACE(ISO, 5, "[invoke sequence outliner] outlined to %s",
          SHOW(outlined_method));
    m_outlined_methods++;
    return outlined_method;
  }

  CallSitePatternIds* get_call_site_pattern_ids() {
    if (m_config.full_dbg_positions) {
      return &m_call_site_pattern_ids;
    } else {
      always_assert(m_call_site_pattern_ids.empty());
      return nullptr;
    }
  }

  PositionPattern get_outlined_dbg_positions(const Candidate& c,
                                             const CandidateMethodLocation& cml,
                                             DexMethod* method) {
    auto& cfg = method->get_code()->cfg();
    auto root_insn_it = cfg.find_insn(cml.first_insn, cml.hint_block);
    if (root_insn_it.is_end()) {
      // This should not happen, as for each candidate we never produce
      // overlapping locations in a method, and overlaps across selected
      // candidates are prevented by meticulously removing remaining overlapping
      // occurrences after processing a candidate.
      not_reached();
    }
    PositionPattern positions;
    auto* root_dbg_pos = skip_fileless(cfg.get_dbg_pos(root_insn_it));
    if (root_dbg_pos == nullptr) {
      if (!m_config.full_dbg_positions) {
        return positions;
      }
      // We'll provide a "synthetic entry position" as the root. Copies of that
      // position will be made later when it's actually needed. For now, we just
      // need to obtain a template instance, and we need to store it somewhere
      // so that we don't leak it.
      auto it = m_unique_entry_positions.find(method);
      if (it == m_unique_entry_positions.end()) {
        it = m_unique_entry_positions
                 .emplace(method,
                          DexPosition::make_synthetic_entry_position(method))
                 .first;
      }
      root_dbg_pos = it->second.get();
      TRACE(ISO, 6,
            "[instruction sequence outliner] using synthetic position for "
            "outlined code within %s",
            SHOW(method));
    }
    std::function<void(DexPosition * dbg_pos, const CandidateNode& cn,
                       big_blocks::Iterator it)>
        walk;
    walk = [&positions, &walk](DexPosition* dbg_pos,
                               const CandidateNode& cn,
                               big_blocks::Iterator it) {
      cfg::Block* last_block{nullptr};
      for (const auto& csi : cn.insns) {
        for (; it->type == MFLOW_POSITION || it->type == MFLOW_DEBUG ||
               it->type == MFLOW_SOURCE_BLOCK || it->type == MFLOW_REMARK;
             it++) {
          if (it->type == MFLOW_POSITION && (it->pos->file != nullptr)) {
            dbg_pos = it->pos.get();
          }
        }
        always_assert(it->type == MFLOW_OPCODE);
        always_assert(it->insn->opcode() == csi.core.opcode);
        positions.push_back(dbg_pos);
        last_block = it.block();
        it++;
      }
      if (!cn.succs.empty()) {
        always_assert(last_block != nullptr);
        auto succs = get_ordered_goto_and_branch_succs(last_block);
        always_assert(succs.size() == cn.succs.size());
        for (size_t i = 0; i < succs.size(); i++) {
          always_assert(normalize(succs.at(i)) == cn.succs.at(i).first);
          auto& succ_cn = *cn.succs.at(i).second;
          auto* succ_block = succs.at(i)->target();
          auto succ_it = big_blocks::Iterator(succ_block, succ_block->begin());
          walk(dbg_pos, succ_cn, succ_it);
        }
      }
    };
    walk(root_dbg_pos, c.root,
         big_blocks::Iterator(root_insn_it.block(), root_insn_it.unwrap(),
                              /* ignore_throws */ true));
    return positions;
  }

  ~OutlinedMethodCreator() {
    m_mgr.incr_metric("num_outlined_methods", m_outlined_methods);
    TRACE(ISO, 2,
          "[instruction sequence outliner] %zu outlined methods created",
          m_outlined_methods);
  }
};

// Rewrite instructions in existing method to invoke an outlined
// method instead.
static void rewrite_at_location(DexMethod* outlined_method,
                                const CallSitePatternIds* call_site_pattern_ids,
                                DexMethod* method,
                                cfg::ControlFlowGraph& cfg,
                                const Candidate& c,
                                const CandidateMethodLocation& cml) {
  // Figure out argument and result registers
  auto first_insn_it = cfg.find_insn(cml.first_insn, cml.hint_block);
  if (first_insn_it.is_end()) {
    // This should not happen, as for each candidate we never produce
    // overlapping locations in a method, and overlaps across selected
    // candidates are prevented by meticulously removing remaining overlapping
    // occurrences after processing a candidate.
    not_reached();
  }

  auto* code = method->get_code();
  if (code->get_debug_item() == nullptr) {
    // Create an empty item so that debug info of method we are outlining from
    // does not get lost.
    code->set_debug_item(std::make_unique<DexDebugItem>());
    // Create a synthetic initial position.
    cfg.insert_before(cfg.entry_block(),
                      cfg.entry_block()->get_first_non_param_loading_insn(),
                      DexPosition::make_synthetic_entry_position(method));
    TRACE(ISO, 6,
          "[instruction sequence outliner] setting debug item and synthetic "
          "entry position in %s",
          SHOW(method));
  }

  auto* last_dbg_pos = skip_fileless(cfg.get_dbg_pos(first_insn_it));
  cfg::CFGMutation cfg_mutation(cfg);
  const auto first_arg_reg = c.temp_regs;
  std::optional<reg_t> last_arg_reg;
  std::vector<reg_t> arg_regs;
  std::function<void(const CandidateNode& cn,
                     big_blocks::InstructionIterator it)>
      walk;
  auto gather_arg_regs = [first_arg_reg, &last_arg_reg,
                          &arg_regs](reg_t mapped_reg, reg_t reg) {
    if (mapped_reg >= first_arg_reg &&
        (!last_arg_reg || mapped_reg > *last_arg_reg)) {
      last_arg_reg = mapped_reg;
      arg_regs.push_back(reg);
    }
  };
  walk = [&walk, &last_dbg_pos, &gather_arg_regs, &cml, &cfg, &cfg_mutation](
             const CandidateNode& cn, big_blocks::InstructionIterator it) {
    cfg::Block* last_block{nullptr};
    std::optional<cfg::InstructionIterator> last_insn_it;
    for (size_t insn_idx = 0; insn_idx < cn.insns.size();
         last_block = it.block(), last_insn_it = it.unwrap(), insn_idx++,
                it++) {
      const auto& ci = cn.insns.at(insn_idx);
      always_assert(it->insn->opcode() == ci.core.opcode);
      for (size_t i = 0; i < ci.srcs.size(); i++) {
        gather_arg_regs(ci.srcs.at(i), it->insn->src(i));
      }
      if (!opcode::is_move_result_any(it->insn->opcode())) {
        cfg_mutation.remove(it.unwrap());
      }
    }
    if (cn.succs.empty()) {
      if (cn.res_reg) {
        gather_arg_regs(*cn.res_reg, *cml.out_reg);
      }
      if (last_insn_it) {
        auto* dbg_pos = skip_fileless(cfg.get_dbg_pos(*last_insn_it));
        if (dbg_pos != nullptr) {
          last_dbg_pos = dbg_pos;
        }
      }
    } else {
      always_assert(last_block != nullptr);
      auto succs = get_ordered_goto_and_branch_succs(last_block);
      always_assert(succs.size() == cn.succs.size());
      for (size_t i = 0; i < succs.size(); i++) {
        always_assert(normalize(succs.at(i)) == cn.succs.at(i).first);
        auto succ_cn = *cn.succs.at(i).second;
        auto* succ_block = succs.at(i)->target();
        auto succ_ii = InstructionIterable(succ_block);
        auto succ_it = big_blocks::InstructionIterator(
            succ_block->to_cfg_instruction_iterator(succ_ii.begin()));
        walk(succ_cn, succ_it);
      }
    }
  };
  walk(c.root, big_blocks::InstructionIterator(first_insn_it,
                                               /* ignore_throws */ true));

  // Generate and insert invocation instructions
  std::vector<IRInstruction*> outlined_method_invocation;
  IRInstruction* invoke_insn = new IRInstruction(OPCODE_INVOKE_STATIC);
  invoke_insn->set_method(outlined_method);
  invoke_insn->set_srcs(arg_regs);
  outlined_method_invocation.push_back(invoke_insn);
  IRInstruction* move_result_insn = nullptr;
  if (c.res_type != nullptr) {
    move_result_insn =
        new IRInstruction(opcode::move_result_for_invoke(outlined_method));
    move_result_insn->set_dest(*cml.out_reg);
    outlined_method_invocation.push_back(move_result_insn);
  }
  cfg_mutation.insert_before(first_insn_it, outlined_method_invocation);

  std::unique_ptr<DexPosition> new_dbg_pos;
  if (call_site_pattern_ids != nullptr) {
    auto* manager = g_redex->get_position_pattern_switch_manager();
    auto pattern_id = call_site_pattern_ids->at(cml.first_insn);
    new_dbg_pos = manager->make_pattern_position(pattern_id);
  } else {
    new_dbg_pos = std::make_unique<DexPosition>(
        DexString::make_string("RedexGenerated"), 0);
    new_dbg_pos->bind(DexString::make_string(show(outlined_method)));
  }

  cfg_mutation.insert_before(first_insn_it, std::move(new_dbg_pos));
  if (last_dbg_pos != nullptr) {
    new_dbg_pos = std::make_unique<DexPosition>(*last_dbg_pos);
  } else {
    new_dbg_pos = DexPosition::make_synthetic_entry_position(method);
    TRACE(
        ISO, 6,
        "[instruction sequence outliner] reverting to synthetic position in %s",
        SHOW(method));
  }
  cfg_mutation.insert_after(first_insn_it, std::move(new_dbg_pos));
  cfg_mutation.flush();
}

// Manages references and assigns numeric ids to classes
// We don't want to use more methods or types than are available, so we gather
// all already used references in the given scope.
class DexState {
 private:
  PassManager& m_mgr;
  DexClasses& m_dex;
  size_t m_dex_id;
  UnorderedSet<const DexType*> m_type_refs;
  size_t m_method_refs_count;
  UnorderedMap<const DexType*, size_t> m_class_ids;
  size_t max_type_refs;

 public:
  DexState() = delete;
  DexState(const DexState&) = delete;
  DexState& operator=(const DexState&) = delete;
  DexState(PassManager& mgr,
           const init_classes::InitClassesWithSideEffects&
               init_classes_with_side_effects,
           DexClasses& dex,
           size_t dex_id,
           size_t reserved_trefs,
           size_t reserved_mrefs)
      : m_mgr(mgr), m_dex(dex), m_dex_id(dex_id) {
    UnorderedSet<DexMethodRef*> method_refs;
    std::vector<const DexType*> init_classes;
    for (auto* cls : dex) {
      cls->gather_methods(method_refs);
      cls->gather_types(m_type_refs);
      cls->gather_init_classes(init_classes);
    }
    m_method_refs_count = method_refs.size() + reserved_mrefs;

    walk::classes(dex, [&class_ids = m_class_ids](DexClass* cls) {
      class_ids.emplace(cls->get_type(), class_ids.size());
    });

    UnorderedSet<DexType*> refined_types;
    for (const auto* type : init_classes) {
      const auto* refined_type = init_classes_with_side_effects.refine(type);
      if (refined_type != nullptr) {
        m_type_refs.insert(refined_type->to_mutable());
      }
    }
    max_type_refs =
        get_max_type_refs(m_mgr.get_redex_options().min_sdk) - reserved_trefs;
  }

  size_t get_dex_id() { return m_dex_id; }

  bool can_insert_type_refs(const UnorderedSet<const DexType*>& types) {
    size_t inserted_count{0};
    for (const auto* t : UnorderedIterable(types)) {
      if (m_type_refs.count(t) == 0u) {
        inserted_count++;
      }
    }
    // Yes, looks a bit quirky, but matching what happens in
    // InterDex/DexStructure: The number of type refs must stay *below* the
    // maximum, and must never reach it.
    if ((m_type_refs.size() + inserted_count) >= max_type_refs) {
      m_mgr.incr_metric("kMaxTypeRefs", 1);
      TRACE(ISO, 2, "[invoke sequence outliner] hit kMaxTypeRefs");
      return false;
    }
    return true;
  }

  void insert_type_refs(const UnorderedSet<const DexType*>& types) {
    always_assert(can_insert_type_refs(types));
    insert_unordered_iterable(m_type_refs, types);
    always_assert(m_type_refs.size() < max_type_refs);
  }

  bool can_insert_method_ref() {
    if (m_method_refs_count >= kMaxMethodRefs) {
      m_mgr.incr_metric("kMaxMethodRefs", 1);
      TRACE(ISO, 2, "[invoke sequence outliner] hit kMaxMethodRefs");
      return false;
    }
    return true;
  }

  void insert_method_ref() {
    always_assert(can_insert_method_ref());
    m_method_refs_count++;
    always_assert(m_method_refs_count <= kMaxMethodRefs);
  }

  // insert at beginning of dex, but after canary class, if any
  void insert_outlined_class(DexClass* outlined_cls) {
    auto it = m_dex.begin();
    for (; it != m_dex.end() && (is_canary(*it) || (*it)->rstate.outlined());
         it++) {
    }
    m_dex.insert(it, outlined_cls);
  }

  // Class ids represent the position of a class in the dex; we use this to
  // determine if class in the dex, which one comes first, when deciding
  // on a host class for an outlined method.
  std::optional<size_t> get_class_id(const DexType* t) {
    auto it = m_class_ids.find(t);
    return it == m_class_ids.end() ? std::nullopt
                                   : std::optional<size_t>(it->second);
  }
};

// Provides facilities to select existing, or create new host classes for
// outlined methods
class HostClassSelector {
 private:
  const Config& m_config;
  PassManager& m_mgr;
  DexState& m_dex_state;
  DexClass* m_outlined_cls{nullptr};
  size_t m_outlined_classes{0};
  size_t m_hosted_direct_count{0};
  size_t m_hosted_base_count{0};
  size_t m_hosted_at_refs_count{0};
  size_t m_hosted_helper_count{0};
  int m_min_sdk;
  size_t m_iteration;

 public:
  HostClassSelector() = delete;
  HostClassSelector(const HostClassSelector&) = delete;
  HostClassSelector& operator=(const HostClassSelector&) = delete;
  HostClassSelector(const Config& config,
                    PassManager& mgr,
                    DexState& dex_state,
                    int min_sdk,
                    size_t iteration)
      : m_config(config),
        m_mgr(mgr),
        m_dex_state(dex_state),
        m_min_sdk(min_sdk),
        m_iteration(iteration) {}
  ~HostClassSelector() {
    m_mgr.incr_metric("num_hosted_direct_count", m_hosted_direct_count);
    m_mgr.incr_metric("num_hosted_base_count", m_hosted_base_count);
    m_mgr.incr_metric("num_hosted_at_refs_count", m_hosted_at_refs_count);
    m_mgr.incr_metric("num_hosted_helper_count", m_hosted_helper_count);
    TRACE(ISO, 2,
          "[invoke sequence outliner] %zu direct, %zu base, %zu at refs, %zu "
          "helpers hosted",
          m_hosted_direct_count, m_hosted_base_count, m_hosted_at_refs_count,
          m_hosted_helper_count);

    m_mgr.incr_metric("num_outlined_classes", m_outlined_classes);
    TRACE(ISO, 2,
          "[invoke sequence outliner] %zu outlined helper classes created",
          m_outlined_classes);
  }

  // Return current outlined helper class, if exists and we can add one more
  // method to it
  DexType* reuse_last_outlined_class() {
    if ((m_outlined_cls == nullptr) ||
        m_outlined_cls->get_dmethods().size() >=
            m_config.max_outlined_methods_per_class) {
      return nullptr;
    }
    return m_outlined_cls->get_type();
  }

  // Create type that will represent next outlined helper class
  DexType* peek_at_next_outlined_class() {
    const auto* name = DexString::make_string(
        std::string(OUTLINED_CLASS_NAME_PREFIX) + std::to_string(m_iteration) +
        "$" + std::to_string(m_dex_state.get_dex_id()) + "$" +
        std::to_string(m_outlined_classes) + ";");
    return DexType::make_type(name);
  }

  // Create a new helper class into which we can place outlined methods.
  void create_next_outlined_class() {
    always_assert(reuse_last_outlined_class() == nullptr);
    auto* outlined_type = peek_at_next_outlined_class();
    m_outlined_classes++;
    ClassCreator cc(outlined_type);
    cc.set_access(ACC_PUBLIC | ACC_FINAL);
    cc.set_super(type::java_lang_Object());
    m_outlined_cls = cc.create();
    m_outlined_cls->rstate.set_generated();
    m_outlined_cls->rstate.set_outlined();
    m_outlined_cls->set_perf_sensitive(PerfSensitiveGroup::OUTLINED);
    m_dex_state.insert_outlined_class(m_outlined_cls);
  }

  const DexType* get_direct_or_base_class(
      UnorderedSet<const DexType*> types,
      const std::function<UnorderedSet<const DexType*>(
          const UnorderedSet<const DexType*>&)>& get_super_classes,
      const std::function<bool(const DexType*)>& predicate =
          [](const DexType*) { return true; }) {
    // When there's only one type, try to use that
    if (types.size() == 1) {
      const auto* direct_type = *unordered_any(types);
      if (m_dex_state.get_class_id(direct_type) && predicate(direct_type)) {
        auto* direct_cls = type_class(direct_type);
        always_assert(direct_cls);
        if (can_rename(direct_cls) && can_delete(direct_cls)) {
          return direct_type;
        }
      }
    }

    // Try to find the first allowable base types
    const DexType* host_class{nullptr};
    std::optional<size_t> host_class_id;
    auto super_classes = get_super_classes(types);
    for (const auto* type : UnorderedIterable(super_classes)) {
      auto class_id = m_dex_state.get_class_id(type);
      if (!class_id || !predicate(type)) {
        continue;
      }
      auto* cls = type_class(type);
      if ((cls == nullptr) || !can_rename(cls) || !can_delete(cls)) {
        continue;
      }
      // In particular, use the base type that appears first in this dex.
      if (host_class == nullptr || *host_class_id > *class_id) {
        host_class_id = class_id;
        host_class = type;
      }
    }
    return host_class;
  }

  const DexType* get_direct_or_base_class(const Candidate& c,
                                          const CandidateInfo& ci,
                                          bool* not_outlinable) {
    *not_outlinable = false;
    // When all candidate instances come from methods of a single class, use
    // that type as the host class
    auto declaring_types = get_declaring_types(ci);
    always_assert(!declaring_types.empty());

    auto can_be_host_class = [min_sdk = m_min_sdk](const DexType* type) {
      auto* cls = type_class(type);
      // Before Android 7, invoking static methods defined in interfaces was
      // not supported. See rule A24 in
      // https://source.android.com/devices/tech/dalvik/constraints
      return min_sdk >= 24 || ((cls != nullptr) && !is_interface(cls));
    };

    // Whether this type will not trigger a clinit
    auto no_clinit = [](const DexType* type) {
      while (true) {
        auto* cls = type_class(type);
        if ((cls == nullptr) || cls->is_external()) {
          // We stop at external classes
          return true;
        }
        if (cls->get_clinit() != nullptr) {
          return false;
        }
        type = cls->get_super_class();
      }
    };

    const auto* host_class =
        get_direct_or_base_class(declaring_types, get_common_super_classes);
    if (declaring_types.size() == 1) {
      const auto* direct_type = *unordered_any(declaring_types);
      if (host_class == direct_type && can_be_host_class(host_class)) {
        m_hosted_direct_count++;
        return host_class;
      }
      if (has_non_init_invoke_directs(c)) {
        // TODO: Consider making those methods static if they can be renamed,
        // just like what the inliner does
        *not_outlinable = true;
        return nullptr;
      }
    }
    always_assert(!has_non_init_invoke_directs(c));

    if ((host_class != nullptr) && can_be_host_class(host_class)) {
      m_hosted_base_count++;
      return host_class;
    }

    // If an outlined code snippet occurs in many unrelated classes, but always
    // references some types that share a common base type, then that common
    // base type is a reasonable place where to put the outlined code.
    auto referenced_types = get_referenced_types(c);
    // Let's see if we can reduce the set to a most specific sub-type
    if (referenced_types.size() > 1) {
      auto common_super_classes = get_common_super_classes(referenced_types);
      for (const auto* t : UnorderedIterable(common_super_classes)) {
        referenced_types.erase(t);
      }
    }
    host_class = get_direct_or_base_class(
        referenced_types, get_super_classes,
        [&can_be_host_class, no_clinit](const DexType* type) {
          return can_be_host_class(type) && no_clinit(type);
        });
    if (host_class != nullptr) {
      m_hosted_at_refs_count++;
      return host_class;
    }

    // Fallback: put the outlined method in a dedicated helper class.
    m_hosted_helper_count++;
    return nullptr;
  }
};

using NewlyOutlinedMethods = UnorderedMap<DexMethod*, std::vector<DexMethod*>>;

// Outlining all occurrences of a particular candidate.
bool outline_candidate(const Config& config,
                       const DexStore* store,
                       const DexStoreDependencies& store_dependencies,
                       const Candidate& c,
                       const CandidateInfo& ci,
                       ReusableOutlinedMethods* outlined_methods,
                       NewlyOutlinedMethods* newly_outlined_methods,
                       DexState* dex_state,
                       HostClassSelector* host_class_selector,
                       OutlinedMethodCreator* outlined_method_creator,
                       size_t* num_reused_methods,
                       bool reuse_outlined_methods_across_dexes) {
  // Before attempting to create or reuse an outlined method that hasn't been
  // referenced in this dex before, we'll make sure that all the involved
  // type refs can be added to the dex. We collect those type refs.
  UnorderedSet<const DexType*> type_refs_to_insert;
  for (const auto* t : c.arg_types) {
    type_refs_to_insert.insert(t->to_mutable());
  }
  const auto* rtype = c.res_type != nullptr ? c.res_type : type::_void();
  type_refs_to_insert.insert(rtype);

  DexMethod* outlined_method{
      find_reusable_method(store, store_dependencies, c, ci, *outlined_methods,
                           reuse_outlined_methods_across_dexes)};
  if (outlined_method != nullptr) {
    type_refs_to_insert.insert(outlined_method->get_class());
    if (!dex_state->can_insert_type_refs(type_refs_to_insert)) {
      return false;
    }

    if (config.full_dbg_positions) {
      auto& c_outlined_methods = outlined_methods->map.at(c);
      auto it =
          std::find_if(c_outlined_methods.begin(), c_outlined_methods.end(),
                       [outlined_method](const auto& p) {
                         return p.method == outlined_method;
                       });
      outlined_method_creator->add_outlined_dbg_position_patterns(
          c, ci, &it->pattern_ids, &it->slot_provenance);
    }
    (*num_reused_methods)++;

    TRACE(ISO, 5, "[invoke sequence outliner] reused %s",
          SHOW(outlined_method));
  } else {
    bool not_outlinable;
    const auto* host_class =
        host_class_selector->get_direct_or_base_class(c, ci, &not_outlinable);
    if (not_outlinable) {
      return false;
    }
    bool must_create_next_outlined_class{false};
    if (host_class == nullptr) {
      host_class = host_class_selector->reuse_last_outlined_class();
      if (host_class == nullptr) {
        host_class = host_class_selector->peek_at_next_outlined_class();
        must_create_next_outlined_class = true;
      }
    }
    type_refs_to_insert.insert(host_class);
    if (!dex_state->can_insert_type_refs(type_refs_to_insert)) {
      return false;
    }
    if (must_create_next_outlined_class) {
      host_class_selector->create_next_outlined_class();
    }
    std::set<uint32_t> position_pattern_ids;
    PatternSlotProvenance slot_provenance;
    outlined_method = outlined_method_creator->create_outlined_method(
        c, ci, host_class, &position_pattern_ids, &slot_provenance);
    outlined_methods->order.push_back(c);
    outlined_methods->map[c].push_back({store, outlined_method,
                                        position_pattern_ids,
                                        std::move(slot_provenance)});
    auto& methods = (*newly_outlined_methods)[outlined_method];
    for (const auto& p : UnorderedIterable(ci.methods)) {
      methods.push_back(p.first);
    }
  }

  DexClass* outlined_method_host_cls = type_class(outlined_method->get_class());
  dex_state->insert_type_refs(type_refs_to_insert);
  auto* call_site_pattern_ids =
      outlined_method_creator->get_call_site_pattern_ids();
  for (const auto& p : UnorderedIterable(ci.methods)) {
    auto* method = p.first;
    // If any outlined method comes from BETAMAP class, its host class should
    // also marked as BETAMAP_ORDERED.
    if (outlined_method_host_cls->get_perf_sensitive() !=
        PerfSensitiveGroup::BETAMAP_ORDERED) {
      DexClass* method_host_cls = type_class(method->get_class());
      if (method_host_cls->get_perf_sensitive() ==
          PerfSensitiveGroup::BETAMAP_ORDERED) {
        outlined_method_host_cls->set_perf_sensitive(
            PerfSensitiveGroup::BETAMAP_ORDERED);
      }
    }
    auto& cfg = method->get_code()->cfg();

    TRACE(ISO, 7, "[invoke sequence outliner] before outlined %s from %s\n%s",
          SHOW(outlined_method), SHOW(method), SHOW(cfg));
    for (const auto& cml : p.second) {
      rewrite_at_location(outlined_method, call_site_pattern_ids, method, cfg,
                          c, cml);
    }
    TRACE(ISO, 6, "[invoke sequence outliner] after outlined %s from %s\n%s",
          SHOW(outlined_method), SHOW(method), SHOW(cfg));
  }
  return true;
}

// Perform outlining of most beneficial candidates, while staying within
// reference limits.
static NewlyOutlinedMethods outline(
    const Config& config,
    PassManager& mgr,
    const DexStore* store,
    const DexStoreDependencies& store_dependencies,
    DexState& dex_state,
    int min_sdk,
    std::vector<CandidateWithInfo>* candidates_with_infos,
    UnorderedMap<DexMethod*, UnorderedSet<CandidateId>>*
        candidate_ids_by_methods,
    ReusableOutlinedMethods* outlined_methods,
    size_t iteration,
    size_t* num_reused_methods) {
  MethodNameGenerator method_name_generator(mgr, iteration);
  OutlinedMethodCreator outlined_method_creator(config, mgr,
                                                method_name_generator);
  HostClassSelector host_class_selector(config, mgr, dex_state, min_sdk,
                                        iteration);
  // While we have a set of beneficial candidates, many are overlapping each
  // other. We are using a priority queue to iteratively outline the most
  // beneficial candidate at any point in time, then removing all impacted
  // other overlapping occurrences, which in turn changes the priority of
  // impacted candidates, until there is no more beneficial candidate left.
  using Priority = uint64_t;
  MutablePriorityQueue<CandidateId, Priority> pq;
  auto get_priority = [&config, store, &store_dependencies,
                       &candidates_with_infos,
                       outlined_methods](CandidateId id) {
    auto& cwi = candidates_with_infos->at(id);
    auto savings = get_savings(config, store, store_dependencies, cwi.candidate,
                               cwi.info, *outlined_methods);
    auto size = cwi.candidate.size;
    auto count = cwi.info.count;
    Priority primary_priority = (savings + 1) * 100000 / (size * count);
    // clip primary_priority to 32-bit
    if (primary_priority >= (static_cast<uint64_t>(1u) << 32)) {
      primary_priority = (static_cast<uint64_t>(1u) << 32) - 1;
    }
    // make unique via candidate id
    return (primary_priority << 32) | id;
  };
  auto erase = [&pq, candidate_ids_by_methods](CandidateId id,
                                               CandidateWithInfo& cwi) {
    pq.erase(id);
    for (auto& p : UnorderedIterable(cwi.info.methods)) {
      (*candidate_ids_by_methods)[p.first].erase(id);
    }
    cwi.info.methods.clear();
    cwi.info.count = 0;
  };
  for (CandidateId id = 0; id < candidates_with_infos->size(); id++) {
    pq.insert(id, get_priority(id));
  }
  size_t total_savings{0};
  size_t outlined_count{0};
  size_t outlined_sequences_count{0};
  size_t not_outlined_count{0};
  NewlyOutlinedMethods newly_outlined_methods;
  while (!pq.empty()) {
    // Make sure beforehand that there's a method ref left for us
    if (!dex_state.can_insert_method_ref()) {
      break;
    }

    auto id = pq.front();
    auto& cwi = candidates_with_infos->at(id);
    auto savings = get_savings(config, store, store_dependencies, cwi.candidate,
                               cwi.info, *outlined_methods);
    always_assert(savings > 0);
    total_savings += savings;
    outlined_count += cwi.info.count;
    outlined_sequences_count++;

    TRACE(ISO, 3,
          "[invoke sequence outliner] %4zx(%3zu) [%zu]: %zu byte savings",
          cwi.info.count, cwi.info.methods.size(), cwi.candidate.size,
          2 * savings);
    if (outline_candidate(config, store, store_dependencies, cwi.candidate,
                          cwi.info, outlined_methods, &newly_outlined_methods,
                          &dex_state, &host_class_selector,
                          &outlined_method_creator, num_reused_methods,
                          config.reuse_outlined_methods_across_dexes)) {
      dex_state.insert_method_ref();
    } else {
      TRACE(ISO, 3, "[invoke sequence outliner] could not outline");
      not_outlined_count++;
    }

    // Remove overlapping occurrences
    UnorderedSet<CandidateId> other_candidate_ids_with_changes;
    for (auto& p : UnorderedIterable(cwi.info.methods)) {
      auto* method = p.first;
      auto& cmls = p.second;
      for (auto other_id :
           UnorderedIterable(candidate_ids_by_methods->at(method))) {
        if (other_id == id) {
          continue;
        }
        auto& other_c = candidates_with_infos->at(other_id);
        for (auto& cml : cmls) {
          auto& other_cmls = other_c.info.methods.at(method);
          std::erase_if(other_cmls, [&](auto& other_cml) {
            if (ranges_overlap(cml.ranges, other_cml.ranges)) {
              other_c.info.count--;
              if (other_id != id) {
                other_candidate_ids_with_changes.insert(other_id);
              }
              return true;
            }
            return false;
          });
        }
      }
    }
    erase(id, cwi);
    // Update priorities of affected candidates
    for (auto other_id : UnorderedIterable(other_candidate_ids_with_changes)) {
      auto& other_cwi = candidates_with_infos->at(other_id);
      auto other_savings =
          get_savings(config, store, store_dependencies, other_cwi.candidate,
                      other_cwi.info, *outlined_methods);
      if (other_savings == 0) {
        erase(other_id, other_cwi);
      } else {
        pq.update_priority(other_id, get_priority(other_id));
      }
    }
  }

  mgr.incr_metric("num_not_outlined", not_outlined_count);
  TRACE(ISO, 2, "[invoke sequence outliner] %zu not outlined",
        not_outlined_count);

  mgr.incr_metric("num_outlined", outlined_count);
  mgr.incr_metric("num_outlined_sequences", outlined_sequences_count);
  mgr.incr_metric("num_total_savings", total_savings);
  TRACE(ISO, 1,
        "[invoke sequence outliner] %zu unique sequences outlined in %zu "
        "places; %zu total savings",
        outlined_sequences_count, outlined_count, total_savings);
  return newly_outlined_methods;
}

size_t count_affected_methods(
    const NewlyOutlinedMethods& newly_outlined_methods) {
  UnorderedSet<DexMethod*> methods;
  for (const auto& p : UnorderedIterable(newly_outlined_methods)) {
    methods.insert(p.second.begin(), p.second.end());
  }
  return methods.size();
}

////////////////////////////////////////////////////////////////////////////////
// reorder_with_method_profiles
////////////////////////////////////////////////////////////////////////////////

UnorderedMap<const DexMethodRef*, double> get_methods_global_order(
    ConfigFiles& config_files, const Config& config) {
  if (!config.reorder_with_method_profiles) {
    return {};
  }
  auto& method_profiles = config_files.get_method_profiles();
  if (!method_profiles.has_stats()) {
    return {};
  }

  UnorderedMap<std::string, size_t> interaction_indices;
  auto register_interaction = [&](const std::string& interaction_id) {
    return interaction_indices
        .emplace(interaction_id, interaction_indices.size())
        .first->second;
  };
  // Make sure that the "ColdStart" interaction comes before everything else
  register_interaction("ColdStart");
  UnorderedMap<const DexMethodRef*, double> methods_global_order;
  for (const auto& p : method_profiles.all_interactions()) {
    const auto& interaction_id = p.first;
    const auto& method_stats = p.second;
    auto index = register_interaction(interaction_id);
    TRACE(ISO, 3,
          "[instruction sequence outliner] Interaction [%s] gets index %zu",
          interaction_id.c_str(), index);
    for (const auto& q : UnorderedIterable(method_stats)) {
      // Seed the running minimum with infinity, as reorder_with_method_profiles
      // does. operator[] would default-construct 0.0, and every candidate here
      // is non-negative (index >= 0 and order_percent in [0, 100]), so the
      // minimum would be 0.0 for every method no matter what the profile says.
      auto it =
          methods_global_order
              .try_emplace(q.first, std::numeric_limits<double>::infinity())
              .first;
      it->second = std::min(it->second, static_cast<double>(index * 100) +
                                            q.second.order_percent);
    }
  }
  auto ordered_methods = unordered_to_ordered_keys(
      methods_global_order, [&](const DexMethodRef* a, const DexMethodRef* b) {
        auto a_order = methods_global_order.at(a);
        auto b_order = methods_global_order.at(b);
        if (a_order != b_order) {
          return a_order < b_order;
        }
        return compare_dexmethods(a, b);
      });
  TRACE(ISO, 4, "[instruction sequence outliner] %zu globally ordered methods",
        ordered_methods.size());
  for (const auto* method : ordered_methods) {
    TRACE(ISO, 5, "[instruction sequence outliner] [%f] %s",
          methods_global_order.at(method), SHOW(method));
  }
  return methods_global_order;
}

void reorder_with_method_profiles(
    const Config& config,
    PassManager& mgr,
    const Scope& dex,
    const UnorderedMap<const DexMethodRef*, double>& methods_global_order,
    const NewlyOutlinedMethods& newly_outlined_methods) {
  if (methods_global_order.empty()) {
    return;
  }

  UnorderedMap<const DexMethod*, double> outlined_methods_global_order;
  std::vector<DexMethod*> ordered_outlined_methods;
  UnorderedSet<DexClass*> outlined_classes;
  for (const auto& p : UnorderedIterable(newly_outlined_methods)) {
    auto* cls = type_class(p.first->get_class());
    if (!cls->rstate.outlined()) {
      continue;
    }
    outlined_classes.insert(cls);
    auto min_order = std::numeric_limits<double>::infinity();
    for (auto* method : p.second) {
      auto it = methods_global_order.find(method);
      if (it != methods_global_order.end()) {
        min_order = std::min(min_order, it->second);
      }
    }
    outlined_methods_global_order.emplace(p.first, min_order);
    ordered_outlined_methods.push_back(p.first);
  }
  std::vector<DexClass*> ordered_outlined_classes;
  for (auto* cls : dex) {
    if (outlined_classes.count(cls) != 0u) {
      ordered_outlined_classes.push_back(cls);
      TRACE(ISO, 5,
            "[instruction sequence outliner] Found outlined class %s with %zu "
            "methods",
            SHOW(cls), cls->get_dmethods().size());
    }
  }
  std::sort(ordered_outlined_methods.begin(),
            ordered_outlined_methods.end(),
            [&](const DexMethod* a, const DexMethod* b) {
              auto a_order = outlined_methods_global_order.at(a);
              auto b_order = outlined_methods_global_order.at(b);
              if (a_order != b_order) {
                return a_order < b_order;
              }
              // If order is same, prefer smaller methods, as they are likely
              // invoked more often / have higher invocation cost
              auto a_size = a->get_code()->sum_opcode_sizes();
              auto b_size = b->get_code()->sum_opcode_sizes();
              if (a_size != b_size) {
                return a_size < b_size;
              }
              // Then use the method name (which is essentially a stable hash of
              // the instructions) as a tie-breaker.
              if (a->get_name() != b->get_name()) {
                return compare_dexstrings(a->get_name(), b->get_name());
              }
              // Final tie-breaker is full method signature comparison
              return compare_dexmethods(a, b);
            });
  TRACE(ISO, 4,
        "[instruction sequence outliner] %zu globally ordered outlined methods",
        ordered_outlined_methods.size());
  for (auto* method : ordered_outlined_methods) {
    TRACE(ISO, 5, "[instruction sequence outliner] [%f] %s",
          outlined_methods_global_order.at(method), SHOW(method));
  }
  size_t class_index = 0;
  size_t methods_count = 0;
  size_t relocated_outlined_methods = 0;
  auto flush = [&]() {
    if (methods_count == 0) {
      return;
    }
    auto* cls = ordered_outlined_classes.at(class_index);
    TRACE(ISO, 4,
          "[instruction sequence outliner] Finished outlined class %s with "
          "%zu methods",
          SHOW(cls), cls->get_dmethods().size());
    class_index++;
    methods_count = 0;
  };
  for (auto* method : ordered_outlined_methods) {
    auto* target_class = ordered_outlined_classes.at(class_index);
    if (method->get_class() != target_class->get_type()) {
      TRACE(ISO, 4,
            "[instruction sequence outliner] Relocating outlined method %s "
            "from %s to %s",
            SHOW(method->get_name()), SHOW(method->get_class()),
            SHOW(target_class));
      change_visibility(method, target_class->get_type());
      relocate_method(method, target_class->get_type());
      method->set_deobfuscated_name(show(method));
      relocated_outlined_methods++;
    }
    if (++methods_count == config.max_outlined_methods_per_class) {
      flush();
    }
  }
  flush();
  mgr.incr_metric("num_relocated_outlined_methods", relocated_outlined_methods);
}

////////////////////////////////////////////////////////////////////////////////
// clear_cfgs
////////////////////////////////////////////////////////////////////////////////

static size_t count_methods(const Scope& scope) {
  std::atomic<size_t> methods{0};
  walk::parallel::code(scope, [&methods](DexMethod* method, IRCode&) {
    if (!can_outline_from_method(method)) {
      return;
    }
    methods++;
  });

  return (size_t)methods;
}

////////////////////////////////////////////////////////////////////////////////
// reorder_all_methods
////////////////////////////////////////////////////////////////////////////////

using OutlinedMethodsToReorder =
    std::vector<std::pair<const Scope*, const NewlyOutlinedMethods>>;
// helper function to reorder all the outlined methods
// after all the dex files are processed.
void reorder_all_methods(
    const Config& config,
    PassManager& mgr,
    const UnorderedMap<const DexMethodRef*, double>& methods_global_order,
    const OutlinedMethodsToReorder& outlined_methods_to_reorder) {
  for (const auto& dex_methods_pair : outlined_methods_to_reorder) {
    const auto& dex = dex_methods_pair.first;
    const auto& outlined_methods = dex_methods_pair.second;
    reorder_with_method_profiles(config, mgr, *dex, methods_global_order,
                                 outlined_methods);
  }
}

////////////////////////////////////////////////////////////////////////////////
// derive_method_profiles_stats
////////////////////////////////////////////////////////////////////////////////
size_t derive_method_profiles_stats(
    ConfigFiles& config,
    const OutlinedMethodsToReorder& outlined_methods_by_dex) {
  auto& method_profiles = config.get_method_profiles();
  size_t res = 0;
  for (const auto& [dex, outlined_methods] : outlined_methods_by_dex) {
    for (const auto& [target, sources] : UnorderedIterable(outlined_methods)) {
      res += method_profiles.derive_stats(target, sources);
    }
  }
  return res;
}

class OutlinedMethodBodySetter {
 private:
  const Config& m_config;
  PassManager& m_mgr;
  size_t m_outlined_method_body_set{0};
  size_t m_outlined_method_nodes{0};
  size_t m_outlined_method_positions{0};
  size_t m_outlined_method_instructions{0};

 public:
  OutlinedMethodBodySetter() = delete;
  OutlinedMethodBodySetter(const OutlinedMethodBodySetter&) = delete;
  OutlinedMethodBodySetter& operator=(const OutlinedMethodBodySetter&) = delete;
  explicit OutlinedMethodBodySetter(const Config& config, PassManager& mgr)
      : m_config(config), m_mgr(mgr) {}

  ~OutlinedMethodBodySetter() {
    m_mgr.incr_metric("num_outlined_method_body_set",
                      m_outlined_method_body_set);
    m_mgr.incr_metric("num_outlined_method_instructions",
                      m_outlined_method_instructions);
    m_mgr.incr_metric("num_outlined_method_nodes", m_outlined_method_nodes);
    m_mgr.incr_metric("num_outlined_method_positions",
                      m_outlined_method_positions);
    TRACE(ISO, 2,
          "[invoke sequence outliner] set body for %zu outlined methods with "
          "%zu "
          "instructions across %zu nodes and %zu positions",
          m_outlined_method_body_set, m_outlined_method_instructions,
          m_outlined_method_nodes, m_outlined_method_positions);
  }

  // Construct an IRCode datastructure from a candidate.
  std::unique_ptr<IRCode> get_outlined_code(
      DexMethod* outlined_method,
      const Candidate& c,
      const std::set<uint32_t>& current_pattern_ids,
      const PatternSlotProvenance& slots) {
    auto* manager = g_redex->get_position_pattern_switch_manager();
    std::map<uint32_t, const PositionPattern*> current_patterns;
    bool any_positions = false;
    const auto& all_managed_patterns = manager->get_patterns();
    for (auto pattern_id : current_pattern_ids) {
      const auto* pattern = &all_managed_patterns.at(pattern_id);
      current_patterns.emplace(pattern_id, pattern);
      if (!pattern->empty()) {
        any_positions = true;
      }
    }
    auto code = std::make_unique<IRCode>(outlined_method, c.temp_regs);
    if (any_positions) {
      code->set_debug_item(std::make_unique<DexDebugItem>());
    }
    std::function<void(const CandidateNode& cn)> walk;
    UnorderedMap<DexPosition*, DexPosition*> cloned_dbg_positions;
    std::function<DexPosition*(DexPosition*)> get_or_add_cloned_dbg_position;
    get_or_add_cloned_dbg_position =
        [this, &code, &get_or_add_cloned_dbg_position,
         &cloned_dbg_positions](DexPosition* dbg_pos) -> DexPosition* {
      always_assert(dbg_pos);
      auto it = cloned_dbg_positions.find(dbg_pos);
      if (it != cloned_dbg_positions.end()) {
        return it->second;
      }
      auto cloned_dbg_pos = std::make_unique<DexPosition>(*dbg_pos);
      if (dbg_pos->parent != nullptr) {
        cloned_dbg_pos->parent =
            get_or_add_cloned_dbg_position(dbg_pos->parent);
      }
      auto* cloned_dbg_pos_ptr = cloned_dbg_pos.get();
      code->push_back(std::move(cloned_dbg_pos));
      m_outlined_method_positions++;
      cloned_dbg_positions.emplace(dbg_pos, cloned_dbg_pos_ptr);
      return cloned_dbg_pos_ptr;
    };
    size_t dbg_positions_idx = 0;
    walk = [this, manager, &code, &current_patterns, any_positions, &walk, &c,
            &get_or_add_cloned_dbg_position, &slots,
            &dbg_positions_idx](const CandidateNode& cn) {
      m_outlined_method_nodes++;
      UnorderedMap<uint32_t, std::pair<DexPosition*, DexPosition*>>
          last_dbg_poses;
      for (auto& p : current_patterns) {
        last_dbg_poses.emplace(p.first, std::make_pair(nullptr, nullptr));
      }
      for (const auto& ci : cn.insns) {
        if (!opcode::is_a_move_result_pseudo(ci.core.opcode) && any_positions) {
          PositionSwitch position_switch;
          bool any_changed = false;
          for (auto& p : current_patterns) {
            auto pattern_id = p.first;
            auto& pattern = p.second;
            DexPosition* dbg_pos =
                pattern->empty() ? nullptr : pattern->at(dbg_positions_idx);
            auto* provenance =
                pattern->empty()
                    ? nullptr
                    : slot_provenance(slots, pattern_id, dbg_positions_idx);
            position_switch.push_back({pattern_id, dbg_pos, provenance});
            // A slot that keeps the same position but changes provenance
            // still needs a new entry, or its instructions would inherit the
            // previous slot's.
            auto& [last_dbg_pos, last_provenance] =
                last_dbg_poses.at(pattern_id);
            if (dbg_pos != last_dbg_pos || provenance != last_provenance) {
              always_assert(dbg_pos);
              any_changed = true;
              last_dbg_pos = dbg_pos;
              last_provenance = provenance;
            }
          }
          if (any_changed) {
            if (current_patterns.size() == 1) {
              // Always push a new leaf: the cache would return an earlier
              // leaf without a position entry, leaving the instructions
              // under whatever position came last. A slot with provenance
              // gets a clone of its provenance snapshot -- each level's
              // candidate set or mark copies with it; its callers come from
              // the snapshot too, so a caller's set survives.
              auto* dbg_pos = position_switch.front().emitted_position();
              auto cloned_dbg_pos = std::make_unique<DexPosition>(*dbg_pos);
              if (dbg_pos->parent != nullptr) {
                cloned_dbg_pos->parent =
                    get_or_add_cloned_dbg_position(dbg_pos->parent);
              }
              code->push_back(std::move(cloned_dbg_pos));
              m_outlined_method_positions++;
            } else {
              always_assert(position_switch.size() >= 2);
              auto switch_id = manager->make_switch(position_switch);
              code->push_back(manager->make_switch_position(switch_id));
            }
          }
        }
        dbg_positions_idx++;
        if (m_config.debug_make_crashing &&
            opcode::is_an_iget(ci.core.opcode)) {
          auto* const_insn = new IRInstruction(OPCODE_CONST);
          const_insn->set_literal(0);
          const_insn->set_dest(ci.srcs.at(0));
          code->push_back(const_insn);
        }
        auto* insn = new IRInstruction(ci.core.opcode);
        insn->set_srcs(ci.srcs);
        if (ci.dest) {
          insn->set_dest(*ci.dest);
        }
        if (insn->has_method()) {
          insn->set_method(ci.core.method);
        } else if (insn->has_field()) {
          insn->set_field(ci.core.field);
        } else if (insn->has_string()) {
          insn->set_string(ci.core.string);
        } else if (insn->has_type()) {
          insn->set_type(ci.core.type);
        } else if (insn->has_literal()) {
          insn->set_literal(ci.core.literal);
        } else if (insn->has_data()) {
          insn->set_data(ci.core.data->clone_as_unique_ptr());
        }
        code->push_back(insn);
      }
      m_outlined_method_instructions += cn.insns.size();
      if (cn.succs.empty()) {
        if (c.res_type != nullptr) {
          IROpcode ret_opcode =
              type::is_object(c.res_type)      ? OPCODE_RETURN_OBJECT
              : type::is_wide_type(c.res_type) ? OPCODE_RETURN_WIDE
                                               : OPCODE_RETURN;
          auto* ret_insn = new IRInstruction(ret_opcode);
          ret_insn->set_src(0, *cn.res_reg);
          code->push_back(ret_insn);
        } else {
          auto* ret_insn = new IRInstruction(OPCODE_RETURN_VOID);
          code->push_back(ret_insn);
        }
      } else {
        auto& last_mie = *code->rbegin();
        for (const auto& p : cn.succs) {
          const auto& e = p.first;
          if (e.type == cfg::EDGE_GOTO) {
            always_assert(e == cn.succs.front().first);
            code->push_back(); // MFLOW_FALLTHROUGH
          } else {
            always_assert(e.type == cfg::EDGE_BRANCH);
            BranchTarget* branch_target =
                e.case_key ? new BranchTarget(&last_mie, *e.case_key)
                           : new BranchTarget(&last_mie);
            code->push_back(branch_target);
          }
          walk(*p.second);
        }
      }
    };
    walk(c.root);
    return code;
  }

  // set body for each method stored in ReusableOutlinedMethod
  void set_method_body(ReusableOutlinedMethods& outlined_methods) {
    for (auto& c : outlined_methods.order) {
      auto it = outlined_methods.map.find(c);
      always_assert(it != outlined_methods.map.end());
      auto& c_outlined_methods = it->second;
      auto& front = c_outlined_methods.front();
      auto& outlined_method = front.method;
      always_assert(!front.pattern_ids.empty());
      outlined_method->set_code(get_outlined_code(
          outlined_method, c, front.pattern_ids, front.slot_provenance));
      change_visibility(outlined_method->get_code(),
                        outlined_method->get_class(), outlined_method);
      outlined_method->get_code()->build_cfg();
      TRACE(ISO, 5, "[invoke sequence outliner] set the body of %s as \n%s",
            SHOW(outlined_method), SHOW(outlined_method->get_code()));
      m_outlined_method_body_set++;
      // pop up the front pair to avoid duplicate
      c_outlined_methods.pop_front();
      if (c_outlined_methods.empty()) {
        outlined_methods.map.erase(c);
      }
    }
    always_assert(outlined_methods.map.empty());
    outlined_methods.order.clear();
  }
};

////////////////////////////////////////////////////////////////////////////////
// reorder_all_methods
////////////////////////////////////////////////////////////////////////////////
struct MethodProfileUpdate {
  // Name matches offered to MethodProfiles, i.e. (mdt, outlined method) pairs.
  // This is an upper bound on what gets resolved, not a count of resolutions.
  size_t name_matches{0};
  method_profiles::MethodProfiles::ResolutionStats resolution;
};

MethodProfileUpdate update_method_profiles(
    ConfigFiles& config,
    const OutlinedMethodsToReorder& outlined_methods_to_reorder) {
  // Outlined methods have rather unique method names of the form
  //   $outlined$X$YYYYYYYY
  // where X is 0 or 1 indicating whether the method was generated by the first
  // or second outliner run, and YYYYYYYY is a stable hash that is derived from
  // the outlined instruction sequence. While these names should be stable
  // across builds and releases, the dex file and class any particular outlined
  // method ends up in is not stable. To still reliably match outlined methods,
  // we adjust the method profiles here accordingly based on the outlined method
  // names.

  auto& method_profiles = config.get_method_profiles();
  UnorderedMap<std::string_view,
               std::vector<dex_member_refs::MethodDescriptorTokens>>
      unresolved_names;
  auto mdts = method_profiles.get_unresolved_method_descriptor_tokens();
  for (const auto& mdt : UnorderedIterable(mdts)) {
    unresolved_names[mdt.name].push_back(mdt);
  }
  UnorderedMap<dex_member_refs::MethodDescriptorTokens,
               std::vector<DexMethodRef*>>
      map;
  size_t count{0};
  for (const auto& [dex, outlined_methods] : outlined_methods_to_reorder) {
    for (auto&& [outlined_method, methods] :
         UnorderedIterable(outlined_methods)) {
      const auto* name = outlined_method->get_name();
      auto it = unresolved_names.find(name->str());
      if (it == unresolved_names.end()) {
        continue;
      }
      for (auto& mdt : it->second) {
        map[mdt].push_back(outlined_method);
        TRACE(ISO, 5, "[instruction sequence outliner] matched name %s with %s",
              SHOW(name), SHOW(outlined_method));
        count++;
      }
    }
  }
  return MethodProfileUpdate{
      count, method_profiles.resolve_method_descriptor_tokens(map)};
}

std::vector<DexStore*> get_stores(DexStoresVector& stores,
                                  XStoreRefs& xstores) {
  std::vector<DexStore*> res;
  res.reserve(stores.size());
  for (auto& store : stores) {
    res.emplace_back(&store);
  }
  // Order dependencies before dependents.
  //
  // Answering "is s a transitive dependency of t" directly and falling back to
  // name order is not a strict weak ordering: dependency is a partial order,
  // and interleaving it with a total order on the incomparable pairs admits
  // cycles. std::sort on an intransitive comparator is undefined behaviour.
  //
  // Sorting by transitive dependency count preserves the intent. The closure
  // built by build_transitive_resolved_dependencies is transitive and
  // necessarily acyclic, so `s in deps(t)` implies `deps(s)` is a subset of
  // `deps(t)` that does not contain s, hence `|deps(s)| < |deps(t)|`. Name and
  // then original position break the remaining ties, which makes this a total
  // order and leaves nothing for the unstable sort to decide.
  UnorderedMap<const DexStore*, size_t> original_position;
  for (size_t i = 0; i < res.size(); ++i) {
    original_position.emplace(res[i], i);
  }
  std::sort(res.begin(), res.end(), [&](DexStore* s, DexStore* t) {
    auto s_deps = xstores.get_transitive_resolved_dependencies(s).size();
    auto t_deps = xstores.get_transitive_resolved_dependencies(t).size();
    if (s_deps != t_deps) {
      return s_deps < t_deps;
    }
    if (s->get_name() != t->get_name()) {
      return s->get_name() < t->get_name();
    }
    return original_position.at(s) < original_position.at(t);
  });
  // The dependency-count argument above is a proof about the closure, not a
  // check of it. Verify the property it is standing in for: no store precedes
  // one of its own transitive dependencies. Quadratic, but there are a few
  // dozen stores, and it is compiled out in opt builds.
  if (debug) {
    for (size_t i = 0; i < res.size(); ++i) {
      const auto& deps = xstores.get_transitive_resolved_dependencies(res[i]);
      for (size_t j = i + 1; j < res.size(); ++j) {
        assert_log(deps.count(res[j]) == 0u,
                   "store %s was ordered before its dependency %s",
                   res[i]->get_name().c_str(), res[j]->get_name().c_str());
      }
    }
  }
  return res;
}

} // namespace

void InstructionSequenceOutliner::bind_config() {
  auto& pg = m_config.profile_guidance;
  bind("min_insns_size", m_config.min_insns_size, m_config.min_insns_size,
       "Minimum number of instructions to be outlined in a sequence");
  bind("max_insns_size", m_config.max_insns_size, m_config.max_insns_size,
       "Maximum number of instructions to be outlined in a sequence");
  bind("cost_method_metadata", m_config.cost_method_metadata,
       m_config.cost_method_metadata,
       "Average cost of having an outlined method reference (method_id_item, "
       "proto_id, type_list, string) in code units");
  bind("cost_method_body", m_config.cost_method_body, m_config.cost_method_body,
       "Average cost of having an outlined method body (encoded_method, "
       "code_item) in code units");
  bind("cost_invoke_with_result", m_config.cost_invoke_with_result,
       m_config.cost_invoke_with_result,
       "Overhead of calling an outlined method with a result (invoke + "
       "move-result).");
  bind("cost_invoke_without_result", m_config.cost_invoke_without_result,
       m_config.cost_invoke_without_result,
       "Overhead of calling an outlined method without a result.");
  bind("max_args", m_config.max_args, m_config.max_args,
       "Maximum number of arguments in outlined methods to avoid /range "
       "instructions");
  bind("use_method_profiles", pg.use_method_profiles, pg.use_method_profiles,
       "Whether to use provided method-profiles configuration data to "
       "determine if certain code should not be outlined from a method");
  bind("enable_hotness_propagation", pg.enable_hotness_propagation,
       pg.enable_hotness_propagation,
       "Whether to propagate method hotness (and warmness) to cold callees "
       "if the call site blocks were executed.");
  bind("method_profiles_appear_percent",
       pg.method_profiles_appear_percent,
       pg.method_profiles_appear_percent,
       "Cut off when a method in a method profile is deemed relevant");
  bind("throughput_interaction_name_pattern",
       pg.throughput_interaction_name_pattern,
       pg.throughput_interaction_name_pattern,
       "Regular expression identifying throughput interaction names");
  bind("method_profiles_throughput_hot_call_count",
       pg.method_profiles_throughput_hot_call_count,
       pg.method_profiles_throughput_hot_call_count,
       "No code is outlined out of methods in throughput interactions");
  bind("method_profiles_hot_call_count",
       pg.method_profiles_hot_call_count,
       pg.method_profiles_hot_call_count,
       "No code is outlined out of hot methods");
  bind("method_profiles_warm_call_count",
       pg.method_profiles_warm_call_count,
       pg.method_profiles_warm_call_count,
       "Loops are not outlined from warm methods");
  std::string perf_sensitivity_str;
  bind("perf_sensitivity", "always-hot", perf_sensitivity_str);
  bind("block_profiles_hits",
       pg.block_profiles_hits,
       pg.block_profiles_hits,
       "No code is outlined out of hot blocks in hot methods");
  bind("reuse_outlined_methods_across_dexes",
       m_config.reuse_outlined_methods_across_dexes,
       m_config.reuse_outlined_methods_across_dexes,
       "Whether to allow reusing outlined methods across dexes within the same "
       "store");
  bind("derive_method_profiles_stats",
       m_config.derive_method_profiles_stats,
       m_config.derive_method_profiles_stats,
       "Whether to derive method profile stats for generated outline methods "
       "from methods outlined from");
  bind("max_outlined_methods_per_class",
       m_config.max_outlined_methods_per_class,
       m_config.max_outlined_methods_per_class,
       "Maximum number of outlined methods per generated helper class; "
       "indirectly drives number of needed helper classes");
  bind("savings_threshold", m_config.savings_threshold,
       m_config.savings_threshold,
       "Minimum number of code units saved before a particular code sequence "
       "is outlined anywhere");
  bind("outline_from_primary_dex", m_config.outline_from_primary_dex,
       m_config.outline_from_primary_dex,
       "Whether to outline from primary dex");
  bind("full_dbg_positions", m_config.full_dbg_positions,
       m_config.full_dbg_positions,
       "Whether to encode all possible outlined positions");
  bind("debug_make_crashing", m_config.debug_make_crashing,
       m_config.debug_make_crashing,
       "Make outlined code crash, to harvest crashing stack traces involving "
       "outlined code.");
  bind("obfuscate_method_names", m_config.obfuscate_method_names,
       m_config.obfuscate_method_names,
       "Whether to obfuscate generated method names for outlined methods, "
       "instead of encoding a strong hash of their contents. Obfuscated names "
       "tend to be shorter, but are less stable across builds.");
  bind("outline_blocklist_prefixes", m_config.outline_blocklist_prefixes,
       m_config.outline_blocklist_prefixes,
       "Prefixes of class name that we turn off outlining for");
  after_configuration(
      [this, perf_sensitivity_str = std::move(perf_sensitivity_str)]() {
        always_assert(m_config.min_insns_size >= MIN_INSNS_SIZE);
        always_assert(m_config.max_insns_size >= m_config.min_insns_size);
        always_assert(m_config.max_outlined_methods_per_class > 0);
        always_assert(!perf_sensitivity_str.empty());
        m_config.profile_guidance.perf_sensitivity =
            parse_perf_sensitivity(perf_sensitivity_str);
      });
}

void InstructionSequenceOutliner::run_pass(DexStoresVector& stores,
                                           ConfigFiles& config,
                                           PassManager& mgr) {
  int32_t min_sdk = mgr.get_redex_options().min_sdk;
  mgr.incr_metric("min_sdk", min_sdk);
  TRACE(ISO, 2, "[invoke sequence outliner] min_sdk: %d", min_sdk);
  auto min_sdk_api_file = config.get_android_sdk_api_file(min_sdk);
  const api::AndroidSDK* min_sdk_api{nullptr};
  if (!min_sdk_api_file) {
    mgr.incr_metric("min_sdk_no_file", 1);
    TRACE(ISO, 2,
          "[invoke sequence outliner] Android SDK API %d file cannot be found.",
          min_sdk);
  } else {
    min_sdk_api = &config.get_android_sdk_api(min_sdk);
  }

  if (g_redex->instrument_mode) {
    m_config.outline_control_flow = false;
  }

  auto scope = build_class_scope(stores);
  // At the start of pass running, we mark all methods within blocklisted
  // classes as no_outlining.
  if (!m_config.outline_blocklist_prefixes.empty()) {
    walk::parallel::classes(scope, [&](DexClass* cls) {
      if (unordered_find_if(m_config.outline_blocklist_prefixes,
                            [cls](const std::string& prefix) {
                              return cls->get_name()->str().starts_with(prefix);
                            }) != m_config.outline_blocklist_prefixes.end()) {
        for (auto* m : cls->get_all_methods()) {
          m->rstate.set_no_outlining();
        }
      }
    });
  }

  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, config.create_init_class_insns());

  UnorderedSet<size_t> throughput_interaction_indices;
  UnorderedSet<std::string> throughput_interaction_ids;
  get_throughput_interactions(config, m_config.profile_guidance,
                              &throughput_interaction_indices,
                              &throughput_interaction_ids);
  mgr.incr_metric("num_throughput_interactions",
                  throughput_interaction_ids.size());

  UnorderedSet<DexMethod*> throughput_methods;
  UnorderedSet<DexMethod*> sufficiently_warm_methods;
  UnorderedSet<DexMethod*> sufficiently_hot_methods;
  gather_sufficiently_warm_and_hot_methods(
      scope, config, mgr, m_config.profile_guidance, throughput_interaction_ids,
      &throughput_methods, &sufficiently_warm_methods,
      &sufficiently_hot_methods);
  mgr.incr_metric("num_throughput_methods", throughput_methods.size());
  mgr.incr_metric("num_sufficiently_warm_methods",
                  sufficiently_warm_methods.size());
  mgr.incr_metric("num_sufficiently_hot_methods",
                  sufficiently_hot_methods.size());
  const OutlineabilityContext outlineability(
      m_config.profile_guidance, throughput_interaction_indices,
      throughput_methods, sufficiently_warm_methods, sufficiently_hot_methods);
  auto methods_global_order = get_methods_global_order(config, m_config);
  mgr.incr_metric("num_ordered_methods", methods_global_order.size());
  XStoreRefs xstores(stores, config.normal_primary_dex());
  size_t dex_id{0};
  const auto& interdex_metrics = mgr.get_interdex_metrics();
  auto it = interdex_metrics.find(interdex::METRIC_RESERVED_MREFS);
  size_t reserved_mrefs = it == interdex_metrics.end() ? 0 : it->second;
  it = interdex_metrics.find(interdex::METRIC_RESERVED_TREFS);
  size_t reserved_trefs = it == interdex_metrics.end() ? 0 : it->second;
  TRACE(
      ISO, 2,
      "[invoke sequence outliner] found %zu reserved trefs, %zu reserved mrefs",
      reserved_trefs, reserved_mrefs);
  ReusableOutlinedMethods outlined_methods;
  OutlinedMethodBodySetter outlined_method_body_setter(m_config, mgr);
  // keep track of the outlined methods and scope for reordering later
  OutlinedMethodsToReorder outlined_methods_to_reorder;
  size_t num_reused_methods{0};
  auto iteration = m_iteration++;
  bool is_primary_dex{true};
  for (auto* store : get_stores(stores, xstores)) {
    auto store_dependencies =
        xstores.get_transitive_resolved_dependencies(store);
    for (auto& dex : store->get_dexen()) {
      if (is_primary_dex) {
        is_primary_dex = false;
        if (!m_config.outline_from_primary_dex) {
          // Don't touch the primary dex
          continue;
        }
      }
      if (dex.empty()) {
        continue;
      }
      auto store_idx = xstores.get_store_idx(dex.front()->get_type());
      always_assert(std::find_if(dex.begin(), dex.end(),
                                 [&xstores, store_idx](DexClass* cls) {
                                   return xstores.get_store_idx(
                                              cls->get_type()) != store_idx;
                                 }) == dex.end());
      RefChecker ref_checker{&xstores, store_idx, min_sdk_api};
      CandidateInstructionCoresSet recurring_cores;
      get_recurring_cores(m_config, mgr, dex, outlineability, ref_checker,
                          &recurring_cores);
      std::vector<CandidateWithInfo> candidates_with_infos;
      UnorderedMap<DexMethod*, UnorderedSet<CandidateId>>
          candidate_ids_by_methods;
      get_beneficial_candidates(m_config, mgr, store, store_dependencies, dex,
                                ref_checker, recurring_cores, outlineability,
                                &outlined_methods, &candidates_with_infos,
                                &candidate_ids_by_methods);

      // TODO: Merge candidates that are equivalent except that one returns
      // something and the other doesn't. Affects around 1.5% of candidates.
      DexState dex_state(mgr, init_classes_with_side_effects, dex, dex_id++,
                         reserved_trefs, reserved_mrefs);
      auto newly_outlined_methods =
          outline(m_config, mgr, store, store_dependencies, dex_state, min_sdk,
                  &candidates_with_infos, &candidate_ids_by_methods,
                  &outlined_methods, iteration, &num_reused_methods);
      outlined_methods_to_reorder.emplace_back(&dex, newly_outlined_methods);
      auto affected_methods = count_affected_methods(newly_outlined_methods);
      auto total_methods = count_methods(dex);
      if (total_methods > 0) {
        mgr.incr_metric(std::string("percent_methods_affected_in_Dex") +
                            std::to_string(dex_id) + "_" + store->get_name(),
                        affected_methods * 100 / total_methods);
      }
    }
  }

  // set body of the methods after all
  // patterns are discovered then reorder
  outlined_method_body_setter.set_method_body(outlined_methods);
  reorder_all_methods(m_config, mgr, methods_global_order,
                      outlined_methods_to_reorder);
  if (m_config.derive_method_profiles_stats) {
    size_t derived_method_profile_stats =
        derive_method_profiles_stats(config, outlined_methods_to_reorder);
    mgr.incr_metric("num_derived_method_profile_stats",
                    derived_method_profile_stats);
  }
  auto method_profile_update =
      update_method_profiles(config, outlined_methods_to_reorder);
  // Kept under its historical name for continuity with existing redex-stats
  // comparisons, even though it counts name matches rather than resolutions.
  mgr.incr_metric("num_resolved_method_profiles",
                  method_profile_update.name_matches);
  const auto& resolution = method_profile_update.resolution;
  mgr.incr_metric("num_method_profile_lines_resolved",
                  resolution.lines_resolved);
  mgr.incr_metric("num_method_profile_rows_added", resolution.rows_added);
  mgr.incr_metric("num_baseline_method_profile_lines_resolved",
                  resolution.baseline_lines_resolved);
  mgr.incr_metric("num_baseline_method_profile_rows_added",
                  resolution.baseline_rows_added);
  mgr.incr_metric("num_reused_methods", num_reused_methods);

  // Position interning. These are cumulative manager state rather than
  // per-iteration counts, so set rather than incr. The gap between them is
  // what the interning saves; when it was broken they were equal.
  auto* position_manager = g_redex->get_position_pattern_switch_manager();
  mgr.set_metric("num_internalize_calls",
                 position_manager->get_num_internalize_calls());
  mgr.set_metric("num_interned_positions",
                 position_manager->get_num_interned_positions());
}

static InstructionSequenceOutliner s_pass;
