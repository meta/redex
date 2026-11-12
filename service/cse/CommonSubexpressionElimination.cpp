/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

/*
 * This optimizer pass eliminates common subexpression.
 *
 * It's implemented via a global-value-numbering scheme.
 * While doing abstract interpretation on a method's code, we evolve...
 * 1) a mapping of registers to "values"
 * 2) a mapping of "values" to first-defining instructions
 *
 * A "value" is similar to an instruction, in that it has an IROpcode,
 * a list of srcs dependencies, and type/field/string/... payload data as
 * necessary; however it's different in that it doesn't have an identity, and
 * srcs dependencies are expressed in terms of other values, not registers.
 *
 * If the same value has multiple (equivalent) defining instructions after the
 * analysis reaches its fixed point, then the optimization...
 * - inserts a move of the result to a temporary register after the
 *   defining instruction, and it
 * - inserts another move from the temporary register to the result register
 *   of later (equivalent) defining instruction, after the defining instruction
 *
 * The moves are usually eliminated by copy-propagation, and the now redundant
 * later defining instructions are removed by local dce --- both of which get to
 * run on a method's code immediately if cse did a mutation.
 *
 * Notes:
 * - Memory read instructions are captured as well, and, in effect, may be
 *   reordered --- basically, later redundant reads may be replaced by results
 *   of earlier reads.
 *   Of course, true memory barriers are modeled (method invocations, volatile
 *   field accesses, monitor instructions), and to be conservative, all other
 *   writes to the heap (fields, array elements) are also treated as a memory
 *   barrier. This certainly ensures that thread-local behaviors is unaffected.
 * - There is no proper notion of phi-nodes at this time. Instead, conflicting
 *   information in the register-to-values and values'-first-definitions envs
 *   simply merge to top. Similarly, (memory) barriers are realized by setting
 *   all barrier-sensitive (heap-dependent) mapping entries to top. When later
 *   an instruction is interpreted that depends on a source register where the
 *   register-to-value binding is top, then a special value is created for that
 *   register (a "pre-state-source" value that refers to the value of a source
 *   register as it was *before* the instruction). This recovers the tracking
 *   of merged or havoced registers, in a way that's similar to phi-nodes, but
 *   lazy.
 */

#include "CommonSubexpressionElimination.h"

#include <cinttypes>
#include <optional>
#include <utility>

#include <sparta/ConstantAbstractDomain.h>
#include <sparta/PatriciaTreeMapAbstractEnvironment.h>
#include <sparta/PatriciaTreeSetAbstractDomain.h>
#include <sparta/ReducedProductAbstractDomain.h>

#include "BaseIRAnalyzer.h"
#include "CFGMutation.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "FieldOpTracker.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "ReachableClasses.h"
#include "Resolver.h"
#include "Show.h"
#include "Trace.h"
#include "TypeInference.h"

using namespace sparta;
using namespace cse_impl;

namespace {

using value_id_t = uint64_t;
constexpr size_t TRACKED_LOCATION_BITS = 42; // leaves 20 bits for running index
enum ValueIdFlags : value_id_t {
  // lower bits for tracked locations
  UNTRACKED = 0,
  IS_FIRST_TRACKED_LOCATION = ((value_id_t)1),
  IS_OTHER_TRACKED_LOCATION = ((value_id_t)1) << TRACKED_LOCATION_BITS,
  IS_ONLY_READ_NOT_WRITTEN_LOCATION = ((value_id_t)1)
                                      << (TRACKED_LOCATION_BITS + 1),
  IS_TRACKED_LOCATION_MASK = IS_ONLY_READ_NOT_WRITTEN_LOCATION * 2 - 1,
  // upper bits for unique running index
  BASE = ((value_id_t)1) << (TRACKED_LOCATION_BITS + 2),
};

using namespace ir_analyzer;

// Marker opcode for values representing a source of an instruction; this is
// used to recover from merged / havoced values.
const IROpcode IOPCODE_PRE_STATE_SRC = IROpcode(0xFFFF);

// Marker opcode for positional values that must not be moved.
const IROpcode IOPCODE_POSITIONAL = IROpcode(0xFFFE);

// This is only used for an INVOKE-VIRTUAL insn. Marker opocode for a potential
// unboxing value.
const IROpcode IOPCODE_POSITIONAL_UNBOXING = IROpcode(0xFFFD);

struct IRValue {
  IROpcode opcode;
  std::vector<value_id_t> srcs;
  union {
    // Zero-initialize this union with the uint64_t member instead of a
    // pointer-type member so that it works properly even on 32-bit machines
    uint64_t literal{0};
    const DexString* string;
    const DexType* type;
    const DexFieldRef* field;
    const DexMethodRef* method;
    const DexOpcodeData* data;

    // By setting positional_insn to the pointer of an instruction, it
    // effectively makes the "value" unique (as unique as the instruction),
    // avoiding identifying otherwise structurally equivalent operations, e.g.
    // two move-exception instructions that really must remain at their existing
    // position, and cannot be replaced.
    const IRInstruction* positional_insn;
  };
};

struct IRValueHasher {
  size_t operator()(const IRValue& tv) const {
    size_t hash = tv.opcode;
    for (auto src : tv.srcs) {
      hash = hash * 27 + src;
    }
    hash = hash * 27 + (size_t)tv.literal;
    return hash;
  }
};

bool operator==(const IRValue& a, const IRValue& b) {
  return a.opcode == b.opcode && a.srcs == b.srcs && a.literal == b.literal;
}

using IRInstructionsDomain =
    sparta::PatriciaTreeSetAbstractDomain<const IRInstruction*>;
using ValueIdDomain = sparta::ConstantAbstractDomain<value_id_t>;
using DefEnvironment =
    sparta::PatriciaTreeMapAbstractEnvironment<value_id_t,
                                               IRInstructionsDomain>;
using RefEnvironment =
    sparta::PatriciaTreeMapAbstractEnvironment<reg_t, ValueIdDomain>;
class CondEnvironment final
    : public sparta::AbstractDomainReverseAdaptor<
          sparta::PatriciaTreeSetAbstractDomain<value_id_t>,
          CondEnvironment> {
 public:
  using AbstractDomainReverseAdaptor::AbstractDomainReverseAdaptor;
};

class CseEnvironment final
    : public sparta::ReducedProductAbstractDomain<CseEnvironment,
                                                  DefEnvironment,
                                                  RefEnvironment,
                                                  CondEnvironment> {
 public:
  using ReducedProductAbstractDomain::ReducedProductAbstractDomain;
  CseEnvironment()
      : ReducedProductAbstractDomain(std::make_tuple(
            DefEnvironment(),
            RefEnvironment(),
            CondEnvironment(sparta::PatriciaTreeSet<value_id_t>()))) {}

  static void reduce_product(
      std::tuple<DefEnvironment, RefEnvironment, CondEnvironment>&) {}

  const DefEnvironment& get_def_env() const {
    return ReducedProductAbstractDomain::get<0>();
  }

  const RefEnvironment& get_ref_env() const {
    return ReducedProductAbstractDomain::get<1>();
  }

  const CondEnvironment& get_cond_env() const {
    return ReducedProductAbstractDomain::get<2>();
  }

  CseEnvironment& mutate_def_env(
      const std::function<void(DefEnvironment*)>& f) {
    apply<0>(f);
    return *this;
  }

  CseEnvironment& mutate_ref_env(
      const std::function<void(RefEnvironment*)>& f) {
    apply<1>(f);
    return *this;
  }

  CseEnvironment& mutate_cond_env(
      const std::function<void(CondEnvironment*)>& f) {
    apply<2>(f);
    return *this;
  }

  bool has_cond(value_id_t cond) const {
    return get_cond_env().unwrap().contains(cond);
  }

  CseEnvironment& add_cond(value_id_t cond, value_id_t neg_cond) {
    if (has_cond(neg_cond)) {
      set_to_bottom();
      return *this;
    }
    return mutate_cond_env(
        [cond](CondEnvironment* env) { env->unwrap().add(cond); });
  }
};

static Barrier make_barrier(const IRInstruction* insn) {
  Barrier b;
  b.opcode = insn->opcode();
  if (insn->has_field()) {
    b.field =
        resolve_field(insn->get_field(), opcode::is_an_sfield_op(insn->opcode())
                                             ? FieldSearch::Static
                                             : FieldSearch::Instance);
  } else if (insn->has_method()) {
    b.method =
        resolve_method_deprecated(insn->get_method(), opcode_to_search(insn));
  }
  return b;
}

CseLocation get_written_array_location(IROpcode opcode) {
  switch (opcode) {
  case OPCODE_APUT:
    return CseLocation(CseSpecialLocations::ARRAY_COMPONENT_TYPE_INT);
  case OPCODE_APUT_BYTE:
    return CseLocation(CseSpecialLocations::ARRAY_COMPONENT_TYPE_BYTE);
  case OPCODE_APUT_CHAR:
    return CseLocation(CseSpecialLocations::ARRAY_COMPONENT_TYPE_CHAR);
  case OPCODE_APUT_WIDE:
    return CseLocation(CseSpecialLocations::ARRAY_COMPONENT_TYPE_WIDE);
  case OPCODE_APUT_SHORT:
    return CseLocation(CseSpecialLocations::ARRAY_COMPONENT_TYPE_SHORT);
  case OPCODE_APUT_OBJECT:
    return CseLocation(CseSpecialLocations::ARRAY_COMPONENT_TYPE_OBJECT);
  case OPCODE_APUT_BOOLEAN:
    return CseLocation(CseSpecialLocations::ARRAY_COMPONENT_TYPE_BOOLEAN);
  default:
    always_assert(false);
  }
}

CseLocation get_written_location(const Barrier& barrier) {
  if (opcode::is_an_aput(barrier.opcode)) {
    return get_written_array_location(barrier.opcode);
  } else if (opcode::is_an_iput(barrier.opcode) ||
             opcode::is_an_sput(barrier.opcode)) {
    return get_field_location(barrier.opcode, barrier.field);
  } else {
    return CseLocation(CseSpecialLocations::GENERAL_MEMORY_BARRIER);
  }
}

bool is_barrier_relevant(const Barrier& barrier,
                         const CseUnorderedLocationSet& read_locations) {
  auto location = get_written_location(barrier);
  return location == CseLocation(CseSpecialLocations::GENERAL_MEMORY_BARRIER) ||
         (read_locations.count(location) != 0u);
}

const CseUnorderedLocationSet no_locations = CseUnorderedLocationSet();

const CseUnorderedLocationSet general_memory_barrier_locations =
    CseUnorderedLocationSet{
        CseLocation(CseSpecialLocations::GENERAL_MEMORY_BARRIER)};

class Analyzer final : public BaseEdgeAwareIRAnalyzer<CseEnvironment> {
 public:
  Analyzer(SharedState* shared_state,
           cfg::ControlFlowGraph& cfg,
           bool is_method_static,
           bool is_method_init_or_clinit,
           DexType* declaring_type)
      : BaseEdgeAwareIRAnalyzer(cfg), m_shared_state(shared_state) {
    // Collect all read locations
    UnorderedMap<CseLocation, size_t, CseLocationHasher> read_location_counts;
    for (const auto& mie : cfg::InstructionIterable(cfg)) {
      auto* insn = mie.insn;
      auto location = get_read_location(insn);
      if (location !=
          CseLocation(CseSpecialLocations::GENERAL_MEMORY_BARRIER)) {
        read_location_counts[location]++;
      } else if (opcode::is_an_invoke(insn->opcode()) &&
                 shared_state->has_pure_method(insn)) {
        for (auto l : UnorderedIterable(
                 shared_state->get_read_locations_of_conditionally_pure_method(
                     insn->get_method(), insn->opcode()))) {
          read_location_counts[l]++;
        }
      }
    }

    // Prune those which are final fields that cannot get mutated in our context
    unordered_erase_if(read_location_counts, [&](auto& p) {
      auto location = p.first;
      // If we are reading a final field...
      if (location.has_field() &&
          shared_state->is_finalish(location.get_field()) &&
          !root(location.get_field()) && can_rename(location.get_field()) &&
          can_delete(location.get_field()) &&
          !location.get_field()->is_external()) {
        // ... and we are not analyzing a method that is a corresponding
        // constructor or static initializer of the declaring type of the
        // field ...
        if (!is_method_init_or_clinit ||
            location.get_field()->get_class() != declaring_type ||
            is_static(location.get_field()) != is_method_static) {
          // ... then we don't need track the field as a memory location
          // (that in turn might get invalidated on general memory barriers).
          m_tracked_locations.emplace(location, ValueIdFlags::UNTRACKED);
          return true;
        }
      }
      m_read_locations.insert(location);
      return false;
    });

    // Collect all relevant written locations
    UnorderedMap<CseLocation, size_t, CseLocationHasher>
        written_location_counts;
    for (const auto& mie : cfg::InstructionIterable(cfg)) {
      auto locations = shared_state->get_relevant_written_locations(
          mie.insn, nullptr /* exact_virtual_scope */, m_read_locations);
      if (locations.count(
              CseLocation(CseSpecialLocations::GENERAL_MEMORY_BARRIER)) == 0u) {
        for (const auto& location : UnorderedIterable(locations)) {
          written_location_counts[location]++;
        }
      }
    }

    // Check which locations get written and read (vs. just written)
    std::vector<CseLocation> read_and_written_locations;
    for (const auto& p : UnorderedIterable(written_location_counts)) {
      always_assert(p.first !=
                    CseLocation(CseSpecialLocations::GENERAL_MEMORY_BARRIER));
      if (read_location_counts.count(p.first) != 0u) {
        read_and_written_locations.push_back(p.first);
      } else {
        always_assert(!m_tracked_locations.count(p.first));
        m_tracked_locations.emplace(p.first, ValueIdFlags::UNTRACKED);
      }
    }

    // Also keep track of locations that get read but not written
    for (const auto& p : UnorderedIterable(read_location_counts)) {
      if (written_location_counts.count(p.first) == 0u) {
        always_assert(!m_tracked_locations.count(p.first));
        m_tracked_locations.emplace(
            p.first, ValueIdFlags::IS_ONLY_READ_NOT_WRITTEN_LOCATION);
      }
    }
    // We'll use roughly half of the bits in a value_id to encode what kind of
    // heap locations were involved in producing the value, so that we can
    // later quickly identify which values need to be invalidated when
    // encountering a write to a specific location. However, we only have a
    // limited number of bits available, and potentially many more relevant
    // locations.
    //
    // We'll identify the long tail of locations that are read and written via a
    // separate bit (IS_OTHER_TRACKED_LOCATION), and we'll also reserve one bit
    // for locations that are read but not written
    // (IS_ONLY_READ_NOT_WRITTEN_LOCATION), so that we can identify these
    // heap-dependent locations when we need to validate all heap-dependent
    // locations in case of a general memory barrier.
    //
    // We use a heuristic to decide which locations get their own bit, vs
    // the long-tail treatment.
    //
    // The currently implemented heuristic prefers locations that are often
    // read and rarely written.
    //
    // TODO: Explore other (variations of this) heuristics.

    std::sort(read_and_written_locations.begin(),
              read_and_written_locations.end(),
              [&](CseLocation a, CseLocation b) {
                auto get_weight = [&](CseLocation l) {
                  auto reads = read_location_counts.at(l);
                  auto writes = written_location_counts.at(l);
                  return (reads << 16) / writes;
                };
                auto weight_a = get_weight(a);
                auto weight_b = get_weight(b);
                if (weight_a != weight_b) {
                  // higher weight takes precedence
                  return weight_a > weight_b;
                }
                // in case of a tie, still ensure a deterministic total ordering
                return a < b;
              });
    TRACE(CSE, 4, "[CSE] relevant locations: %zu %s",
          read_and_written_locations.size(),
          read_and_written_locations.size() > 13 ? "(HUGE!)" : "");
    value_id_t next_bit = ValueIdFlags::IS_FIRST_TRACKED_LOCATION;
    for (auto l : read_and_written_locations) {
      TRACE(CSE, 4, "[CSE]   %s: %zu reads, %zu writes",
            l.special_location < CseSpecialLocations::END ? "array element"
                                                          : SHOW(l.field),
            read_location_counts.at(l), written_location_counts.at(l));
      m_tracked_locations.emplace(l, next_bit);
      if (next_bit == ValueIdFlags::IS_OTHER_TRACKED_LOCATION) {
        m_using_other_tracked_location_bit = true;
      } else {
        // we've already reached the last catch-all tracked read/write location
        next_bit <<= 1;
      }
    }

    run({});
  }

  void analyze_instruction_normal(
      const IRInstruction* insn, CseEnvironment* current_state) const override {
    if (current_state->is_bottom()) {
      return;
    }

    const auto set_current_state_at = [&](reg_t reg, bool wide,
                                          ValueIdDomain value) {
      current_state->mutate_ref_env([&](RefEnvironment* env) {
        env->set(reg, value);
        if (wide) {
          env->set(reg + 1, ValueIdDomain::top());
        }
      });
    };

    init_pre_state(insn, current_state);
    auto clobbered_locations = get_clobbered_locations(insn, current_state);
    auto opcode = insn->opcode();
    switch (opcode) {
    case OPCODE_MOVE:
    case OPCODE_MOVE_OBJECT:
    case OPCODE_MOVE_WIDE: {
      auto domain = current_state->get_ref_env().get(insn->src(0));
      set_current_state_at(insn->dest(), insn->dest_is_wide(), domain);
      break;
    }
    default: {
      // If we get here, reset destination.
      if (insn->has_dest()) {
        ValueIdDomain domain;
        if (opcode::is_move_result_any(opcode)) {
          domain = current_state->get_ref_env().get(RESULT_REGISTER);
        } else {
          domain =
              get_value_id_domain(insn, current_state, clobbered_locations);
        }
        auto c = domain.get_constant();
        if (c) {
          auto value_id = *c;
          if (current_state->get_def_env().get(value_id).is_top()) {
            current_state->mutate_def_env([&](DefEnvironment* env) {
              env->set(value_id, IRInstructionsDomain(insn));
            });
          }
        }
        set_current_state_at(insn->dest(), insn->dest_is_wide(), domain);
      } else if (insn->has_move_result_any()) {
        ValueIdDomain domain =
            get_value_id_domain(insn, current_state, clobbered_locations);
        current_state->mutate_ref_env(
            [&](RefEnvironment* env) { env->set(RESULT_REGISTER, domain); });
      }
      break;
    }
    }

    if (!clobbered_locations.empty()) {
      value_id_t mask = (value_id_t)0;
      for (const auto& l : UnorderedIterable(clobbered_locations)) {
        mask |= get_location_value_id_mask(l);
      }

      // TODO: The following loops are probably the most expensive thing in this
      // algorithm; is there a better way of doing this? (Then again, overall,
      // the time this algorithm takes seems reasonable.)

      bool any_changes = false;
      current_state->mutate_def_env([mask, &any_changes](DefEnvironment* env) {
        if (env->erase_all_matching(mask)) {
          any_changes = true;
        }
      });
      current_state->mutate_cond_env([mask](CondEnvironment* env) {
        env->unwrap().erase_all_matching(mask);
      });
      current_state->mutate_ref_env([mask, &any_changes](RefEnvironment* env) {
        bool any_map_changes = env->transform([mask](ValueIdDomain domain) {
          auto c = domain.get_constant();
          always_assert(c);
          auto value_id = *c;
          if ((value_id & mask) != 0u) {
            return ValueIdDomain::top();
          }
          return domain;
        });
        if (any_map_changes) {
          any_changes = true;
        }
      });
      if (any_changes) {
        m_shared_state->log_barrier(make_barrier(insn));
      }
    }
  }

  void add_cond(const IRValue& value, CseEnvironment* env) const {
    if (value.opcode == OPCODE_IF_NE) {
      always_assert(value.srcs.size() == 2);
      if (value.srcs[0] == value.srcs[1]) {
        env->set_to_bottom();
        return;
      }
    }
    auto value_id = *get_value_id(value);

    auto neg_value = value;
    neg_value.opcode = opcode::invert_conditional_branch(value.opcode);
    auto neg_value_id = *get_value_id(neg_value);

    env->add_cond(value_id, neg_value_id);
  }

  void analyze_if(const IRInstruction* insn,
                  const EdgeId& edge,
                  CseEnvironment* env) const override {
    if (env->is_bottom()) {
      return;
    }

    auto value = get_value(insn, env, {});
    if (edge->type() == cfg::EDGE_GOTO) {
      value.opcode = opcode::invert_conditional_branch(value.opcode);
    }
    add_cond(value, env);
  }

  void analyze_switch(const IRInstruction* insn,
                      const EdgeId& edge,
                      CseEnvironment* env) const override {
    if (env->is_bottom()) {
      return;
    }

    const auto& ref_env = env->get_ref_env();
    auto selector_reg = insn->src(0);
    auto c = ref_env.get(selector_reg).get_constant();
    if (!c) {
      return;
    }
    value_id_t selector_value_id = *c;

    const auto& case_key = edge->case_key();
    if (!case_key) {
      always_assert(edge->type() == cfg::EDGE_GOTO);
      return;
    }

    always_assert(edge->type() == cfg::EDGE_BRANCH);
    IRValue const_value;
    const_value.opcode = OPCODE_CONST;
    const_value.literal = *case_key;
    auto const_value_id = *get_value_id(const_value);

    IRValue if_value;
    if_value.opcode = OPCODE_IF_EQ;
    if_value.srcs = {selector_value_id, const_value_id};
    add_cond(if_value, env);
  }

  void analyze_no_throw(const IRInstruction* insn,
                        CseEnvironment* current_state) const override {
    if (current_state->is_bottom()) {
      return;
    }

    auto opcode = insn->opcode();
    if (opcode == OPCODE_NEW_ARRAY) {
      const auto& domain = current_state->get_ref_env().get(RESULT_REGISTER);
      if (domain.get_constant()) {
        auto value = get_array_length_value(*domain.get_constant());
        TRACE(CSE, 4, "[CSE] installing array-length forwarding for %s",
              SHOW(insn));
        install_forwarding(insn, value, current_state);
      }
      return;
    }
    auto value = get_equivalent_put_value(insn, current_state);
    if (value) {
      auto barrier = make_barrier(insn);
      if (is_barrier_relevant(barrier, m_read_locations) &&
          get_written_location(barrier) !=
              CseLocation(CseSpecialLocations::GENERAL_MEMORY_BARRIER)) {
        TRACE(CSE, 4, "[CSE] installing store-to-load forwarding for %s",
              SHOW(insn));
        install_forwarding(insn, *value, current_state);
      }
    }
  }

  void install_forwarding(const IRInstruction* insn,
                          const IRValue& value,
                          CseEnvironment* current_state) const {
    auto value_id = *get_value_id(value);
    current_state->mutate_def_env([value_id, insn](DefEnvironment* env) {
      env->set(value_id, IRInstructionsDomain(insn));
    });
  }

  bool is_pre_state_src(value_id_t value_id) const {
    return !(m_pre_state_value_ids.count(value_id) == 0u);
  }

  size_t get_value_ids_size() { return m_value_ids.size(); }

  bool using_other_tracked_location_bit() {
    return m_using_other_tracked_location_bit;
  }

  // Only meaningful once collection has been enabled; see
  // start_collecting_unboxing_insns.
  const std::vector<IRInstruction*>& get_unboxing_insns() {
    always_assert(m_unboxing_collection);
    return m_unboxing_collection->insns;
  }

  // get_value_id records unboxing candidates as a side effect, and it runs on
  // the intermediate (not yet converged) states of the fixpoint as well as on
  // the converged ones. An intermediate state can be more precise than the
  // fixed point - a loop head is at its most precise before the back edge is
  // joined in - so a match seen there may not hold at convergence, and acting
  // on it emits a check-cast for a type the value need not have.
  //
  // Collection is therefore off while the fixpoint runs, and is enabled for
  // the replay over the converged states.
  void start_collecting_unboxing_insns() { m_unboxing_collection.emplace(); }

 private:
  // After analysis, the insns in this list should be refined to call its
  // unboxing implementor.
  // `seen` dedups: the same instruction can be recorded more than once in a
  // single pass, and applying a refinement twice trips the always_assert in
  // the patch loop, because the first application rewrites the method ref that
  // the second one looks up.
  struct UnboxingCollection {
    std::vector<IRInstruction*> insns;
    UnorderedSet<IRInstruction*> seen;
  };
  mutable std::optional<UnboxingCollection> m_unboxing_collection;

  CseUnorderedLocationSet get_clobbered_locations(
      const IRInstruction* insn, const CseEnvironment* current_state) const {
    const DexType* exact_virtual_scope = nullptr;
    if (insn->opcode() == OPCODE_INVOKE_VIRTUAL) {
      auto src0 = current_state->get_ref_env().get(insn->src(0)).get_constant();
      if (src0) {
        exact_virtual_scope = get_exact_type(*src0);
      }
    }
    return m_shared_state->get_relevant_written_locations(
        insn, exact_virtual_scope, m_read_locations);
  }

  ValueIdDomain get_value_id_domain(
      const IRInstruction* insn,
      const CseEnvironment* current_state,
      const CseUnorderedLocationSet& clobbered_locations) const {
    auto value = get_value(insn, current_state, clobbered_locations);
    auto value_id = get_value_id(value);
    return value_id ? ValueIdDomain(*value_id) : ValueIdDomain::top();
  }

  value_id_t get_pre_state_src_value_id(reg_t reg,
                                        const IRInstruction* insn) const {
    auto value = get_pre_state_src_value(reg, insn);
    auto value_id = get_value_id(value);
    always_assert(value_id);
    return *value_id;
  }

  std::optional<value_id_t> unwrap_value(const IRValue& value,
                                         const DexMethodRef* unwrap_method,
                                         const DexMethodRef* wrap_method,
                                         const DexMethodRef* abs_method,
                                         bool is_unboxed) const {
    if (is_unboxed) {
      // for unboxing in boxing-unboxing pattern, the value could be an invoke
      // or IOPCODE_POSITIONAL_UNBOXING.
      if (!opcode::is_an_invoke(value.opcode) &&
          value.opcode != IOPCODE_POSITIONAL_UNBOXING) {
        return std::nullopt;
      }
    } else {
      // for boxing, we only consider invoke value.
      if (!opcode::is_an_invoke(value.opcode)) {
        return std::nullopt;
      }
    }

    const auto* value_method = opcode::is_an_invoke(value.opcode)
                                   ? value.method
                                   : value.positional_insn->get_method();
    bool has_unwrap_method = is_unboxed ? (value_method == unwrap_method ||
                                           value_method == abs_method)
                                        : value_method == unwrap_method;
    if (!has_unwrap_method) {
      return std::nullopt;
    }

    auto it = m_proper_id_values.find(value.srcs.at(0));
    if (it == m_proper_id_values.end()) {
      return std::nullopt;
    }

    const auto& inner_value = it->second;
    // For unboxing-boxing pattern, we don't consider abs-unboxing (i.e.
    // Ljava/lang/Number;.*value()*) at this time.
    if (opcode::is_an_invoke(inner_value.opcode) &&
        inner_value.method == wrap_method) {
      auto unwrapped_value = inner_value.srcs.at(0);
      if (!is_pre_state_src(unwrapped_value)) {
        // TODO: Support capturing pre-state values
        return std::optional<value_id_t>(unwrapped_value);
      }
    }
    return std::nullopt;
  }

  std::optional<value_id_t> get_value_id(const IRValue& value) const {
    auto it = m_value_ids.find(value);
    if (it != m_value_ids.end()) {
      return std::optional<value_id_t>(it->second);
    }
    value_id_t id = m_value_ids.size() * ValueIdFlags::BASE;
    always_assert(id / ValueIdFlags::BASE == m_value_ids.size());
    if (opcode::is_an_aget(value.opcode)) {
      id |= get_location_value_id_mask(get_read_array_location(value.opcode));
    } else if (opcode::is_an_iget(value.opcode) ||
               opcode::is_an_sget(value.opcode)) {
      auto location = get_field_location(value.opcode, value.field);
      if (location ==
          CseLocation(CseSpecialLocations::GENERAL_MEMORY_BARRIER)) {
        return std::nullopt;
      }
      id |= get_location_value_id_mask(location);
    } else if (opcode::is_an_invoke(value.opcode)) {
      id |= get_invoke_value_id_mask(value);
    }
    if (value.opcode != IOPCODE_PRE_STATE_SRC) {
      for (auto src : value.srcs) {
        id |= (src & ValueIdFlags::IS_TRACKED_LOCATION_MASK);
      }
    }
    if (value.opcode == IOPCODE_POSITIONAL) {
      m_positional_insns.emplace(id, value.positional_insn);
    } else if (value.opcode == IOPCODE_PRE_STATE_SRC) {
      m_pre_state_value_ids.insert(id);
    } else {
      const auto& abs_map = m_shared_state->get_abstract_map();
      // First match wins over an unordered iteration, which is only
      // deterministic because at most one pair can match: several pairs may
      // share an abstract unwrap method (Number.intValue backs both
      // Integer.intValue and Short.intValue), but unwrap_value also requires
      // the producer's method to equal this pair's wrap method, and the
      // producer has exactly one. unwrap_value is free of side effects, so the
      // pairs probed before the winner leave nothing behind either.
#if __GNUC__ >= 11 && __GNUC__ <= 14 && !defined(__clang__)
#pragma GCC diagnostic push
// Work around https://gcc.gnu.org/bugzilla/show_bug.cgi?id=116731
#pragma GCC diagnostic ignored "-Wrange-loop-construct"
#endif // __GNUC__ >= 11 && __GNUC__ <= 14 && !defined(__clang__)
      for (const auto [box_method, unbox_method] :
           UnorderedIterable(m_shared_state->get_boxing_map())) {
#if __GNUC__ >= 11 && __GNUC__ <= 14 && !defined(__clang__)
#pragma GCC diagnostic pop
#endif // __GNUC__ >= 11 && __GNUC__ <= 14 && !defined(__clang__)
        const DexMethodRef* abs_method = nullptr;
        auto abs_it = abs_map.find(unbox_method);
        if (abs_it != abs_map.end()) {
          abs_method = abs_it->second;
        }
        auto optional_unboxed_value_id = unwrap_value(
            value, unbox_method, box_method, abs_method, /* unboxed */ true);
        if (optional_unboxed_value_id) {
          // boxing-unboxing
          if (value.opcode == IOPCODE_POSITIONAL_UNBOXING &&
              m_unboxing_collection) {
            auto* insn = const_cast<IRInstruction*>(value.positional_insn);
            if (m_unboxing_collection->seen.insert(insn).second) {
              m_unboxing_collection->insns.emplace_back(insn);
            }
          }
          // Deliberately returns without entering `value` into `m_value_ids`.
          // The replay over the converged states re-runs this to rebuild the
          // unboxing list, and a cache hit here would skip the record above and
          // leave that list empty. Memoizing would also need a separate map:
          // the id returned here belongs to the inner value, not to `value`.
          return optional_unboxed_value_id;
        }
        auto optional_boxed_value_id = unwrap_value(
            value, box_method, unbox_method, abs_method, /* boxed */ false);
        if (optional_boxed_value_id) {
          // unboxing-boxing
          return optional_boxed_value_id;
        }
      }
      if (value.opcode == IOPCODE_POSITIONAL_UNBOXING) {
        // This means this value is not in a boxing-unboxing pattern. Therefore,
        // we put it in m_positional_insns list.
        m_positional_insns.emplace(id, value.positional_insn);
      } else {
        m_proper_id_values.emplace(id, value);
      }
    }
    m_value_ids.emplace(value, id);
    return std::optional<value_id_t>(id);
  }

  IRValue get_array_length_value(value_id_t array_value_id) const {
    IRValue value;
    value.opcode = OPCODE_ARRAY_LENGTH;
    value.srcs.push_back(array_value_id);
    return value;
  }

  std::optional<IRValue> get_equivalent_put_value(
      const IRInstruction* insn, CseEnvironment* current_state) const {
    const auto& ref_env = current_state->get_ref_env();
    if (opcode::is_an_sput(insn->opcode())) {
      always_assert(insn->srcs_size() == 1);
      IRValue value;
      value.opcode = (IROpcode)(insn->opcode() - OPCODE_SPUT + OPCODE_SGET);
      value.field = insn->get_field();
      return value;
    } else if (opcode::is_an_iput(insn->opcode())) {
      always_assert(insn->srcs_size() == 2);
      auto src1 = ref_env.get(insn->src(1)).get_constant();
      if (src1) {
        IRValue value;
        value.opcode = (IROpcode)(insn->opcode() - OPCODE_IPUT + OPCODE_IGET);
        value.srcs.push_back(*src1);
        value.field = insn->get_field();
        return value;
      }
    } else if (insn->opcode() == OPCODE_APUT_OBJECT) {
      // Skip this case. Statically, the incoming value can be of any object
      // type, as runtime validation ensures type correctness. Thus, we cannot
      // propagate an aput-object to an aget-object with a simple move-object.
      // TODO: Allow this here, but also insert a check-cast instead of a simple
      // move-object in this case, using type inference on the array argument of
      // the aget-object instruction.
    } else if (opcode::is_an_aput(insn->opcode())) {
      always_assert(insn->srcs_size() == 3);
      auto src1 = ref_env.get(insn->src(1)).get_constant();
      auto src2 = ref_env.get(insn->src(2)).get_constant();
      if (src1 && src2) {
        IRValue value;
        value.opcode = (IROpcode)(insn->opcode() - OPCODE_APUT + OPCODE_AGET);
        value.srcs.push_back(*src1);
        value.srcs.push_back(*src2);
        return value;
      }
    }
    return std::nullopt;
  }

  IRValue get_pre_state_src_value(reg_t reg, const IRInstruction* insn) const {
    IRValue value;
    value.opcode = IOPCODE_PRE_STATE_SRC;
    value.srcs.push_back(reg);
    value.positional_insn = insn;
    return value;
  }

  void init_pre_state(const IRInstruction* insn,
                      CseEnvironment* current_state) const {
    auto ref_env = current_state->get_ref_env();
    UnorderedMap<reg_t, value_id_t> new_pre_state_src_values;
    for (auto reg : insn->srcs()) {
      auto c = ref_env.get(reg).get_constant();
      if (!c) {
        auto it = new_pre_state_src_values.find(reg);
        if (it == new_pre_state_src_values.end()) {
          auto value_id = get_pre_state_src_value_id(reg, insn);
          new_pre_state_src_values.emplace(reg, value_id);
        }
      }
    }
    if (!new_pre_state_src_values.empty()) {
      current_state->mutate_ref_env([&](RefEnvironment* env) {
        for (const auto& p : UnorderedIterable(new_pre_state_src_values)) {
          env->set(p.first, ValueIdDomain(p.second));
        }
      });
    }
  }

  IRValue get_value(const IRInstruction* insn,
                    const CseEnvironment* current_state,
                    const CseUnorderedLocationSet& clobbered_locations) const {
    IRValue value;
    auto opcode = insn->opcode();
    always_assert(opcode != IOPCODE_PRE_STATE_SRC);
    value.opcode = opcode;
    const auto& ref_env = current_state->get_ref_env();
    for (auto reg : insn->srcs()) {
      auto c = ref_env.get(reg).get_constant();
      always_assert_log(c, "%s", SHOW(ref_env.get(reg)));
      value_id_t value_id = *c;
      value.srcs.push_back(value_id);
    }
    if (opcode::is_a_conditional_branch(opcode) && insn->srcs_size() == 1) {
      switch (opcode) {
      case OPCODE_IF_EQZ:
        opcode = OPCODE_IF_EQ;
        break;
      case OPCODE_IF_NEZ:
        opcode = OPCODE_IF_NE;
        break;
      case OPCODE_IF_LTZ:
        opcode = OPCODE_IF_LT;
        break;
      case OPCODE_IF_LEZ:
        opcode = OPCODE_IF_LE;
        break;
      case OPCODE_IF_GTZ:
        opcode = OPCODE_IF_GT;
        break;
      case OPCODE_IF_GEZ:
        opcode = OPCODE_IF_GE;
        break;
      default:
        not_reached();
      }
      value.opcode = opcode;
      IRValue zero_value;
      zero_value.opcode = OPCODE_CONST;
      zero_value.literal = 0;
      auto zero_value_id = *get_value_id(zero_value);
      value.srcs.push_back(zero_value_id);
    }
    if (opcode::is_commutative(opcode)) {
      std::sort(value.srcs.begin(), value.srcs.end());
    }
    bool is_positional;
    bool is_potential_abs_unboxing = false;
    switch (insn->opcode()) {
    case IOPCODE_LOAD_PARAM:
    case IOPCODE_LOAD_PARAM_OBJECT:
    case IOPCODE_LOAD_PARAM_WIDE:
    case OPCODE_MOVE_EXCEPTION:
    case OPCODE_NEW_ARRAY:
    case OPCODE_NEW_INSTANCE:
    case OPCODE_FILLED_NEW_ARRAY:
      is_positional = true;
      break;
    case OPCODE_INVOKE_VIRTUAL: {
      is_potential_abs_unboxing =
          m_shared_state->has_potential_unboxing_method(insn);
      is_positional = !m_shared_state->has_pure_method(insn);
      break;
    }
    case OPCODE_INVOKE_SUPER:
    case OPCODE_INVOKE_DIRECT:
    case OPCODE_INVOKE_STATIC:
    case OPCODE_INVOKE_INTERFACE: {
      // TODO: Is this really safe for all virtual/interface invokes? This
      //       mimics the way assumenosideeffects is used in LocalDCE.
      is_positional = !m_shared_state->has_pure_method(insn);
      break;
    }
    default:
      // there might be an impacted field, array element, general memory barrier
      always_assert(clobbered_locations.size() <= 1);
      is_positional = !clobbered_locations.empty();
      break;
    }
    if (is_positional) {
      if (is_potential_abs_unboxing) {
        value.opcode = IOPCODE_POSITIONAL_UNBOXING;
      } else {
        value.opcode = IOPCODE_POSITIONAL;
      }
      value.positional_insn = insn;
    } else if (insn->has_literal()) {
      value.literal = insn->get_literal();
    } else if (insn->has_type()) {
      value.type = insn->get_type();
    } else if (insn->has_field()) {
      value.field = insn->get_field();
    } else if (insn->has_method()) {
      value.method = insn->get_method();
    } else if (insn->has_string()) {
      value.string = insn->get_string();
    } else if (insn->has_data()) {
      value.data = insn->get_data();
    }
    return value;
  }

  value_id_t get_location_value_id_mask(CseLocation l) const {
    if (l == CseLocation(CseSpecialLocations::GENERAL_MEMORY_BARRIER)) {
      return ValueIdFlags::IS_TRACKED_LOCATION_MASK;
    } else {
      return m_tracked_locations.at(l);
    }
  }

  value_id_t get_invoke_value_id_mask(const IRValue& value) const {
    always_assert(opcode::is_an_invoke(value.opcode));
    value_id_t mask = 0;
    for (auto l : UnorderedIterable(
             m_shared_state->get_read_locations_of_conditionally_pure_method(
                 value.method, value.opcode))) {
      mask |= get_location_value_id_mask(l);
    }
    return mask;
  }

  const DexType* get_exact_type(value_id_t value_id) const {
    auto it = m_positional_insns.find(value_id);
    if (it == m_positional_insns.end()) {
      return nullptr;
    }
    const auto* insn = it->second;
    switch (insn->opcode()) {
    case OPCODE_NEW_ARRAY:
    case OPCODE_NEW_INSTANCE:
    case OPCODE_FILLED_NEW_ARRAY:
      return insn->get_type();
    default:
      return nullptr;
    }
  }

  bool m_using_other_tracked_location_bit{false};
  CseUnorderedLocationSet m_read_locations;
  UnorderedMap<CseLocation, value_id_t, CseLocationHasher> m_tracked_locations;
  SharedState* m_shared_state;
  mutable UnorderedMap<IRValue, value_id_t, IRValueHasher> m_value_ids;
  mutable UnorderedSet<value_id_t> m_pre_state_value_ids;
  mutable UnorderedMap<value_id_t, const IRInstruction*> m_positional_insns;
  mutable UnorderedMap<value_id_t, IRValue> m_proper_id_values;
};

} // namespace

namespace cse_impl {

////////////////////////////////////////////////////////////////////////////////

SharedState::SharedState(
    const UnorderedSet<DexMethodRef*>& pure_methods,
    const UnorderedSet<const DexString*>& finalish_field_names,
    const UnorderedSet<const DexField*>& finalish_fields)
    : m_pure_methods(pure_methods),
      m_safe_methods(pure_methods),
      m_finalish_field_names(finalish_field_names),
      m_finalish_fields(finalish_fields) {
  // The following methods are...
  // - static, or
  // - direct (constructors), or
  // - virtual methods defined in final classes
  // that do not mutate any fields or array elements that could be directly
  // accessed (read or written) by user code, and they will not invoke user
  // code.
  //
  // The list of methods is not exhaustive; it was derived by observing the most
  // common barriers encountered in real-life code, and then studying their spec
  // to check whether they are "safe" in the context of CSE barriers.
  static constexpr auto safe_method_names = std::to_array<std::string_view>({
      "Landroid/os/SystemClock;.elapsedRealtime:()J",
      "Landroid/os/SystemClock;.uptimeMillis:()J",
      "Landroid/util/SparseArray;.append:(ILjava/lang/Object;)V",
      "Landroid/util/SparseArray;.get:(I)Ljava/lang/Object;",
      "Landroid/util/SparseArray;.put:(ILjava/lang/Object;)V",
      "Landroid/util/SparseArray;.size:()I",
      "Landroid/util/SparseArray;.valueAt:(I)Ljava/lang/Object;",
      "Landroid/util/SparseIntArray;.put:(II)V",
      "Ljava/lang/Boolean;.parseBoolean:(Ljava/lang/String;)Z",
      "Ljava/lang/Byte;.parseByte:(Ljava/lang/String;)B",
      "Ljava/lang/Class;.forName:(Ljava/lang/String;)Ljava/lang/Class;",
      "Ljava/lang/Double;.parseDouble:(Ljava/lang/String;)D",
      // NOLINTNEXTLINE(bugprone-suspicious-missing-comma)
      "Ljava/lang/Enum;.valueOf:(Ljava/lang/Class;Ljava/lang/String;)Ljava/"
      "lang/Enum;",
      "Ljava/lang/Float;.parseFloat:(Ljava/lang/String;)F",
      "Ljava/lang/Integer;.parseInt:(Ljava/lang/String;)I",
      "Ljava/lang/Integer;.parseInt:(Ljava/lang/String;I)I",
      "Ljava/lang/Integer;.valueOf:(Ljava/lang/String;)Ljava/lang/Integer;",
      "Ljava/lang/Long;.parseLong:(Ljava/lang/String;)J",
      "Ljava/lang/Math;.addExact:(II)I",
      "Ljava/lang/Math;.addExact:(JJ)J",
      "Ljava/lang/Math;.decrementExact:(J)J",
      "Ljava/lang/Math;.decrementExact:(I)I",
      "Ljava/lang/Math;.incrementExact:(I)I",
      "Ljava/lang/Math;.incrementExact:(J)J",
      "Ljava/lang/Math;.multiplyExact:(II)I",
      "Ljava/lang/Math;.multiplyExact:(JJ)J",
      "Ljava/lang/Math;.negateExact:(I)I",
      "Ljava/lang/Math;.negateExact:(J)J",
      "Ljava/lang/Math;.subtractExact:(JJ)J",
      "Ljava/lang/Math;.subtractExact:(II)I",
      "Ljava/lang/Math;.toIntExact:(J)I",
      "Ljava/lang/ref/Reference;.get:()Ljava/lang/Object;",
      "Ljava/lang/String;.getBytes:()[B",
      "Ljava/lang/String;.split:(Ljava/lang/String;)[Ljava/lang/String;",
      "Ljava/lang/StringBuilder;.append:(C)Ljava/lang/StringBuilder;",
      "Ljava/lang/StringBuilder;.append:(I)Ljava/lang/StringBuilder;",
      "Ljava/lang/StringBuilder;.append:(J)Ljava/lang/StringBuilder;",
      "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/"
      "StringBuilder;",
      "Ljava/lang/StringBuilder;.append:(Z)Ljava/lang/StringBuilder;",
      "Ljava/lang/StringBuilder;.length:()I",
      "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;",
      "Ljava/lang/System;.currentTimeMillis:()J",
      "Ljava/lang/System;.nanoTime:()J",
      "Ljava/util/ArrayList;.add:(Ljava/lang/Object;)Z",
      "Ljava/util/ArrayList;.add:(ILjava/lang/Object;)V",
      "Ljava/util/ArrayList;.clear:()V",
      "Ljava/util/ArrayList;.get:(I)Ljava/lang/Object;",
      "Ljava/util/ArrayList;.isEmpty:()Z",
      "Ljava/util/ArrayList;.remove:(I)Ljava/lang/Object;",
      "Ljava/util/ArrayList;.size:()I",
      "Ljava/util/BitSet;.clear:()V",
      "Ljava/util/BitSet;.get:(I)Z",
      "Ljava/util/BitSet;.set:(I)V",
      "Ljava/util/HashMap;.isEmpty:()Z",
      "Ljava/util/HashMap;.size:()I",
      "Ljava/util/HashSet;.clear:()V",
      "Ljava/util/LinkedList;.add:(Ljava/lang/Object;)Z",
      "Ljava/util/LinkedList;.addLast:(Ljava/lang/Object;)V",
      "Ljava/util/LinkedList;.clear:()V",
      "Ljava/util/LinkedList;.get:(I)Ljava/lang/Object;",
      "Ljava/util/LinkedList;.getFirst:()Ljava/lang/Object;",
      "Ljava/util/LinkedList;.removeFirst:()Ljava/lang/Object;",
      "Ljava/util/LinkedList;.size:()I",
      "Ljava/util/Random;.nextInt:(I)I",

      "Landroid/util/Pair;.<init>:(Ljava/lang/Object;Ljava/lang/Object;)V",
      "Landroid/util/SparseArray;.<init>:()V",
      "Ljava/io/IOException;.<init>:(Ljava/lang/String;)V",
      "Ljava/lang/Enum;.<init>:(Ljava/lang/String;I)V",
      "Ljava/lang/Exception;.<init>:()V",
      "Ljava/lang/IllegalArgumentException;.<init>:(Ljava/lang/String;)V",
      "Ljava/lang/IllegalStateException;.<init>:()V",
      "Ljava/lang/IllegalStateException;.<init>:(Ljava/lang/String;)V",
      "Ljava/lang/Integer;.<init>:(I)V",
      "Ljava/lang/Long;.<init>:(J)V",
      "Ljava/lang/NullPointerException;.<init>:(Ljava/lang/String;)V",
      "Ljava/lang/Object;.<init>:()V",
      "Ljava/lang/RuntimeException;.<init>:(Ljava/lang/String;)V",
      "Ljava/lang/Short;.<init>:(S)V",
      "Ljava/lang/String;.<init>:(Ljava/lang/String;)V",
      "Ljava/lang/StringBuilder;.<init>:()V",
      "Ljava/lang/StringBuilder;.<init>:(I)V",
      "Ljava/lang/StringBuilder;.<init>:(Ljava/lang/String;)V",
      "Ljava/lang/UnsupportedOperationException;.<init>:(Ljava/lang/"
      "String;)V",
      "Ljava/util/ArrayList;.<init>:()V",
      "Ljava/util/ArrayList;.<init>:(I)V",
      "Ljava/util/BitSet;.<init>:(I)V",
      "Ljava/util/HashMap;.<init>:()V",
      "Ljava/util/HashMap;.<init>:(I)V",
      "Ljava/util/HashSet;.<init>:()V",
      "Ljava/util/LinkedHashMap;.<init>:()V",
      "Ljava/util/LinkedList;.<init>:()V",
      "Ljava/util/Random;.<init>:()V",
  });

  for (auto const safe_method_name : safe_method_names) {
    auto* method_ref = DexMethod::get_method(safe_method_name);
    if (method_ref == nullptr) {
      TRACE(CSE, 1, "[CSE]: Could not find safe method %s",
            str_copy(safe_method_name).c_str());
      continue;
    }

    m_safe_methods.insert(method_ref);
  }

  if (traceEnabled(CSE, 2)) {
    m_barriers.reset(new AtomicMap<Barrier, size_t, BarrierHasher>());
  }

  const std::vector<DexType*> boxing_types = {
      type::java_lang_Boolean(), type::java_lang_Byte(),
      type::java_lang_Short(),   type::java_lang_Character(),
      type::java_lang_Integer(), type::java_lang_Long(),
      type::java_lang_Float(),   type::java_lang_Double()};

  for (const auto* type : boxing_types) {
    const auto* box_method = type::make_value_of_method_for_type(type);
    const auto* unbox_method = type::make_unboxing_method_for_type(type);
    const auto* abs_method = type::make_Number_unboxing_method_for_type(type);
    m_boxing_map.insert({box_method, unbox_method});
    m_abstract_map.insert({unbox_method, abs_method});
  }
}

const method_override_graph::Graph* SharedState::get_method_override_graph()
    const {
  return m_method_override_graph.get();
}

void SharedState::init_method_barriers(const Scope& scope) {
  Timer t("init_method_barriers");
  auto iterations = compute_locations_closure(
      scope, m_method_override_graph.get(),
      [&](DexMethod* method) -> std::optional<LocationsAndDependencies> {
        auto action = get_base_or_overriding_method_action(
            method, &m_safe_method_defs,
            /* ignore_methods_with_assumenosideeffects */ true);
        if (action == MethodOverrideAction::UNKNOWN) {
          return std::nullopt;
        }
        LocationsAndDependencies lads;
        if (action == MethodOverrideAction::EXCLUDE) {
          return lads;
        }
        auto* code = method->get_code();
        for (const auto& mie : cfg::InstructionIterable(code->cfg())) {
          auto* insn = mie.insn;
          if (may_be_barrier(insn, nullptr /* exact_virtual_scope */)) {
            auto barrier = make_barrier(insn);
            if (!opcode::is_an_invoke(barrier.opcode)) {
              auto location = get_written_location(barrier);
              if (location ==
                  CseLocation(CseSpecialLocations::GENERAL_MEMORY_BARRIER)) {
                return std::nullopt;
              }
              lads.locations.insert(location);
              continue;
            }

            if (barrier.opcode == OPCODE_INVOKE_SUPER) {
              // TODO: Implement
              return std::nullopt;
            }

            if (!process_base_and_overriding_methods(
                    m_method_override_graph.get(), barrier.method,
                    &m_safe_method_defs,
                    /* ignore_methods_with_assumenosideeffects */ true,
                    [&](DexMethod* other_method) {
                      if (other_method != method) {
                        lads.dependencies.insert(other_method);
                      }
                      return true;
                    })) {
              return std::nullopt;
            }
          }
        }

        return lads;
      },
      &m_method_written_locations);
  m_stats.method_barriers_iterations = iterations;
  m_stats.method_barriers = m_method_written_locations.size();

  for (const auto& p : UnorderedIterable(m_method_written_locations)) {
    const auto* method = p.first;
    const auto& written_locations = p.second;
    TRACE(CSE, 4, "[CSE] inferred barrier for %s: %s", SHOW(method),
          SHOW(&written_locations));
  }
}

void SharedState::init_finalizable_fields(const Scope& scope) {
  Timer t("init_finalizable_fields");
  field_op_tracker::FieldStatsMap field_stats =
      field_op_tracker::analyze(scope);

  for (auto& pair : UnorderedIterable(field_stats)) {
    auto* field = pair.first;
    auto& stats = pair.second;
    // We are checking a subset of what the AccessMarking pass is checking for
    // finalization, as that's what CSE really cares about.
    if (stats.init_writes == stats.writes && can_rename(field) &&
        !is_final(field) && !is_volatile(field) && !field->is_external()) {
      m_finalizable_fields.insert(field);
    }
  }
  m_stats.finalizable_fields = m_finalizable_fields.size();
}

void SharedState::init_scope(
    const Scope& scope,
    const method::ClInitHasNoSideEffectsPredicate& clinit_has_no_side_effects) {
  always_assert(!m_method_override_graph);
  m_method_override_graph = method_override_graph::build_graph(scope);

  auto iterations = compute_conditionally_pure_methods(
      scope, m_method_override_graph.get(), clinit_has_no_side_effects,
      m_pure_methods, &m_conditionally_pure_methods);
  m_stats.conditionally_pure_methods = m_conditionally_pure_methods.size();
  m_stats.conditionally_pure_methods_iterations = iterations;
  for (const auto& p : UnorderedIterable(m_conditionally_pure_methods)) {
    m_pure_methods.insert(const_cast<DexMethod*>(p.first));
  }

  for (auto* method_ref : UnorderedIterable(m_safe_methods)) {
    auto* method = method_ref->as_def();
    if (method != nullptr) {
      m_safe_method_defs.insert(method);
    }
  }

  init_method_barriers(scope);
  init_finalizable_fields(scope);
}

CseUnorderedLocationSet SharedState::get_relevant_written_locations(
    const IRInstruction* insn,
    const DexType* exact_virtual_scope,
    const CseUnorderedLocationSet& read_locations) {
  if (may_be_barrier(insn, exact_virtual_scope)) {
    if (opcode::is_an_invoke(insn->opcode())) {
      return get_relevant_written_locations(insn, read_locations);
    } else {
      auto barrier = make_barrier(insn);
      if (is_barrier_relevant(barrier, read_locations)) {
        return CseUnorderedLocationSet{get_written_location(barrier)};
      }
    }
  }
  return no_locations;
}

bool SharedState::may_be_barrier(const IRInstruction* insn,
                                 const DexType* exact_virtual_scope) {
  auto opcode = insn->opcode();
  switch (opcode) {
  case OPCODE_MONITOR_ENTER:
  case OPCODE_MONITOR_EXIT:
  case OPCODE_FILL_ARRAY_DATA:
    return true;
  default:
    if (opcode::is_an_aput(opcode) || opcode::is_an_iput(opcode) ||
        opcode::is_an_sput(opcode)) {
      return true;
    } else if (opcode::is_an_invoke(opcode)) {
      return !is_invoke_safe(insn, exact_virtual_scope);
    }
    if (insn->has_field()) {
      always_assert(opcode::is_an_iget(opcode) || opcode::is_an_sget(opcode));
      if (get_field_location(opcode, insn->get_field()) ==
          CseLocation(CseSpecialLocations::GENERAL_MEMORY_BARRIER)) {
        return true;
      }
    }

    return false;
  }
}

bool SharedState::is_invoke_safe(const IRInstruction* insn,
                                 const DexType* exact_virtual_scope) {
  always_assert(opcode::is_an_invoke(insn->opcode()));
  auto* method_ref = insn->get_method();
  auto opcode = insn->opcode();

  if ((opcode == OPCODE_INVOKE_STATIC || opcode == OPCODE_INVOKE_DIRECT) &&
      (m_safe_methods.count(method_ref) != 0u)) {
    return true;
  }

  auto* method = resolve_method_deprecated(method_ref, opcode_to_search(insn));
  if (method == nullptr) {
    return false;
  }

  if ((opcode == OPCODE_INVOKE_STATIC || opcode == OPCODE_INVOKE_DIRECT) &&
      (m_safe_methods.count(method) != 0u)) {
    return true;
  }

  if (opcode == OPCODE_INVOKE_VIRTUAL && (m_safe_methods.count(method) != 0u)) {
    auto* type = method->get_class();
    auto* cls = type_class(type);
    always_assert(cls);
    if (is_final(cls) || is_final(method)) {
      return true;
    }
    if (type == exact_virtual_scope) {
      return true;
    }
  }

  if (opcode == OPCODE_INVOKE_INTERFACE &&
      (m_safe_methods.count(method) != 0u)) {
    return true;
  }

  return false;
}

CseUnorderedLocationSet SharedState::get_relevant_written_locations(
    const IRInstruction* insn, const CseUnorderedLocationSet& read_locations) {
  always_assert(opcode::is_an_invoke(insn->opcode()));

  auto opcode = insn->opcode();
  if (opcode == OPCODE_INVOKE_SUPER) {
    // TODO
    return general_memory_barrier_locations;
  }

  auto* method_ref = insn->get_method();
  DexMethod* method =
      resolve_method_deprecated(method_ref, opcode_to_search(insn));
  CseUnorderedLocationSet written_locations;
  if (!process_base_and_overriding_methods(
          m_method_override_graph.get(), method, &m_safe_method_defs,
          /* ignore_methods_with_assumenosideeffects */ true,
          [&](DexMethod* other_method) {
            auto it = m_method_written_locations.find(other_method);
            if (it == m_method_written_locations.end()) {
              return false;
            }
            insert_unordered_iterable(written_locations, it->second);
            return true;
          })) {
    return general_memory_barrier_locations;
  }

  // Remove written locations that are not read
  unordered_erase_if(written_locations, [&read_locations](auto& l) {
    return !read_locations.count(l);
  });

  return written_locations;
}

void SharedState::log_barrier(const Barrier& barrier) {
  if (m_barriers) {
    m_barriers->fetch_add(barrier, 1);
  }
}

const CseUnorderedLocationSet&
SharedState::get_read_locations_of_conditionally_pure_method(
    const DexMethodRef* method_ref, IROpcode opcode) const {
  auto* method = resolve_method_deprecated(
      const_cast<DexMethodRef*>(method_ref), opcode_to_search(opcode));
  if (method == nullptr) {
    return no_locations;
  }
  auto it = m_conditionally_pure_methods.find(method);
  if (it == m_conditionally_pure_methods.end()) {
    return no_locations;
  } else {
    return it->second;
  }
}

bool SharedState::has_potential_unboxing_method(
    const IRInstruction* insn) const {
  auto* method_ref = insn->get_method();
  for (const auto& abs_pair : UnorderedIterable(get_abstract_map())) {
    const auto* abs_method = abs_pair.second;
    if (method_ref == abs_method) {
      return true;
    }
  }
  return false;
}

bool SharedState::has_pure_method(const IRInstruction* insn) const {
  auto* method_ref = insn->get_method();
  if (m_pure_methods.find(method_ref) != m_pure_methods.end()) {
    TRACE(CSE, 4, "[CSE] unresolved %spure for %s",
          (method_ref->is_def() &&
           m_conditionally_pure_methods.count(method_ref->as_def()))
              ? "conditionally "
              : "",
          SHOW(method_ref));
    return true;
  }

  auto* method =
      resolve_method_deprecated(insn->get_method(), opcode_to_search(insn));
  if (method != nullptr &&
      m_pure_methods.find(method) != m_pure_methods.end()) {
    TRACE(CSE, 4, "[CSE] resolved %spure for %s",
          m_conditionally_pure_methods.count(method) ? "conditionally " : "",
          SHOW(method));
    return true;
  }

  return false;
}

bool SharedState::is_finalish(const DexField* field) const {
  return is_final(field) || !(m_finalizable_fields.count(field) == 0u) ||
         !(m_finalish_fields.count(field) == 0u) ||
         !(m_finalish_field_names.count(field->get_name()) == 0u);
}

void SharedState::cleanup() {
  if (!m_barriers) {
    return;
  }

  std::vector<std::pair<Barrier, size_t>> ordered_barriers;
  ordered_barriers.reserve(m_barriers->size());
  for (auto&& [barrier, count] : UnorderedIterable(*m_barriers)) {
    ordered_barriers.emplace_back(barrier, count.load());
  }
  std::sort(
      ordered_barriers.begin(), ordered_barriers.end(),
      [](const std::pair<Barrier, size_t>& a,
         const std::pair<Barrier, size_t>& b) { return b.second < a.second; });

  TRACE(CSE, 2, "most common barriers:");
  for (const auto& p : ordered_barriers) {
    const auto& b = p.first;
    auto c = p.second;
    if (opcode::is_an_invoke(b.opcode)) {
      TRACE(CSE, 2, "%s %s x %zu", SHOW(b.opcode), SHOW(b.method), c);
    } else if (opcode::is_an_ifield_op(b.opcode) ||
               opcode::is_an_sfield_op(b.opcode)) {
      TRACE(CSE, 2, "%s %s x %zu", SHOW(b.opcode), SHOW(b.field), c);
    } else {
      TRACE(CSE, 2, "%s x %zu", SHOW(b.opcode), c);
    }
  }
}

CommonSubexpressionElimination::CommonSubexpressionElimination(
    SharedState* shared_state,
    cfg::ControlFlowGraph& cfg,
    bool is_static,
    bool is_init_or_clinit,
    DexType* declaring_type,
    DexTypeList* args)
    : m_cfg(cfg),
      m_is_static(is_static),
      m_declaring_type(declaring_type),
      m_args(args),
      m_abs_map(shared_state->get_abstract_map()) {
  Analyzer analyzer(shared_state, cfg, is_static, is_init_or_clinit,
                    declaring_type);
  m_stats.max_value_ids = analyzer.get_value_ids_size();
  if (analyzer.using_other_tracked_location_bit()) {
    m_stats.methods_using_other_tracked_location_bit = 1;
  }

  UnorderedMap<std::vector<size_t>, size_t, boost::hash<std::vector<size_t>>>
      insns_ids;
  auto get_earlier_insns_index =
      [&](const PatriciaTreeSet<const IRInstruction*>& insns) {
        std::vector<size_t> ordered_ids;
        for (const auto* insn : insns) {
          ordered_ids.push_back(get_earlier_insn_id(insn));
        }
        std::sort(ordered_ids.begin(), ordered_ids.end());
        auto it = insns_ids.find(ordered_ids);
        if (it != insns_ids.end()) {
          return it->second;
        }
        auto index = insns_ids.size();
        always_assert(m_earlier_insns.size() == index);
        insns_ids.emplace(ordered_ids, index);
        m_earlier_insns.push_back(insns);
        return index;
      };

  // identify all instruction pairs where the result of the first instruction
  // can be forwarded to the second

  // Collect unboxing candidates from here on, so that they come from the
  // converged states the replay below walks, the same way m_forward is derived.
  analyzer.start_collecting_unboxing_insns();

  for (cfg::Block* block : cfg.blocks()) {
    auto env = analyzer.get_entry_state_at(block);
    if (env.is_bottom()) {
      continue;
    }
    auto last_insn = block->get_last_insn();
    if (last_insn == block->end()) {
      continue;
    }
    for (const auto& mie : InstructionIterable(block)) {
      IRInstruction* insn = mie.insn;
      analyzer.analyze_instruction(insn, &env, insn == last_insn->insn);
      auto opcode = insn->opcode();
      if (!insn->has_dest() || opcode::is_a_move(opcode) ||
          opcode::is_a_const(opcode)) {
        continue;
      }
      auto ref_c = env.get_ref_env().get(insn->dest()).get_constant();
      if (!ref_c) {
        continue;
      }
      auto value_id = *ref_c;
      always_assert(!analyzer.is_pre_state_src(value_id));
      auto defs = env.get_def_env().get(value_id);
      always_assert(!defs.is_top() && !defs.is_bottom());
      auto earlier_insns = defs.elements();
      if (earlier_insns.contains(insn)) {
        continue;
      }
      bool skip{false};
      for (const auto* earlier_insn : earlier_insns) {
        auto earlier_opcode = earlier_insn->opcode();
        if (opcode::is_a_load_param(earlier_opcode)) {
          skip = true;
          break;
        }
        if (opcode::is_a_cmp(opcode) || opcode::is_a_cmp(earlier_opcode)) {
          // See T46241704. We never de-duplicate cmp instructions due to an
          // apparent bug in various Dalvik (and ART?) versions. Also see this
          // documentation in the r8 source code:
          // https://r8.googlesource.com/r8/+/2638db4d3465d785a6a740cf09969cab96099cff/src/main/java/com/android/tools/r8/utils/InternalOptions.java#604
          skip = true;
          break;
        }
      }

      if (skip) {
        continue;
      }

      auto earlier_insns_index = get_earlier_insns_index(earlier_insns);
      m_forward.push_back({earlier_insns_index, insn});
    }

    if (!opcode::is_switch(last_insn->insn->opcode()) &&
        !opcode::is_a_conditional_branch(last_insn->insn->opcode())) {
      continue;
    }
    for (auto* edge : block->succs()) {
      const auto& exit_env = analyzer.get_exit_state_at(block);
      if (analyzer.analyze_edge(edge, exit_env).is_bottom()) {
        m_dead_edges.push_back(edge);
      }
    }
  }

  m_unboxing = analyzer.get_unboxing_insns();
}

size_t CommonSubexpressionElimination::get_earlier_insn_id(
    const IRInstruction* insn) {
  // We need some helper state/functions to build the list m_earlier_insns
  // of unique earlier-instruction sets. To make that deterministic, we use
  // instruction ids that represent the position of an instruction in the cfg.
  if (m_earlier_insn_ids.empty()) {
    for (const auto& mie : InstructionIterable(m_cfg)) {
      m_earlier_insn_ids.emplace(mie.insn, m_earlier_insn_ids.size());
    }
  }
  return m_earlier_insn_ids.at(insn);
}

static IROpcode get_move_opcode(const IRInstruction* earlier_insn) {
  always_assert(!opcode::is_a_literal_const(earlier_insn->opcode()));
  if (earlier_insn->has_dest()) {
    return earlier_insn->dest_is_wide()     ? OPCODE_MOVE_WIDE
           : earlier_insn->dest_is_object() ? OPCODE_MOVE_OBJECT
                                            : OPCODE_MOVE;
  } else if (earlier_insn->opcode() == OPCODE_NEW_ARRAY) {
    return OPCODE_MOVE;
  } else {
    always_assert(opcode::is_an_aput(earlier_insn->opcode()) ||
                  opcode::is_an_iput(earlier_insn->opcode()) ||
                  opcode::is_an_sput(earlier_insn->opcode()));
    return earlier_insn->src_is_wide(0) ? OPCODE_MOVE_WIDE
           : (earlier_insn->opcode() == OPCODE_APUT_OBJECT ||
              earlier_insn->opcode() == OPCODE_IPUT_OBJECT ||
              earlier_insn->opcode() == OPCODE_SPUT_OBJECT)
               ? OPCODE_MOVE_OBJECT
               : OPCODE_MOVE;
  }
}

static std::pair<IROpcode, std::optional<int64_t>> get_move_or_const_literal(
    const sparta::PatriciaTreeSet<const IRInstruction*>& insns) {
  std::optional<IROpcode> opcode;
  std::optional<int64_t> literal;
  for (const auto* insn : insns) {
    if (opcode::is_a_literal_const(insn->opcode())) {
      if (literal) {
        always_assert(*literal == insn->get_literal());
        always_assert(*opcode == insn->opcode());
      } else {
        literal = insn->get_literal();
        opcode = insn->opcode();
      }
      continue;
    }
    if (opcode) {
      always_assert(*opcode == get_move_opcode(insn));
    } else {
      opcode = get_move_opcode(insn);
    }
  }
  always_assert(opcode);
  always_assert(opcode::is_a_move(*opcode) ||
                opcode::is_a_literal_const(*opcode));
  always_assert(!opcode::is_a_literal_const(*opcode) || literal);
  return std::make_pair(*opcode, literal);
}

bool CommonSubexpressionElimination::patch(bool runtime_assertions) {
  if (!m_dead_edges.empty()) {
    m_cfg.delete_edges(m_dead_edges.begin(), m_dead_edges.end());
    m_stats.instructions_eliminated += m_cfg.remove_unreachable_blocks().first;
    m_stats.branches_eliminated += m_dead_edges.size();
  }

  if (m_forward.empty() && m_unboxing.empty()) {
    return !m_dead_edges.empty();
  }

  TRACE(CSE, 5, "[CSE] before:\n%s", SHOW(m_cfg));

  // gather relevant instructions, and allocate temp registers

  // We'll allocate one temp per "earlier_insns_index".
  // TODO: Do better, use less. A subset and its superset can share a temp.
  UnorderedMap<size_t, std::pair<IROpcode, reg_t>> temps;
  // We also remember for which instructions we'll need an iterator, as we'll
  // want to insert something after them.
  UnorderedSet<const IRInstruction*> iterator_insns;
  UnorderedSet<const IRInstruction*> combined_earlier_insns;
  for (const auto& f : m_forward) {
    iterator_insns.insert(f.insn);
    if (temps.count(f.earlier_insns_index) != 0u) {
      continue;
    }
    auto& earlier_insns = m_earlier_insns.at(f.earlier_insns_index);
    auto move_or_const_literal = get_move_or_const_literal(earlier_insns);
    auto opcode = move_or_const_literal.first;
    if (!opcode::is_a_move(opcode)) {
      continue;
    }
    combined_earlier_insns.insert(earlier_insns.begin(), earlier_insns.end());
    reg_t temp_reg = opcode == OPCODE_MOVE_WIDE ? m_cfg.allocate_wide_temp()
                                                : m_cfg.allocate_temp();
    temps.emplace(f.earlier_insns_index, std::make_pair(opcode, temp_reg));
  }
  for (const auto* earlier_insn : UnorderedIterable(combined_earlier_insns)) {
    iterator_insns.insert(earlier_insn);
    if (earlier_insn->has_dest()) {
      m_stats.results_captured++;
    } else if (earlier_insn->opcode() == OPCODE_NEW_ARRAY) {
      m_stats.array_lengths_captured++;
    } else {
      always_assert(opcode::is_an_aput(earlier_insn->opcode()) ||
                    opcode::is_an_iput(earlier_insn->opcode()) ||
                    opcode::is_an_sput(earlier_insn->opcode()));
      m_stats.stores_captured++;
    }
  }

  for (auto* unboxing_insn : m_unboxing) {
    iterator_insns.insert(unboxing_insn);
  }

  // find all iterators in one sweep

  UnorderedMap<IRInstruction*, cfg::InstructionIterator> iterators;
  auto iterable = cfg::InstructionIterable(m_cfg);
  for (auto it = iterable.begin(); it != iterable.end(); ++it) {
    auto* insn = it->insn;
    if (iterator_insns.count(insn) != 0u) {
      iterators.emplace(insn, it);
    }
  }

  // insert moves to use the forwarded value

  std::vector<std::pair<Forward, IRInstruction*>> to_check;
  for (const auto& f : m_forward) {
    auto& earlier_insns = m_earlier_insns.at(f.earlier_insns_index);

    IRInstruction* insn = f.insn;
    auto& it = iterators.at(insn);

    auto temp_it = temps.find(f.earlier_insns_index);
    if (temp_it == temps.end()) {
      auto move_or_const_literal = get_move_or_const_literal(earlier_insns);
      auto const_opcode = move_or_const_literal.first;
      always_assert(opcode::is_a_literal_const(const_opcode));
      auto literal = *(move_or_const_literal.second);

      // Consider this case:
      //   1. (const v0 0)
      //   2. (iput-object v0 v3 "LClass1;.field:Ljava/lang/Object;")
      //   3. (const v0 0)
      //   4. boxing-unboxing v0
      //   5. (move-result v0)
      //   6. (iput-boolean v0 v4 "LClass2;.field:Z")
      // We need to make sure that after opt-out "boxing-unboxing v0", v0 used
      // in insn 6. should not be the one used in insn 2, since in line 2, v0 is
      // used as null-0 and in line 4, v0 should be int. Therfore, instead of
      // insert a move, if there is any literal_const load in earlier_insns, we
      // just clone that const insn and override the dest to current insn's
      // dest. No need to add this new insn for runtime-assertion since it is
      // just a clone.
      IRInstruction* const_insn = new IRInstruction(const_opcode);
      const_insn->set_literal(literal)->set_dest(insn->dest());
      auto iterators_invalidated = m_cfg.insert_after(it, const_insn);
      always_assert(!iterators_invalidated);

      for (const auto* earlier_insn : earlier_insns) {
        TRACE(CSE, 4, "[CSE] forwarding %s to %s as const %" PRId64,
              SHOW(earlier_insn), SHOW(insn), literal);
      }
    } else {
      auto [move_opcode, temp_reg] = temp_it->second;
      always_assert(opcode::is_a_move(move_opcode));

      IRInstruction* move_insn = new IRInstruction(move_opcode);
      move_insn->set_src(0, temp_reg)->set_dest(insn->dest());
      auto iterators_invalidated = m_cfg.insert_after(it, move_insn);
      always_assert(!iterators_invalidated);
      if (runtime_assertions) {
        to_check.emplace_back(f, move_insn);
      }

      for (const auto* earlier_insn : earlier_insns) {
        TRACE(CSE, 4, "[CSE] forwarding %s to %s via v%u", SHOW(earlier_insn),
              SHOW(insn), temp_reg);
      }
    }

    if (opcode::is_move_result_any(insn->opcode())) {
      insn = m_cfg.primary_instruction_of_move_result(it)->insn;
      if (opcode::is_an_invoke(insn->opcode())) {
        TRACE(CSE, 3, "[CSE] eliminating invocation of %s",
              SHOW(insn->get_method()));
      }
    }
    m_stats.eliminated_opcodes[insn->opcode()]++;
  }

  // Insert moves to define the forwarded value.
  // We are going to call ControlFlow::insert_after, which may introduce new
  // blocks when inserting after the last instruction of a block with
  // throws-edges. To make that deterministic, we need to make sure that we
  // insert in a deterministic order. To this end, we follow the deterministic
  // m_forward order, and we order earlier instructions by their ids.
  for (const auto& f : m_forward) {
    auto temp_it = temps.find(f.earlier_insns_index);
    if (temp_it == temps.end()) {
      continue;
    }
    auto [move_opcode, temp_reg] = temp_it->second;
    always_assert(opcode::is_a_move(move_opcode));
    temps.erase(temp_it);

    auto& earlier_insns_unordered = m_earlier_insns.at(f.earlier_insns_index);
    std::vector<const IRInstruction*> earlier_insns_ordered(
        earlier_insns_unordered.begin(), earlier_insns_unordered.end());
    always_assert(!m_earlier_insn_ids.empty());
    std::sort(earlier_insns_ordered.begin(), earlier_insns_ordered.end(),
              [&](const auto* a, const auto* b) {
                return get_earlier_insn_id(a) < get_earlier_insn_id(b);
              });

    for (const auto* earlier_insn : earlier_insns_ordered) {
      auto& it = iterators.at(const_cast<IRInstruction*>(earlier_insn));
      IRInstruction* move_insn = new IRInstruction(move_opcode);
      auto src_reg = earlier_insn->has_dest() ? earlier_insn->dest()
                                              : earlier_insn->src(0);
      move_insn->set_src(0, src_reg)->set_dest(temp_reg);
      if (earlier_insn->opcode() == OPCODE_NEW_ARRAY) {
        // we need to capture the array-length register of a new-array
        // instruction *before* the instruction, as the dest of the instruction
        // may overwrite the incoming array length value
        auto iterators_invalidated = m_cfg.insert_before(it, move_insn);
        always_assert(!iterators_invalidated);
      } else {
        auto iterators_invalidated = m_cfg.insert_after(it, move_insn);
        always_assert(!iterators_invalidated);
      }
    }
  }
  always_assert(temps.empty());

  if (runtime_assertions) {
    insert_runtime_assertions(to_check);
  }

  TRACE(CSE, 5, "[CSE] after:\n%s", SHOW(m_cfg));

  m_stats.instructions_eliminated += m_forward.size();

  if (!m_unboxing.empty()) {
    // Inserting check-casts might split blocks and invalidate iterators, thus
    // we go through the CFGMutation helper class that properly deals with this
    // complication.

    cfg::CFGMutation mutation(m_cfg);
    // For the abs methods which are part of boxing-unboxing pattern, we refine
    // it to its impl, which will be viewed as "pure" method and can be optmized
    // out later.
    for (auto* unboxing_insn : m_unboxing) {
      auto& it = iterators.at(unboxing_insn);
      auto* method_ref = unboxing_insn->get_method();
      auto abs_it = unordered_find_if(
          m_abs_map, [method_ref](auto& p) { return p.second == method_ref; });
      // set_method below rewrites the ref, so a repeated instruction would not
      // resolve here on its second visit.
      always_assert_log(abs_it != m_abs_map.end(),
                        "not an abstract unboxing method: %s",
                        SHOW(unboxing_insn));
      const auto* impl = abs_it->first;
      auto src_reg = unboxing_insn->src(0);
      auto* check_cast_insn = (new IRInstruction(OPCODE_CHECK_CAST))
                                  ->set_src(0, src_reg)
                                  ->set_type(impl->get_class());
      auto* pseudo_move_result_insn =
          (new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT))
              ->set_dest(src_reg);
      // Add instructions
      mutation.insert_before(it, {check_cast_insn, pseudo_move_result_insn});
      // Replace the call method from abs_unboxing method to its impl.
      unboxing_insn->set_method(const_cast<DexMethodRef*>(impl));
    }
    mutation.flush();
  }

  return true;
}

void CommonSubexpressionElimination::insert_runtime_assertions(
    const std::vector<std::pair<Forward, IRInstruction*>>& to_check) {
  // For every instruction that CSE will effectively eliminate, we insert
  // code like the following:
  //
  // OLD_CODE:
  //    first-instruction r0
  //    redundant-instruction r1
  //  NEW_ASSERTION_CODE:
  //    if-ne r0, r1, THROW
  //  CSE_CODE:
  //    move r1, r0 // <= to realize CSE; without the NEW_ASSERTION_CODE,
  //                //    the redundant-instruction would be eliminated by DCE.
  //    ...
  //  THROW:
  //    const r2, 0
  //    throw r2
  //
  // The new throw instruction would throw a NullPointerException when the
  // redundant instruction didn't actually produce the same result as the
  // first instruction.
  //
  // TODO: Consider throwing a custom exception, possibly created by code
  // sitting behind an auxiliary method call to keep the code size distortion
  // small which may influence other optimizations. See
  // ConstantPropagationAssertHandler for inspiration.
  //
  // Note: Somehow inserting assertions seems to trip up the OptimizeEnumsPass
  // (it fails while running Redex).
  // TODO: Investigate why. Until then, disable that pass to test CSE.

  // If the original block had a throw-edge, then the new block that throws an
  // exception needs to have a corresponding throw-edge. As we split blocks to
  // insert conditional branches, and splitting blocks removes throw-edges from
  // the original block, we need to make sure that we track what throw-edges as\
  // needed. (All this is to appease the Android verifier in the presence of
  // monitor instructions.)
  UnorderedMap<cfg::Block*, std::vector<cfg::Edge*>> outgoing_throws;
  for (auto* b : m_cfg.blocks()) {
    outgoing_throws.emplace(b, b->get_outgoing_throws_in_order());
  }

  // We need type inference information to generate the right kinds of
  // conditional branches.
  type_inference::TypeInference type_inference(m_cfg);
  type_inference.run(m_is_static, m_declaring_type, m_args);
  auto& type_environments = type_inference.get_type_environments();

  for (const auto& p : to_check) {
    const auto& f = p.first;
    auto& earlier_insns = m_earlier_insns.at(f.earlier_insns_index);
    for (const auto* earlier_insn : earlier_insns) {
      IRInstruction* insn = f.insn;
      auto* move_insn = p.second;

      auto& type_environment = type_environments.at(insn);
      auto temp = move_insn->src(0);
      auto type = type_environment.get_type(temp);
      always_assert(!type.is_top());
      always_assert(!type.is_bottom());
      TRACE(CSE, 6, "[CSE] to check: %s => %s - r%u: %s", SHOW(earlier_insn),
            SHOW(insn), temp, SHOW(type.element()));
      always_assert(type.element() != IRType::CONST2);
      always_assert(type.element() != IRType::LONG2);
      always_assert(type.element() != IRType::DOUBLE2);
      always_assert(type.element() != IRType::SCALAR2);
      if (type.element() != IRType::ZERO && type.element() != IRType::CONST &&
          type.element() != IRType::INT &&
          type.element() != IRType::REFERENCE &&
          type.element() != IRType::LONG1) {
        // TODO: Handle floats and doubles via Float.floatToIntBits and
        // Double.doubleToLongBits to deal with NaN.
        // TODO: Improve TypeInference so that we never have to deal with
        // SCALAR* values where we don't know if it's a int/float or
        // long/double.
        continue;
      }

      auto it = m_cfg.find_insn(insn);
      auto* old_block = it.block();
      auto* new_block = m_cfg.split_block(it);
      outgoing_throws.emplace(new_block, outgoing_throws.at(old_block));

      auto* throw_block = m_cfg.create_block();
      auto null_reg = m_cfg.allocate_temp();
      IRInstruction* const_insn = new IRInstruction(OPCODE_CONST);
      const_insn->set_literal(0);
      const_insn->set_dest(null_reg);
      throw_block->push_back(const_insn);
      IRInstruction* throw_insn = new IRInstruction(OPCODE_THROW);
      throw_insn->set_src(0, null_reg);
      throw_block->push_back(throw_insn);

      for (auto* e : outgoing_throws.at(old_block)) {
        auto* throw_info = e->throw_info();
        m_cfg.add_edge(throw_block, e->target(), throw_info->catch_type,
                       throw_info->index);
      }

      if (type.element() == IRType::LONG1) {
        auto cmp_reg = m_cfg.allocate_temp();
        IRInstruction* cmp_insn = new IRInstruction(OPCODE_CMP_LONG);
        cmp_insn->set_dest(cmp_reg);
        cmp_insn->set_src(0, move_insn->dest());
        cmp_insn->set_src(1, move_insn->src(0));
        old_block->push_back(cmp_insn);

        IRInstruction* if_insn = new IRInstruction(OPCODE_IF_NEZ);
        if_insn->set_src(0, cmp_reg);
        m_cfg.create_branch(old_block, if_insn, new_block, throw_block);
      } else {
        IRInstruction* if_insn = new IRInstruction(OPCODE_IF_NE);
        if_insn->set_src(0, move_insn->dest());
        if_insn->set_src(1, move_insn->src(0));
        m_cfg.create_branch(old_block, if_insn, new_block, throw_block);
      }
    }
  }
}

Stats& Stats::operator+=(const Stats& that) {
  results_captured += that.results_captured;
  stores_captured += that.stores_captured;
  array_lengths_captured += that.array_lengths_captured;
  instructions_eliminated += that.instructions_eliminated;
  max_value_ids = std::max(max_value_ids, that.max_value_ids);
  methods_using_other_tracked_location_bit +=
      that.methods_using_other_tracked_location_bit;
  for (const auto& p : UnorderedIterable(that.eliminated_opcodes)) {
    eliminated_opcodes[p.first] += p.second;
  }
  max_iterations = std::max(max_iterations, that.max_iterations);
  branches_eliminated += that.branches_eliminated;
  return *this;
}

} // namespace cse_impl
