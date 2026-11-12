/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ReduceArrayLiterals.h"

#include <cinttypes>

#include <sparta/ConstantAbstractDomain.h>
#include <sparta/HashedSetAbstractDomain.h>
#include <sparta/PatriciaTreeMap.h>
#include <sparta/PatriciaTreeMapAbstractEnvironment.h>
#include <sparta/PatriciaTreeSet.h>

#include "BaseIRAnalyzer.h"
#include "CFGMutation.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexStructure.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "LiveRange.h"
#include "PassManager.h"
#include "Show.h"
#include "Trace.h"
#include "TypeUtil.h"
#include "Walkers.h"

using namespace sparta;

namespace {

constexpr const char* METRIC_FILLED_ARRAYS = "num_filled_arrays";
constexpr const char* METRIC_FILLED_ARRAY_ELEMENTS =
    "num_filled_array_elements";
constexpr const char* METRIC_FILLED_ARRAY_CHUNKS = "num_filled_array_chunks";
constexpr const char* METRIC_REMAINING_WIDE_ARRAYS =
    "num_remaining_wide_arrays";
constexpr const char* METRIC_REMAINING_WIDE_ARRAY_ELEMENTS =
    "num_remaining_wide_array_elements";
constexpr const char* METRIC_REMAINING_UNIMPLEMENTED_ARRAYS =
    "num_remaining_unimplemented_arrays";
constexpr const char* METRIC_REMAINING_UNIMPLEMENTED_ARRAY_ELEMENTS =
    "num_remaining_unimplemented_array_elements";
constexpr const char* METRIC_REMAINING_BUGGY_ARRAYS =
    "num_remaining_buggy_arrays";
constexpr const char* METRIC_REMAINING_BUGGY_ARRAY_ELEMENTS =
    "num_remaining_buggy_array_elements";

/* A tracked value is...
 * - a 32-bit literal,
 * - or a new-array instruction that was reached with a well-known array length,
 *   and has been followed by a number of aput instructions that initialized the
 *   individual array elements in order, or
 * - some other value.
 */

enum TrackedValueKind : uint32_t { Other, Literal, NewArray };

struct TrackedValue {
  TrackedValueKind kind;
  union {
    int32_t literal; // for kind == Literal
    uint32_t length; // for kind == NewArray
  };
  // The following are only used for kind == NewArray
  const IRInstruction* new_array_insn;
  uint32_t aput_insns_size{0};
  PatriciaTreeMap<uint32_t, const IRInstruction*> aput_insns{};
  PatriciaTreeSet<const IRInstruction*> aput_insns_range;
};

struct TrackedValueHasher {
  size_t operator()(const TrackedValue& tv) const {
    switch (tv.kind) {
    case TrackedValueKind::Other:
      return std::numeric_limits<size_t>::max();
    case TrackedValueKind::Literal:
      return static_cast<size_t>(tv.literal);
    case TrackedValueKind::NewArray:
      return tv.length + reinterpret_cast<size_t>(tv.new_array_insn) ^
             tv.aput_insns_size;
    default:
      not_reached();
    }
  }
};

bool operator==(const TrackedValue& a, const TrackedValue& b) {
  if (a.kind != b.kind) {
    return false;
  }
  switch (a.kind) {
  case TrackedValueKind::Other:
    return true;
  case TrackedValueKind::Literal:
    return a.literal == b.literal;
  case TrackedValueKind::NewArray:
    return a.length == b.length && a.new_array_insn == b.new_array_insn &&
           a.aput_insns_size == b.aput_insns_size &&
           a.aput_insns == b.aput_insns;
  default:
    not_reached();
  }
}

TrackedValue make_other() {
  return (TrackedValue){.kind = TrackedValueKind::Other,
                        .literal = 0,
                        .new_array_insn = nullptr,
                        .aput_insns_range = {}};
}

TrackedValue make_literal(const IRInstruction* instr) {
  always_assert(instr->opcode() == OPCODE_CONST);
  always_assert(instr->has_literal());
  auto lit = instr->get_literal();
  always_assert(lit <= 2147483647 && lit >= -2147483648);
  return (TrackedValue){.kind = TrackedValueKind::Literal,
                        .literal = static_cast<int32_t>(lit),
                        .new_array_insn = nullptr,
                        .aput_insns_range = {}};
}

TrackedValue make_array(uint32_t length, const IRInstruction* instr) {
  always_assert(length >= 0);
  always_assert(instr->opcode() == OPCODE_NEW_ARRAY);
  return (TrackedValue){.kind = TrackedValueKind::NewArray,
                        .length = length,
                        .new_array_insn = instr,
                        .aput_insns_range = {}};
}

bool is_new_array(const TrackedValue& tv) {
  return tv.kind == TrackedValueKind::NewArray;
}

bool is_literal(const TrackedValue& tv) {
  return tv.kind == TrackedValueKind::Literal;
}

int64_t get_literal(const TrackedValue& tv) {
  always_assert(is_literal(tv));
  return tv.literal;
}

bool is_next_index(const TrackedValue& tv, int64_t index) {
  always_assert(is_new_array(tv));
  return index == tv.aput_insns_size;
}

bool is_array_literal(const TrackedValue& tv) {
  return is_new_array(tv) && (int64_t)tv.aput_insns_size == tv.length;
}

bool can_add_element(TrackedValue& array,
                     int64_t index,
                     const IRInstruction* aput_insn) {
  always_assert(is_new_array(array));
  always_assert(is_next_index(array, index));
  always_assert(!is_array_literal(array));
  always_assert(aput_insn != nullptr);
  return !array.aput_insns_range.contains(aput_insn);
}

bool add_element(TrackedValue& array,
                 int64_t index,
                 const IRInstruction* aput_insn) {
  if (!can_add_element(array, index, aput_insn)) {
    return false;
  }
  array.aput_insns_size++;
  array.aput_insns_range.insert(aput_insn);
  array.aput_insns.insert_or_assign((uint32_t)index, aput_insn);
  return true;
}

std::vector<const IRInstruction*> get_aput_insns(const TrackedValue& array) {
  always_assert(is_array_literal(array));
  std::vector<const IRInstruction*> aput_insns;
  aput_insns.reserve(array.length);
  for (uint32_t i = 0; i < array.length; i++) {
    const IRInstruction* aput_insn = array.aput_insns.at(i);
    always_assert(aput_insn != nullptr);
    aput_insns.push_back(aput_insn);
  }
  return aput_insns;
}

using namespace ir_analyzer;

using TrackedDomain =
    sparta::HashedSetAbstractDomain<TrackedValue, TrackedValueHasher>;
using EscapedArrayDomain =
    sparta::ConstantAbstractDomain<std::vector<const IRInstruction*>>;

/**
 * For each register that holds a relevant value, keep track of it.
 **/
using TrackedDomainEnvironment =
    sparta::PatriciaTreeMapAbstractEnvironment<reg_t, TrackedDomain>;

class Analyzer final
    : public BaseEdgeAwareIRAnalyzer<TrackedDomainEnvironment> {

 public:
  explicit Analyzer(cfg::ControlFlowGraph& cfg) : BaseEdgeAwareIRAnalyzer(cfg) {
    MonotonicFixpointIterator::run(TrackedDomainEnvironment::top());
  }

  void analyze_instruction_normal(
      const IRInstruction* insn,
      TrackedDomainEnvironment* current_state) const override {
    TRACE(RAL, 3, "[RAL] %s", SHOW(insn));
    switch (insn->opcode()) {
    case OPCODE_CONST:
      set_current_state_at(insn->dest(), false /* is_wide */,
                           TrackedDomain(make_literal(insn)), current_state);
      break;

    case OPCODE_NEW_ARRAY: {
      TRACE(RAL, 4, "[RAL]   new array of type %s", SHOW(insn->get_type()));
      if (!get_constructible_array_length(insn, *current_state)) {
        m_escaped_arrays[insn] = EscapedArrayDomain::top();
        default_case(insn, current_state);
      }
      break;
    }

    case IOPCODE_MOVE_RESULT_PSEUDO_OBJECT: {
      const auto& value = current_state->get(RESULT_REGISTER);
      set_current_state_at(insn->dest(), false /* is_wide */, value,
                           current_state);
      break;
    }

    case OPCODE_APUT:
    case OPCODE_APUT_BYTE:
    case OPCODE_APUT_CHAR:
    case OPCODE_APUT_WIDE:
    case OPCODE_APUT_SHORT:
    case OPCODE_APUT_OBJECT:
    case OPCODE_APUT_BOOLEAN: {
      escape_new_arrays(insn->src(0), current_state);
      const auto array = get_singleton(current_state->get(insn->src(1)));
      const auto index = get_singleton(current_state->get(insn->src(2)));
      TRACE(RAL, 4, "[RAL]   aput: %d %d", array && is_new_array(*array),
            index && is_literal(*index));
      if (is_array_construction_in_progress(array, index)) {
        int64_t index_literal = get_literal(*index);
        TRACE(RAL, 4, "[RAL]    index %" PRId64 " of %u", index_literal,
              array->length);
        if (is_next_index(*array, index_literal)) {
          TRACE(RAL, 4, "[RAL]    is next");
          TrackedValue new_array = *array;
          if (can_add_element(new_array, index_literal, insn)) {
            break;
          }
        }
      }

      default_case(insn, current_state);
      break;
    }

    case OPCODE_MOVE: {
      const auto value = get_singleton(current_state->get(insn->src(0)));
      if (value && is_literal(*value)) {
        set_current_state_at(insn->dest(), false /* is_wide */,
                             TrackedDomain(*value), current_state);
        break;
      }

      default_case(insn, current_state);
      break;
    }

    default: {
      default_case(insn, current_state);
      break;
    }
    }
  }

  void analyze_no_throw(
      const IRInstruction* insn,
      TrackedDomainEnvironment* current_state) const override {
    TRACE(RAL, 3, "[RAL] %s", SHOW(insn));
    switch (insn->opcode()) {
    case OPCODE_NEW_ARRAY: {
      TRACE(RAL, 4, "[RAL]   new array of type %s", SHOW(insn->get_type()));
      const auto length = get_constructible_array_length(insn, *current_state);
      if (length) {
        TRACE(RAL, 4, "[RAL]     with length %u", *length);
        current_state->set(RESULT_REGISTER,
                           TrackedDomain(make_array(*length, insn)));
      }
      break;
    }

    case OPCODE_APUT:
    case OPCODE_APUT_BYTE:
    case OPCODE_APUT_CHAR:
    case OPCODE_APUT_WIDE:
    case OPCODE_APUT_SHORT:
    case OPCODE_APUT_OBJECT:
    case OPCODE_APUT_BOOLEAN: {
      const auto array = get_singleton(current_state->get(insn->src(1)));
      const auto index = get_singleton(current_state->get(insn->src(2)));
      TRACE(RAL, 4, "[RAL]   aput: %d %d", array && is_new_array(*array),
            index && is_literal(*index));
      if (is_array_construction_in_progress(array, index)) {
        int64_t index_literal = get_literal(*index);
        TRACE(RAL, 4, "[RAL]    index %" PRId64 " of %u", index_literal,
              array->length);
        if (is_next_index(*array, index_literal)) {
          TRACE(RAL, 4, "[RAL]    is next");
          TrackedValue new_array = *array;
          if (add_element(new_array, index_literal, insn)) {
            current_state->set(insn->src(1), TrackedDomain(new_array));
          }
        }
      }
      break;
    }

    default: {
      break;
    }
    }
  }

  UnorderedMap<const IRInstruction*, std::vector<const IRInstruction*>>
  get_array_literals() {
    UnorderedMap<const IRInstruction*, std::vector<const IRInstruction*>>
        result;
    for (auto& p : UnorderedIterable(m_escaped_arrays)) {
      auto constant = p.second.get_constant();
      if (constant) {
        result.emplace(p.first, *constant);
      }
    }
    return result;
  }

 private:
  // The length of the array that a new-array instruction constructs, if it is
  // a known literal. A negative length makes new-array throw
  // NegativeArraySizeException, so no array is constructed and there is no
  // literal array to track.
  std::optional<uint32_t> get_constructible_array_length(
      const IRInstruction* new_array_insn,
      const TrackedDomainEnvironment& current_state) const {
    const auto length =
        get_singleton(current_state.get(new_array_insn->src(0)));
    if (!length || !is_literal(*length)) {
      return std::nullopt;
    }
    const int64_t literal = get_literal(*length);
    always_assert(literal <= std::numeric_limits<int32_t>::max());
    if (literal < 0) {
      return std::nullopt;
    }
    return static_cast<uint32_t>(literal);
  }

  bool is_array_construction_in_progress(
      const std::optional<TrackedValue>& array,
      const std::optional<TrackedValue>& index) const {
    return array && is_new_array(*array) && !is_array_literal(*array) &&
           index && is_literal(*index);
  }

  void set_current_state_at(reg_t reg,
                            bool wide,
                            const TrackedDomain& value,
                            TrackedDomainEnvironment* current_state) const {
    current_state->set(reg, value);
    if (wide) {
      current_state->set(reg + 1, TrackedDomain::top());
    }
  }

  std::optional<TrackedValue> get_singleton(const TrackedDomain& domain) const {
    if (domain.kind() != AbstractValueKind::Value) {
      return std::nullopt;
    }
    const auto& elements = domain.elements();
    if (elements.size() != 1) {
      return std::nullopt;
    }
    return std::optional<TrackedValue>(*elements.begin());
  }

  void escape_new_arrays(uint32_t reg,
                         TrackedDomainEnvironment* current_state) const {
    const auto& domain = current_state->get(reg);
    always_assert(domain.kind() == AbstractValueKind::Value);
    for (const auto& value : domain.elements()) {
      if (is_new_array(value)) {
        if (is_array_literal(value)) {
          auto escaped_array = EscapedArrayDomain(get_aput_insns(value));
          auto it = m_escaped_arrays.find(value.new_array_insn);
          if (it == m_escaped_arrays.end()) {
            m_escaped_arrays.emplace(value.new_array_insn, escaped_array);
          } else {
            it->second.join_with(escaped_array);
          }
          TRACE(RAL, 4, "[RAL]   literal array escaped");
        } else {
          TRACE(RAL, 4, "[RAL]   non-literal array escaped");
          m_escaped_arrays[value.new_array_insn] = EscapedArrayDomain::top();
        }
      }
    }
  }

  void default_case(const IRInstruction* insn,
                    TrackedDomainEnvironment* current_state) const {
    // mark escaping arrays
    for (size_t i = 0; i < insn->srcs_size(); i++) {
      escape_new_arrays(insn->src(i), current_state);
    }

    // If we get here, reset destination.
    if (insn->has_dest()) {
      set_current_state_at(insn->dest(), insn->dest_is_wide(),
                           TrackedDomain(make_other()), current_state);
    } else if (insn->has_move_result_any()) {
      current_state->set(RESULT_REGISTER, TrackedDomain(make_other()));
    }
  }

  mutable UnorderedMap<const IRInstruction*, EscapedArrayDomain>
      m_escaped_arrays;
};

bool has_left_out_aputs(live_range::DefUseChains du_chains,
                        const IRInstruction* new_array_insn,
                        const std::vector<const IRInstruction*>& aput_insns) {
  const auto& use_set = du_chains[const_cast<IRInstruction*>(new_array_insn)];
  // We don't want to patch an array literal if the array value is consumed by
  // an APUT that's not tracked by the analysis. Please see the
  // `conditional_escape2` test case in ReduceArrayLiteralsTest.
  size_t num_use_aputs = unordered_count_if(use_set, [](const auto& use) {
    return opcode::is_an_aput(use.insn->opcode());
  });
  always_assert(num_use_aputs >= aput_insns.size());
  return num_use_aputs > aput_insns.size();
}

} // namespace

////////////////////////////////////////////////////////////////////////////////

ReduceArrayLiterals::ReduceArrayLiterals(cfg::ControlFlowGraph& cfg,
                                         size_t max_filled_elements,
                                         int32_t min_sdk,
                                         Architecture arch)
    : m_cfg(cfg),
      m_max_filled_elements(max_filled_elements),
      m_min_sdk(min_sdk),
      m_arch(arch) {

  std::vector<IRInstruction*> new_array_insns;
  for (auto& mie : cfg::InstructionIterable(cfg)) {
    auto* insn = mie.insn;
    if (insn->opcode() == OPCODE_NEW_ARRAY) {
      new_array_insns.push_back(insn);
    }
  }

  if (new_array_insns.empty()) {
    return;
  }

  Analyzer analyzer(cfg);
  auto array_literals = analyzer.get_array_literals();
  // sort array literals by order of occurrence for determinism
  for (IRInstruction* new_array_insn : new_array_insns) {
    auto it = array_literals.find(new_array_insn);
    if (it != array_literals.end()) {
      m_array_literals.emplace_back(*it);
    }
  }
  always_assert(array_literals.size() == m_array_literals.size());
}

void ReduceArrayLiterals::patch() {
  live_range::MoveAwareChains chains(m_cfg);
  live_range::DefUseChains du_chains = chains.get_def_use_chains();

  for (auto& p : m_array_literals) {
    const IRInstruction* new_array_insn = p.first;
    std::vector<const IRInstruction*>& aput_insns = p.second;
    if (aput_insns.empty()) {
      // Really no point of doing anything with these
      continue;
    }

    const auto* type = new_array_insn->get_type();
    auto* element_type = type::get_array_component_type(type);

    if (has_left_out_aputs(du_chains, new_array_insn, aput_insns)) {
      continue;
    }

    if (m_min_sdk < 24) {
      // See T45708995.
      //
      // There seems to be an issue with the filled-new-array instruction on
      // Android 5 and 6.
      //
      // We see crashes in
      //   bool art::interpreter::DoFilledNewArray<true, false, false>(
      //     art::Instruction const*, art::ShadowFrame const&, art::Thread*,
      //     art::JValue*) (libart.so :)
      // and
      //   bool art::interpreter::DoFilledNewArray<false, false, false>(
      //     art::Instruction const*, art::ShadowFrame const&, art::Thread*,
      //     art::JValue*) (libart.so :)
      //
      // The actual cause, and whether it affects all kinds of arrays, is not
      // clear and needs further investigation.
      // For the time being, we play it safe, and don't do the transformation.
      //
      // TODO: Find true root cause, and make this exception more targetted.
      m_stats.remaining_buggy_arrays++;
      m_stats.remaining_buggy_array_elements += aput_insns.size();
      continue;
    }

    if (type::is_wide_type(element_type)) {
      // TODO: Consider using an annotation-based scheme.
      m_stats.remaining_wide_arrays++;
      m_stats.remaining_wide_array_elements += aput_insns.size();
      continue;
    }

    if (type::is_primitive(element_type) && element_type != type::_int()) {
      // Somewhat surprising random implementation limitation in all known
      // ART versions:
      // https://android.googlesource.com/platform/art/+/400455c23d6a9a849d090b9e60ff53c4422e461b/runtime/interpreter/interpreter_common.cc#189
      m_stats.remaining_unimplemented_arrays++;
      m_stats.remaining_unimplemented_array_elements += aput_insns.size();
      continue;
    }

    m_stats.filled_arrays++;
    m_stats.filled_array_elements += aput_insns.size();

    patch_new_array(new_array_insn, aput_insns);
  }
}

void ReduceArrayLiterals::patch_new_array(
    const IRInstruction* new_array_insn,
    const std::vector<const IRInstruction*>& aput_insns) {
  const auto* type = new_array_insn->get_type();

  // prepare for chunking, if needed

  std::optional<reg_t> chunk_dest;
  if (aput_insns.size() > m_max_filled_elements) {
    // we are going to chunk
    chunk_dest = m_cfg.allocate_temp();
    // ensure we have access to some temp regs just needed for local operations;
    // these temps can be shared across new-array optimizations, as they are
    // only used in a very narrow region
    for (; m_local_temp_regs.size() < 3;) {
      m_local_temp_regs.push_back(m_cfg.allocate_temp());
    }
  }

  // remove new-array instruction

  auto it = m_cfg.find_insn(new_array_insn);
  always_assert(new_array_insn->opcode() == OPCODE_NEW_ARRAY);
  auto move_result_it = m_cfg.move_result_of(it);
  if (move_result_it.is_end()) {
    return;
  }
  always_assert(move_result_it->insn->opcode() ==
                IOPCODE_MOVE_RESULT_PSEUDO_OBJECT);
  auto overall_dest = move_result_it->insn->dest();
  if (!chunk_dest) {
    m_cfg.remove_insn(it); // removes move-result-pseudo as well
  }

  // We'll maintain a vector of temporary registers that will receive the moved
  // aput values. Note that we cannot share these registers across different
  // new-array optimizations, as they may have overlapping scopes. Most of these
  // temporary registers will get optimized away by later optimization passes.
  std::vector<reg_t> temp_regs;
  for (size_t chunk_start = 0; chunk_start < aput_insns.size();) {
    auto chunk_size = patch_new_array_chunk(
        type, chunk_start, aput_insns, chunk_dest, overall_dest, &temp_regs);
    chunk_start += chunk_size;
  }
}

size_t ReduceArrayLiterals::patch_new_array_chunk(
    const DexType* type,
    size_t chunk_start,
    const std::vector<const IRInstruction*>& aput_insns,
    std::optional<reg_t> chunk_dest,
    reg_t overall_dest,
    std::vector<reg_t>* temp_regs) {
  cfg::CFGMutation mutation(m_cfg);

  size_t chunk_size =
      std::min(aput_insns.size() - chunk_start, m_max_filled_elements);
  size_t chunk_end = chunk_start + chunk_size;

  // insert filled-new-array instruction after the last aput of the current
  // chunk:
  //   filled-new-array t0, ..., tn, type
  //   move-result      c

  IRInstruction* last_aput_insn =
      const_cast<IRInstruction*>(aput_insns[chunk_end - 1]);
  auto it = m_cfg.find_insn(last_aput_insn);

  std::vector<IRInstruction*> new_insns;

  IRInstruction* filled_new_array_insn =
      new IRInstruction(OPCODE_FILLED_NEW_ARRAY);
  filled_new_array_insn->set_type(type);
  filled_new_array_insn->set_srcs_size(chunk_size);
  for (size_t index = chunk_start; index < chunk_end; index++) {
    size_t temp_reg_index = index - chunk_start;
    if (temp_reg_index == temp_regs->size()) {
      temp_regs->push_back(m_cfg.allocate_temp());
    }
    filled_new_array_insn->set_src(index - chunk_start,
                                   temp_regs->at(index - chunk_start));
  }
  new_insns.push_back(filled_new_array_insn);

  IRInstruction* move_result_object_insn =
      new IRInstruction(OPCODE_MOVE_RESULT_OBJECT);
  move_result_object_insn->set_dest(chunk_dest ? *chunk_dest : overall_dest);
  new_insns.push_back(move_result_object_insn);

  if (chunk_dest) {
    m_stats.filled_array_chunks++;
    // insert call to copy array elements from chunk to overall result array:
    // const lt0, 0
    // const lt1, chunk_start
    // const lt2, chunk_size
    // invoke-static chunk-dest, lt0, overall-dest, lt1, lt2

    IRInstruction* const_insn = new IRInstruction(OPCODE_CONST);
    const_insn->set_literal(0)->set_dest(m_local_temp_regs[0]);
    new_insns.push_back(const_insn);
    const_insn = new IRInstruction(OPCODE_CONST);
    const_insn->set_literal(static_cast<int64_t>(chunk_start))
        ->set_dest(m_local_temp_regs[1]);
    new_insns.push_back(const_insn);
    const_insn = new IRInstruction(OPCODE_CONST);
    const_insn->set_literal(static_cast<int64_t>(chunk_size))
        ->set_dest(m_local_temp_regs[2]);
    new_insns.push_back(const_insn);
    IRInstruction* invoke_static_insn = new IRInstruction(OPCODE_INVOKE_STATIC);
    auto* arraycopy_method = DexMethod::get_method(
        "Ljava/lang/System;.arraycopy:"
        "(Ljava/lang/Object;ILjava/lang/Object;II)V");
    always_assert(arraycopy_method != nullptr);
    invoke_static_insn->set_method(arraycopy_method);
    invoke_static_insn->set_srcs_size(5);
    invoke_static_insn->set_src(0, *chunk_dest);
    invoke_static_insn->set_src(1, m_local_temp_regs[0]);
    invoke_static_insn->set_src(2, overall_dest);
    invoke_static_insn->set_src(3, m_local_temp_regs[1]);
    invoke_static_insn->set_src(4, m_local_temp_regs[2]);
    new_insns.push_back(invoke_static_insn);
  }
  mutation.insert_after(it, new_insns);

  // find iterators corresponding to the aput instructions
  UnorderedSet<const IRInstruction*> aput_insns_set(aput_insns.begin(),
                                                    aput_insns.end());
  UnorderedMap<const IRInstruction*, cfg::InstructionIterator>
      aput_insns_iterators;
  auto iterable = cfg::InstructionIterable(m_cfg);
  for (auto insn_it = iterable.begin(); insn_it != iterable.end(); ++insn_it) {
    auto* insn = insn_it->insn;
    if (aput_insns_set.count(insn) != 0u) {
      aput_insns_iterators.emplace(insn, insn_it);
    }
  }

  // replace aput instructions with moves or check-cast instructions to
  // temporary regs used by filled-new-array instruction (see above)

  // most check-cast instructions will get eliminated again by the
  // remove-reundant-check-casts pass

  auto* component_type = type::get_array_component_type(type);
  bool is_component_type_primitive = type::is_primitive(component_type);
  for (size_t index = chunk_start; index < chunk_end; index++) {
    const IRInstruction* aput_insn = aput_insns[index];
    always_assert(opcode::is_an_aput(aput_insn->opcode()));
    always_assert(aput_insn->src(1) == overall_dest);
    it = aput_insns_iterators.at(aput_insn);
    auto dest = filled_new_array_insn->src(index - chunk_start);
    auto src = aput_insn->src(0);
    if (is_component_type_primitive) {
      always_assert(aput_insn->opcode() != OPCODE_APUT_OBJECT);
      IRInstruction* move_insn = new IRInstruction(OPCODE_MOVE);
      move_insn->set_dest(dest);
      move_insn->set_src(0, src);
      mutation.replace(it, {move_insn});
    } else {
      always_assert(aput_insn->opcode() == OPCODE_APUT_OBJECT);
      IRInstruction* check_cast_insn = new IRInstruction(OPCODE_CHECK_CAST);
      check_cast_insn->set_type(component_type);
      check_cast_insn->set_src(0, src);
      IRInstruction* move_result_pseudo_object_insn =
          new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT);
      move_result_pseudo_object_insn->set_dest(dest);
      mutation.replace(it, {check_cast_insn, move_result_pseudo_object_insn});
    }
  }
  mutation.flush();

  return chunk_size;
}

void ReduceArrayLiteralsPass::bind_config() {
  bind("debug", false, m_debug);
  // The default value 27 is somewhat arbitrary and could be tweaked.
  // Intention is to be reasonably small as to not cause excessive pressure on
  // the register allocator, and use an excessive number of stack space at
  // runtime, while also being reasonably large so that this optimization still
  // results in a significant win in terms of instructions count.
  bind("max_filled_elements", 27, m_max_filled_elements);
  after_configuration([this] { always_assert(m_max_filled_elements < 0xff); });
}

void ReduceArrayLiteralsPass::eval_pass(DexStoresVector&,
                                        ConfigFiles&,
                                        PassManager& mgr) {
  if (m_eval++ == 0) {
    m_reserved_refs_handle = mgr.reserve_refs(name(),
                                              ReserveRefsInfo(/* frefs */ 0,
                                                              /* trefs */ 0,
                                                              /* mrefs */ 1));
  }
}

void ReduceArrayLiteralsPass::run_pass(DexStoresVector& stores,
                                       ConfigFiles& /* conf */,
                                       PassManager& mgr) {
  ++m_run;
  // For the last invocation, release reserved refs.
  if (m_eval == m_run) {
    always_assert(m_reserved_refs_handle);
    mgr.release_reserved_refs(*m_reserved_refs_handle);
    m_reserved_refs_handle = std::nullopt;
  }

  int32_t min_sdk = mgr.get_redex_options().min_sdk;
  Architecture arch = mgr.get_redex_options().arch;
  TRACE(RAL, 1, "[RAL] min_sdk=%d, arch=%s", min_sdk,
        architecture_to_string(arch));

  const auto scope = build_class_scope(stores);

  const auto stats = walk::parallel::methods<ReduceArrayLiterals::Stats>(
      scope,
      [&](DexMethod* m) {
        auto* const code = m->get_code();
        if (code == nullptr || m->rstate.no_optimizations()) {
          return ReduceArrayLiterals::Stats();
        }
        always_assert(code->cfg_built());
        ReduceArrayLiterals ral(code->cfg(), m_max_filled_elements, min_sdk,
                                arch);
        ral.patch();
        return ral.get_stats();
      },
      m_debug ? 1 : redex_parallel::default_num_threads());
  mgr.incr_metric(METRIC_FILLED_ARRAYS, stats.filled_arrays);
  mgr.incr_metric(METRIC_FILLED_ARRAY_ELEMENTS, stats.filled_array_elements);
  mgr.incr_metric(METRIC_FILLED_ARRAY_CHUNKS, stats.filled_array_chunks);
  mgr.incr_metric(METRIC_REMAINING_WIDE_ARRAYS, stats.remaining_wide_arrays);
  mgr.incr_metric(METRIC_REMAINING_WIDE_ARRAY_ELEMENTS,
                  stats.remaining_wide_array_elements);
  mgr.incr_metric(METRIC_REMAINING_UNIMPLEMENTED_ARRAYS,
                  stats.remaining_unimplemented_arrays);
  mgr.incr_metric(METRIC_REMAINING_UNIMPLEMENTED_ARRAY_ELEMENTS,
                  stats.remaining_unimplemented_array_elements);
  mgr.incr_metric(METRIC_REMAINING_BUGGY_ARRAYS, stats.remaining_buggy_arrays);
  mgr.incr_metric(METRIC_REMAINING_BUGGY_ARRAY_ELEMENTS,
                  stats.remaining_buggy_array_elements);
}

ReduceArrayLiterals::Stats& ReduceArrayLiterals::Stats::operator+=(
    const ReduceArrayLiterals::Stats& that) {
  filled_arrays += that.filled_arrays;
  filled_array_elements += that.filled_array_elements;
  filled_array_chunks += that.filled_array_chunks;
  remaining_wide_arrays += that.remaining_wide_arrays;
  remaining_wide_array_elements += that.remaining_wide_array_elements;
  remaining_unimplemented_arrays += that.remaining_unimplemented_arrays;
  remaining_unimplemented_array_elements +=
      that.remaining_unimplemented_array_elements;
  remaining_buggy_arrays += that.remaining_buggy_arrays;
  remaining_buggy_array_elements += that.remaining_buggy_array_elements;
  return *this;
}

static ReduceArrayLiteralsPass s_pass;
