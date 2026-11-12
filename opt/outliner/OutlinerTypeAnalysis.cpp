/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "OutlinerTypeAnalysis.h"

#include <bit>
#include <queue>

#include "Debug.h"
#include "DexClass.h"
#include "DexTypeEnvironment.h"
#include "Lazy.h"
#include "Show.h"

namespace outliner_impl {

namespace {

// The five integral types, in the order of the bits of an integral mask.
enum Integral : uint8_t { Z, B, S, C, I, kNumIntegral };

const DexType* integral_dex_type(uint8_t k) {
  switch (k) {
  case Z:
    return type::_boolean();
  case B:
    return type::_byte();
  case S:
    return type::_short();
  case C:
    return type::_char();
  default:
    return type::_int();
  }
}

uint8_t integral_index(const DexType* t) {
  if (t == type::_boolean()) {
    return Z;
  }
  if (t == type::_byte()) {
    return B;
  }
  if (t == type::_short()) {
    return S;
  }
  if (t == type::_char()) {
    return C;
  }
  always_assert_log(t == type::_int(), "%s is not integral", SHOW(t));
  return I;
}

// Z < B < S < I and Z < C < I.
constexpr bool integral_leq(uint8_t a, uint8_t b) {
  if (a == b || b == I) {
    return true;
  }
  if (a == Z) {
    return b == B || b == S || b == C;
  }
  return a == B && b == S;
}

constexpr uint8_t integral_lub(uint8_t a, uint8_t b) {
  if (integral_leq(a, b)) {
    return b;
  }
  if (integral_leq(b, a)) {
    return a;
  }
  return I;
}

// The types among Z, B, S, C that hold `value`, as a mask.
uint8_t holding_types(int64_t value) {
  uint8_t mask = 0;
  if (value >= 0 && value <= 1) {
    mask |= 1u << Z;
  }
  if (value >= std::numeric_limits<int8_t>::min() &&
      value <= std::numeric_limits<int8_t>::max()) {
    mask |= 1u << B;
  }
  if (value >= std::numeric_limits<int16_t>::min() &&
      value <= std::numeric_limits<int16_t>::max()) {
    mask |= 1u << S;
  }
  if (value >= 0 && value <= std::numeric_limits<uint16_t>::max()) {
    mask |= 1u << C;
  }
  return mask;
}

// The types among Z, B, S, C that hold every constant in `constants`, a set of
// holding masks as `IntegralType` keeps them.
uint8_t holding_every(uint16_t constants) {
  uint8_t mask = (1u << Z) | (1u << B) | (1u << S) | (1u << C);
  for (uint8_t h = 0; h < 16; ++h) {
    if ((constants & (1u << h)) != 0) {
      mask &= h;
    }
  }
  return mask;
}

// ART's merge of a value of type `t` with a constant held by exactly the types
// in `holding` (`RegType::Merge`): the first of Z, B, S, C that is at or above
// `t` and holds the constant, else I. Note the order: a `boolean` and 65
// merge into `byte` although `char` holds both too.
constexpr uint8_t merge_type_with_constant(uint8_t t, uint8_t holding) {
  for (uint8_t k : {Z, B, S, C}) {
    if (integral_leq(t, k) && (holding & (1u << k)) != 0) {
      return k;
    }
  }
  return I;
}

// `float`, `long` and `double`, in the order of the bits of a mask.
const DexType* primitive_dex_type(uint8_t mask) {
  switch (mask) {
  case 1:
    return type::_float();
  case 2:
    return type::_long();
  default:
    always_assert(mask == 4);
    return type::_double();
  }
}

uint8_t primitive_bit(const DexType* t) {
  if (t == type::_float()) {
    return 1;
  }
  if (t == type::_long()) {
    return 2;
  }
  if (t == type::_double()) {
    return 4;
  }
  return 0;
}

// Sorts `t` into the masks and set that `art::Value` and `art::Demand` keep.
void add_integral(uint8_t* integral, const DexType* t) {
  *integral |= 1u << integral_index(t);
}

void add_integral(std::optional<IntegralType>* integral, const DexType* t) {
  *integral = IntegralType::join(*integral, IntegralType::of(t));
}

template <class IntegralRep>
void classify(const DexType* t,
              IntegralRep* integral,
              uint8_t* primitives,
              UnorderedSet<const DexType*>* references) {
  if (type::is_integral(t)) {
    add_integral(integral, t);
  } else if (auto bit = primitive_bit(t); bit != 0) {
    *primitives |= bit;
  } else {
    references->insert(t);
  }
}

// `and`, `or` and `xor`, whose result ART types by their operands.
bool is_bitwise(IROpcode op) {
  switch (op) {
  case OPCODE_AND_INT:
  case OPCODE_OR_INT:
  case OPCODE_XOR_INT:
  case OPCODE_AND_INT_LIT:
  case OPCODE_OR_INT_LIT:
  case OPCODE_XOR_INT_LIT:
    return true;
  default:
    return false;
  }
}

// Whether ART types `bitwise` as boolean when all its register operands are
// boolean. A literal operand must also be 0 or 1.
bool keeps_booleanness(const IRInstruction* bitwise) {
  return !bitwise->has_literal() || bitwise->get_literal() == 0 ||
         bitwise->get_literal() == 1;
}

// Whether a demand walk follows a value through `use` into its result.
bool follows_boolean(const IRInstruction* use) {
  return is_bitwise(use->opcode()) && keeps_booleanness(use);
}

const DexType* compute_joined_type(const UnorderedSet<const DexType*>& types) {
  std::optional<dtv_impl::DexTypeValue> joined_type_value;
  // Fold in a stable type order, because `join_with` is neither associative
  // nor commutative. When the walk up the superclasses reaches Object,
  // `find_common_type` falls back to the interfaces both operands implement.
  // It collects them from the left operand only. When there are several
  // incomparable ones, it gives up and returns Top, because no DexType can
  // hold their intersection. Either rule makes the result depend on the
  // order in which the types are joined.
  for (const auto* t : unordered_to_ordered(types, compare_dextypes)) {
    if (!type::is_object(t)) {
      return nullptr;
    }
    auto type_value = dtv_impl::DexTypeValue(t);
    if (joined_type_value) {
      if (joined_type_value->join_with(type_value) ==
          sparta::AbstractValueKind::Top) {
        return nullptr;
      }
      always_assert(joined_type_value->get_dex_type());
    } else {
      joined_type_value = type_value;
    }
  }
  return joined_type_value ? joined_type_value->get_dex_type() : nullptr;
}

// Removes each class or array type `u` from `types` when another class or
// array type `t` in `types` satisfies `is_redundant(u, t)`.
template <class Pred>
void erase_redundant_references(UnorderedSet<const DexType*>* types,
                                const Pred& is_redundant) {
  unordered_erase_if(*types, [types, &is_redundant](const DexType* u) {
    return type::is_object(u) &&
           unordered_any_of(*types, [u, &is_redundant](const DexType* t) {
             return t != u && type::is_object(t) && is_redundant(u, t);
           });
  });
}

} // namespace

IntegralType IntegralType::of(const DexType* t) {
  return {static_cast<uint8_t>(1u << integral_index(t)), 0};
}

IntegralType IntegralType::constant(int64_t value) {
  return {0, static_cast<uint16_t>(1u << holding_types(value))};
}

IntegralType IntegralType::join(const IntegralType& a, const IntegralType& b) {
  return {static_cast<uint8_t>(a.m_types | b.m_types),
          static_cast<uint16_t>(a.m_constants | b.m_constants)};
}

const DexType* IntegralType::type() const {
  if (is_constant()) {
    return nullptr;
  }
  // The join of every type and of every merge of a type with one constant.
  // OutlinerTypeAnalysisTest checks it against ART's merge in every order.
  uint8_t joined = kNumIntegral;
  for (uint8_t t = 0; t < kNumIntegral; ++t) {
    if ((m_types & (1u << t)) == 0) {
      continue;
    }
    joined = joined == kNumIntegral ? t : integral_lub(joined, t);
    for (uint8_t holding = 0; holding < 16; ++holding) {
      if ((m_constants & (1u << holding)) != 0) {
        joined = integral_lub(joined, merge_type_with_constant(t, holding));
      }
    }
  }
  return integral_dex_type(joined);
}

const DexType* IntegralType::exact_type() const {
  if (is_constant()) {
    return nullptr;
  }
  // The lowest type any merge order ends at is the join of the producers'
  // types merged with all constants at once. The orders agree exactly when
  // that lowest end is also `type()`, the highest. OutlinerTypeAnalysisTest
  // checks this against ART's merge in every order.
  uint8_t types = kNumIntegral;
  for (uint8_t t = 0; t < kNumIntegral; ++t) {
    if ((m_types & (1u << t)) != 0) {
      types = types == kNumIntegral ? t : integral_lub(types, t);
    }
  }
  const auto lowest =
      merge_type_with_constant(types, holding_every(m_constants));
  const auto* upper = type();
  return integral_dex_type(lowest) == upper ? upper : nullptr;
}

bool IntegralType::leq(const IntegralType& bound) const {
  if (bound.is_constant()) {
    if (!is_constant()) {
      return false;
    }
    auto mine = holding_every(m_constants);
    return (mine & holding_every(bound.m_constants)) ==
           holding_every(bound.m_constants);
  }
  auto b = integral_index(bound.type());
  if (is_constant()) {
    return b == I || (holding_every(m_constants) & (1u << b)) != 0;
  }
  return integral_leq(integral_index(type()), b);
}

namespace art {

Value Value::unknown() {
  Value v;
  v.m_unknown = true;
  return v;
}

Value Value::of_type(const DexType* t) {
  if (t == nullptr) {
    return unknown();
  }
  Value v;
  classify(t, &v.m_integral, &v.m_primitives, &v.m_references);
  return v;
}

Value Value::constant(const IRInstruction* insn) {
  always_assert(insn->opcode() == OPCODE_CONST ||
                insn->opcode() == OPCODE_CONST_WIDE);
  Value v;
  v.m_constants = IntegralType::constant(insn->get_literal());
  v.m_wide_constant = insn->opcode() == OPCODE_CONST_WIDE;
  return v;
}

void Value::join_with(const Value& other) {
  m_unknown |= other.m_unknown;
  if (other.m_integral) {
    m_integral = IntegralType::join(m_integral, *other.m_integral);
  }
  m_primitives |= other.m_primitives;
  insert_unordered_iterable(m_references, other.m_references);
  if (other.m_constants) {
    m_constants = IntegralType::join(m_constants, *other.m_constants);
  }
  m_wide_constant |= other.m_wide_constant;
}

std::optional<IntegralType> Value::integral() const {
  if (m_unknown || m_wide_constant || m_primitives != 0 ||
      !m_references.empty() || (!m_integral && !m_constants)) {
    return std::nullopt;
  }
  if (!m_constants) {
    return m_integral;
  }
  return IntegralType::join(m_integral, *m_constants);
}

bool Value::is_constant() const {
  return !m_unknown && m_constants && !m_integral && m_primitives == 0 &&
         m_references.empty();
}

const DexType* Value::upper() const {
  if (m_unknown) {
    return nullptr;
  }
  const int kinds = (m_integral ? 1 : 0) + std::popcount(m_primitives) +
                    (m_references.empty() ? 0 : 1);
  if (kinds != 1) {
    return nullptr;
  }
  if (m_integral) {
    auto value = integral();
    return value ? value->type() : nullptr;
  }
  if (m_primitives != 0) {
    return primitive_dex_type(m_primitives);
  }
  // The least specific types, joined.
  auto types = m_references;
  erase_redundant_references(&types, [](const DexType* u, const DexType* t) {
    return type::check_cast(u, t);
  });
  if (types.size() > 1) {
    return compute_joined_type(types);
  }
  return types.empty() ? nullptr : *unordered_any(types);
}

const DexType* Value::exact() const {
  const auto* t = upper();
  return t != nullptr && m_integral ? integral()->exact_type() : t;
}

Demand Demand::unknown() {
  Demand d;
  d.m_unknown = true;
  return d;
}

Demand Demand::of_use(const DexType* t) {
  if (t == nullptr) {
    return unknown();
  }
  Demand d;
  classify(t, &d.m_integral, &d.m_primitives, &d.m_references);
  return d;
}

void Demand::meet_with(const Demand& other) {
  m_unknown |= other.m_unknown;
  m_integral |= other.m_integral;
  m_primitives |= other.m_primitives;
  insert_unordered_iterable(m_references, other.m_references);
}

Demand Demand::through_bitwise() const {
  constexpr uint8_t kNarrow = (1u << Z) | (1u << B) | (1u << S) | (1u << C);
  Demand d = *this;
  if ((d.m_integral & kNarrow) != 0) {
    d.m_integral = (d.m_integral & ~kNarrow) | (1u << Z);
  }
  return d;
}

bool Demand::is_none() const {
  return !m_unknown && m_integral == 0 && m_primitives == 0 &&
         m_references.empty();
}

const DexType* Demand::widest() const {
  if (m_unknown) {
    return nullptr;
  }
  auto has = [this](uint8_t k) { return (m_integral & (1u << k)) != 0; };
  const DexType* integral = nullptr;
  if (has(Z)) {
    integral = type::_boolean();
  } else if (has(C) && (has(B) || has(S))) {
    // Of the integral types, only `boolean` is assignable both to `char` and
    // to `byte` or `short`, and `int` is assignable to neither.
    return nullptr;
  } else {
    for (uint8_t k : {B, S, C, I}) {
      if (has(k)) {
        integral = integral_dex_type(k);
        break;
      }
    }
  }
  // The most specific types.
  auto types = m_references;
  erase_redundant_references(&types, [](const DexType* u, const DexType* t) {
    return type::check_cast(t, u);
  });
  const size_t kinds = (integral != nullptr ? 1 : 0) +
                       std::popcount(m_primitives) + types.size();
  if (kinds != 1) {
    return nullptr;
  }
  if (integral != nullptr) {
    return integral;
  }
  if (m_primitives != 0) {
    return primitive_dex_type(m_primitives);
  }
  return *unordered_any(types);
}

const DexType* declare_parameter(const Demand& uses,
                                 const std::function<Value()>& supply) {
  if (const auto* t = uses.widest()) {
    return t;
  }
  return supply().upper();
}

const DexType* declare_result(const Value& returned) {
  return returned.exact();
}

} // namespace art

OutlinerTypeAnalysis::OutlinerTypeAnalysis(DexMethod* method)
    : m_method(method),
      m_reaching_defs_environments([method]() {
        auto& cfg = method->get_code()->cfg();
        reaching_defs::MoveAwareFixpointIterator reaching_defs_fp_iter(cfg);
        reaching_defs_fp_iter.run({});
        ReachingDefsEnvironments res;
        for (auto* block : cfg.blocks()) {
          auto env = reaching_defs_fp_iter.get_entry_state_at(block);
          for (auto& mie : InstructionIterable(block)) {
            res[mie.insn] = env;
            reaching_defs_fp_iter.analyze_instruction(mie.insn, &env);
          }
        }
        return res;
      }),
      m_immediate_chains([method]() {
        auto& cfg = method->get_code()->cfg();
        return std::make_unique<live_range::Chains>(cfg);
      }),
      m_immediate_reaching_defs_environments([this, method]() {
        auto& cfg = method->get_code()->cfg();
        const auto& reaching_defs_fp_iter = m_immediate_chains->get_fp_iter();
        ReachingDefsEnvironments res;
        for (auto* block : cfg.blocks()) {
          auto env = reaching_defs_fp_iter.get_entry_state_at(block);
          for (auto& mie : InstructionIterable(block)) {
            res[mie.insn] = env;
            reaching_defs_fp_iter.analyze_instruction(mie.insn, &env);
          }
        }
        return res;
      }),
      m_immediate_def_uses([this]() {
        return std::make_unique<live_range::DefUseChains>(
            m_immediate_chains->get_def_use_chains());
      }),
      m_type_environments([method]() {
        auto& cfg = method->get_code()->cfg();
        type_inference::TypeInference type_inference(cfg);
        type_inference.run(method);
        // Move, not copy: `type_inference` is a local that dies with this
        // lambda, and the map holds one environment per instruction.
        return std::move(type_inference.get_type_environments());
      }),
      m_constant_uses([method]() {
        auto& cfg = method->get_code()->cfg();
        return std::make_unique<constant_uses::ConstantUses>(cfg, method);
      }) {}

art::Value OutlinerTypeAnalysis::value_of_assignments(
    const UnorderedSet<const IRInstruction*>& assignments,
    const std::optional<art::Value>& incoming,
    const Membership& candidate) {
  auto defs = get_defs(assignments);
  if (!defs) {
    return incoming ? *incoming : art::Value::unknown();
  }
  return value_of_defs(*defs, incoming ? *incoming : art::Value(), candidate);
}

art::Value OutlinerTypeAnalysis::value_at(const IRInstruction* anchor,
                                          reg_t reg) {
  const auto& env = m_type_environments->at(anchor);
  switch (env.get_type(reg).element()) {
  case IRType::BOTTOM:
  case IRType::ZERO:
  case IRType::CONST:
  case IRType::CONST1:
  case IRType::SCALAR:
  case IRType::SCALAR1:
  case IRType::INT: {
    // Type inference tells neither constants nor `boolean`, `byte`, `short`,
    // `char` and `int` apart; go back to the definitions.
    auto defs = m_reaching_defs_environments->at(anchor).get(reg);
    if (defs.is_bottom() || defs.is_top()) {
      return art::Value::unknown();
    }
    return value_of_defs(UnorderedSet<const IRInstruction*>(
                             defs.elements().begin(), defs.elements().end()),
                         art::Value(), /* candidate */ {});
  }
  case IRType::REFERENCE: {
    auto dex_type = env.get_dex_type(reg);
    return art::Value::of_type(dex_type ? *dex_type : nullptr);
  }
  case IRType::FLOAT:
    return art::Value::of_type(type::_float());
  case IRType::LONG1:
    return art::Value::of_type(type::_long());
  case IRType::DOUBLE1:
    return art::Value::of_type(type::_double());
  case IRType::CONST2:
  case IRType::DOUBLE2:
  case IRType::LONG2:
  case IRType::SCALAR2:
  case IRType::TOP:
  default:
    // shouldn't happen for any input, but we don't need to fight that here
    return art::Value::unknown();
  }
}

art::Demand OutlinerTypeAnalysis::demand_of_use(IRInstruction* use,
                                                src_index_t src_index) {
  return art::Demand::of_use(get_type_demand(use, src_index));
}

art::Demand OutlinerTypeAnalysis::demand_in_candidate(
    const PartialCandidate& pc,
    reg_t reg,
    const std::optional<std::pair<reg_t, const DexType*>>& result) {
  // The candidate is a tree of instruction sequences, not closed under
  // control-flow predecessors: a block it covers may also be entered from
  // outside. So walk it in program order, tracking which registers still hold
  // the value on each path, and which of those hold it through a followed use.
  art::Demand demand;
  art::Demand followed_demand;
  std::function<void(const PartialCandidateNode&, UnorderedSet<reg_t>,
                     UnorderedSet<reg_t>)>
      walk;
  walk = [&](const PartialCandidateNode& pcn, UnorderedSet<reg_t> tracked,
             UnorderedSet<reg_t> followed) {
    auto demand_of = [&](reg_t r) -> art::Demand& {
      return followed.count(r) != 0u ? followed_demand : demand;
    };
    for (size_t insn_idx = 0; insn_idx < pcn.insns.size() && !tracked.empty();
         insn_idx++) {
      bool track_dest{false};
      bool dest_followed{false};
      auto* insn = pcn.insns.at(insn_idx);
      for (size_t i = 0; i < insn->srcs_size(); i++) {
        if (tracked.count(insn->src(i)) == 0u) {
          continue;
        }
        if (opcode::is_a_move(insn->opcode())) {
          track_dest = true;
          dest_followed = followed.count(insn->src(i)) != 0u;
          continue;
        }
        demand_of(insn->src(i)).meet_with(demand_of_use(insn, i));
        if (follows_boolean(insn)) {
          track_dest = true;
          dest_followed = true;
        }
      }
      always_assert(!track_dest || insn->has_dest());
      if (insn->has_dest()) {
        if (track_dest) {
          tracked.insert(insn->dest());
        } else {
          tracked.erase(insn->dest());
        }
        if (track_dest && dest_followed) {
          followed.insert(insn->dest());
        } else {
          followed.erase(insn->dest());
        }
        if (insn->dest_is_wide()) {
          tracked.erase(insn->dest() + 1);
          followed.erase(insn->dest() + 1);
        }
      }
    }
    if (pcn.succs.empty() && result && tracked.count(result->first) != 0u) {
      demand_of(result->first).meet_with(art::Demand::of_use(result->second));
    }
    for (const auto& p : pcn.succs) {
      walk(*p.second, tracked, followed);
    }
  };
  walk(pc.root, {reg}, {});
  demand.meet_with(followed_demand.through_bitwise());
  return demand;
}

art::Demand OutlinerTypeAnalysis::demand_of_uses(
    const sparta::PatriciaTreeSet<IRInstruction*>& seeds,
    const Membership& scope) {
  // Each def is queued with whether its value reached it through a followed
  // use. A def reached both ways is walked once per way.
  art::Demand demand;
  art::Demand followed_demand;
  std::queue<std::pair<IRInstruction*, bool>> workqueue;
  UnorderedSet<IRInstruction*> visited;
  UnorderedSet<IRInstruction*> visited_followed;
  for (auto* def : seeds) {
    workqueue.emplace(def, /* followed */ false);
  }
  while (!workqueue.empty()) {
    auto [def, followed] = workqueue.front();
    workqueue.pop();
    if (!(followed ? visited_followed : visited).insert(def).second) {
      continue;
    }
    // `find`, not `operator[]`: this is a const query over a def-use map shared
    // across the whole method, and `operator[]` would default-insert an empty
    // entry for any def that has no uses.
    auto uses_it = m_immediate_def_uses->find(def);
    if (uses_it == m_immediate_def_uses->end()) {
      continue;
    }
    for (const auto& use : UnorderedIterable(uses_it->second)) {
      if (!scope(use.insn)) {
        continue;
      }
      if (opcode::is_a_move(use.insn->opcode())) {
        workqueue.emplace(use.insn, followed);
        continue;
      }
      (followed ? followed_demand : demand)
          .meet_with(demand_of_use(use.insn, use.src_index));
      if (follows_boolean(use.insn)) {
        workqueue.emplace(use.insn, /* followed */ true);
      }
    }
  }
  demand.meet_with(followed_demand.through_bitwise());
  return demand;
}

sparta::PatriciaTreeSet<IRInstruction*> OutlinerTypeAnalysis::defs_at(
    const IRInstruction* anchor, reg_t reg) {
  return m_reaching_defs_environments->at(anchor).get(reg).elements();
}

sparta::PatriciaTreeSet<IRInstruction*> OutlinerTypeAnalysis::immediate_defs_at(
    const IRInstruction* anchor, reg_t reg) {
  return m_immediate_reaching_defs_environments->at(anchor).get(reg).elements();
}

size_t OutlinerTypeAnalysis::get_load_param_index(
    const IRInstruction* load_param_insn) {
  always_assert(opcode::is_a_load_param(load_param_insn->opcode()));
  auto& cfg = m_method->get_code()->cfg();
  auto param_insns = cfg.get_param_instructions();
  auto it = std::find_if(param_insns.begin(), param_insns.end(),
                         [load_param_insn](MethodItemEntry& mie) {
                           return mie.insn == load_param_insn;
                         });
  always_assert(it != param_insns.end());
  return std::distance(param_insns.begin(), it);
}

const DexType* OutlinerTypeAnalysis::get_result_type_helper(
    const IRInstruction* insn) {
  switch (insn->opcode()) {
  case OPCODE_CONST:
  case OPCODE_CONST_WIDE:
  case OPCODE_AND_INT:
  case OPCODE_OR_INT:
  case OPCODE_XOR_INT:
  case OPCODE_AND_INT_LIT:
  case OPCODE_OR_INT_LIT:
  case OPCODE_XOR_INT_LIT:
  case IOPCODE_UNREACHABLE:
    // These (must) get a special handling by caller
    not_reached();

  case IOPCODE_MOVE_RESULT_PSEUDO:
  case OPCODE_MOVE_RESULT:
  case IOPCODE_MOVE_RESULT_PSEUDO_OBJECT:
  case OPCODE_MOVE_RESULT_OBJECT:
  case IOPCODE_MOVE_RESULT_PSEUDO_WIDE:
  case OPCODE_MOVE_RESULT_WIDE:
  case OPCODE_MOVE:
  case OPCODE_MOVE_WIDE:
  case OPCODE_MOVE_OBJECT:
    // Not supported here
    not_reached();

  case IOPCODE_LOAD_PARAM:
  case IOPCODE_LOAD_PARAM_OBJECT:
  case IOPCODE_LOAD_PARAM_WIDE: {
    auto arg_idx = get_load_param_index(insn);
    if (!is_static(m_method) && arg_idx-- == 0) {
      return m_method->get_class();
    }
    const auto* arg_types = m_method->get_proto()->get_args();
    return arg_types->at(arg_idx);
  }

  case OPCODE_FILL_ARRAY_DATA:
  case OPCODE_GOTO:
  case OPCODE_NOP:
  case OPCODE_RETURN_VOID:
  case OPCODE_RETURN:
  case OPCODE_RETURN_WIDE:
  case OPCODE_RETURN_OBJECT:
  case OPCODE_MONITOR_ENTER:
  case OPCODE_MONITOR_EXIT:
  case OPCODE_IF_EQ:
  case OPCODE_IF_NE:
  case OPCODE_IF_EQZ:
  case OPCODE_IF_NEZ:
  case OPCODE_IF_LTZ:
  case OPCODE_IF_GEZ:
  case OPCODE_IF_GTZ:
  case OPCODE_IF_LEZ:
  case OPCODE_IF_LT:
  case OPCODE_IF_GE:
  case OPCODE_IF_GT:
  case OPCODE_IF_LE:
  case OPCODE_SWITCH:
  case OPCODE_APUT:
  case OPCODE_APUT_BOOLEAN:
  case OPCODE_APUT_BYTE:
  case OPCODE_APUT_CHAR:
  case OPCODE_APUT_SHORT:
  case OPCODE_APUT_WIDE:
  case OPCODE_APUT_OBJECT:
  case OPCODE_IPUT:
  case OPCODE_IPUT_BOOLEAN:
  case OPCODE_IPUT_BYTE:
  case OPCODE_IPUT_CHAR:
  case OPCODE_IPUT_SHORT:
  case OPCODE_IPUT_WIDE:
  case OPCODE_IPUT_OBJECT:
  case OPCODE_SPUT:
  case OPCODE_SPUT_BOOLEAN:
  case OPCODE_SPUT_BYTE:
  case OPCODE_SPUT_CHAR:
  case OPCODE_SPUT_SHORT:
  case OPCODE_SPUT_WIDE:
  case OPCODE_SPUT_OBJECT:
  case OPCODE_THROW:
  case IOPCODE_INIT_CLASS:
  case IOPCODE_INJECTION_ID:
  case IOPCODE_WRITE_BARRIER:
    not_reached();

  case OPCODE_MOVE_EXCEPTION:
    return type::java_lang_Throwable();

  case OPCODE_NEG_INT:
  case OPCODE_NOT_INT:
  case OPCODE_ADD_INT:
  case OPCODE_SUB_INT:
  case OPCODE_MUL_INT:
  case OPCODE_SHL_INT:
  case OPCODE_SHR_INT:
  case OPCODE_USHR_INT:
  case OPCODE_ADD_INT_LIT:
  case OPCODE_RSUB_INT_LIT:
  case OPCODE_MUL_INT_LIT:
  case OPCODE_SHL_INT_LIT:
  case OPCODE_SHR_INT_LIT:
  case OPCODE_USHR_INT_LIT:
  case OPCODE_FLOAT_TO_INT:
  case OPCODE_DOUBLE_TO_INT:
  case OPCODE_LONG_TO_INT:
  case IOPCODE_R_CONST:
    return type::_int();

  case OPCODE_INT_TO_BYTE:
    return type::_byte();
  case OPCODE_INT_TO_CHAR:
    return type::_char();
  case OPCODE_INT_TO_SHORT:
    return type::_short();
  case OPCODE_INT_TO_LONG:
  case OPCODE_FLOAT_TO_LONG:
  case OPCODE_DOUBLE_TO_LONG:
  case OPCODE_NEG_LONG:
  case OPCODE_NOT_LONG:
  case OPCODE_ADD_LONG:
  case OPCODE_SUB_LONG:
  case OPCODE_MUL_LONG:
  case OPCODE_AND_LONG:
  case OPCODE_OR_LONG:
  case OPCODE_XOR_LONG:
  case OPCODE_SHL_LONG:
  case OPCODE_SHR_LONG:
  case OPCODE_USHR_LONG:
    return type::_long();
  case OPCODE_INT_TO_FLOAT:
  case OPCODE_NEG_FLOAT:
  case OPCODE_ADD_FLOAT:
  case OPCODE_SUB_FLOAT:
  case OPCODE_MUL_FLOAT:
  case OPCODE_DIV_FLOAT:
  case OPCODE_REM_FLOAT:
  case OPCODE_DOUBLE_TO_FLOAT:
  case OPCODE_LONG_TO_FLOAT:
    return type::_float();
  case OPCODE_INT_TO_DOUBLE:
  case OPCODE_FLOAT_TO_DOUBLE:
  case OPCODE_NEG_DOUBLE:
  case OPCODE_ADD_DOUBLE:
  case OPCODE_SUB_DOUBLE:
  case OPCODE_MUL_DOUBLE:
  case OPCODE_DIV_DOUBLE:
  case OPCODE_REM_DOUBLE:
  case OPCODE_LONG_TO_DOUBLE:
    return type::_double();

  case OPCODE_CMPL_FLOAT:
  case OPCODE_CMPG_FLOAT:
  case OPCODE_CMPL_DOUBLE:
  case OPCODE_CMPG_DOUBLE:
  case OPCODE_CMP_LONG:
    return type::_int();

  case OPCODE_CONST_STRING:
    return type::java_lang_String();
  case OPCODE_CONST_CLASS:
    return type::java_lang_Class();
  case OPCODE_NEW_INSTANCE:
  case OPCODE_NEW_ARRAY:
  case OPCODE_FILLED_NEW_ARRAY:
  case OPCODE_CHECK_CAST:
    return insn->get_type();
  case OPCODE_SGET:
  case OPCODE_SGET_BOOLEAN:
  case OPCODE_SGET_BYTE:
  case OPCODE_SGET_CHAR:
  case OPCODE_SGET_SHORT:
  case OPCODE_SGET_WIDE:
  case OPCODE_SGET_OBJECT:
  case OPCODE_IGET:
  case OPCODE_IGET_BOOLEAN:
  case OPCODE_IGET_BYTE:
  case OPCODE_IGET_CHAR:
  case OPCODE_IGET_SHORT:
  case OPCODE_IGET_WIDE:
  case OPCODE_IGET_OBJECT:
    return insn->get_field()->get_type();
  case OPCODE_ARRAY_LENGTH:
    return type::_int();
  case OPCODE_INSTANCE_OF:
  case OPCODE_AGET_BOOLEAN:
    return type::_boolean();
  case OPCODE_AGET_BYTE:
    return type::_byte();
  case OPCODE_AGET_CHAR:
    return type::_char();
  case OPCODE_AGET_SHORT:
    return type::_short();
  case OPCODE_AGET:
  case OPCODE_AGET_WIDE:
  case OPCODE_AGET_OBJECT: {
    auto& env = m_type_environments->at(insn);
    auto dex_type = env.get_dex_type(insn->src(0));
    return (dex_type && type::is_array(*dex_type))
               ? type::make_array_component_type(*dex_type)
               : nullptr;
  }
  case OPCODE_INVOKE_VIRTUAL:
  case OPCODE_INVOKE_SUPER:
  case OPCODE_INVOKE_DIRECT:
  case OPCODE_INVOKE_STATIC:
  case OPCODE_INVOKE_INTERFACE:
    return insn->get_method()->get_proto()->get_rtype();

  case OPCODE_INVOKE_CUSTOM:
  case OPCODE_INVOKE_POLYMORPHIC:
  case OPCODE_CONST_METHOD_HANDLE:
  case OPCODE_CONST_METHOD_TYPE:
    // These opcodes are legal input dex that the analysis does not model.
    // `value_of_def` types every definition that is neither a constant nor a
    // bitwise operation here, so they reach this switch. `nullptr` means
    // "undeterminable", and every caller then drops the candidate.
    return nullptr;

  case OPCODE_DIV_INT:
  case OPCODE_REM_INT:
  case OPCODE_DIV_INT_LIT:
  case OPCODE_REM_INT_LIT:
    return type::_int();
  case OPCODE_DIV_LONG:
  case OPCODE_REM_LONG:
    return type::_long();
  }
}

// The demand a field or array put places on the value it stores. ART checks a
// primitive put by category only: any integral value may be stored into a
// `boolean`, `byte`, `char` or `short` slot. So an integral slot demands `int`,
// whatever its declared type. An invocation argument, in contrast, must be
// assignable to the parameter type. Taking the slot type as the demand would
// therefore turn a value that only ever reaches such a put into an outlined
// parameter narrower than what the caller holds.
static const DexType* primitive_put_value_demand(const DexType* slot_type) {
  return type::is_integral(slot_type) ? type::_int() : slot_type;
}

const DexType* OutlinerTypeAnalysis::get_if_insn_type_demand(
    IRInstruction* insn) {
  always_assert(opcode::is_a_conditional_branch(insn->opcode()));
  auto& env = m_type_environments->at(insn);
  for (size_t src_index = 0; src_index < insn->srcs_size(); src_index++) {
    auto t = env.get_type(insn->src(src_index));
    if (t.element() == IRType::REFERENCE) {
      return type::java_lang_Object();
    } else if (t.element() == IRType::FLOAT) {
      return type::_float();
    } else if (t.element() == IRType::INT) {
      return type::_int();
    }
  }
  return nullptr;
}

const DexType* OutlinerTypeAnalysis::get_type_demand(IRInstruction* insn,
                                                     size_t src_index) {
  always_assert(src_index < insn->srcs_size());
  switch (insn->opcode()) {
  case OPCODE_GOTO:
  case IOPCODE_LOAD_PARAM:
  case IOPCODE_LOAD_PARAM_OBJECT:
  case IOPCODE_LOAD_PARAM_WIDE:
  case OPCODE_NOP:
  case IOPCODE_MOVE_RESULT_PSEUDO:
  case OPCODE_MOVE_RESULT:
  case IOPCODE_MOVE_RESULT_PSEUDO_OBJECT:
  case OPCODE_MOVE_RESULT_OBJECT:
  case IOPCODE_MOVE_RESULT_PSEUDO_WIDE:
  case OPCODE_MOVE_RESULT_WIDE:
  case OPCODE_MOVE_EXCEPTION:
  case OPCODE_RETURN_VOID:
  case OPCODE_CONST:
  case OPCODE_CONST_WIDE:
  case OPCODE_CONST_STRING:
  case OPCODE_CONST_CLASS:
  case OPCODE_NEW_INSTANCE:
  case OPCODE_SGET:
  case OPCODE_SGET_BOOLEAN:
  case OPCODE_SGET_BYTE:
  case OPCODE_SGET_CHAR:
  case OPCODE_SGET_SHORT:
  case OPCODE_SGET_WIDE:
  case OPCODE_SGET_OBJECT:
  case IOPCODE_INIT_CLASS:
  case IOPCODE_INJECTION_ID:
  case IOPCODE_UNREACHABLE:
  case IOPCODE_WRITE_BARRIER:
    not_reached();

  case OPCODE_RETURN:
  case OPCODE_RETURN_WIDE:
  case OPCODE_RETURN_OBJECT:
    always_assert(src_index == 0);
    return m_method->get_proto()->get_rtype();

  case OPCODE_MOVE:
  case OPCODE_MOVE_WIDE:
  case OPCODE_MOVE_OBJECT:
    // Handled by caller
    not_reached();

  case OPCODE_MONITOR_ENTER:
  case OPCODE_MONITOR_EXIT:
  case OPCODE_CHECK_CAST:
  case OPCODE_INSTANCE_OF:
    always_assert(src_index == 0);
    return type::java_lang_Object();

  case OPCODE_ARRAY_LENGTH:
  case OPCODE_FILL_ARRAY_DATA: {
    always_assert(src_index == 0);
    auto& env = m_type_environments->at(insn);
    auto dex_type = env.get_dex_type(insn->src(0));
    return dex_type ? *dex_type : nullptr;
  }

  case OPCODE_THROW:
    always_assert(src_index == 0);
    return type::java_lang_Throwable();

  case OPCODE_IGET:
  case OPCODE_IGET_BOOLEAN:
  case OPCODE_IGET_BYTE:
  case OPCODE_IGET_CHAR:
  case OPCODE_IGET_SHORT:
  case OPCODE_IGET_WIDE:
  case OPCODE_IGET_OBJECT:
    always_assert(src_index == 0);
    return insn->get_field()->get_class();

  case OPCODE_IF_EQ:
  case OPCODE_IF_NE:
    always_assert(src_index < 2);
    // Could be int or object
    return get_if_insn_type_demand(insn);

  case OPCODE_IF_EQZ:
  case OPCODE_IF_NEZ:
  case OPCODE_IF_LTZ:
  case OPCODE_IF_GEZ:
  case OPCODE_IF_GTZ:
  case OPCODE_IF_LEZ:
    always_assert(src_index == 0);
    // Could be int or object
    return get_if_insn_type_demand(insn);

  case OPCODE_IF_LT:
  case OPCODE_IF_GE:
  case OPCODE_IF_GT:
  case OPCODE_IF_LE:
  case OPCODE_NEW_ARRAY:
  case OPCODE_SWITCH:
  case OPCODE_NEG_INT:
  case OPCODE_NOT_INT:
  case OPCODE_INT_TO_BYTE:
  case OPCODE_INT_TO_CHAR:
  case OPCODE_INT_TO_SHORT:
  case OPCODE_INT_TO_LONG:
  case OPCODE_INT_TO_FLOAT:
  case OPCODE_INT_TO_DOUBLE:
  case OPCODE_ADD_INT:
  case OPCODE_SUB_INT:
  case OPCODE_MUL_INT:
  case OPCODE_SHL_INT:
  case OPCODE_SHR_INT:
  case OPCODE_USHR_INT:
  case OPCODE_DIV_INT:
  case OPCODE_REM_INT:
  case OPCODE_ADD_INT_LIT:
  case OPCODE_RSUB_INT_LIT:
  case OPCODE_MUL_INT_LIT:
  case OPCODE_SHL_INT_LIT:
  case OPCODE_SHR_INT_LIT:
  case OPCODE_USHR_INT_LIT:
  case OPCODE_DIV_INT_LIT:
  case OPCODE_REM_INT_LIT:
    always_assert(src_index < 2);
    return type::_int();

  case OPCODE_AND_INT:
  case OPCODE_OR_INT:
  case OPCODE_XOR_INT:
  case OPCODE_AND_INT_LIT:
  case OPCODE_OR_INT_LIT:
  case OPCODE_XOR_INT_LIT:
    always_assert(src_index < 2);
    // Note: These opcodes can preserve boolean-ness. The caller of this
    // method needs to track that.
    return type::_int();

  case OPCODE_FILLED_NEW_ARRAY:
    return type::make_array_component_type(insn->get_type());

  case OPCODE_CMPL_FLOAT:
  case OPCODE_CMPG_FLOAT:
  case OPCODE_NEG_FLOAT:
  case OPCODE_FLOAT_TO_INT:
  case OPCODE_FLOAT_TO_LONG:
  case OPCODE_FLOAT_TO_DOUBLE:
  case OPCODE_ADD_FLOAT:
  case OPCODE_SUB_FLOAT:
  case OPCODE_MUL_FLOAT:
  case OPCODE_DIV_FLOAT:
  case OPCODE_REM_FLOAT:
    always_assert(src_index < 2);
    return type::_float();

  case OPCODE_CMPL_DOUBLE:
  case OPCODE_CMPG_DOUBLE:
  case OPCODE_NEG_DOUBLE:
  case OPCODE_DOUBLE_TO_INT:
  case OPCODE_DOUBLE_TO_LONG:
  case OPCODE_DOUBLE_TO_FLOAT:
  case OPCODE_ADD_DOUBLE:
  case OPCODE_SUB_DOUBLE:
  case OPCODE_MUL_DOUBLE:
  case OPCODE_DIV_DOUBLE:
  case OPCODE_REM_DOUBLE:
    always_assert(src_index < 2);
    return type::_double();

  case OPCODE_CMP_LONG:
  case OPCODE_NEG_LONG:
  case OPCODE_NOT_LONG:
  case OPCODE_LONG_TO_INT:
  case OPCODE_LONG_TO_FLOAT:
  case OPCODE_LONG_TO_DOUBLE:
  case OPCODE_ADD_LONG:
  case OPCODE_SUB_LONG:
  case OPCODE_MUL_LONG:
  case OPCODE_AND_LONG:
  case OPCODE_OR_LONG:
  case OPCODE_XOR_LONG:
  case OPCODE_DIV_LONG:
  case OPCODE_REM_LONG:
    always_assert(src_index < 2);
    return type::_long();

  case OPCODE_SHL_LONG:
  case OPCODE_SHR_LONG:
  case OPCODE_USHR_LONG:
    if (src_index == 0) {
      return type::_long();
    }
    always_assert(src_index == 1);
    return type::_int();

  case IOPCODE_R_CONST:
    return type::_int();

  case OPCODE_AGET:
  case OPCODE_AGET_BOOLEAN:
  case OPCODE_AGET_BYTE:
  case OPCODE_AGET_CHAR:
  case OPCODE_AGET_SHORT:
  case OPCODE_AGET_WIDE:
  case OPCODE_AGET_OBJECT:
    if (src_index == 0) {
      auto& env = m_type_environments->at(insn);
      auto dex_type = env.get_dex_type(insn->src(0));
      return dex_type ? *dex_type : nullptr;
    }
    always_assert(src_index == 1);
    return type::_int();

  case OPCODE_APUT:
  case OPCODE_APUT_BOOLEAN:
  case OPCODE_APUT_BYTE:
  case OPCODE_APUT_CHAR:
  case OPCODE_APUT_SHORT:
  case OPCODE_APUT_WIDE:
  case OPCODE_APUT_OBJECT:
    if (src_index == 1) {
      if (insn->opcode() == OPCODE_APUT_OBJECT) {
        return DexType::make_type("[Ljava/lang/Object;");
      }
      auto& env = m_type_environments->at(insn);
      auto dex_type = env.get_dex_type(insn->src(1));
      return dex_type ? *dex_type : nullptr;
    }
    if (src_index == 2) {
      return type::_int();
    }
    always_assert(src_index == 0);
    switch (insn->opcode()) {
    case OPCODE_APUT:
    case OPCODE_APUT_WIDE: {
      auto& env = m_type_environments->at(insn);
      auto dex_type = env.get_dex_type(insn->src(1));
      return (dex_type && type::is_array(*dex_type))
                 ? primitive_put_value_demand(
                       type::make_array_component_type(*dex_type))
                 : nullptr;
    }
    case OPCODE_APUT_BOOLEAN:
    case OPCODE_APUT_BYTE:
    case OPCODE_APUT_CHAR:
    case OPCODE_APUT_SHORT: {
      // Into an array, ART checks the value by category only
      // (`primitive_put_value_demand`). But when ART types the array operand
      // as null, it checks the value strictly against the instruction's own
      // type (`VerifyAPut` in `method_verifier.cc`, android-6.0.0_r1 and
      // later). A known array type proves that ART sees an array: the operand
      // comes from a definition of an array, and ART merges a null with an
      // array into the array. Without a known array type, ART may still see an
      // array that Redex does not, for example after an `instance-of` test. So
      // only a proven null demands the instruction's type.
      auto& env = m_type_environments->at(insn);
      auto dex_type = env.get_dex_type(insn->src(1));
      if (dex_type && type::is_array(*dex_type)) {
        return type::_int();
      }
      if (!is_null_to_art(insn, insn->src(1))) {
        return nullptr;
      }
      switch (insn->opcode()) {
      case OPCODE_APUT_BOOLEAN:
        return type::_boolean();
      case OPCODE_APUT_BYTE:
        return type::_byte();
      case OPCODE_APUT_CHAR:
        return type::_char();
      default:
        return type::_short();
      }
    }
    case OPCODE_APUT_OBJECT:
      // There seems to be very little static verification for this
      // instruction, as most is deferred to runtime.
      // https://android.googlesource.com/platform/dalvik/+/android-cts-4.4_r4/vm/analysis/CodeVerify.cpp#186
      // So, we can just get away with the following:
      return type::java_lang_Object();
    default:
      not_reached();
    }

  case OPCODE_IPUT:
  case OPCODE_IPUT_BOOLEAN:
  case OPCODE_IPUT_BYTE:
  case OPCODE_IPUT_CHAR:
  case OPCODE_IPUT_SHORT:
  case OPCODE_IPUT_WIDE:
  case OPCODE_IPUT_OBJECT:
    if (src_index == 1) {
      return insn->get_field()->get_class();
    }
    always_assert(src_index == 0);
    return primitive_put_value_demand(insn->get_field()->get_type());

  case OPCODE_SPUT:
  case OPCODE_SPUT_BOOLEAN:
  case OPCODE_SPUT_BYTE:
  case OPCODE_SPUT_CHAR:
  case OPCODE_SPUT_SHORT:
  case OPCODE_SPUT_WIDE:
  case OPCODE_SPUT_OBJECT:
    always_assert(src_index == 0);
    return primitive_put_value_demand(insn->get_field()->get_type());

  case OPCODE_INVOKE_VIRTUAL:
  case OPCODE_INVOKE_SUPER:
  case OPCODE_INVOKE_DIRECT:
  case OPCODE_INVOKE_STATIC:
  case OPCODE_INVOKE_INTERFACE: {
    DexMethodRef* dex_method = insn->get_method();
    const auto* arg_types = dex_method->get_proto()->get_args();
    size_t expected_args =
        (insn->opcode() != OPCODE_INVOKE_STATIC ? 1 : 0) + arg_types->size();
    always_assert(insn->srcs_size() == expected_args);

    if (insn->opcode() != OPCODE_INVOKE_STATIC) {
      // The first argument is a reference to the object instance on which the
      // method is invoked.
      if (src_index-- == 0) {
        return dex_method->get_class();
      }
    }
    return arg_types->at(src_index);
  }
  case OPCODE_INVOKE_CUSTOM:
  case OPCODE_INVOKE_POLYMORPHIC:
    // The argument demand of a call site or a polymorphic signature is not
    // modelled. Like the producers in `get_result_type_helper`, these come from
    // the input dex, so the answer is "undeterminable" rather than an abort:
    // the use's demand is then unknown, and each caller falls back to the
    // value's type or refuses the candidate.
    return nullptr;
  case OPCODE_CONST_METHOD_HANDLE:
  case OPCODE_CONST_METHOD_TYPE:
    not_reached_log(
        "Unsupported instruction {%s} in "
        "get_type_demand\n",
        SHOW(insn));
  }
}

std::optional<UnorderedSet<const IRInstruction*>>
OutlinerTypeAnalysis::get_defs(
    const UnorderedSet<const IRInstruction*>& insns) {
  UnorderedSet<const IRInstruction*> res;
  for (const auto* insn : UnorderedIterable(insns)) {
    always_assert(insn->has_dest());
    if (opcode::is_a_move(insn->opcode()) ||
        opcode::is_move_result_any(insn->opcode())) {
      auto reg = insn->srcs_size() != 0u ? insn->src(0) : RESULT_REGISTER;
      auto defs = m_reaching_defs_environments->at(insn).get(reg);
      if (defs.is_bottom() || defs.is_top()) {
        return std::nullopt;
      }
      res.insert(defs.elements().begin(), defs.elements().end());
      continue;
    }
    res.insert(insn);
  }
  return res;
}

const DexType* OutlinerTypeAnalysis::get_const_insns_type_demand(
    const Membership& candidate,
    const UnorderedSet<const IRInstruction*>& const_insns) {
  always_assert(!const_insns.empty());
  // `value_of_defs` classifies `IOPCODE_UNREACHABLE` (a synthetic undefined
  // value) separately and never routes it here: it carries no literal, so both
  // the constant-uses analysis and the literal-range checks below would assert
  // on it. Only real `const`/`const-wide` defs reach this point.
  // The integral types that hold the value of every constant in `const_insns`.
  auto constants_value = [&const_insns]() {
    std::optional<IntegralType> value;
    for (const auto* insn : UnorderedIterable(const_insns)) {
      value = IntegralType::join(value,
                                 IntegralType::constant(insn->get_literal()));
    }
    always_assert(value.has_value());
    return *value;
  };
  // 1. Let's see if we can get something out of the constant-uses analysis.
  constant_uses::TypeDemand type_demand{constant_uses::TypeDemand::None};
  for (const auto* insn : UnorderedIterable(const_insns)) {
    type_demand =
        (constant_uses::TypeDemand)(type_demand &
                                    m_constant_uses->get_constant_type_demand(
                                        const_cast<IRInstruction*>(insn)));
    if (type_demand == constant_uses::TypeDemand::Error) {
      return nullptr;
    }
  }
  if ((type_demand & constant_uses::TypeDemand::Object) != 0) {
    always_assert(unordered_none_of(const_insns, [](const IRInstruction* insn) {
      return insn->get_literal() != 0;
    }));
  } else if ((type_demand & constant_uses::TypeDemand::Long) != 0) {
    return type::_long();
  } else if ((type_demand & constant_uses::TypeDemand::Float) != 0) {
    return type::_float();
  } else if ((type_demand & constant_uses::TypeDemand::Double) != 0) {
    return type::_double();
  } else {
    always_assert(type_demand == constant_uses::TypeDemand::Int);
    const auto value = constants_value();
    if (value.held_by(type::_boolean())) {
      return type::_boolean();
    } else {
      const bool short_holds = value.held_by(type::_short());
      const bool char_holds = value.held_by(type::_char());
      if (!short_holds && !char_holds) {
        return type::_int();
      } else if (!short_holds) {
        return type::_char();
      } else if (!char_holds) {
        return type::_short();
      }
    }
  }

  // No, so...
  // 2. Let's go over all constant-uses, and use our own judgement.
  art::Demand demand;
  bool not_object{false};
  // Both scan all of `const_insns`, which does not change in the loop below, so
  // each is worth computing at most once. Lazily, because most opcodes reach
  // neither: an eager pair of scans would charge every caller for work the
  // switch below usually never asks for. Only a zero is also a null.
  Lazy<bool> all_boolean(
      [&] { return constants_value().held_by(type::_boolean()); });
  Lazy<bool> any_nonzero([&const_insns] {
    return unordered_any_of(const_insns, [](const IRInstruction* insn) {
      return insn->get_literal() != 0;
    });
  });
  for (const auto* insn : UnorderedIterable(const_insns)) {
    for (const auto& p :
         m_constant_uses->get_constant_uses(const_cast<IRInstruction*>(insn))) {
      if (candidate && candidate(p.first)) {
        continue;
      }
      if (is_bitwise(p.first->opcode())) {
        demand.meet_with(art::Demand::of_use(*all_boolean ? type::_boolean()
                                                          : type::_int()));
        continue;
      }
      switch (p.first->opcode()) {
      case OPCODE_MOVE:
        not_object = true;
        break;
      case OPCODE_MOVE_WIDE:
        break;
      case OPCODE_MOVE_OBJECT:
        demand.meet_with(art::Demand::of_use(type::java_lang_Object()));
        break;
      case OPCODE_IF_EQ:
      case OPCODE_IF_NE:
      case OPCODE_IF_EQZ:
      case OPCODE_IF_NEZ:
      case OPCODE_IF_LTZ:
      case OPCODE_IF_GEZ:
      case OPCODE_IF_GTZ:
      case OPCODE_IF_LEZ:
        // Could be int or object
        if (*any_nonzero) {
          demand.meet_with(art::Demand::of_use(type::_int()));
          break;
        }
        [[fallthrough]];
      default:
        demand.meet_with(demand_of_use(p.first, p.second));
        break;
      }
    }
  }
  if (demand.is_none()) {
    // A constant without (meaningful) use? Oh well. Dead code!
    return (*unordered_any(const_insns))->dest_is_wide() ? type::_long()
                                                         : type::_int();
  }
  const auto* narrowed_type_demand = demand.widest();
  if ((narrowed_type_demand != nullptr) &&
      type::is_object(narrowed_type_demand) && not_object) {
    return nullptr;
  }
  return narrowed_type_demand;
}

bool OutlinerTypeAnalysis::is_null_to_art(const IRInstruction* insn,
                                          reg_t reg) {
  // ART types a `const 0` as null, and an `aget-object` from a null array too
  // (`VerifyAGet` in `method_verifier.cc`, android-5.0.0_r1 and
  // android-16.0.0_r1).
  std::vector<std::pair<const IRInstruction*, reg_t>> worklist{{insn, reg}};
  UnorderedSet<const IRInstruction*> visited;
  bool defined = false;
  while (!worklist.empty()) {
    auto [use, src] = worklist.back();
    worklist.pop_back();
    const auto& defs = m_reaching_defs_environments->at(use).get(src);
    if (defs.is_bottom() || defs.is_top()) {
      return false;
    }
    for (const auto* def : defs.elements()) {
      if (def->opcode() == IOPCODE_UNREACHABLE || !visited.insert(def).second) {
        continue;
      }
      defined = true;
      if (def->opcode() == OPCODE_CONST && def->get_literal() == 0) {
        continue;
      }
      if (def->opcode() == OPCODE_AGET_OBJECT) {
        worklist.emplace_back(def, def->src(0));
        continue;
      }
      return false;
    }
  }
  return defined;
}

art::Value OutlinerTypeAnalysis::value_of_defs(
    const UnorderedSet<const IRInstruction*>& defs,
    art::Value value,
    const Membership& candidate) {
  UnorderedSet<const IRInstruction*> const_insns;
  for (const auto* def : UnorderedIterable(defs)) {
    if (def->opcode() == OPCODE_CONST || def->opcode() == OPCODE_CONST_WIDE) {
      const_insns.insert(def);
    }
    value.join_with(value_of_def(def));
  }
  if (value.is_constant()) {
    // Constants alone give a register no type; their uses do.
    return art::Value::of_type(
        get_const_insns_type_demand(candidate, const_insns));
  }
  return value;
}

art::Value OutlinerTypeAnalysis::value_of_def(const IRInstruction* def) {
  always_assert(!opcode::is_a_move(def->opcode()) &&
                !opcode::is_move_result_any(def->opcode()));
  switch (def->opcode()) {
  case IOPCODE_UNREACHABLE:
    // A synthetic undefined value contributes nothing.
    return art::Value();
  case OPCODE_CONST:
  case OPCODE_CONST_WIDE:
    return art::Value::constant(def);
  default:
    if (is_bitwise(def->opcode())) {
      auto boolean = get_bitwise_booleanness(def);
      if (!boolean) {
        return art::Value::unknown();
      }
      return art::Value::of_type(*boolean ? type::_boolean() : type::_int());
    }
    return art::Value::of_type(get_result_type_helper(def));
  }
}

std::optional<bool> OutlinerTypeAnalysis::get_bitwise_booleanness(
    const IRInstruction* bitwise) {
  if (auto it = m_bitwise_booleanness.find(bitwise);
      it != m_bitwise_booleanness.end()) {
    return it->second;
  }
  // ART types the result boolean when every operand is boolean, and int
  // otherwise. An operand can itself be a bitwise operation, and such
  // operations can share operands and form cycles. A recursion would visit a
  // shared operand once per path to it, so the answer is a fixpoint over the
  // graph of bitwise operations reachable from `bitwise`. Each operation
  // starts out boolean. A literal or an operand can make it int or unknown,
  // and that change propagates to the operations that use it. A cycle that
  // nothing else feeds stays boolean, as in ART.
  enum class State : uint8_t { Boolean, Int, Unknown };
  UnorderedMap<const IRInstruction*, State> state;
  UnorderedMap<const IRInstruction*, std::vector<const IRInstruction*>> users;
  std::vector<const IRInstruction*> order;
  std::vector<const IRInstruction*> stack{bitwise};
  state.emplace(bitwise, State::Boolean);
  while (!stack.empty()) {
    const auto* op = stack.back();
    stack.pop_back();
    order.push_back(op);
    if (auto it = m_bitwise_booleanness.find(op);
        it != m_bitwise_booleanness.end()) {
      state.at(op) = !it->second   ? State::Unknown
                     : *it->second ? State::Boolean
                                   : State::Int;
      continue;
    }
    // Not a reference into `state`: the loop below inserts into it.
    auto s = keeps_booleanness(op) ? State::Boolean : State::Int;
    for (auto src : op->srcs()) {
      const auto& defs = m_reaching_defs_environments->at(op).get(src);
      if (defs.is_bottom() || defs.is_top()) {
        s = State::Unknown;
        continue;
      }
      for (const auto* def : defs.elements()) {
        if (def->opcode() == IOPCODE_UNREACHABLE) {
          continue;
        }
        if (is_bitwise(def->opcode())) {
          users[def].push_back(op);
          if (state.emplace(def, State::Boolean).second) {
            stack.push_back(def);
          }
          continue;
        }
        auto v = value_of_def(def).integral();
        if (!v) {
          s = State::Unknown;
        } else if (s == State::Boolean && !v->held_by(type::_boolean())) {
          s = State::Int;
        }
      }
    }
    state.at(op) = s;
  }
  std::vector<const IRInstruction*> worklist;
  for (const auto* op : order) {
    if (state.at(op) != State::Boolean) {
      worklist.push_back(op);
    }
  }
  while (!worklist.empty()) {
    const auto* op = worklist.back();
    worklist.pop_back();
    auto it = users.find(op);
    if (it == users.end()) {
      continue;
    }
    const auto s = state.at(op);
    for (const auto* user : it->second) {
      auto& u = state.at(user);
      if (u < s) {
        u = s;
        worklist.push_back(user);
      }
    }
  }
  for (const auto* op : order) {
    const auto s = state.at(op);
    m_bitwise_booleanness.emplace(
        op, s == State::Unknown ? std::nullopt
                                : std::optional<bool>(s == State::Boolean));
  }
  return m_bitwise_booleanness.at(bitwise);
}

} // namespace outliner_impl
