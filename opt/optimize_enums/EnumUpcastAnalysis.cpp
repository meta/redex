/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "EnumUpcastAnalysis.h"

#include <functional>
#include <memory>
#include <utility>
#include <vector>

#include "Debug.h"
#include "EnumClinitAnalysis.h"
#include "Lazy.h"
#include "LiveRange.h"
#include "Macros.h"
#include "Resolver.h"
#include "Show.h"
#include "Trace.h"
#include "Walkers.h"

namespace {

using namespace optimize_enums;
using namespace ir_analyzer;

// Whether the method references any candidate enum, and therefore must be
// analyzed. This intentionally does NOT skip methods whose candidate enums are
// already rejected: rejection is accumulated concurrently, so gating on it
// makes which method records which rejection reason depend on thread
// scheduling. That does not change which enums are ultimately rejected
// (analyzing a method whose candidates are all already rejected cannot reject a
// fresh enum), but it does make the per-reason stats non-deterministic.
// Analyzing every referencing method yields the complete, order-independent set
// of reasons per enum.
bool need_analyze(const DexMethod* method,
                  const ConcurrentSet<const DexType*>& candidate_enums) {
  const IRCode* code = method->get_code();
  if (code == nullptr) {
    return false;
  }
  std::vector<const DexType*> types;
  method->gather_types(types);
  for (const DexType* t : types) {
    if (type::is_array(t)) {
      t = type::make_array_element_type(t);
    }
    if (candidate_enums.count_unsafe(t) != 0u) {
      return true;
    }
  }
  return false;
}

UnorderedSet<const DexType*> discard_primitives(const EnumTypes& types) {
  UnorderedSet<const DexType*> res;
  for (const auto* type : types.elements()) {
    if (!type::is_primitive(type)) {
      res.insert(type);
    }
  }
  return res;
}

// Boxing replaces a value of the candidate enum, or array of them, `type` with
// an Integer, or an Integer array. Whether `instance-of test` holds changes
// only where the two disagree on it, e.g. for `Number` or `Enum` but not
// `Object`, `Comparable` or `String`.
bool boxing_may_change_instance_of(const DexType* type, const DexType* test) {
  while (type::is_array(type)) {
    if (!type::is_array(test)) {
      // Both arrays are instances of `Object`, `Cloneable` and `Serializable`,
      // and of nothing else that is not an array.
      return false;
    }
    type = type::make_array_component_type(type);
    test = type::make_array_component_type(test);
  }
  if (type::is_primitive(test)) {
    return false;
  }
  auto as_enum = type::is_instance_of_if_known(type, test);
  auto as_integer =
      type::is_instance_of_if_known(type::java_lang_Integer(), test);
  return !as_enum || !as_integer || *as_enum != *as_integer;
}

// Whether a value of `type` may be an Integer, which boxing may make identical
// to a boxed enum constant: for `Object` or `Number`, not for `String` or an
// app class. Any interface may, since the verifier does not check interface
// types, and so may a type Redex has not loaded, which may be an interface.
bool may_be_integer(const DexType* type) {
  const auto* cls = type_class(type);
  return cls == nullptr || is_interface(cls) ||
         type::is_instance_of_if_known(type::java_lang_Integer(), type)
             .value_or(true);
}

bool is_static_field_on_enum_class(const DexFieldRef* fref) {
  const auto* field = fref->as_def();
  if ((field == nullptr) || !is_static(field)) {
    return false;
  }
  auto* container = type_class(field->get_class());
  return (container != nullptr) && is_enum(container);
}

bool is_enum_constant_field(const DexFieldRef* field_ref) {
  return is_static_field_on_enum_class(field_ref) &&
         check_required_access_flags(enum_field_access(),
                                     field_ref->as_def()->get_access());
}

/**
 * Inspect instructions to reject enum class that may be casted to another type.
 */
template <typename RejectFn>
class EnumUpcastDetector {
 public:
  EnumUpcastDetector(const DexMethod* method,
                     Config* config,
                     const RejectFn& reject_fn)
      : m_method(method),
        m_config(config),
        m_candidate_enums(&config->candidate_enums),
        m_reject_fn(reject_fn) {}

  // Pairs of candidates this method compares by identity with each other.
  const std::vector<std::pair<const DexType*, const DexType*>>&
  compared_candidates() const {
    return m_compared_candidates;
  }

  void run(const EnumFixpointIterator& engine,
           const cfg::ControlFlowGraph& cfg) {
    if (m_config->support_kt_19_enum_entries && method::is_clinit(m_method) &&
        m_candidate_enums->count_unsafe(m_method->get_class()) != 0u) {
      m_clinit_chains.emplace(
          [&cfg] { return std::make_unique<live_range::LazyLiveRanges>(cfg); });
    }
    for (const auto& block : cfg.blocks()) {
      EnumTypeEnvironment env = engine.get_entry_state_at(block);
      if (env.is_bottom()) {
        continue;
      }
      for (const auto& mie : InstructionIterable(block)) {
        engine.analyze_instruction(mie.insn, &env);
        if (compares_by_identity(mie.insn)) {
          process_identity_comparison(engine, cfg, block, mie.insn, env);
        }
        process_instruction(mie.insn, &env);
      }
    }
  }

 private:
  /**
   * Process instructions when we reach the fixpoint.
   */
  void process_instruction(const IRInstruction* insn,
                           const EnumTypeEnvironment* env) {
    reject_unless_candidate_defines(insn);
    switch (insn->opcode()) {
    case OPCODE_CHECK_CAST: {
      const auto* type = insn->get_type();
      // Assume the local upcast is safe and we only care about upcasting when
      // the value is escaping.
      if (type::is_enum_array(type)) {
        process_enum_entries_input(insn, 0, env,
                                   UnsafeType::kUsageCastCheckCast);
      } else if (type != OBJECT_TYPE) {
        reject_if_inconsistent(insn, env->get(insn->src(0)), type,
                               UnsafeType::kUsageCastCheckCast);
      }
    } break;
    case OPCODE_CONST_CLASS:
      reject(insn, insn->get_type(), UnsafeType::kUsageUsedAsClassObject);
      break;
    case OPCODE_INSTANCE_OF:
      reject(insn, insn->get_type(), UnsafeType::kUsageUsedInInstanceOf);
      for (const auto* type : env->get(insn->src(0)).elements()) {
        if (is_candidate(type) &&
            boxing_may_change_instance_of(type, insn->get_type())) {
          reject(insn, type, UnsafeType::kUsageUsedInInstanceOf);
        }
      }
      break;
    case OPCODE_INVOKE_CUSTOM:
    case OPCODE_INVOKE_POLYMORPHIC:
      // The call site or method handle decides at run time which code
      // receives the arguments.
      for (size_t i = 0; i < insn->srcs_size(); ++i) {
        reject(insn, env->get(insn->src(i)),
               UnsafeType::kUsagePassedToCallSiteOrMethodHandle);
      }
      reject_linkage_types(insn);
      break;
    case OPCODE_CONST_METHOD_HANDLE:
    case OPCODE_CONST_METHOD_TYPE:
      reject_linkage_types(insn);
      break;
    case OPCODE_MONITOR_ENTER:
    case OPCODE_MONITOR_EXIT:
      reject(insn, env->get(insn->src(0)), UnsafeType::kUsageUsedInMonitor);
      break;
    case OPCODE_INVOKE_INTERFACE:
    case OPCODE_INVOKE_SUPER:
      process_general_invocation(insn, env);
      break;
    case OPCODE_INVOKE_DIRECT:
      process_direct_invocation(insn, env);
      break;
    case OPCODE_INVOKE_STATIC:
      process_static_invocation(insn, env);
      break;
    case OPCODE_INVOKE_VIRTUAL:
      process_virtual_invocation(insn, env);
      break;
    case OPCODE_RETURN_OBJECT:
      process_return_object(insn, env);
      break;
    case OPCODE_APUT_OBJECT:
      process_aput_object(insn, env);
      break;
    case OPCODE_FILLED_NEW_ARRAY:
      process_filled_new_array(insn, env);
      break;
    case OPCODE_IPUT_OBJECT:
      process_isput_object(insn, env);
      reject(insn, insn->get_field()->get_class(),
             UnsafeType::kUsageIFieldSetOutsideInit);
      break;
    case OPCODE_IPUT:
    case OPCODE_IPUT_WIDE:
    case OPCODE_IPUT_BOOLEAN:
    case OPCODE_IPUT_BYTE:
    case OPCODE_IPUT_CHAR:
    case OPCODE_IPUT_SHORT:
      reject(insn, insn->get_field()->get_class(),
             UnsafeType::kUsageIFieldSetOutsideInit);
      break;
    case OPCODE_SGET_OBJECT:
      process_sget_object(insn);
      break;
    case OPCODE_SPUT_OBJECT:
      process_sput_object(insn, env);
      break;
    default:
      break;
    }
  }

  /**
   * Whether `insn` compares its two sources by identity: `if-eq`, `if-ne`, or
   * `Enum.equals(Object)`, which the transformation turns into
   * `Integer.equals(Object)` on a boxed receiver. That compares values, and
   * each constant is boxed to the one cached `Integer` of its ordinal, so it
   * agrees with `==` on the boxed values.
   */
  bool compares_by_identity(const IRInstruction* insn) const {
    if (insn->opcode() == OPCODE_IF_EQ || insn->opcode() == OPCODE_IF_NE) {
      return true;
    }
    if (insn->opcode() != OPCODE_INVOKE_VIRTUAL) {
      return false;
    }
    const auto* method = insn->get_method();
    return (method->get_class() == ENUM_TYPE ||
            m_candidate_enums->count_unsafe(method->get_class()) != 0u) &&
           method::signatures_match(method, ENUM_EQUALS_METHOD);
  }

  struct IdentityRisks {
    // Candidates whose comparison may give another result once boxed.
    UnorderedSet<const DexType*> unsafe;
    // Candidates compared with another candidate, which may give another
    // result only if both are boxed.
    std::vector<std::pair<const DexType*, const DexType*>> compared_candidates;
  };

  /**
   * Boxing replaces each constant with the shared `Integer` of its ordinal.
   * Within one enum that keeps identity: comparing two values of the same enum,
   * or a value with null, keeps its result. (The exception is an enum in
   * `break_reference_equality_allowlist`, whose constants from `max_enum_size`
   * on are boxed with `Integer.valueOf` at every use, so their identity is not
   * guaranteed, as the option's name allows.) Across enums, constants with
   * equal ordinals become identical, and so does a constant and any other
   * `Integer` with its ordinal. So a comparison keeps its result unless the
   * other operand can be an Integer after boxing: a value of a type an Integer
   * may belong to (see `may_be_integer`), or a value of another candidate enum,
   * if that enum is boxed too, which is decided once the other checks have run.
   * Only a register whose types include the enum can hold one of its
   * constants: a local upcast keeps the enum's type on the register, and an
   * upcast that lets a constant leave the method rejects the enum, so a
   * `String` or app-class operand keeps the result.
   *
   * The analysis joins the types that reach the comparison along different
   * paths. Where the joined types would reject, the comparison is judged again
   * on each path into its block, so that operands from different incoming
   * edges are not paired: `a == A` and `b == B`, merged into one block, are not
   * mistaken for `a == B`.
   */
  void process_identity_comparison(const EnumFixpointIterator& engine,
                                   const cfg::ControlFlowGraph& cfg,
                                   const cfg::Block* block,
                                   const IRInstruction* insn,
                                   const EnumTypeEnvironment& env) {
    IdentityRisks joined;
    collect_identity_risks(insn, env, &joined);
    if (joined.unsafe.empty() && joined.compared_candidates.empty()) {
      return;
    }
    // Every execution enters the block along one edge, or at the method entry;
    // joins in earlier blocks stay joined, which can only reject more.
    IdentityRisks on_paths;
    auto judge_path = [&](EnumTypeEnvironment path_env) {
      if (path_env.is_bottom()) {
        return;
      }
      for (const auto& mie : InstructionIterable(block)) {
        engine.analyze_instruction(mie.insn, &path_env);
        if (mie.insn == insn) {
          break;
        }
      }
      collect_identity_risks(insn, path_env, &on_paths);
    };
    if (block == cfg.entry_block()) {
      judge_path(EnumFixpointIterator::gen_env(m_method));
    }
    for (auto* edge : block->preds()) {
      judge_path(
          engine.analyze_edge(edge, engine.get_exit_state_at(edge->src())));
    }
    reject(insn, on_paths.unsafe, UnsafeType::kUsageComparedByIdentity);
    m_compared_candidates.insert(m_compared_candidates.end(),
                                 on_paths.compared_candidates.begin(),
                                 on_paths.compared_candidates.end());
  }

  void collect_identity_risks(const IRInstruction* insn,
                              const EnumTypeEnvironment& env,
                              IdentityRisks* risks) const {
    auto left = discard_primitives(env.get(insn->src(0)));
    auto right = discard_primitives(env.get(insn->src(1)));
    auto collect = [&](const UnorderedSet<const DexType*>& side,
                       const UnorderedSet<const DexType*>& other) {
      for (const auto* type : UnorderedIterable(side)) {
        if (type::is_array(type) || !is_candidate(type)) {
          // Boxing keeps the identity of arrays and of non-candidate objects.
          continue;
        }
        for (const auto* other_type : UnorderedIterable(other)) {
          if (other_type == type || type::is_array(other_type)) {
            continue;
          }
          if (is_candidate(other_type)) {
            risks->compared_candidates.emplace_back(type, other_type);
          } else if (may_be_integer(other_type)) {
            risks->unsafe.insert(type);
          }
        }
      }
    };
    collect(left, right);
    collect(right, left);
  }

  /**
   * Process return-object instruction when we reach the fixpoint.
   */
  void process_return_object(const IRInstruction* insn,
                             const EnumTypeEnvironment* env) const {
    DexType* return_type = m_method->get_proto()->get_rtype();
    always_assert_log(env->get(insn->src(0)).is_value(),
                      "method %s\ninsn %s %s\n", SHOW(m_method), SHOW(insn),
                      SHOW(m_method->get_code()->cfg()));
    reject_if_inconsistent(insn, env->get(insn->src(0)), return_type,
                           UnsafeType::kUsageCastWhenReturn);
  }

  /**
   * Process iput-object and sput-object instructions when we reach the fix
   * point.
   */
  void process_isput_object(const IRInstruction* insn,
                            const EnumTypeEnvironment* env) const {
    auto arg_reg = insn->src(0);
    DexType* field_type = insn->get_field()->get_type();
    reject_if_inconsistent(insn, env->get(arg_reg), field_type,
                           UnsafeType::kUsageCastISPutObject);
  }

  // Whether this is the <clinit> of the class that declares `field`.
  bool in_declaring_clinit(const DexFieldRef* field) const {
    return field->get_class() == m_method->get_class() &&
           method::is_clinit(m_method);
  }

  void process_sput_object(const IRInstruction* insn,
                           const EnumTypeEnvironment* env) const {
    DexFieldRef* field = insn->get_field();
    // The transformation deletes the constant, values array and `$ENTRIES`
    // fields and removes their stores from the enum's own <clinit> only.
    if (!in_declaring_clinit(field)) {
      if (is_enum_values_field(field)) {
        reject(insn, field->get_class(), UnsafeType::kUsageUsedValuesField);
      } else if (is_enum_entries(field)) {
        reject(insn, field->get_class(), UnsafeType::kUsageUsedEnumEntries);
      } else if (is_enum_constant_field(field)) {
        reject(insn, field->get_class(),
               UnsafeType::kUsageConstantSetOutsideClinit);
      }
    }
    process_isput_object(insn, env);
  }

  /**
   * The transformation deletes `$ENTRIES` and the values array field, so no
   * read of them may remain. It rewrites only `values()`, which is not
   * analyzed, and the enum's own <clinit>. kotlinc reads `$ENTRIES` only in
   * the `getEntries()` accessor; `<clinit>` reads it too once that accessor is
   * inlined. `<clinit>` may read the values array field only to build
   * `$ENTRIES` (see `process_enum_entries_input`).
   */
  void process_sget_object(const IRInstruction* insn) const {
    DexFieldRef* field = insn->get_field();
    if (is_enum_entries(field)) {
      TRACE(ENUM, 5, "sget_object enum entries %s in %s", SHOW(field),
            SHOW(m_method));
      reject(insn, field->get_class(), UnsafeType::kUsageUsedEnumEntries);
    } else if (is_enum_values_field(field) &&
               (field->get_class() != m_method->get_class() ||
                !only_used_by(insn, [this](const live_range::Use& use) {
                  return builds_only_enum_entries(use, /*allow_cast=*/true);
                }))) {
      TRACE(ENUM, 5, "sget_object values array %s in %s", SHOW(field),
            SHOW(m_method));
      reject(insn, field->get_class(), UnsafeType::kUsageUsedValuesField);
    }
  }

  /**
   * A Kotlin enum's `<clinit>` builds `$ENTRIES` from its values array, which
   * it upcasts to `Enum[]`:
   *
   *   $ENTRIES = EnumEntriesKt.enumEntries((Enum[]) $VALUES);
   *   $ENTRIES = new EnumEntriesList($VALUES);  // the factory, inlined
   *
   * The transformation deletes the `$ENTRIES` store, and the code that only
   * fed it becomes dead. The enum's own array may reach source `src` of
   * `insn` as `Enum[]` only in this shape: any other code would receive the
   * boxed integers.
   */
  void process_enum_entries_input(const IRInstruction* insn,
                                  src_index_t src,
                                  const EnumTypeEnvironment* env,
                                  UnsafeType reason) const {
    const bool builds_entries = builds_only_enum_entries(
        live_range::Use{const_cast<IRInstruction*>(insn), src},
        /*allow_cast=*/true);
    for (const auto* type : env->get(insn->src(src)).elements()) {
      if (!builds_entries ||
          type::get_array_component_type(type) != m_method->get_class()) {
        reject(insn, type, reason);
      }
    }
  }

  /**
   * Whether `use` of the candidate's values array only builds its `$ENTRIES`
   * in `<clinit>`, in one of three shapes:
   *
   *   - a cast to `Enum[]` (allowed only when `allow_cast`) whose result is
   *     used only by one of the next two;
   *   - the argument of `enumEntries(Enum[])`, whose result is only stored in
   *     the candidate's `$ENTRIES`;
   *   - the argument of the `EnumEntriesList` constructor, whose object is
   *     only stored in the candidate's `$ENTRIES`.
   */
  bool builds_only_enum_entries(const live_range::Use& use,
                                bool allow_cast) const {
    if (!m_clinit_chains) {
      return false;
    }
    const auto* insn = use.insn;
    if (insn->opcode() == OPCODE_CHECK_CAST) {
      return allow_cast && use.src_index == 0 &&
             type::is_enum_array(insn->get_type()) &&
             only_used_by(insn, [this](const live_range::Use& cast_use) {
               return builds_only_enum_entries(cast_use,
                                               /*allow_cast=*/false);
             });
    }
    if (opcode::is_invoke_static(insn->opcode())) {
      return use.src_index == 0 &&
             is_kt_enum_entries_factory(insn->get_method()) &&
             only_used_by(insn, [this](const live_range::Use& result_use) {
               return is_own_enum_entries_store(result_use);
             });
    }
    if (opcode::is_invoke_direct(insn->opcode())) {
      if (use.src_index != 1 ||
          !is_kt_enum_entries_list_ctor(insn->get_method())) {
        return false;
      }
      const auto& use_defs = *(*m_clinit_chains)->use_def_chains;
      auto defs_it = use_defs.find(live_range::Use{use.insn, 0});
      if (defs_it == use_defs.end() || defs_it->second.empty()) {
        return false;
      }
      return std::all_of(
          defs_it->second.begin(), defs_it->second.end(),
          [&](const IRInstruction* def) {
            return def->opcode() == OPCODE_NEW_INSTANCE &&
                   def->get_type() == insn->get_method()->get_class() &&
                   only_used_by(def, [&](const live_range::Use& list_use) {
                     return (list_use.insn == insn &&
                             list_use.src_index == 0) ||
                            is_own_enum_entries_store(list_use);
                   });
          });
    }
    return false;
  }

  // Whether every use of what `def` defines, other than a move, satisfies
  // `pred`. False outside this candidate's `<clinit>`.
  bool only_used_by(
      const IRInstruction* def,
      const std::function<bool(const live_range::Use&)>& pred) const {
    if (!m_clinit_chains) {
      return false;
    }
    const auto& def_uses = *(*m_clinit_chains)->def_use_chains;
    auto it = def_uses.find(const_cast<IRInstruction*>(def));
    if (it == def_uses.end()) {
      return true;
    }
    return unordered_all_of(it->second, [&](const live_range::Use& use) {
      return opcode::is_a_move(use.insn->opcode()) || pred(use);
    });
  }

  bool is_own_enum_entries_store(const live_range::Use& use) const {
    return use.insn->opcode() == OPCODE_SPUT_OBJECT && use.src_index == 0 &&
           is_enum_entries(use.insn->get_field()) &&
           use.insn->get_field()->get_class() == m_method->get_class();
  }

  /**
   * Process filled-new-array when we reach the fixpoint: like aput-object, it
   * stores each source into an array, here of a known component type.
   */
  void process_filled_new_array(const IRInstruction* insn,
                                const EnumTypeEnvironment* env) const {
    const DexType* elem = type::make_array_component_type(insn->get_type());
    if (elem == nullptr || type::is_primitive(elem)) {
      return;
    }
    for (auto src : insn->srcs()) {
      reject_if_inconsistent(insn, env->get(src), elem,
                             UnsafeType::kUsageCastFilledNewArray);
    }
  }

  /**
   * Process aput-object instruction when we reach the fixpoint.
   */
  void process_aput_object(const IRInstruction* insn,
                           const EnumTypeEnvironment* env) const {
    // It's possible that the array_types contains non-array types or is
    // array of primitives. Just ignore them.
    EnumTypes array_types = env->get(insn->src(1));
    EnumTypes elem_types = env->get(insn->src(0));
    UnorderedSet<const DexType*> acceptable_elem_types;
    for (const DexType* type : array_types.elements()) {
      // The stored value must have the array's component type, which for an
      // array of arrays is itself an array type.
      const DexType* elem = type::make_array_component_type(type);
      if ((elem != nullptr) && !type::is_primitive(elem)) {
        acceptable_elem_types.insert(elem); // An array of one type of objects.
      }
    }
    if (acceptable_elem_types.size() > 1) {
      // If a register might be an array of multiple types, it's hard to do
      // further analysis so that we simply reject the types here.
      reject(insn, elem_types, UnsafeType::kUsageCastAputObject);
      reject(insn, acceptable_elem_types, UnsafeType::kUsageCastAputObject);
    } else if (acceptable_elem_types.size() == 1) {
      const DexType* acceptable = *unordered_any(acceptable_elem_types);
      reject_if_inconsistent(insn, elem_types, acceptable,
                             UnsafeType::kUsageCastAputObject);
    }
  }

  /**
   * Direct calls are checked like any other call, including the constructor
   * calls in a candidate's <clinit>: the candidate may stay an enum, and its
   * constructor's parameters then keep their types.
   */
  void process_direct_invocation(const IRInstruction* insn,
                                 const EnumTypeEnvironment* env) const {
    always_assert(insn->opcode() == OPCODE_INVOKE_DIRECT);
    auto* invoked = insn->get_method();
    if (m_clinit_chains && is_kt_enum_entries_list_ctor(invoked)) {
      process_enum_entries_input(insn, 1, env, UnsafeType::kUsageCastParameter);
      return;
    }
    process_general_invocation(insn, env);
  }

  /**
   * Analyze static method invocations if the invoked method is not
   * LString;.valueOf:(LObject;)LString;
   * LCandidateEnum;.valueOf:(String)LCandidateEnum; or
   * LCandidateEnum;.values:()[LCandidateEnum;
   *
   * Otherwise, figure out implicit parameter upcasting by adopting param
   * summary data.
   */
  void process_static_invocation(const IRInstruction* insn,
                                 const EnumTypeEnvironment* env) {
    always_assert(insn->opcode() == OPCODE_INVOKE_STATIC);
    auto* method_ref = insn->get_method();
    if (method_ref == STRING_VALUEOF_METHOD) {
      EnumTypes types = env->get(insn->src(0));
      check_object_cast(types, insn);
      return;
    }
    if (m_clinit_chains && is_kt_enum_entries_factory(method_ref)) {
      process_enum_entries_input(insn, 0, env, UnsafeType::kUsageCastParameter);
      return;
    }
    auto* container = method_ref->get_class();
    if (m_candidate_enums->count_unsafe(container) != 0u) {
      if (is_enum_values(method_ref) || is_enum_valueof(method_ref)) {
        return;
      }
    }
    auto* method = resolve_method_deprecated(method_ref, MethodSearch::Static);
    if ((method == nullptr) ||
        !params_contain_object_type(method, OBJECT_TYPE)) {
      process_general_invocation(insn, env);
      return;
    }
    auto summary_it = m_config->param_summary_map.find(method);
    UnorderedSet<uint16_t>* safe_params = nullptr;
    if (summary_it != m_config->param_summary_map.end()) {
      auto& summary = summary_it->second;
      safe_params = &summary.safe_params;
    }

    auto* const args = method->get_proto()->get_args();
    auto it = args->begin();
    for (size_t arg_id = 0; arg_id < insn->srcs_size(); ++arg_id, ++it) {
      if ((safe_params != nullptr) && (safe_params->count(arg_id) != 0u)) {
        continue;
      }
      reject_if_inconsistent(insn, env->get(insn->src(arg_id)), *it,
                             UnsafeType::kUsageCastParameter);
    }
  }

  /**
   * Process invoke-virtual instructions after we reach the fixpoint.
   *
   * But we can make assumptions for some methods although the invocations
   * seem to involve some cast operations.
   *
   *  # Enum.equals(Object) and Enum.compareTo(Enum) are final methods.
   *  INVOKE_VIRTUAL LCandidateEnum;.equals:(Ljava/lang/Object;)Z
   *  INVOKE_VIRTUAL LCandidateEnum;.compareTo:(Ljava/lang/Enum;)I
   *
   *  # We reject the candidate enum if it overrides `toString()` previously,
   *  # so the CandidateEnum.toString() is Enum.toString() and it behaves
   *  # the same as CandidateEnum.name().
   *  INVOKE_VIRTUAL LCandidateEnum;.toString:()String
   *  INVOKE_VIRTUAL LCandidateEnum;.name:()String
   *
   *  # When the Object param is a candidate enum object, the invocation can be
   *  * modeled.
   *  INVOKE_VIRTUAL StringBuilder.append:(Object)StringBuilder
   *
   *  # Other virtual invocations on candidate enum object that are considered
   *    safe.
   *  INVOKE_VIRTUAL ordinal:()I
   *  INVOKE_VIRTUAL hashCode:()I
   */
  void process_virtual_invocation(const IRInstruction* insn,
                                  const EnumTypeEnvironment* env) const {
    always_assert(insn->opcode() == OPCODE_INVOKE_VIRTUAL);
    const DexMethodRef* method = insn->get_method();
    DexType* container = method->get_class();

    // Class is Enum or a candidate enum class.
    if (container == ENUM_TYPE ||
        (m_candidate_enums->count_unsafe(container) != 0u)) {
      EnumTypes a_types = env->get(insn->src(0));
      auto this_types = discard_primitives(a_types);
      if (method::signatures_match(method, ENUM_EQUALS_METHOD)) {
        // `process_identity_comparison` judges the argument; the
        // transformation needs a receiver of one enum.
        if (this_types.size() > 1) {
          reject(insn, this_types, UnsafeType::kUsageMultiEnumTypes);
        }
        return;
      }
      if (method::signatures_match(method, ENUM_COMPARETO_METHOD)) {
        EnumTypes b_types = env->get(insn->src(1));
        auto that_types = discard_primitives(b_types);
        const DexType* this_type =
            this_types.empty() ? nullptr : *unordered_any(this_types);
        const DexType* that_type =
            that_types.empty() ? nullptr : *unordered_any(that_types);
        // Reject multiple types in the registers.
        if (this_types.size() > 1 || that_types.size() > 1 ||
            ((this_type != nullptr) && (that_type != nullptr) &&
             this_type != that_type)) {
          reject(insn, this_types, UnsafeType::kUsageCastThisPointer);
          reject(insn, that_types, UnsafeType::kUsageCastParameter);
        }
        return;
      } else if (method::signatures_match(method, ENUM_TOSTRING_METHOD) ||
                 method::signatures_match(method, ENUM_HASHCODE_METHOD) ||
                 method::signatures_match(method, ENUM_NAME_METHOD) ||
                 method::signatures_match(method, ENUM_ORDINAL_METHOD)) {
        if (this_types.size() > 1) {
          reject(insn, this_types, UnsafeType::kUsageMultiEnumTypes);
        }
        return;
      }
    } else if (method == STRINGBUILDER_APPEND_METHOD) {
      EnumTypes b_types = env->get(insn->src(1));
      check_object_cast(b_types, insn);
      return;
    }
    // If not special cases, do the general processing.
    process_general_invocation(insn, env);
  }

  /**
   * Analyze invoke instruction's arguments, if the type of arguments are not
   * consistent with the method signature, reject these types.
   */
  void process_general_invocation(const IRInstruction* insn,
                                  const EnumTypeEnvironment* env) const {
    always_assert(insn->has_method());
    auto* method = insn->get_method();
    auto* proto = method->get_proto();
    auto* container = method->get_class();
    // Check the type of arguments.
    auto* args = proto->get_args();
    always_assert(args->size() == insn->srcs_size() ||
                  args->size() == insn->srcs_size() - 1);
    size_t arg_id = 0;
    if (insn->srcs_size() == args->size() + 1) {
      // this pointer
      reject_if_inconsistent(insn, env->get(insn->src(arg_id)), container,
                             UnsafeType::kUsageCastThisPointer);
      arg_id++;
    }
    // Arguments
    auto it = args->begin();
    for (; arg_id < insn->srcs_size(); ++arg_id, ++it) {
      reject_if_inconsistent(insn, env->get(insn->src(arg_id)), *it,
                             UnsafeType::kUsageCastParameter);
    }
  }

  bool is_candidate(const DexType* type) const {
    if (type == nullptr) {
      return false;
    }
    type = type::make_element_type_if_array(type);
    return m_candidate_enums->count_unsafe(type) != 0u;
  }

  void check_object_cast(const EnumTypes& types,
                         const IRInstruction* insn) const {
    auto that_types = discard_primitives(types);
    if (that_types.size() > 1) {
      reject(insn, that_types, UnsafeType::kUsageMultiEnumTypes);
    } else if (that_types.size() == 1 &&
               type::is_array(*unordered_any(that_types))) {
      reject(insn, that_types, UnsafeType::kUsageCastEnumArrayToObject);
    }
  }

  /**
   * If types of register is not consistent with required_type, remove these
   * types from candidate enum set.
   */
  void reject_if_inconsistent(const IRInstruction* insn,
                              const EnumTypes& types,
                              const DexType* required_type,
                              UnsafeType reason = UnsafeType::kUsage) const {
    if (is_candidate(required_type)) {
      bool need_delete = false;
      for (const auto* possible_type : types.elements()) {
        if (!type::is_primitive(possible_type) &&
            possible_type != required_type) {
          need_delete = true;
          reject(insn, possible_type, reason);
        }
      }
      if (need_delete) {
        reject(insn, required_type, reason);
      }
    } else {
      for (const auto* possible_type : types.elements()) {
        reject(insn, possible_type, reason);
      }
    }
  }

  // The transform does not rewrite the call sites, method handles and method
  // types that name an enum: a boxed enum named there would no longer match
  // what the call site or method handle links to.
  void reject_linkage_types(const IRInstruction* insn) const {
    std::vector<const DexType*> types;
    insn->gather_types(types);
    for (const auto* type : types) {
      reject(insn, type, UnsafeType::kUsageNamedByCallSiteOrMethodHandle);
    }
  }

  /**
   * Reject the candidate that a method or field reference names, directly or
   * as the element type of an array, unless the candidate defines that member,
   * or `process_virtual_invocation` rewrites the call: `equals`, `compareTo`,
   * `toString`, `hashCode`, `name` and `ordinal`. The transformation turns a
   * candidate into a subclass of `Object` whose methods are static, so a member
   * it inherits, such as `Enum.valueOf(Class, String)` or
   * `Enum.getDeclaringClass()`, does not exist on it, and it rewrites a call
   * through an array of the candidate, like `clone()`, as a call of the
   * candidate's own method.
   */
  void reject_unless_candidate_defines(const IRInstruction* insn) const {
    if (insn->has_method()) {
      const auto* method = insn->get_method();
      if (is_candidate(method->get_class()) && !method->is_def() &&
          !is_rewritten_enum_method(method)) {
        reject(insn, method->get_class(),
               UnsafeType::kUsageUnsafeInvocationOnCandidateEnum);
      }
    } else if (insn->has_field()) {
      const auto* field = insn->get_field();
      if (m_candidate_enums->count_unsafe(field->get_class()) != 0u &&
          !field->is_def()) {
        reject(insn, field->get_class(), UnsafeType::kUsageInheritedFieldRef);
      }
    }
  }

  bool is_rewritten_enum_method(const DexMethodRef* method) const {
    return method::signatures_match(method, ENUM_EQUALS_METHOD) ||
           method::signatures_match(method, ENUM_COMPARETO_METHOD) ||
           method::signatures_match(method, ENUM_TOSTRING_METHOD) ||
           method::signatures_match(method, ENUM_HASHCODE_METHOD) ||
           method::signatures_match(method, ENUM_NAME_METHOD) ||
           method::signatures_match(method, ENUM_ORDINAL_METHOD);
  }

  void reject(const IRInstruction* insn,
              const UnorderedSet<const DexType*>& types,
              UnsafeType reason = UnsafeType::kUsage) const {
    for (const DexType* type : UnorderedIterable(types)) {
      reject(insn, type, reason);
    }
  }

  void reject(const IRInstruction* insn,
              const EnumTypes& types,
              UnsafeType reason = UnsafeType::kUsage) const {
    for (const DexType* type : types.elements()) {
      reject(insn, type, reason);
    }
  }

  void reject(const IRInstruction* insn,
              const DexType* type,
              UnsafeType reason = UnsafeType::kUsage) const {
    type = type::make_element_type_if_array(type);
    if (m_candidate_enums->count_unsafe(type) != 0u) {
      m_reject_fn(type, reason);
      if (traceEnabled(ENUM, 9)) {
        std::ostringstream os;
        os << reason;
        TRACE(ENUM, 9, "reject %s %s %s %s", SHOW(type), os.str().c_str(),
              SHOW(m_method), SHOW(insn));
      }
    }
  }

  const DexMethodRef* ENUM_EQUALS_METHOD = method::java_lang_Enum_equals();
  const DexMethodRef* ENUM_COMPARETO_METHOD =
      method::java_lang_Enum_compareTo();
  const DexMethodRef* ENUM_TOSTRING_METHOD = method::java_lang_Enum_toString();
  const DexMethodRef* ENUM_HASHCODE_METHOD = method::java_lang_Enum_hashCode();
  const DexMethodRef* ENUM_NAME_METHOD = method::java_lang_Enum_name();
  const DexMethodRef* ENUM_ORDINAL_METHOD = method::java_lang_Enum_ordinal();
  const DexMethodRef* STRING_VALUEOF_METHOD = DexMethod::make_method(
      "Ljava/lang/String;.valueOf:(Ljava/lang/Object;)Ljava/lang/String;");
  const DexMethodRef* STRINGBUILDER_APPEND_METHOD = DexMethod::make_method(
      "Ljava/lang/StringBuilder;.append:(Ljava/lang/Object;)Ljava/lang/"
      "StringBuilder;");
  const DexType* ENUM_TYPE = type::java_lang_Enum();
  const DexType* OBJECT_TYPE = type::java_lang_Object();
  const DexType* STRING_TYPE = type::java_lang_String();

  const DexMethod* m_method;
  Config* m_config;
  const ConcurrentSet<const DexType*>* m_candidate_enums;
  const RejectFn& m_reject_fn;
  // The chains of a candidate's `<clinit>`, where Kotlin builds `$ENTRIES`;
  // absent elsewhere, and computed only when an instruction needs them.
  mutable std::optional<Lazy<live_range::LazyLiveRanges>> m_clinit_chains;
  std::vector<std::pair<const DexType*, const DexType*>> m_compared_candidates;
};

bool is_static_method_on_enum_class(const DexMethodRef* ref) {
  const auto* method = dynamic_cast<const DexMethod*>(ref);
  if ((method == nullptr) || !method->is_def() || !is_static(method)) {
    return false;
  }
  auto* container = type_class(method->get_class());
  return (container != nullptr) && is_enum(container);
}
} // namespace

namespace optimize_enums {

/**
 * Analyze all the instructions that may involve object or type and handle
 * possible candidate enums specificly.
 */
void EnumFixpointIterator::analyze_instruction(const IRInstruction* insn,
                                               EnumTypeEnvironment* env) const {
  const bool use_result = insn->has_move_result_any();
  if (use_result || insn->has_dest()) {
    reg_t dest = use_result ? RESULT_REGISTER : insn->dest();

    switch (insn->opcode()) {
    case IOPCODE_LOAD_PARAM:
    case IOPCODE_LOAD_PARAM_OBJECT:
    case IOPCODE_LOAD_PARAM_WIDE:
      // Parameters are processed before we run FixpointIterator
      break;
    case OPCODE_MOVE_OBJECT:
      env->set(dest, env->get(insn->src(0)));
      break;
    case OPCODE_INVOKE_STATIC: {
      auto* method =
          resolve_method_deprecated(insn->get_method(), MethodSearch::Static);
      if (method != nullptr) {
        auto it = m_config.param_summary_map.find(method);
        if (it != m_config.param_summary_map.end()) {
          const auto& summary = it->second;
          if (summary.returned_param) {
            auto returned = *summary.returned_param;
            if (summary.safe_params.count(returned) != 0u) {
              env->set(dest, env->get(insn->src(returned)));
              return;
            }
          }
        }
      }
      env->set(dest, EnumTypes(insn->get_method()->get_proto()->get_rtype()));
    } break;
    case OPCODE_INVOKE_SUPER:
    case OPCODE_INVOKE_DIRECT:
    case OPCODE_INVOKE_INTERFACE:
    case OPCODE_INVOKE_VIRTUAL:
      env->set(dest, EnumTypes(insn->get_method()->get_proto()->get_rtype()));
      break;
    case OPCODE_INVOKE_CUSTOM:
    case OPCODE_INVOKE_POLYMORPHIC:
      env->set(dest, EnumTypes(insn->get_callsite_proto()->get_rtype()));
      break;

    // These dex 038 and 039 instructions cannot reach OptimizeEnumsPass, which
    // supports dex 035 (`pass_support_dex_version()` is 35): PassManager aborts
    // before running it on input that has them. Their results are objects all
    // the same, never null, so an identity comparison with one cannot be judged
    // as one with null.
    case OPCODE_CONST_METHOD_HANDLE:
    case OPCODE_CONST_METHOD_TYPE:
      env->set(dest, EnumTypes(OBJECT_TYPE));
      break;
    case OPCODE_CONST_CLASS:
      env->set(dest, EnumTypes(type::java_lang_Class()));
      break;
    case OPCODE_CHECK_CAST: {
      const auto* type = insn->get_type();
      if (type == OBJECT_TYPE) {
        env->set(dest, env->get(insn->src(0)));
      } else {
        env->set(dest, EnumTypes(type));
      }
    } break;
    case IOPCODE_MOVE_RESULT_PSEUDO_OBJECT:
    case OPCODE_MOVE_RESULT_OBJECT:
      env->set(dest, env->get(RESULT_REGISTER));
      break;
    case OPCODE_SGET_OBJECT:
    case OPCODE_IGET_OBJECT: {
      DexType* type = insn->get_field()->get_type();
      if (!type::is_primitive(type)) {
        env->set(dest, EnumTypes(type));
      }
    } break;
    case OPCODE_AGET_OBJECT: {
      EnumTypes types;
      EnumTypes array_types = env->get(insn->src(0));
      for (const auto* const array_type : array_types.elements()) {
        // Reading `rows[0]` from a `Bar[][]` yields a `Bar[]`, not a `Bar`.
        auto* const type = type::make_array_component_type(array_type);
        if ((type != nullptr) && !type::is_primitive(type)) {
          types.add(type);
        }
      }
      env->set(dest, types);
    } break;
    case OPCODE_CONST_STRING: {
      env->set(dest, EnumTypes(type::java_lang_String()));
    } break;
    case OPCODE_MOVE_EXCEPTION: {
      env->set(dest, EnumTypes(type::java_lang_Throwable()));
    } break;
    case OPCODE_NEW_ARRAY:
    case OPCODE_NEW_INSTANCE:
    case OPCODE_FILLED_NEW_ARRAY:
    default:
      if (insn->has_type()) {
        env->set(dest, EnumTypes(insn->get_type()));
      } else {
        env->set(dest, EnumTypes());
      }
      // When we write a wide register v, the v+1 register is overrode.
      if (insn->has_dest() && insn->dest_is_wide()) {
        env->set(dest + 1, EnumTypes());
      }
      break;
    }
  }
}

/**
 * Generate environment with method parameter registers.
 */
EnumTypeEnvironment EnumFixpointIterator::gen_env(const DexMethod* method) {
  EnumTypeEnvironment env;
  const auto params = method->get_code()->cfg().get_param_instructions();
  const DexTypeList* args = method->get_proto()->get_args();
  const bool has_this_pointer = !is_static(method);
  size_t load_param_inst_size = 0;
  for (const auto& mie ATTRIBUTE_UNUSED : InstructionIterable(params)) {
    ++load_param_inst_size;
  }
  always_assert(load_param_inst_size == args->size() + has_this_pointer);

  auto iterable = InstructionIterable(params);
  auto it = iterable.begin();
  if (has_this_pointer) { // Has this pointer
    env.set(it->insn->dest(), EnumTypes(method->get_class()));
    ++it;
  }
  for (const DexType* type : *args) {
    env.set(it->insn->dest(), EnumTypes(type));
    ++it;
  }
  return env;
}

/**
 * Reject enums that would cause constructors to have prototypes that would
 * become identical.
 */
void reject_enums_for_colliding_constructors(
    const std::vector<DexClass*>& classes,
    ConcurrentSet<const DexType*>* candidate_enums) {
  ConcurrentSet<DexType*> rejected_enums;

  walk::parallel::classes(classes, [&](DexClass* cls) {
    const auto& ctors = cls->get_ctors();
    if (ctors.size() <= 1) {
      return;
    }
    UnorderedSet<DexTypeList*> modified_params_lists;
    for (auto* ctor : ctors) {
      UnorderedSet<DexType*> transforming_enums;
      DexTypeList::ContainerType param_types{
          ctor->get_proto()->get_args()->begin(),
          ctor->get_proto()->get_args()->end()};
      for (size_t i = 0; i < param_types.size(); i++) {
        auto* base_type = const_cast<DexType*>(
            type::make_element_type_if_array(param_types[i]));
        if (candidate_enums->count(base_type) != 0u) {
          transforming_enums.insert(base_type);
          param_types[i] = type::make_array_type(
              type::java_lang_Integer(), type::get_array_level(param_types[i]));
        }
      }
      auto* new_params = DexTypeList::make_type_list(std::move(param_types));
      if (modified_params_lists.count(new_params) != 0u) {
        for (auto* enum_type : UnorderedIterable(transforming_enums)) {
          TRACE(ENUM, 4,
                "Reject %s because it would create a method prototype "
                "collision for %s",
                SHOW(enum_type), SHOW(ctor));
          rejected_enums.insert(enum_type);
        }
      } else {
        auto* new_proto = DexProto::make_proto(type::_void(), new_params);
        if (DexMethod::get_method(ctor->get_class(), ctor->get_name(),
                                  new_proto) != nullptr) {
          for (auto* enum_type : UnorderedIterable(transforming_enums)) {
            TRACE(ENUM, 4,
                  "Reject %s because it would create a method prototype "
                  "collision for %s",
                  SHOW(enum_type), SHOW(ctor));
            rejected_enums.insert(enum_type);
          }
        } else {
          modified_params_lists.insert(new_params);
        }
      }
    }
  });

  for (DexType* type : UnorderedIterable(rejected_enums)) {
    candidate_enums->erase(type);
  }
}

void reject_enums_for_relaxed_inits(
    const std::vector<DexClass*>& classes,
    ConcurrentSet<const DexType*>* candidate_enums) {
  ConcurrentSet<const DexType*> rejected_enums;
  walk::parallel::code(classes, [&](DexMethod* method, IRCode& code) {
    auto& cfg = code.cfg();
    UnorderedSet<const IRInstruction*> new_instances_to_verify;
    for (auto& mie : InstructionIterable(cfg)) {
      auto* insn = mie.insn;
      if (insn->opcode() != OPCODE_NEW_INSTANCE ||
          (candidate_enums->count(insn->get_type()) == 0u)) {
        continue;
      }
      new_instances_to_verify.insert(insn);
    }
    if (new_instances_to_verify.empty()) {
      return;
    }
    live_range::MoveAwareChains chains(
        cfg, /* ignore_unreachable */ false,
        [&](auto* insn) { return new_instances_to_verify.count(insn); });
    live_range::DefUseChains du_chains = chains.get_def_use_chains();
    for (const auto* new_instance_insn :
         UnorderedIterable(new_instances_to_verify)) {
      const auto* enum_type = new_instance_insn->get_type();
      const auto& use_set =
          du_chains[const_cast<IRInstruction*>(new_instance_insn)];
      for (const auto& use : UnorderedIterable(use_set)) {
        if (use.src_index != 0) {
          continue;
        }
        auto* use_insn = use.insn;
        if (opcode::is_a_move(use_insn->opcode())) {
          // Ignore moves
          continue;
        }
        if (!use_insn->has_method()) {
          continue;
        }
        auto* callee = use_insn->get_method();
        if (!method::is_init(callee)) {
          continue;
        }
        const auto* resolved_callee = resolve_method_deprecated(
            callee, opcode_to_search(use_insn), method);
        if ((resolved_callee == nullptr) ||
            resolved_callee->get_class() != enum_type) {
          TRACE(ENUM, 4,
                "Reject %s because base constructor %s in invoke instruction "
                "%s may be called on new-instance instruction %s in %s",
                SHOW(enum_type), SHOW(resolved_callee), SHOW(use_insn),
                SHOW(new_instance_insn), SHOW(method));
          rejected_enums.insert(enum_type);
          break;
        }
      }
    }
  });
  for (const DexType* type : UnorderedIterable(rejected_enums)) {
    candidate_enums->erase(type);
  }
}

void reject_unsafe_enums(
    const std::vector<DexClass*>& classes,
    Config* config,
    const std::function<void(const DexType*, UnsafeType u)>& reject_fn) {
  auto* candidate_enums = &config->candidate_enums;
  ConcurrentSet<const DexType*> rejected_enums;
  ConcurrentMap<const DexType*, UnorderedSet<const DexType*>>
      compared_candidates;

  walk::parallel::fields(
      classes, [candidate_enums, &rejected_enums, &reject_fn](DexField* field) {
        if (can_rename(field)) {
          return;
        }
        if (candidate_enums->count_unsafe(field->get_class()) != 0u) {
          auto access = field->get_access();
          if (check_required_access_flags(enum_field_access(), access) ||
              check_required_access_flags(synth_access(), access)) {
            return;
          }
        }
        auto* type = const_cast<DexType*>(
            type::make_element_type_if_array(field->get_type()));
        if (candidate_enums->count_unsafe(type) != 0u) {
          rejected_enums.insert(type);
          reject_fn(type, UnsafeType::kUsageUnrenamableFieldType);
        }
      });

  walk::parallel::methods(classes, [&](DexMethod* method) {
    // Boxing an enum rewrites every method that refers to it, but Redex must
    // leave a method marked `no_optimizations` exactly as it is.
    if (method->rstate.no_optimizations()) {
      std::vector<const DexType*> types;
      method->gather_types(types);
      for (const auto* type : types) {
        const auto* elem_type = type::make_element_type_if_array(type);
        if (candidate_enums->count_unsafe(elem_type) != 0u) {
          rejected_enums.insert(elem_type);
          reject_fn(elem_type, UnsafeType::kUsageNoOptimizationsMethod);
        }
      }
      return;
    }

    // When doing static analysis, simply skip some javac-generated enum
    // methods <init>, values(), and valueOf(String). Skip unconditionally:
    // these methods have known-safe patterns and are only ever analyzed (under
    // the old rejected-class gate) once the enum is already rejected, so
    // skipping them never changes which enums are rejected -- it only avoids
    // recording spurious, scheduling-dependent reasons against an
    // already-rejected enum.
    if ((candidate_enums->count_unsafe(method->get_class()) != 0u) &&
        (method::is_init(method) || is_enum_values(method) ||
         is_enum_valueof(method))) {
      return;
    }

    auto reject_proto_types = [&](DexMethod* method, UnsafeType u) {
      std::vector<const DexType*> types;
      method->get_proto()->gather_types(types);
      for (const auto* type : types) {
        auto* elem_type =
            const_cast<DexType*>(type::make_element_type_if_array(type));
        if (candidate_enums->count_unsafe(elem_type) != 0u) {
          TRACE(ENUM, 5,
                "Rejecting %s due to !can_rename or usage from annotation",
                SHOW(elem_type));
          reject_fn(elem_type, u);
          rejected_enums.insert(elem_type);
        }
      }
    };

    if (!can_rename(method)) {
      reject_proto_types(method, UnsafeType::kUsageUnrenamableMethodRef);
      if (!is_static(method) &&
          (candidate_enums->count_unsafe(method->get_class()) != 0u)) {
        rejected_enums.insert(method->get_class());
      }
    }

    auto* method_cls = type_class(method->get_class());
    if (method_cls != nullptr && is_annotation(method_cls)) {
      reject_proto_types(method, UnsafeType::kUsageAnnotationMethodRef);
    }

    if (!need_analyze(method, *candidate_enums)) {
      return;
    }

    auto& cfg = method->get_code()->cfg();
    EnumTypeEnvironment env = EnumFixpointIterator::gen_env(method);
    EnumFixpointIterator engine(cfg, *config);
    engine.run(env);

    auto local_reject_fn = [&](const DexType* type, UnsafeType u) {
      rejected_enums.insert(type);
      reject_fn(type, u);
    };

    EnumUpcastDetector detector(method, config, local_reject_fn);
    detector.run(engine, cfg);
    for (const auto& pair : detector.compared_candidates()) {
      compared_candidates.update(pair.first, [&](auto*, auto& others, bool) {
        others.insert(pair.second);
      });
    }
  });

  for (const auto* type : UnorderedIterable(rejected_enums)) {
    candidate_enums->erase(type);
  }

  reject_enums_for_colliding_constructors(classes, candidate_enums);
  reject_enums_for_relaxed_inits(classes, candidate_enums);

  // Comparing two candidates by identity may give another result only if both
  // are boxed. Collect both ends of every pair against the candidates left now
  // before erasing either, so that iteration order cannot decide which enum
  // stays boxed: two enums that are compared only with each other both stay
  // enums. Each pair is recorded in both orders, so rejecting each key rejects
  // both ends.
  std::vector<const DexType*> compared_with_candidate;
  for (const auto& [type, others] : UnorderedIterable(compared_candidates)) {
    if (candidate_enums->count(type) != 0u &&
        unordered_any_of(others, [&](const DexType* other) {
          return candidate_enums->count(other) != 0u;
        })) {
      compared_with_candidate.push_back(type);
    }
  }
  for (const auto* type : compared_with_candidate) {
    reject_fn(type, UnsafeType::kUsageComparedByIdentity);
    candidate_enums->erase(type);
  }
}

bool is_enum_valueof(const DexMethodRef* method) {
  if (!is_static_method_on_enum_class(method) || method->str() != "valueOf") {
    return false;
  }
  auto* proto = method->get_proto();
  if (method->get_class() != proto->get_rtype()) {
    return false;
  }
  auto* args = proto->get_args();
  return args->size() == 1 && args->at(0) == type::java_lang_String();
}

bool is_enum_values(const DexMethodRef* method) {
  if (!is_static_method_on_enum_class(method) || method->str() != "values") {
    return false;
  }
  auto* proto = method->get_proto();
  if (!proto->get_args()->empty()) {
    return false;
  }
  return type::make_array_component_type(proto->get_rtype()) ==
         method->get_class();
}

bool is_enum_values_field(const DexFieldRef* field_ref) {
  if (!is_static_field_on_enum_class(field_ref)) {
    return false;
  }
  const auto* field = field_ref->as_def();
  return check_required_access_flags(synth_access(), field->get_access()) &&
         type::get_array_component_type(field->get_type()) ==
             field->get_class();
}

namespace {

// Whether the code that runs for the Kotlin library method `method` is
// Kotlin's own: an app's copy marked `no_optimizations` may not be what runs.
bool runs_kotlin_library_code(const DexMethodRef* method) {
  const auto* def = method->as_def();
  return def == nullptr || !def->rstate.no_optimizations();
}

} // namespace

bool is_kt_enum_entries_factory(const DexMethodRef* method) {
  const auto* factory = DexMethod::make_method(KT_ENUM_ENTRIES_FACTORY_METHOD);
  const auto* rtype = method->get_proto()->get_rtype();
  return method->get_class() == factory->get_class() &&
         method->get_name() == factory->get_name() &&
         method->get_proto()->get_args() == factory->get_proto()->get_args() &&
         (rtype == factory->get_proto()->get_rtype() ||
          rtype ==
              DexMethod::make_method(KT_ENUM_ENTRIES_LIST_CTOR)->get_class()) &&
         runs_kotlin_library_code(method);
}

bool is_kt_enum_entries_list_ctor(const DexMethodRef* method) {
  return method == DexMethod::make_method(KT_ENUM_ENTRIES_LIST_CTOR) &&
         runs_kotlin_library_code(method);
}

bool is_enum_entries(const DexFieldRef* field) {
  if (!is_static_field_on_enum_class(field) ||
      field->str() != ENUM_ENTRIES_FIELD) {
    return false;
  }
  return field->get_type() == DexType::get_type(KT_ENUM_ENTRIES_TYPE);
}

} // namespace optimize_enums
