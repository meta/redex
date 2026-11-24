/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "EnumClinitAnalysis.h"

#include <algorithm>
#include <optional>
#include <vector>

#include "ConstantPropagationAnalysis.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexAccess.h"
#include "EnumUpcastAnalysis.h"
#include "IROpcode.h"
#include "KotlinNullCheckMethods.h"
#include "LocalPointersAnalysis.h"
#include "LoopInfo.h"
#include "MethodUtil.h"
#include "Purity.h"
#include "Resolver.h"
#include "Show.h"
#include "Trace.h"

/* clang-format off */
/*
 * This module analyzes the clinit of an Enum class in order to determine the
 * ordinal and name values of each Enum instance. The pattern we are targeting
 * is:
 *
 * FooEnum.<clinit>()V:
 *   const/4 v1, #int 0 // ordinal value
 *   const-string v2, "ENUM_NAME"
 *   const-string v3, "SomeOtherData"
 *   new-instance v0, "LFooEnum;"
 *   invoke-direct {v0, v1, v2, v3}, LFooEnum;.<init>:(Ljava/lang/String;ILjava/lang/String)V
 *   sput-object v0, LFooEnum;.ENUM_NAME
 *   ...
 *
 * FooEnum.<init>(Ljava/lang/String;I;Ljava/lang/String)V:
 *   invoke-direct {v0, v1, v2}, Ljava/lang/Enum;.<init>:(Ljava/lang/String;I)V // set the enum name and ordinal
 *   ...
 *
 * The call to Enum.<init> sets the enum's name and ordinal. It's implemented
 * in the Java runtime, so we can't analyze its bytecode, but it can be modeled
 * as setting two private fields in the Enum object.
 */
/* clang-format on */

namespace cp = constant_propagation;

namespace {

DexMethod* get_enum_ctor() {
  return dynamic_cast<DexMethod*>(
      DexMethod::get_method("Ljava/lang/Enum;.<init>:(Ljava/lang/String;I)V"));
}

/*
 * This field does not actually exist -- we are just defining it so we have a
 * way of representing the ordinal value during abstract interpretation.
 */
DexField* get_fake_field(const std::string& full_descriptor) {
  DexField* field =
      dynamic_cast<DexField*>(DexField::make_field(full_descriptor));
  if (field->is_concrete()) {
    field->make_concrete(ACC_PUBLIC);
  }
  return field;
}

DexField* get_ordinal_field() {
  return get_fake_field("Ljava/lang/Enum;.__ordinal__:I");
}

DexField* get_enum_name_field() {
  return get_fake_field("Ljava/lang/Enum;.__name__:Ljava/lang/String;");
}

struct EnumOrdinalAnalyzerState {
  // NOLINTNEXTLINE(google-explicit-constructor,hicpp-explicit-conversions)
  /* implicit */ EnumOrdinalAnalyzerState(const DexType* clinit_class)
      : clinit_class(clinit_class) {
    auto& fields = type_class(clinit_class)->get_ifields();
    enum_instance_fields =
        UnorderedSet<DexField*>(fields.begin(), fields.end());
  }

  const DexMethod* enum_ordinal_init{get_enum_ctor()};

  const DexField* enum_ordinal_field{get_ordinal_field()};

  const DexField* enum_name_field{get_enum_name_field()};

  const DexType* enum_type{type::java_lang_Enum()};

  // The Enum class whose <clinit> we are currently analyzing.
  const DexType* clinit_class;

  // The instance fields of the enum whose <clinit> we are analyzing.
  UnorderedSet<DexField*> enum_instance_fields;
};

class EnumOrdinalAnalyzer;

using CombinedAnalyzer =
    InstructionAnalyzerCombiner<EnumOrdinalAnalyzer,
                                cp::HeapEscapeAnalyzer,
                                cp::StringAnalyzer,
                                cp::ConstantClassObjectAnalyzer,
                                cp::ResourceIdAnalyzer,
                                cp::PrimitiveAnalyzer>;

class EnumOrdinalAnalyzer
    : public InstructionAnalyzerBase<EnumOrdinalAnalyzer,
                                     ConstantEnvironment,
                                     EnumOrdinalAnalyzerState> {
 public:
  static bool analyze_new_instance(const EnumOrdinalAnalyzerState& /*state*/,
                                   const IRInstruction* insn,
                                   ConstantEnvironment* env) {
    auto* cls = type_class(insn->get_type());
    if (cls == nullptr) {
      return false;
    }
    if (!is_enum(cls)) {
      return false;
    }
    env->new_heap_value(RESULT_REGISTER, insn, ConstantObjectDomain());
    return true;
  }

  static bool analyze_iput(const EnumOrdinalAnalyzerState& state,
                           const IRInstruction* insn,
                           ConstantEnvironment* env) {
    auto* field = resolve_field(insn->get_field());
    if (field == nullptr) {
      return false;
    }
    if (state.enum_instance_fields.count(field) != 0u) {
      env->set_object_field(insn->src(1), field, env->get(insn->src(0)));
      return true;
    }
    return false;
  }

  static bool analyze_sput(const EnumOrdinalAnalyzerState& state,
                           const IRInstruction* insn,
                           ConstantEnvironment* env) {
    auto* field = resolve_field(insn->get_field());
    if (field == nullptr) {
      return false;
    }
    if (field->get_class() == state.clinit_class) {
      env->set(field, env->get(insn->src(0)));
      return true;
    }
    return false;
  }

  static bool analyze_aput(const EnumOrdinalAnalyzerState& /*state*/,
                           const IRInstruction* insn,
                           ConstantEnvironment* /*env*/) {
    // Simply not do further analysis for the aput-object instructions. Maybe
    // we can improve the analysis in the future.
    return insn->opcode() == OPCODE_APUT_OBJECT;
  }

  static bool analyze_invoke(const EnumOrdinalAnalyzerState& state,
                             const IRInstruction* insn,
                             ConstantEnvironment* env) {
    auto* method =
        resolve_method_deprecated(insn->get_method(), opcode_to_search(insn));
    if (method == nullptr) {
      return false;
    }
    if (method == state.enum_ordinal_init) {
      auto name = env->get(insn->src(1));
      auto ordinal = env->get(insn->src(2));
      env->set_object_field(insn->src(0), state.enum_name_field, name);
      env->set_object_field(insn->src(0), state.enum_ordinal_field, ordinal);
      return true;
    } else if (method::is_init(method) &&
               method->get_class() == state.clinit_class) {
      // TODO(fengliu) : Analyze enums with an instance string field.
      cp::semantically_inline_method(
          method->get_code(),
          insn,
          CombinedAnalyzer(state, nullptr, nullptr, nullptr, nullptr, nullptr),
          env);
      return true;
    }
    return false;
  }
};

/**
 * Ordinals should be consecutive and all the static final fields in the enum
 * type are in the result map.
 */
bool validate_result(const DexClass* cls,
                     const optimize_enums::EnumConstantsMap& constants,
                     const bool support_kt_19_enum_entries) {
  if (constants.empty()) {
    TRACE(ENUM, 2, "\tEmpty result for %s", SHOW(cls));
    return false;
  }
  std::vector<bool> ordinals(constants.size(), false);
  size_t synth_values_field_cnt = 0;

  auto enum_field_access = optimize_enums::enum_field_access();
  auto values_access = optimize_enums::synth_access();

  for (auto* enum_sfield : cls->get_sfields()) {
    auto access = enum_sfield->get_access();
    auto it = constants.find(enum_sfield);
    if (it != constants.end()) {
      if (!check_required_access_flags(enum_field_access, access)) {
        TRACE(ENUM, 2, "\tUnexpected access %x on %s", access,
              SHOW(enum_sfield));
        return false;
      }
      uint32_t ordinal = it->second.ordinal;
      if (ordinal >= ordinals.size()) {
        TRACE(ENUM, 2, "\tUnexpected ordinal %u on %s", ordinal,
              SHOW(enum_sfield));
        return false;
      }
      ordinals[ordinal] = true;
    } else {
      if (check_required_access_flags(enum_field_access, access)) {
        TRACE(ENUM, 2, "\tEnum value %s is missing in the result",
              SHOW(enum_sfield));
        return false;
      }
      if (check_required_access_flags(values_access, access)) {
        if (synth_values_field_cnt < 2) {
          synth_values_field_cnt++;
        } else {
          // $VALUES and $ENTRIES
          TRACE(ENUM, 2, "\tMore static synthetic fields than expected on %s",
                SHOW(cls));
          return false;
        }
      }
    }
  }
  if (synth_values_field_cnt == 2) {
    always_assert_log(support_kt_19_enum_entries,
                      "Only Kotlin 1.9 enums have two synth fields.");
  }
  if (std::all_of(ordinals.begin(), ordinals.end(),
                  [](bool item) { return item; })) {
    return true;
  }
  TRACE(ENUM, 2, "\tEnum %s has some values in the same ordinal", SHOW(cls));
  return false;
}

// Whether `method` makes a method handle call or calls through a call site,
// either of which may run any code.
bool calls_method_handle(const DexMethod* method) {
  const auto* code = method->get_code();
  if (code == nullptr) {
    return false;
  }
  auto ii = cfg::ConstInstructionIterable(code->cfg());
  return std::any_of(ii.begin(), ii.end(), [](const auto& mie) {
    return opcode::is_invoke_polymorphic(mie.insn->opcode()) ||
           opcode::is_invoke_custom(mie.insn->opcode());
  });
}

bool is_constant_of(const DexClass* cls, const DexField* field) {
  return field != nullptr && field->get_class() == cls->get_type() &&
         check_required_access_flags(optimize_enums::enum_field_access(),
                                     field->get_access());
}

// Whether `<clinit>` has assigned `field` on every path to the state `env`.
bool is_assigned(const ConstantEnvironment& env, DexField* field) {
  auto heap_ptr = env.get(field).maybe_get<AbstractHeapPointer>();
  return heap_ptr && heap_ptr->get_constant();
}

// The constants of `cls` that `<clinit>` has not assigned on every path to the
// state `env`.
UnorderedSet<const DexField*> unassigned_constants(
    const DexClass* cls, const ConstantEnvironment& env) {
  UnorderedSet<const DexField*> unassigned;
  for (auto* field : cls->get_sfields()) {
    if (is_constant_of(cls, field) && !is_assigned(env, field)) {
      unassigned.insert(field);
    }
  }
  return unassigned;
}

/**
 * The constants of `cls` that `insn` reads: the constant itself for an
 * `sget-object` of one, or all of them for a read of the values array or a call
 * of `values()` or `valueOf(String)`, which see them only once every one is
 * assigned.
 */
void add_constants_read(const IRInstruction* insn,
                        UnorderedSet<const DexField*>* reads) {
  if (insn->opcode() != OPCODE_SGET_OBJECT) {
    return;
  }
  const auto* field = resolve_field(insn->get_field(), FieldSearch::Static);
  const auto* cls = field == nullptr ? nullptr : type_class(field->get_class());
  if (cls == nullptr || !is_enum(cls)) {
    return;
  }
  if (is_constant_of(cls, field)) {
    reads->insert(field);
    return;
  }
  if (!optimize_enums::is_enum_values_field(field)) {
    return;
  }
  // The values array holds every constant, so it exists only once every one
  // is assigned.
  for (auto* constant : cls->get_sfields()) {
    if (is_constant_of(cls, constant)) {
      reads->insert(constant);
    }
  }
}

// Whether `insn` reads one of the constants in `unassigned`.
bool reads_unassigned_constant(
    const IRInstruction* insn,
    const UnorderedSet<const DexField*>& unassigned) {
  UnorderedSet<const DexField*> reads;
  add_constants_read(insn, &reads);
  return unordered_any_of(reads, [&](const DexField* field) {
    return unassigned.count(field) != 0u;
  });
}

/**
 * Whether `insn` may read one of `cls`'s constants before `<clinit>` has
 * assigned it on every path, given the state `env` before `insn`, directly or
 * in the code a call runs. Such a read sees null, as in
 * `enum E { A(E.B == null), B(false); }`, but would see the boxed constant once
 * the enum is boxed. `<clinit>` makes no `invoke-polymorphic` or
 * `invoke-custom` call, as `analyze_enum_clinit` checks first. The class
 * initializers that this code triggers are not followed: Redex may change when
 * static initializers run (website/docs/fb/faq/specbreaker.md, Static
 * Initializers), as FinalInlinePassV2 already does.
 */
bool may_read_unassigned_constant(
    const DexClass* cls,
    const IRInstruction* insn,
    const ConstantEnvironment& env,
    optimize_enums::ConstantReadSummaries* reads) {
  const bool is_call = opcode::is_a_method_invoke(insn->opcode());
  if (env.is_bottom() || (insn->opcode() != OPCODE_SGET_OBJECT && !is_call)) {
    return false;
  }
  const auto unassigned = unassigned_constants(cls, env);
  return !unassigned.empty() &&
         (reads_unassigned_constant(insn, unassigned) ||
          (is_call && reads->call_may_read(insn, unassigned)));
}

} // namespace

namespace optimize_enums {

DexAccessFlags enum_field_access() { return ACC_STATIC | ACC_ENUM; }

DexAccessFlags synth_access() { return ACC_STATIC | ACC_FINAL | ACC_SYNTHETIC; }

namespace {

// The methods that run no app code, so a call of one reads no constant.
UnorderedSet<DexMethodRef*> methods_running_no_app_code() {
  auto methods = get_pure_methods();
  insert_unordered_iterable(
      methods, kotlin_nullcheck_wrapper::get_trusted_kotlin_null_assertions());
  methods.insert(method::java_lang_Object_ctor());
  if (auto* enum_ctor = get_enum_ctor()) {
    methods.insert(enum_ctor);
  }
  return methods;
}

} // namespace

ConstantReadSummaries::ConstantReadSummaries(
    const method_override_graph::Graph& override_graph)
    : m_override_graph(override_graph),
      m_runs_no_app_code(methods_running_no_app_code()) {}

bool ConstantReadSummaries::add_callees(
    const IRInstruction* call, std::vector<const DexMethod*>* callees) const {
  auto* ref = call->has_method() ? call->get_method() : nullptr;
  if (ref == nullptr) {
    // An `invoke-custom` names a call site, not a method.
    return false;
  }
  // An array's `clone()` has no definition and runs no app code.
  if (local_pointers::is_array_clone(ref)) {
    return true;
  }
  // A call that does not dispatch runs exactly the method its reference names,
  // so a trusted one runs no app code even when Redex has no definition of it.
  const bool dispatches = opcode::is_invoke_virtual(call->opcode()) ||
                          opcode::is_invoke_interface(call->opcode());
  if (!dispatches && m_runs_no_app_code.count(ref) != 0u) {
    return true;
  }
  // Method refs name their definitions (ResolveRefsPass runs first), so no
  // resolution here.
  auto* def = ref->as_def();
  if (def == nullptr) {
    return false;
  }
  auto is_trusted = [&](const DexMethod* method) {
    return m_runs_no_app_code.count(const_cast<DexMethodRef*>(
               static_cast<const DexMethodRef*>(method))) != 0u;
  };
  // A method whose code may not be what runs can run anything.
  auto add = [&](const DexMethod* callee) {
    if (is_trusted(callee)) {
      return true;
    }
    if (callee->rstate.no_optimizations() || callee->is_external() ||
        callee->get_code() == nullptr) {
      return false;
    }
    callees->push_back(callee);
    return true;
  };
  if (!dispatches || !def->is_virtual()) {
    return add(def);
  }
  // A virtual call runs the base method or any override, including a default
  // method of a sub-interface, as Purity decides: an abstract one runs nothing
  // itself, and an interface method that a runtime proxy may implement, like an
  // external one, may run anything.
  auto add_dispatched = [&](const DexMethod* method) {
    if (is_trusted(method)) {
      return true;
    }
    switch (get_base_or_overriding_method_action(
        method, /* methods_to_ignore */ nullptr,
        /* ignore_methods_with_assumenosideeffects */ false)) {
    case MethodOverrideAction::UNKNOWN:
      return false;
    case MethodOverrideAction::EXCLUDE:
      return true;
    case MethodOverrideAction::INCLUDE:
      return add(method);
    }
    not_reached();
  };
  return add_dispatched(def) && method_override_graph::all_overriding_methods(
                                    m_override_graph, def, add_dispatched,
                                    /* include_interfaces */ true);
}

ConstantReadSummaries::Body ConstantReadSummaries::scan(
    const DexMethod* method) {
  Body body;
  body.own.emplace();
  const auto* code = method->get_code();
  always_assert(code != nullptr && code->cfg_built());
  for (const auto& mie : cfg::ConstInstructionIterable(code->cfg())) {
    auto* insn = mie.insn;
    add_constants_read(insn, &*body.own);
    const bool is_call = opcode::is_a_method_invoke(insn->opcode()) ||
                         insn->opcode() == OPCODE_INVOKE_CUSTOM ||
                         insn->opcode() == OPCODE_INVOKE_POLYMORPHIC;
    if (is_call && !add_callees(insn, &body.callees)) {
      body.own.reset();
      body.callees.clear();
      return body;
    }
  }
  return body;
}

void ConstantReadSummaries::compute(const DexMethod* root) {
  // Scan every method reached from `root` that has no summary yet. Methods
  // that call each other need each other's summaries, so compute them
  // together, by taking what each one reads and adding what its callees read
  // until nothing changes.
  UnorderedMap<const DexMethod*, Body> bodies;
  std::vector<const DexMethod*> work{root};
  while (!work.empty()) {
    const auto* method = work.back();
    work.pop_back();
    if (m_summaries.get(method) != nullptr || bodies.count(method) != 0u) {
      continue;
    }
    auto body = scan(method);
    for (const auto* callee : body.callees) {
      work.push_back(callee);
    }
    bodies.emplace(method, std::move(body));
  }
  UnorderedMap<const DexMethod*, Summary> computed;
  for (auto& [method, body] : UnorderedIterable(bodies)) {
    computed.emplace(method, body.own);
  }
  for (bool changed = true; changed;) {
    changed = false;
    for (auto& [method, body] : UnorderedIterable(bodies)) {
      auto& summary = computed.at(method);
      if (!summary) {
        continue;
      }
      for (const auto* callee : body.callees) {
        const auto* stored = m_summaries.get(callee);
        const auto& callee_summary =
            stored != nullptr ? *stored : computed.at(callee);
        if (!callee_summary) {
          summary.reset();
          changed = true;
          break;
        }
        for (const auto* field : UnorderedIterable(*callee_summary)) {
          changed |= summary->insert(field).second;
        }
      }
    }
  }
  for (auto& [method, summary] : UnorderedIterable(computed)) {
    m_summaries.emplace(method, std::move(summary));
  }
}

const ConstantReadSummaries::Summary& ConstantReadSummaries::of(
    const DexMethod* method) {
  if (const auto* summary = m_summaries.get(method)) {
    return *summary;
  }
  compute(method);
  const auto* summary = m_summaries.get(method);
  always_assert(summary != nullptr);
  return *summary;
}

bool ConstantReadSummaries::call_may_read(
    const IRInstruction* call, const UnorderedSet<const DexField*>& constants) {
  std::vector<const DexMethod*> callees;
  if (!add_callees(call, &callees)) {
    return true;
  }
  for (const auto* callee : callees) {
    const auto& summary = of(callee);
    if (!summary || unordered_any_of(*summary, [&](const DexField* field) {
          return constants.count(field) != 0u;
        })) {
      return true;
    }
  }
  return false;
}

EnumAttributes analyze_enum_clinit(const DexClass* cls,
                                   const bool support_kt_19_enum_entries,
                                   ConstantReadSummaries* reads) {
  always_assert(is_enum(cls));

  auto* code = cls->get_clinit()->get_code();
  always_assert(code->cfg_built());
  auto& cfg = code->cfg();
  // The analysis cannot model such calls in <clinit> or in the constructors it
  // follows, so it leaves the enum unanalyzed.
  const auto& ctors = cls->get_ctors();
  if (calls_method_handle(cls->get_clinit()) ||
      std::any_of(ctors.begin(), ctors.end(), calls_method_handle)) {
    TRACE(ENUM, 2, "\t%s makes a method handle call", SHOW(cls));
    return EnumAttributes();
  }
  auto fp_iter = std::make_unique<cp::intraprocedural::FixpointIterator>(
      cfg,
      CombinedAnalyzer(cls->get_type(), nullptr, nullptr, nullptr, nullptr,
                       nullptr));
  fp_iter->run(ConstantEnvironment());

  // XXX we can't use collect_return_state below because it doesn't capture the
  // field environment. We should consider doing away with the field environment
  // and using the heap to model static field values as well, which would
  // simplify code like this.
  auto return_env = ConstantEnvironment::bottom();
  for (cfg::Block* b : cfg.blocks()) {
    auto env = fp_iter->get_entry_state_at(b);
    auto last_insn = b->get_last_insn();
    for (auto& mie : InstructionIterable(b)) {
      auto* insn = mie.insn;
      if (may_read_unassigned_constant(cls, insn, env, reads)) {
        TRACE(ENUM, 2, "\t%s may read a constant before assigning it: %s",
              SHOW(cls), SHOW(insn));
        return EnumAttributes();
      }
      fp_iter->analyze_instruction(insn, &env, insn == last_insn->insn);
      if (opcode::is_a_return(insn->opcode())) {
        return_env.join_with(env);
      }
    }
  }

  if (!return_env.get_field_environment().is_value()) {
    return EnumAttributes();
  }
  auto* ordinal_field = get_ordinal_field();
  auto* enum_name_field = get_enum_name_field();
  EnumAttributes attributes;
  for (const auto& pair : return_env.get_field_environment().bindings()) {
    const auto* enum_sfield = pair.first;
    if (enum_sfield->get_class() != cls->get_type() ||
        !check_required_access_flags(optimize_enums::enum_field_access(),
                                     enum_sfield->get_access())) {
      continue;
    }
    auto heap_ptr = pair.second.maybe_get<AbstractHeapPointer>();
    if (!heap_ptr) {
      continue;
    }
    auto ptr = return_env.get_pointee<ConstantObjectDomain>(*heap_ptr);
    auto ordinal = ptr.get<SignedConstantDomain>(ordinal_field);
    auto ordinal_value = ordinal.get_constant();
    if (!ordinal_value) {
      continue;
    }
    if (*ordinal_value < 0) {
      TRACE(ENUM, 2, "\tNegative ordinal on %s", SHOW(enum_sfield));
      return EnumAttributes();
    }

    auto name = ptr.get<StringDomain>(enum_name_field);
    auto name_value = name.get_constant();
    if (!name_value) {
      continue;
    }

    attributes.m_constants_map[enum_sfield].ordinal =
        static_cast<int32_t>(*ordinal_value);
    attributes.m_constants_map[enum_sfield].name = *name_value;
    // A constant ordinal is read from a known allocation.
    const auto allocation = heap_ptr->get_constant();
    always_assert(allocation);
    attributes.m_constant_allocations.emplace(*allocation, enum_sfield);

    for (auto* enum_ifield : cls->get_ifields()) {
      auto env_value = ptr.get(enum_ifield);
      if (env_value.is_bottom()) {
        if (enum_ifield->get_type() == type::java_lang_String()) {
          attributes.m_field_map[enum_ifield][*ordinal_value].string_value =
              nullptr;
        } else {
          attributes.m_field_map[enum_ifield][*ordinal_value].primitive_value =
              0;
        }
        continue;
      }
      if (enum_ifield->get_type() == type::java_lang_String()) {
        if (auto string_ptr = env_value.maybe_get<SignedConstantDomain>()) {
          if (auto string_ptr_value = string_ptr->get_constant()) {
            always_assert(*string_ptr_value == 0);
            // The `Ljava/lang/String` value is a `null` constant.
            attributes.m_field_map[enum_ifield][*ordinal_value].string_value =
                nullptr;
            continue;
          }
        } else if (auto string_value = env_value.maybe_get<StringDomain>()) {
          if (auto string_const = string_value->get_constant()) {
            attributes.m_field_map[enum_ifield][*ordinal_value].string_value =
                *string_const;
            continue;
          }
        }
      } else { // `enum_ifield` is a primitive type
        if (auto primitive_value =
                env_value.maybe_get<SignedConstantDomain>()) {
          if (auto primitive_const = primitive_value->get_constant()) {
            attributes.m_field_map[enum_ifield][*ordinal_value]
                .primitive_value = *primitive_const;
            continue;
          }
        } else if (auto resource_id_value =
                       env_value.maybe_get<ConstantResourceIdDomain>()) {
          if (auto primitive_const = resource_id_value->get_constant()) {
            auto& enum_field_value =
                attributes.m_field_map[enum_ifield][*ordinal_value];
            enum_field_value.primitive_value = primitive_const->id;
            enum_field_value.is_resource_id = true;
            continue;
          }
        }
      }

      TRACE(ENUM, 9,
            "Reject enum %s because we could not find constant value of "
            "instance field %s",
            SHOW(cls), SHOW(enum_ifield));
      return EnumAttributes();
    }
  }
  if (!validate_result(cls, attributes.m_constants_map,
                       support_kt_19_enum_entries)) {
    return EnumAttributes();
  }
  // Every candidate allocation must create exactly one known constant. An
  // unrecorded site, or a recorded site in a loop, can create an extra instance
  // that the values array keeps even though no constant field does.
  loop_impl::LoopInfo loops(cfg);
  for (auto* block : cfg.blocks()) {
    for (const auto& mie : InstructionIterable(block)) {
      if (mie.insn->opcode() != OPCODE_NEW_INSTANCE ||
          mie.insn->get_type() != cls->get_type()) {
        continue;
      }
      if (attributes.m_constant_allocations.count(mie.insn) == 0 ||
          loops.get_loop_for(block) != nullptr) {
        TRACE(ENUM, 2, "\t%s creates an instance that is not a unique constant",
              SHOW(cls));
        return EnumAttributes();
      }
    }
  }
  return attributes;
}

} // namespace optimize_enums
