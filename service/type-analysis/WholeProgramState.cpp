/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "WholeProgramState.h"

#include "Debug.h"
#include "GlobalTypeAnalyzer.h"
#include "Resolver.h"
#include "Show.h"
#include "Walkers.h"

using namespace type_analyzer;

std::ostream& operator<<(std::ostream& out, const DexField& field) {
  return out << show(static_cast<const DexFieldRef*>(&field));
}

std::ostream& operator<<(std::ostream& out, const DexMethod& method) {
  return out << show(static_cast<const DexMethodRef*>(&method));
}

/* Map of method to known return type - Especially for the Boxed values. TODO
 * construct the list.*/
UnorderedMap<const char*, const char*> STATIC_METHOD_TO_TYPE_MAP = {
    {"Ljava/lang/Boolean;.valueOf:(Z)Ljava/lang/Boolean;",
     "Ljava/lang/Boolean;"},
    {"Ljava/lang/Character;.valueOf:(C)Ljava/lang/Character;",
     "Ljava/lang/Character;"},
    {"Ljava/lang/Byte;.valueOf:(B)Ljava/lang/Byte;", "Ljava/lang/Byte;"},
    {"Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;",
     "Ljava/lang/Integer;"},
    {"Ljava/lang/Long;.valueOf:(J)Ljava/lang/Long;", "Ljava/lang/Long;"},
    {"Ljava/lang/Float;.valueOf:(F)Ljava/lang/Float;", "Ljava/lang/Float;"},
    {"Ljava/lang/Double;.valueOf:(D)Ljava/lang/Double;", "Ljava/lang/Double;"},
    {"Ljava/lang/String;.valueOf:(C)Ljava/lang/String;", "Ljava/lang/String;"},
    {"Ljava/lang/String;.valueOf:(D)Ljava/lang/String;", "Ljava/lang/String;"},
    {"Ljava/lang/String;.valueOf:(F)Ljava/lang/String;", "Ljava/lang/String;"},
    {"Ljava/lang/String;.valueOf:(I)Ljava/lang/String;", "Ljava/lang/String;"},
    {"Ljava/lang/String;.valueOf:(J)Ljava/lang/String;", "Ljava/lang/String;"},
    {"Ljava/lang/String;.valueOf:(Z)Ljava/lang/String;", "Ljava/lang/String;"},
};

namespace {

bool is_reference(const DexField* field) {
  return type::is_object(field->get_type());
}

bool returns_reference(const DexMethod* method) {
  auto* rtype = method->get_proto()->get_rtype();
  return type::is_object(rtype);
}

void set_encoded_values(const DexClass* cls, DexTypeEnvironment* env) {
  for (auto* sfield : cls->get_sfields()) {
    if (sfield->is_external() || !is_reference(sfield)) {
      continue;
    }
    redex_assert(!type::is_primitive(sfield->get_type()));
    auto* value = sfield->get_static_value();
    if (value == nullptr || value->evtype() == DEVT_NULL) {
      env->set(sfield, DexTypeDomain::null());
    } else if (sfield->get_type() == type::java_lang_String() &&
               value->evtype() == DEVT_STRING) {
      env->set(sfield,
               DexTypeDomain::create_not_null(type::java_lang_String()));
    } else if (sfield->get_type() == type::java_lang_Class() &&
               value->evtype() == DEVT_TYPE) {
      env->set(sfield, DexTypeDomain::create_not_null(type::java_lang_Class()));
    } else {
      env->set(sfield, DexTypeDomain::top());
    }
  }
}

/*
 * If a static field is not populated in clinit, it is implicitly null or
 * unknown.
 */
void set_sfields_in_partition(const DexClass* cls,
                              const DexTypeEnvironment& env,
                              DexTypeFieldPartition* field_partition) {
  for (const auto& field : cls->get_sfields()) {
    if (!is_reference(field)) {
      continue;
    }
    auto domain = env.get(field);
    if (!domain.is_top()) {
      // Mark sfields as nullable
      domain.join_with(DexTypeDomain::null());
      TRACE(TYPE, 5, "%s has type %s after <clinit>", SHOW(field),
            SHOW(domain));
      always_assert(field->get_class() == cls->get_type());
    } else {
      // Other encoded value might not be fully supported.
      TRACE(TYPE, 5, "%s has unknown type after <clinit>", SHOW(field));
    }
    field_partition->set(field, std::move(domain));
  }
}

/*
 * If an instance field is not populated in ctor, it is implicitly null.
 * Note that a class can have multiple ctors. If an instance field is not
 * initialized in any ctor, it is nullable. That's why we need to join the type
 * mapping across all ctors.
 */
void set_ifields_in_partition(
    const DexClass* cls,
    const DexTypeEnvironment& env,
    const EligibleIfields& eligible_ifields,
    const bool only_aggregate_safely_inferrable_fields,
    DexTypeFieldPartition* field_partition) {
  for (const auto& field : cls->get_ifields()) {
    if (!is_reference(field) || (only_aggregate_safely_inferrable_fields &&
                                 eligible_ifields.count(field) == 0)) {
      continue;
    }
    auto domain = env.get(field);
    if (!domain.is_top()) {
      // Mark ifields as nullable
      domain.join_with(DexTypeDomain::null());
      TRACE(TYPE, 5, "%s has type %s after <init>", SHOW(field), SHOW(domain));
      always_assert(field->get_class() == cls->get_type());
    } else {
      TRACE(TYPE, 5, "%s has unknown type after <init>", SHOW(field));
    }
    field_partition->update(field, [&domain](auto* current_type) {
      current_type->join_with(domain);
    });
  }
}

bool analyze_gets_helper(const WholeProgramState* whole_program_state,
                         const IRInstruction* insn,
                         DexTypeEnvironment* env) {
  auto* field = resolve_field(insn->get_field());
  if (field == nullptr || !type::is_object(field->get_type())) {
    return false;
  }
  auto field_type = whole_program_state->get_field_type(field);
  if (field_type.is_top()) {
    return false;
  }
  env->set(RESULT_REGISTER, field_type);
  return true;
}

} // namespace

namespace type_analyzer {

WholeProgramState::WholeProgramState(
    const Scope& scope,
    const global::GlobalTypeAnalyzer& gta,
    const InsertOnlyConcurrentSet<DexMethod*>& non_true_virtuals,
    const ConcurrentSet<const DexMethod*>& any_init_reachables,
    const EligibleIfields& eligible_ifields,
    const bool only_aggregate_safely_inferrable_fields)
    : m_any_init_reachables(&any_init_reachables),
      m_only_aggregate_safely_inferrable_fields(
          only_aggregate_safely_inferrable_fields) {
  // Exclude fields we cannot correctly analyze.
  walk::fields(scope, [&](DexField* field) {
    if (!type::is_object(field->get_type())) {
      return;
    }
    // We assume that a field we cannot delete is marked by a Proguard keep rule
    // or an annotation. The reason behind is that the field is referenced by
    // non-dex code.
    if (!can_delete(field) || field->is_external() || is_volatile(field)) {
      return;
    }
    m_known_fields.emplace(field);
  });

  // TODO: revisit this for multiple callee call graph.
  // Put non-root non true virtual methods in known methods.
  for (const auto& non_true_virtual : UnorderedIterable(non_true_virtuals)) {
    if (!root(non_true_virtual) && (non_true_virtual->get_code() != nullptr)) {
      m_known_methods.emplace(non_true_virtual);
    }
  }
  walk::code(scope, [&](DexMethod* method, const IRCode&) {
    if (!method->is_virtual() && (method->get_code() != nullptr)) {
      // Put non virtual methods in known methods.
      m_known_methods.emplace(method);
    }
  });
  setup_known_method_returns();
  analyze_clinits_and_ctors(scope, gta, eligible_ifields, &m_field_partition);
  collect(scope, gta, eligible_ifields);
}

WholeProgramState::WholeProgramState(
    const Scope& scope,
    const global::GlobalTypeAnalyzer& gta,
    const InsertOnlyConcurrentSet<DexMethod*>& non_true_virtuals,
    const ConcurrentSet<const DexMethod*>& any_init_reachables,
    const EligibleIfields& eligible_ifields,
    const bool only_aggregate_safely_inferrable_fields,
    std::shared_ptr<const call_graph::Graph> call_graph)
    : WholeProgramState(scope,
                        gta,
                        non_true_virtuals,
                        any_init_reachables,
                        eligible_ifields,
                        only_aggregate_safely_inferrable_fields) {
  m_call_graph = std::move(call_graph);
}

std::string WholeProgramState::show_field(const DexField* f) { return show(f); }
std::string WholeProgramState::show_method(const DexMethod* m) {
  return show(m);
}
void WholeProgramState::setup_known_method_returns() {
  for (auto& p : UnorderedIterable(STATIC_METHOD_TO_TYPE_MAP)) {
    auto* method = DexMethod::make_method(p.first);
    auto type = DexTypeDomain::create_not_null(
        DexType::make_type(DexString::make_string(p.second)));
    m_known_method_returns.insert(std::make_pair(method, type));
  }
}

/*
 * We initialize the type mapping of all fields using the result of the local
 * FieldTypeEnvironment of clinits and ctors. We do so in order to correctly
 * initialize the NullnessDomain for fields. A static or instance field is
 * implicitly null if not initialized with non-null value in clinit or ctor
 * respectively.
 *
 * The implicit null value is not visible to the rest of the program before the
 * execution of clinit or ctor. That's why we don't want to simply initialize
 * all fields as null. That way we are overly conservative. A final instance
 * field that is always initialized in ctors is not nullable to the rest of the
 * program.
 *
 * TODO:
 * There are exceptions of course. That is before the end of the ctor, our
 * nullness result is not sound. If a ctor calls another method, that method
 * could access an uninitialiezd instance field on the class. We don't cover
 * this case correctly right now.
 */
void WholeProgramState::analyze_clinits_and_ctors(
    const Scope& scope,
    const global::GlobalTypeAnalyzer& gta,
    const EligibleIfields& eligible_ifields,
    DexTypeFieldPartition* field_partition) {

  std::mutex mutex;
  walk::parallel::classes(scope, [&](auto* cls) {
    DexTypeFieldPartition cls_field_partition;

    if (!cls->get_sfields().empty()) {
      auto clinit = cls->get_clinit();
      if (clinit) {
        IRCode* code = clinit->get_code();
        auto& cfg = code->cfg();
        auto lta = gta.get_internal_local_analysis(clinit);
        const auto& env = lta->get_exit_state_at(cfg.exit_block());
        set_sfields_in_partition(cls, env, &cls_field_partition);
      } else {
        DexTypeEnvironment env;
        set_encoded_values(cls, &env);
        set_sfields_in_partition(cls, env, &cls_field_partition);
      }
    }

    const auto& ctors = cls->get_ctors();
    for (auto* ctor : ctors) {
      if (!is_reachable(gta, ctor) || !ctor->get_code()) {
        continue;
      }
      IRCode* code = ctor->get_code();
      auto& cfg = code->cfg();
      auto lta = gta.get_internal_local_analysis(ctor);
      const auto& env = lta->get_exit_state_at(cfg.exit_block());
      set_ifields_in_partition(cls, env, eligible_ifields,
                               m_only_aggregate_safely_inferrable_fields,
                               &cls_field_partition);
    }

    std::lock_guard<std::mutex> lock_guard(mutex);
    field_partition->join_with(cls_field_partition);
  });
}

void WholeProgramState::collect(const Scope& scope,
                                const global::GlobalTypeAnalyzer& gta,
                                const EligibleIfields& eligible_ifields) {
  ConcurrentMap<const DexField*, DexTypeDomain> fields_tmp;
  ConcurrentMap<const DexMethod*, DexTypeDomain> methods_tmp;

  walk::parallel::methods(scope, [&](DexMethod* method) {
    IRCode* code = method->get_code();
    if (code == nullptr) {
      return;
    }
    if (!is_reachable(gta, method)) {
      return;
    }
    auto& cfg = code->cfg();
    auto lta = gta.get_internal_local_analysis(method);
    for (cfg::Block* b : cfg.blocks()) {
      auto env = lta->get_entry_state_at(b);
      for (auto& mie : InstructionIterable(b)) {
        auto* insn = mie.insn;
        lta->analyze_instruction(insn, &env);
        collect_field_types(insn, env, eligible_ifields, &fields_tmp);
        collect_return_types(insn, env, method, &methods_tmp);
      }
    }
  });
  for (const auto& pair : UnorderedIterable(fields_tmp)) {
    m_field_partition.update(pair.first, [&pair](auto* current_type) {
      current_type->join_with(pair.second);
    });
  }
  for (const auto& pair : UnorderedIterable(methods_tmp)) {
    m_method_partition.update(pair.first, [&pair](auto* current_type) {
      current_type->join_with(pair.second);
    });
  }
}

void WholeProgramState::collect_field_types(
    const IRInstruction* insn,
    const DexTypeEnvironment& env,
    const EligibleIfields& eligible_ifields,
    ConcurrentMap<const DexField*, DexTypeDomain>* field_tmp) {
  for_each_field_access(insn, [&](IROpcode op, DexFieldRef* field_ref,
                                  const DexMethodHandle* method_handle) {
    if (!opcode::is_an_sput(op) && !opcode::is_an_iput(op)) {
      return;
    }
    auto* field = method_handle == nullptr
                      ? resolve_field(field_ref)
                      : resolve_field_handle(method_handle);
    if ((field == nullptr) || !type::is_object(field->get_type())) {
      return;
    }
    if (opcode::is_an_iput(op) && m_only_aggregate_safely_inferrable_fields &&
        eligible_ifields.count(field) == 0) {
      // Skip writes to non-eligible instance fields.
      return;
    }
    // A method handle that puts a field can be called anywhere, with any value.
    auto type =
        method_handle == nullptr ? env.get(insn->src(0)) : DexTypeDomain::top();
    if (traceEnabled(TYPE, 5)) {
      std::ostringstream ss;
      ss << type;
      TRACE(TYPE, 5, "collecting field %s -> %s", SHOW(field),
            ss.str().c_str());
    }
    field_tmp->update(
        field,
        [&type](const DexField*, DexTypeDomain& current_type, bool exists) {
          if (exists) {
            current_type.join_with(type);
          } else {
            current_type = std::move(type);
          }
        });
  });
}

void WholeProgramState::collect_return_types(
    const IRInstruction* insn,
    const DexTypeEnvironment& env,
    const DexMethod* method,
    ConcurrentMap<const DexMethod*, DexTypeDomain>* method_tmp) {
  auto op = insn->opcode();
  if (!opcode::is_a_return(op)) {
    return;
  }
  if (!returns_reference(method)) {
    // We must set the binding to Top here to record the fact that this method
    // does indeed return -- even though `void` is not actually a return type,
    // this tells us that the code following any invoke of this method is
    // reachable.
    method_tmp->update(
        method,
        [](const DexMethod*, DexTypeDomain& current_type, bool /* exists */) {
          current_type = DexTypeDomain::top();
        });
    return;
  }
  auto type = env.get(insn->src(0));
  if (traceEnabled(TYPE, 5)) {
    std::ostringstream ss;
    ss << type;
    TRACE(TYPE, 5, "collecting method %s -> %s", SHOW(method),
          ss.str().c_str());
  }
  method_tmp->update(method, [&type](const DexMethod*,
                                     DexTypeDomain& current_type, bool exists) {
    if (exists) {
      current_type.join_with(type);
    } else {
      current_type = std::move(type);
    }
  });
}

bool WholeProgramState::is_reachable(const global::GlobalTypeAnalyzer& gta,
                                     const DexMethod* method) const {
  return (m_known_methods.count(method) == 0u) || gta.is_reachable(method);
}

std::string WholeProgramState::print_field_partition_diff(
    const WholeProgramState& other) const {
  std::ostringstream ss;
  if (m_field_partition.is_top()) {
    ss << "[wps] diff this < is top" << '\n';
    return ss.str();
  }
  if (other.m_field_partition.is_top()) {
    ss << "[wps] diff other > is top" << '\n';
    return ss.str();
  }
  const auto& this_field_bindings = m_field_partition.bindings();
  const auto& other_field_bindings = other.m_field_partition.bindings();
  for (const auto& pair : this_field_bindings) {
    const auto* field = pair.first;
    if (other_field_bindings.count(field) == 0u) {
      ss << "[wps] diff " << field << " < " << pair.second << '\n';
    } else {
      const auto& this_type = pair.second;
      const auto& other_type = other_field_bindings.at(field);
      if (!this_type.equals(other_type)) {
        ss << "[wps] diff " << field << " < " << this_type << " > "
           << other_type << '\n';
      }
    }
  }
  for (const auto& pair : other_field_bindings) {
    const auto* field = pair.first;
    if (this_field_bindings.count(field) == 0u) {
      ss << "[wps] diff " << field << " > " << pair.second << '\n';
    }
  }

  return ss.str();
}

std::string WholeProgramState::print_method_partition_diff(
    const WholeProgramState& other) const {
  std::ostringstream ss;
  if (m_method_partition.is_top()) {
    ss << "[wps] diff this < is top" << '\n';
    return ss.str();
  }
  if (other.m_method_partition.is_top()) {
    ss << "[wps] diff other > is top" << '\n';
    return ss.str();
  }
  const auto& this_method_bindings = m_method_partition.bindings();
  const auto& other_method_bindings = other.m_method_partition.bindings();
  for (const auto& pair : this_method_bindings) {
    const auto* method = pair.first;
    if (other_method_bindings.count(method) == 0u) {
      ss << "[wps] diff " << method << " < " << pair.second << '\n';
    } else {
      const auto& this_type = pair.second;
      const auto& other_type = other_method_bindings.at(method);
      if (!this_type.equals(other_type)) {
        ss << "[wps] diff " << method << " < " << this_type << " > "
           << other_type << '\n';
      }
    }
  }
  for (const auto& pair : other_method_bindings) {
    const auto* method = pair.first;
    if (this_method_bindings.count(method) == 0u) {
      ss << "[wps] diff " << method << " > " << pair.second << '\n';
    }
  }

  return ss.str();
}

bool WholeProgramAwareAnalyzer::analyze_iget(
    const WholeProgramState* whole_program_state,
    const IRInstruction* insn,
    DexTypeEnvironment* env) {
  return analyze_gets_helper(whole_program_state, insn, env);
}

bool WholeProgramAwareAnalyzer::analyze_sget(
    const WholeProgramState* whole_program_state,
    const IRInstruction* insn,
    DexTypeEnvironment* env) {
  return analyze_gets_helper(whole_program_state, insn, env);
}

bool WholeProgramAwareAnalyzer::analyze_invoke(
    const WholeProgramState* whole_program_state,
    const IRInstruction* insn,
    DexTypeEnvironment* env) {
  if (whole_program_state == nullptr) {
    return false;
  }
  auto known_type = whole_program_state->get_type_for_method_with_known_type(
      insn->get_method());
  if (known_type) {
    env->set(RESULT_REGISTER, *known_type);
    return false;
  }

  if (whole_program_state->has_call_graph()) {
    if (whole_program_state->invoke_is_dynamic(insn)) {
      env->set(RESULT_REGISTER, DexTypeDomain::top());
      return false;
    }
    auto type = whole_program_state->get_return_type_from_cg(insn);
    env->set(RESULT_REGISTER, type);
    return true;
  }

  auto* method =
      resolve_method_deprecated(insn->get_method(), opcode_to_search(insn));
  if (method == nullptr || !returns_reference(method)) {
    // Reset RESULT_REGISTER
    env->set(RESULT_REGISTER, DexTypeDomain::top());
    return false;
  }
  auto type = whole_program_state->get_return_type(method);
  env->set(RESULT_REGISTER, type);
  return false;
}

} // namespace type_analyzer
