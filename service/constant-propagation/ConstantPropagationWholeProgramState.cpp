/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ConstantPropagationWholeProgramState.h"

#include "Debug.h"
#include "IPConstantPropagationAnalysis.h"
#include "Resolver.h"
#include "Trace.h"
#include "Walkers.h"

using namespace constant_propagation;

namespace {

/*
 * Walk all the static or instance fields in :cls, copying their bindings in
 * :field_env over to :field_partition.
 */
void set_fields_in_partition(const DexClass* cls,
                             const FieldEnvironment& field_env,
                             const FieldType& field_type,
                             ConstantFieldPartition* field_partition) {
  // Note that we *must* iterate over the list of fields in the class and not
  // the bindings in field_env here. This ensures that fields whose values are
  // unknown (and therefore implicitly represented by Top in the field_env)
  // get correctly bound to Top in field_partition (which defaults its
  // bindings to Bottom).
  const auto& fields =
      field_type == FieldType::STATIC ? cls->get_sfields() : cls->get_ifields();
  for (const auto& field : fields) {
    auto value = field_env.get(field);
    if (!value.is_top()) {
      TRACE(ICONSTP, 2, "%s has value %s after <clinit> or <init>", SHOW(field),
            SHOW(value));
      always_assert(field->get_class() == cls->get_type());
    } else {
      TRACE(ICONSTP, 2, "%s has unknown value after <clinit> or <init>",
            SHOW(field));
    }
    field_partition->set(field, std::move(value));
  }
}

/*
 * Record in :field_partition the values of the static fields after the class
 * initializers have finished executing.
 *
 * XXX this assumes that there are no cycles in the class initialization graph!
 */
void analyze_clinits(const Scope& scope,
                     const interprocedural::FixpointIterator& fp_iter,
                     ConstantFieldPartition* field_partition) {
  std::mutex mutex;
  walk::parallel::classes(scope, [&](auto* cls) {
    if (cls->get_sfields().empty()) {
      return;
    }
    ConstantFieldPartition cls_field_partition;
    auto clinit = cls->get_clinit();
    if (clinit == nullptr) {
      // If there is no class initializer, then the initial field values are
      // simply the DexEncodedValues.
      ConstantEnvironment env;
      set_encoded_values(cls, &env);
      set_fields_in_partition(cls, env.get_field_environment(),
                              FieldType::STATIC, &cls_field_partition);
    } else {
      IRCode* code = clinit->get_code();
      auto& cfg = code->cfg();
      auto ipa = fp_iter.get_intraprocedural_analysis(clinit);
      const auto& env = ipa->fp_iter.get_exit_state_at(cfg.exit_block());
      set_fields_in_partition(cls, env.get_field_environment(),
                              FieldType::STATIC, &cls_field_partition);
    }
    std::lock_guard<std::mutex> lock_guard(mutex);
    field_partition->join_with(cls_field_partition);
  });
}

// Returns the whole-program value of the field that `insn` reads (Bottom if it
// never holds a value), or Top.
ConstantValue get_read_field_value(
    const WholeProgramStateAccessor* whole_program_state,
    const IRInstruction* insn) {
  if (whole_program_state == nullptr) {
    return ConstantValue::top();
  }
  auto* field = resolve_field(insn->get_field());
  if (field == nullptr) {
    return ConstantValue::top();
  }
  return whole_program_state->get_field_value(field);
}

// Returns the whole-program value that the method `insn` calls returns (Bottom
// if it never returns), or Top.
ConstantValue get_invoke_return_value(
    const WholeProgramStateAccessor* whole_program_state,
    const IRInstruction* insn) {
  if (whole_program_state == nullptr) {
    return ConstantValue::top();
  }
  if (whole_program_state->has_call_graph()) {
    if (whole_program_state->invoke_is_dynamic(insn)) {
      return ConstantValue::top();
    }
    return whole_program_state->get_return_value_from_cg(insn);
  }
  auto op = insn->opcode();
  if (op != OPCODE_INVOKE_DIRECT && op != OPCODE_INVOKE_STATIC &&
      op != OPCODE_INVOKE_VIRTUAL) {
    return ConstantValue::top();
  }
  auto* method =
      resolve_method_deprecated(insn->get_method(), opcode_to_search(insn));
  if (method == nullptr) {
    return ConstantValue::top();
  }
  return whole_program_state->get_return_value(method);
}

// Binds the result register to `value`, the whole-program value of the
// instruction just analyzed. Binds nothing for Top, nor for Bottom: binding
// Bottom makes the whole state Bottom, and with it the state on the
// instruction's exception edges, which the instruction can still take.
bool bind_result(const ConstantValue& value, ConstantEnvironment* env) {
  if (value.is_top() || value.is_bottom()) {
    return false;
  }
  env->set(RESULT_REGISTER, value);
  return true;
}

bool is_eligible_ifield(const DexField* field) {
  return !is_static(field) && !field->is_external() && can_delete(field) &&
         !is_volatile(field) &&
         // A transient field may be null after deserialization.
         !is_transient(field);
}

/**
 * Initialize non-external, can be deleted instance fields' value to be 0.
 */
void initialize_ifields(
    const Scope& scope,
    ConstantFieldPartition* field_partition,
    const UnorderedSet<const DexField*>& definitely_assigned_ifields) {
  walk::fields(scope, [&](DexField* field) {
    if (!is_eligible_ifield(field)) {
      return;
    }
    // For instance fields that are always written to before they are read, the
    // initial 0 value is not observable, so we don't even have to include it.
    auto value = definitely_assigned_ifields.count(field) != 0u
                     ? SignedConstantDomain::bottom()
                     : SignedConstantDomain(0);
    field_partition->set(field, std::move(value));
  });
}

/**
 * Return if a field is a root field that is not in a resource class.
 */
bool is_non_resource_root(DexField* field) {
  const auto& field_cls_name = field->get_class()->get_name()->str();
  return (field_cls_name.find("/R$") == std::string::npos) && root(field);
}

} // namespace

namespace constant_propagation {

// TODO(T275196808): Remove this once the per-parameter exit-value summary is
// fully rolled out. Declared in ConstantPropagationAnalysis.h.
bool enable_param_exit_value_summary = false;

WholeProgramState::WholeProgramState(
    const Scope& scope,
    const interprocedural::FixpointIterator& fp_iter,
    const InsertOnlyConcurrentSet<DexMethod*>& non_true_virtuals,
    const UnorderedSet<const DexType*>& field_blocklist,
    const UnorderedSet<const DexField*>& definitely_assigned_ifields,
    std::shared_ptr<const call_graph::Graph> call_graph)
    : m_call_graph(std::move(call_graph)), m_field_blocklist(field_blocklist) {

  walk::fields(scope, [&](DexField* field) {
    // We exclude those marked by keep rules: keep-marked fields may be
    // written to by non-Dex bytecode.
    // All fields not in m_known_fields will be bound to Top.
    if (field_blocklist.count(field->get_class()) != 0u) {
      return;
    }
    const bool is_non_root_static_field = is_static(field) && !root(field);
    if (is_non_root_static_field || is_eligible_ifield(field)) {
      m_known_fields.emplace(field);
    }
  });
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
  analyze_clinits(scope, fp_iter, &m_field_partition);
  collect(scope, fp_iter, definitely_assigned_ifields);
}

/*
 * Walk over the entire program, doing a join over the values written to each
 * field, as well as a join over the values returned by each method.
 */
void WholeProgramState::collect(
    const Scope& scope,
    const interprocedural::FixpointIterator& fp_iter,
    const UnorderedSet<const DexField*>& definitely_assigned_ifields) {
  initialize_ifields(scope, &m_field_partition, definitely_assigned_ifields);
  ConcurrentMap<const DexField*, ConstantValue> fields_value_tmp;
  ConcurrentMap<const DexMethod*, ConstantValue> methods_value_tmp;
  ConcurrentMap<const DexMethod*, MethodParamEnv> methods_param_env_tmp;
  walk::parallel::methods(scope, [&](DexMethod* method) {
    IRCode* code = method->get_code();
    if (code == nullptr) {
      return;
    }
    auto& cfg = code->cfg();
    auto ipa = fp_iter.get_intraprocedural_analysis(method);
    auto& intra_cp = ipa->fp_iter;
    // Param registers in declaration order. Each load-param's dest reg holds
    // the corresponding entry value at method entry.
    std::vector<reg_t> param_regs;
    UnorderedSet<reg_t> stable_param_regs;
    // TODO(T275196808): Remove this guard once the feature is fully rolled out.
    if (enable_param_exit_value_summary) {
      for (const auto& mie :
           InstructionIterable(code->get_param_instructions())) {
        param_regs.push_back(mie.insn->dest());
        stable_param_regs.insert(mie.insn->dest());
      }
      // Pre-pass: a param register is "stable" only if no non-load-param
      // instruction ever writes to it. For unstable regs, the value at a
      // RETURN does not necessarily reflect the entry value (the param may
      // have been reassigned), so we cannot derive a "caller passed X"
      // precondition from "register is X at exit".
      //
      // This stability test is deliberately flow-insensitive: one write
      // anywhere drops the param everywhere. A more precise version is possible
      // and sound -- snapshot the param's value just before its first
      // overwrite (it still holds the entry value there), and at each RETURN
      // use only the value carried along paths that have not yet overwritten
      // the register. But that requires tracking, per param and at every
      // program point, the param's value reset to Bottom once its register is
      // reassigned -- a forward dataflow that must also reproduce CP's own
      // refinements (e.g. non-null from a dereference), so it would have to
      // live inside the shared ConstantEnvironment reduced product or duplicate
      // CP's transfer functions.
      for (cfg::Block* b : cfg.blocks()) {
        for (const auto& mie : InstructionIterable(b)) {
          auto* insn = mie.insn;
          if (opcode::is_a_load_param(insn->opcode())) {
            continue;
          }
          if (insn->has_dest()) {
            stable_param_regs.erase(insn->dest());
            if (insn->dest_is_wide()) {
              stable_param_regs.erase(insn->dest() + 1);
            }
          }
        }
      }
    }
    for (cfg::Block* b : cfg.blocks()) {
      auto env = intra_cp.get_entry_state_at(b);
      auto last_insn = b->get_last_insn();
      for (auto& mie : InstructionIterable(b)) {
        auto* insn = mie.insn;
        intra_cp.analyze_instruction(insn, &env, insn == last_insn->insn);
        collect_field_values(insn, env,
                             method::is_clinit(method) ? method->get_class()
                                                       : nullptr,
                             &fields_value_tmp);
        collect_return_values(insn, env, method, &methods_value_tmp);
        if (enable_param_exit_value_summary) {
          collect_param_exit_values(insn, env, method, param_regs,
                                    stable_param_regs, &methods_param_env_tmp);
        }
      }
    }
  });
  for (const auto& pair : UnorderedIterable(fields_value_tmp)) {
    m_field_partition.update(pair.first, [&pair](auto* current_value) {
      current_value->join_with(pair.second);
    });
  }
  for (const auto& pair : UnorderedIterable(methods_value_tmp)) {
    m_method_partition.update(pair.first, [&pair](auto* current_value) {
      current_value->join_with(pair.second);
    });
  }
  for (auto& pair : UnorderedIterable(methods_param_env_tmp)) {
    m_method_param_partition.set(pair.first, std::move(pair.second));
  }
}

/*
 * For each field, do a join over all the values that may have been
 * written to it at any point in the program.
 *
 * If we are encountering a static field write of some value to Foo.someField
 * in the body of Foo.<clinit>, don't do anything -- that value will only be
 * visible to other methods if it remains unchanged up until the end of the
 * <clinit>. In that case, analyze_clinits() will record it.
 */
void WholeProgramState::collect_field_values(
    const IRInstruction* insn,
    const ConstantEnvironment& env,
    const DexType* clinit_cls,
    ConcurrentMap<const DexField*, ConstantValue>* fields_value_tmp) {
  if (!opcode::is_an_sput(insn->opcode()) &&
      !opcode::is_an_iput(insn->opcode())) {
    return;
  }
  auto* field = resolve_field(insn->get_field());
  if (field != nullptr && (m_known_fields.count(field) != 0u)) {
    if (opcode::is_an_sput(insn->opcode()) &&
        field->get_class() == clinit_cls) {
      return;
    }
    auto value = env.get(insn->src(0));
    fields_value_tmp->update(
        field,
        [&value](const DexField*, ConstantValue& current_value, bool exists) {
          if (exists) {
            current_value.join_with(value);
          } else {
            current_value = std::move(value);
          }
        });
  }
}

/*
 * For each method, do a join over all the values that can be returned by it.
 *
 * If there are no reachable return opcodes in the method, then it never
 * returns. Its return value will be represented by Bottom in our analysis.
 */
void WholeProgramState::collect_return_values(
    const IRInstruction* insn,
    const ConstantEnvironment& env,
    const DexMethod* method,
    ConcurrentMap<const DexMethod*, ConstantValue>* methods_value_tmp) {
  auto op = insn->opcode();
  if (!opcode::is_a_return(op)) {
    return;
  }
  if (op == OPCODE_RETURN_VOID) {
    // We must set the binding to Top here to record the fact that this method
    // does indeed return -- even though `void` is not actually a return value,
    // this tells us that the code following any invoke of this method is
    // reachable.
    methods_value_tmp->update(
        method,
        [](const DexMethod*, ConstantValue& current_value, bool /* exists */) {
          current_value = ConstantValue::top();
        });
    return;
  }
  auto value = env.get(insn->src(0));
  methods_value_tmp->update(
      method,
      [&value](const DexMethod*, ConstantValue& current_value, bool exists) {
        if (exists) {
          current_value.join_with(value);
        } else {
          current_value = std::move(value);
        }
      });
}

/*
 * Build a per-param env at one normal exit of :method (using stable param
 * registers only) and join it into the running per-method binding. Across
 * exits, this gives the join of env values at every reachable normal exit
 * -- the abstract value the caller-passed argument MUST belong to whenever
 * the call returns normally.
 */
void WholeProgramState::collect_param_exit_values(
    const IRInstruction* insn,
    const ConstantEnvironment& env,
    const DexMethod* method,
    const std::vector<reg_t>& param_regs,
    const UnorderedSet<reg_t>& stable_param_regs,
    ConcurrentMap<const DexMethod*, MethodParamEnv>* methods_param_env_tmp) {
  if (!opcode::is_a_return(insn->opcode())) {
    return;
  }
  // Skip unreachable returns.
  if (env.is_bottom()) {
    return;
  }
  MethodParamEnv exit_env;
  for (param_index_t i = 0; i < param_regs.size(); ++i) {
    // Only stable param registers preserve the entry value at exit. For
    // reassigned params, the exit value does not reflect what the caller
    // passed in; leave the binding at top so the caller cannot refine.
    if (stable_param_regs.count(param_regs[i]) == 0) {
      continue;
    }
    exit_env.set(i, env.get(param_regs[i]));
  }
  methods_param_env_tmp->update(
      method,
      [&exit_env](const DexMethod*, MethodParamEnv& current, bool exists) {
        if (!exists) {
          current = std::move(exit_env);
        } else {
          current.join_with(exit_env);
        }
      });
}

void WholeProgramState::collect_static_finals(const DexClass* cls,
                                              FieldEnvironment field_env) {
  for (auto* field : cls->get_sfields()) {
    if (is_static(field) && !is_non_resource_root(field) && is_final(field) &&
        !field->is_external() &&
        m_field_blocklist.count(field->get_class()) == 0) {
      m_known_fields.emplace(field);
    } else {
      field_env.set(field, ConstantValue::top());
    }
  }
  set_fields_in_partition(cls, field_env, FieldType::STATIC,
                          &m_field_partition);
}

void WholeProgramState::collect_instance_finals(
    const DexClass* cls,
    const EligibleIfields& eligible_ifields,
    FieldEnvironment field_env) {
  always_assert(!cls->is_external());
  if (cls->get_ctors().size() > 1) {
    // Not dealing with instance field in class not having exact 1 constructor
    // now. TODO(suree404): Might be able to improve?
    for (auto* field : cls->get_ifields()) {
      field_env.set(field, ConstantValue::top());
    }
  } else {
    for (auto* field : cls->get_ifields()) {
      if ((eligible_ifields.count(field) != 0u) &&
          m_field_blocklist.count(field->get_class()) == 0) {
        m_known_fields.emplace(field);
      } else {
        field_env.set(field, ConstantValue::top());
      }
    }
  }
  set_fields_in_partition(cls, field_env, FieldType::INSTANCE,
                          &m_field_partition);
}

bool WholeProgramAwareAnalyzer::analyze_sget(
    const WholeProgramStateAccessor* whole_program_state,
    const IRInstruction* insn,
    ConstantEnvironment* env) {
  return bind_result(get_read_field_value(whole_program_state, insn), env);
}

bool WholeProgramAwareAnalyzer::analyze_iget(
    const WholeProgramStateAccessor* whole_program_state,
    const IRInstruction* insn,
    ConstantEnvironment* env) {
  return bind_result(get_read_field_value(whole_program_state, insn), env);
}

bool WholeProgramAwareAnalyzer::analyze_invoke(
    const WholeProgramStateAccessor* whole_program_state,
    const IRInstruction* insn,
    ConstantEnvironment* env) {
  return bind_result(get_invoke_return_value(whole_program_state, insn), env);
}

namespace {

// Refines an invoke's source registers from the IPCP per-(method, param)
// exit-value summary on the no-throw edge. Composed before
// DefaultNoThrowAnalyzer so the hardcoded null-check facts still apply
// afterward.
class WpsAwareNoThrowAnalyzer final
    : public InstructionAnalyzerBase<WpsAwareNoThrowAnalyzer,
                                     ConstantEnvironment,
                                     const WholeProgramStateAccessor*> {
 public:
  static bool analyze_invoke(const WholeProgramStateAccessor* wps_accessor,
                             const IRInstruction* insn,
                             ConstantEnvironment* env) {
    // TODO(T275196808): Remove the `enable_param_exit_value_summary` guard once
    // the feature is fully rolled out.
    if (!enable_param_exit_value_summary || wps_accessor == nullptr) {
      return false;
    }
    auto op = insn->opcode();
    // Refine only when the callee is statically known. With a call graph,
    // that is non-dynamic dispatch (the graph resolves the callee set);
    // otherwise the statically-dispatched opcodes plus invoke-virtual -- an
    // overridable callee yields a top summary, so nothing unsound is applied.
    std::optional<MethodParamEnv> param_env;
    if (wps_accessor->has_call_graph()) {
      if (!wps_accessor->invoke_is_dynamic(insn)) {
        param_env = wps_accessor->get_method_param_env_from_cg(insn);
      }
    } else if (op == OPCODE_INVOKE_STATIC || op == OPCODE_INVOKE_DIRECT ||
               op == OPCODE_INVOKE_SUPER || op == OPCODE_INVOKE_VIRTUAL) {
      auto* method = resolve_method(insn->get_method(), opcode_to_search(insn));
      if (method != nullptr) {
        // get_method_param_env yields top for overridable virtuals.
        param_env = wps_accessor->get_method_param_env(method);
      }
    }
    if (param_env) {
      assert_log(
          !insn->has_dest(),
          "invoke has no dest in Redex IR (result is on the following "
          "move-result*); every src is an argument, so all are refined here");
      for (size_t i = 0; i < insn->srcs_size(); ++i) {
        auto src = insn->src(i);
        auto value = env->get(src);
        value.meet_with(param_env->get(i));
        env->set(src, value);
      }
    }
    return false;
  }
};

} // namespace

InstructionAnalyzer<ConstantEnvironment> make_wps_aware_no_throw_analyzer(
    const NullCheckMethods* null_check_methods,
    const WholeProgramStateAccessor* wps_accessor) {
  // WpsAwareNoThrowAnalyzer applies the WPS-driven refinement first, then
  // DefaultNoThrowAnalyzer applies the hardcoded null-check facts.
  return InstructionAnalyzerCombiner<WpsAwareNoThrowAnalyzer,
                                     intraprocedural::DefaultNoThrowAnalyzer>(
      wps_accessor, null_check_methods);
}

} // namespace constant_propagation
