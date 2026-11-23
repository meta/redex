/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ResultPropagation.h"

#include <vector>

#include <sparta/ConstantAbstractDomain.h>
#include <sparta/PatriciaTreeMapAbstractEnvironment.h>

#include "BaseIRAnalyzer.h"
#include "ControlFlow.h"
#include "Debug.h"
#include "DexUtil.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "PassManager.h"
#include "Resolver.h"
#include "Show.h"
#include "Trace.h"
#include "TypeUtil.h"
#include "Walkers.h"

using namespace sparta;

namespace {

constexpr const char* METRIC_METHODS_WHICH_RETURN_PARAMETER =
    "num_methods_which_return_parameters";
constexpr const char* METRIC_ERASED_MOVE_RESULTS = "num_erased_move_results";
constexpr const char* METRIC_PATCHED_MOVE_RESULTS = "num_patched_move_results";
constexpr const char* METRIC_UNVERIFIABLE_MOVE_RESULTS =
    "num_unverifiable_move_results";
constexpr const char* METRIC_METHODS_WHICH_RETURN_PARAMETER_ITERATIONS =
    "num_methods_which_return_parameters_iterations";
constexpr const ParamIndex WIDE_HIGH = 1u << 31;

void patch_move_result_to_move(IRInstruction* move_result_inst, reg_t reg) {
  const auto op = move_result_inst->opcode();
  move_result_inst->set_opcode(opcode::move_result_to_move(op));
  move_result_inst->set_srcs_size(1);
  move_result_inst->set_src(0, reg);
}

const DexType* get_param_type(bool is_static,
                              const DexMethodRef* method,
                              ParamIndex param_index) {
  if (!is_static && param_index-- == 0) {
    return method->get_class();
  }
  const auto* args = method->get_proto()->get_args();
  return args->at(param_index);
}

using namespace ir_analyzer;

using ParamDomain = sparta::ConstantAbstractDomain<ParamIndex>;

/**
 * For each register that holds an reference to a param
 * keeps track of the param index.
 **/
using ParamDomainEnvironment =
    sparta::PatriciaTreeMapAbstractEnvironment<reg_t, ParamDomain>;

// We use this special register to denote the value that is being returned.
reg_t RETURN_VALUE = RESULT_REGISTER - 1;

bool isNotHigh(const ParamDomain& domain) {
  auto const constant = domain.get_constant();
  return !constant || (((*constant) & WIDE_HIGH) == 0);
}

ParamDomain makeHigh(const ParamDomain& domain) {
  always_assert(isNotHigh(domain));
  auto const constant = domain.get_constant();
  return constant ? ParamDomain((*constant) | WIDE_HIGH) : domain;
}

class Analyzer final : public BaseIRAnalyzer<ParamDomainEnvironment> {

 public:
  Analyzer(const cfg::ControlFlowGraph& cfg,
           const ReturnParamResolver& resolver,
           const UnorderedMap<const DexMethod*, ParamIndex>&
               methods_which_return_parameter)
      : BaseIRAnalyzer(cfg),
        m_resolver(resolver),
        m_methods_which_return_parameter(methods_which_return_parameter),
        m_load_param_map(get_load_param_map(cfg)) {
    MonotonicFixpointIterator::run(ParamDomainEnvironment::top());
  }

  void analyze_instruction(
      const IRInstruction* insn,
      ParamDomainEnvironment* current_state) const override {

    // While the special registers RESULT_REGISTER and RETURN_VALUE do not
    // participate in possible wide low and high register splitting, all
    // other registers should be accessed through the following two helper
    // functions to ensure that wide values are properly handled.

    const auto get_current_state_at = [&](reg_t reg, bool wide) {
      const auto& low = current_state->get(reg);
      if (!wide) {
        return isNotHigh(low) ? low : ParamDomain::top();
      }
      const auto high = current_state->get(reg + 1);
      return (isNotHigh(low) && makeHigh(low) == high) ? low
                                                       : ParamDomain::top();
    };

    const auto set_current_state_at = [&](reg_t reg, bool wide,
                                          const ParamDomain& value) {
      always_assert(isNotHigh(value));
      current_state->set(reg, value);
      if (wide) {
        current_state->set(reg + 1, makeHigh(value));
      }
    };

    const auto default_case = [&]() {
      // If we get here, reset destination.
      if (insn->has_dest()) {
        set_current_state_at(insn->dest(), insn->dest_is_wide(),
                             ParamDomain::top());
      } else if (insn->has_move_result_any()) {
        current_state->set(RESULT_REGISTER, ParamDomain::top());
      }
    };

    switch (insn->opcode()) {
    case OPCODE_RETURN:
    case OPCODE_RETURN_OBJECT:
    case OPCODE_RETURN_WIDE: {
      const auto value =
          get_current_state_at(insn->src(0), insn->src_is_wide(0));
      current_state->set(RETURN_VALUE, value);
      break;
    }

    case OPCODE_MOVE:
    case OPCODE_MOVE_OBJECT:
    case OPCODE_MOVE_WIDE: {
      const auto value =
          get_current_state_at(insn->src(0), insn->src_is_wide(0));
      set_current_state_at(insn->dest(), insn->dest_is_wide(), value);
      break;
    }

    case IOPCODE_MOVE_RESULT_PSEUDO:
    case IOPCODE_MOVE_RESULT_PSEUDO_OBJECT:
    case IOPCODE_MOVE_RESULT_PSEUDO_WIDE:
    case OPCODE_MOVE_RESULT:
    case OPCODE_MOVE_RESULT_OBJECT:
    case OPCODE_MOVE_RESULT_WIDE: {
      const auto& value = current_state->get(RESULT_REGISTER);
      set_current_state_at(insn->dest(), insn->dest_is_wide(), value);
      break;
    }

    case IOPCODE_LOAD_PARAM:
    case IOPCODE_LOAD_PARAM_OBJECT:
    case IOPCODE_LOAD_PARAM_WIDE: {
      const auto param_index = m_load_param_map.at(insn);
      const auto value = ParamDomain(param_index);
      set_current_state_at(insn->dest(), insn->dest_is_wide(), value);
      break;
    }

    case OPCODE_CHECK_CAST: {
      // We track check cast like a move; this gives us the maximum information
      // across various call chains. Only when we are about to actually patch
      // the code we check whether such patching is verifiable.
      const auto value =
          get_current_state_at(insn->src(0), insn->src_is_wide(0));
      current_state->set(RESULT_REGISTER, value);
      break;
    }

    case OPCODE_INVOKE_DIRECT:
    case OPCODE_INVOKE_VIRTUAL:
    case OPCODE_INVOKE_STATIC:
    case OPCODE_INVOKE_INTERFACE:
    case OPCODE_INVOKE_SUPER: {
      // Avoid call resolution if all srcs are top anyway.
      bool all_top = true;
      for (size_t i = 0; i < insn->srcs_size(); i++) {
        const auto param_value =
            get_current_state_at(insn->src(i), insn->src_is_wide(i));
        if (!param_value.is_top()) {
          all_top = false;
          break;
        }
      }
      if (all_top) {
        default_case();
        break;
      }

      // TODO(perf): call resolution is quite expensive; figure out
      // beforehand if the result of this invoke instruction can ever flow
      // to a return instruction; if not, skip this
      const auto param_index = m_resolver.get_return_param_index(
          insn, m_methods_which_return_parameter, m_resolved_refs);
      if (!param_index) {
        default_case();
        break;
      }

      const auto param_value = get_current_state_at(
          insn->src(*param_index), insn->src_is_wide(*param_index));
      current_state->set(RESULT_REGISTER, param_value);
      break;
    }

    default: {
      default_case();
      break;
    }
    }
  }

 private:
  const ReturnParamResolver& m_resolver;
  const UnorderedMap<const DexMethod*, ParamIndex>&
      m_methods_which_return_parameter;
  const UnorderedMap<const IRInstruction*, ParamIndex> m_load_param_map;
  mutable MethodRefCache m_resolved_refs;
};
} // namespace

////////////////////////////////////////////////////////////////////////////////

std::optional<ParamIndex> ReturnParamResolver::get_return_param_index(
    const IRInstruction* insn,
    const UnorderedMap<const DexMethod*, ParamIndex>&
        methods_which_return_parameter,
    MethodRefCache& resolved_refs) const {
  always_assert(opcode::is_a_method_invoke(insn->opcode()));
  auto* const method = insn->get_method();
  auto* const proto = method->get_proto();
  if (proto->is_void()) {
    // No point in doing any further analysis
    return std::nullopt;
  }

  const auto opcode = insn->opcode();
  if (opcode == OPCODE_INVOKE_VIRTUAL && returns_receiver(method)) {
    return 0;
  }

  auto* callee = resolve_invoke_method_deprecated(insn, resolved_refs);
  if (callee == nullptr) {
    return std::nullopt;
  }

  ParamDomain param = ParamDomain::bottom();
  if (is_abstract(callee)) {
    // Some compilers emit `invoke-super` to an abstract method as the body
    // of a synthetic covariant-return bridge (observed in
    // org.chromium.net.impl.CronetEngineBase shipped with
    // play-services-cronet). Such a call, if dispatched at runtime, would
    // throw AbstractMethodError; here we just bail out conservatively so
    // the rest of the analysis can proceed. This is sister to the upstream
    // BridgeSynthInlinePass rewrite that normalizes these bridges to an
    // explicit throw; this branch remains as a defense in depth in case
    // that pass hasn't run (it runs after this pass in the default config)
    // or in case a similar pattern reaches us from elsewhere.
    if (opcode == OPCODE_INVOKE_SUPER) {
      return std::nullopt;
    }
    always_assert(opcode == OPCODE_INVOKE_VIRTUAL ||
                  opcode == OPCODE_INVOKE_INTERFACE);
  } else {
    const auto& mwrpit = methods_which_return_parameter.find(callee);
    if (mwrpit == methods_which_return_parameter.end()) {
      return std::nullopt;
    }
    param = ParamDomain(mwrpit->second);
  }

  if (opcode == OPCODE_INVOKE_VIRTUAL || opcode == OPCODE_INVOKE_INTERFACE) {
    always_assert(callee->is_virtual());
    // Make sure all implementations of this method have the same param index

    if (opcode == OPCODE_INVOKE_INTERFACE &&
        (root(callee) || !can_rename(callee))) {
      // We cannot rule out that there are dynamically added classes, created
      // via Proxy.newProxyInstance, that override this method.
      // So we assume the worst.
      return std::nullopt;
    }

    if (opcode == OPCODE_INVOKE_INTERFACE &&
        is_annotation(type_class(callee->get_class()))) {
      return std::nullopt;
    }

    auto* static_base_type = method->get_class();
    const auto overriding_methods =
        method_override_graph::get_overriding_methods(
            m_graph, callee, /* include_interfaces */ false, static_base_type);
    for (const auto* overriding : UnorderedIterable(overriding_methods)) {
      if (!method::may_be_invoke_target(overriding)) {
        continue;
      }
      const auto& mwrpit = methods_which_return_parameter.find(overriding);
      if (mwrpit == methods_which_return_parameter.end()) {
        return std::nullopt;
      }
      param.join_with(ParamDomain(mwrpit->second));
      if (param.is_top()) {
        // Bail out early if possible; it's the common case
        return std::nullopt;
      }
    }

    // TODO: Are we doing something about abstract methods without any overrides
    // somewhere?
    always_assert(!param.is_bottom() || is_abstract(callee));
  }

  auto c = param.get_constant();
  return c ? std::make_optional(*c) : std::nullopt;
}

bool ReturnParamResolver::returns_compatible_with_receiver(
    const DexMethodRef* method) const {
  // Because of covariance and implemented interfaces, we might be looking at a
  // synthesized bridge method that formally returns something weaker than the
  // receiver (an implemented interface). Still, the actually returned value can
  // be substituted by the receiver.
  auto* ctype = method->get_class();
  auto* rtype = method->get_proto()->get_rtype();
  if (ctype == rtype) {
    return true;
  }
  auto* cls = type_class(ctype);
  if (cls == nullptr) {
    // Hm, we don't have framework types available.
    return true;
  }
  auto* type_list = cls->get_interfaces();
  return std::find(type_list->begin(), type_list->end(), rtype) !=
         type_list->end();
}

bool ReturnParamResolver::returns_receiver(const DexMethodRef* method) const {
  // Hard-coded very special knowledge about certain framework methods

  DexType* cls = method->get_class();

  // these framework classes implement the "Appendable" interface, with the
  // formal return type being the exact class type
  if (cls == m_char_buffer_type || cls == m_string_buffer_type ||
      cls == m_string_builder_type) {
    if (method->get_name() == DexString::make_string("append")) {
      always_assert(returns_compatible_with_receiver(method));
      return true;
    }
  }

  if (cls == m_byte_buffer_type || cls == m_char_buffer_type ||
      cls == m_double_buffer_type || cls == m_float_buffer_type ||
      cls == m_int_buffer_type || cls == m_long_buffer_type ||
      cls == m_short_buffer_type) {
    const auto* name = method->get_name();
    if (name == DexString::make_string("compact") ||
        name == DexString::make_string("put")) {
      always_assert(returns_compatible_with_receiver(method));
      return true;
    }
  }

  if (cls == m_byte_buffer_type) {
    const auto* name = method->get_name();
    if (name == DexString::make_string("putChar") ||
        name == DexString::make_string("putDouble") ||
        name == DexString::make_string("putFloat") ||
        name == DexString::make_string("putInt") ||
        name == DexString::make_string("putLong") ||
        name == DexString::make_string("putShort")) {
      always_assert(returns_compatible_with_receiver(method));
      return true;
    }
  }

  if (cls == m_string_buffer_type || cls == m_string_builder_type) {
    const auto* name = method->get_name();
    if (name == DexString::make_string("appendCodePoint") ||
        name == DexString::make_string("delete") ||
        name == DexString::make_string("deleteCharAt") ||
        name == DexString::make_string("insert") ||
        name == DexString::make_string("replace") ||
        name == DexString::make_string("reverse")) {
      always_assert(returns_compatible_with_receiver(method));
      return true;
    }
  }

  if (method == m_string_to_string_method) {
    return true;
  }

  return false;
}

std::optional<ParamIndex> ReturnParamResolver::get_return_param_index(
    const cfg::ControlFlowGraph& cfg,
    const UnorderedMap<const DexMethod*, ParamIndex>&
        methods_which_return_parameter) const {
  Analyzer analyzer(cfg, *this, methods_which_return_parameter);
  auto return_param_index = ParamDomain::bottom();
  // join together return values of all blocks which end with a
  // return instruction
  for (auto* const block : cfg.blocks()) {
    const auto& last = block->get_last_insn();
    if (last == block->end() || !opcode::is_a_return(last->insn->opcode())) {
      continue;
    }
    const auto& env = analyzer.get_exit_state_at(block);
    const auto& block_return_param_index = env.get(RETURN_VALUE);
    return_param_index.join_with(block_return_param_index);
  }

  auto c = return_param_index.get_constant();
  return c ? std::make_optional(*c) : std::nullopt;
}

void ResultPropagation::patch(PassManager& mgr, cfg::ControlFlowGraph& cfg) {
  // turn move-result-... into move instructions if the called method
  // is known to always return a particular parameter
  std::vector<cfg::InstructionIterator> deletes;
  auto ii = InstructionIterable(cfg);
  for (auto it = ii.begin(); it != ii.end(); it++) {
    // do we have a sequence of invoke + move-result instruction?
    auto* const insn = it->insn;
    TRACE(RP, 6, "  evaluating instruction  %s", SHOW(insn));

    if (!opcode::is_a_move_result(insn->opcode())) {
      TRACE(RP, 6, "  not a move_result.");
      continue;
    }

    auto primary_it = cfg.primary_instruction_of_move_result(it);
    if (primary_it.is_end()) {
      continue;
    }

    auto* primary_insn = primary_it->insn;

    if (!opcode::is_a_method_invoke(primary_insn->opcode())) {
      TRACE(RP, 6, "  primary instruction not an invoke.");
      continue;
    }

    // do we know the invoked method always returns a particular parameter?
    const auto param_index = m_resolver.get_return_param_index(
        primary_insn, m_methods_which_return_parameter, m_resolved_refs);
    if (!param_index) {
      continue;
    }

    if (!mgr.get_redex_options().verify_none_enabled) {
      // Let's check if replacing move-result with a move does not impact
      // verifiability.
      // TODO(configurability): Introduce a flag whether we care about
      // verifiability.
      // TODO(effectiveness): We are currently very consersative, only
      // looking locally at the proto's param type. Instead, track where the
      // register flowing into the invoke instruction was defined, and what
      // its statically known type is.
      const auto is_static = primary_insn->opcode() == OPCODE_INVOKE_STATIC;
      const auto* const param_type =
          get_param_type(is_static, primary_insn->get_method(), *param_index);
      auto* const rtype = primary_insn->get_method()->get_proto()->get_rtype();
      if (!type::check_cast(param_type, rtype)) {
        ++m_stats.unverifiable_move_results;
        continue;
      }
    }

    if (m_callee_blocklist.count(
            resolve_method_deprecated(primary_insn->get_method(),
                                      opcode_to_search(primary_insn),
                                      m_resolved_refs)) != 0u) {
      continue;
    }

    // rewrite instruction
    const auto source_reg = primary_insn->src(*param_index);
    if (insn->dest() == source_reg) {
      deletes.push_back(it);
      ++m_stats.erased_move_results;
    } else {
      patch_move_result_to_move(insn, source_reg);
      ++m_stats.patched_move_results;
    }
  }
  for (auto const& instr : deletes) {
    cfg.remove_insn(instr);
  }
}

void ResultPropagationPass::run_pass(DexStoresVector& stores,
                                     ConfigFiles& /* conf */,
                                     PassManager& mgr) {
  const auto scope = build_class_scope(stores);
  const auto method_override_graph = method_override_graph::build_graph(scope);
  ReturnParamResolver resolver(*method_override_graph);
  const auto methods_which_return_parameter =
      find_methods_which_return_parameter(mgr, scope, resolver);

  const auto stats = walk::parallel::methods<ResultPropagation::Stats>(
      scope, [&](DexMethod* m) {
        auto* const code = m->get_code();
        if (code == nullptr || m->rstate.no_optimizations()) {
          return ResultPropagation::Stats();
        }

        ResultPropagation rp(methods_which_return_parameter, resolver,
                             m_callee_blocklist);
        always_assert(code->cfg_built());
        auto& cfg = code->cfg();
        rp.patch(mgr, cfg);
        return rp.get_stats();
      });
  mgr.incr_metric(METRIC_METHODS_WHICH_RETURN_PARAMETER,
                  methods_which_return_parameter.size());
  mgr.incr_metric(METRIC_ERASED_MOVE_RESULTS, stats.erased_move_results);
  mgr.incr_metric(METRIC_PATCHED_MOVE_RESULTS, stats.patched_move_results);
  mgr.incr_metric(METRIC_UNVERIFIABLE_MOVE_RESULTS,
                  stats.unverifiable_move_results);
  TRACE(RP, 1,
        "result propagation --- potential methods: %zu, erased moves: %zu, "
        "patched moves: %zu, "
        "unverifiable moves: %zu",
        methods_which_return_parameter.size(), stats.erased_move_results,
        stats.patched_move_results, stats.unverifiable_move_results);
}

using ParamIndexMap = UnorderedMap<const DexMethod*, ParamIndex>;

UnorderedMap<const DexMethod*, ParamIndex>
ResultPropagationPass::find_methods_which_return_parameter(
    PassManager& mgr, const Scope& scope, const ReturnParamResolver& resolver) {
  UnorderedMap<const DexMethod*, ParamIndex> methods_which_return_parameter;
  // We iterate a few times to capture chains of method calls that all
  // eventually return `this`.
  // TODO(perf): Add flag to limit number of iterations
  // TODO(perf): For each analyzed method, keep track of the reasons (a set of
  // methods) why the call resolution gave up, and use that "dependency"
  // information to limit what needs to be processed in subsequent iterations
  while (true) {
    mgr.incr_metric(METRIC_METHODS_WHICH_RETURN_PARAMETER_ITERATIONS, 1);
    const auto next_methods_which_return_parameter =
        walk::parallel::methods<ParamIndexMap,
                                UnorderedMergeContainers<ParamIndexMap>>(
            scope, [&](DexMethod* method) {
              UnorderedMap<const DexMethod*, ParamIndex> res;

              const auto* code = method->get_code();
              if (code == nullptr) {
                return res;
              }
              const auto* proto = method->get_proto();
              if (proto->is_void()) {
                // void methods cannot return a parameter, skip expensive
                // analysis
                return res;
              }

              const auto mwrpit = methods_which_return_parameter.find(method);
              if (mwrpit != methods_which_return_parameter.end()) {
                // Short-circuit re-computing for perf
                res.insert({method, mwrpit->second});
                return res;
              }

              always_assert(code->cfg_built());
              const auto& cfg = code->cfg();
              const auto return_param_index = resolver.get_return_param_index(
                  cfg, methods_which_return_parameter);
              if (return_param_index) {
                res.insert({method, *return_param_index});
              }

              return res;
            });

    if (next_methods_which_return_parameter.size() ==
        methods_which_return_parameter.size()) {
      return methods_which_return_parameter;
    }
    methods_which_return_parameter = next_methods_which_return_parameter;
  }
}

static ResultPropagationPass s_pass;
