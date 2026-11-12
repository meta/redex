/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "IPConstantPropagation.h"

#include <future>

#include "AtomicStatCounter.h"
#include "ConfigFiles.h"
#include "ConstantEnvironment.h"
#include "ConstantPropagationAnalysis.h"
#include "ConstantPropagationState.h"
#include "ConstructorParams.h"
#include "Debug.h"
#include "DefinitelyAssignedIFields.h"
#include "DexUtil.h"
#include "IPConstantPropagationAnalysis.h"
#include "MethodOverrideGraph.h"
#include "PassManager.h"
#include "Purity.h"
#include "ScopedMetrics.h"
#include "Show.h"
#include "StringBuilderAppendChain.h"
#include "Trace.h"
#include "Walkers.h"
#include "WrappedPrimitives.h"

namespace mog = method_override_graph;

namespace {

// Whether, for a given type, a non-top value represents useful information.
bool is_useful(DexType* type, const ConstantValue& value) {
  always_assert(!value.is_top());
  if (type::is_boolean(type)) {
    // Since a boolean value can only have 1 and 0 as values, "GEZ" tells us
    // nothing useful.
    return !value.equals(SignedConstantDomain(sign_domain::Interval::GEZ)) &&
           !value.equals(SignedConstantDomain(0, 1));
  }
  return true;
}

} // namespace

namespace constant_propagation {

namespace interprocedural {

using CombinedAnalyzer =
    InstructionAnalyzerCombiner<ClinitFieldAnalyzer,
                                ImmutableAttributeAnalyzer,
                                WholeProgramAwareAnalyzer,
                                EnumFieldAnalyzer,
                                BoxedBooleanAnalyzer,
                                StringAnalyzer,
                                ConstantClassObjectAnalyzer,
                                ApiLevelAnalyzer,
                                PackageNameAnalyzer,
                                NewObjectAnalyzer,
                                ResourceIdAnalyzer,
                                PrimitiveAnalyzer>;

namespace {

class AnalyzerGenerator {
  UnorderedSet<const DexField*> m_clinit_only_fields;
  ImmutableAttributeAnalyzerState* m_immut_analyzer_state;
  ApiLevelAnalyzerState* m_api_level_analyzer_state;
  BoxedBooleanAnalyzerState m_boxed_boolean_analyzer_state{};
  EnumFieldAnalyzerState m_enum_field_analyzer_state;
  StringAnalyzerState* m_string_analyzer_state;
  PackageNameState* m_package_name_state;
  const NullCheckMethods& m_null_check_methods;

 public:
  explicit AnalyzerGenerator(
      const Scope& scope,
      ImmutableAttributeAnalyzerState* immut_analyzer_state,
      ApiLevelAnalyzerState* api_level_analyzer_state,
      StringAnalyzerState* string_analyzer_state,
      PackageNameState* package_name_state,
      const NullCheckMethods& null_check_methods)
      : m_clinit_only_fields(get_clinit_only_written_fields(scope)),
        m_immut_analyzer_state(immut_analyzer_state),
        m_api_level_analyzer_state(api_level_analyzer_state),
        m_string_analyzer_state(string_analyzer_state),
        m_package_name_state(package_name_state),
        m_null_check_methods(null_check_methods) {}

  std::unique_ptr<IntraproceduralAnalysis> operator()(
      const DexMethod* method,
      const WholeProgramState& wps,
      ArgumentDomain args) {
    always_assert(method->get_code() != nullptr);
    const auto& code = *method->get_code();
    // Currently, our callgraph does not include calls to non-devirtualizable
    // virtual methods. So those methods may appear unreachable despite being
    // reachable.
    if (args.is_bottom()) {
      args.set_to_top();
    } else if (!args.is_top()) {
      TRACE(ICONSTP, 3, "Have args for %s: %s", SHOW(method), SHOW(args));
    }

    auto env = env_with_params(is_static(method), &code, args);
    DexType* class_under_init{nullptr};
    if (method::is_clinit(method)) {
      class_under_init = method->get_class();
      set_encoded_values(type_class(class_under_init), &env);
    }
    TRACE(ICONSTP, 5, "%s", SHOW(code.cfg()));

    auto wps_accessor = std::make_unique<WholeProgramStateAccessor>(wps);
    auto* wps_accessor_ptr = wps_accessor.get();
    return std::make_unique<IntraproceduralAnalysis>(
        &m_null_check_methods, std::move(wps_accessor), code.cfg(),
        CombinedAnalyzer(
            ClinitFieldAnalyzerState(class_under_init, &m_clinit_only_fields),
            m_immut_analyzer_state, wps_accessor_ptr,
            m_enum_field_analyzer_state, m_boxed_boolean_analyzer_state,
            m_string_analyzer_state, nullptr, *m_api_level_analyzer_state,
            m_package_name_state, m_immut_analyzer_state, nullptr, nullptr),
        std::move(env));
  }
};

} // namespace

/*
 * This algorithm is based off the approach in this paper[1]. We start off by
 * assuming no knowledge of any field values or method return values, i.e. we
 * just interprocedurally propagate constants from const opcodes. Then, we use
 * the result of that "bootstrap" run to build an approximation of the field
 * and method return values, which is represented by a WholeProgramState. We
 * re-run propagation using that WholeProgramState until we reach a fixpoint or
 * a configurable limit.
 *
 * [1]: Venet, Arnaud. Precise and Efficient Static Array Bound Checking for
 *      Large Embedded C Programs.
 *      https://ntrs.nasa.gov/search.jsp?R=20040081118
 */
std::unique_ptr<FixpointIterator> PassImpl::analyze(
    const Scope& scope,
    ImmutableAttributeAnalyzerState* immut_analyzer_state,
    ApiLevelAnalyzerState* api_level_analyzer_state,
    StringAnalyzerState* string_analyzer_state,
    PackageNameState* package_name_state,
    const NullCheckMethods& null_check_methods) {
  auto method_override_graph = mog::build_graph(scope);
  std::shared_ptr<call_graph::Graph> cg;
  {
    cg = m_config.use_multiple_callee_callgraph
             ? std::make_shared<call_graph::Graph>(
                   call_graph::multiple_callee_graph(
                       *method_override_graph, scope,
                       m_config.big_override_threshold))
             : std::make_shared<call_graph::Graph>(
                   call_graph::single_callee_graph(*method_override_graph,
                                                   scope));
  }
  auto cg_for_wps = m_config.use_multiple_callee_callgraph ? cg : nullptr;
  auto cg_stats = get_num_nodes_edges(*cg);
  m_stats.callgraph_nodes = cg_stats.num_nodes;
  m_stats.callgraph_edges = cg_stats.num_edges;
  m_stats.callgraph_callsites = cg_stats.num_callsites;
  auto fp_iter = std::make_unique<FixpointIterator>(
      cg,
      AnalyzerGenerator(scope, immut_analyzer_state, api_level_analyzer_state,
                        string_analyzer_state, package_name_state,
                        null_check_methods),
      cg_for_wps);
  // Run the bootstrap. All field value and method return values are
  // represented by Top.
  fp_iter->run(Domain{{CURRENT_PARTITION_LABEL, ArgumentDomain()}});
  auto non_true_virtuals =
      mog::get_non_true_virtuals(*method_override_graph, scope);
  UnorderedSet<const DexField*> definitely_assigned_ifields;
  if (m_config.compute_definitely_assigned_ifields) {
    definitely_assigned_ifields =
        definitely_assigned_ifields::get_definitely_assigned_ifields(
            scope, m_config.analyze_ancestor_constructors);
  }
  m_stats.definitely_assigned_ifields = definitely_assigned_ifields.size();
  for (size_t i = 0; i < m_config.max_heap_analysis_iterations; ++i) {
    // Build an approximation of all the field values and method return values.
    auto wps = std::make_unique<WholeProgramState>(
        scope, *fp_iter, non_true_virtuals, m_config.field_blocklist,
        definitely_assigned_ifields, cg_for_wps);
    // If this approximation is not better than the previous one, we are done.
    if (fp_iter->get_whole_program_state().leq(*wps)) {
      break;
    }
    // Use the refined WholeProgramState to propagate more constants via
    // the stack and registers.
    fp_iter->set_whole_program_state(std::move(wps));
    fp_iter->run(Domain{{CURRENT_PARTITION_LABEL, ArgumentDomain()}});
    m_stats.heap_analysis_iterations++;
  }
  compute_analysis_stats(fp_iter->get_whole_program_state(),
                         definitely_assigned_ifields);
  return fp_iter;
}

void PassImpl::compute_analysis_stats(
    const WholeProgramState& wps,
    const UnorderedSet<const DexField*>& definitely_assigned_ifields) {
  if (!wps.get_field_partition().is_top()) {
    for (const auto& pair : wps.get_field_partition().bindings()) {
      const auto* field = pair.first;
      const auto& value = pair.second;
      if (value.is_top() || !is_useful(field->get_type(), value)) {
        continue;
      }
      if (definitely_assigned_ifields.count(field) != 0u) {
        ++m_stats.constant_definitely_assigned_ifields;
        TRACE(ICONSTP, 4, "definitely assigned field partition for %s: %s",
              SHOW(field), SHOW(value));
      } else {
        TRACE(ICONSTP, 4, "field partition for %s: %s", SHOW(field),
              SHOW(value));
      }
      ++m_stats.constant_fields;
    }
  }
  if (!wps.get_method_partition().is_top()) {
    for (const auto& pair : wps.get_method_partition().bindings()) {
      const auto* method = pair.first;
      const auto& value = pair.second;
      if (value.is_top() ||
          !is_useful(method->get_proto()->get_rtype(), value)) {
        continue;
      }
      TRACE(ICONSTP, 4, "method partition for %s: %s", SHOW(method),
            SHOW(value));
      ++m_stats.constant_methods;
    }
  }
}

/*
 * Transform all methods using the information about constant method arguments
 * that analyze() obtained.
 */
void PassImpl::optimize(
    const Scope& scope,
    const TypeSystem& type_system,
    const XStoreRefs& xstores,
    const FixpointIterator& fp_iter,
    const ImmutableAttributeAnalyzerState* immut_analyzer_state,
    const NullCheckMethods& null_check_methods) {
  const auto& pure_methods = ::get_pure_methods();
  // `String.concat` is a method ref, which InterDex budgets per dex, so one it
  // has already packed may have no room for it.
  const bool reduce_concat =
      m_config.reduce_stringbuilder_concat && !m_interdex_has_run;
  AtomicStatCounter<size_t> appends_merged{0};
  AtomicStatCounter<size_t> stringbuilder_constant_tostrings_replaced{0};
  AtomicStatCounter<size_t> concat_reduced{0};
  m_transform_stats =
      walk::parallel::methods<Transform::Stats>(scope, [&](DexMethod* method) {
        if (method->get_code() == nullptr ||
            method->rstate.no_optimizations()) {
          return Transform::Stats();
        }
        auto& code = *method->get_code();
        auto ipa = fp_iter.get_intraprocedural_analysis(method);

        if (m_config.create_runtime_asserts) {
          RuntimeAssertTransform rat(m_config.runtime_assert);
          rat.apply(ipa->fp_iter, fp_iter.get_whole_program_state(), method);
          return Transform::Stats();
        } else {
          Transform::Config config(m_config.transform);
          config.class_under_init =
              method::is_clinit(method) ? method->get_class() : nullptr;
          config.getter_methods_for_immutable_fields =
              &immut_analyzer_state->attribute_methods;
          config.pure_methods = &pure_methods;
          Transform tf(config, null_check_methods);
          tf.legacy_apply_constants_and_prune_unreachable(
              ipa->fp_iter,
              fp_iter.get_whole_program_state(),
              code.cfg(),
              &xstores,
              method->get_class());
          // If configured, plug in IPCP state to do additional transforms
          // (API unwrapping to primitives for known ObjectWithImmutAttr
          // instances).
          wrapped_primitives::optimize_method(type_system, ipa->fp_iter,
                                              fp_iter.get_whole_program_state(),
                                              method, code.cfg());
          // The merge goes first: shortening a chain to two appends brings it
          // within the concat reduction's reach, and the concatenation it
          // materializes is a const-string, which that reduction requires to be
          // provably non-null.
          if (m_config.merge_adjacent_constant_appends) {
            appends_merged +=
                stringbuilder_append_chain::merge_adjacent_constant_appends(
                    ipa->fp_iter, code.cfg());
          }
          // This must come after merge_adjacent_constant_appends because it can
          // take advantage of the result of merge_adjacent_constant_appends,
          // which increases the number of of StringBuilder-append-toString
          // chains that contain only one append on constant.
          if (m_config
                  .replace_constant_stringbuilder_tostring_with_const_string) {
            stringbuilder_constant_tostrings_replaced +=
                stringbuilder_append_chain::
                    replace_constant_tostring_with_const_string(ipa->fp_iter,
                                                                code.cfg());
          }
          if (reduce_concat) {
            concat_reduced +=
                stringbuilder_append_chain::reduce_two_append_concats(
                    ipa->fp_iter, code.cfg());
          }
          return tf.get_stats();
        }
      });
  m_appends_merged = appends_merged.load();
  m_stringbuilder_constant_tostrings_replaced =
      stringbuilder_constant_tostrings_replaced.load();
  m_concat_reduced = concat_reduced.load();
}

void PassImpl::run(const DexStoresVector& stores,
                   const ConfigFiles& conf,
                   int min_sdk,
                   const std::optional<std::string>& package_name) {
  // reset statistics, to be meaningful when pass runs multiple times
  m_stats = Stats();
  m_transform_stats = Transform::Stats();

  auto scope = build_class_scope(stores);
  XStoreRefs xstores(stores, conf.normal_primary_dex());

  walk::parallel::code(scope, [&](const DexMethod* /*method*/, IRCode& code) {
    always_assert(code.cfg_built());
    code.cfg().calculate_exit_block();
  });

  // Hold the analyzer state of ImmutableAttributeAnalyzer.
  ImmutableAttributeAnalyzerState immut_analyzer_state;
  immutable_state::analyze_constructors(scope, &immut_analyzer_state);
  ApiLevelAnalyzerState api_level_analyzer_state{min_sdk};
  auto string_analyzer_state = StringAnalyzerState::make_default();
  auto package_name_state = PackageNameState::make(package_name);
  NullCheckMethods null_check_methods;
  // Ensure java.lang.Object's DexClass and methods exist before launching the
  // async TypeSystem construction. TypeSystem → ClassScopes →
  // build_signature_map → get_vmethods may lazily call create_object_class(),
  // which mutates java.lang.Object by adding methods. If that runs
  // concurrently with analyze()'s parallel class walkers (which read the same
  // method vectors), it causes a heap-use-after-free.
  create_object_class();
  // Start TypeSystem construction in background — only reads scope now that
  // java.lang.Object is fully initialized. Hides ~16s cost behind analyze().
  auto type_system_future =
      std::async(std::launch::async, [&scope]() { return TypeSystem(scope); });
  auto fp_iter =
      analyze(scope, &immut_analyzer_state, &api_level_analyzer_state,
              &string_analyzer_state, &package_name_state, null_check_methods);
  m_stats.fp_iter = fp_iter->get_stats();
  auto type_system = type_system_future.get();
  optimize(scope, type_system, xstores, *fp_iter, &immut_analyzer_state,
           null_check_methods);
}

void PassImpl::eval_pass(DexStoresVector& /*stores*/,
                         ConfigFiles& /*conf*/,
                         PassManager&) {
  StringAnalyzerState::make_default().set_methods_as_root();
}

void PassImpl::run_pass(DexStoresVector& stores,
                        ConfigFiles& config,
                        PassManager& mgr) {
  if (m_config.create_runtime_asserts) {
    m_config.runtime_assert =
        RuntimeAssertTransform::Config(config.get_proguard_map());
  }

  m_interdex_has_run = mgr.interdex_has_run();

  const auto& options = mgr.get_redex_options();
  run(stores, config, options.min_sdk, options.package_name);

  ScopedMetrics sm(mgr);
  m_transform_stats.log_metrics(sm, /* with_scope= */ false);

  mgr.incr_metric("definitely_assigned_ifields",
                  m_stats.definitely_assigned_ifields);
  mgr.incr_metric("constant_definitely_assigned_ifields",
                  m_stats.constant_definitely_assigned_ifields);
  mgr.incr_metric("constant_fields", m_stats.constant_fields);
  mgr.incr_metric("constant_methods", m_stats.constant_methods);
  mgr.incr_metric("callgraph_edges", m_stats.callgraph_edges);
  mgr.incr_metric("callgraph_nodes", m_stats.callgraph_nodes);
  mgr.incr_metric("callgraph_callsites", m_stats.callgraph_callsites);
  mgr.incr_metric("heap_analysis_iterations", m_stats.heap_analysis_iterations);
  mgr.incr_metric("fp_iter.method_cache_hits",
                  m_stats.fp_iter.method_cache_hits);
  mgr.incr_metric("fp_iter.method_cache_misses",
                  m_stats.fp_iter.method_cache_misses);

  mgr.set_metric("config.max_heap_analysis_iterations",
                 m_config.max_heap_analysis_iterations);
  mgr.set_metric("config.analyze_ancestor_constructors",
                 m_config.analyze_ancestor_constructors);
  mgr.incr_metric("stringbuilder_appends_merged", m_appends_merged);
  mgr.incr_metric("stringbuilder_constant_tostrings_replaced",
                  m_stringbuilder_constant_tostrings_replaced);
  mgr.incr_metric("stringbuilder_concat_reduced", m_concat_reduced);
}

static PassImpl s_pass;

} // namespace interprocedural

} // namespace constant_propagation
