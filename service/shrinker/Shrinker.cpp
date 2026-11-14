/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "Shrinker.h"

#include <fstream>

#include "BranchPrefixHoisting.h"
#include "ConstantUses.h"
#include "ConstructorParams.h"
#include "Debug.h"
#include "LinearScan.h"
#include "RegisterAllocation.h"
#include "ScopedMetrics.h"
#include "Trace.h"

namespace shrinker {

namespace {

inline Shrinker::ShrinkerForest::FeatureFunctionMap
get_default_feature_function_map() {
  return {
      // Caller.
      {"caller_insns",
       [](const Shrinker::MethodContext& caller) { return caller.m_insns; }},
      {"caller_regs",
       [](const Shrinker::MethodContext& caller) { return caller.m_regs; }},
      {"caller_blocks",
       [](const Shrinker::MethodContext& caller) { return caller.m_blocks; }},
      {"caller_edges",
       [](const Shrinker::MethodContext& caller) { return caller.m_edges; }},
  };
}

Shrinker::ShrinkerForest load(const std::string& filename) {
  std::string content;
  if (!filename.empty() && filename != "none") {
    std::stringstream buffer;
    {
      std::ifstream ifs(filename);
      always_assert(ifs);
      buffer << ifs.rdbuf();
      always_assert(!ifs.fail());
    }
    content = buffer.str();
  }
  if (content.empty()) {
    TRACE(MMINL, 1, "No shrinker forest: %s", filename.c_str());
    return Shrinker::ShrinkerForest(); // Empty forest accepts everything.
  }
  return Shrinker::ShrinkerForest::deserialize(
      content, get_default_feature_function_map());
}

bool should_shrink(IRCode* code, const Shrinker::ShrinkerForest& forest) {
  const auto& cfg = code->cfg();

  size_t regs = cfg.get_registers_size();
  size_t insn = cfg.num_opcodes();
  size_t blocks = cfg.num_blocks();
  size_t edges = cfg.num_edges();

  return forest.accept(Shrinker::MethodContext{
      (uint32_t)regs, (uint32_t)insn, (uint32_t)blocks, (uint32_t)edges});
}

} // namespace

Shrinker::Shrinker(
    DexStoresVector& stores,
    const Scope& scope,
    const init_classes::InitClassesWithSideEffects&
        init_classes_with_side_effects,
    const ConfigFiles& conf,
    const ShrinkerConfig& config,
    int min_sdk,
    const UnorderedSet<DexMethodRef*>& configured_pure_methods,
    const UnorderedSet<const DexString*>& configured_finalish_field_names,
    const UnorderedSet<const DexField*>& configured_finalish_fields,
    const std::optional<std::string>& package_name,
    const method_override_graph::Graph* method_override_graph)
    : m_forest(load(config.reg_alloc_random_forest)),
      m_xstores(stores, conf.normal_primary_dex()),
      m_config(config),
      m_min_sdk(min_sdk),
      m_enabled(config.run_const_prop || config.run_cse ||
                config.run_copy_prop || config.run_local_dce ||
                config.run_reg_alloc || config.run_fast_reg_alloc ||
                config.run_dedup_blocks || config.run_branch_prefix_hoisting),
      m_init_classes_with_side_effects(init_classes_with_side_effects),
      m_pure_methods(configured_pure_methods),
      m_finalish_field_names(configured_finalish_field_names),
      m_finalish_fields(configured_finalish_fields),
      m_api_level_analyzer_state(m_min_sdk),
      m_boxed_boolean_analyzer_state(),
      m_string_analyzer_state(
          constant_propagation::StringAnalyzerState::make_default()),
      m_package_name_state(
          constant_propagation::PackageNameState::make(package_name)) {
  if (config.run_cse || config.run_local_dce) {
    if (config.compute_pure_methods) {
      const auto& pure_methods = ::get_pure_methods();
      insert_unordered_iterable(m_pure_methods, pure_methods);
      auto immutable_getters = get_immutable_getters(scope);
      insert_unordered_iterable(m_pure_methods, immutable_getters);
    }
    if (config.run_cse) {
      m_cse_shared_state = std::make_unique<cse_impl::SharedState>(
          m_pure_methods, m_finalish_field_names, m_finalish_fields);
    }
    if (config.run_local_dce && config.compute_pure_methods) {
      // Note that because we are not invoking m_cse_shared_state->init_scope(),
      // we don't already have a method-override-graph.
      always_assert(!config.run_cse ||
                    m_cse_shared_state->get_method_override_graph() == nullptr);
      std::unique_ptr<const method_override_graph::Graph>
          owned_method_override_graph;
      if (method_override_graph == nullptr) {
        owned_method_override_graph = method_override_graph::build_graph(scope);
        method_override_graph = owned_method_override_graph.get();
      }
      UnorderedSet<const DexMethod*> computed_no_side_effects_methods;
      /* Returns computed_no_side_effects_methods_iterations */
      method::ClInitHasNoSideEffectsPredicate clinit_has_no_side_effects =
          [&](const DexType* type) {
            return init_classes_with_side_effects.refine(type) == nullptr;
          };
      compute_no_side_effects_methods(
          scope, method_override_graph, clinit_has_no_side_effects,
          m_pure_methods, &computed_no_side_effects_methods);
      for (const auto* m :
           UnorderedIterable(computed_no_side_effects_methods)) {
        m_pure_methods.insert(const_cast<DexMethod*>(m));
      }
    }
  }
  if (config.run_const_prop && config.analyze_constructors) {
    constant_propagation::immutable_state::analyze_constructors(
        scope, &m_immut_analyzer_state);
  }
  TRACE(MMINL, 1, "shrinker normal_primary_dex: %d; largest_root_store_id: %zu",
        conf.normal_primary_dex(), m_xstores.largest_root_store_id());
}

constant_propagation::Transform::Stats Shrinker::constant_propagation(
    bool is_static,
    DexType* declaring_type,
    DexProto* proto,
    IRCode* code,
    const ConstantEnvironment& initial_env,
    const constant_propagation::Transform::Config& config) {
  constant_propagation::intraprocedural::FixpointIterator fp_iter(
      code->cfg(),
      constant_propagation::ConstantPrimitiveAndBoxedAnalyzer(
          &m_immut_analyzer_state, &m_immut_analyzer_state,
          m_enum_analyzer_state, m_boxed_boolean_analyzer_state,
          &m_string_analyzer_state, m_api_level_analyzer_state,
          &m_package_name_state, nullptr, &m_immut_analyzer_state, nullptr,
          nullptr),
      constant_propagation::intraprocedural::make_default_no_throw_analyzer(
          &m_null_check_methods),
      /* imprecise_switches */ true);
  fp_iter.run(initial_env);
  constant_propagation::Transform tf(config, m_null_check_methods);
  tf.apply(fp_iter, constant_propagation::WholeProgramState(), code->cfg(),
           &m_xstores, is_static, declaring_type, proto);
  return tf.get_stats();
}

LocalDce::Stats Shrinker::local_dce(IRCode* code,
                                    bool normalize_new_instances,
                                    DexType* declaring_type) {
  // LocalDce doesn't care if cfg_built
  auto local_dce = LocalDce(&m_init_classes_with_side_effects, m_pure_methods);
  local_dce.dce(code, normalize_new_instances, declaring_type);
  return local_dce.get_stats();
}

copy_propagation_impl::Stats Shrinker::copy_propagation(DexMethod* method) {
  return copy_propagation(method->get_code(),
                          is_static(method),
                          method->get_class(),
                          method->get_proto()->get_rtype(),
                          method->get_proto()->get_args(),
                          [method]() { return show(method); });
}

copy_propagation_impl::Stats Shrinker::copy_propagation(
    IRCode* code,
    bool is_static,
    DexType* declaring_type,
    DexType* rtype,
    DexTypeList* args,
    std::function<std::string()> method_describer) {
  copy_propagation_impl::Config config;
  copy_propagation_impl::CopyPropagation copy_propagation(config);
  return copy_propagation.run(code, is_static, declaring_type, rtype, args,
                              std::move(method_describer));
}
void Shrinker::shrink_method(DexMethod* method) {
  shrink_code(method->get_code(),
              is_static(method),
              method::is_init(method) || method::is_clinit(method),
              method->get_class(),
              method->get_proto(),
              [method]() { return show(method); });
}

void Shrinker::shrink_code(
    IRCode* code,
    bool is_static,
    bool is_init_or_clinit,
    DexType* declaring_type,
    DexProto* proto,
    const std::function<std::string()>& method_describer) {
  always_assert(code->cfg_built());
  // force simplification/linearization of any existing cfg once, and
  // forget existing cfg for a clean start
  code->cfg().recompute_registers_size();
  code->clear_cfg();

  constant_propagation::Transform::Stats const_prop_stats;
  cse_impl::Stats cse_stats;
  copy_propagation_impl::Stats copy_prop_stats;
  LocalDce::Stats local_dce_stats;
  dedup_blocks_impl::Stats dedup_blocks_stats;
  size_t branch_prefix_hoisting_stats{0};
  positions::JoinStats join_stats;

  code->build_cfg();
  if (m_config.run_const_prop) {
    auto timer = m_const_prop_timer.scope();
    constant_propagation::Transform::Config config;
    config.pure_methods = &m_pure_methods;
    const_prop_stats = constant_propagation(is_static, declaring_type, proto,
                                            code, {}, config);
  }

  if (m_config.run_cse) {
    auto timer = m_cse_timer.scope();
    cse_impl::CommonSubexpressionElimination cse(
        m_cse_shared_state.get(), code->cfg(), is_static, is_init_or_clinit,
        declaring_type, proto->get_args());
    cse.patch();
    cse_stats = cse.get_stats();
  }

  if (m_config.run_copy_prop) {
    auto timer = m_copy_prop_timer.scope();
    copy_prop_stats =
        copy_propagation(code, is_static, declaring_type, proto->get_rtype(),
                         proto->get_args(), method_describer);
  }

  if (m_config.run_local_dce) {
    auto timer = m_local_dce_timer.scope();
    local_dce_stats =
        local_dce(code, m_config.normalize_new_instances, declaring_type);
  }

  using stats_t = std::tuple<size_t, size_t, size_t, size_t>;
  auto get_features = [&code](int mminl_level) -> stats_t {
    if (!traceEnabled(MMINL, mminl_level)) {
      return stats_t{};
    }
    const auto& cfg = code->cfg();

    size_t regs_before = cfg.get_registers_size();
    size_t insn_before = cfg.num_opcodes();
    size_t blocks_before = cfg.num_blocks();
    size_t edges = cfg.num_edges();
    return stats_t{regs_before, insn_before, blocks_before, edges};
  };

  constexpr int kMMINLDataCollectionLevel = 10;
  auto data_before_reg_alloc = get_features(kMMINLDataCollectionLevel);

  size_t reg_alloc_inc{0};
  if (m_config.run_reg_alloc) {
    if (should_shrink(code, m_forest) ||
        traceEnabled(MMINL, kMMINLDataCollectionLevel)) {
      auto timer = m_reg_alloc_timer.scope();

      // It's OK to ensure we have an CFG, the allocator would build
      // it, too.
      auto before_features = get_features(4);

      auto config = regalloc::graph_coloring::Allocator::Config{};
      config.no_overwrite_this = true; // Downstream passes may rely on this.
      regalloc::graph_coloring::allocate(config, code, is_static,
                                         method_describer);
      // After this, any CFG is gone.

      // Assume that dedup will run, so building CFG is OK.
      auto after_features = get_features(4);
      TRACE(MMINL, 4,
            "Inliner.RegAlloc: %s: (%zu, %zu, %zu) -> (%zu, %zu, %zu)",
            method_describer().c_str(), std::get<0>(before_features),
            std::get<1>(before_features), std::get<2>(before_features),
            std::get<0>(after_features), std::get<1>(after_features),
            std::get<2>(after_features));

      reg_alloc_inc = 1;
    }
  }

  if (m_config.run_fast_reg_alloc) {
    auto timer = m_reg_alloc_timer.scope();
    auto allocator =
        fastregalloc::LinearScanAllocator(code, is_static, method_describer);
    allocator.allocate();
  }

  if (m_config.run_dedup_blocks) {
    auto timer = m_dedup_blocks_timer.scope();
    dedup_blocks_impl::Config config;
    dedup_blocks_impl::DedupBlocks dedup_blocks(
        &config, code, is_static, declaring_type, proto->get_args());
    dedup_blocks.run();
    dedup_blocks_stats = dedup_blocks.get_stats();
  }

  if (m_config.run_branch_prefix_hoisting) {
    auto timer = m_branch_prefix_hoisting_timer.scope();
    auto& cfg = code->cfg();
    Lazy<const constant_uses::ConstantUses> constant_uses([&] {
      return std::make_unique<const constant_uses::ConstantUses>(
          cfg, is_static, declaring_type, proto->get_rtype(), proto->get_args(),
          method_describer,
          /* force_type_inference */ true);
    });
    branch_prefix_hoisting_stats = branch_prefix_hoisting_impl::process_cfg(
        cfg, constant_uses, /* can_allocate_regs */ true, &join_stats);
  }

  auto data_after_dedup = get_features(kMMINLDataCollectionLevel);
  if (traceEnabled(MMINL, kMMINLDataCollectionLevel)) {
    TRACE(
        MMINL, kMMINLDataCollectionLevel,
        "Inliner.RegDedupe %zu|%zu|%zu|%zu|%zu|%zu|%zu|%zu",
        std::get<0>(data_before_reg_alloc), std::get<1>(data_before_reg_alloc),
        std::get<2>(data_before_reg_alloc), std::get<3>(data_before_reg_alloc),
        std::get<0>(data_after_dedup), std::get<1>(data_after_dedup),
        std::get<2>(data_after_dedup), std::get<3>(data_after_dedup));
  }

  std::lock_guard<std::mutex> guard(m_stats_mutex);
  m_const_prop_stats += const_prop_stats;
  m_cse_stats += cse_stats;
  m_copy_prop_stats += copy_prop_stats;
  m_local_dce_stats += local_dce_stats;
  m_dedup_blocks_stats += dedup_blocks_stats;
  m_methods_shrunk++;
  m_methods_reg_alloced += reg_alloc_inc;
  m_branch_prefix_hoisting_stats += branch_prefix_hoisting_stats;
  m_position_join_stats += join_stats;
  m_position_join_stats += dedup_blocks_stats.join_stats;
}

void Shrinker::log_metrics(ScopedMetrics& sm) const {
  auto scope = sm.scope("shrinker");
  m_const_prop_stats.log_metrics(sm);
  sm.set_metric(positions::metrics::kMarkedUnreliable,
                m_position_join_stats.marked_unreliable);
  sm.set_metric(positions::metrics::kNotRecorded,
                m_position_join_stats.not_recorded);
}

} // namespace shrinker
