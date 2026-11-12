/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ClassMergingPass.h"

#include "ClassMerging.h"
#include "ConfigFiles.h"
#include "ConfigUtils.h"
#include "Debug.h"
#include "DexUtil.h"
#include "InterDexGrouping.h"
#include "MergingStrategies.h"
#include "PassManager.h"
#include "Show.h"
#include "Trace.h"
#include "TypeSystem.h"

using namespace class_merging;

namespace {

template <typename Types>
void load_types(const std::vector<std::string>& type_names, Types& types) {
  std::vector<DexType*> ts = utils::get_types(type_names);
  for (const auto& t : ts) {
    const auto& cls = type_class(t);
    if (cls == nullptr) {
      TRACE(CLMG, 2, "Missing definition for type %s", SHOW(t));
      types.clear();
      return;
    }
    types.insert(t);
  }
}

/**
 * Verify model specs are consistent
 */
bool verify_model_spec(const std::vector<ModelSpec>& model_specs,
                       const ModelSpec& model_spec) {
  always_assert_log(
      !model_spec.name.empty(),
      "[ClassMerging] Wrong specification: model must have \"name\"");
  always_assert_log(!model_spec.class_name_prefix.empty(),
                    "[ClassMerging] Wrong specification: model %s must have "
                    "\"class_name_prefix\"",
                    model_spec.name.c_str());

  if (model_spec.roots.empty()) {
    // To share the configurations easily across apps, we ignore the models
    // without roots.
    TRACE(CLMG, 2,
          "[ClassMerging] Wrong specification: model %s must have \"roots\"",
          model_spec.name.c_str());
    return false;
  }

  for (const auto* const root : model_spec.roots) {
    always_assert_log(
        root,
        "[ClassMerging] Wrong specification: model %s must have \"roots\"",
        model_spec.name.c_str());
    if (type_class(root) == nullptr) {
      TRACE(CLMG, 2,
            "[ClassMerging] Wrong specification: model %s has \"root\" %s w/o "
            "definition",
            model_spec.name.c_str(), SHOW(root));
      return false;
    }
  }

  for (const auto& spec : model_specs) {
    bool duplicated =
        spec.name == model_spec.name || spec.roots == model_spec.roots;
    always_assert_log(!duplicated, "Duplicated model spec %s",
                      model_spec.name.c_str());
  }
  return true;
}

strategy::Strategy get_merging_strategy(const std::string& merging_strategy) {
  const static UnorderedMap<std::string, strategy::Strategy>
      string_to_strategy = {
          {"by_cls_count", strategy::Strategy::BY_CLASS_COUNT},
          {"by_code_size", strategy::Strategy::BY_CODE_SIZE},
          {"by_refs", strategy::Strategy::BY_REFS}};

  always_assert_log(string_to_strategy.count(merging_strategy) > 0,
                    "Merging strategy %s not found. Please check the list"
                    " of accepted values.",
                    merging_strategy.c_str());
  return string_to_strategy.at(merging_strategy);
}

TypeTagConfig get_type_tag_config(const std::string& type_tag_config) {
  const static UnorderedMap<std::string, TypeTagConfig> string_to_config = {
      {"none", TypeTagConfig::NONE},
      {"generate", TypeTagConfig::GENERATE},
      {"input-pass-type-tag-to-ctor",
       TypeTagConfig::INPUT_PASS_TYPE_TAG_TO_CTOR},
      {"input-handled", TypeTagConfig::INPUT_HANDLED}};
  always_assert_log(string_to_config.count(type_tag_config) > 0,
                    "Type tag config type %s not found. Please check the list"
                    " of accepted values.",
                    type_tag_config.c_str());
  TRACE(CLMG, 5, "type tag config %s %d", type_tag_config.c_str(),
        string_to_config.at(type_tag_config));
  return string_to_config.at(type_tag_config);
}

TypeLikeStringConfig get_type_like_string_config(
    const std::string& type_like_string_config) {
  const static UnorderedMap<std::string, TypeLikeStringConfig>
      string_to_config = {{"replace", TypeLikeStringConfig::REPLACE},
                          {"exclude", TypeLikeStringConfig::EXCLUDE}};
  return string_to_config.at(type_like_string_config);
}

} // namespace

namespace class_merging {

void ClassMergingPass::bind_config() {
  bool process_method_meta;
  bind("process_method_meta", false, process_method_meta);
  int64_t max_num_dispatch_target;
  bind("max_num_dispatch_target", 0, max_num_dispatch_target);
  trait(Traits::Pass::unique, true);
  bool use_stable_shape_names;
  bind("use_stable_shape_names", false, use_stable_shape_names);
  bool skip_anonymous_classes;
  bind("skip_anonymous_classes", false, skip_anonymous_classes);
  bool preserve_unanimous_field_types;
  bind("preserve_unanimous_field_types", false, preserve_unanimous_field_types,
       "Keep unanimous reference slot types when they are safe to reference.");
  bool update_method_profiles_stats;
  bind("update_method_profiles_stats", true, update_method_profiles_stats,
       "Whether to update method profiles stats for merged methods.");

  // load model specifications
  std::vector<Json::Value> models;
  bind("models", {}, models);

  std::string interdex_grouping_inferring_mode;
  bind("interdex_grouping_inferring_mode", "class-loads",
       interdex_grouping_inferring_mode);

  after_configuration([this, max_num_dispatch_target,
                       models = std::move(models),
                       interdex_grouping_inferring_mode =
                           std::move(interdex_grouping_inferring_mode),
                       process_method_meta, skip_anonymous_classes,
                       preserve_unanimous_field_types, use_stable_shape_names,
                       update_method_profiles_stats] {
    if (max_num_dispatch_target > 0) {
      m_max_num_dispatch_target =
          std::optional<size_t>(static_cast<size_t>(max_num_dispatch_target));
    }

    if (models.empty()) {
      return;
    }

    // load each model spec for erasure
    for (auto it = models.begin(); it != models.end(); ++it) {
      const auto& value = *it;
      always_assert_log(
          value.isObject(),
          "[ClassMerging] Wrong specification: model in array not an object");
      JsonWrapper model_spec = JsonWrapper(value);
      ModelSpec model;
      model_spec.get("enabled", true, model.enabled);
      std::string type_tag_config;
      model_spec.get("type_tag_config", "generate", type_tag_config);
      model.type_tag_config = get_type_tag_config(type_tag_config);
      size_t min_count;
      model_spec.get("min_count", 2, min_count);
      model.min_count = min_count > 0 ? min_count : 0;
      model_spec.get("name", "", model.name);
      std::vector<std::string> root_names;
      model_spec.get("roots", {}, root_names);
      load_types(root_names, model.roots);
      std::vector<std::string> excl_names;
      model_spec.get("exclude", {}, excl_names);
      utils::load_types_and_prefixes(excl_names, model.exclude_types,
                                     model.exclude_prefixes);
      model_spec.get("class_name_prefix", "", model.class_name_prefix);
      Json::Value generated;
      model_spec.get("generated", Json::Value(), generated);
      if (!generated.isNull()) {
        if (!generated.isObject()) {
          fprintf(stderr,
                  "[ClassMerging] Wrong specification: model in array not an "
                  "object\n");
          m_model_specs.clear();
          return;
        }
        JsonWrapper gen_spec = JsonWrapper(generated);
        std::vector<std::string> gen_names;
        gen_spec.get("other_roots", {}, gen_names);
        load_types(gen_names, model.gen_types);

        std::vector<std::string> gen_anno_names;
        gen_spec.get("annos", {}, gen_anno_names);
        load_types(gen_anno_names, model.gen_annos);
      }

      std::vector<std::string> const_class_safe_names;
      model_spec.get("const_class_safe_types", {}, const_class_safe_names);
      load_types(const_class_safe_names, model.const_class_safe_types);

      model_spec.get("include_primary_dex", false, model.include_primary_dex);

      // Merging strategy is by default `by_cls_count`.
      std::string merging_strategy;
      model_spec.get("merging_strategy", "by_cls_count", merging_strategy);
      model.strategy = get_merging_strategy(merging_strategy);

      // InterDex grouping option is by default `non-ordered-set`.
      std::string interdex_grouping;
      model_spec.get("interdex_grouping", "non-ordered-set", interdex_grouping);
      model.interdex_config.init_type(interdex_grouping);

      always_assert_log(!model.interdex_config.is_enabled() ||
                            (model.type_tag_config != TypeTagConfig::NONE),
                        "Cannot group %s when type tag is not needed.",
                        model.name.c_str());

      model_spec.get("hot_cold_grouping", false, model.hot_cold_grouping);

      std::string interdex_grouping_inferring_mode_local;
      model_spec.get("interdex_grouping_inferring_mode",
                     interdex_grouping_inferring_mode,
                     interdex_grouping_inferring_mode_local);

      size_t max_count;
      model_spec.get("max_count", 0, max_count);
      Json::Value approximate_shaping;
      model_spec.get("approximate_shape_merging", Json::Value(),
                     model.approximate_shape_merging);
      model_spec.get("merge_types_with_static_fields", false,
                     model.merge_types_with_static_fields);
      model_spec.get("keep_debug_info", false, model.keep_debug_info);

      // TypeLikeStringConfig defaults to `exclude`.
      std::string type_like_string_config;
      model_spec.get("type_like_string_config", "exclude",
                     type_like_string_config);
      model.type_like_string_confg =
          get_type_like_string_config(type_like_string_config);
      if (model.type_like_string_confg == TypeLikeStringConfig::REPLACE) {
        always_assert_log(
            model.type_tag_config != TypeTagConfig::GENERATE,
            "Type like strings are not safe to replace with TypeTagConfig %s",
            type_tag_config.c_str());
      }

      if (max_count > 0) {
        model.max_count = std::optional<size_t>(max_count);
      }
      model.process_method_meta = process_method_meta;
      model.max_num_dispatch_target = m_max_num_dispatch_target;
      model.use_stable_shape_names = use_stable_shape_names;
      model.skip_anonymous_classes = skip_anonymous_classes;
      model.preserve_unanimous_field_types = preserve_unanimous_field_types;
      model.update_method_profiles_stats = update_method_profiles_stats;
      // Assume config based models are all generated code.
      model_spec.get("is_generated_code", true, model.is_generated_code);

      model.interdex_config.init_inferring_mode(
          interdex_grouping_inferring_mode_local);

      if (!verify_model_spec(m_model_specs, model)) {
        continue;
      }

      m_model_specs.emplace_back(std::move(model));
    }

    TRACE(CLMG, 2, "[ClassMerging] valid model specs %zu",
          m_model_specs.size());
  });
}

void ClassMergingPass::run_pass(DexStoresVector& stores,
                                ConfigFiles& conf,
                                PassManager& mgr) {
  mgr.set_metric("num_merged_volatile_fields", 0);
  mgr.set_metric("num_merged_final_fields", 0);
  if (m_model_specs.empty()) {
    return;
  }

  auto scope = build_class_scope(stores);
  TypeSystem type_system(scope);
  // Built once, before the spec loop, and shared across specs -- like
  // type_system -- so every spec reads the same pre-merge scope even though
  // merge_model mutates `scope` between iterations.
  virtual_scope::VirtualScopes vscopes(scope);
  ModelStats total_stats;
  for (ModelSpec& model_spec : m_model_specs) {
    if (!model_spec.enabled) {
      continue;
    }
    if (conf.force_single_dex() && !model_spec.include_primary_dex) {
      TRACE(CLMG, 2,
            "Change include_primary_dex to true because the apk will be single "
            "dex");
      model_spec.include_primary_dex = true;
    }
    if (model_spec.merging_targets.empty()) {
      class_merging::load_roots_subtypes_as_merging_targets(type_system,
                                                            &model_spec);
    }
    if (model_spec.merging_targets.empty()) {
      continue;
    }
    total_stats += class_merging::merge_model(type_system, vscopes, scope, conf,
                                              mgr, stores, model_spec, false);
  }
  post_dexen_changes(scope, stores);
  total_stats.update_redex_stats(" total", mgr);
}

static ClassMergingPass s_pass;

} // namespace class_merging
