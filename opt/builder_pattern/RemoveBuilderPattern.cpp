/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "RemoveBuilderPattern.h"

#include <boost/regex.hpp> // NOLINT

#include "BuilderTransform.h"
#include "ConfigFiles.h"
#include "Debug.h"
#include "DexClass.h"
#include "DexUtil.h"
#include "GlobalConfig.h"
#include "InitClassesWithSideEffects.h"
#include "MethodUtil.h"
#include "PassManager.h"
#include "Show.h"
#include "Trace.h"
#include "TypeSystem.h"
#include "Walkers.h"

namespace builder_pattern {

constexpr size_t MAX_NUM_INLINE_ITERATION = 4;
constexpr size_t ESCAPING_CALLEE_SIZE_THRESHOLD = 140;

namespace {

/**
 * Example: Lcom/facebook/RandomClassName; -> RandomClassName
 */
std::string only_class_name(const DexType* type) {
  std::string type_str(type->c_str());
  size_t package_delim = type_str.rfind('/');
  always_assert(package_delim != std::string::npos);

  size_t class_start = package_delim + 1;
  return type_str.substr(class_start, type_str.size() - package_delim - 2);
}

UnorderedSet<DexType*> get_associated_buildees(
    const UnorderedSet<const DexType*>& builders) {

  UnorderedSet<DexType*> buildees;
  for (const auto& builder : UnorderedIterable(builders)) {
    const auto builder_name = builder->str();
    std::string buildee_name =
        builder_name.substr(0, builder_name.size() - 9) + ";";

    auto* type = DexType::get_type(buildee_name);
    if (type != nullptr) {
      buildees.emplace(type);
    }
  }

  return buildees;
}

bool has_statics(const DexClass* cls) {
  always_assert(cls);
  const auto& dmethods = cls->get_dmethods();
  for (const auto* m : dmethods) {
    if (is_static(m)) {
      return true;
    }
  }

  return !cls->get_sfields().empty();
}

bool has_large_escaping_calls(const UnorderedSet<IRInstruction*>& to_inline) {
  for (const auto* invoke : UnorderedIterable(to_inline)) {
    always_assert(invoke->has_method());
    auto* callee = invoke->get_method()->as_def();
    size_t callee_size = callee->get_code()->sum_opcode_sizes();
    if (callee_size > ESCAPING_CALLEE_SIZE_THRESHOLD) {
      return true;
    }
  }
  return false;
}

class RemoveClasses {
 public:
  RemoveClasses(const DexType* super_cls,
                const Scope& scope,
                const ConfigFiles& conf,
                const init_classes::InitClassesWithSideEffects&
                    init_classes_with_side_effects,
                const inliner::InlinerConfig& inliner_config,
                const std::vector<const DexType*>& blocklist,
                const size_t max_num_inline_iteration,
                DexStoresVector& stores)
      : m_root(super_cls),
        m_scope(scope),
        m_blocklist(blocklist),
        m_type_system(scope),
        m_transform(scope,
                    conf,
                    super_cls,
                    init_classes_with_side_effects,
                    inliner_config,
                    stores),
        m_max_num_inline_iteration(max_num_inline_iteration) {
    gather_classes();
  }

  void optimize() {
    collect_excluded_types();

    if (m_root != type::java_lang_Object()) {
      // We can't inline a method that has super calls.
      for (const DexType* builder : UnorderedIterable(m_classes)) {
        if (!m_transform.inline_super_calls_and_ctors(builder)) {
          TRACE(BLD_PATTERN, 2,
                "Excluding type %s since we cannot inline super calls for all "
                "methods",
                SHOW(builder));
          m_excluded_types.emplace(builder);
        }
      }
    }

    update_usage();
  }

  void cleanup() { m_transform.cleanup(); }

  void print_stats(PassManager& mgr) {
    auto root_name = only_class_name(m_root);
    mgr.set_metric(root_name + "_total_classes", m_classes.size());
    mgr.set_metric(root_name + "_num_classes_excluded",
                   m_excluded_types.size());
    mgr.set_metric(root_name + "_num_total_usages", m_num_usages);
    mgr.set_metric(root_name + "_num_removed_usages", m_num_removed_usages);

    TRACE(BLD_PATTERN, 1, "num_classes_excluded %zu", m_excluded_types.size());
    TRACE(BLD_PATTERN, 1, "num_classes_removed %zu", m_removed_types.size());
    for (const auto& type : UnorderedIterable(m_excluded_types)) {
      TRACE(BLD_PATTERN, 2, "Excluded type: %s", SHOW(type));
    }
    mgr.set_metric(root_name + "_num_classes_removed", m_removed_types.size());
    for (const auto& type : UnorderedIterable(m_removed_types)) {
      TRACE(BLD_PATTERN, 2, "Removed type: %s", SHOW(type));
    }
    for (const auto& pair : m_num_inline_iterations) {
      std::stringstream metric;
      metric << "_num_inline_iteration_" << pair.first;
      mgr.incr_metric(root_name + metric.str(), pair.second);
      TRACE(BLD_PATTERN, 4, "%s_num_inline_iteration %zu %zu",
            root_name.c_str(), pair.first, pair.second);
    }
  }

 private:
  void gather_classes() {
    const TypeSet& subclasses = m_type_system.get_children(m_root);
    auto* object_type = type::java_lang_Object();
    boost::regex re("\\$Builder;$");

    for (const DexType* type : subclasses) {
      if (!m_type_system.get_children(type).empty()) {
        // Only leaf classes
        continue;
      }

      auto* cls = type_class(type);
      if ((cls == nullptr) || cls->is_external()) {
        continue;
      }

      if (m_root == object_type && has_statics(cls)) {
        // Only simple builders with no static methods or fields.
        continue;
      }
      // For Builders extending j/l/Object;, we filter by name.
      if (m_root != object_type || boost::regex_search(type->c_str(), re)) {
        m_classes.emplace(type);
      }
    }
  }

  void update_usage() {
    auto buildee_types = get_associated_buildees(m_classes);

    std::mutex methods_mutex;
    std::vector<DexMethod*> methods;

    walk::parallel::methods(m_scope, [&](DexMethod* method) {
      if ((method == nullptr) || !method::is_optimizable(method)) {
        return;
      }

      if ((m_classes.count(method->get_class()) != 0u) ||
          (buildee_types.count(method->get_class()) != 0u)) {
        // Skip builder and associated buildee methods.
        return;
      }

      BuilderAnalysis analysis(m_classes, m_excluded_types, method);
      analysis.run_analysis();
      if (analysis.has_usage()) {
        std::unique_lock<std::mutex> lock{methods_mutex};
        methods.push_back(method);
      }
    });

    if (methods.empty()) {
      return;
    }
    std::sort(methods.begin(), methods.end(), compare_dexmethods);

    for (auto* method : methods) {
      BuilderAnalysis analysis(m_classes, m_excluded_types, method);

      bool have_builders_to_remove =
          inline_builders_and_check_method(method, &analysis);
      m_num_usages += analysis.get_total_num_usages();
      m_num_inline_iterations[analysis.get_num_inline_iterations()]++;

      if (!have_builders_to_remove) {
        continue;
      }

      // When we get here we know that we can remove the builders.
      m_num_removed_usages += analysis.get_num_usages();

      auto removed_types = analysis.get_instantiated_types();
      TRACE(BLD_PATTERN, 2, "Removed following builders from %s", SHOW(method));
      for (const auto& type : UnorderedIterable(removed_types)) {
        m_removed_types.emplace(type);
        TRACE(BLD_PATTERN, 2, "\t %s", SHOW(type));
      }

      m_transform.replace_fields(analysis.get_usage(), method);
    }

    shrink_methods(methods);
  }

  void shrink_methods(const std::vector<DexMethod*>& methods) {
    // Run shrinking opts to optimize the changed methods.
    Timer t("shrink_methods");

    auto post_process = [&](DexMethod* method) {
      m_transform.get_shrinker().shrink_method(method);
      always_assert(method->get_code()->cfg_built());
    };

    // Walkers are over classes, so need to do this "manually."
    workqueue_run<DexMethod*>(post_process, methods);
  }

  void collect_excluded_types() {
    walk::fields(m_scope, [&](DexField* field) {
      auto* type = field->get_type();
      if (m_classes.count(type) != 0u) {
        TRACE(BLD_PATTERN, 2,
              "Excluding type since it is stored in a field: %s", SHOW(type));
        m_excluded_types.emplace(type);
      }
    });

    for (const DexType* type : m_blocklist) {
      if (m_classes.count(type) != 0u) {
        TRACE(BLD_PATTERN, 2,
              "Excluding type since it was in the blocklist: %s", SHOW(type));
        m_excluded_types.emplace(type);
      }
    }
  }

  /**
   * Returns true if there are builders that we can remove from the current
   * method.
   */
  bool inline_builders_and_check_method(DexMethod* method,
                                        BuilderAnalysis* analysis) {
    bool builders_to_remove = false;

    std::unique_ptr<IRCode> original_code = nullptr;
    size_t num_iterations = 1;

    for (; num_iterations < m_max_num_inline_iteration; num_iterations++) {
      analysis->run_analysis();

      if (!analysis->has_usage()) {
        TRACE(BLD_PATTERN, 6, "No builder to remove from %s", SHOW(method));
        break;
      }
      if (original_code == nullptr) {
        // Keep a copy of the code, in order to restore it, if needed.
        original_code = std::make_unique<IRCode>(*method->get_code());
      }

      // First bind virtual callsites to the current implementation, if any,
      // in order to be able to inline them.
      auto vinvoke_to_instance = analysis->get_vinvokes_to_this_infered_type();
      m_transform.update_virtual_calls(vinvoke_to_instance);

      // Inline all methods that are either called on the builder instance
      // or take the builder as an argument, except for the ctors.
      UnorderedSet<IRInstruction*> to_inline =
          analysis->get_all_inlinable_insns();
      if (to_inline.empty()) {
        TRACE(BLD_PATTERN, 3,
              "Everything that could be inlined was inlined for %s",
              SHOW(method));

        // Check if any of the instance builder types cannot be removed.
        auto non_removable_types = analysis->non_removable_types();
        if (!non_removable_types.empty()) {
          insert_unordered_iterable(m_excluded_types, non_removable_types);

          // Restore method and re-try. We will only
          // try removing non-excluded types.
          method->set_code(std::make_unique<IRCode>(*original_code));
          continue;
        } else {
          TRACE(BLD_PATTERN, 2,
                "Everything that could be inlined was inlined and none of "
                "the instances escape for %s",
                SHOW(method));
          analysis->print_usage();
          builders_to_remove = true;
          break;
        }
      }

      // For Simple Builders (the ones exntending j/l/Object;), if the escaping
      // callee is too large, we give up on inlining them. Instead, we treat all
      // `to_inline` calls as `not_inlined` and mark escaping types as excluded.
      UnorderedSet<IRInstruction*> not_inlined_insns;
      if (m_root != type::java_lang_Object() ||
          !has_large_escaping_calls(to_inline)) {
        not_inlined_insns = m_transform.try_inline_calls(method, to_inline);
      } else {
        not_inlined_insns = to_inline;
      }

      if (!not_inlined_insns.empty()) {
        auto escaped_builders =
            analysis->get_escaped_types_from_invokes(not_inlined_insns);
        insert_unordered_iterable(m_excluded_types, escaped_builders);

        if (not_inlined_insns.size() == to_inline.size()) {
          // Nothing left to do, since nothing was inlined.
          TRACE(BLD_PATTERN, 4, "Couldn't inline any of the methods in %s",
                SHOW(method));
          for (const auto& insn : UnorderedIterable(not_inlined_insns)) {
            TRACE(BLD_PATTERN, 5, "\t%s", SHOW(insn));
          }
          break;
        } else {
          // Restore method and re-try. We will only try inlining non-excluded
          // types.
          TRACE(BLD_PATTERN, 4, "Couldn't inline all the methods in %s",
                SHOW(method));
          for (const auto& insn : UnorderedIterable(not_inlined_insns)) {
            TRACE(BLD_PATTERN, 5, "\t%s", SHOW(insn));
          }
          method->set_code(std::make_unique<IRCode>(*original_code));
        }
      }

      // If we inlined everything, we still need to make sure we don't have
      // new methods to inline (for example from something that was inlined
      // in this step).
    }

    if (!builders_to_remove && original_code != nullptr) {
      method->set_code(std::move(original_code));
    }

    analysis->set_num_inline_iterations(num_iterations);
    return builders_to_remove;
  }

  const DexType* m_root;
  const Scope& m_scope;
  const std::vector<const DexType*>& m_blocklist;
  TypeSystem m_type_system;
  BuilderTransform m_transform;
  UnorderedSet<const DexType*> m_classes;
  UnorderedSet<const DexType*> m_excluded_types;
  UnorderedSet<const DexType*> m_removed_types;
  size_t m_num_usages{0};
  size_t m_num_removed_usages{0};
  size_t m_max_num_inline_iteration{0};
  std::map<size_t, size_t> m_num_inline_iterations;
};

} // namespace

void RemoveBuilderPatternPass::bind_config() {
  std::vector<const DexType*> roots;
  bind("roots", {}, roots, Configurable::default_doc(),
       Configurable::bindflags::types::warn_if_unresolvable);
  bind("blocklist", {}, m_blocklist, Configurable::default_doc(),
       Configurable::bindflags::types::warn_if_unresolvable);
  bind("max_num_iteration", MAX_NUM_INLINE_ITERATION,
       m_max_num_inline_iteration);

  // TODO(T44502473): if we could pass a binding filter lambda instead of
  // bindflags, this could be more simply expressed
  after_configuration([this, roots] {
    auto* object_type = type::java_lang_Object();
    m_roots.clear();
    for (const auto& root : roots) {
      if (type_class(root) == nullptr) {
        continue;
      }
      if (root != object_type) {
        auto* super_cls = type_class(root)->get_super_class();
        if (super_cls != object_type) {
          fprintf(stderr,
                  "[builders]: %s isn't a valid root as it extends %s\n",
                  root->c_str(), super_cls->c_str());
          continue;
        }
      }
      m_roots.push_back(root);
    }
  });
}

void RemoveBuilderPatternPass::run_pass(DexStoresVector& stores,
                                        ConfigFiles& conf,
                                        PassManager& mgr) {
  auto scope = build_class_scope(stores);
  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, conf.create_init_class_insns());

  for (const auto& root : m_roots) {
    TRACE(BLD_PATTERN, 1, "removing root %s w/ %zu iterations", SHOW(root),
          m_max_num_inline_iteration);
    Timer t("root_iteration");
    RemoveClasses rm_builder_pattern(
        root, scope, conf, init_classes_with_side_effects,
        *conf.get_global_config().get_config_by_name<InlinerConfig>("inliner"),
        m_blocklist, m_max_num_inline_iteration, stores);
    rm_builder_pattern.optimize();
    rm_builder_pattern.print_stats(mgr);
    rm_builder_pattern.cleanup();
  }
}

static RemoveBuilderPatternPass s_pass;

} // namespace builder_pattern
