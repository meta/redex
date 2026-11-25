/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <optional>
#include <string>
#include <vector>

#include "DeterministicContainers.h"
#include "DexClass.h"
#include "IRInstruction.h"
#include "MethodOverrideGraph.h"

struct ConfigFiles;

namespace clinit_batching {

/**
 * Result of the early class loads analysis.
 */
struct EarlyClassLoadsResult {
  // Classes that could be loaded before the orchestrator is called
  UnorderedSet<DexClass*> early_loaded_classes;

  // Entry point methods discovered from the manifest
  std::vector<DexMethod*> entry_points;

  // Whether the orchestrator invocation was encountered during the walk
  bool orchestrator_encountered{false};

  // Error message if the analysis failed
  std::optional<std::string> error_message;

  // A call reachable before the orchestrator whose target is unknown: a
  // virtual or interface call that the resolver cannot resolve (e.g. because
  // a type in the hierarchy has no definition), a dynamic invoke, or a library
  // call that runs a method handle's target. The classes it loads are then
  // unknown too, so `early_loaded_classes` is incomplete and must not be used
  // for batching.
  const IRInstruction* unknown_early_call{nullptr};
};

/**
 * Analyzes the callgraph from Android app entry points to identify classes
 * that could be loaded before the clinit batching orchestrator is called.
 *
 * Entry points include (in order of earliest invocation):
 * 1. AppComponentFactory constructor (API 28+)
 * 2. AppComponentFactory.instantiateClassLoader() (API 28+)
 * 3. AppComponentFactory.instantiateApplication() (API 28+)
 * 4. Application subclass constructor
 * 5. Application.attachBaseContext()
 *
 * Classes loaded before the orchestrator is called must be excluded from
 * clinit batching, as their static fields would be accessed before
 * initialization.
 */
class EarlyClassLoadsAnalysis {
 public:
  /**
   * Constructs the analysis.
   *
   * @param scope The class scope to analyze
   * @param orchestrator_method The method annotated with
   * @GenerateStaticInitBatch
   * @param conf Configuration files containing APK/manifest info
   * @param method_override_graph Override graph for virtual call resolution
   */
  EarlyClassLoadsAnalysis(
      DexMethod* orchestrator_method,
      ConfigFiles& conf,
      const method_override_graph::Graph* method_override_graph);

  /**
   * Runs the analysis and returns the result.
   */
  EarlyClassLoadsResult run();

 private:
  struct ManifestClassesResult {
    DexClass* application_class{nullptr};
    DexClass* app_component_factory{nullptr};
    std::optional<std::string> error_message;
  };

  ManifestClassesResult find_manifest_classes();

  void collect_application_entry_points(DexClass* application_class,
                                        std::vector<DexMethod*>& entry_points);

  void collect_app_component_factory_entry_points(
      DexClass* app_component_factory, std::vector<DexMethod*>& entry_points);

  void walk_callgraph(const std::vector<DexMethod*>& entry_points,
                      EarlyClassLoadsResult& result);

  DexMethod* m_orchestrator_method;
  ConfigFiles& m_conf;
  const method_override_graph::Graph* m_method_override_graph;

  // Android framework types
  const DexType* m_application_type;
  const DexType* m_app_component_factory_type;
  const DexType* m_context_type;
};

} // namespace clinit_batching
