/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

/*
 * This analysis identifies all classes that are loaded before the clinit
 * batching orchestrator method runs. These classes must be excluded from
 * batching, because their static fields would be accessed before the batched
 * initialization has had a chance to run.
 *
 * Background: The ClinitBatchingPass transforms hot class initializers
 * (<clinit>) by extracting their bodies into separate __initStatics$*()
 * methods, removing the original clinits (making the classes "trivially
 * initialized"), and collecting all the extracted methods into a single
 * orchestrator method that is called early during app startup. The
 * orchestrator method is marked with @GenerateStaticInitBatch and is
 * expected to be called from Application.attachBaseContext() or similar.
 *
 * The problem: If a class's clinit is removed but its static fields are
 * accessed before the orchestrator runs, those fields will have their
 * zero/null default values instead of the values the clinit would have
 * assigned. We must therefore identify every class that could be loaded
 * before the orchestrator call and exclude it from batching.
 *
 * Entry points:
 *
 * The analysis starts from Android app entry points discovered by parsing
 * the AndroidManifest.xml. The Android framework invokes these methods
 * in the following order during app startup:
 *
 *   1. AppComponentFactory.<init>()          (API 28+, optional)
 *   2. AppComponentFactory.instantiateClassLoader()  (API 28+)
 *   3. AppComponentFactory.instantiateApplication()  (API 28+)
 *   4. Application.<init>()
 *   5. Application.attachBaseContext(Context)
 *
 * The orchestrator call typically lives inside attachBaseContext(). Any
 * class loaded by the framework or by user code that runs before that
 * call must be excluded.
 *
 * Core algorithm — BFS callgraph walk with two-phase processing within
 * each method:
 *
 * The analysis performs a BFS traversal of the callgraph starting from
 * the entry points. BFS (as opposed to DFS) is essential for soundness:
 * it guarantees that all methods at depth N are fully processed before
 * any method at depth N+1 is examined. This matters because the set of
 * loaded classes grows monotonically during the walk, and virtual call
 * resolution at depth N+1 depends on knowing which classes were loaded
 * by all sibling methods at depth N.
 *
 * Each method is processed in two phases:
 *
 *   Phase 1 — Collect class loads: Scan every instruction for operations
 *   that trigger class loading per the JVM specification:
 *     - invoke-static: loads the target class
 *     - sget/sput: loads the field's declaring class
 *     - new-instance: loads the instantiated class
 *     - const-class: loads the referenced class
 *     - instance-of: loads the checked class
 *     - check-cast: loads the cast target class
 *     - filled-new-array: loads the array element class
 *   When a class is loaded, its entire superclass chain and all
 *   implemented interfaces are also loaded (and their <clinit> methods
 *   are added to the BFS worklist, since clinit execution can
 *   transitively load more classes).
 *
 *   Phase 2 — Resolve callees: Scan again for call instructions and
 *   add their targets to the BFS worklist. This phase runs after
 *   Phase 1 so that the loaded_classes set is up to date for virtual
 *   call resolution (see below).
 *
 * Key insight — virtual/interface call filtering:
 *
 * For invoke-static and invoke-direct, the callee is statically known
 * and is always added to the worklist. For invoke-virtual and
 * invoke-interface, however, the actual dispatch target depends on the
 * runtime type of the receiver. We cannot know the receiver type, but
 * we can observe that a virtual override can only be dispatched to if
 * its declaring class has been loaded. If a class has not been loaded,
 * no object of that class can exist, so no virtual call can dispatch
 * to its methods. We therefore only follow overrides whose declaring
 * class is already in the loaded_classes set.
 *
 * This is the central insight that makes the analysis precise without
 * being unsound: we avoid over-approximating the set of reachable
 * methods (which would cause us to exclude too many classes from
 * batching) while still being conservative (any override that could
 * actually be dispatched to will be followed, because its class must
 * have been loaded by some prior instruction).
 *
 * The two-phase structure ensures this works correctly: by the time
 * Phase 2 runs for a method, Phase 1 has already added all classes
 * loaded by that method's instructions, so the virtual call filter
 * sees the complete picture.
 *
 * invoke-super handling:
 *
 * invoke-super resolves to a specific method in the caller's superclass
 * hierarchy. We use a manual superclass walk instead of resolve_method()
 * because resolve_method(ref, Super) without a caller falls back to a
 * Virtual search starting from the ref's declaring class, not the
 * caller's superclass.
 *
 * Orchestrator detection with dominance analysis:
 *
 * When the method containing the orchestrator call is found, we must
 * be precise about which instructions execute before vs. after the
 * orchestrator. A naive approach would stop processing the method
 * entirely upon seeing the call, but this is incorrect: in branching
 * control flow, some paths might not go through the orchestrator at all.
 *
 * We therefore compute the dominator tree. An
 * instruction is skipped (considered "after the orchestrator") only if
 * its block is strictly dominated by the orchestrator's block, or if
 * it appears after the orchestrator call within the same block.
 * Instructions in blocks not dominated by the orchestrator block are
 * still processed, because they might execute on a control flow path
 * that does not pass through the orchestrator call.
 *
 * Class hierarchy collection:
 *
 * Per the JVM specification (JVMS 5.5), when a class is initialized,
 * its direct superclass must be initialized first (if not already), and
 * so on recursively up the hierarchy. Similarly, interface initialization
 * is triggered. We model this by recursively collecting the entire
 * superclass chain and all implemented interfaces whenever a class is
 * added to loaded_classes. Each newly loaded class's <clinit> is also
 * added to the BFS worklist, since clinit execution can itself load
 * additional classes through static field accesses, static calls, and
 * object allocations.
 */

#include "EarlyClassLoadsAnalysis.h"

#include <array>
#include <queue>

#include "ConfigFiles.h"
#include "ControlFlow.h" // NOLINT(facebook-unused-include-check)
#include "DexUtil.h"
#include "Dominators.h"
#include "IRInstruction.h"
#include "MethodOverrideGraph.h"
#include "MethodUtil.h"
#include "RedexResources.h"
#include "Resolver.h"
#include "Show.h"
#include "Trace.h"
#include "TypeUtil.h"

namespace clinit_batching {

namespace {
constexpr size_t kMaxBfsVisited = 10000;

const char* const kApplicationType = "Landroid/app/Application;";
const char* const kAppComponentFactoryType =
    "Landroid/app/AppComponentFactory;";
const char* const kContextType = "Landroid/content/Context;";

// Checks if cls extends (directly or transitively) the given base type.
bool extends_class(DexClass* cls, const DexType* base_type) {
  if (cls == nullptr || base_type == nullptr) {
    return false;
  }

  const DexType* current_type = cls->get_type();
  while (current_type != nullptr) {
    if (current_type == base_type) {
      return true;
    }

    DexClass* current_cls = type_class(current_type);
    if (current_cls == nullptr) {
      break;
    }
    current_type = current_cls->get_super_class();
  }

  return false;
}

void collect_class_hierarchy(DexClass* cls,
                             UnorderedSet<DexClass*>& loaded_classes,
                             UnorderedSet<const DexMethod*>* visited,
                             std::queue<const DexMethod*>* worklist) {
  if (cls == nullptr || !loaded_classes.insert(cls).second) {
    return;
  }

  // When a class is loaded, its <clinit> is executed. Add it to the worklist.
  if (visited != nullptr && worklist != nullptr) {
    DexMethod* clinit = cls->get_clinit();
    if (clinit != nullptr && visited->insert(clinit).second) {
      worklist->push(clinit);
    }
  }

  // Collect superclass
  auto* super_type = cls->get_super_class();
  if (super_type != nullptr) {
    auto* super_cls = type_class(super_type);
    collect_class_hierarchy(super_cls, loaded_classes, visited, worklist);
  }

  // Collect implemented interfaces
  auto* interfaces = cls->get_interfaces();
  if (interfaces != nullptr) {
    for (const auto* intf_type : *interfaces) {
      auto* intf_cls = type_class(intf_type);
      collect_class_hierarchy(intf_cls, loaded_classes, visited, worklist);
    }
  }
}

void collect_loaded_classes(IRInstruction* insn,
                            UnorderedSet<DexClass*>& loaded_classes,
                            UnorderedSet<const DexMethod*>& visited,
                            std::queue<const DexMethod*>& worklist) {
  auto opcode = insn->opcode();
  DexClass* cls = nullptr;

  if (opcode::is_invoke_static(opcode)) {
    // INVOKE_STATIC: target class is loaded
    auto* method_ref = insn->get_method();
    if (method_ref != nullptr) {
      cls = type_class(method_ref->get_class());
    }
  } else if (opcode::is_an_sget(opcode) || opcode::is_an_sput(opcode)) {
    // SGET*/SPUT*: the declaring class's clinit is triggered.
    // Resolve the field to find the actual declaring class, since
    // SubClass.parentField triggers Parent's clinit, not SubClass's.
    auto* field_ref = insn->get_field();
    if (field_ref != nullptr) {
      auto* resolved_field = resolve_field(field_ref, FieldSearch::Static);
      cls = resolved_field != nullptr ? type_class(resolved_field->get_class())
                                      : type_class(field_ref->get_class());
    }
  } else if (opcode == OPCODE_NEW_INSTANCE || opcode == OPCODE_CONST_CLASS ||
             opcode == OPCODE_INSTANCE_OF || opcode == OPCODE_CHECK_CAST) {
    // NEW_INSTANCE / CONST_CLASS / INSTANCE_OF / CHECK_CAST: the referenced
    // class is loaded
    cls = type_class(insn->get_type());
  } else if (opcode == OPCODE_FILLED_NEW_ARRAY) {
    // FILLED_NEW_ARRAY: the array element class is loaded
    const auto* arr_type = insn->get_type();
    if (arr_type != nullptr) {
      const auto* elem_type = type::make_element_type_if_array(arr_type);
      if (elem_type != nullptr) {
        cls = type_class(elem_type);
      }
    }
  }

  if (cls != nullptr) {
    collect_class_hierarchy(cls, loaded_classes, &visited, &worklist);
  }
}

} // namespace

EarlyClassLoadsAnalysis::EarlyClassLoadsAnalysis(
    DexMethod* orchestrator_method,
    ConfigFiles& conf,
    const method_override_graph::Graph* method_override_graph)
    : m_orchestrator_method(orchestrator_method),
      m_conf(conf),
      m_method_override_graph(method_override_graph) {
  m_application_type = DexType::get_type(kApplicationType);
  m_app_component_factory_type = DexType::get_type(kAppComponentFactoryType);
  m_context_type = DexType::get_type(kContextType);
}

EarlyClassLoadsResult EarlyClassLoadsAnalysis::run() {
  EarlyClassLoadsResult result;

  always_assert_log(
      m_orchestrator_method != nullptr &&
          m_orchestrator_method->is_concrete() &&
          m_orchestrator_method->get_code() != nullptr,
      "EarlyClassLoadsAnalysis: orchestrator method %s is not resolvable "
      "(concrete=%d, has_code=%d)",
      SHOW(m_orchestrator_method),
      m_orchestrator_method ? m_orchestrator_method->is_concrete() : 0,
      m_orchestrator_method ? (m_orchestrator_method->get_code() != nullptr)
                            : 0);

  // Step 1: Find Application and AppComponentFactory classes from manifest
  auto [application_class, app_component_factory, manifest_error] =
      find_manifest_classes();
  if (manifest_error.has_value()) {
    result.error_message = std::move(manifest_error);
    return result;
  }

  // Step 2: Collect entry point methods in actual invocation order.
  // AppComponentFactory runs before Application in the Android bootstrap
  // sequence, and the order matters: the BFS processes methods in FIFO order,
  // and earlier methods' class loads expand the loaded_classes set used to
  // filter virtual call overrides for later methods.
  if (app_component_factory != nullptr) {
    collect_app_component_factory_entry_points(app_component_factory,
                                               result.entry_points);
  }
  if (application_class != nullptr) {
    collect_application_entry_points(application_class, result.entry_points);
  }

  if (result.entry_points.empty()) {
    result.error_message =
        "No entry point methods found from Application or AppComponentFactory";
    return result;
  }

  TRACE(CLINIT_BATCHING,
        2,
        "EarlyClassLoadsAnalysis: found %zu entry points",
        result.entry_points.size());

  // Step 3: Walk callgraph from entry points
  walk_callgraph(result.entry_points, result);

  TRACE(CLINIT_BATCHING,
        1,
        "EarlyClassLoadsAnalysis: found %zu early loaded classes, "
        "orchestrator %s",
        result.early_loaded_classes.size(),
        result.orchestrator_encountered ? "encountered" : "not encountered");

  return result;
}

EarlyClassLoadsAnalysis::ManifestClassesResult
EarlyClassLoadsAnalysis::find_manifest_classes() {
  ManifestClassesResult result;

  // Get APK directory from config
  std::string apk_dir;
  m_conf.get_json_config().get("apk_dir", "", apk_dir);
  if (apk_dir.empty()) {
    result.error_message = "No apk_dir specified in config";
    return result;
  }

  // Parse manifest to get application classes
  std::unique_ptr<AndroidResources> resources;
  ManifestClassInfo manifest_info;
  try {
    resources = create_resource_reader(apk_dir);
    manifest_info = resources->get_manifest_class_info();
  } catch (const std::exception& e) {
    result.error_message = std::string("Error reading manifest: ") + e.what();
    return result;
  }

  // Find Application and AppComponentFactory classes
  for (const auto& class_name :
       UnorderedIterable(manifest_info.application_classes)) {
    DexType* type = DexType::get_type(class_name);
    if (type == nullptr) {
      TRACE(CLINIT_BATCHING,
            3,
            "EarlyClassLoadsAnalysis: manifest class %s not found as type",
            class_name.c_str());
      continue;
    }

    DexClass* cls = type_class(type);
    if (cls == nullptr) {
      TRACE(CLINIT_BATCHING,
            3,
            "EarlyClassLoadsAnalysis: manifest class %s has no DexClass",
            class_name.c_str());
      continue;
    }

    // Determine if this is Application or AppComponentFactory
    if (m_application_type != nullptr &&
        extends_class(cls, m_application_type)) {
      always_assert_log(
          result.application_class == nullptr,
          "EarlyClassLoadsAnalysis: multiple Application classes in manifest: "
          "%s and %s",
          SHOW(result.application_class), SHOW(cls));
      result.application_class = cls;
      TRACE(CLINIT_BATCHING,
            2,
            "EarlyClassLoadsAnalysis: found Application class %s",
            SHOW(cls));
    } else if (m_app_component_factory_type != nullptr &&
               extends_class(cls, m_app_component_factory_type)) {
      result.app_component_factory = cls;
      TRACE(CLINIT_BATCHING,
            2,
            "EarlyClassLoadsAnalysis: found AppComponentFactory class %s",
            SHOW(cls));
    }
  }

  if (result.application_class == nullptr) {
    result.error_message =
        "Application class not found in manifest or not in scope";
    return result;
  }

  // AppComponentFactory is optional (API 28+)
  if (result.app_component_factory == nullptr) {
    TRACE(CLINIT_BATCHING,
          2,
          "EarlyClassLoadsAnalysis: no AppComponentFactory found (optional)");
  }

  return result;
}

void EarlyClassLoadsAnalysis::collect_application_entry_points(
    DexClass* application_class, std::vector<DexMethod*>& entry_points) {
  // Add all constructors
  size_t ctor_count = 0;
  for (DexMethod* dmethod : application_class->get_dmethods()) {
    if (method::is_init(dmethod)) {
      entry_points.push_back(dmethod);
      ctor_count++;
      TRACE(CLINIT_BATCHING,
            3,
            "EarlyClassLoadsAnalysis: entry point - Application.<init> %s",
            SHOW(dmethod));
    }
  }
  always_assert_log(ctor_count > 0,
                    "EarlyClassLoadsAnalysis: Application class %s has no "
                    "constructors",
                    SHOW(application_class));

  // Add attachBaseContext(Context) - walk up class hierarchy to find it
  const DexString* attach_base_context_name =
      DexString::get_string("attachBaseContext");
  always_assert_log(attach_base_context_name != nullptr,
                    "EarlyClassLoadsAnalysis: attachBaseContext string not "
                    "found in dex");
  always_assert_log(m_context_type != nullptr,
                    "EarlyClassLoadsAnalysis: android.content.Context type not "
                    "found in dex");

  DexTypeList* args = DexTypeList::make_type_list({m_context_type});
  DexProto* proto = DexProto::make_proto(type::_void(), args);

  // Walk up the class hierarchy to find attachBaseContext
  // (it may be defined in a superclass like NonBlockingApplication)
  DexMethod* found_attach = nullptr;
  DexClass* current_class = application_class;
  while (current_class != nullptr && !current_class->is_external()) {
    for (DexMethod* vmethod : current_class->get_vmethods()) {
      if (vmethod->get_name() == attach_base_context_name &&
          vmethod->get_proto() == proto) {
        found_attach = vmethod;
        break;
      }
    }
    if (found_attach != nullptr) {
      break;
    }
    auto* super_type = current_class->get_super_class();
    current_class = (super_type != nullptr) ? type_class(super_type) : nullptr;
  }
  always_assert_log(found_attach != nullptr,
                    "EarlyClassLoadsAnalysis: attachBaseContext not found in "
                    "Application class %s or its superclasses",
                    SHOW(application_class));
  entry_points.push_back(found_attach);
  TRACE(CLINIT_BATCHING,
        3,
        "EarlyClassLoadsAnalysis: entry point - "
        "Application.attachBaseContext %s",
        SHOW(found_attach));
}

void EarlyClassLoadsAnalysis::collect_app_component_factory_entry_points(
    DexClass* app_component_factory, std::vector<DexMethod*>& entry_points) {
  // Add all constructors
  size_t ctor_count = 0;
  for (DexMethod* dmethod : app_component_factory->get_dmethods()) {
    if (method::is_init(dmethod)) {
      entry_points.push_back(dmethod);
      ctor_count++;
      TRACE(CLINIT_BATCHING,
            3,
            "EarlyClassLoadsAnalysis: entry point - AppComponentFactory.<init> "
            "%s",
            SHOW(dmethod));
    }
  }
  always_assert_log(ctor_count > 0,
                    "EarlyClassLoadsAnalysis: AppComponentFactory class %s has "
                    "no constructors",
                    SHOW(app_component_factory));

  // Add instantiateClassLoader and instantiateApplication
  static constexpr std::array<const char*, 2> factory_methods = {
      "instantiateClassLoader", "instantiateApplication"};

  for (const auto* method_name : factory_methods) {
    const DexString* name = DexString::get_string(method_name);
    if (name == nullptr) {
      TRACE(CLINIT_BATCHING, 3,
            "EarlyClassLoadsAnalysis: %s string not found in dex, skipping",
            method_name);
      continue;
    }

    bool found = false;
    for (DexMethod* vmethod : app_component_factory->get_vmethods()) {
      if (vmethod->get_name() == name) {
        entry_points.push_back(vmethod);
        found = true;
        TRACE(CLINIT_BATCHING,
              3,
              "EarlyClassLoadsAnalysis: entry point - AppComponentFactory.%s "
              "%s",
              method_name,
              SHOW(vmethod));
      }
    }
    if (!found) {
      // The method may be inherited from the base AppComponentFactory class
      // and not overridden. This is expected — skip silently.
      TRACE(CLINIT_BATCHING, 3,
            "EarlyClassLoadsAnalysis: AppComponentFactory.%s not overridden "
            "in %s, skipping",
            method_name, SHOW(app_component_factory));
    }
  }
}

void EarlyClassLoadsAnalysis::walk_callgraph(
    const std::vector<DexMethod*>& entry_points,
    EarlyClassLoadsResult& result) {
  // BFS through the callgraph
  // BFS is essential for soundness: it processes all methods at depth N before
  // depth N+1, so class loads from all siblings are visible when processing
  // their shared callees.
  std::queue<const DexMethod*> worklist;
  UnorderedSet<const DexMethod*> visited;

  // Reference to loaded_classes for convenience
  UnorderedSet<DexClass*>& loaded_classes = result.early_loaded_classes;

  // Initialize with entry points and their classes
  for (DexMethod* entry : entry_points) {
    worklist.push(entry);
    visited.insert(entry);
    // Entry point classes are loaded by the framework
    if (auto* cls = type_class(entry->get_class())) {
      collect_class_hierarchy(cls, loaded_classes, &visited, &worklist);
    }
  }

  while (!worklist.empty()) {
    const DexMethod* method = worklist.front();
    worklist.pop();

    if (visited.size() > kMaxBfsVisited) {
      TRACE(CLINIT_BATCHING,
            1,
            "EarlyClassLoadsAnalysis: BFS visited limit reached (%zu methods),"
            " bailing out to be safe",
            visited.size());
      result.error_message =
          "BFS visited limit reached — pre-orchestrator callgraph too large";
      return;
    }

    if (method->get_code() == nullptr) {
      continue;
    }

    // Collect the class of this method (may already be in loaded_classes)
    DexClass* method_class = type_class(method->get_class());
    if (method_class != nullptr) {
      collect_class_hierarchy(method_class, loaded_classes, &visited,
                              &worklist);
    }

    // InstructionIterable requires non-const access for implementation reasons,
    // but we only read instructions. This const_cast is safe.
    auto* code = const_cast<IRCode*>(method->get_code());

    // Processes callees from a single instruction, adding them to the worklist.
    auto process_callees = [&](IRInstruction* insn) {
      auto opcode = insn->opcode();
      if (!opcode::is_an_invoke(opcode)) {
        return;
      }

      auto* callee_ref = insn->get_method();
      if (callee_ref == nullptr) {
        return;
      }

      if (opcode::is_invoke_static(opcode) ||
          opcode::is_invoke_direct(opcode)) {
        auto search = opcode::is_invoke_static(opcode) ? MethodSearch::Static
                                                       : MethodSearch::Direct;
        auto* callee = resolve_method(callee_ref, search);
        if (callee != nullptr && visited.insert(callee).second) {
          worklist.push(callee);
        }
      } else if (opcode::is_invoke_super(opcode)) {
        // Manual superclass walk instead of resolve_method because
        // resolve_method(ref, Super) without a caller falls back to a
        // Virtual search starting from the ref's declaring class, not the
        // caller's superclass (see T132919742).
        auto* caller_cls = type_class(method->get_class());
        if (caller_cls != nullptr) {
          auto* super_type = caller_cls->get_super_class();
          auto* current = super_type ? type_class(super_type) : nullptr;
          while (current != nullptr && !current->is_external()) {
            for (auto* vm : current->get_vmethods()) {
              if (vm->get_name() == callee_ref->get_name() &&
                  vm->get_proto() == callee_ref->get_proto()) {
                if (visited.insert(vm).second) {
                  worklist.push(vm);
                }
                current = nullptr; // break outer loop
                break;
              }
            }
            if (current != nullptr) {
              auto* next_super = current->get_super_class();
              current = next_super ? type_class(next_super) : nullptr;
            }
          }
        }
      } else if ((opcode::is_invoke_virtual(opcode) ||
                  opcode::is_invoke_interface(opcode)) &&
                 m_method_override_graph != nullptr) {
        auto search = opcode::is_invoke_virtual(opcode)
                          ? MethodSearch::Virtual
                          : MethodSearch::Interface;
        auto* base_callee = resolve_method(callee_ref, search);
        if (base_callee == nullptr) {
          return;
        }

        auto* base_class = type_class(base_callee->get_class());
        if (base_class != nullptr && loaded_classes.count(base_class) != 0) {
          if (visited.insert(base_callee).second) {
            worklist.push(base_callee);
          }
        }

        // Only follow overrides whose declaring class is already loaded.
        // A virtual dispatch can only reach an override if an instance of
        // that class exists, which requires the class to have been loaded.
        // This is the key precision insight: it avoids over-approximating
        // the reachable method set while remaining sound.
        method_override_graph::all_overriding_methods(
            *m_method_override_graph, base_callee,
            [&](const DexMethod* overrider) {
              auto* overrider_class = type_class(overrider->get_class());
              if (overrider_class == nullptr ||
                  loaded_classes.count(overrider_class) == 0) {
                return true; // continue
              }
              if (visited.insert(overrider).second) {
                worklist.push(overrider);
              }
              return true; // continue
            },
            /* include_interfaces */ true);
      }
    };

    // Find the orchestrator call in this method's CFG, if present.
    always_assert(code->cfg_built());
    auto& cfg = code->cfg();
    cfg::Block* orch_block = nullptr;
    IRInstruction* orch_insn = nullptr;
    for (auto* block : cfg.blocks()) {
      for (auto& mie : ir_list::InstructionIterable(block)) {
        if (opcode::is_invoke_static(mie.insn->opcode())) {
          auto* callee_ref = mie.insn->get_method();
          if (callee_ref != nullptr) {
            auto* callee = resolve_method(callee_ref, MethodSearch::Static);
            if (callee == m_orchestrator_method) {
              orch_block = block;
              orch_insn = mie.insn;
              break;
            }
          }
        }
      }
      if (orch_block != nullptr) {
        break;
      }
    }

    if (orch_block != nullptr) {
      // This method contains the orchestrator call. Use dominance analysis
      // to skip only instructions dominated by the orchestrator call, and
      // still process instructions/callees that are NOT dominated by it.
      result.orchestrator_encountered = true;
      TRACE(CLINIT_BATCHING,
            3,
            "EarlyClassLoadsAnalysis: found orchestrator call in %s, using "
            "dominance analysis",
            SHOW(method));

      auto doms = dominators::SimpleFastDominators<cfg::GraphInterface>(cfg);

      // Pre-compute the set of blocks strictly dominated by the
      // orchestrator's block. A block B is strictly dominated by
      // orch_block iff walking up B's idom chain reaches orch_block
      // before reaching B itself (i.e., orch_block != B).
      UnorderedSet<cfg::Block*> dominated_blocks;
      for (auto* block : cfg.blocks()) {
        if (block == orch_block) {
          continue;
        }
        auto* runner = block;
        while (true) {
          auto* idom = doms.get_idom(runner);
          if (idom == runner) {
            // Reached the entry node without finding orch_block
            break;
          }
          if (idom == orch_block) {
            dominated_blocks.insert(block);
            break;
          }
          runner = idom;
        }
      }

      // Iterate non-dominated instructions, applying a callback to each.
      auto for_each_non_dominated = [&](auto&& callback) {
        for (auto* block : cfg.blocks()) {
          if (dominated_blocks.count(block) != 0) {
            continue;
          }
          for (auto& mie : ir_list::InstructionIterable(block)) {
            if (block == orch_block && mie.insn == orch_insn) {
              break;
            }
            callback(mie.insn);
          }
        }
      };

      // PHASE 1: Collect class loads from non-dominated instructions.
      for_each_non_dominated([&](IRInstruction* insn) {
        collect_loaded_classes(insn, loaded_classes, visited, worklist);
      });

      // PHASE 2: Process callees from non-dominated instructions.
      for_each_non_dominated(process_callees);

      continue;
    }

    // No orchestrator in this method — use the standard path.
    // PHASE 1: Collect all class loads from this method.
    for (auto* block : cfg.blocks()) {
      for (auto& mie : ir_list::InstructionIterable(block)) {
        collect_loaded_classes(mie.insn, loaded_classes, visited, worklist);
      }
    }

    // PHASE 2: Resolve callees with updated loaded_classes.
    for (auto* block : cfg.blocks()) {
      for (auto& mie : ir_list::InstructionIterable(block)) {
        process_callees(mie.insn);
      }
    }
  }

  TRACE(CLINIT_BATCHING,
        2,
        "EarlyClassLoadsAnalysis: walked %zu methods, found %zu early loaded "
        "classes",
        visited.size(),
        result.early_loaded_classes.size());
}

} // namespace clinit_batching
