/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ReachableNatives.h"

#include <algorithm>
#include <array>
#include <fstream>
#include <iterator>
#include <span>
#include <sstream>
#include <string>
#include <string_view>

#include "ConfigFiles.h"
#include "ControlFlow.h"
#include "CppUtil.h"
#include "Debug.h"
#include "DexClass.h"
#include "DexUtil.h"
#include "IRCode.h"
#include "IROpcode.h"
#include "LiveRange.h"
#include "PassManager.h"
#include "Reachability.h"
#include "RedexContext.h"
#include "Resolver.h"
#include "ScopedCFG.h"
#include "Show.h"
#include "Trace.h"
#include "Walkers.h"
#include "WorkQueue.h"

using namespace std::string_literals;

void ReachableNativesPass::bind_config() {
  bind("output_file_name", "redex-reachable-natives.txt", m_output_file_name);
  bind("live_load_library_file_name", "redex-live-load-library.txt",
       m_live_load_library_file_name);
  bind("dead_load_library_file_name", "redex-dead-load-library.txt",
       m_dead_load_library_file_name);
  bind("analyze_load_library", false, m_analyze_load_library);
  bind("additional_load_library_names", {}, m_additional_load_library_names);
  bind("sweep", false, m_sweep);
  bind("sweep_native_methods", false, m_sweep_native_methods);
  after_configuration(
      [this] { always_assert(!m_sweep_native_methods || m_sweep); });
}

std::vector<const IRInstruction*> ReachableNativesPass::gather_load_library(
    DexMethod* caller, InsertOnlyConcurrentSet<const DexString*>* names) {
  std::vector<const IRInstruction*> non_const_defs;
  if ((m_load_library_methods.count(caller) != 0u) ||
      (m_load_library_unsafe_methods.count(caller) != 0u)) {
    return non_const_defs;
  }
  cfg::ScopedCFG cfg(caller->get_code());
  Lazy<live_range::UseDefChains> udchain(
      [&]() { return live_range::MoveAwareChains(*cfg).get_use_def_chains(); });
  for (auto& mie : InstructionIterable(*cfg)) {
    auto* insn = mie.insn;
    if (!opcode::is_invoke_static(insn->opcode())) {
      continue;
    }
    auto* callee = resolve_invoke_method_deprecated(insn, caller);
    if (callee == nullptr) {
      continue;
    }
    if (m_load_library_methods.count(callee) == 0u) {
      continue;
    }
    for (auto* def : (*udchain)[live_range::Use{insn, 0}]) {
      if (opcode::is_const_string(def->opcode())) {
        names->insert(def->get_string());
        continue;
      }
      non_const_defs.push_back(def);
    }
  }
  return non_const_defs;
}

namespace {

constexpr std::string_view kSoLoader = "Lcom/facebook/soloader/SoLoader;";
constexpr std::string_view kNativeLoader =
    "Lcom/facebook/soloader/nativeloader/NativeLoader;";

constexpr auto kSoLoaderUnsafeMethods = std::to_array<std::string_view>(
    {"Lcom/facebook/soloader/SoLoader;.loadLibraryUnsafe:(Ljava/lang/String;)Z",
     "Lcom/facebook/soloader/SoLoader;.loadLibraryUnsafe:(Ljava/lang/"
     "String;I)Z"});

constexpr auto kSoLoaderMethods = std::to_array<std::string_view>(
    {"Lcom/facebook/soloader/SoLoader;.loadLibrary:(Ljava/lang/String;)Z",
     "Lcom/facebook/soloader/SoLoader;.loadLibrary:(Ljava/lang/String;I)Z"});

constexpr auto kNativeLoaderMethods = std::to_array<std::string_view>(
    {"Lcom/facebook/soloader/nativeloader/NativeLoader;.loadLibrary:(Ljava/"
     "lang/String;)Z",
     "Lcom/facebook/soloader/nativeloader/NativeLoader;.loadLibrary:(Ljava/"
     "lang/String;I)Z"});

constexpr size_t kSoLoaderEntryPointCount =
    std::size(kSoLoaderUnsafeMethods) + std::size(kSoLoaderMethods);

// Pin a load-library entry point so later passes cannot inline, outline or
// delete it, and hand it back so the caller can recognize calls to it. Returns
// nullptr when the input contains no reference to the method at all; whether
// that is legitimate is a question about the declaring class, decided by
// assert_class_fully_recognized below.
//
// A method that IS referenced is an assert in both of the ways it can fail to
// be usable:
//
//   - referenced but not defined in the input (SoLoader supplied as a library
//     jar rather than in the dexes). The app demonstrably loads native
//     libraries, but the pass cannot pin the entry point, so
//     gather_load_library will not recognize those call sites and the analysis
//     would silently under-approximate the live library set. Failing loudly
//     beats stripping native code that is actually reachable.
//   - defined but not static. That signature belongs to SoLoader, so a
//     non-static one means the input is not the SoLoader this pass knows how to
//     reason about.
DexMethod* pin_load_library_entry_point(std::string_view method_name) {
  auto* method_ref = DexMethod::get_method(method_name);
  if (method_ref == nullptr) {
    return nullptr;
  }
  auto* method = method_ref->as_def();
  always_assert_log(method,
                    "%s is referenced but not defined in the input; the "
                    "load-library analysis cannot pin it",
                    std::string(method_name).c_str());
  always_assert_log(is_static(method), "Expected %s to be static",
                    std::string(method_name).c_str());
  method->rstate.set_root();
  method->rstate.set_dont_inline();
  method->rstate.set_no_outlining();
  return method;
}

size_t pin_entry_points(std::span<const std::string_view> method_names,
                        UnorderedSet<DexMethod*>* pinned) {
  size_t count = 0;
  for (auto method_name : method_names) {
    if (auto* method = pin_load_library_entry_point(method_name)) {
      pinned->insert(method);
      ++count;
    }
  }
  return count;
}

bool is_class_in_input(std::string_view class_name) {
  auto* type = DexType::get_type(class_name);
  if (type == nullptr) {
    return false;
  }
  auto* cls = type_class(type);
  return cls != nullptr && !cls->is_external();
}

// The unit of absence is the class.
//
// A class the input does not contain is a legitimate shape rather than a
// configuration error: an app that links no native libraries never pulls
// SoLoader in, and NativeLoader ships as a standalone artifact that other
// libraries depend on without SoLoader, so neither class can be demanded of the
// other. Asserting instead of skipping aborts the build for such an app
// whenever a shared config enables analyze_load_library, which is a config
// written for that app's siblings rather than a defect in the app. With no
// entry points collected there is nothing for the analysis to recognize, and
// eval_pass returns before walking the program.
//
// A class the input DOES contain must declare every entry point this pass
// knows. A subset means something rewrote it -- a rename, a shrink, or a
// SoLoader version this pass has not been taught -- and the sibling that was
// renamed rather than removed still has call sites that gather_load_library
// would no longer recognize. Skipping an unreferenced method is harmless in
// itself; staying quiet about a class that no longer looks like SoLoader is
// not.
void assert_class_fully_recognized(std::string_view class_name,
                                   size_t pinned,
                                   size_t expected) {
  if (pinned == 0 && !is_class_in_input(class_name)) {
    return;
  }
  always_assert_log(pinned == expected,
                    "%s is in the input, but only %zu of the %zu load-library "
                    "entry points this pass knows are present; something "
                    "rewrote it, and the ones that remain cannot be trusted to "
                    "be all of them",
                    std::string(class_name).c_str(), pinned, expected);
}

// The callers that pass a load-library entry point a library name that is not
// a constant string, each with the instructions that define that name.
using NonConstNameCallers =
    InsertOnlyConcurrentMap<DexMethod*, std::vector<std::string>>;

void record_non_const_name_caller(
    DexMethod* caller,
    const std::vector<const IRInstruction*>& non_const_defs,
    NonConstNameCallers* callers) {
  if (non_const_defs.empty()) {
    return;
  }
  std::vector<std::string> shown_defs;
  shown_defs.reserve(non_const_defs.size());
  for (const auto* def : non_const_defs) {
    shown_defs.push_back(show(def));
  }
  std::sort(shown_defs.begin(), shown_defs.end());
  shown_defs.erase(std::unique(shown_defs.begin(), shown_defs.end()),
                   shown_defs.end());
  callers->emplace(caller, std::move(shown_defs));
}

std::string show_non_const_name_callers(const NonConstNameCallers& callers) {
  std::ostringstream oss;
  for (auto* caller : unordered_to_ordered_keys(callers, compare_dexmethods)) {
    oss << "  " << show(caller) << "\n";
    for (const auto& def : callers.at(caller)) {
      oss << "    library name defined by: " << def << "\n";
    }
  }
  return oss.str();
}

} // namespace

void ReachableNativesPass::eval_pass(DexStoresVector& stores,
                                     ConfigFiles&,
                                     PassManager&) {
  if (m_eval_number++ > 0) {
    return;
  }
  if (!m_analyze_load_library) {
    return;
  }
  size_t soloader_pinned =
      pin_entry_points(kSoLoaderUnsafeMethods, &m_load_library_unsafe_methods) +
      pin_entry_points(kSoLoaderMethods, &m_load_library_methods);
  size_t nativeloader_pinned =
      pin_entry_points(kNativeLoaderMethods, &m_load_library_methods);

  assert_class_fully_recognized(kSoLoader, soloader_pinned,
                                kSoLoaderEntryPointCount);
  assert_class_fully_recognized(kNativeLoader, nativeloader_pinned,
                                std::size(kNativeLoaderMethods));

  m_pinned_load_library_entry_points = soloader_pinned + nativeloader_pinned;
  TRACE(NATIVE, 1,
        "Pinned load-library entry points: %zu on SoLoader, %zu on "
        "NativeLoader",
        soloader_pinned, nativeloader_pinned);

  for (auto& library_name : m_additional_load_library_names) {
    g_redex->library_names.insert(DexString::make_string(library_name));
  }
  if (m_load_library_unsafe_methods.empty() && m_load_library_methods.empty()) {
    // gather_load_library only recognizes a callee that is in one of these
    // sets, so the walk below would build a CFG for every method in the app to
    // match nothing.
    return;
  }
  NonConstNameCallers non_const_name_callers;
  walk::parallel::code(
      build_class_scope(stores), [&](DexMethod* caller, IRCode&) {
        record_non_const_name_caller(
            caller, gather_load_library(caller, &g_redex->library_names),
            &non_const_name_callers);
      });
  always_assert_log(
      non_const_name_callers.empty(),
      "Found callers of SoLoader.loadLibrary / NativeLoader.loadLibrary that "
      "do not supply a constant library name string:\n%sThis is not supported, "
      "as it prevents identifying which libraries are referenced. Either "
      "change the call to use loadLibraryUnsafe and add possibly library names "
      "to via additional_load_library_names option to the "
      "ReachableNativesPass, or, preferably, refactor the code so that "
      "loadLibrary is called with string constants only.",
      show_non_const_name_callers(non_const_name_callers).c_str());
}

void ReachableNativesPass::analyze_final_load_library(
    const DexClasses& scope,
    ConfigFiles& cfg,
    PassManager& mgr,
    const std::function<bool(DexMethod*)>& reachable_fn) {
  InsertOnlyConcurrentSet<const DexString*> final_library_names;
  for (auto& library_name : m_additional_load_library_names) {
    final_library_names.insert(DexString::make_string(library_name));
  }
  NonConstNameCallers non_const_name_callers;
  walk::parallel::code(scope, [&](DexMethod* caller, IRCode&) {
    if (!reachable_fn(caller)) {
      return;
    }
    record_non_const_name_caller(
        caller, gather_load_library(caller, &final_library_names),
        &non_const_name_callers);
  });

  // TODO: There is chance that some Redex pass does a code transformation that
  // moves the const-string away, e.g. DedupStringsPass. Consider introducing a
  // "load-library" (pseudo) instruction that takes a string literal, to avoid
  // that.
  always_assert_log(
      non_const_name_callers.empty(),
      "Found reachable callers of SoLoader.loadLibrary / "
      "NativeLoader.loadLibrary that no longer supply a constant library name "
      "string:\n%sThe first ReachableNativesPass accepted every call, so a "
      "pass that ran since then moved the library name away from the call, "
      "and the libraries that remain live can no longer be determined.",
      show_non_const_name_callers(non_const_name_callers).c_str());

  mgr.set_metric("initial_library_names", g_redex->library_names.size());
  mgr.set_metric("final_library_names", final_library_names.size());
  TRACE(NATIVE, 1, "Reachable Library Names: %zu => %zu",
        g_redex->library_names.size(), final_library_names.size());

  for (const auto* library_name : UnorderedIterable(final_library_names)) {
    always_assert(g_redex->library_names.count(library_name));
  }
  auto ordered =
      unordered_to_ordered(g_redex->library_names, compare_dexstrings);

  std::ofstream live_ofs(cfg.metafile(m_live_load_library_file_name),
                         std::ofstream::out | std::ofstream::trunc);
  std::ofstream dead_ofs(cfg.metafile(m_dead_load_library_file_name),
                         std::ofstream::out | std::ofstream::trunc);
  for (const auto* library_name : ordered) {
    if (final_library_names.count(library_name) != 0u) {
      live_ofs << library_name->str() << "\n";
      TRACE(NATIVE, 2, "live library: %s", library_name->c_str());
    } else {
      dead_ofs << library_name->str() << "\n";
      TRACE(NATIVE, 2, "dead library: %s", library_name->c_str());
    }
  }
}

void ReachableNativesPass::run_pass(DexStoresVector& stores,
                                    ConfigFiles& cfg,
                                    PassManager& mgr) {
  m_run_number++;
  const auto& file_name = cfg.metafile(m_output_file_name);
  auto trace_opts = [this]() {
    if (m_run_number == 1) {
      return std::ofstream::out | std::ofstream::trunc;
    }
    return std::ofstream::out | std::ofstream::app;
  }();

  std::ofstream ofs(file_name, trace_opts);

  auto log_line = [&ofs](const auto& line) {
    TRACE(NATIVE, 2, "%s", line);
    ofs << line << "\n";
  };

  log_line(
      ("ReachableNativesPass Run "s + std::to_string(m_run_number)).c_str());

  auto scope = build_class_scope(stores);
  UnorderedSet<const DexClass*> scope_set(scope.begin(), scope.end());
  auto reachable_objects = std::make_unique<reachability::ReachableObjects>();
  reachability::ReachableAspects reachable_aspects;
  reachability::ConditionallyMarked cond_marked;
  auto method_override_graph = method_override_graph::build_graph(scope);

  ConcurrentSet<reachability::ReachableObject,
                reachability::ReachableObjectHash>
      root_set;
  reachability::RootSetMarker root_set_marker(
      *method_override_graph, false, false, false, &cond_marked,
      reachable_objects.get(), &root_set);

  TRACE(NATIVE, 2, "Blanket Native Classes: %zu",
        g_redex->blanket_native_root_classes.size());
  TRACE(NATIVE, 2, "Blanket Native Methods: %zu",
        g_redex->blanket_native_root_methods.size());

  root_set_marker.mark_with_exclusions(scope,
                                       g_redex->blanket_native_root_classes,
                                       g_redex->blanket_native_root_methods);

  size_t num_threads = redex_parallel::default_num_threads();
  reachability::IgnoreSets ignore_sets;
  reachability::Stats stats;
  reachability::TransitiveClosureMarkerSharedState shared_state{
      scope_set,
      &ignore_sets,
      method_override_graph.get(),
      false,
      false,
      false,
      false,
      false,
      false,
      &cond_marked,
      reachable_objects.get(),
      &reachable_aspects,
      &stats};
  workqueue_run<reachability::ReachableObject>(
      [&](reachability::TransitiveClosureMarkerWorkerState* worker_state,
          const reachability::ReachableObject& obj) {
        reachability::TransitiveClosureMarkerWorker worker(&shared_state,
                                                           worker_state);
        worker.visit(obj);
        return nullptr;
      },
      root_set, num_threads,
      /* push_tasks_while_running */ true);
  compute_zombie_methods(*method_override_graph, *reachable_objects,
                         reachable_aspects);

  UnorderedSet<DexMethod*> reachable_natives;
  UnorderedSet<DexMethod*> unreachable_natives;

  walk::methods(scope, [&](DexMethod* m) {
    if (is_native(m)) {
      if (reachable_objects->marked_unsafe(static_cast<DexMethodRef*>(m))) {
        log_line(SHOW(m));
        reachable_natives.insert(m);
      } else {
        unreachable_natives.insert(m);
      }
    }
  });

  log_line("Native methods reachable from non-native:");
  for (auto* m : UnorderedIterable(reachable_natives)) {
    log_line(SHOW(m));
  }
  log_line("");

  log_line("Native methods unreachable from non-native:");
  for (auto* m : UnorderedIterable(unreachable_natives)) {
    log_line(SHOW(m));
  }
  log_line("");

  TRACE(NATIVE, 1, "Reachable Natives: %zu, Unreachable Natives: %zu",
        reachable_natives.size(), unreachable_natives.size());

  mgr.set_metric("reachable_natives", reachable_natives.size());
  mgr.set_metric("unreachable_natives", unreachable_natives.size());
  // Recorded in eval_pass and reported here: PassManager only has a current
  // pass to attribute a metric to while a pass is running.
  mgr.set_metric("pinned_load_library_entry_points",
                 m_pinned_load_library_entry_points);

  if (m_sweep || m_sweep_native_methods) {
    size_t classes_abstracted{0};
    if (!m_sweep_native_methods) {
      // Native methods and their declaring classes themselves must remain
      // reachable, as they may get referenced by native registration code, so
      // we re-include them in the reachable object set, and mark classes as
      // abstract that are only kept for this reason.
      for (auto* m : UnorderedIterable(unreachable_natives)) {
        reachable_objects->mark(m);
        self_recursive_fn(
            [&](auto self, const DexType* type) {
              auto* cls = type_class(type);
              if (!scope_set.count(cls) ||
                  reachable_objects->marked_unsafe(cls)) {
                return;
              }
              reachable_objects->mark(cls);
              self(self, cls->get_super_class());
              for (const auto* intf_type : *cls->get_interfaces()) {
                self(self, intf_type);
              }
              if (!is_abstract(cls)) {
                classes_abstracted++;
                cls->set_access((cls->get_access() & ~ACC_FINAL) |
                                ACC_ABSTRACT);
              }
            },
            m->get_class());
      }
    }

    auto before = reachability::count_objects(stores);
    reachability::sweep(stores, *reachable_objects);
    auto after = reachability::count_objects(stores);

    TRACE(NATIVE, 1, "after: %zu classes, %zu fields, %zu methods",
          after.num_classes, after.num_fields, after.num_methods);
    mgr.incr_metric("classes_removed", before.num_classes - after.num_classes);
    mgr.incr_metric("fields_removed", before.num_fields - after.num_fields);
    mgr.incr_metric("methods_removed", before.num_methods - after.num_methods);
    mgr.incr_metric("classes_abstracted", classes_abstracted);
  }

  if (m_run_number != m_eval_number) {
    return;
  }

  analyze_final_load_library(scope, cfg, mgr, [&](DexMethod* caller) {
    return reachable_objects->marked_unsafe(caller);
  });
}

static ReachableNativesPass s_pass;
