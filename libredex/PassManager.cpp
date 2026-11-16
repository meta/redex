/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "PassManager.h"
#include "Debug.h"
#include "DexAssessments.h"

#include <cinttypes>
#include <cstdio>
#include <cstdlib>
#include <ctime>
#include <exception>
#include <fstream>
#include <functional>
#include <iostream>
#include <json/value.h>
#include <limits>
#include <sstream>
#include <utility>

#include "AnalysisUsage.h"
#include "ApiLevelChecker.h"
#include "Armv7JitLoopChecker.h"
#include "AssetManager.h"
#include "ClassChecker.h"
#include "CommandProfiling.h"
#include "ConfigFiles.h"
#include "DexClass.h"
#include "DexStructure.h"
#include "DexUtil.h"
#include "GlobalConfig.h"
#include "GraphVisualizer.h"
#include "IRCode.h"
#include "IRTypeChecker.h"
#include "JemallocUtil.h"
#include "MethodProfiles.h"
#include "Native.h"
#include "OptData.h"
#include "Pass.h"
#include "PrintSeeds.h"
#include "ProguardPrintConfiguration.h"
#include "ProguardReporting.h"
#include "RedexContext.h"
#include "RedexPropertiesManager.h"
#include "Sanitizers.h"
#include "ScopedMemStats.h"
#include "ScopedMetrics.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "SourceBlocksViolations.h"
#include "ThreadPool.h"
#include "Timer.h"
#include "Trace.h"
#include "Walkers.h"

namespace {

AccumulatingTimer m_hashers_timer{"PassManager.Hashers"};
AccumulatingTimer m_check_unique_deobfuscateds_timer{
    "PassManager.CheckUniqueDeobfuscateds"};

constexpr const char* INCOMING_HASHES = "incoming_hashes.txt";
constexpr const char* OUTGOING_HASHES = "outgoing_hashes.txt";
constexpr const char* REMOVABLE_NATIVES = "redex-removable-natives.txt";
constexpr const char* CLASS_REORDERING_PASS_NAME = "ClassReorderingPass";
constexpr std::string_view PASS_ORDER_KEY{"pass_order"};

const Pass* get_profiled_pass(const PassManager& mgr) {
  const auto* profile_pass_name = getenv("PROFILE_PASS");
  redex_assert(profile_pass_name != nullptr);
  // Resolve the pass in the constructor so that any typos / references to
  // nonexistent passes are caught as early as possible
  const auto* pass = mgr.find_pass(profile_pass_name);
  always_assert_log(pass != nullptr, "Could not find pass named %s",
                    profile_pass_name);
  std::cerr << "Will run profiler for " << pass->name() << '\n';
  return pass;
}

// Returns the pass named by MALLOC_PROFILE_PASS, or nullptr when the variable
// is unset. Like get_profiled_pass, this resolves the name up front so typos
// are caught before any pass runs.
const Pass* get_malloc_profile_pass(const PassManager& mgr) {
  const auto* malloc_profile_pass_name = getenv("MALLOC_PROFILE_PASS");
  if (malloc_profile_pass_name == nullptr) {
    return nullptr;
  }
  const auto* pass = mgr.find_pass(malloc_profile_pass_name);
  always_assert_log(pass != nullptr, "Could not find pass named %s",
                    malloc_profile_pass_name);
  fprintf(stderr, "Will run jemalloc profiler for %s\n", pass->name().c_str());
  return pass;
}

std::string get_apk_dir(const ConfigFiles& config) {
  auto apkdir = config.get_json_config()["apk_dir"].asString();
  apkdir.erase(std::remove(apkdir.begin(), apkdir.end(), '"'), apkdir.end());
  return apkdir;
}

class CheckerConfig {
 public:
  CheckerConfig(const ConfigFiles& conf,
                Architecture arch,
                bool disabled = false)
      : m_arch(arch), m_disabled(disabled) {
    const auto& global_config = conf.get_global_config();
    always_assert(global_config.has_config_by_name("ir_type_checker"));
    m_config = *global_config.get_config_by_name<IRTypeCheckerConfig>(
        "ir_type_checker");
  }

  void on_input(const Scope& scope) {
    if (m_disabled) {
      return;
    }
    if (!m_config.run_on_input) {
      std::cerr << "Note: input type checking is turned off!" << '\n';
      return;
    }

    auto res = check_no_overwrite_this(false)
                   .validate_access(true)
                   .check_armv7_jit_loops(JitLoopCheck::REPORT)
                   .run_verifier(scope, /* exit_on_fail= */ false);
    if (!res) {
      return; // No issues.
    }
    if (!m_config.run_on_input_ignore_access) {
      std::string msg = *res;
      msg +=
          "\n If you are confident that this does not matter (e.g., because "
          "you are using MakePublicPass), turn off accessibility checking on "
          "input with `-J ir_type_checker.run_on_input_ignore_access=true`.\n "
          "You may turn off all input checking with `-J "
          "ir_type_checker.run_on_input=false`.";
      fail_error(std::move(msg));
    }

    res = check_no_overwrite_this(false)
              .validate_access(false)
              .check_armv7_jit_loops(JitLoopCheck::REPORT)
              .run_verifier(scope, /* exit_on_fail= */ false);
    if (!res) {
      std::cerr << "Warning: input has accessibility issues. Continuing."
                << '\n';
      return; // "No" issues.
    }
    std::string msg = *res;
    msg +=
        "\n If you are confident that this does not matter, turn off input "
        "checking with `-J ir_type_checker.run_on_input=false`.";
    fail_error(std::move(msg));
  }

  bool run_after_pass(const Pass* pass) {
    return m_config.run_after_each_pass ||
           m_config.run_after_passes.count(pass->name()) > 0;
  }

  // Literate style.
  CheckerConfig check_no_overwrite_this(bool val) const {
    CheckerConfig ret = *this;
    ret.m_config.check_no_overwrite_this = val;
    return ret;
  }
  CheckerConfig validate_access(bool val) const {
    CheckerConfig ret = *this;
    ret.m_validate_access = val;
    return ret;
  }

  // The ARMv7 JIT loop check is whole-program and its offenders are expected
  // to persist across passes, so it runs on the input and at the end only.
  enum class JitLoopCheck { SKIP, REPORT, ENFORCE };
  CheckerConfig check_armv7_jit_loops(JitLoopCheck val) const {
    CheckerConfig ret = *this;
    ret.m_jit_loop_check = val;
    return ret;
  }

  std::optional<std::string> run_verifier(const Scope& scope,
                                          bool exit_on_fail = true) {
    if (m_disabled) {
      return std::nullopt;
    }

    if (m_config.check_classes) {
      TRACE(PM, 1, "Running ClassChecker...");
      Timer t1("ClassChecker");

      ClassChecker class_checker;
      class_checker.init_setting(
          m_config.definition_check, m_config.definition_check_allowlist,
          m_config.definition_check_allowlist_prefixes, m_config.external_check,
          m_config.external_check_allowlist,
          m_config.external_check_allowlist_prefixes);
      class_checker.run(scope);
      if (class_checker.fail()) {
        std::ostringstream oss = class_checker.print_failed_classes();
        always_assert_log(!exit_on_fail, "%s", oss.str().c_str());
        return oss.str();
      }
    }

    TRACE(PM, 1, "Running IRTypeChecker...");
    Timer t("IRTypeChecker");

    struct Result {
      size_t errors{0};
      DexMethod* smallest_error_method{nullptr};
      size_t smallest_size{std::numeric_limits<size_t>::max()};

      Result() = default;
      explicit Result(DexMethod* m)
          : errors(1),
            smallest_error_method(m),
            smallest_size(m->get_code()->count_opcodes()) {}

      Result& operator+=(const Result& other) {
        errors += other.errors;
        if (smallest_size > other.smallest_size) {
          smallest_size = other.smallest_size;
          smallest_error_method = other.smallest_error_method;
        }
        return *this;
      }
    };

    auto run_checker_tmpl = [&](DexMethod* dex_method, auto fn) {
      IRTypeChecker checker(dex_method, m_validate_access,
                            m_config.validate_invoke_super);
      if (m_config.verify_moves) {
        checker.verify_moves();
      }
      if (m_config.check_no_overwrite_this) {
        checker.check_no_overwrite_this();
      }
      checker.relaxed_init_check();
      return fn(std::move(checker));
    };
    auto run_checker = [&](DexMethod* dex_method) {
      return run_checker_tmpl(dex_method, [](auto checker) {
        checker.run();
        return checker;
      });
    };
    // Takes the checker that already failed on `dex_method`, so that the dump
    // can point at the instruction it tripped over.
    auto run_checker_error = [&](DexMethod* dex_method,
                                 const IRTypeChecker& checker) {
      if (m_config.annotated_cfg_on_error) {
        if (m_config.annotated_cfg_on_error_reduced) {
          return checker.dump_annotated_cfg_on_error(dex_method);
        } else {
          return checker.dump_annotated_cfg(dex_method);
        }
      }
      auto* code = dex_method->get_code();
      return code->cfg_built() ? show(code->cfg()) : show(code);
    };

    auto res =
        walk::parallel::methods<Result>(scope, [&](DexMethod* dex_method) {
          auto checker = run_checker(dex_method);
          if (!checker.fail()) {
            return Result();
          }
          return Result(dex_method);
        });

    if (res.errors != 0) {
      // Re-run the smallest method to produce error message.
      auto checker = run_checker(res.smallest_error_method);
      redex_assert(checker.fail());

      std::ostringstream oss;
      oss << "Inconsistency found in Dex code for "
          << show(res.smallest_error_method) << '\n'
          << " " << checker.what() << '\n'
          << "Code:" << '\n'
          << run_checker_error(res.smallest_error_method, checker);

      if (res.errors > 1) {
        oss << "\n(" << (res.errors - 1) << " more issues!)";
      }

      always_assert_log(!exit_on_fail, "%s", oss.str().c_str());
      return oss.str();
    }

    return run_armv7_jit_loop_checker(scope, exit_on_fail);
  }

  std::optional<std::string> run_armv7_jit_loop_checker(const Scope& scope,
                                                        bool exit_on_fail) {
    if (m_jit_loop_check == JitLoopCheck::SKIP ||
        !Armv7JitLoopChecker::can_crash(m_arch)) {
      return std::nullopt;
    }
    TRACE(PM, 1, "Running Armv7JitLoopChecker...");
    Timer t("Armv7JitLoopChecker");

    Armv7JitLoopChecker checker(
        m_config.armv7_jit_loop_max_score,
        {m_config.armv7_jit_loop_large_frame_carried_values,
         m_config.armv7_jit_loop_large_frame_weight_divisor});
    checker.run(scope);
    bool enforce = m_jit_loop_check == JitLoopCheck::ENFORCE;
    TRACE(PM, 1, "Armv7JitLoopChecker on %s: highest score %" PRIu64,
          enforce ? "output" : "input", checker.highest_score());
    if (!checker.fail()) {
      return std::nullopt;
    }
    auto msg = checker.print_offenders();
    // Failing on the input would blame Redex for code it was given; the input
    // report is there to tell such offenders apart from ones a pass created.
    if (!enforce) {
      std::cerr << "Warning: on input, " << msg << '\n';
      return std::nullopt;
    }
    always_assert_log(!exit_on_fail, "%s", msg.c_str());
    return msg;
  }

  [[noreturn]] static void fail_error(std::string error_msg,
                                      size_t errors = 1) {
    if (errors > 1) {
      error_msg.append("\n(");
      error_msg.append(std::to_string(errors - 1));
      error_msg.append(" more issues!)");
    }
    assert_fail_impl("type-checker", RedexError::TYPE_CHECK_ERROR, "%s",
                     error_msg.c_str());
  }

 private:
  // TODO(fengliu): Kill the `validate_access` flag.
  bool m_validate_access{true};
  JitLoopCheck m_jit_loop_check{JitLoopCheck::SKIP};
  Architecture m_arch;
  bool m_disabled;
  IRTypeCheckerConfig m_config;
};

class CheckUniqueDeobfuscatedNames {
 public:
  bool m_after_each_pass{false};

  explicit CheckUniqueDeobfuscatedNames(ConfigFiles& conf) {
    const Json::Value& args =
        conf.get_json_config()["check_unique_deobfuscated_names"];
    m_after_each_pass = args.get("run_after_each_pass", false).asBool();
    m_initially = args.get("run_initially", false).asBool();
    m_finally = args.get("run_finally", false).asBool();
  }

  void run_initially(const Scope& scope) {
    if (m_initially) {
      check_unique_deobfuscated_names("<initial>", scope);
    }
  }

  void run_finally(const Scope& scope) {
    if (m_finally) {
      check_unique_deobfuscated_names("<final>", scope);
    }
  }

  void run_after_pass(const Pass* pass, const Scope& scope) {
    if (m_after_each_pass) {
      check_unique_deobfuscated_names(pass->name().c_str(), scope);
    }
  }

 private:
  void check_unique_deobfuscated_names(const char* pass_name,
                                       const Scope& scope) {
    TRACE(PM, 1, "Running check_unique_deobfuscated_names...");
    Timer t("check_unique_deobfuscated_names");
    UnorderedMap<const DexString*, DexMethod*> method_names;
    walk::methods(scope, [&method_names, pass_name](DexMethod* dex_method) {
      const auto* deob = dex_method->get_deobfuscated_name_or_null();
      auto it = method_names.find(deob);
      if (it != method_names.end()) {
        fprintf(
            stderr,
            "ABORT! [%s] Duplicate deobfuscated method name: %s\nfor %s\n vs "
            "%s\n",
            pass_name, it->first->c_str(), SHOW(dex_method), SHOW(it->second));
        exit(EXIT_FAILURE);
      }
      method_names.emplace(deob, dex_method);
    });
    UnorderedMap<std::string, DexField*> field_names;
    walk::fields(scope, [&field_names, pass_name](DexField* dex_field) {
      auto deob = dex_field->get_deobfuscated_name();
      auto it = field_names.find(deob);
      if (it != field_names.end()) {
        fprintf(stderr,
                "ABORT! [%s] Duplicate deobfuscated field name: %s\nfor %s\n "
                "vs %s\n",
                pass_name, it->first.c_str(), SHOW(dex_field),
                SHOW(it->second));
        exit(EXIT_FAILURE);
      }
      field_names.emplace(deob, dex_field);
    });
  }

  bool m_initially{false};
  bool m_finally{false};
};

class VisualizerHelper {
 public:
  explicit VisualizerHelper(const ConfigFiles& conf)
      : m_class_cfgs(conf.metafile(CFG_DUMP_BASE_NAME),
                     conf.get_json_config().get("write_cfg_each_pass", false)) {
    m_class_cfgs.add_all(
        conf.get_json_config().get("dump_cfg_classes", std::string("")));
  }

  void add_pass(const Pass* pass, size_t i) {
    m_class_cfgs.add_pass(
        [&]() { return pass->name() + "(" + std::to_string(i) + ")"; },
        VISUALIZER_PASS_OPTIONS);
  }

  void finalize() {
    m_class_cfgs.add_pass("After all passes");
    m_class_cfgs.write();
  }

 private:
  static constexpr visualizer::Options VISUALIZER_PASS_OPTIONS =
      (visualizer::Options)(visualizer::Options::SKIP_NO_CHANGE |
                            visualizer::Options::FORCE_CFG);
  static constexpr const char* CFG_DUMP_BASE_NAME = "redex-cfg-dumps.cfg";

  visualizer::Classes m_class_cfgs;
};

class AnalysisUsageHelper {
 public:
  using PreservedMap = UnorderedMap<AnalysisID, Pass*>;

  explicit AnalysisUsageHelper(PreservedMap& m)
      : m_preserved_analysis_passes(m) {}

  void pre_pass(Pass* pass) { pass->set_analysis_usage(m_analysis_usage); }

  void post_pass(Pass* pass) {
    // Invalidate existing preserved analyses according to policy set by each
    // pass.
    m_analysis_usage.do_pass_invalidation(&m_preserved_analysis_passes);

    if (pass->is_analysis_pass()) {
      // If the pass is an analysis pass, preserve it.
      m_preserved_analysis_passes.emplace(get_analysis_id_by_pass(pass), pass);
    }
  }

 private:
  AnalysisUsage m_analysis_usage;
  PreservedMap& m_preserved_analysis_passes;
};

class JNINativeContextHelper {
 public:
  explicit JNINativeContextHelper(const Scope& scope,
                                  const std::string& jni_output_dir) {
    if (!jni_output_dir.empty()) {
      // Currently, if the path is not found, the native context is going to be
      // empty.
      g_native_context = std::make_unique<native::NativeContext>(
          native::NativeContext::build(jni_output_dir, scope));

      // Before running any passes, treat everything as removable.
      walk::methods(scope, [this](DexMethod* m) {
        if (is_native(m)) {
          auto* native_func = native::get_native_function_for_dex_method(m);
          if (native_func != nullptr) {
            TRACE(NATIVE, 2, "Found native function %s",
                  native_func->get_name().c_str());
            m_removable_natives.emplace(native_func);
          } else {
            // There's a native method which we don't find. Let's be
            // conservative and ask Redex not to remove it.
            m->rstate.set_root();
            // Ignore "linking" failures for pre-existing "linking" failures.
            m_java_method_no_impl_on_input.emplace(m);
          }
        }
      });
    }
  }

  void post_passes(const Scope& scope, ConfigFiles& conf) {
    if (!g_native_context) {
      return;
    }
    // After running all passes, walk through the removable functions and
    // remove the ones should remain.
    walk::methods(scope, [this](DexMethod* m) {
      if (is_native(m)) {
        auto* native_func = native::get_native_function_for_dex_method(m);
        if (native_func != nullptr) {
          auto it = m_removable_natives.find(native_func);
          if (it != m_removable_natives.end()) {
            TRACE(NATIVE, 2, "Cannot remove native function %s, called as %s",
                  native_func->get_name().c_str(), SHOW(m));
            m_removable_natives.erase(it);
          }
        } else if (m_java_method_no_impl_on_input.count(m) == 0u) {
          // TODO: "Linking" error: Change this to an assertion failure
          TRACE(PM, 1, "Unable to find native implementation for %s.", SHOW(m));
        }
      }
    });

    TRACE(NATIVE, 2, "Total removable natives: %zu",
          m_removable_natives.size());

    auto removable_natives_file_name = conf.metafile(REMOVABLE_NATIVES);
    std::vector<std::string> output_symbols;
    output_symbols.reserve(m_removable_natives.size());

    // Might be non-deterministic in order, put them in a vector and sort.
    for (auto* func : UnorderedIterable(m_removable_natives)) {
      output_symbols.push_back(func->get_name());
    }

    std::sort(output_symbols.begin(), output_symbols.end());

    std::ofstream out(removable_natives_file_name);

    // TODO: For better human readability, change this to CSV of native,java?
    for (const auto& name : output_symbols) {
      out << name << '\n';
    }

    g_native_context.reset();
  }

 private:
  UnorderedSet<native::Function*> m_removable_natives;
  UnorderedSet<DexMethod*> m_java_method_no_impl_on_input;
};

void process_method_profiles(PassManager& mgr, ConfigFiles& conf) {
  // New methods might have been introduced by this pass; process previously
  // unresolved methods to see if we can match them now (so that future passes
  // using method profiles benefit)
  conf.process_unresolved_method_profile_lines();
  mgr.set_metric("~result~MethodProfiles~", conf.get_method_profiles().size());
  mgr.set_metric("~result~MethodProfiles~unresolved~",
                 conf.get_method_profiles().unresolved_size());
}

// Collect dex info metrics for the root store after InterDexPass has run.
void set_root_store_metrics(PassManager& mgr,
                            DexStoresVector& stores,
                            const PassManagerConfig* pm_config) {
  auto& root_store = stores.at(0);
  auto& root_dexen = root_store.get_dexen();
  mgr.set_metric("~rootstore.num_dexes", root_dexen.size());
  size_t idx = 0;
  size_t total_methods = 0;
  for (auto& dex : root_dexen) {
    mgr.set_metric("~rootstore.dex_" + std::to_string(++idx) + ".num_classes",
                   dex.size());
    for (auto& cls : dex) {
      total_methods += cls->get_all_methods().size();
    }
  }
  mgr.set_metric("~rootstore.total_class_num", total_methods);
  if (pm_config->dump_mrefs) {
    // dump number of mrefs in each dex in root_store.
    idx = 0;
    size_t total_mrefs = 0;
    for (auto& dex : root_dexen) {
      std::vector<DexMethodRef*> mrefs;
      UnorderedSet<DexMethodRef*> mrefs_set;
      for (DexClass* cls : dex) {
        cls->gather_methods(mrefs);
      }
      for (auto& elem : mrefs) {
        mrefs_set.insert(elem);
      }
      mgr.set_metric("~~rootstore.dex_" + std::to_string(++idx) + ".num_mrefs",
                     mrefs_set.size());
      total_mrefs += mrefs_set.size();
    }
    mgr.set_metric("~~rootstore.total_mrefs", total_mrefs);
    mgr.set_metric("~~rootstore.total_cross_dex_mrefs",
                   total_mrefs - total_methods);
  }
}

// Returns the highest dex version whose features must be validated as absent
// before running `pass`, or std::nullopt if no validation is needed.
std::optional<int> pass_dex_version_to_check(Pass* pass,
                                             int32_t input_dex_version) {
  if (pass->pass_support_dex_version() >= input_dex_version) {
    return std::nullopt;
  }
  always_assert(input_dex_version <= 39);
  for (int version : {39, 38, 37}) {
    if (pass->need_dex_version_support(input_dex_version, version)) {
      return version;
    }
  }
  return std::nullopt;
}

// Abort if the activated passes are ordered in a way that violates their
// declared property interactions.
void verify_pass_order(const PassManager& mgr, ConfigFiles& conf) {
  std::vector<std::pair<std::string, redex_properties::PropertyInteractions>>
      pass_interactions;
  const auto& pass_info = mgr.get_pass_info();
  pass_interactions.reserve(pass_info.size());
  for (const auto& info : pass_info) {
    pass_interactions.emplace_back(info.pass->name(),
                                   info.property_interactions);
  }
  auto failure = redex_properties::Manager::verify_pass_interactions(
      pass_interactions, conf);
  if (failure) {
    fprintf(stderr, "ABORT! Illegal pass order:\n%s", failure->c_str());
    exit(EXIT_FAILURE);
  }
}

void set_pass_timing_metrics(PassManager& mgr,
                             double cpu_time,
                             std::chrono::duration<double> wall_time) {
  mgr.set_metric("timing.cpu_time.100", (int64_t)(cpu_time * 100));
  mgr.set_metric("timing.wall_time.100", (int64_t)(wall_time.count() * 100));
  if (wall_time.count() != 0) {
    mgr.set_metric("timing.speedup.100",
                   (int64_t)(100.0 * cpu_time / wall_time.count()));
    mgr.set_metric(
        "timing.utilization.100",
        (int64_t)(100.0 * cpu_time / wall_time.count() /
                  static_cast<double>(redex_parallel::default_num_threads())));
  }
}

void maybe_write_hashes_incoming(const ConfigFiles& conf, const Scope& scope) {
  if (conf.emit_incoming_hashes()) {
    TRACE(PM, 1, "Writing incoming hashes...");
    Timer t("Writing incoming hashes");
    std::ofstream hashes_file(conf.metafile(INCOMING_HASHES));
    hashing::print_classes(hashes_file, scope);
  }
}

void maybe_write_hashes_outgoing(const ConfigFiles& conf, const Scope& scope) {
  if (conf.emit_outgoing_hashes()) {
    TRACE(PM, 1, "Writing outgoing hashes...");
    Timer t("Writing outgoing hashes");
    std::ofstream hashes_file(conf.metafile(OUTGOING_HASHES));
    hashing::print_classes(hashes_file, scope);
  }
}

void maybe_write_env_seeds_file(const ConfigFiles& conf, const Scope& scope) {
  char* seeds_output_file = std::getenv("REDEX_SEEDS_FILE");
  if (seeds_output_file != nullptr) {
    std::string seed_filename = seeds_output_file;
    Timer t("Writing seeds file " + seed_filename);
    std::ofstream seeds_file(seed_filename);
    keep_rules::print_seeds(seeds_file, conf.get_proguard_map(), scope, false,
                            false);
  }
}

void maybe_print_seeds_incoming(
    const ConfigFiles& conf,
    const Scope& scope,
    const std::unique_ptr<const keep_rules::ProguardConfiguration>& pg_config) {
  if (!conf.get_printseeds().empty()) {
    Timer t("Writing seeds to file " + conf.get_printseeds());
    std::ofstream seeds_file(conf.get_printseeds());
    keep_rules::print_seeds(seeds_file, conf.get_proguard_map(), scope);
    std::ofstream config_file(conf.get_printseeds() + ".pro");
    redex_assert(pg_config != nullptr);
    keep_rules::show_configuration(config_file, scope, *pg_config);
    std::ofstream incoming(conf.get_printseeds() + ".incoming");
    redex::print_classes(incoming, conf.get_proguard_map(), scope);
    std::ofstream shrinking_file(conf.get_printseeds() + ".allowshrinking");
    keep_rules::print_seeds(shrinking_file, conf.get_proguard_map(), scope,
                            true, false);
    std::ofstream obfuscation_file(conf.get_printseeds() + ".allowobfuscation");
    keep_rules::print_seeds(obfuscation_file, conf.get_proguard_map(), scope,
                            false, true);
  }
}

void maybe_print_seeds_outgoing(const ConfigFiles& conf,
                                const DexStoreClassesIterator& it) {
  if (!conf.get_printseeds().empty()) {
    Timer t("Writing outgoing classes to file " + conf.get_printseeds() +
            ".outgoing");
    // Recompute the scope.
    auto scope = build_class_scope(it);
    std::ofstream outgoing(conf.get_printseeds() + ".outgoing");
    redex::print_classes(outgoing, conf.get_proguard_map(), scope);
  }
}

void maybe_enable_opt_data(const ConfigFiles& conf) {
  // Enable opt decision logging if specified in config.
  const Json::Value& opt_decisions_args =
      conf.get_json_config()["opt_decisions"];
  if (opt_decisions_args.get("enable_logs", false).asBool()) {
    opt_metadata::OptDataMapper::get_instance().enable_logs();
  }
}

bool is_run_hasher_after_each_pass(const ConfigFiles& conf,
                                   const RedexOptions& options) {
  if (options.disable_dex_hasher) {
    return false;
  }

  const Json::Value& hasher_args = conf.get_json_config()["hasher"];
  return hasher_args.get("run_after_each_pass", false).asBool();
}

void ensure_cfg(DexStoresVector& stores) {
  auto temp_scope = build_class_scope(stores);
  walk::parallel::code(temp_scope, [&](DexMethod*, IRCode& code) {
    code.build_cfg(/*rebuild_even_if_already_built*/ false);
  });
}

// Ensure the CFG is clean, e.g., no unreachable blocks, after a cfg-friendly
// pass has run.
void simplify_cfgs_after_pass(DexStoresVector& stores, const Pass* pass) {
  auto temp_scope = build_class_scope(stores);
  walk::parallel::code(temp_scope, [&](DexMethod* method, IRCode& code) {
    always_assert_log(code.cfg_built(),
                      "%s has no cfg after cfg-friendly pass %s", SHOW(method),
                      pass->name().c_str());
    code.cfg().simplify();
  });
}

void run_assessor(PassManager& pm, const Scope& scope, bool initially = false) {
  TRACE(PM, 2, "Running assessor...");
  Timer t("Assessor");
  assessments::DexScopeAssessor assessor(scope);
  auto assessment = assessor.run();
  std::string prefix =
      std::string("~") + (initially ? "PRE" : "") + "assessment~";
  // log metric value in a way that fits into JSON number value
  for (auto& p : assessments::order(assessment)) {
    pm.set_metric(prefix + p.first, p.second);
  }
}

namespace {
// Return a set of the items denoted by the given input. Items will have
// leading/trailing spaces trimmed.
std::set<std::string_view> extract_delimited_items(const std::string& input,
                                                   const std::string& delim) {
  std::set<std::string_view> result_set;
  for (auto item : split_string(input, delim)) {
    auto trimmed = trim_whitespaces(item);
    if (!trimmed.empty()) {
      result_set.emplace(trimmed);
    }
  }
  return result_set;
}
} // namespace

// For debugging purpose allows tracing a class after each pass.
// Env variable TRACE_CLASS_FILE provides the name of the output file where
// these data will be written and env variable TRACE_CLASS_NAME would provide
// the name of the class to be traced.
class TraceClassAfterEachPass {
 public:
  TraceClassAfterEachPass() {

    auto* trace_class_file = getenv("TRACE_CLASS_FILE");
    std::cerr << "TRACE_CLASS_FILE="
              << (trace_class_file == nullptr ? "" : trace_class_file) << '\n';

    auto* trace_class_name = getenv("TRACE_CLASS_NAME");
    m_trace_class_env = trace_class_name == nullptr ? "" : trace_class_name;
    std::cerr << "TRACE_CLASS_NAME=" << m_trace_class_env << '\n';
    m_trace_class_names = extract_delimited_items(m_trace_class_env, ",");

    auto* trace_method_name = getenv("TRACE_METHOD_NAME");
    m_trace_method_env = trace_method_name == nullptr ? "" : trace_method_name;
    std::cerr << "TRACE_METHOD_NAME=" << m_trace_method_env << '\n';
    m_trace_method_names = extract_delimited_items(m_trace_method_env, ",");

    if (!m_trace_method_names.empty() || !m_trace_class_names.empty()) {
      if (trace_class_file != nullptr) {
        try {
          int int_fd = std::stoi(trace_class_file);
          m_fd = fdopen(int_fd, "w");
        } catch (std::invalid_argument&) {
          // Not an integer file descriptor; real file name.
          m_fd = fopen(trace_class_file, "w");
        }
        if (m_fd == nullptr) {
          fprintf(stderr,
                  "Unable to open TRACE_CLASS_FILE, falling back to stderr\n");
          m_fd = stderr;
        }
      }
    }
  }

  ~TraceClassAfterEachPass() {
    if (m_fd != stderr) {
      fclose(m_fd);
    }
  }

  void dump_method(DexMethod* m) {
    fprintf(m_fd, "Method %s\n", SHOW(m));
    auto* code = m->get_code();
    if (code != nullptr) {
      if (code->cfg_built()) {
        auto& cfg = code->cfg();
        // Note: would be nice to make the special printers from ShowCFG
        // configurable/callable from here.
        auto cfg_string = show(cfg);
        fprintf(m_fd, "%s\n", cfg_string.c_str());
      } else {
        // NOTE: consider building CFG, showing, and clearing to make the output
        // nicer to look at.
        fprintf(m_fd, "%s\n", SHOW(code));
      }
    }
  }

  void dump_cls(DexClass* cls) {
    fprintf(m_fd, "Class %s\n", SHOW(cls));
    auto* anno_set = cls->get_anno_set();
    if (anno_set != nullptr) {
      fprintf(m_fd, "  Annotations on class: %s\n", SHOW(anno_set));
    }
    std::vector<DexMethod*> methods = cls->get_all_methods();
    std::vector<DexField*> fields = cls->get_all_fields();
    for (auto* v : fields) {
      fprintf(m_fd, "Field %s\n", SHOW(v));
      if (v->is_concrete() && v->get_static_value() != nullptr) {
        auto* static_val = v->get_static_value();
        // Make the printing less verbose; print when the value is nonzero.
        auto zero = DexEncodedValue::zero_for_type(v->get_type());
        if (static_val->value() != zero->value()) {
          fprintf(m_fd, "  Value: %s\n", SHOW(v->get_static_value()));
        }
      }
    }
    for (auto* m : methods) {
      dump_method(m);
    }
  }

  std::optional<std::string_view> matches_source_block(DexMethod* method) {
    auto* code = method->get_code();
    if (code == nullptr) {
      return std::nullopt;
    }
    if (code->cfg_built()) {
      auto& cfg = code->cfg();
      for (auto* b : cfg.blocks()) {
        auto sbs = source_blocks::gather_source_blocks(b);
        for (auto* sb : sbs) {
          auto search = m_trace_method_names.find(sb->src->str());
          if (search != m_trace_method_names.end()) {
            return *search;
          }
        }
      }
    } else {
      for (auto it = code->begin(); it != code->end(); it++) {
        if (it->type == MFLOW_SOURCE_BLOCK) {
          auto search = m_trace_method_names.find(it->src_block->src->str());
          if (search != m_trace_method_names.end()) {
            return *search;
          }
        }
      }
    }
    return std::nullopt;
  }

  void dump(const std::string& pass_name, DexStoresVector& stores) {
    if (m_trace_class_names.empty() && m_trace_method_names.empty()) {
      return;
    }
    fprintf(m_fd, "After Pass %s\n", pass_name.c_str());
    auto temp_scope = build_class_scope(stores);
    if (!m_trace_class_names.empty()) {
      UnorderedMap<std::string_view, DexClass*> to_print;
      for (auto* cls : temp_scope) {
        auto name = cls->get_deobfuscated_name_or_empty();
        if (name.empty()) {
          name = cls->get_name()->str();
        }
        if (m_trace_class_names.count(name) > 0) {
          to_print.emplace(name, cls);
        }
      }
      for (const auto& s : m_trace_class_names) {
        auto search = to_print.find(s);
        if (search != to_print.end()) {
          dump_cls(search->second);
        } else {
          fprintf(m_fd, "Class %.*s not found!\n", static_cast<int>(s.length()),
                  s.data());
        }
      }
    }
    // Attempt to dump specific method contents, falling back on exhaustive
    // search on source blocks to give a coherent representation of where the
    // code went and how it changes after each pass.
    using SetOfMethods = std::set<DexMethod*, dexmethods_comparator>;
    if (!m_trace_method_names.empty()) {
      UnorderedMap<std::string_view, SetOfMethods> to_print;
      for (const auto& s : m_trace_method_names) {
        auto* ref = DexMethod::get_method(s);
        if (ref != nullptr) {
          auto* def = ref->as_def();
          if (def != nullptr) {
            SetOfMethods methods{def};
            to_print.emplace(s, std::move(methods));
          }
        }
      }
      if (to_print.size() != m_trace_method_names.size()) {
        // Fall back and do some hunting to find if the method got inlined; if
        // so, print what would have been its caller (note there could be many).
        std::mutex print_mtx;
        walk::parallel::methods(temp_scope, [&](DexMethod* m) {
          auto str = matches_source_block(m);
          if (str != std::nullopt) {
            std::lock_guard lock(print_mtx);
            auto search = to_print.find(*str);
            if (search == to_print.end()) {
              SetOfMethods methods{m};
              to_print.emplace(*str, std::move(methods));
            } else {
              search->second.emplace(m);
            }
          }
        });
      }
      for (const auto& s : m_trace_method_names) {
        auto search = to_print.find(s);
        if (search != to_print.end()) {
          for (const auto& method : search->second) {
            dump_method(method);
          }
        } else {
          fprintf(m_fd, "Method %.*s not found!\n",
                  static_cast<int>(s.length()), s.data());
        }
      }
    }
  }

 private:
  FILE* m_fd = stderr;
  std::string m_trace_class_env;
  std::string m_trace_method_env;
  std::set<std::string_view> m_trace_class_names;
  std::set<std::string_view> m_trace_method_names;
};

static TraceClassAfterEachPass trace_cls;

struct JemallocStats {
  PassManager* pm;
  const ConfigFiles& c;
  bool full_stats{false};

  JemallocStats(PassManager* pm, const ConfigFiles& c) : pm(pm), c(c) {
    const auto* pmc =
        c.get_global_config().get_config_by_name<PassManagerConfig>(
            "pass_manager");
    redex_assert(pmc != nullptr);

    full_stats = pmc->jemalloc_full_stats;
  }

  void process_jemalloc_stats_for_pass([[maybe_unused]] const Pass* pass,
                                       [[maybe_unused]] size_t run) {
#ifdef USE_JEMALLOC
    std::string key_base = "~jemalloc.";
    auto cb = [&](const char* key, uint64_t value) {
      pm->set_metric(key_base + key, value);
    };
    jemalloc_util::some_malloc_stats(cb);

    if (full_stats) {
      std::string name =
          "jemalloc." + pass->name() + "." + std::to_string(run) + ".json";
      auto filename = c.metafile(name);
      std::ofstream ofs{filename};
      ofs << jemalloc_util::get_malloc_stats();
    }
#endif
  }
};

// Runs the configured verifiers around each pass. The stable collaborators are
// bound once at construction; pre_pass/post_pass take only the per-pass inputs.
//
// Templated on the context type only to break a definition-order cycle:
// RunPassesContext holds a PassVerifiers member, so it is defined below and
// cannot be named here. Ctx is always RunPassesContext.
template <typename Ctx>
struct PassVerifiers {
  Ctx& ctx;
  PassManager& mgr;
  DexStoresVector& stores;
  std::vector<PassManager::PassInfo>& pass_info;
  CheckerConfig& checker_conf;
  const AssessorConfig* assessor_config;
  CheckUniqueDeobfuscatedNames& check_unique_deobfuscated;
  const PassManagerConfig* pm_config;
  redex_properties::Manager* properties_manager;
  bool run_hasher_after_each_pass;

  // Runs verifiers before a pass; currently only the initial assessor run.
  void pre_pass(size_t i, const Scope& scope) {
    if (i == 0 && assessor_config->run_initially) {
      run_assessor(mgr, scope, /* initially */ true);
    }
  }

  // Runs verifiers after a pass: CFG/reference invariants, then (as configured)
  // the hasher, assessor, type checker, and unique-deobfuscated-name check on a
  // freshly built scope, and finally the deep property check.
  void post_pass(Pass* pass, size_t i) {
    auto* current_pass_info = &pass_info[i];
    ConcurrentSet<const DexMethodRef*> all_code_referenced_methods;
    ConcurrentSet<DexMethod*> unique_methods;
    // Build the class scope once and reuse it for the verifier and remark
    // walks.
    auto verifier_scope = build_class_scope(stores);
    walk::parallel::code(verifier_scope, [&](DexMethod* m, IRCode& code) {
      always_assert_log(code.cfg_built(), "%s has a cfg!", SHOW(m));
      code.cfg().reset_exit_block();
      if (slow_invariants_debug) {
        std::vector<DexMethodRef*> methods;
        methods.reserve(1000);
        methods.push_back(m);
        code.gather_methods(methods);
        for (auto* mref : methods) {
          always_assert_log(
              DexMethod::get_method(mref->get_class(), mref->get_name(),
                                    mref->get_proto()) != nullptr,
              "Did not find %s in the context, referenced from %s!", SHOW(mref),
              SHOW(m));
          all_code_referenced_methods.insert(mref);
        }
        if (!unique_methods.insert(m)) {
          not_reached_log("Duplicate method: %s", SHOW(m));
        }
      }
    });
    if (slow_invariants_debug) {
      ScopedMetrics sm(mgr);
      sm.set_metric("num_code_referenced_methods",
                    all_code_referenced_methods.size());
    }

    if (g_redex->insert_remarks) {
      std::atomic<size_t> remark_count{0};
      walk::parallel::code(verifier_scope, [&](DexMethod*, IRCode& code) {
        always_assert(code.cfg_built());
        size_t local = 0;
        for (auto* block : code.cfg().blocks()) {
          for (const auto& mie : *block) {
            if (mie.type == MFLOW_REMARK) {
              ++local;
            }
          }
        }
        if (local != 0) {
          remark_count.fetch_add(local, std::memory_order_relaxed);
        }
      });
      ScopedMetrics sm(mgr);
      sm.set_metric("remarks_count", remark_count.load());
    }

    bool run_hasher = run_hasher_after_each_pass;
    bool run_assessor =
        assessor_config->run_after_each_pass ||
        (assessor_config->run_finally && i == pass_info.size() - 1);
    bool run_type_checker = checker_conf.run_after_pass(pass);

    if (run_hasher || run_assessor || run_type_checker ||
        check_unique_deobfuscated.m_after_each_pass) {
      auto scope = build_class_scope(stores);

      if (run_hasher) {
        current_pass_info->hash = std::optional<hashing::DexHash>(
            ctx.run_hasher(pass->name().c_str(), scope));
      }
      if (run_assessor) {
        ::run_assessor(mgr, scope);
        ScopedMetrics sm(mgr);
        source_blocks::track_source_block_coverage(sm, stores);
      }
      if (run_type_checker) {
        // It's OK to overwrite the `this` register if we are not yet at the
        // output phase -- the register allocator can fix it up later.
        checker_conf.check_no_overwrite_this(false)
            .validate_access(false)
            .run_verifier(scope);
      }
      auto timer = m_check_unique_deobfuscateds_timer.scope();
      check_unique_deobfuscated.run_after_pass(pass, scope);
    }
    if (pm_config->check_properties_deep && properties_manager != nullptr) {
      TRACE(PM, 2, "Checking established properties of %s...",
            current_pass_info->pass->name().c_str());
      properties_manager->apply_and_check(
          current_pass_info->property_interactions, stores, mgr);
    }
  }
};

// Owns the invariant per-run profiling configuration. scope() builds the RAII
// bundle of scoped profilers that stay active for one pass's execution,
// mirroring the ViolationsTracking/Handler pattern.
struct PassProfiling {
  const std::optional<ScopedCommandProfiling::ProfilerInfo>& profiler_info;
  const std::optional<ScopedCommandProfiling::ProfilerInfo>& profiler_all_info;
  const Pass* profiler_info_pass;
  const Pass* malloc_profile_pass;
  source_blocks::ViolationsTracking& violations_tracking;

  // RAII bundle: constructs the scoped profilers for one pass and tears them
  // down (in reverse declaration order) when the pass finishes.
  struct Scope {
    std::optional<ScopedCommandProfiling> command_prof;
    std::optional<ScopedCommandProfiling> command_all_prof;
    jemalloc_util::ScopedProfiling malloc_prof;
    // Declared before `violations`, and therefore destroyed after it, because
    // the handler reports into this sink from its own destructor.
    ScopedMetrics metrics;
    std::optional<source_blocks::ViolationsTracking::Handler> violations;

    // Builds every scoped profiler in place, in declaration order, so their
    // constructor side effects run in the intended sequence: command
    // profiling, then jemalloc scoped profiling, then the metrics sink (which
    // allocates nothing), then violations tracking (whose constructor
    // allocates and must run while malloc profiling is active). Taking the
    // ingredients rather than pre-built members avoids relying on the
    // unspecified evaluation order of constructor arguments.
    Scope(PassProfiling& pp,
          PassManager* mgr,
          Pass* pass,
          DexStoresVector& stores)
        : command_prof(pp.profiler_info_pass == pass
                           ? ScopedCommandProfiling::maybe_from_info(
                                 pp.profiler_info, &pass->name())
                           : std::nullopt),
          command_all_prof(ScopedCommandProfiling::maybe_from_info(
              pp.profiler_all_info, &pass->name())),
          malloc_prof(pp.malloc_profile_pass == pass),
          metrics(*mgr),
          violations(pp.violations_tracking.maybe_track(&metrics, stores)) {}

    Scope(const Scope&) = delete;
    Scope& operator=(const Scope&) = delete;
    Scope(Scope&&) = delete;
    Scope& operator=(Scope&&) = delete;
  };

  Scope scope(PassManager* mgr, Pass* pass, DexStoresVector& stores) {
    return Scope(*this, mgr, pass, stores);
  }
};

} // namespace

std::unique_ptr<keep_rules::ProguardConfiguration> empty_pg_config() {
  return std::make_unique<keep_rules::ProguardConfiguration>();
}

PassManager::PassManager(const std::vector<Pass*>& passes)
    : PassManager(
          passes, ConfigFiles(Json::Value(Json::objectValue)), RedexOptions{}) {
}
PassManager::PassManager(const std::vector<Pass*>& passes,
                         const ConfigFiles& config,
                         const RedexOptions& options)
    : PassManager(passes, empty_pg_config(), config, options) {}

PassManager::PassManager(
    const std::vector<Pass*>& passes,
    std::unique_ptr<keep_rules::ProguardConfiguration> pg_config)
    : PassManager(passes,
                  std::move(pg_config),
                  ConfigFiles(Json::Value(Json::objectValue)),
                  RedexOptions{}) {}
PassManager::PassManager(
    std::vector<Pass*> passes,
    std::unique_ptr<keep_rules::ProguardConfiguration> pg_config,
    const ConfigFiles& config,
    RedexOptions options,
    redex_properties::Manager* properties_manager)
    : m_asset_mgr(get_apk_dir(config)),
      m_registered_passes(std::move(passes)),
      m_current_pass_info(nullptr),
      m_pg_config(std::move(pg_config)),
      m_redex_options(std::move(options)),
      m_internal_fields(new InternalFields()),
      m_properties_manager(properties_manager) {
  init(config);
}

PassManager::~PassManager() {}

void PassManager::init(const ConfigFiles& config) {
  auto activated =
      compute_activated_passes(m_registered_passes, config, nullptr);

  m_activated_passes.reserve(activated.activated_passes.size());
  const auto& json_config = config.get_json_config();
  std::transform(
      activated.activated_passes.begin(), activated.activated_passes.end(),
      std::back_inserter(m_activated_passes), [&json_config](auto& x) {
        x.first->parse_config(JsonWrapper(json_config[x.second.c_str()]));
        return x.first;
      });
  m_cloned_passes = std::move(activated.cloned_passes);

  // Count the number of appearances of each pass name.
  UnorderedMap<const Pass*, size_t> pass_repeats;
  for (const Pass* pass : m_activated_passes) {
    ++pass_repeats[pass];
  }

  // Init m_pass_info
  UnorderedMap<const Pass*, size_t> pass_counters;
  m_pass_info.resize(m_activated_passes.size());
  for (size_t i = 0; i < m_activated_passes.size(); ++i) {
    Pass* pass = m_activated_passes[i];
    const size_t count = pass_counters[pass]++;
    m_pass_info[i].pass = pass;
    m_pass_info[i].order = i;
    m_pass_info[i].repeat = count;
    m_pass_info[i].total_repeat = pass_repeats.at(pass);
    m_pass_info[i].name = pass->name() + "#" + std::to_string(count + 1);
    m_pass_info[i].metrics[std::string(PASS_ORDER_KEY)] =
        static_cast<int64_t>(i);
    m_pass_info[i].config =
        JsonWrapper(config.get_json_config()[pass->name().c_str()]);
  }
}

// Everything whose lifetime spans a single run_passes() call: the constructor
// performs all pre-loop setup, run_pass() one iteration of the main loop, and
// the destructor all post-loop teardown.
//
// Member declaration order is load-bearing, and matches the order the objects
// were created in when this was one long function. Several members hold
// non-owning references to earlier ones -- PassVerifiers to checker_conf and
// check_unique_deobfuscated, PassProfiling to profiler_info, profiler_all_info
// and violations_tracking -- so reverse-order destruction is what keeps the
// referents alive until after the referrers are gone.
class PassManager::RunPassesContext {
 public:
  RunPassesContext(PassManager& mgr, DexStoresVector& stores, ConfigFiles& conf)
      : mgr(mgr),
        stores(stores),
        conf(conf),
        uncaught_on_entry(std::uncaught_exceptions()),
        pm_config(get_pass_manager_config(conf)),
        profiler_info(ScopedCommandProfiling::maybe_info_from_env("")),
        profiler_info_pass(profiler_info ? get_profiled_pass(mgr) : nullptr),
        profiler_all_info(
            ScopedCommandProfiling::maybe_info_from_env("ALL_PASSES_")),
        malloc_profile_pass(get_malloc_profile_pass(mgr)),
        it(squash_and_iterate(stores, conf)),
        scope(build_class_scope(it)),
        // Retrieve the hasher's settings.
        run_hasher_after_each_pass(
            is_run_hasher_after_each_pass(conf, mgr.get_redex_options())),
        // Retrieve the assessor's settings.
        assessor_config(
            conf.get_global_config().get_config_by_name<AssessorConfig>(
                "assessor")),
        // Retrieve the type checker's settings.
        checker_conf(
            conf, mgr.get_redex_options().arch, mgr.m_checker_disabled),
        check_unique_deobfuscated(conf),
        violations_tracking(*get_violations_tracking_config(conf)),
        mem_pass_stats(traceEnabled(STATS, 1) ||
                       conf.get_json_config().get("mem_stats", true)),
        hwm_per_pass(conf.get_json_config().get("mem_stats_per_pass", true)),
        jemalloc_stats(&mgr, conf),
        verifiers{*this,
                  mgr,
                  stores,
                  mgr.m_pass_info,
                  checker_conf,
                  assessor_config,
                  check_unique_deobfuscated,
                  pm_config,
                  mgr.m_properties_manager,
                  run_hasher_after_each_pass},
        pass_profiling{profiler_info, profiler_all_info, profiler_info_pass,
                       malloc_profile_pass, violations_tracking} {
    // Clear stale data. Make sure we start fresh.
    mgr.m_preserved_analysis_passes.clear();

    Timer::scope("API Level Checker", [&] {
      api::LevelChecker::init(mgr.m_redex_options.min_sdk, scope);
    });

    maybe_write_env_seeds_file(conf, scope);
    maybe_print_seeds_incoming(conf, scope, mgr.m_pg_config);
    maybe_write_hashes_incoming(conf, scope);

    maybe_enable_opt_data(conf);

    // Load configurations regarding the scope.
    conf.load(scope, mgr.m_redex_options.arch);

    sanitizers::lsan_do_recoverable_leak_check();

    eval_passes();

    init_property_interactions();

    checker_conf.on_input(scope);

    // Pull on method-profiles, so that they get initialized, and are matched
    // against the *initial* methods
    conf.get_method_profiles();

    if (run_hasher_after_each_pass) {
      // The null pass name keeps run_hasher from emitting metrics, which would
      // assert: there is no current pass during setup.
      mgr.m_initial_hash = run_hasher(nullptr, scope);
    }

    check_unique_deobfuscated.run_initially(scope);

    graph_visualizer.emplace(conf);

    sanitizers::lsan_do_recoverable_leak_check();

    // Abort if the analysis pass dependencies are not satisfied.
    AnalysisUsage::check_dependencies(mgr.m_activated_passes);

    if (pm_config->check_pass_order_properties) {
      verify_pass_order(mgr, conf);
    }

    if (pm_config->check_properties_deep &&
        mgr.m_properties_manager != nullptr) {
      TRACE(PM, 2, "Checking initial properties of...");
      mgr.m_properties_manager->check(stores, mgr);
    }

    jni_native_context_helper.emplace(scope,
                                      mgr.m_redex_options.jni_summary_path);
  }

  // Teardown. Declared `noexcept(false)` because the final type check reports
  // failures by throwing, and that has to keep reaching run_passes' caller.
  ~RunPassesContext() noexcept(false) {
    // Skip teardown while unwinding. Every step below can throw or exit(), and
    // running them over a half-optimized program would replace whatever went
    // wrong with a std::terminate. Before this was a struct, an exception out
    // of the loop simply never reached the post-loop code.
    if (std::uncaught_exceptions() != uncaught_on_entry) {
      return;
    }

    // Always clear cfg and run the type checker before generating the
    // optimized dex code.
    scope = build_class_scope(it);
    walk::parallel::code(scope,
                         [&](DexMethod*, IRCode& code) { code.clear_cfg(); });
    TRACE(PM, 1, "All opt passes are done, clear cfg\n");
    checker_conf
        .check_no_overwrite_this(mgr.get_redex_options().no_overwrite_this())
        .validate_access(true)
        .check_armv7_jit_loops(CheckerConfig::JitLoopCheck::ENFORCE)
        .run_verifier(scope);

    jni_native_context_helper->post_passes(scope, conf);

    check_unique_deobfuscated.run_finally(scope);
    check_unreleased_reserved_refs();

    graph_visualizer->finalize();

    maybe_print_seeds_outgoing(conf, it);
    maybe_write_hashes_outgoing(conf, scope);

    sanitizers::lsan_do_recoverable_leak_check();

    for (auto& [name, seconds] : AccumulatingTimer::get_times()) {
      Timer::add_timer(std::move(name), seconds);
    }
  }

  RunPassesContext(const RunPassesContext&) = delete;
  RunPassesContext& operator=(const RunPassesContext&) = delete;

  // Runs the i-th activated pass, along with the profiling, metrics and
  // verification that surround it.
  void run_pass(size_t i, bool& after_interdex) {
    Pass* pass = mgr.m_activated_passes[i];
    const size_t pass_run = ++runs[pass];
    AnalysisUsageHelper analysis_usage_helper{mgr.m_preserved_analysis_passes};
    analysis_usage_helper.pre_pass(pass);

    if (!after_interdex && pass->name() == "InterDexPass") {
      after_interdex = true;
    }

    TRACE(PM, 1, "Running %s...", pass->name().c_str());
    ScopedMemStats scoped_mem_stats{mem_pass_stats, hwm_per_pass};
    Timer t(pass->name() + " " + std::to_string(pass_run) + " (run)");
    mgr.m_current_pass_info = &mgr.m_pass_info[i];

    verifiers.pre_pass(i, scope);

    double cpu_time;
    std::chrono::duration<double> wall_time;

    {
      auto profiling_scope = pass_profiling.scope(&mgr, pass, stores);
      double cpu_time_start = ((double)std::clock()) / CLOCKS_PER_SEC;
      auto wall_time_start = std::chrono::steady_clock::now();
      // Run build_cfg() in case any newly added methods by previous passes
      // are not built as cfg. But if cfg is already built,
      // no need to rebuild it.
      ensure_cfg(stores);
      TRACE(PM, 2, "%s Pass uses cfg.\n", SHOW(pass->name()));

      auto version = pass_dex_version_to_check(
          pass, mgr.m_redex_options.input_dex_version);
      if (version.has_value()) {
        check_no_new_dex_features(pass, version.value());
      }

      pass->run_pass(stores, conf, mgr);
      auto wall_time_end = std::chrono::steady_clock::now();
      double cpu_time_end = ((double)std::clock()) / CLOCKS_PER_SEC;

      // Collect dex info metrics after InterDexPass.
      if (after_interdex) {
        set_root_store_metrics(mgr, stores, pm_config);
      }
      simplify_cfgs_after_pass(stores, pass);

      g_redex->compact();

      trace_cls.dump(pass->name(), stores);

      cpu_time = cpu_time_end - cpu_time_start;
      wall_time = wall_time_end - wall_time_start;
    }

    scoped_mem_stats.trace_log(&mgr, pass);

    jemalloc_stats.process_jemalloc_stats_for_pass(pass, pass_run);

    mgr.set_metric("~redex_context.leaked_methods", g_redex->leaked_methods());

    sanitizers::lsan_do_recoverable_leak_check();

    graph_visualizer->add_pass(pass, i);

    verifiers.post_pass(pass, i);

    analysis_usage_helper.post_pass(pass);

    process_method_profiles(mgr, conf);

    set_pass_timing_metrics(mgr, cpu_time, wall_time);

    mgr.m_current_pass_info = nullptr;
  }

 private:
  // Gives every activated pass a chance to prepare before the main loop, in
  // pass order. Each pass gets a current pass info for the duration of its own
  // eval_pass so that it can record metrics, and none afterwards.
  void eval_passes() {
    if (mgr.m_redex_options.input_dex_version >= 37) {
      always_assert_log(
          std::find_if(mgr.m_activated_passes.begin(),
                       mgr.m_activated_passes.end(),
                       [](const Pass* pass) {
                         return pass->name() == CLASS_REORDERING_PASS_NAME;
                       }) != mgr.m_activated_passes.end(),
          "Dex version 37+ has stricter class order requirement. Enable "
          "ClassReorderingPass to fulfill the requirement.");
    }
    for (size_t i = 0; i < mgr.m_activated_passes.size(); ++i) {
      Pass* pass = mgr.m_activated_passes[i];
      TRACE(PM, 1, "Evaluating %s...", pass->name().c_str());
      Timer t(pass->name() + " (eval)");
      mgr.m_current_pass_info = &mgr.m_pass_info[i];
      pass->eval_pass(stores, conf, mgr);
      mgr.m_current_pass_info = nullptr;
    }
  }

  // Aborts if the input uses dex features that `pass` cannot handle. The
  // feature scan walks every method, so its result is memoized in the
  // has_dex3*_features members for the rest of the run.
  void check_no_new_dex_features(const Pass* pass, int check_against_version) {
    always_assert_log(check_against_version <= 39 &&
                          check_against_version >= 35,
                      "Checking on unknown version %d", check_against_version);
    if ((check_against_version >= 37 && has_dex37_features == std::nullopt) ||
        (check_against_version >= 38 && has_dex38_features == std::nullopt) ||
        (check_against_version >= 39 && has_dex39_features == std::nullopt)) {
      // We run the feature check once in the full pass run and store the value
      std::atomic<bool> found_dex37_features{false};
      std::atomic<bool> found_dex38_features{false};
      std::atomic<bool> found_dex39_features{false};
      walk::parallel::classes(build_class_scope(stores), [&](DexClass* cls) {
        if (is_interface(cls)) {
          for (auto* m : cls->get_vmethods()) {
            if (m->get_code() != nullptr) {
              found_dex37_features = true;
            }
          }
        }
        for (auto* m : cls->get_all_methods()) {
          if (m->get_code() == nullptr) {
            continue;
          }
          for (auto& mie : InstructionIterable(m->get_code()->cfg())) {
            auto* insn = mie.insn;
            const auto& op = insn->opcode();
            if (op == OPCODE_INVOKE_CUSTOM || op == OPCODE_INVOKE_POLYMORPHIC) {
              found_dex38_features = true;
            }
            if (op == OPCODE_CONST_METHOD_HANDLE ||
                op == OPCODE_CONST_METHOD_TYPE) {
              found_dex39_features = true;
            }
            if (op == OPCODE_INVOKE_SUPER || op == OPCODE_INVOKE_DIRECT) {
              // invoke-super and invoke-direct on interface methods need
              // additional support.
              if (insn->get_method() == nullptr) {
                continue;
              }
              auto* insn_method_cls =
                  type_class(insn->get_method()->get_class());
              if (insn_method_cls != nullptr && is_interface(insn_method_cls)) {
                found_dex37_features = true;
              }
            }
          }
        }
      });
      has_dex37_features = found_dex37_features;
      has_dex38_features = found_dex38_features;
      has_dex39_features = found_dex39_features;
    }

    switch (check_against_version) {
    case 39:
      always_assert_log(
          !has_dex39_features.value(),
          "Input APK has dex39 features that this pass %s doesn't support",
          pass->name().c_str());
      [[fallthrough]];
    case 38:
      always_assert_log(
          !has_dex38_features.value(),
          "Input APK has dex38 features that this pass %s doesn't support",
          pass->name().c_str());
      [[fallthrough]];
    case 37:
      always_assert_log(
          !has_dex37_features.value(),
          "Input APK has dex37 features that this pass %s doesn't support",
          pass->name().c_str());
      [[fallthrough]];
    case 35:
      return;
    default:
      not_reached();
    }
  }

  // Every reservation a pass makes has to be released before the run ends.
  void check_unreleased_reserved_refs() {
    if (!mgr.m_reserved_ref_infos.empty()) {
      const auto& [name, info] = mgr.m_reserved_ref_infos.front();
      fprintf(stderr, "ABORT! Unreleased reserved refs: %s(%zu, %zu, %zu)\n",
              name.c_str(), info.frefs, info.trefs, info.mrefs);
      exit(EXIT_FAILURE);
    }
  }

  // PassVerifiers::post_pass hashes the scope it builds.
  friend struct PassVerifiers<RunPassesContext>;

  // Hashes the scope and traces the result. A null pass_name means the initial
  // hash, taken during setup, and suppresses the metrics: there is no current
  // pass yet, and emitting one without it asserts.
  hashing::DexHash run_hasher(const char* pass_name,
                              const Scope& scope_to_hash) {
    TRACE(PM, 2, "Running hasher...");
    Timer t("Hasher");
    auto timer = m_hashers_timer.scope();
    hashing::DexScopeHasher hasher(scope_to_hash);
    auto hash = hasher.run();
    if (pass_name != nullptr) {
      // log metric value in a way that fits into JSON number value
      mgr.set_metric("~result~code~hash~",
                     hash.code_hash & ((((size_t)1) << 52) - 1));
      mgr.set_metric("~result~registers~hash~",
                     hash.registers_hash & ((((size_t)1) << 52) - 1));
      mgr.set_metric("~result~positions~hash~",
                     hash.positions_hash & ((((size_t)1) << 52) - 1));
      mgr.set_metric("~result~signature~hash~",
                     hash.signature_hash & ((((size_t)1) << 52) - 1));
    }
    auto positions_hash_string = hashing::hash_to_string(hash.positions_hash);
    auto registers_hash_string = hashing::hash_to_string(hash.registers_hash);
    auto code_hash_string = hashing::hash_to_string(hash.code_hash);
    auto signature_hash_string = hashing::hash_to_string(hash.signature_hash);
    TRACE(PM, 3,
          "[scope hash] %s: positions#%s, registers#%s, code#%s, signature#%s",
          pass_name ? pass_name : "(initial)", positions_hash_string.c_str(),
          registers_hash_string.c_str(), code_hash_string.c_str(),
          signature_hash_string.c_str());
    return hash;
  }

  // Records each pass's declared property interactions, dropping the ones for
  // properties that are not enabled.
  void init_property_interactions() {
    for (size_t i = 0; i < mgr.m_activated_passes.size(); ++i) {
      Pass* pass = mgr.m_activated_passes[i];
      auto* pass_info = &mgr.m_pass_info[i];
      auto m = pass->get_property_interactions();
      unordered_erase_if(m, [&](auto& p) {
        auto&& [name, property_interaction] = p;

        if (mgr.m_properties_manager != nullptr &&
            !mgr.m_properties_manager->property_is_enabled(name)) {
          return true;
        }

        always_assert_log(property_interaction.is_valid(),
                          "%s has an invalid property interaction for %s",
                          pass->name().c_str(),
                          redex_properties::get_name(name));
        return false;
      });
      pass_info->property_interactions = std::move(m);
    }
  }

  static const PassManagerConfig* get_pass_manager_config(
      const ConfigFiles& conf) {
    const auto* pm_config =
        conf.get_global_config().get_config_by_name<PassManagerConfig>(
            "pass_manager");
    redex_assert(pm_config != nullptr);
    return pm_config;
  }

  static const ViolationsTrackingConfig* get_violations_tracking_config(
      const ConfigFiles& conf) {
    const auto* config =
        conf.get_global_config().get_config_by_name<ViolationsTrackingConfig>(
            "violations_tracking");
    redex_assert(config != nullptr);
    return config;
  }

  // Squashes the dexes before handing out the iterator, so that it and the
  // scope built from it see the final dex layout.
  static DexStoreClassesIterator squash_and_iterate(DexStoresVector& stores,
                                                    ConfigFiles& conf) {
    if (conf.force_single_dex()) {
      // Squash the dexes into one, so that the passes all see only one dex and
      // all the cross-dex reference checking are accurate.
      squash_into_one_dex(stores);
    }
    return DexStoreClassesIterator(stores);
  }

  PassManager& mgr;
  DexStoresVector& stores;
  ConfigFiles& conf;

  // Compared against std::uncaught_exceptions() in the destructor to tell a
  // normal scope exit from unwinding.
  const int uncaught_on_entry;
  const PassManagerConfig* pm_config;
  std::optional<ScopedCommandProfiling::ProfilerInfo> profiler_info;
  const Pass* profiler_info_pass;
  std::optional<ScopedCommandProfiling::ProfilerInfo> profiler_all_info;
  const Pass* malloc_profile_pass;
  DexStoreClassesIterator it;
  // Rebuilt during teardown, and therefore not const. Inside the loop this is
  // the *initial* scope; per-pass work rebuilds its own from `stores`.
  Scope scope;
  bool run_hasher_after_each_pass;
  const AssessorConfig* assessor_config;
  CheckerConfig checker_conf;
  CheckUniqueDeobfuscatedNames check_unique_deobfuscated;
  // graph_visualizer and jni_native_context_helper are optional so that the
  // constructor body can emplace them at the right point in the setup
  // sequence: both constructors inspect the program -- resolving class names,
  // walking every method -- and so have to run after eval_passes(), which an
  // initializer list cannot express.
  std::optional<VisualizerHelper> graph_visualizer;
  source_blocks::ViolationsTracking violations_tracking;
  const bool mem_pass_stats;
  const bool hwm_per_pass;
  std::optional<JNINativeContextHelper> jni_native_context_helper;
  JemallocStats jemalloc_stats;
  UnorderedMap<const Pass*, size_t> runs;
  PassVerifiers<RunPassesContext> verifiers;
  PassProfiling pass_profiling;

  // Memoized by check_no_new_dex_features, which is the only user. Scoped to
  // the run: a second run_passes call re-scans rather than reusing a result
  // that the first run's passes may have invalidated.
  std::optional<bool> has_dex37_features;
  std::optional<bool> has_dex38_features;
  std::optional<bool> has_dex39_features;
};

void PassManager::run_passes(DexStoresVector& stores, ConfigFiles& conf) {
  // Setup runs here; teardown runs when `ctx` goes out of scope.
  RunPassesContext ctx{*this, stores, conf};

  /////////////////////
  // MAIN PASS LOOP. //
  /////////////////////
  bool after_interdex = false;
  for (size_t i = 0; i < m_activated_passes.size(); ++i) {
    ctx.run_pass(i, after_interdex);
  }
}

PassManager::ActivatedPasses PassManager::compute_activated_passes(
    std::vector<Pass*> registered_passes,
    const ConfigFiles& config,
    PassManagerConfig* pm_config_override) {
  ActivatedPasses result;
  if (config.get_json_config().contains("redex") &&
      config.get_json_config().get("redex", Json::Value()).isMember("passes")) {
    PassManagerConfig default_config;
    auto& pm_config = [&]() -> PassManagerConfig& {
      if (pm_config_override != nullptr) {
        return *pm_config_override;
      }
      if (!config.get_global_config().has_config_by_name("pass_manager")) {
        return default_config;
      }
      return *config.get_global_config().get_config_by_name<PassManagerConfig>(
          "pass_manager");
    }();
    auto get_alias = [pm_config](const auto& name) -> const std::string* {
      auto it = pm_config.pass_aliases.find(name);
      if (it == pm_config.pass_aliases.end()) {
        return nullptr;
      }
      return &it->second;
    };

    const auto& json_config = config.get_json_config();
    const auto& passes_from_config = json_config["redex"]["passes"];
    for (const auto& pass : passes_from_config) {
      std::string pass_name = pass.asString();

      // Check whether it is explicitly disabled.
      auto is_disabled = [&json_config, &pass_name]() {
        if (!json_config.contains(pass_name.c_str())) {
          return false;
        }
        const auto& pass_data = json_config[pass_name.c_str()];
        if (!pass_data.isMember("disabled")) {
          return false;
        }
        return pass_data["disabled"].asBool();
      };
      if (is_disabled()) {
        continue;
      }

      // Names may or may not have a "#<id>" suffix to indicate their order in
      // the pass list, which needs to be removed for matching.
      auto activate = [&registered_passes, &result](const std::string& n,
                                                    const std::string* a) {
        for (auto* registered_pass : registered_passes) {
          if (n == registered_pass->name()) {
            auto* activated_pass = registered_pass;
            if (a != nullptr) {
              auto cloned_pass = registered_pass->clone(*a);
              always_assert_log(cloned_pass != nullptr,
                                "Cannot clone pass %s to make alias %s",
                                n.c_str(), a->c_str());
              activated_pass = cloned_pass.get();
              result.cloned_passes.emplace_back(std::move(cloned_pass));
            }

            result.activated_passes.emplace_back(activated_pass,
                                                 a == nullptr ? n : *a);

            return true;
          }
        }
        return false;
      };

      // Does a pass exist with this name (directly)?
      if (activate(pass_name, nullptr)) {
        continue;
      }

      // Can we find it under the given alias?
      const auto* alias = get_alias(pass_name);
      if (alias != nullptr && activate(*alias, &pass_name)) {
        continue;
      }

      always_assert_log(false, "No pass named %s(%s)!", pass_name.c_str(),
                        alias != nullptr ? alias->c_str() : "n/a");
    }
  } else {
    result.activated_passes.reserve(registered_passes.size());
    for (auto* pass : registered_passes) {
      result.activated_passes.emplace_back(pass, pass->name());
    }
  }
  return result;
}

Pass* PassManager::find_pass(const std::string& pass_name) const {
  auto pass_it = std::find_if(
      m_activated_passes.begin(),
      m_activated_passes.end(),
      [&pass_name](const Pass* pass) { return pass->name() == pass_name; });
  return pass_it != m_activated_passes.end() ? *pass_it : nullptr;
}

int64_t PassManager::get_metric(const std::string& key) {
  std::unique_lock<std::mutex> lock{m_internal_fields->m_metrics_lock};
  return (m_current_pass_info->metrics)[key];
}

const std::vector<PassManager::PassInfo>& PassManager::get_pass_info() const {
  return m_pass_info;
}

const UnorderedMap<std::string, int64_t>& PassManager::get_interdex_metrics() {
  for (const auto& pass_info : m_pass_info) {
    if (pass_info.pass->name() == "InterDexPass") {
      return pass_info.metrics;
    }
  }
  static UnorderedMap<std::string, int64_t> empty;
  return empty;
}

ReserveRefsInfoHandle PassManager::reserve_refs(const std::string& name,
                                                const ReserveRefsInfo& info) {
  return m_reserved_ref_infos.insert(m_reserved_ref_infos.end(),
                                     std::make_pair(name, info));
}

void PassManager::release_reserved_refs(ReserveRefsInfoHandle handle) {
  m_reserved_ref_infos.erase(handle);
}

ReserveRefsInfo PassManager::get_reserved_refs() const {
  ReserveRefsInfo res;
  for (const auto& [_, info] : m_reserved_ref_infos) {
    res += info;
  }
  return res;
}
