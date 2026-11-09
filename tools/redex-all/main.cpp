/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <json/reader.h>
#include <json/value.h>
#include <json/writer.h>

#include <cstring>
#include <ctime>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <iterator>
#include <memory>
#include <optional>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>

#include <fcntl.h>
#include <signal.h>
#include <sstream>
#include <sys/stat.h>

#ifdef _MSC_VER
#include <io.h>
#else
#include <unistd.h>
#endif

#include <boost/program_options/options_description.hpp>
#include <boost/program_options/parsers.hpp>
#include <boost/program_options/positional_options.hpp>
#include <boost/program_options/value_semantic.hpp>
#include <boost/program_options/variables_map.hpp>

#include "AggregateException.h"
#include "ChromeTraceWriter.h"
#include "ClassOrderSample.h"
#include "CommandProfiling.h"
#include "ConfigFiles.h"
#include "ControlFlow.h" // To set s_DEBUG.
#include "Debug.h"
#include "DebugUtils.h"
#include "DexClass.h"
#include "DexHasher.h"
#include "DexLoader.h"
#include "DexOutput.h"
#include "DexPosition.h"
#include "DexVt.h"
#include "DuplicateClasses.h"
#include "GlobalConfig.h"
#include "IODIMetadata.h"
#include "InstructionLowering.h"
#include "JarLoader.h"
#include "JemallocUtil.h"
#include "KeepReason.h"
#include "Macros.h"
#include "MallocDebug.h"
#include "MethodProfiles.h"
#include "MethodUtil.h"
#include "NoOptimizationsMatcher.h"
#include "OptData.h"
#include "PassRegistry.h"
#include "ProguardConfiguration.h" // New ProGuard configuration
#include "ProguardMatcher.h"
#include "ProguardParser.h" // New ProGuard Parser
#include "ProguardPrintConfiguration.h" // New ProGuard configuration
#include "ProguardReporting.h"
#include "ReachableClasses.h"
#include "RedexContext.h"
#include "RedexProperties.h"
#include "RedexPropertiesManager.h"
#include "RedexPropertyCheckerRegistry.h"
#include "RedexResources.h"
#include "Sanitizers.h"
// NOLINTNEXTLINE(facebook-unused-include-check)
#include "ConstantPropagationAnalysis.h"
#include "ConstantPropagationTransform.h"
// NOLINTNEXTLINE(facebook-unused-include-check)
#include "SanitizersConfig.h"
#include "ScopedMemStats.h"
#include "Show.h"
#include "ThreadPool.h"
#include "Timer.h"
#include "ToolsCommon.h"
#include "Walkers.h"
#include "Warning.h"
#include "WorkQueue.h" // For concurrency.

namespace {

// Do *not* change these values. Many services will break.
constexpr const char* LINE_NUMBER_MAP = "redex-line-number-map-v2";
constexpr const char* DEBUG_LINE_MAP = "redex-debug-line-map-v2";
constexpr const char* IODI_METADATA = "iodi-metadata";
constexpr const char* OPT_DECISIONS = "redex-opt-decisions.json";
constexpr const char* CLASS_METHOD_INFO_MAP = "redex-class-method-info-map.txt";
constexpr const char* STRING_LOCALE_DUMP = "redex-string-locales.txt";
constexpr const char* CLASS_TO_FILES_MAP = "redex-class-to-files-map.txt";

const std::string k_usage_header = "usage: redex-all [options...] dex-files...";

void print_usage() {
  std::cout << k_usage_header << '\n';
  std::cout << "Try 'redex-all -h' for more information." << '\n';
}

struct Arguments {
  Json::Value config{Json::nullValue};
  std::set<std::string> jar_paths;
  std::vector<std::string> proguard_config_paths;
  std::string out_dir;
  std::vector<std::string> dex_files;
  // Entry data contains the list of dex files, config file and original
  // command line arguments. For development usage
  Json::Value entry_data;
  std::optional<int> stop_pass_idx;
  RedexOptions redex_options;
  bool properties_check{false};
  bool properties_check_allow_disabled{false};
  std::optional<std::string> assert_abort;
  std::optional<std::string> crash_file;
  bool chrome_trace{false};
};

DEBUG_ONLY void dump_args(const Arguments& args) {
  std::cout << "out_dir: " << args.out_dir << '\n';
  std::cout << "verify_none_mode: " << args.redex_options.verify_none_enabled
            << '\n';
  std::cout << "art_build: " << args.redex_options.is_art_build << '\n';
  std::cout << "enable_instrument_pass: "
            << args.redex_options.instrument_pass_enabled << '\n';
  std::cout << "min_sdk: " << args.redex_options.min_sdk << '\n';
  std::cout << "debug_info_kind: "
            << debug_info_kind_to_string(args.redex_options.debug_info_kind)
            << '\n';
  std::cout << "jar_paths: " << '\n';
  for (const auto& e : args.jar_paths) {
    std::cout << "  " << e << '\n';
  }
  std::cout << "proguard_config_paths: " << '\n';
  for (const auto& e : args.proguard_config_paths) {
    std::cout << "  " << e << '\n';
  }
  std::cout << "dex_files: " << '\n';
  for (const auto& e : args.dex_files) {
    std::cout << "  " << e << '\n';
  }
  std::cout << "config: " << '\n';
  std::cout << args.config << '\n';
  std::cout << "arch: " << '\n';
  std::cout << args.redex_options.arch << '\n';
}

Json::Value parse_json_value(const std::string& value_string) {
  std::istringstream temp_stream(value_string);
  Json::Value temp_json;
  temp_stream >> temp_json;
  return temp_json;
}

bool add_value_to_config(Json::Value& config,
                         const std::string& key_value,
                         bool is_json) {
  const size_t equals_idx = key_value.find('=');
  if (equals_idx == std::string::npos) {
    return false;
  }

  const size_t dot_idx = key_value.find('.');
  if (dot_idx != std::string::npos && dot_idx < equals_idx) {
    // Pass-specific config value specified with -Dpassname.key=value
    std::string pass = key_value.substr(0, dot_idx);
    std::string key = key_value.substr(dot_idx + 1, equals_idx - dot_idx - 1);
    std::string value_string = key_value.substr(equals_idx + 1);
    if (is_json) {
      config[pass][key] = parse_json_value(value_string);
    } else {
      config[pass][key] = value_string;
    }
  } else {
    // Global config value specified with -Dkey=value
    std::string key = key_value.substr(0, equals_idx);
    std::string value_string = key_value.substr(equals_idx + 1);
    if (is_json) {
      config[key] = parse_json_value(value_string);
    } else {
      config[key] = value_string;
    }
  }
  return true;
}

Json::Value default_config() {
  const auto passes = {
      "ReBindRefsPass",   "BridgeSynthInlinePass", "FinalInlinePassV2",
      "DelSuperPass",     "SingleImplPass",        "MethodInlinePass",
      "StaticReloPassV2", "RegAllocPass",
  };
  std::istringstream temp_json("{\"redex\":{\"passes\":[]}}");
  Json::Value cfg;
  temp_json >> cfg;
  for (auto const& pass : passes) {
    cfg["redex"]["passes"].append(pass);
  }
  return cfg;
}

Json::Value reflect_config(const Configurable::Reflection& cr) {
  Json::Value params = Json::arrayValue;
  Json::Value traits = Json::arrayValue;
  int params_idx = 0;
  for (const auto& entry : cr.params) {
    Json::Value param;
    param["name"] = entry.first;
    param["doc"] = entry.second.doc;
    param["is_required"] = entry.second.is_required;
    param["bindflags"] = static_cast<Json::UInt64>(entry.second.bindflags);
    [&]() {
      switch (entry.second.type) {
      case Configurable::ReflectionParam::Type::PRIMITIVE:
        param["type"] =
            std::get<Configurable::ReflectionParam::Type::PRIMITIVE>(
                entry.second.variant);
        param["default_value"] = entry.second.default_value;
        return;
      case Configurable::ReflectionParam::Type::COMPOSITE:
        param["type"] = reflect_config(
            std::get<Configurable::ReflectionParam::Type::COMPOSITE>(
                entry.second.variant));
        return;
      }
      not_reached_log("Invalid Configurable::ReflectionParam::Type: %d",
                      entry.second.type);
    }();
    params[params_idx++] = param;
  }
  int traits_idx = 0;
  for (const auto& entry : cr.traits) {
    Json::Value trait;
    trait["name"] = entry.first;
    trait["value"] = entry.second.value;
    traits[traits_idx++] = trait;
  }
  Json::Value reflected_config;
  reflected_config["name"] = cr.name;
  reflected_config["doc"] = cr.doc;
  reflected_config["params"] = params;
  reflected_config["traits"] = traits;
  return reflected_config;
}

void add_pass_properties_reflection(Json::Value& value, Pass* pass) {
  using namespace redex_properties;
  auto interactions = pass->get_property_interactions();
  if (interactions.empty()) {
    return;
  }

  Json::Value establishes = Json::arrayValue;
  Json::Value requires_ = Json::arrayValue;
  Json::Value preserves = Json::arrayValue;
  Json::Value requires_finally = Json::arrayValue;

  for (const auto& [property, inter] : UnorderedIterable(interactions)) {
    if (inter.establishes) {
      establishes.append(get_name(property));
    }
    if (inter.requires_) {
      requires_.append(get_name(property));
    }
    if (inter.preserves) {
      preserves.append(get_name(property));
    }
    if (inter.requires_finally) {
      requires_finally.append(get_name(property));
    }
  }

  Json::Value properties;
  properties["establishes"] = establishes;
  properties["requires"] = requires_;
  properties["preserves"] = preserves;
  properties["requires_finally"] = requires_finally;

  value["properties"] = properties;
}

Json::Value reflect_property_definitions() {
  Json::Value properties;

  properties["properties"] = []() {
    Json::Value prop_map;
    auto all = redex_properties::get_all_properties();
    for (auto& prop : all) {
      Json::Value prop_value;
      prop_value["negative"] = redex_properties::is_negative(prop);
      prop_map[redex_properties::get_name(prop)] = std::move(prop_value);
    }
    return prop_map;
  }();

  auto create_sorted = [](const auto& input) -> Json::Value {
    auto tmp = unordered_to_ordered(input);

    Json::Value holder = Json::arrayValue;
    for (auto& prop : tmp) {
      holder.append(redex_properties::get_name(prop));
    }
    return holder;
  };

  properties["initial"] =
      create_sorted(redex_properties::Manager::get_default_initial());
  properties["final"] =
      create_sorted(redex_properties::Manager::get_default_final());

  return properties;
}

#pragma GCC diagnostic push
// Necessary for unknown errors in older versions.
#pragma GCC diagnostic ignored "-Wpragmas"
// NOLINTNEXTLINE
#pragma GCC diagnostic ignored "-Wdangling-pointer"
#pragma GCC diagnostic ignored "-Winfinite-recursion"
void __attribute__((noinline, optnone)) assert_abort(const std::string& message,
                                                     size_t depth) {
  // Ensure some stack for testing.
  if (depth < 3) {
    assert_abort(message, depth + 1);
  } else {
    always_assert_log(false, "%s", message.c_str());
  }
}

[[noreturn]] void __attribute__((noinline)) asan_abort() {
  // Use a use-after-scope issue for simplicity.
  volatile int* tmp;
  {
    int x = 5;
    tmp = &x;
  }
  *tmp = 6;

  // Uh-oh.
  always_assert_log(false, "Should have failed by now. :-(");
}
#pragma GCC diagnostic pop

struct CrashFile {
  bool ok_exit{false};
  std::string path;
  int fd{-1};

  CrashFile() = default;

  CrashFile(const CrashFile&) = delete;
  CrashFile& operator=(const CrashFile&) = delete;

  ~CrashFile() {
    // We leave the fd dangling on error cases so we do not have to think
    // about all the error paths and RAII.
    if (fd != -1 && ok_exit) {
      close(fd);
      std::filesystem::remove(path);
    }
  }

  int open(std::string crash_file_path) {
    path = std::move(crash_file_path);
    fd = ::open(path.c_str(), O_CREAT | O_WRONLY,
                S_IRUSR | S_IWUSR | S_IRGRP | S_IROTH);
    return fd;
  }

  void set_ok() { ok_exit = true; }
};

Arguments parse_args(int argc, char* argv[]) {
  Arguments args;
  args.out_dir = ".";
  args.config = default_config();

  namespace po = boost::program_options;
  po::options_description od(k_usage_header);
  od.add_options()("help,h", "print this help message");
  od.add_options()("reflect-config",
                   "print a reflection of the config and exit");
  od.add_options()(
      "properties-check",
      "parse configuration, perform a stack properties check and exit");
  od.add_options()("properties-check-allow-disabled",
                   "accept the disable flag in the configuration");
  od.add_options()("apkdir,a",
                   // We allow overwrites to most of the options but will take
                   // only the last one.
                   po::value<std::vector<std::string>>(),
                   "directory containing unzipped APK");
  od.add_options()("config,c",
                   po::value<std::vector<std::string>>(),
                   "JSON-formatted config file");
  od.add_options()("outdir,o",
                   po::value<std::vector<std::string>>(),
                   "output directory for optimized dexes");
  od.add_options()(
      // This option value will be accumulated to a vector.
      "jarpath,j",
      po::value<std::vector<std::string>>(),
      "classpath jar");
  od.add_options()("proguard-config,p",
                   po::value<std::vector<std::string>>(), // Accumulation
                   "ProGuard config file");
  od.add_options()("printseeds,q",
                   po::value<std::vector<std::string>>(),
                   "file to report seeds computed by redex");
  od.add_options()(
      "used-js-assets", po::value<std::vector<std::string>>(),
      "A JSON file (or files) containing a list of resources used by JS");
  od.add_options()(
      "dump-string-locales",
      po::value<bool>(),
      "Writes out the locales of all string resources into a file");
  od.add_options()("warn,w",
                   po::value<std::vector<int>>(),
                   "warning level:\n"
                   "  0: no warnings\n"
                   "  1: count of warnings\n"
                   "  2: full text of warnings");
  od.add_options()(
      "verify-none-mode",
      po::bool_switch(&args.redex_options.verify_none_enabled)
          ->default_value(false),
      "run redex in verify-none mode\n"
      "  \tThis will activate optimization passes or code in some passes that "
      "wouldn't normally operate with verification enabled.");
  od.add_options()(
      "emit-dexvt",
      po::bool_switch(&args.redex_options.emit_dexvt)->default_value(false),
      "Emit the dexvt build-side export (symbolicated disassembly + per-method "
      "PGO + authoritative sizes + xref) as NDJSON in the output metadata "
      "dir.");
  od.add_options()(
      "is-art-build",
      po::bool_switch(&args.redex_options.is_art_build)->default_value(false),
      "If specified, states that the current build is art specific.\n");
  od.add_options()(
      "disable-dex-hasher",
      po::bool_switch(&args.redex_options.disable_dex_hasher)
          ->default_value(false),
      "If specified, states that the current run disables dex hasher.\n");
  od.add_options()(
      "arch,A",
      po::value<std::vector<std::string>>(),
      "Architecture; one of arm/arm64/thumb2/x86_64/x86/mips/mips64");
  od.add_options()("enable-instrument-pass",
                   po::bool_switch(&args.redex_options.instrument_pass_enabled)
                       ->default_value(false),
                   "If specified, enables InstrumentPass if any.\n");
  od.add_options()(",S",
                   po::value<std::vector<std::string>>(), // Accumulation
                   "-Skey=string\n"
                   "  \tAdd a string value to the global config, overwriting "
                   "the existing value if any\n"
                   "    \te.g. -Smy_param_name=foo\n"
                   "-Spass_name.key=string\n"
                   "  \tAdd a string value to a pass"
                   "config, overwriting the existing value if any\n"
                   "    \te.g. -SMyPass.config=\"foo bar\"");
  od.add_options()(
      ",J",
      po::value<std::vector<std::string>>(), // Accumulation
      "-Jkey=<json value>\n"
      "  \tAdd a json value to the global config, overwriting the existing "
      "value if any\n"
      "    \te.g. -Jmy_param_name={\"foo\": true}\n"
      "-JSomePassName.key=<json value>\n"
      "  \tAdd a json value to a pass config, overwriting the existing value "
      "if any\n"
      "    \te.g. -JMyPass.config=[1, 2, 3]\n"
      "Note: Be careful to properly escape JSON parameters, e.g., strings must "
      "be quoted.");
  od.add_options()("show-passes", "show registered passes");
  od.add_options()("dex-files", po::value<std::vector<std::string>>(),
                   "dex files");

  // Development usage only, and Python script will generate the following
  // arguments.
  od.add_options()("stop-pass", po::value<int>(),
                   "Stop before pass n and output IR to file");
  od.add_options()("output-ir", po::value<std::string>(),
                   "IR output directory, used with --stop-pass");
  od.add_options()("jni-summary",
                   po::value<std::string>(),
                   "Path to JNI summary directory of json files.");

  od.add_options()("crash-file", po::value<std::string>(),
                   "Path to a file crash data should be written to.");
  od.add_options()(
      "chrome-trace",
      "Write a Chrome Trace Event JSON file (redex-chrome-trace.json) to the "
      "meta output directory for visualization in Perfetto or "
      "chrome://tracing.");

  // For testing purposes.
  od.add_options()("assert-abort", po::value<std::string>(),
                   "Assert on startup with the given message.");
  od.add_options()(
      "assert-abort-thread", po::value<std::string>(),
      "Assert on startup on a non-main thread with the given message.");
  od.add_options()("asan-abort", "Run code that should trigger an ASAN abort.");

  po::positional_options_description pod;
  pod.add("dex-files", -1);
  po::variables_map vm;

  try {
    po::store(
        po::command_line_parser(argc, argv).options(od).positional(pod).run(),
        vm);
    po::notify(vm);
  } catch (std::exception& e) {
    std::cerr << e.what() << "\n\n";
    print_usage();
    exit(EXIT_FAILURE);
  }

  // -h, --help handling must be the first.
  if (vm.count("help") != 0u) {
    od.print(std::cout);
    exit(EXIT_SUCCESS);
  }

  if (vm.count("crash-file") != 0u) {
    args.crash_file = vm["crash-file"].as<std::string>();
  }

  if (vm.count("chrome-trace") != 0u) {
    args.chrome_trace = true;
  }

  if (vm.count("assert-abort") != 0u) {
    CrashFile crash_file;
    if (args.crash_file) {
      set_crash_fd(crash_file.open(*args.crash_file));
    }
    assert_abort(vm["assert-abort"].as<std::string>(), 0);
  }
  if (vm.count("assert-abort-thread") != 0u) {
    CrashFile crash_file;
    if (args.crash_file) {
      set_crash_fd(crash_file.open(*args.crash_file));
    }
    // Some effort to ensure we're on a different thread.
    workqueue_run_for(0, 100, [&](auto num) {
      if (num == 99) {
        assert_abort(vm["assert-abort-thread"].as<std::string>(), 0);
      }
    });
    always_assert_log(false, "Should have failed by now. :-(");
  }
  if (vm.count("asan-abort") != 0u) {
    asan_abort();
  }

  // --reflect-config handling must be next
  if (vm.count("reflect-config") != 0u) {
    Json::Value reflected_config;

    GlobalConfig gc(GlobalConfig::default_registry());
    reflected_config["global"] = reflect_config(gc.reflect());

    Json::Value pass_configs = Json::arrayValue;
    const auto& passes = PassRegistry::get().get_passes();
    for (size_t i = 0; i < passes.size(); ++i) {
      const auto& pass = passes[i];
      pass_configs[static_cast<int>(i)] = reflect_config(pass->reflect());
      add_pass_properties_reflection(pass_configs[static_cast<int>(i)], pass);
    }
    reflected_config["passes"] = pass_configs;

    reflected_config["properties"] = reflect_property_definitions();

    std::cout << reflected_config << std::flush;
    // Use _exit() to avoid running static destructors, which can crash
    // when ConcurrentContainer destructors access already-destroyed
    // AccumulatingTimer globals during exit() tear-down.
    _exit(EXIT_SUCCESS);
  }

  if (vm.count("show-passes") != 0u) {
    const auto& passes = PassRegistry::get().get_passes();
    std::cout << "Registered passes: " << passes.size() << '\n';
    for (size_t i = 0; i < passes.size(); ++i) {
      std::cout << i + 1 << ": " << passes[i]->name() << '\n';
    }
    exit(EXIT_SUCCESS);
  }

  if (vm.count("properties-check") != 0u) {
    args.properties_check = true;
  }
  if (vm.count("properties-check-allow-disabled") != 0u) {
    args.properties_check_allow_disabled = true;
  }

  if (vm.count("dex-files") != 0u) {
    args.dex_files = vm["dex-files"].as<std::vector<std::string>>();
  } else if (!args.properties_check) {
    std::cerr << "error: no input dex files\n\n";
    print_usage();
    exit(EXIT_SUCCESS);
  }

  if (vm.count("warn") != 0u) {
    const auto& warns = vm["warn"].as<std::vector<int>>();
    for (int warn : warns) {
      if (0 > warn || warn > 2) {
        std::cerr << "warning: ignoring invalid warning level option: " << warn
                  << '\n';
      }
    }
    g_warning_level = OptWarningLevel(warns.back());
  }

  auto take_last = [](const auto& value) {
    return value.template as<std::vector<std::string>>().back();
  };

  if (vm.count("config") != 0u) {
    const std::string& config_file = take_last(vm["config"]);
    args.entry_data["config"] =
        boost::filesystem::absolute(config_file).string();
    args.config = redex::parse_config(config_file);
  }

  if (vm.count("outdir") != 0u) {
    args.out_dir = take_last(vm["outdir"]);
    if (!redex::dir_is_writable(args.out_dir)) {
      std::cerr << "error: outdir is not a writable directory: " << args.out_dir
                << '\n';
      exit(EXIT_FAILURE);
    }
  }

  if (vm.count("proguard-config") != 0u) {
    args.proguard_config_paths =
        vm["proguard-config"].as<std::vector<std::string>>();
  }

  if (vm.count("jarpath") != 0u) {
    const auto& jar_paths = vm["jarpath"].as<std::vector<std::string>>();
    for (const auto& e : jar_paths) {
      TRACE(MAIN, 2, "Command line -j option: %s", e.c_str());
      args.jar_paths.emplace(e);
    }
  }

  // We add these values to the config at the end so that they will always
  // overwrite values read from the config file regardless of the order of
  // arguments.
  if (vm.count("apkdir") != 0u) {
    args.entry_data["apk_dir"] = args.config["apk_dir"] =
        take_last(vm["apkdir"]);
  }

  if (vm.count("printseeds") != 0u) {
    args.config["printseeds"] = take_last(vm["printseeds"]);
  }

  if (vm.count("used-js-assets") != 0u) {
    const auto& js_assets_lists =
        vm["used-js-assets"].as<std::vector<std::string>>();
    Json::Value array(Json::arrayValue);
    for (const auto& list : js_assets_lists) {
      array.append(list);
    }
    args.config["used-js-assets"] = array;
  }

  if (vm.count("dump-string-locales") != 0u) {
    args.config["dump-string-locales"] = vm["dump-string-locales"].as<bool>();
  }

  if (vm.count("arch") != 0u) {
    std::string arch = take_last(vm["arch"]);
    args.redex_options.arch = parse_architecture(arch);
    if (args.redex_options.arch == Architecture::UNKNOWN) {
      std::cerr << "warning: cannot architecture " << arch << '\n';
    }
  }

  if (vm.count("-S") != 0u) {
    for (const auto& key_value : vm["-S"].as<std::vector<std::string>>()) {
      if (!add_value_to_config(args.config, key_value, false)) {
        std::cerr << "warning: cannot parse -S" << key_value << '\n';
      }
    }
  }

  if (vm.count("-J") != 0u) {
    for (const auto& key_value : vm["-J"].as<std::vector<std::string>>()) {
      if (!add_value_to_config(args.config, key_value, true)) {
        std::cerr << "warning: cannot parse -J" << key_value << '\n';
      }
    }
  }

  args.redex_options.debug_info_kind =
      parse_debug_info_kind(args.config.get("debug_info_kind", "").asString());

  // Development usage only
  if (vm.count("stop-pass") != 0u) {
    args.stop_pass_idx = vm["stop-pass"].as<int>();
  }

  if (vm.count("output-ir") != 0u) {
    // The out_dir is for final apk only or intermediate results only.
    always_assert(args.stop_pass_idx);
    args.out_dir = vm["output-ir"].as<std::string>();
  }

  if (vm.count("jni-summary") != 0u) {
    args.redex_options.jni_summary_path = vm["jni-summary"].as<std::string>();
  }

  if (args.stop_pass_idx != std::nullopt) {
    // Resize the passes list and append an additional RegAllocPass if its final
    // pass is not RegAllocPass.
    auto& passes_list = args.config["redex"]["passes"];
    int idx = *args.stop_pass_idx;
    if (idx < 0 || (size_t)idx > passes_list.size()) {
      std::cerr << "Invalid stop_pass value\n";
      exit(EXIT_FAILURE);
    }
    if (passes_list.size() > (size_t)idx) {
      passes_list.resize(idx);
    }
    // Append the two passes when `--stop-pass` is enabled.
    passes_list.append("MakePublicPass");
    passes_list.append("RegAllocPass");
    if (args.out_dir.empty() || !redex::dir_is_writable(args.out_dir)) {
      std::cerr << "output-ir is empty or not writable" << '\n';
      exit(EXIT_FAILURE);
    }
  }

  std::string metafiles = args.out_dir + "/meta/";
  int status = [&metafiles]() -> int {
#if !IS_WINDOWS
    return mkdir(metafiles.c_str(), 0755);
#else
    return mkdir(metafiles.c_str());
#endif
  }();
  if (status != 0 && errno != EEXIST) {
    // Attention: errno may get changed by syscalls or lib functions.
    // Saving before printing is a conventional way of using errno.
    int errsv = errno;
    std::cerr << "error: cannot mkdir meta in outdir. errno = " << errsv
              << '\n';
    exit(EXIT_FAILURE);
  }

  TRACE(MAIN, 2, "Verify-none mode: %s",
        args.redex_options.verify_none_enabled ? "Yes" : "No");
  TRACE(MAIN, 2, "Art build: %s",
        args.redex_options.is_art_build ? "Yes" : "No");
  TRACE(MAIN, 2, "Enable InstrumentPass: %s",
        args.redex_options.instrument_pass_enabled ? "Yes" : "No");

  return args;
}

Json::Value get_stats(const dex_stats_t& stats) {
  Json::Value val;
  val["num_types"] = stats.num_types;
  val["num_type_lists"] = stats.num_type_lists;
  val["num_classes"] = stats.num_classes;
  val["num_methods"] = stats.num_methods;
  val["num_method_refs"] = stats.num_method_refs;
  val["num_fields"] = stats.num_fields;
  val["num_field_refs"] = stats.num_field_refs;
  val["num_strings"] = stats.num_strings;
  val["num_protos"] = stats.num_protos;
  val["num_static_values"] = stats.num_static_values;
  val["num_annotations"] = stats.num_annotations;
  val["num_bytes"] = stats.num_bytes;
  val["num_instructions"] = stats.num_instructions;
  val["num_tries"] = stats.num_tries;

  val["num_unique_types"] = stats.num_unique_types;
  val["num_unique_protos"] = stats.num_unique_protos;
  val["num_unique_strings"] = stats.num_unique_strings;
  val["num_unique_method_refs"] = stats.num_unique_method_refs;
  val["num_unique_field_refs"] = stats.num_unique_field_refs;

  val["types_total_size"] = stats.types_total_size;
  val["protos_total_size"] = stats.protos_total_size;
  val["strings_total_size"] = stats.strings_total_size;
  val["method_refs_total_size"] = stats.method_refs_total_size;
  val["field_refs_total_size"] = stats.field_refs_total_size;

  val["num_dbg_items"] = stats.num_dbg_items;
  val["dbg_total_size"] = stats.dbg_total_size;

  val["instruction_bytes"] = stats.instruction_bytes;

  val["header_item_count"] = stats.header_item_count;
  val["header_item_bytes"] = stats.header_item_bytes;
  val["string_id_count"] = stats.string_id_count;
  val["string_id_bytes"] = stats.string_id_bytes;
  val["type_id_count"] = stats.type_id_count;
  val["type_id_bytes"] = stats.type_id_bytes;
  val["proto_id_count"] = stats.proto_id_count;
  val["proto_id_bytes"] = stats.proto_id_bytes;
  val["field_id_count"] = stats.field_id_count;
  val["field_id_bytes"] = stats.field_id_bytes;
  val["method_id_count"] = stats.method_id_count;
  val["method_id_bytes"] = stats.method_id_bytes;
  val["class_def_count"] = stats.class_def_count;
  val["class_def_bytes"] = stats.class_def_bytes;
  val["call_site_id_count"] = stats.call_site_id_count;
  val["call_site_id_bytes"] = stats.call_site_id_bytes;
  val["method_handle_count"] = stats.method_handle_count;
  val["method_handle_bytes"] = stats.method_handle_bytes;
  val["map_list_count"] = stats.map_list_count;
  val["map_list_bytes"] = stats.map_list_bytes;
  val["type_list_count"] = stats.type_list_count;
  val["type_list_bytes"] = stats.type_list_bytes;
  val["annotation_set_ref_list_count"] = stats.annotation_set_ref_list_count;
  val["annotation_set_ref_list_bytes"] = stats.annotation_set_ref_list_bytes;
  val["annotation_set_count"] = stats.annotation_set_count;
  val["annotation_set_bytes"] = stats.annotation_set_bytes;
  val["class_data_count"] = stats.class_data_count;
  val["class_data_bytes"] = stats.class_data_bytes;
  val["code_count"] = stats.code_count;
  val["code_bytes"] = stats.code_bytes;
  val["string_data_count"] = stats.string_data_count;
  val["string_data_bytes"] = stats.string_data_bytes;
  val["debug_info_count"] = stats.debug_info_count;
  val["debug_info_bytes"] = stats.debug_info_bytes;
  val["annotation_count"] = stats.annotation_count;
  val["annotation_bytes"] = stats.annotation_bytes;
  val["encoded_array_count"] = stats.encoded_array_count;
  val["encoded_array_bytes"] = stats.encoded_array_bytes;
  val["annotations_directory_count"] = stats.annotations_directory_count;
  val["annotations_directory_bytes"] = stats.annotations_directory_bytes;

  val["class_order_violations"] = stats.class_order_violations;

  return val;
}

Json::Value get_pass_stats(const PassManager& mgr) {
  Json::Value all(Json::ValueType::objectValue);
  for (const auto& pass_info : mgr.get_pass_info()) {
    if (pass_info.metrics.empty()) {
      continue;
    }
    Json::Value pass;
    for (const auto& pass_metric : UnorderedIterable(pass_info.metrics)) {
      pass[pass_metric.first] = (Json::Int64)pass_metric.second;
    }
    all[pass_info.name] = pass;
  }
  return all;
}

Json::Value get_pass_hashes(const PassManager& mgr) {
  Json::Value all(Json::ValueType::objectValue);
  auto initial_hash = mgr.get_initial_hash();
  if (initial_hash) {
    all["(initial)-positions"] =
        hashing::hash_to_string(initial_hash->positions_hash);
    all["(initial)-registers"] =
        hashing::hash_to_string(initial_hash->registers_hash);
    all["(initial)-code"] = hashing::hash_to_string(initial_hash->code_hash);
    all["(initial)-signature"] =
        hashing::hash_to_string(initial_hash->signature_hash);
  }
  for (const auto& pass_info : mgr.get_pass_info()) {
    auto hash = pass_info.hash;
    if (hash) {
      all[pass_info.name + "-positions"] =
          hashing::hash_to_string(hash->positions_hash);
      all[pass_info.name + "-registers"] =
          hashing::hash_to_string(hash->registers_hash);
      all[pass_info.name + "-code"] = hashing::hash_to_string(hash->code_hash);
      all[pass_info.name + "-signature"] =
          hashing::hash_to_string(hash->signature_hash);
    }
  }
  return all;
}

Json::Value get_lowering_stats(const instruction_lowering::Stats& stats) {
  using namespace instruction_lowering;

  Json::Value obj(Json::ValueType::objectValue);
  obj["num_2addr_instructions"] = Json::UInt(stats.to_2addr);
  obj["num_move_added_for_check_cast"] = Json::UInt(stats.move_for_check_cast);

  if (!stats.sparse_switches.data.empty()) {
    // Some statistics.
    Json::Value sparse_switches(Json::ValueType::objectValue);
    sparse_switches["min"] =
        Json::UInt(stats.sparse_switches.data.begin()->first);
    sparse_switches["max"] =
        Json::UInt(stats.sparse_switches.data.rbegin()->first);
    sparse_switches["avg100"] = Json::UInt([&]() {
      size_t cnt = 0;
      size_t sum = 0;
      for (const auto& p : stats.sparse_switches.data) {
        cnt += p.second.all;
        sum += p.second.all * p.first;
      }
      return sum * 100 / cnt;
    }());

    auto span = stats.sparse_switches.data.rbegin()->first -
                stats.sparse_switches.data.begin()->first;
    constexpr size_t kBuckets = 10;
    if (span > kBuckets) {
      const auto first = stats.sparse_switches.data.begin()->first;
      const auto last = stats.sparse_switches.data.rbegin()->first;

      auto it = stats.sparse_switches.data.begin();
      auto end = stats.sparse_switches.data.end();
      Json::Value buckets(Json::ValueType::objectValue);

      auto per_bucket = span / kBuckets;
      for (size_t i = 0; i != kBuckets; ++i) {
        auto start_size = first + i * per_bucket;
        auto end_size = first + (i + 1) * per_bucket;
        if (i == kBuckets - 1) {
          end_size = last + 1;
        }
        redex_assert(it->first >= start_size);
        redex_assert(end_size > start_size);

        Stats::SparseSwitches::Data tmp{};
        for (; it != end && it->first < end_size; ++it) {
          tmp += it->second;
        }

        if (tmp.all != 0) {
          Json::Value bucket(Json::ValueType::objectValue);
          bucket["all"] = Json::UInt(tmp.all);
          bucket["in_hot_methods"] = Json::UInt(tmp.in_hot_methods);
          bucket["min"] = Json::UInt(start_size);
          bucket["max"] = Json::UInt(end_size);
          buckets[std::to_string(i)] = bucket;
        }
      }
      redex_assert(it == end);
      sparse_switches["buckets"] = buckets;
    }

    obj["sparse_switches"] = sparse_switches;
  }

  return obj;
}

Json::Value get_position_stats(const PositionMapper* pos_mapper) {
  Json::Value obj(Json::ValueType::objectValue);
  obj["num_positions"] = Json::UInt(pos_mapper->size());
  return obj;
}

Json::Value get_detailed_stats(const std::vector<dex_stats_t>& dexes_stats) {
  Json::Value dexes;
  int i = 0;
  for (const dex_stats_t& stats : dexes_stats) {
    dexes[i++] = get_stats(stats);
  }
  return dexes;
}

Json::Value get_times(double cpu_time_s) {
  Json::Value list(Json::arrayValue);
  for (const auto& t : Timer::get_times()) {
    Json::Value element;
    element[t.first] = std::round(t.second * 10) / 10.0;
    list.append(element);
  }
  {
    Json::Value cpu_element;
    cpu_element["cpu_time"] = std::round(cpu_time_s * 10) / 10.0;
    list.append(cpu_element);
  }
  if (redex_thread_pool::ThreadPool::get_instance() != nullptr) {
    Json::Value thread_pool_element;
    thread_pool_element["thread_pool_size"] = static_cast<double>(
        redex_thread_pool::ThreadPool::get_instance()->size());
    list.append(thread_pool_element);
  }
  return list;
}

Json::Value get_input_stats(const dex_stats_t& stats,
                            const std::vector<dex_stats_t>& dexes_stats) {
  Json::Value d;
  d["total_stats"] = get_stats(stats);
  d["dexes_stats"] = get_detailed_stats(dexes_stats);
  return d;
}

Json::Value get_output_dexes_stats(
    const std::vector<std::pair<std::string, enhanced_dex_stats_t>>&
        dexes_stats) {
  Json::Value dexes;
  int i = 0;
  for (const auto& [store_name, stats] : dexes_stats) {
    dexes[i] = get_stats(stats);
    dexes[i]["store_name"] = store_name;
    ++i;
  }
  return dexes;
}

Json::Value get_output_stats(
    const dex_stats_t& stats,
    const std::vector<std::pair<std::string, enhanced_dex_stats_t>>&
        dexes_stats,
    const PassManager& mgr,
    const instruction_lowering::Stats& instruction_lowering_stats,
    const PositionMapper* pos_mapper) {
  Json::Value d;
  d["total_stats"] = get_stats(stats);
  d["dexes_stats"] = get_output_dexes_stats(dexes_stats);
  d["pass_stats"] = get_pass_stats(mgr);
  d["pass_hashes"] = get_pass_hashes(mgr);
  d["lowering_stats"] = get_lowering_stats(instruction_lowering_stats);
  d["position_stats"] = get_position_stats(pos_mapper);
  return d;
}

// Emit a segment-aware, stratified fingerprint of the main APK's class
// placement, for per-regime cross-build comparison. Only root stores are
// considered (Voltron modules are excluded); classes are visited in emission
// order (faithful to the on-disk class_defs order) and bucketed by dex-ordering
// regime: the primary dex, the betamap-ordered coldstart region, the cold
// (cross-dex-ref-minimized) region, and the likely-dead (Halfnosis) tail.
Json::Value get_class_order_sample(const DexStoresVector& stores,
                                   int cold_cap) {
  size_t num_root_classes = 0;
  for (const auto& store : stores) {
    if (!store.is_root_store()) {
      continue;
    }
    for (const auto& dex : store.get_dexen()) {
      num_root_classes += dex.size();
    }
  }
  std::vector<class_order_sample::ClassEntry> classes;
  classes.reserve(num_root_classes);

  // Monotonic across all root stores so dex indices are globally unique (dex 0
  // is the one true primary dex) even in the unusual multi-root-store case.
  uint32_t dex_index = 0;
  for (const auto& store : stores) {
    if (!store.is_root_store()) {
      continue;
    }
    for (const auto& dex : store.get_dexen()) {
      for (auto* cls : dex) {
        // classify() owns the (precedence-sensitive) bucketing rule; here we
        // just extract the primitive facts it needs from the class.
        const auto segment = class_order_sample::classify(
            cls->is_dynamically_dead(),
            cls->get_perf_sensitive() == PerfSensitiveGroup::BETAMAP_ORDERED,
            dex_index);
        classes.push_back({cls->get_deobfuscated_name_or_empty(),
                           cls->rstate.is_generated(), segment, dex_index});
      }
      dex_index++;
    }
  }

  // Guard against a non-positive cap: casting a negative int straight to
  // uint64_t would yield an enormous cap, making threshold() keep the entire
  // cold segment unsampled and silently defeat the sampling intent. Treat any
  // non-positive value as "sample no cold classes" instead.
  const uint64_t cold_cap_bound =
      cold_cap > 0 ? static_cast<uint64_t>(cold_cap) : 0;
  auto sample = class_order_sample::build(classes, cold_cap_bound);

  auto seg_to_json = [](const class_order_sample::SegmentSample& seg) {
    Json::Value hashes(Json::objectValue);
    for (const auto& sc : seg.sampled) {
      Json::Value pair(Json::arrayValue);
      pair.append((Json::UInt)sc.seg_index);
      pair.append((Json::UInt)sc.dex);
      hashes[std::to_string(sc.name_hash)] = std::move(pair);
    }
    Json::Value v(Json::objectValue);
    v["hashes"] = std::move(hashes);
    v["num_classes"] = (Json::UInt)seg.num_classes;
    v["collisions"] = (Json::UInt)seg.collisions;
    return v;
  };

  Json::Value segments(Json::objectValue);
  segments["primary"] = seg_to_json(sample.primary);
  segments["betamap"] = seg_to_json(sample.betamap);
  segments["cold"] = seg_to_json(sample.cold);
  Json::Value dead(Json::objectValue);
  dead["num_classes"] = (Json::UInt)sample.dead_num_classes;
  segments["dead"] = std::move(dead);

  Json::Value val(Json::objectValue);
  // Report the effective (clamped) cap actually used for sampling, not the raw
  // configured value, so the metadata matches what the fingerprint reflects.
  val["cold_cap"] = (Json::UInt64)cold_cap_bound;
  val["segments"] = std::move(segments);
  return val;
}

Json::Value get_threads_stats() {
  Json::Value d;
  d["used"] = (Json::UInt64)redex_parallel::default_num_threads();
  d["hardware"] = (Json::UInt64)boost::thread::hardware_concurrency();
  d["physical"] = (Json::UInt64)boost::thread::physical_concurrency();
  return d;
}

void write_debug_line_mapping(
    const std::string& debug_line_map_filename,
    const UnorderedMap<DexMethod*, uint64_t>& method_to_id,
    const UnorderedMap<DexCode*, std::vector<DebugLineItem>>& code_debug_lines,
    DexStoresVector& stores,
    const std::vector<DexMethod*>& needs_debug_line_mapping) {
  /*
   * Binary file format:
   * magic number 0xfaceb000 (4 byte)
   * version number (4 byte)
   * number (m) of methods that has debug line info (4 byte)
   * a list (m elements) of:
   *   [ encoded method-id (8 byte), method debug info byte offset (4 byte),
   *     method debug info byte size (4 byte) ]
   *
   * a list (m elements) of :
   *   encoded method-id (8 byte)
   *   a list (n elements) of:
   *     [ memory offset (4 byte), line number (4 byte) ]
   */
  size_t bit_32_size = sizeof(uint32_t);
  size_t bit_64_size = sizeof(uint64_t);
  uint32_t num_method = static_cast<uint32_t>(code_debug_lines.size());
  uint32_t offset = num_method + 2;
  // Start of debug line info information would be after all of
  // method-id => offset info, so set the start of offset to be after that.
  uint32_t binary_offset = static_cast<uint32_t>(
      3 * bit_32_size + (bit_64_size + 2 * bit_32_size) * num_method);
  std::ofstream ofs(debug_line_map_filename.c_str(),
                    std::ofstream::out | std::ofstream::trunc);
  uint32_t magic = 0xfaceb000; // serves as endianess check
  ofs.write(reinterpret_cast<const char*>(&magic),
            static_cast<std::streamsize>(bit_32_size));
  uint32_t version = 1;
  ofs.write(reinterpret_cast<const char*>(&version),
            static_cast<std::streamsize>(bit_32_size));
  ofs.write(reinterpret_cast<const char*>(&num_method),
            static_cast<std::streamsize>(bit_32_size));
  std::ostringstream line_out;

  auto scope = build_class_scope(stores);
  std::vector<DexMethod*> all_methods(std::begin(needs_debug_line_mapping),
                                      std::end(needs_debug_line_mapping));
  walk::methods(scope,
                [&](DexMethod* method) { all_methods.push_back(method); });
  std::stable_sort(all_methods.begin(), all_methods.end(), compare_dexmethods);

  for (auto* method : all_methods) {
    auto* dex_code = method->get_dex_code();
    if (dex_code == nullptr ||
        code_debug_lines.find(dex_code) == code_debug_lines.end()) {
      continue;
    }

    uint64_t method_id = method_to_id.at(method);
    // write method id => offset info for binary file
    ofs.write(reinterpret_cast<const char*>(&method_id),
              static_cast<std::streamsize>(bit_64_size));
    ofs.write(reinterpret_cast<const char*>(&binary_offset),
              static_cast<std::streamsize>(bit_32_size));

    auto debug_lines = code_debug_lines.at(dex_code);
    uint32_t num_line_info = static_cast<uint32_t>(debug_lines.size());
    offset = offset + 1 + num_line_info;
    uint32_t info_section_size =
        static_cast<uint32_t>(bit_64_size) +
        (num_line_info * 2 * static_cast<uint32_t>(bit_32_size));
    ofs.write(reinterpret_cast<const char*>(&info_section_size),
              static_cast<std::streamsize>(bit_32_size));
    binary_offset = binary_offset + info_section_size;

    // Generate debug line info for binary file.
    line_out.write(reinterpret_cast<const char*>(&method_id),
                   static_cast<std::streamsize>(bit_64_size));
    for (auto it = debug_lines.begin(); it != debug_lines.end(); ++it) {
      line_out.write(reinterpret_cast<const char*>(&it->offset),
                     static_cast<std::streamsize>(bit_32_size));
      line_out.write(reinterpret_cast<const char*>(&it->line),
                     static_cast<std::streamsize>(bit_32_size));
    }
  }
  ofs << line_out.str();
}

std::string get_dex_magic(std::vector<std::string>& dex_files) {
  always_assert_log(!dex_files.empty(), "APK contains no dex file\n");
  // Get dex magic from the first dex file since all dex magic
  // should be consistent within one APK.
  return load_dex_magic_from_dex(
      DexLocation::make_location("dex", dex_files[0]));
}

void dump_keep_reasons(const ConfigFiles& conf,
                       const Arguments& args,
                       const DexStoresVector& stores) {
  if (!args.config.get("dump_keep_reasons", false).asBool()) {
    return;
  }

  std::ofstream ofs(conf.metafile("redex-keep-reasons.txt"));

  auto scope = build_class_scope(stores);
  for (const auto* cls : scope) {
    auto has_keep_reasons = [cls]() {
      if (!cls->rstate.keep_reasons().empty()) {
        return true;
      }
      for (auto* m : cls->get_all_methods()) {
        if (!m->rstate.keep_reasons().empty()) {
          return true;
        }
      }
      for (auto* f : cls->get_all_fields()) {
        if (!f->rstate.keep_reasons().empty()) {
          return true;
        }
      }
      return false;
    };
    if (!has_keep_reasons()) {
      continue;
    }
    auto print_keep_reasons = [&ofs](const auto& reasons, const char* indent) {
      for (const auto* r : UnorderedIterable(reasons)) {
        ofs << indent << "* " << *r << "\n";
      }
    };
    ofs << "Class: " << show_deobfuscated(cls) << "\n";
    print_keep_reasons(cls->rstate.keep_reasons(), " ");

    auto print_list = [&ofs, &print_keep_reasons](const auto& c,
                                                  const char* name) {
      for (const auto* member : c) {
        if (member->rstate.keep_reasons().empty()) {
          continue; // Skip stuff w/o reasons.
        }
        ofs << " " << name << ": " << show_deobfuscated(member) << "\n";
        print_keep_reasons(member->rstate.keep_reasons(), "  ");
      }
    };
    print_list(cls->get_all_fields(), "Field");
    print_list(cls->get_all_methods(), "Method");
  }
}

void process_proguard_rules(
    ConfigFiles& conf,
    const DexStoresVector& stores,
    Scope& scope,
    Scope& external_classes,
    keep_rules::ProguardConfiguration& pg_config,
    bool dump_proguard_lens,
    const keep_rules::proguard_parser::Stats& parser_stats,
    const keep_rules::proguard_parser::Diagnostics& parser_diagnostics,
    size_t blocklisted_rules) {
  bool keep_all_annotation_classes;
  conf.get_json_config().get("keep_all_annotation_classes", true,
                             keep_all_annotation_classes);

  bool record_used_rules;
  conf.get_json_config().get("record_accessed_rules", true, record_used_rules);

  bool unused_rule_abort;
  conf.get_json_config().get("unused_keep_rule_abort", false,
                             unused_rule_abort);
  auto proguard_rule_recorder =
      process_proguard_rules(conf.get_proguard_map(), scope, external_classes,
                             pg_config, keep_all_annotation_classes);
  if (record_used_rules) {
    proguard_rule_recorder.record_accessed_rules(
        conf.metafile("redex-used-proguard-rules.txt"),
        conf.metafile("redex-unused-proguard-rules.txt"));
  }
  if (unused_rule_abort) {
    std::vector<std::string> unused_out;
    for (const keep_rules::KeepSpec* keep_rule :
         UnorderedIterable(proguard_rule_recorder.unused_keep_rules)) {
      unused_out.push_back(keep_rules::show_keep(*keep_rule));
    }
    // Make output deterministic
    if (!unused_out.empty()) {
      std::sort(unused_out.begin(), unused_out.end());
      always_assert_log(false, "%s",
                        [&]() {
                          std::string tmp;
                          for (const auto& s : unused_out) {
                            tmp += s;
                            tmp += " not used\n";
                          }
                          return tmp;
                        }()
                            .c_str());
    }
  }
  if (dump_proguard_lens) {
    redex::dump_proguard_lens_json(
        conf.metafile("redex-proguard-lens-initial.json"),
        stores,
        "initial",
        &pg_config,
        &proguard_rule_recorder,
        &parser_stats,
        &parser_diagnostics,
        blocklisted_rules);
  }
}

void load_library_jars(Arguments& args,
                       Scope& external_classes,
                       const std::set<std::string>& library_jars,
                       const std::string& base_dir) {
  args.entry_data["jars"] = Json::arrayValue;
  if (library_jars.empty()) {
    return;
  }

  auto load = [&](const auto& allowed_fn) {
    for (const auto& library_jar : library_jars) {
      TRACE(MAIN, 1, "LIBRARY JAR: %s", library_jar.c_str());
      if (load_jar_file(DexLocation::make_location("", library_jar),
                        &external_classes, /*attr_hook=*/nullptr, allowed_fn)) {
        auto abs_path = boost::filesystem::absolute(library_jar);
        args.entry_data["jars"].append(abs_path.string());
        continue;
      }

      // Try again with the basedir
      std::string basedir_path = base_dir + "/" + library_jar;
      if (load_jar_file(DexLocation::make_location("", basedir_path),
                        /*classes=*/nullptr, /*attr_hook=*/nullptr,
                        allowed_fn)) {
        args.entry_data["jars"].append(basedir_path);
        continue;
      }

      std::cerr << "error: library jar could not be loaded: " << library_jar
                << '\n';
      _exit(EXIT_FAILURE);
    }
  };

  // We cannot use GlobalConfig here, it is too early.
  JarLoaderConfig jar_conf{};
  if (args.config.isMember("jar_loader")) {
    jar_conf.parse_config(
        JsonWrapper(args.config.get("jar_loader", Json::nullValue)));
  }

  Timer t("Load library jars");

  if (jar_conf.legacy_mode) {
    load(jar_loader::default_duplicate_allow_fn);
  } else {
    load([&](auto* c, auto& jar_name [[maybe_unused]]) {
      auto sv = c->get_name()->str();
      for (const auto& prefix : jar_conf.allowed_prefixes) {
        if (sv.substr(0, prefix.size()) == prefix) {
          return true;
        }
      }
      return false;
    });
  }
}

template <typename C>
void split_string(const std::string& str, C& out) {
  std::istringstream in_stream(str);
  std::string val;
  constexpr char kDelim =
#if IS_WINDOWS
      ';';
#else
      ':';
#endif
  while (std::getline(in_stream, val, kDelim)) {
    out.emplace(val);
  }
}

template <typename C>
std::string to_string(const C& c) {
  std::string ret;
  for (auto& e : c) {
    if (!ret.empty()) {
      ret.append(", ");
    }
    ret.append(e);
  }
  return ret;
}

ProguardConfig load_early_pg_config(ConfigFiles& conf) {
  ProguardConfig pg_conf{};
  if (conf.get_json_config().contains("proguard")) {
    pg_conf.parse_config(
        JsonWrapper(conf.get_json_config().get("proguard", Json::Value())));
  }
  return pg_conf;
}

// Emits `<deobfuscated class name>,<source file>` for every class that carries
// a source file. Must run in the frontend: StripDebugInfoPass clears the source
// file of every class (drop_src_files defaults to true), so the mapping is only
// recoverable at load time.
void dump_class_to_files_map(const std::string& file_path,
                             const DexStoresVector& stores) {
  std::ofstream ofs(file_path, std::ofstream::out | std::ofstream::trunc);
  for (const auto& store : stores) {
    for (const auto& classes : store.get_dexen()) {
      for (const auto* cls : classes) {
        const auto* source_file = cls->get_source_file();
        if (source_file == nullptr) {
          continue;
        }
        auto name = cls->get_deobfuscated_name_or_empty();
        if (name.empty()) {
          name = cls->get_name()->str();
        }
        ofs << name << "," << source_file->str() << '\n';
      }
    }
  }
}

/**
 * Pre processing steps: load dex and configurations
 */
void redex_frontend(ConfigFiles& conf, /* input */
                    Arguments& args, /* inout */
                    keep_rules::ProguardConfiguration& pg_config,
                    DexStoresVector& stores,
                    bool dump_proguard_lens,
                    Json::Value& stats) {
  Timer redex_frontend_timer("Redex_frontend");

  g_redex->load_pointers_cache();

  keep_rules::proguard_parser::Stats parser_stats{};
  keep_rules::proguard_parser::Diagnostics parser_diagnostics{};
  for (const auto& pg_config_path : args.proguard_config_paths) {
    Timer time_pg_parsing("Parsed ProGuard config file");
    parser_stats += keep_rules::proguard_parser::parse_file(
        pg_config_path,
        &pg_config,
        dump_proguard_lens ? &parser_diagnostics : nullptr);
  }

  size_t blocklisted_rules{0};
  {
    // We cannot use GlobalConfig here, it is too early.
    ProguardConfig pg_conf = load_early_pg_config(conf);
    for (const auto& block_rules : pg_conf.blocklist) {
      blocklisted_rules +=
          keep_rules::proguard_parser::remove_blocklisted_rules(block_rules,
                                                                &pg_config);
    }
    if (!pg_conf.disable_default_blocklist) {
      blocklisted_rules +=
          keep_rules::proguard_parser::remove_default_blocklisted_rules(
              &pg_config);
    }

    always_assert(!pg_conf.fail_on_unknown_commands ||
                  parser_stats.unknown_commands == 0);
  }

  // WARNING: No further modifications of pg_config should happen after this
  // call
  // TODO: T148153725: [redex] Better encapsulate ProguardConfiguration
  // construction
  keep_rules::proguard_parser::identify_blanket_native_rules(&pg_config);

  auto ignore_no_keep_rules =
      args.config.get("ignore_no_keep_rules", false).asBool();
  if (pg_config.keep_rules.empty() && !ignore_no_keep_rules) {
    std::cerr << "error: No ProGuard keep rules provided. Redex optimizations "
                 "will not preserve semantics without accurate keep rules."
              << '\n';
    exit(EXIT_FAILURE);
  }

  {
    Json::Value d;
    using u64 = Json::Value::UInt64;
    d["parse_errors"] = (u64)parser_stats.parse_errors;
    d["unknown_tokens"] = (u64)parser_stats.unknown_tokens;
    d["unimplemented"] = (u64)parser_stats.unimplemented;
    d["skipped_if_rules"] = (u64)parser_stats.skipped_if_rules;
    d["unknown_commands"] = (u64)parser_stats.unknown_commands;
    d["ok"] = (u64)(pg_config.ok ? 1 : 0);
    d["blocklisted_rules"] = (u64)blocklisted_rules;
    d["blanket_native_rules"] = (u64)(std::distance(
        pg_config.keep_rules_native_begin.value_or(pg_config.keep_rules.end()),
        pg_config.keep_rules.end()));
    stats["proguard"] = d;
  }

  // Initialize with PG config libraryjars. The parser separated out any list
  // items.
  std::set<std::string> library_jars{pg_config.libraryjars.begin(),
                                     pg_config.libraryjars.end()};
  // For command line jar paths we accept lists delimited with an OS-specific
  // separator.
  for (const auto& jar_path : args.jar_paths) {
    split_string(jar_path, library_jars);
  }
  TRACE(MAIN, 2, "Library jars: %s", to_string(library_jars).c_str());

  DexStore root_store("classes");
  // Only set dex magic to root DexStore since all dex magic
  // should be consistent within one APK.
  root_store.set_dex_magic(get_dex_magic(args.dex_files));
  stores.emplace_back(std::move(root_store));

  const JsonWrapper& json_config = conf.get_json_config();
  dup_classes::read_dup_class_allowlist(json_config);

  run_rethrow_first_aggregate([&]() {
    Timer t("Load classes from dexes");
    dex_stats_t input_totals;
    std::vector<dex_stats_t> input_dexes_stats;
    int input_dex_version = 0;
    int64_t support_dex_version;
    json_config.get("support_dex_version", 35, support_dex_version);
    redex::load_classes_from_dexes_and_metadata(
        args.dex_files, stores, input_totals, input_dexes_stats,
        input_dex_version, static_cast<int>(support_dex_version));
    args.redex_options.input_dex_version = input_dex_version;
    stats["input_stats"] = get_input_stats(input_totals, input_dexes_stats);
  });

  Scope external_classes;
  load_library_jars(args, external_classes, library_jars,
                    pg_config.basedirectory);

  Timer::scope("Deobfuscating dex elements", [&] {
    for (auto& store : stores) {
      apply_deobfuscated_names(store.get_dexen(), conf.get_proguard_map());
    }
  });
  Timer::scope("Writing class to files map", [&] {
    dump_class_to_files_map(conf.metafile(CLASS_TO_FILES_MAP), stores);
  });
  DexStoreClassesIterator it(stores);
  Scope scope = build_class_scope(it);
  Timer::scope("No Optimizations Rules", [&] {
    // this will change rstate of methods
    keep_rules::process_no_optimizations_rules(
        conf.get_no_optimizations_annos(),
        conf.get_no_optimizations_blocklist(), scope);
  });
  Timer::scope("Initializing reachable classes", [&] {
    // init reachable will change rstate of classes, methods and fields
    init_reachable_classes(scope, ReachableClassesConfig(json_config));
  });
  Timer::scope("Processing proguard rules", [&] {
    process_proguard_rules(conf,
                           stores,
                           scope,
                           external_classes,
                           pg_config,
                           dump_proguard_lens,
                           parser_stats,
                           parser_diagnostics,
                           blocklisted_rules);
  });

  TRACE(NATIVE, 2, "Blanket native classes: %zu",
        g_redex->blanket_native_root_classes.size());
  TRACE(NATIVE, 2, "Blanket native methods: %zu",
        g_redex->blanket_native_root_methods.size());

  if (keep_reason::Reason::record_keep_reasons()) {
    dump_keep_reasons(conf, args, stores);
  }
}

// Performa check for resources that must exist for app to behave correctly,
// crash the build if they fail to present.
void check_required_resources(ConfigFiles& conf, bool pre_run) {
  std::vector<std::string> check_required_resources;
  conf.get_json_config().get("check_required_resources", {},
                             check_required_resources);
  if (check_required_resources.empty()) {
    return;
  }

  std::string apk_dir;
  conf.get_json_config().get("apk_dir", "", apk_dir);
  TRACE(MAIN, 1, "Validating resources.");
  auto resources = create_resource_reader(apk_dir);
  auto res_table = resources->load_res_table();
  for (const auto& required_resource : check_required_resources) {
    always_assert_log(res_table->name_to_ids.count(required_resource) != 0,
                      "Required resource %s does not exist in %s apk",
                      required_resource.c_str(),
                      pre_run ? "input" : "final");
  }
}

// Performa final wave of cleanup (i.e. garbage collect unreferenced strings,
// etc) so that this only needs to happen once and not after every resource
// modification.
void finalize_resource_table(ConfigFiles& conf) {
  if (!conf.finalize_resource_table()) {
    return;
  }

  std::string apk_dir;
  conf.get_json_config().get("apk_dir", "", apk_dir);
  if (apk_dir.empty()) {
    return;
  }
  TRACE(MAIN, 1, "Finalizing resource table.");
  auto resources = create_resource_reader(apk_dir);
  auto res_table = resources->load_res_table();
  auto* global_resources_config =
      conf.get_global_config().get_config_by_name<ResourceConfig>("resources");
  res_table->finalize_resource_table(*global_resources_config);
}

void collect_classes_for_full_jsonl(const DexStore& store,
                                    std::vector<Json::Value>* full_map_root) {
  full_map_root->reserve(full_map_root->size() +
                         std::accumulate(store.get_dexen().begin(),
                                         store.get_dexen().end(), 0,
                                         [](size_t acc, const auto& classes) {
                                           return acc + classes.size();
                                         }));

  for (const auto& classes : store.get_dexen()) {
    for (const auto& cls : classes) {
      Json::Value class_entry;
      class_entry["name"] = std::string(cls->get_deobfuscated_name_or_empty());
      class_entry["obfuscated"] = show(cls);
      class_entry["store"] = store.get_name();
      class_entry["original_store"] = cls->get_location()->get_store_name();

      auto collect_members = [](const auto& members) -> Json::Value {
        Json::Value members_entry{Json::ValueType::objectValue};
        for (const auto* member : members) {
          members_entry[std::string(member->get_deobfuscated_name_or_empty())] =
              show(member);
        }
        return members_entry;
      };
      class_entry["ifields"] = collect_members(cls->get_ifields());
      class_entry["sfields"] = collect_members(cls->get_sfields());
      class_entry["dmethods"] = collect_members(cls->get_dmethods());
      class_entry["vmethods"] = collect_members(cls->get_vmethods());

      full_map_root->emplace_back(std::move(class_entry));
    }
  }
}

/**
 * Post processing steps: write dex and collect stats
 */
void redex_backend(ConfigFiles& conf,
                   PassManager& manager,
                   DexStoresVector& stores,
                   Json::Value& stats) {
  Timer redex_backend_timer("Redex_backend");
  const RedexOptions& redex_options = manager.get_redex_options();
  const auto& output_dir = conf.get_outdir();

  // dexvt is enabled either as a redex-all CLI switch (--emit-dexvt, for
  // redex.py direct runs) or via the JSON config key emit_dexvt=true -- the
  // latter lets an app build turn it on through the standard
  // `redex.globals.emit_dexvt=true` path without a bespoke passthrough.
  const bool emit_dexvt = redex_options.emit_dexvt ||
                          conf.get_json_config().get("emit_dexvt", false);

  finalize_resource_table(conf);
  check_required_resources(conf, false);

  // Before the dexvt capture: normalizing disposes and recreates branch
  // targets and gotos, so the code dexvt captures must already be the list
  // IRCode::sync emits.
  bool lower_with_cfg = true;
  conf.get_json_config().get("lower_with_cfg", true, lower_with_cfg);
  if (lower_with_cfg) {
    Timer t("Normalize CFG");
    instruction_lowering::normalize_cfg(stores);
  }

  // dexvt: pre-lowering capture (disasm + per-block SourceBlocks + PGO + xref).
  // Must run before instruction_lowering::run — the CFG is cleared by
  // PassManager before the backend, so the capture rebuilds it per method.
  dexvt::Exporter dexvt_exporter;
  if (emit_dexvt) {
    Timer t("dexvt pre-lowering capture");
    dexvt_exporter.capture_pre_lowering(stores, conf);
  }

  instruction_lowering::Stats instruction_lowering_stats;
  {
    Timer t("Instruction lowering");
    instruction_lowering_stats = instruction_lowering::run(stores, &conf);
  }

  sanitizers::lsan_do_recoverable_leak_check();

  TRACE(MAIN, 1, "Writing out new DexClasses...");
  const JsonWrapper& json_config = conf.get_json_config();

  enhanced_dex_stats_t output_totals;
  std::vector<std::pair<std::string, enhanced_dex_stats_t>> output_dexes_stats;

  const std::string& line_number_map_filename = conf.metafile(LINE_NUMBER_MAP);
  const std::string& debug_line_map_filename = conf.metafile(DEBUG_LINE_MAP);
  const std::string& iodi_metadata_filename = conf.metafile(IODI_METADATA);

  auto dik = redex_options.debug_info_kind;
  bool needs_addresses = dik == DebugInfoKind::NoPositions || is_iodi(dik);

  std::unique_ptr<PositionMapper> pos_mapper(PositionMapper::make(
      dik == DebugInfoKind::NoCustomSymbolication ? ""
                                                  : line_number_map_filename));
  UnorderedMap<DexMethod*, uint64_t> method_to_id;
  UnorderedMap<DexCode*, std::vector<DebugLineItem>> code_debug_lines;

  auto iodi_metadata = [&]() {
    auto val = conf.get_json_config().get("iodi_layer_mode", Json::Value());
    return IODIMetadata(redex_options.min_sdk,
                        val.isNull()
                            ? IODIMetadata::IODILayerMode::kFull
                            : IODIMetadata::parseLayerMode(val.asString()));
  }();

  std::set<uint32_t> signatures;

  const bool mem_stats_enabled =
      traceEnabled(STATS, 1) || conf.get_json_config().get("mem_stats", true);
  const bool reset_hwm = conf.get_json_config().get("mem_stats_per_pass", true);

  if (is_iodi(dik)) {
    Timer t("Compute initial IODI metadata");
    ScopedMemStats iodi_mem_stats{mem_stats_enabled, reset_hwm};
    iodi_metadata.mark_methods(stores,
                               dik == DebugInfoKind::InstructionOffsetsLayered);
    iodi_mem_stats.trace_log("Compute initial IODI metadata");
  }

  auto& dex_output_config =
      *conf.get_global_config().get_config_by_name<DexOutputConfig>(
          "dex_output");

  // dexvt needs the authoritative per-class and per-method sizes, both gated
  // off by default. Force them on so output_totals carries the size maps.
  if (emit_dexvt) {
    dex_output_config.write_class_sizes = true;
    dex_output_config.write_method_sizes = true;
  }

  auto string_sort_mode = get_string_sort_mode(conf);

  bool should_preserve_input_dexes =
      conf.get_json_config().get("preserve_input_dexes", false);
  if (should_preserve_input_dexes) {
    TRACE(MAIN, 1, "Skipping writing output dexes as configured");
  } else {
    always_assert(!stores.empty());
    const auto& dex_magic = stores[0].get_dex_magic();
    auto min_sdk = manager.get_redex_options().min_sdk;
    ScopedMemStats wod_mem_stats{mem_stats_enabled, reset_hwm};
    std::vector<Json::Value> full_jsonl;
    constexpr const char* kJsonTimerName =
        "Collecting full-rename-map-json data";
    AccumulatingTimer json_timer{kJsonTimerName};
    for (size_t store_number = 0; store_number < stores.size();
         ++store_number) {
      auto& store = stores[store_number];
      const auto& store_name = store.get_name();
      auto code_sort_mode = get_code_sort_mode(conf, store_name);
      Timer t("Writing optimized dexes");
      for (size_t i = 0; i < store.get_dexen().size(); i++) {
        DexClasses* classes = &store.get_dexen()[i];
        auto gtypes = std::make_shared<GatheredTypes>(classes);

        auto this_dex_stats = write_classes_to_dex(
            redex::get_dex_output_name(output_dir, store, i),
            classes,
            gtypes,
            store_number,
            &store_name,
            i,
            conf,
            pos_mapper.get(),
            redex_options.debug_info_kind,
            needs_addresses ? &method_to_id : nullptr,
            needs_addresses ? &code_debug_lines : nullptr,
            is_iodi(dik) ? &iodi_metadata : nullptr,
            dex_magic,
            dex_output_config,
            min_sdk,
            code_sort_mode,
            string_sort_mode);

        output_totals += this_dex_stats;
        // Remove class sizes here to free up memory.
        this_dex_stats.class_size.clear();
        signatures.insert(
            *reinterpret_cast<uint32_t*>(this_dex_stats.signature));
        output_dexes_stats.emplace_back(store.get_name(),
                                        std::move(this_dex_stats));
      }
      {
        auto timer_scope = json_timer.scope();
        collect_classes_for_full_jsonl(store, &full_jsonl);
      }
    }
    Timer::add_timer(kJsonTimerName, json_timer.get_seconds());
    wod_mem_stats.trace_log("Writing optimized dexes");

    Timer::scope("Writing full rename map JSON", [&] {
      std::ofstream ofs(conf.metafile("redex-full-rename-map.jsonl"));
      // We want this to be JSONL. Unclear why `<<` does this for redex-stats
      // but need extra here.
      Json::StreamWriterBuilder builder;
      builder["indentation"] = "";
      auto writer =
          std::unique_ptr<Json::StreamWriter>(builder.newStreamWriter());
      for (const auto& json : full_jsonl) {
        writer->write(json, &ofs);
        ofs << "\n";
      }
    });
  }

  sanitizers::lsan_do_recoverable_leak_check();

  // dexvt: post-lowering emit. output_totals carries the authoritative
  // per-class and per-method sizes accumulated across dexes.
  if (emit_dexvt) {
    Timer t("dexvt emit");
    // Retry lazy method-profile resolution so the manifest's resolution counts
    // are final. Note: PassManager::set_metric is pass-scoped and must NOT be
    // called here (no active pass in redex_backend); resolution health is
    // reported in the artifact manifest instead (see Exporter::emit).
    conf.process_unresolved_method_profile_lines();
    dexvt_exporter.emit(conf, output_totals, &method_to_id);
  }

  std::vector<DexMethod*> needs_debug_line_mapping;

  Timer::scope("Writing opt decisions data", [&] {
    const Json::Value& opt_decisions_args = json_config["opt_decisions"];
    if (opt_decisions_args.get("enable_logs", false).asBool()) {
      auto opt_decisions_output_path = conf.metafile(OPT_DECISIONS);
      auto opt_data =
          opt_metadata::OptDataMapper::get_instance().serialize_sql();
      {
        std::ofstream opt_data_out(opt_decisions_output_path);
        opt_data_out << opt_data;
      }
    }
  });

  Timer::scope("Writing stats", [&] {
    if (needs_addresses) {
      Timer t2{"Writing debug line mapping"};
      write_debug_line_mapping(debug_line_map_filename, method_to_id,
                               code_debug_lines, stores,
                               needs_debug_line_mapping);
    }
    if (is_iodi(dik)) {
      Timer t2{"Writing IODI metadata"};
      iodi_metadata.write(iodi_metadata_filename, method_to_id);
    }
    Timer::scope("Writing position map", [&] { pos_mapper->write_map(); });
    Timer::scope("Collecting output stats", [&] {
      stats["output_stats"] =
          get_output_stats(output_totals, output_dexes_stats, manager,
                           instruction_lowering_stats, pos_mapper.get());
      if (dex_output_config.emit_class_order_sample) {
        stats["output_stats"]["class_order_sample"] = get_class_order_sample(
            stores, dex_output_config.class_order_sample_cap);
      }
    });
    print_warning_summary();

    if (dex_output_config.write_class_sizes) {
      Timer t2("Writing class sizes");
      // Sort for stability.
      auto keys = unordered_to_ordered_keys(output_totals.class_size,
                                            compare_dexclasses);
      std::ofstream ofs{conf.metafile("redex-class-sizes.csv")};
      for (const auto* c : keys) {
        ofs << c->get_deobfuscated_name_or_empty() << ","
            << output_totals.class_size.at(c) << "\n";
      }
    }
  });
}

void dump_class_method_info_map(const std::string& file_path,
                                DexStoresVector& stores) {
  std::ofstream ofs(file_path, std::ofstream::out | std::ofstream::trunc);

  static const char* header =
      "# This map enumerates all class and method sizes and some properties.\n"
      "# To minimize the size, dex location strings are interned.\n"
      "# Class information is also interned.\n"
      "#\n"
      "# First column can be M, C, and I.\n"
      "# - C => Class index and information\n"
      "# - M => Method information\n"
      "# - I,DEXLOC => Dex location string index\n"
      "#\n"
      "# C,<index>,<obfuscated class name>,<deobfuscated class name>,\n"
      "#   <# of all methods>,<# of all virtual methods>,\n"
      "#   <dex location string index>\n"
      "# M,<class index>,<obfuscated method name>,<deobfuscated method name>,\n"
      "#   <size>,<virtual>,<external>,<concrete>\n"
      "# I,DEXLOC,<index>,<string>";
  ofs << header << '\n';

  auto exclude_class_name = [&](const std::string& full_name) {
    const auto dot_pos = full_name.find('.');
    always_assert(dot_pos != std::string::npos);
    // Return excluding class name and "."
    return full_name.substr(dot_pos + 1);
  };

  auto print = [&](const int cls_idx, const DexMethod* method) {
    ofs << "M," << cls_idx << "," << exclude_class_name(show(method)) << ","
        << exclude_class_name(method->get_fully_deobfuscated_name()) << ","
        << (method->get_dex_code() != nullptr ? method->get_dex_code()->size()
                                              : 0)
        << "," << method->is_virtual() << "," << method->is_external() << ","
        << method->is_concrete() << '\n';
  };

  // Interning
  std::unordered_map<const DexClass*, int /*index*/> class_map;
  std::unordered_map<std::string /*location*/, int /*index*/> dexloc_map;

  walk::classes(build_class_scope(stores), [&](const DexClass* cls) {
    const auto& dexloc = cls->get_location()->get_file_name();
    if (dexloc_map.count(dexloc) == 0u) {
      dexloc_map[dexloc] = static_cast<int>(dexloc_map.size());
      ofs << "I,DEXLOC," << dexloc_map[dexloc] << "," << dexloc << '\n';
    }

    redex_assert(!class_map.count(cls));
    const int cls_idx = (class_map[cls] = static_cast<int>(class_map.size()));
    ofs << "C," << cls_idx << "," << show(cls) << "," << show_deobfuscated(cls)
        << "," << (cls->get_dmethods().size() + cls->get_vmethods().size())
        << "," << cls->get_vmethods().size() << "," << dexloc_map[dexloc]
        << '\n';

    for (auto* dmethod : cls->get_dmethods()) {
      print(cls_idx, dmethod);
    }
    for (auto* vmethod : cls->get_vmethods()) {
      print(cls_idx, vmethod);
    }
  });
}

void dump_string_locales(const std::string& file_path,
                         const std::vector<android::ResTable_config>& configs) {
  std::ofstream ofs(file_path, std::ofstream::out | std::ofstream::trunc);
  ofs << configs_to_string(
      std::set<android::ResTable_config>(configs.begin(), configs.end()));
  ofs.close();
}

void maybe_dump_jemalloc_profile(const char* env_name) {
  auto* dump_path = std::getenv(env_name);
  if (dump_path != nullptr) {
    jemalloc_util::dump(dump_path);
  }
}

void copy_proguard_stats(Json::Value& stats) {
  if (!stats.isMember("proguard")) {
    return;
  }
  if (!stats.isMember("output_stats")) {
    return;
  }
  auto& output = stats["output_stats"];
  if (!output.isMember("pass_stats")) {
    return;
  }
  auto& passes = output["pass_stats"];

  Json::Value* first_pass = nullptr;
  for (const auto& name : passes.getMemberNames()) {
    auto& pass = passes[name];
    if (first_pass == nullptr || pass["pass_order"].asUInt64() <
                                     (*first_pass)["pass_order"].asUInt64()) {
      first_pass = &pass;
    }
  }

  if (first_pass == nullptr) {
    return;
  }

  auto& pr = stats["proguard"];
  for (const auto& name : pr.getMemberNames()) {
    std::string compound_name = "proguard_" + name;
    (*first_pass)[compound_name] = pr[name];
  }
}

int check_pass_properties(const Arguments& args) {
  using namespace redex_properties;
  // Cannot parse GlobalConfig nor passes, as they may require binding
  // to dex elements. So this looks more complicated than necessary.

  ConfigFiles conf(args.config, args.out_dir);

  PassManagerConfig pmc;
  if (conf.get_json_config().contains("pass_manager")) {
    pmc.parse_config(JsonWrapper(conf.get_json_config().get(
        "pass_manager", (Json::Value)Json::nullValue)));
  }

  if (!pmc.check_pass_order_properties &&
      args.properties_check_allow_disabled) {
    std::cout << "Properties checks are disabled, skipping." << '\n';
    return 0;
  }

  auto const& all_passes = PassRegistry::get().get_passes();
  auto props_manager =
      Manager(conf, PropertyCheckerRegistry::get().get_checkers());
  auto active_passes =
      PassManager::compute_activated_passes(all_passes, conf, &pmc);

  std::vector<std::pair<std::string, PropertyInteractions>> pass_interactions;
  for (const auto& [pass, _] : active_passes.activated_passes) {
    auto m = pass->get_property_interactions();
    unordered_erase_if(m, [pass_ = pass, &props_manager](auto& p) {
      auto&& [name, property_interaction] = p;

      if (!props_manager.property_is_enabled(name)) {
        return true;
      }

      always_assert_log(property_interaction.is_valid(),
                        "%s has an invalid property interaction for %s",
                        pass_->name().c_str(), get_name(name));
      return false;
    });
    pass_interactions.emplace_back(pass->name(), std::move(m));
  }
  auto failure = Manager::verify_pass_interactions(pass_interactions, conf);
  if (failure) {
    std::cerr << "Illegal pass order:\n" << *failure << '\n';
    return 1;
  }
  return 0;
}

} // namespace

// NOLINTNEXTLINE(bugprone-exception-escape)
int main(int argc, char* argv[]) {
  // Start chrome tracing as early as possible so the epoch predates all
  // timers. Will be disabled after argument parsing if --chrome-trace
  // was not requested.
  ChromeTraceWriter::init();

  signal(SIGABRT, debug_backtrace_handler);
  signal(SIGINT, debug_backtrace_handler);
  signal(SIGSEGV, crash_backtrace_handler);
#if !IS_WINDOWS
  signal(SIGBUS, crash_backtrace_handler);
#endif

  // Only log one assert.
  block_multi_asserts(/*block=*/true);
  // For better stacks in abort dumps.
  set_abort_if_not_this_thread();

  // For Breadcrumbs issues, do not throw, do not print stack trace. Improves
  // error readability.
  redex_debug::set_exc_type_as_abort(RedexError::REJECTED_CODING_PATTERN);
  redex_debug::disable_stack_trace_for_exc_type(
      RedexError::REJECTED_CODING_PATTERN);

  // Duplicate classes in the input are an input error, not a Redex crash.
  redex_debug::set_exc_type_as_abort(RedexError::DUPLICATE_CLASSES);
  redex_debug::disable_stack_trace_for_exc_type(RedexError::DUPLICATE_CLASSES);

  // Input type check issues are a straight issue, not a Redex crash.
  redex_debug::set_exc_type_as_abort(RedexError::TYPE_CHECK_ERROR);
  redex_debug::disable_stack_trace_for_exc_type(RedexError::TYPE_CHECK_ERROR);
  redex_debug::set_exc_type_as_abort(RedexError::TYPEDEF_ANNO_CHECKER_ERROR);
  redex_debug::disable_stack_trace_for_exc_type(
      RedexError::TYPEDEF_ANNO_CHECKER_ERROR);

  auto maybe_global_profile =
      ScopedCommandProfiling::maybe_from_env("GLOBAL_", "global");

  ConcurrentContainerConcurrentDestructionScope
      concurrent_container_destruction_scope;

  std::string stats_output_path;
  std::optional<std::string> chrome_trace_path;
  bool chrome_trace_enabled{false};
  Json::Value stats;
  double cpu_time_s;

  CrashFile crash_file;
  {
    Timer redex_all_main_timer("redex-all main()");

    g_redex = new RedexContext();

    // Currently there are two sources that specify the library jars:
    // 1. The jar_path argument, which may specify one library jar.
    // 2. The library_jars vector, which lists the library jars specified in
    //    the ProGuard configuration.
    // If -jarpath specified a library jar it is appended to the
    // library_jars vector so this vector can be used to iterate over
    // all the library jars regardless of whether they were specified
    // on the command line or ProGuard file.
    // TODO: Make the command line -jarpath option like a colon separated
    //       list of library JARS.
    Arguments args = parse_args(argc, argv);

    if (args.chrome_trace) {
      chrome_trace_enabled = true;
    } else {
      ChromeTraceWriter::disable();
    }

    if (args.crash_file) {
      set_crash_fd(crash_file.open(*args.crash_file));
    }

    if (args.properties_check) {
      int ret = check_pass_properties(args);
      crash_file.set_ok();
      return ret;
    }

    keep_reason::Reason::set_record_keep_reasons(
        args.config.get("record_keep_reasons", false).asBool());

    constant_propagation::enable_check_cast_value_preservation =
        args.config.get("enable_check_cast_value_preservation", false).asBool();

    // TODO(T275196808): Remove this.
    constant_propagation::enable_param_exit_value_summary =
        args.config.get("enable_param_exit_value_summary", false).asBool();

    // For convenience.
    g_redex->instrument_mode = args.redex_options.instrument_pass_enabled;
    if (g_redex->instrument_mode) {
      IRList::CONSECUTIVE_STYLE = IRList::ConsecutiveStyle::kChain;
    }
    {
      auto consecutive_val =
          args.config.get("sb_consecutive_style", Json::nullValue);
      if (consecutive_val.isString()) {
        auto str = consecutive_val.asString();
        IRList::CONSECUTIVE_STYLE = [&]() {
          if (str == "drop") {
            return IRList::ConsecutiveStyle::kDrop;
          } else if (str == "chain") {
            return IRList::ConsecutiveStyle::kChain;
          } else if (str == "max") {
            return IRList::ConsecutiveStyle::kMax;
          } else {
            not_reached_log("Unknown sb_consecutive_style %s", str.c_str());
          }
        }();
      }
    }

    slow_invariants_debug =
        args.config.get("slow_invariants_debug", false).asBool();
    g_redex->slow_invariants_debug = slow_invariants_debug;
    g_redex->insert_remarks = args.config.get("insert_remarks", false).asBool();
    cfg::ControlFlowGraph::s_DEBUG =
        cfg::ControlFlowGraph::s_DEBUG || slow_invariants_debug;
    if (slow_invariants_debug) {
      std::cerr << "Slow invariants enabled." << '\n';
    }

    auto pg_config = std::make_unique<keep_rules::ProguardConfiguration>();
    DexStoresVector stores;
    ConfigFiles conf(args.config, args.out_dir);

    {
      // We cannot use GlobalConfig here, it is too early.
      ProguardConfig pg_conf = load_early_pg_config(conf);
      if (!pg_conf.frozen_basedirectory.empty()) {
        pg_config->basedirectory = pg_conf.frozen_basedirectory;
        pg_config->frozen_basedirectory = true;
      }
    }

    std::string apk_dir;
    conf.get_json_config().get("apk_dir", "", apk_dir);
    auto resources = create_resource_reader(apk_dir);
    auto maybe_sdk = resources->get_min_sdk();
    if (maybe_sdk != std::nullopt) {
      TRACE(MAIN, 2, "parsed minSdkVersion = %d", *maybe_sdk);
      args.redex_options.min_sdk = *maybe_sdk;
    }
    // Allow overriding min_sdk from config.
    {
      int64_t min_sdk_override;
      conf.get_json_config().get("min_sdk_override", 0, min_sdk_override);
      if (min_sdk_override > 0) {
        args.redex_options.min_sdk = (int32_t)min_sdk_override;
        TRACE(MAIN, 0, "Overriding minSdkVersion = %d",
              args.redex_options.min_sdk);
      }
    }

    bool dump_proguard_lens =
        args.config.get("dump_proguard_lens", false).asBool();

    {
      auto profile_frontend =
          ScopedCommandProfiling::maybe_from_env("FRONTEND_", "frontend");
      redex_frontend(conf, args, *pg_config, stores, dump_proguard_lens, stats);
      conf.parse_global_config();
      if (args.redex_options.instrument_pass_enabled) {
        auto* global_resources_config =
            conf.get_global_config().get_config_by_name<ResourceConfig>(
                "resources");
        global_resources_config->cleanup_r_class_rewriting = false;
      }
      maybe_dump_jemalloc_profile("MALLOC_PROFILE_DUMP_FRONTEND");
    }

    g_redex->disable_violation_fixes = conf.disable_violation_fixes();
    g_redex->preserve_count_integrity = conf.preserve_count_integrity();

    if (conf.evaluate_package_name()) {
      args.redex_options.package_name = resources->get_manifest_package_name();
      if (args.redex_options.package_name != std::nullopt) {
        const auto* name_str = args.redex_options.package_name->c_str();
        TRACE(MAIN, 2, "Package name '%s' will be evaluated", name_str);
      }
    }

    check_required_resources(conf, true);

    // Verify that areEqual has the expected semantics (delegates to
    // first.equals(second)) before allowing the swap optimization. This must
    // happen after redex_frontend (which loads dex files and creates method
    // refs) and before any parallel walk, because reading areEqual's IRCode
    // is not thread-safe. An input in which areEqual is neither defined nor
    // referenced has nothing to rewrite, so there is nothing to verify.
    if (method::kotlin_jvm_internal_Intrinsics_areEqual() != nullptr) {
      auto err = constant_propagation::verify_areequal_semantics();
      always_assert_log(!err.has_value(),
                        "Intrinsics.areEqual does not match what the areEqual "
                        "rewrite expects: %s",
                        err->c_str());
    }

    auto const& passes = PassRegistry::get().get_passes();
    auto props_manager = redex_properties::Manager(
        conf, redex_properties::PropertyCheckerRegistry::get().get_checkers());
    PassManager manager(passes, std::move(pg_config), conf, args.redex_options,
                        &props_manager);

    Timer::scope("Running optimization passes", [&] {
      manager.run_passes(stores, conf);
      maybe_dump_jemalloc_profile("MALLOC_PROFILE_DUMP_AFTER_ALL_PASSES");
    });

    if (dump_proguard_lens) {
      redex::dump_proguard_lens_json(
          conf.metafile("redex-proguard-lens-final.json"), stores, "final");
    }

    if (args.stop_pass_idx == std::nullopt) {
      // Call redex_backend by default
      auto profile_backend =
          ScopedCommandProfiling::maybe_from_env("BACKEND_", "backend");
      redex_backend(conf, manager, stores, stats);
      if (args.config.get("emit_class_method_info_map", false).asBool()) {
        dump_class_method_info_map(conf.metafile(CLASS_METHOD_INFO_MAP),
                                   stores);
      }
    } else {
      redex::write_all_intermediate(conf, args.out_dir, args.redex_options,
                                    stores, args.entry_data);
    }
    maybe_dump_jemalloc_profile("MALLOC_PROFILE_DUMP_BACKEND");

    stats_output_path = conf.metafile(
        args.config.get("stats_output", "redex-stats.txt").asString());

    if (chrome_trace_enabled) {
      chrome_trace_path = conf.metafile("redex-chrome-trace.json");
    }

    const bool dump_strings =
        args.config.get("dump-string-locales", false).asBool();
    if (dump_strings) {
      auto post_resources = create_resource_reader(apk_dir);
      auto post_res_table = post_resources->load_res_table();
      std::vector<android::ResTable_config> configs;
      post_res_table->get_configurations(APPLICATION_PACKAGE, "string",
                                         &configs);
      dump_string_locales(conf.metafile(STRING_LOCALE_DUMP), configs);
    }

    Timer::scope("Freeing global memory", [&] { delete g_redex; });
    cpu_time_s = ((double)std::clock()) / CLOCKS_PER_SEC;
  }
  // now that all the timers are done running, we can collect the data
  stats["output_stats"]["time_stats"] = get_times(cpu_time_s);

  auto vm_stats = get_mem_stats();
  stats["output_stats"]["mem_stats"]["vm_peak"] =
      (Json::UInt64)vm_stats.vm_peak;
  stats["output_stats"]["mem_stats"]["vm_hwm"] = (Json::UInt64)vm_stats.vm_hwm;

  stats["output_stats"]["threads"] = get_threads_stats();

  stats["output_stats"]["build_cfg_counter"] = (Json::UInt64)build_cfg_counter;
  // For the time being, copy proguard stats, if any, to the first pass.
  copy_proguard_stats(stats);

  {
    std::ofstream out(stats_output_path);
    out << stats;
  }

  if (chrome_trace_path) {
    ChromeTraceWriter::write(*chrome_trace_path);
  }

  TRACE(MAIN, 1, "Done.");
  if (traceEnabled(MAIN, 1) || traceEnabled(STATS, 1)) {
    TRACE(STATS, 0, "Memory stats: VmPeak=%s VmHWM=%s",
          pretty_bytes(vm_stats.vm_peak).c_str(),
          pretty_bytes(vm_stats.vm_hwm).c_str());
  }

  redex_thread_pool::ThreadPool::destroy();

  malloc_debug::set_shutdown();

  crash_file.set_ok();

  return 0;
}
