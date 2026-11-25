/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include <array>
#include <bitset>
#include <fstream>
#include <span>
#include <sstream>
#include <stdexcept>
#include <thread>
#include <utility>

#include "Creators.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexDefs.h"
#include "DexLoader.h"
#include "DexOutput.h"
#include "DexPosition.h"
#include "DexUtil.h"
#include "IODIMetadata.h"
#include "IRAssembler.h"
#include "InstructionLowering.h"
#include "RedexContext.h"
#include "RedexOptions.h"
#include "RedexTestUtils.h"
#include "Show.h"
#include "TypeUtil.h"
#include "Walkers.h"

using namespace std::literals::string_literals;

struct DexOutputTestHelper {
  // Valid only while `output` is alive: the bytes belong to the DexOutput and
  // are released with it, so they cannot be detached from it.
  static std::span<const uint8_t> output_bytes(const DexOutput& output) {
    return {output.m_output.get(), output.m_offset};
  }
};

namespace {

class IODITest : public ::testing::Test {
 public:
  void reset_redex() {
    if (g_redex != nullptr) {
      delete g_redex;
    }
    g_redex = new RedexContext();
  }

  using MidMap = UnorderedMap<std::string, uint64_t>;

  DexClasses run_redex(MidMap* mids = nullptr,
                       std::string* iodi_data = nullptr,
                       bool iodi_layers = false,
                       bool phased = false,
                       std::vector<uint8_t>* dex_bytes = nullptr) {
    reset_redex();
    const char* dexfile = std::getenv("dexfile");
    EXPECT_NE(nullptr, dexfile);
    std::vector<DexStore> stores;
    DexMetadata dm;
    dm.set_id("classes");
    DexStore root_store(dm);
    root_store.add_classes(
        load_classes_from_dex(DexLocation::make_location("dex", dexfile)));
    stores.emplace_back(std::move(root_store));

    instruction_lowering::normalize_cfg(stores);
    instruction_lowering::run(stores);

    std::unique_ptr<PositionMapper> pos_mapper(PositionMapper::make("tmp"));
    UnorderedMap<DexMethod*, uint64_t> method_to_id;
    UnorderedMap<DexCode*, std::vector<DebugLineItem>> code_debug_lines;
    IODIMetadata iodi_metadata;
    iodi_metadata.mark_methods(stores, iodi_layers);

    Json::Value conf_obj = Json::nullValue;
    ConfigFiles dummy_cfg(conf_obj);

    auto& store = only(stores);
    auto& dexen = store.get_dexen();
    always_assert(dexen.size() == 1);

    auto gtypes = std::make_shared<GatheredTypes>(dexen.data());
    DexOutput output("tmp.dex", /* filename */
                     dexen.data(),
                     std::move(gtypes),
                     false, /* normal_primary_dex */
                     0,
                     nullptr, /* store name */
                     0,
                     iodi_layers ? DebugInfoKind::InstructionOffsetsLayered
                                 : DebugInfoKind::InstructionOffsets,
                     &iodi_metadata,
                     dummy_cfg,
                     pos_mapper.get(),
                     &method_to_id,
                     &code_debug_lines);
    if (phased) {
      output.prepare_without_debug(SortMode::DEFAULT, {SortMode::DEFAULT},
                                   dummy_cfg, "dex\n035\0"s);
      output.finalize_debug_and_header();
    } else {
      output.prepare(SortMode::DEFAULT, {SortMode::DEFAULT}, dummy_cfg,
                     "dex\n035\0"s);
    }
    if (dex_bytes != nullptr) {
      auto bytes = DexOutputTestHelper::output_bytes(output);
      dex_bytes->assign(bytes.begin(), bytes.end());
    }
    if (mids != nullptr) {
      for (auto& iter : UnorderedIterable(method_to_id)) {
        DexMethod* method = iter.first;
        redex_assert(CONSTP(method)->get_dex_code() != nullptr);
        redex_assert(CONSTP(method)->get_dex_code()->get_debug_item() !=
                     nullptr);
        mids->emplace(show(method), iter.second);
      }
    }
    if (iodi_data != nullptr) {
      std::stringstream sstream;
      iodi_metadata.write(sstream, method_to_id);
      *iodi_data = sstream.str();
    }
    reset_redex();
    auto data = DexOutputTestHelper::output_bytes(output);
    auto result =
        load_classes_from_dex(reinterpret_cast<const dex_header*>(data.data()),
                              DexLocation::make_location("", "tmp.dex"),
                              /*balloon=*/false);
    return result;
  }

  struct OutputSnapshot {
    std::vector<std::vector<uint8_t>> dexes;
    std::string positions;
    std::string iodi;
  };

  OutputSnapshot emit_multi_dex(bool parallel,
                                DebugInfoKind kind,
                                SortMode code_mode,
                                bool compression_conscious = true,
                                size_t batch_size = 4,
                                bool use_single_dex_api = false,
                                bool load_method_profile = true) {
    reset_redex();
    auto temp = redex::make_tmp_dir("parallel-dex-test-%%%%-%%%%");
    redex::create_directories(temp.path + "/meta");
    const auto map_path = temp.path + "/positions";
    // Isolate writer concurrency from the loader's lazy-index cache races.
    auto input = load_classes_from_dex(
        DexLocation::make_location("dex", std::getenv("dexfile")),
        /*stats=*/nullptr, /*input_dex_version=*/nullptr, /*balloon=*/true,
        /*throw_on_balloon_error=*/true, /*support_dex_version=*/35,
        DexLoader::Parallel::kNo);
    input.reserve(input.size() + 6);
    for (size_t helper = 0; helper < 6; ++helper) {
      const auto type_name = "LGreedyHelper" + std::to_string(helper) + ";";
      ClassCreator creator(DexType::make_type(type_name));
      creator.set_super(type::java_lang_Object());
      auto* base = DexMethod::make_method(type_name + ".base:()I")
                       ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
      base->set_code(
          assembler::ircode_from_string("((const v0 1) (return v0))"));
      creator.add_method(base);
      // Repeat each body pattern eight times so CC retains distinguishing
      // k-mers.
      for (size_t i = 0; i < 32; ++i) {
        const auto method_name = type_name + ".m" + std::to_string(i) + ":()I";
        auto* method = DexMethod::make_method(method_name)
                           ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
        method->set_code(assembler::ircode_from_string(
            "((.pos \"" + method_name +
            "\" \"ParallelDexTest.java\" \"1\") "
            "(const v3 " +
            std::to_string((helper * 4 + i / 8) / 2 + 1) +
            ") "
            "(add-int/lit v3 v3 7) (mul-int/lit v3 v3 3) "
            "(const v0 " +
            std::to_string(helper * 4 + i / 8 + 1) +
            ") (add-int v0 v0 v3) "
            "(.try_start a) "
            "(invoke-static () \"LGreedyHelper0;.base:()I\") "
            "(move-result v1) (.try_end a) "
            "(add-int v0 v0 v1) (if-eqz v0 :zero) (return v0) "
            "(:zero) (const v0 0) (return v0) "
            "(.catch (a) \"Ljava/lang/Exception;\") "
            "(move-exception v2) (const v0 -1) (return v0))"));
        creator.add_method(method);
      }
      input.push_back(creator.create());
    }
    DexStore store("classes");
    std::vector<DexClasses> partitions(3);
    for (size_t i = 0; i < input.size(); ++i) {
      partitions[i % partitions.size()].push_back(input[i]);
    }
    for (auto& partition : partitions) {
      store.add_classes(std::move(partition));
    }
    DexStoresVector stores;
    stores.emplace_back(std::move(store));
    instruction_lowering::normalize_cfg(stores);
    instruction_lowering::run(stores);
    Json::Value json_config(Json::objectValue);
    json_config["method_similarity_order"]["disable"] = false;
    json_config["method_similarity_order"]["use_compression_conscious_order"] =
        compression_conscious;
    if (code_mode == SortMode::METHOD_PROFILED_ORDER && load_method_profile) {
      const auto profile_path = temp.path + "/methods.csv";
      std::ofstream profile(profile_path);
      profile << "interaction,appear#\nColdStart,100\n"
                 "index,name,appear100,appear#,avg_call,avg_order,"
                 "avg_rank100,min_api_level\n";
      for (size_t i = 0; i < 6; ++i) {
        profile << i << ",LGreedyHelper" << i
                << ";.m31:()I,100,100,10,0,0,21\n";
      }
      profile.close();
      json_config["agg_method_stats_files"] = Json::Value(Json::arrayValue);
      json_config["agg_method_stats_files"].append(profile_path);
    }
    const char* const mode_name = [&]() {
      switch (code_mode) {
      case SortMode::METHOD_SIMILARITY:
        return "method_similarity_order";
      case SortMode::METHOD_COLDSTART_ORDER:
        return "method_coldstart_order";
      case SortMode::METHOD_PROFILED_ORDER:
        return "method_profiled_order";
      case SortMode::CLASS_ORDER:
        return "class_order";
      case SortMode::CLINIT_FIRST:
        return "clinit_order";
      case SortMode::CLASS_STRINGS:
      case SortMode::DEFAULT:
        return "default";
      }
      not_reached();
    }();
    json_config["bytecode_sort_mode"] = mode_name;
    ConfigFiles config(json_config, temp.path);
    config.parse_global_config();
    std::unique_ptr<PositionMapper> mapper(PositionMapper::make(map_path));
    UnorderedMap<DexMethod*, uint64_t> method_to_id;
    UnorderedMap<DexCode*, std::vector<DebugLineItem>> debug_lines;
    IODIMetadata metadata;
    if (::is_iodi(kind)) {
      metadata.mark_methods(stores,
                            kind == DebugInfoKind::InstructionOffsetsLayered);
    }
    auto& root = only(stores);
    auto& dexen = root.get_dexen();
    for (const auto& dex : dexen) {
      size_t coded_methods = 0;
      size_t coded_classes = 0;
      for (auto* cls : dex) {
        bool has_code = false;
        for (auto* method : cls->get_dmethods()) {
          if (method->get_code() != nullptr ||
              method->get_dex_code() != nullptr) {
            ++coded_methods;
            has_code = true;
          }
        }
        for (auto* method : cls->get_vmethods()) {
          if (method->get_code() != nullptr ||
              method->get_dex_code() != nullptr) {
            ++coded_methods;
            has_code = true;
          }
        }
        if (has_code) {
          ++coded_classes;
        }
      }
      always_assert_log(coded_methods >= 64 && coded_classes >= 2,
                        "Each test dex must contain at least 64 coded methods "
                        "across multiple classes");
    }
    std::vector<std::string> filenames(dexen.size());
    for (size_t i = 0; i < dexen.size(); ++i) {
      filenames[i] = temp.path + "/" + dex_name(root, i);
    }
    DexOutputConfig options;
    options.parallel_dex_writing = parallel;
    options.parallel_dex_writing_max_batch_size =
        static_cast<int64_t>(batch_size);
    const auto dex_magic = "dex\n035\0"s;
    DexWritingContext context{.output_dir = temp.path,
                              .dex_magic = dex_magic,
                              .config = config,
                              .position_mapper = mapper.get(),
                              .debug_info_kind = kind,
                              .method_to_id = &method_to_id,
                              .code_debug_lines = &debug_lines,
                              .iodi_metadata =
                                  ::is_iodi(kind) ? &metadata : nullptr,
                              .dex_output_config = options,
                              .min_sdk = 0};
    if (use_single_dex_api) {
      for (size_t i = 0; i < dexen.size(); ++i) {
        write_classes_to_dex(filenames[i], &dexen[i],
                             std::make_shared<GatheredTypes>(&dexen[i]), 0,
                             &root.get_name(), i, config, mapper.get(), kind,
                             &method_to_id, &debug_lines, context.iodi_metadata,
                             dex_magic, options, 0, {code_mode});
      }
    } else {
      const auto caller = std::this_thread::get_id();
      size_t callbacks = 0;
      write_classes_to_multiple_dexes(
          root, 0, context, [&](enhanced_dex_stats_t stats) {
            EXPECT_EQ(std::this_thread::get_id(), caller);
            ASSERT_LT(callbacks, filenames.size());
            EXPECT_EQ(redex::file_size(filenames[callbacks]), stats.num_bytes);
            std::ifstream dex_file(filenames[callbacks], std::ios::binary);
            std::array<uint8_t, 20> signature;
            dex_file.seekg(12);
            dex_file.read(reinterpret_cast<char*>(signature.data()),
                          sizeof(signature));
            ASSERT_TRUE(dex_file);
            EXPECT_TRUE(std::equal(signature.begin(), signature.end(),
                                   stats.signature));
            ++callbacks;
          });
      EXPECT_EQ(callbacks, dexen.size());
    }
    OutputSnapshot result;
    result.dexes.reserve(filenames.size());
    for (const auto& filename : filenames) {
      std::ifstream dex_file(filename, std::ios::binary);
      always_assert(dex_file);
      const std::string bytes(std::istreambuf_iterator<char>(dex_file), {});
      result.dexes.emplace_back(bytes.begin(), bytes.end());
    }
    mapper->write_map();
    std::ifstream positions(map_path, std::ios::binary);
    result.positions.assign(std::istreambuf_iterator<char>(positions), {});
    if (::is_iodi(kind)) {
      std::ostringstream stream;
      metadata.write(stream, method_to_id);
      result.iodi = stream.str();
    }
    return result;
  }

  static bool is_layered_iodi(const DexDebugItem& debug_item) {
    const auto line_start = debug_item.get_line_start();
    return (line_start & DexOutput::kIODILayerMask) != 0;
  }

  static bool is_plain_or_iodi_plain(const DexDebugItem& debug_item) {
    return (debug_item.get_line_start() & DexOutput::kIODIDataMask) != 0;
  }

  static bool is_iodi(const DexDebugItem& debug_item) {
    bool iodi_layered{is_layered_iodi(debug_item)};
    if (iodi_layered) {
      return true;
    }

    if (debug_item.get_line_start() != 0) {
      return false;
    }

    const auto& entries = debug_item.get_entries();
    for (size_t i = 0; i < entries.size(); i++) {
      const auto& entry = entries[i];
      // IODI emits only DBG_FIRST_SPECIAL opcodes.
      // If we see anything else, its not IODI.
      if (entry.type != DexDebugEntryType::Position) {
        return false;
      }
      auto line = entry.pos->line;
      if ((line & DexOutput::kIODILayerMask) != 0) {
        return false;
      }
      line &= DexOutput::kIODIDataMask;
      if (i != entry.addr || i != line) {
        return false;
      }
    }
    return true;
  }

  static std::optional<size_t> get_iodi_layer(const DexDebugItem& debug_item) {
    auto line_start = debug_item.get_line_start();
    if (line_start != 0 && !is_layered_iodi(debug_item)) {
      return std::nullopt;
    }
    return (line_start & DexOutput::kIODILayerMask) >>
           DexOutput::kIODILayerShift;
  }

  static size_t debug_item_line_table_size(const DexDebugItem& debug_item) {
    size_t result = 0;
    const auto& entries = debug_item.get_entries();
    for (const auto& entry : entries) {
      if (entry.type == DexDebugEntryType::Position) {
        result += 1;
      }
    }
    return result;
  }

  struct DexDebugComp {
    bool operator()(const DexDebugItem* lhs, const DexDebugItem* rhs) const {
      if (lhs->get_source_checksum() != rhs->get_source_checksum()) {
        return lhs->get_source_checksum() < rhs->get_source_checksum();
      } else {
        return lhs->get_source_offset() < rhs->get_source_offset();
      }
    }
  };

  using DexMethods = std::vector<DexMethod*>;
  using DexDebugMap = std::map<DexDebugItem*, DexMethods, DexDebugComp>;
  DexDebugMap debug_to_methods(const DexClasses& classes) {
    DexDebugMap result;
    walk::methods(classes, [&](DexMethod* method) {
      DexCode* code = method->get_dex_code();
      if (code == nullptr) {
        return;
      }
      DexDebugItem* debug_item = code->get_debug_item();
      if (debug_item == nullptr) {
        return;
      }
      result[debug_item].push_back(method);
    });
    return result;
  }

  std::string dex_debug_item_to_str(const DexDebugItem& item) {
    std::ostringstream oss;
    oss << "\"positions\" : [\n";
    for (const auto& entry : item.get_entries()) {
      if (entry.type != DexDebugEntryType::Position) {
        continue;
      }
      oss << "    " << entry.addr << " : " << entry.pos->line << " = "
          << std::hex << entry.pos->line << std::dec << ",\n";
    }
    oss << "  ],\n  \"is_iodi\" : "
        << (is_iodi(item) ? "\"true\"" : "\"false\"");
    return oss.str();
  }

#if 0
void log_debug_to_methods(const std::map<void*, DexMethods>& result) {
  for (auto& dtm : result) {
    std::cerr << "{\n  ";
    std::cerr << dex_debug_item_to_str(*(DexDebugItem*)dtm.first);
    std::cerr << ",\n  \"methods\" : [\n";
    for (DexMethod* method : dtm.second) {
      std::cerr << "    \"" << show(method) << "\",\n";
    }
    std::cerr << "  ],\n}\n";
  }
}
#endif

  UnorderedMap<std::string, uint32_t> extract_method_to_debug_size() {
    reset_redex();
    UnorderedMap<std::string, uint32_t> result;
    const char* dexfile = std::getenv("dexfile");
    redex_assert(dexfile);
    auto pre_classes = load_classes_from_dex(
        DexLocation::make_location("", dexfile), /*stats=*/nullptr,
        /*input_dex_version*/ nullptr, false);
    auto pre_debug_data = debug_to_methods(pre_classes);
    for (auto& data : pre_debug_data) {
      EXPECT_EQ(data.second.size(), 1);
      result.emplace(show(data.second[0]),
                     ((DexDebugItem*)data.first)->get_on_disk_size());
    }
    return result;
  }

  struct PCCompare {
    bool operator()(const DexMethod* lhs, const DexMethod* rhs) const {
      if (lhs->get_dex_code()->size() == rhs->get_dex_code()->size()) {
        return (uintptr_t)lhs > (uintptr_t)rhs;
      } else {
        return lhs->get_dex_code()->size() > rhs->get_dex_code()->size();
      }
    }
  };
};

} // namespace

TEST_F(IODITest, ExplicitPreparationPhasesPreserveDexBytes) {
  for (bool layered : {false, true}) {
    std::vector<uint8_t> serial;
    std::vector<uint8_t> phased;
    run_redex(nullptr, nullptr, layered, false, &serial);
    run_redex(nullptr, nullptr, layered, true, &phased);
    ASSERT_FALSE(serial.empty());
    EXPECT_EQ(serial, phased);
  }
}

TEST_F(IODITest, parallelPreparationPreservesMultiDexBytesAndDebugMaps) {
  for (auto kind : {DebugInfoKind::PerMethodDebug, DebugInfoKind::NoPositions,
                    DebugInfoKind::InstructionOffsetsLayered}) {
    for (auto sort : {SortMode::DEFAULT, SortMode::METHOD_COLDSTART_ORDER,
                      SortMode::METHOD_SIMILARITY}) {
      SCOPED_TRACE(static_cast<uint32_t>(kind));
      SCOPED_TRACE(static_cast<uint32_t>(sort));
      const auto serial = emit_multi_dex(false, kind, sort);
      ASSERT_EQ(serial.dexes.size(), 3u);
      ASSERT_FALSE(serial.positions.empty());
      if (::is_iodi(kind)) {
        ASSERT_FALSE(serial.iodi.empty());
      }
      for (size_t repeat = 0; repeat < 3; ++repeat) {
        const auto parallel = emit_multi_dex(
            true, kind, sort, true, repeat == 0 ? 1 : (repeat == 1 ? 2 : 4));
        EXPECT_EQ(serial.dexes, parallel.dexes);
        EXPECT_EQ(serial.positions, parallel.positions);
        EXPECT_EQ(serial.iodi, parallel.iodi);
      }
    }
  }
}

TEST_F(IODITest, parallelGreedyWritingPreservesMultiDexBytesAndDebugMaps) {
  for (auto kind : {DebugInfoKind::PerMethodDebug, DebugInfoKind::NoPositions,
                    DebugInfoKind::InstructionOffsetsLayered}) {
    SCOPED_TRACE(static_cast<uint32_t>(kind));
    const auto serial =
        emit_multi_dex(false, kind, SortMode::METHOD_SIMILARITY, false);
    ASSERT_EQ(serial.dexes.size(), 3u);
    for (size_t repeat = 0; repeat < 3; ++repeat) {
      const auto parallel =
          emit_multi_dex(true, kind, SortMode::METHOD_SIMILARITY, false,
                         repeat == 0 ? 1 : (repeat == 1 ? 2 : 4));
      EXPECT_EQ(serial.dexes, parallel.dexes);
      EXPECT_EQ(serial.positions, parallel.positions);
      EXPECT_EQ(serial.iodi, parallel.iodi);
    }
  }
}

TEST_F(IODITest, multiDexSerialHelperPreservesSingleDexApiOutput) {
  for (bool compression_conscious : {false, true}) {
    const auto kind = DebugInfoKind::InstructionOffsetsLayered;
    const auto old_api =
        emit_multi_dex(false, kind, SortMode::METHOD_SIMILARITY,
                       compression_conscious, 4, true);
    const auto store_api = emit_multi_dex(
        false, kind, SortMode::METHOD_SIMILARITY, compression_conscious);
    EXPECT_EQ(old_api.dexes, store_api.dexes);
    EXPECT_EQ(old_api.positions, store_api.positions);
    EXPECT_EQ(old_api.iodi, store_api.iodi);
  }
}

TEST_F(IODITest, multiDexHelperInitializesColdMethodProfiles) {
  const auto kind = DebugInfoKind::InstructionOffsetsLayered;
  const auto sort = SortMode::METHOD_PROFILED_ORDER;
  const auto without_profile =
      emit_multi_dex(false, kind, sort, true, 4, false, false);
  const auto serial = emit_multi_dex(false, kind, sort);
  EXPECT_NE(without_profile.dexes, serial.dexes);
  for (size_t batch : {1u, 2u, 4u}) {
    const auto parallel = emit_multi_dex(true, kind, sort, true, batch);
    EXPECT_EQ(serial.dexes, parallel.dexes);
    EXPECT_EQ(serial.positions, parallel.positions);
    EXPECT_EQ(serial.iodi, parallel.iodi);
  }
}

TEST_F(IODITest, avoidDexLayoutOOM) {
  // Here we want to test that for each debug program the inflated size in
  // dexlayout on Android 8, 8.1 is bounded by 8k (arbitrary number, yes,
  // but in practice works out)
  auto classes = run_redex();
  auto debug_data = debug_to_methods(classes);
  for (auto& data : debug_data) {
    DexDebugItem* debug_item = (DexDebugItem*)data.first;
    auto& methods = data.second;
    if (!is_iodi(*debug_item)) {
      continue;
    }
    size_t inflated_size =
        debug_item_line_table_size(*debug_item) * data.second.size();
    auto print_methods = [&methods]() {
      std::ostringstream oss;
      for (const auto* m : methods) {
        oss << " " << show(m);
      }
      return oss.str();
    };
    EXPECT_LE(inflated_size, 8 * 1024) << print_methods();
  }
}

// Below will need to compute debug program size (meaning including the
// header)
TEST_F(IODITest, usingIODIWorthIt) {
  // TODO: This will have to load the original line maps and compute
  //       the regular debug sizes to compare. Sometimes using plain
  //       IODI is an improvement, just for line number encoding.
}

// Below will need to compute debug program size (meaning including the
// header)
TEST_F(IODITest, couldIODIBeBetter) {
  auto method_to_pre_debug_size = extract_method_to_debug_size();
  EXPECT_GT(method_to_pre_debug_size.size(), 0);
  auto classes = run_redex();
  auto debug_data = debug_to_methods(classes);
  for (auto& data : debug_data) {
    DexDebugItem* debug_item = (DexDebugItem*)data.first;
    if (!is_iodi(*debug_item)) {
      continue;
    }
    std::set<DexMethod*, PCCompare> methods;
    methods.insert(data.second.begin(), data.second.end());
    EXPECT_EQ(methods.size(), data.second.size());
    if (methods.size() == 1) {
      continue;
    }
    auto next_biggest = methods.begin();
    uint32_t biggest_insns = (*next_biggest)->get_dex_code()->size();
    while ((*next_biggest)->get_dex_code()->size() == biggest_insns &&
           // NOLINTNEXTLINE(bugprone-inc-dec-in-conditions)
           ++next_biggest != methods.end()) {
      ;
    }

    uint32_t total_debug_size = 0;
    for (auto iter = methods.begin(); iter != next_biggest; iter++) {
      auto size_iter = method_to_pre_debug_size.find(show(*iter));
      ASSERT_NE(size_iter, method_to_pre_debug_size.end());
      total_debug_size += size_iter->second;
    }

    if (next_biggest != methods.end()) {
      // Check that removing the biggest method results in growing the binary
      EXPECT_GT(total_debug_size + (*next_biggest)->get_dex_code()->size(),
                biggest_insns);
      for (auto iter = next_biggest; iter != methods.end(); iter++) {
        auto size_iter = method_to_pre_debug_size.find(show(*iter));
        ASSERT_NE(size_iter, method_to_pre_debug_size.end());
        total_debug_size += size_iter->second;
      }
      // Make sure it's worth it to create IODI whatsoever
      EXPECT_GT(total_debug_size, (*next_biggest)->get_dex_code()->size());
    }
  }
}

TEST_F(IODITest, noCrossAritySharing) {
  // In certain lower versions of Android if the arity of a debug item
  // doesn't match the arity of the method pointing to it then symbolication
  // will fail.
  auto classes = run_redex();
  auto debug_data = debug_to_methods(classes);
  for (auto& data : debug_data) {
    DexDebugItem* debug_item = (DexDebugItem*)data.first;
    if (!is_iodi(*debug_item)) {
      continue;
    }
    ASSERT_GT(data.second.size(), 0);
    size_t arity = data.second[0]->get_proto()->get_args()->size();
    for (auto& meth : data.second) {
      EXPECT_EQ(meth->get_proto()->get_args()->size(), arity);
    }
  }
}

TEST_F(IODITest, iodiBigEnough) {
  auto classes = run_redex();
  auto debug_data = debug_to_methods(classes);
  for (auto& data : debug_data) {
    DexDebugItem* debug_item = (DexDebugItem*)data.first;
    if (is_plain_or_iodi_plain(*debug_item)) {
      continue;
    }
    for (DexMethod* method : data.second) {
      EXPECT_GE(debug_item_line_table_size(*debug_item),
                method->get_dex_code()->size())
          << show(method) << "\n"
          << dex_debug_item_to_str(*debug_item);
    }
  }
}

TEST_F(IODITest, someUseIODI) {
  auto classes = run_redex();
  auto debug_data = debug_to_methods(classes);
  uint32_t iodi_count = 0;
  for (auto& data : debug_data) {
    DexDebugItem* debug_item = (DexDebugItem*)data.first;
    if (!is_iodi(*debug_item)) {
      continue;
    }
    iodi_count += 1;
  }
  EXPECT_GT(iodi_count, 0);
}

TEST_F(IODITest, sameNameDontUseIODI) {
  auto classes = run_redex(nullptr, nullptr, /*iodi_layers=*/false);
  size_t same_name_count = 0;
  for (DexClass* cls : classes) {
    UnorderedMap<std::string_view, DexMethods> name_to_methods;
    for (DexMethod* method : cls->get_dmethods()) {
      name_to_methods[method->str()].push_back(method);
    }
    for (DexMethod* method : cls->get_vmethods()) {
      name_to_methods[method->str()].push_back(method);
    }

    for (auto& iter : UnorderedIterable(name_to_methods)) {
      if (iter.second.size() == 1) {
        continue;
      }
      for (DexMethod* method : iter.second) {
        DexCode* code = method->get_dex_code();
        if (code == nullptr) {
          continue;
        }
        DexDebugItem* debug_item = code->get_debug_item();
        if (debug_item == nullptr) {
          continue;
        }
        EXPECT_FALSE(is_iodi(*debug_item));
        same_name_count += 1;
      }
    }
  }
  // <init>, <init>, sameName, sameName, sameName (3x + 1)
  EXPECT_EQ(same_name_count, 12);
}

TEST_F(IODITest, sameNameIODILayered) {
  auto classes = run_redex(nullptr, nullptr, /*iodi_layers=*/true);
  size_t same_name_count = 0;
  for (DexClass* cls : classes) {
    UnorderedMap<std::string_view, DexMethods> name_to_methods;
    for (DexMethod* method : cls->get_dmethods()) {
      name_to_methods[method->str()].push_back(method);
    }
    for (DexMethod* method : cls->get_vmethods()) {
      name_to_methods[method->str()].push_back(method);
    }

    for (auto& iter : UnorderedIterable(name_to_methods)) {
      if (iter.second.size() == 1) {
        continue;
      }
      size_t w_dbg = 0;
      size_t iodi = 0;
      for (DexMethod* method : iter.second) {
        DexCode* code = method->get_dex_code();
        if (code == nullptr) {
          continue;
        }
        DexDebugItem* debug_item = code->get_debug_item();
        if (debug_item == nullptr) {
          continue;
        }
        ++w_dbg;
        iodi += is_iodi(*debug_item) ? 1 : 0;
        same_name_count += 1;
      }
      auto print = [&]() {
        std::ostringstream oss;
        for (DexMethod* method : iter.second) {
          DexCode* code = method->get_dex_code();
          if (code == nullptr) {
            continue;
          }
          DexDebugItem* debug_item = code->get_debug_item();
          if (debug_item == nullptr) {
            continue;
          }
          oss << show(method) << ": " << dex_debug_item_to_str(*debug_item)
              << "\n";
        }
        return oss.str();
      };
      EXPECT_EQ(iodi, w_dbg) << print();
    }
  }
  // <init>, <init>, sameName, sameName, sameName (3x + 1)
  EXPECT_EQ(same_name_count, 12);
}

TEST_F(IODITest, iodiLayers) {
  auto classes = run_redex(nullptr, nullptr, /*iodi_layers=*/true);
  size_t cluster_count{0};
  for (DexClass* cls : classes) {
    UnorderedMap<std::string_view, DexMethods> name_to_methods;
    for (DexMethod* method : cls->get_dmethods()) {
      name_to_methods[method->str()].push_back(method);
    }
    for (DexMethod* method : cls->get_vmethods()) {
      name_to_methods[method->str()].push_back(method);
    }

    for (auto& iter : UnorderedIterable(name_to_methods)) {
      if (iter.second.size() == 1) {
        continue;
      }
      std::bitset<DexOutput::kIODILayerBound + 1> iodi_layers{};
      bool have_non_iodi = false;
      for (DexMethod* method : iter.second) {
        DexCode* code = method->get_dex_code();
        if (code == nullptr) {
          continue;
        }
        DexDebugItem* debug_item = code->get_debug_item();
        if (debug_item == nullptr) {
          continue;
        }

        if (!is_iodi(*debug_item)) {
          have_non_iodi = true;
          EXPECT_FALSE(iodi_layers.test(0));
          continue;
        }

        auto layer = get_iodi_layer(*debug_item);
        ASSERT_TRUE(layer);
        EXPECT_FALSE(iodi_layers.test(*layer))
            << show(method) << ": " << *layer << " @ "
            << debug_item->get_line_start();
        EXPECT_TRUE(*layer != 0 || !have_non_iodi);
        iodi_layers.set(*layer);
      }
      if (iodi_layers.test(1)) {
        ++cluster_count;
      }
    }
  }
  EXPECT_EQ(4u, cluster_count);
}

namespace {
struct IODIParser {
  template <typename T>
  const T* parse(size_t len = sizeof(T)) {
    check_end();
    const T* result = (const T*)cursor;
    cursor += len;
    return result;
  }

  void check_end() {
    if (cursor >= end) {
      throw std::runtime_error("Attempting to parse past end of buffer");
    }
  }

  void ensure_at_end() {
    if (cursor != end) {
      std::string err("Parse error, expected to be at end of buffer. ");
      err += std::to_string(end - cursor) + " unknown bytes";
      throw std::runtime_error(err);
    }
  }

  const uint8_t* cursor;
  const uint8_t* end;
};

class IODIEncodingTest : public IODITest {
 protected:
  void run(bool layered) {
    std::string iodi_data;
    MidMap mids;
    auto classes = run_redex(&mids, &iodi_data, layered);
    EXPECT_GT(mids.size(), 0);
    EXPECT_GT(iodi_data.size(), 0);

    // First verify all methods with IODI are in the method_id map
    auto debug_data = debug_to_methods(classes);
    UnorderedMap<std::string, uint64_t> iodi_mid;
    UnorderedSet<std::string> plain_set;
    for (auto& data : debug_data) {
      DexDebugItem* debug_item = (DexDebugItem*)data.first;
      bool is_plain = is_plain_or_iodi_plain(*debug_item);
      for (DexMethod* method : data.second) {
        std::string pretty_name =
            java_names::internal_to_external(method->get_class()->str());
        pretty_name.push_back('.');
        pretty_name += method->str();
        if (layered) {
          auto layer = get_iodi_layer(*debug_item);
          if (layer) {
            pretty_name =
                IODIMetadata::get_layered_name(std::move(pretty_name), *layer);
          }
        }
        if (is_plain) {
          plain_set.insert(pretty_name);
        } else {
          std::string name = show(method);
          auto iter = mids.find(name);
          ASSERT_NE(iter, mids.end()) << name;
          auto res = iodi_mid.emplace(pretty_name, iter->second);
          ASSERT_TRUE(res.second) << name << " " << pretty_name;
        }
      }
    }

    /*
     * Binary file format
     * {
     *  magic: uint32_t = 0xfaceb001
     *  version: uint32_t = 1
     *  count: uint32_t
     *  zero: uint32_t = 0
     *  entries: entry_t[count]
     * }
     * where
     * entry_t = {
     *  klen: uint16_t
     *  method_id: uint64_t
     *  key: char[klen]
     * }
     */
    auto* buffer = (uint8_t*)iodi_data.data();
    auto buffer_len = iodi_data.size();
    IODIParser p{buffer, buffer + buffer_len};
    struct __attribute__((__packed__)) Header {
      uint32_t magic;
      uint32_t version;
      uint32_t count;
      uint32_t zero;
    };
    // Now verify the resulting metadata file parses correctly
    const Header& hdr = *p.parse<Header>();
    EXPECT_EQ(hdr.magic, 0xfaceb001);
    EXPECT_EQ(hdr.version, 1);
    EXPECT_EQ(hdr.count, iodi_mid.size());
    EXPECT_EQ(hdr.zero, 0);
    struct __attribute__((__packed__)) EntryHeader {
      uint16_t klen;
      uint64_t method_id;
    };
    for (uint32_t i = 0; i < hdr.count; i++) {
      const EntryHeader& entry = *p.parse<EntryHeader>();
      const char* key_c = p.parse<char>(entry.klen);
      auto name = std::string(key_c, entry.klen);
      auto mid_it = iodi_mid.find(name);
      if (mid_it != iodi_mid.end()) {
        EXPECT_EQ(mid_it->second, entry.method_id);
        iodi_mid.erase(name);
      } else {
        EXPECT_NE(mid_it, iodi_mid.end()) << name;
        EXPECT_EQ(0, plain_set.count(name)) << name;
      }
    }
    p.ensure_at_end();
    for (const auto& m : UnorderedIterable(iodi_mid)) {
      EXPECT_TRUE(false) << "Unencoded: " << m.first;
    }
  }
};

} // namespace

TEST_F(IODIEncodingTest, encodedMetadataContainsAllIODI) {
  run(/*layered=*/false);
}

TEST_F(IODIEncodingTest, encodedMetadataContainsAllIODILayered) {
  run(/*layered=*/true);
}
