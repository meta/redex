/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>
#include <json/json.h>

#include "ConfigFiles.h"
#include "Creators.h"
#include "DexPosition.h"
#include "DexUtil.h"
#include "InstructionLowering.h"
#include "RedexTest.h"
#include "Show.h"
#include "Walkers.h"

#include "DexOutput.h"

class DexOutputTest : public RedexIntegrationTest {
 public:
  DexOutputTest() {}

  std::vector<DexMethod*> get_ordered_methods(DexOutput& dout) {
    std::vector<DexMethod*> code_items;
    code_items.reserve(dout.m_code_item_emits.size());
    for (auto& ci : dout.m_code_item_emits) {
      code_items.push_back(ci.method);
    }
    return code_items;
  }
};

TEST_F(DexOutputTest, SplitWritePreservesOpenFailureBehavior) {
  auto temp = redex::make_tmp_dir("dex-write-phase-%%%%-%%%%");
  redex::create_directories(temp.path + "/meta");
  ConfigFiles config(Json::Value(Json::objectValue), temp.path);
  DexClasses empty_classes;
  const std::string store_name("classes");
  const auto filename = temp.path + "/missing/output.dex";
  std::unique_ptr<PositionMapper> mapper(PositionMapper::make(""));
  DexOutput output(filename.c_str(), &empty_classes,
                   std::make_shared<GatheredTypes>(&empty_classes), true, 0,
                   &store_name, 0, DebugInfoKind::NoCustomSymbolication,
                   nullptr, config, mapper.get(), nullptr, nullptr);
  output.prepare(SortMode::DEFAULT, {SortMode::DEFAULT}, config, "dex\n035");
  EXPECT_THROW(output.write_dex(), RedexException);
  EXPECT_THROW(output.write(), RedexException);
  EXPECT_EQ(output.m_stats.num_bytes, 0);
  EXPECT_FALSE(redex::exists(config.metafile("redex-class-rename-map.txt")));
  EXPECT_FALSE(redex::exists(config.metafile("redex-full-rename-map.txt")));
}

TEST_F(DexOutputTest, PreparationValidationHandlesUnnamedStores) {
  ClassCreator parent(DexType::make_type("LPhaseParent;"));
  parent.set_super(DexType::make_type("Ljava/lang/Object;"));
  auto* parent_class = parent.create();
  ClassCreator child(DexType::make_type("LPhaseChild;"));
  child.set_super(parent_class->get_type());
  DexClasses invalid_order{child.create(), parent_class};
  Json::Value json;
  json["enforce_class_order"] = true;
  ConfigFiles config(json);
  std::unique_ptr<PositionMapper> mapper(PositionMapper::make(""));
  DexOutput output("unused.dex", &invalid_order,
                   std::make_shared<GatheredTypes>(&invalid_order), true, 0,
                   nullptr, 0, DebugInfoKind::NoCustomSymbolication, nullptr,
                   config, mapper.get(), nullptr, nullptr);
  EXPECT_THROW(output.prepare_without_debug(
                   SortMode::DEFAULT, {SortMode::DEFAULT}, config, "dex\n035"),
               RedexException);
}

class MultiDexWriterTest : public RedexTest {};

TEST_F(MultiDexWriterTest, MultiDexWriterHandlesEmptyAndSingleDexStores) {
  for (bool parallel : {false, true}) {
    auto temp = redex::make_tmp_dir("multi-dex-boundary-%%%%-%%%%");
    redex::create_directories(temp.path + "/meta");
    ConfigFiles config(Json::Value(Json::objectValue), temp.path);
    config.parse_global_config();
    DexOutputConfig options;
    options.parallel_dex_writing = parallel;
    std::unique_ptr<PositionMapper> mapper(PositionMapper::make(""));
    const std::string magic("dex\n035");
    DexWritingContext context{temp.path,
                              magic,
                              config,
                              mapper.get(),
                              DebugInfoKind::NoCustomSymbolication,
                              nullptr,
                              nullptr,
                              nullptr,
                              options,
                              0};
    DexStore store("classes");
    size_t callbacks = 0;
    auto consume = [&](const enhanced_dex_stats_t& stats) {
      ++callbacks;
      EXPECT_GT(stats.num_bytes, 0);
      EXPECT_EQ(stats.num_bytes,
                redex::file_size(temp.path + "/" + dex_name(store, 0)));
    };
    write_classes_to_multiple_dexes(store, 0, context, consume);
    EXPECT_EQ(callbacks, 0u);
    store.add_classes({});
    write_classes_to_multiple_dexes(store, 0, context, consume);
    EXPECT_EQ(callbacks, 1u);
  }
}

TEST_F(MultiDexWriterTest, MultiDexWriterStopsAfterCallbackFailure) {
  for (bool parallel : {false, true}) {
    auto temp = redex::make_tmp_dir("multi-dex-consumer-%%%%-%%%%");
    redex::create_directories(temp.path + "/meta");
    ConfigFiles config(Json::Value(Json::objectValue), temp.path);
    config.parse_global_config();
    DexOutputConfig options;
    options.parallel_dex_writing = parallel;
    options.parallel_dex_writing_max_batch_size = 1;
    std::unique_ptr<PositionMapper> mapper(PositionMapper::make(""));
    const std::string magic("dex\n035");
    DexWritingContext context{temp.path,
                              magic,
                              config,
                              mapper.get(),
                              DebugInfoKind::NoCustomSymbolication,
                              nullptr,
                              nullptr,
                              nullptr,
                              options,
                              0};
    DexStore store("classes");
    store.add_classes({});
    store.add_classes({});
    size_t callbacks = 0;
    auto consume = [&](const enhanced_dex_stats_t&) {
      ++callbacks;
      throw std::runtime_error("consumer stopped");
    };
    EXPECT_THROW(write_classes_to_multiple_dexes(store, 0, context, consume),
                 std::runtime_error);
    EXPECT_EQ(callbacks, 1u);
    EXPECT_TRUE(redex::exists(temp.path + "/" + dex_name(store, 0)));
    EXPECT_FALSE(redex::exists(temp.path + "/" + dex_name(store, 1)));
  }
}

TEST_F(DexOutputTest, TEST_SIMILARITY_ORDERER) {
  std::vector<SortMode> sort_modes{SortMode::METHOD_PROFILED_ORDER,
                                   SortMode::METHOD_SIMILARITY};

  Json::Value cfg;
  ConfigFiles config_files(cfg);
  config_files.parse_global_config();
  std::unique_ptr<PositionMapper> pos_mapper(PositionMapper::make(""));
  auto scope = build_class_scope(stores);

  // Lower the code
  instruction_lowering::normalize_cfg(stores);
  walk::parallel::methods<>(
      scope, [](DexMethod* m) { instruction_lowering::lower(m); });

  auto gtypes = std::make_shared<GatheredTypes>(&*classes);
  DexOutput dout("", &*classes, std::move(gtypes), true, 0, nullptr, 0,
                 DebugInfoKind::NoCustomSymbolication, nullptr, config_files,
                 pos_mapper.get(), nullptr, nullptr, DexOutputConfig(), 25);

  dout.prepare(SortMode::DEFAULT, sort_modes, config_files, "dex\n039");
  auto code_items = get_ordered_methods(dout);

  uint32_t i = 0;
  std::vector<std::string> method_names(code_items.size());
  for (auto* m : code_items) {
    method_names[i++] = show(m);
  }

  std::vector<std::string> expected_order = {
      "LDexOutputTest$NonPerfSensitiveClass;.<init>:(LDexOutputTest;)V",
      "LDexOutputTest$PerfSensitiveClass;.<init>:(LDexOutputTest;)V",
      "LDexOutputTest$SecondPerfSensitiveClass;.<init>:(LDexOutputTest;)V",
      "LDexOutputTest;.<init>:()V",
      "LDexOutputTest$NonPerfSensitiveClass;.EjustReturnFive:()I",
      "LDexOutputTest$PerfSensitiveClass;.EjustReturnFive:()I",
      "LDexOutputTest$SecondPerfSensitiveClass;.EjustReturnFive:()I",
      "LDexOutputTest;.AjustReturnFive:()I",
      "LDexOutputTest;.EjustReturnFive:()I",
      "LDexOutputTest;.DgetSixpublic:()I",
      "LDexOutputTest$NonPerfSensitiveClass;.FsomeLogic:(I)I",
      "LDexOutputTest$PerfSensitiveClass;.FsomeLogic:(I)I",
      "LDexOutputTest$SecondPerfSensitiveClass;.FsomeLogic:(I)I",
      "LDexOutputTest;.CsomeLogic:(I)I",
      "LDexOutputTest;.FsomeLogic:(I)I",
      "LDexOutputTest;.HsomeLogic:(I)I",
      "LDexOutputTest;.BjustCallSixpublic:()I",
      "LDexOutputTest;.GjustCallSixpublic:()I"};

  EXPECT_TRUE(std::equal(method_names.begin(), method_names.end(),
                         expected_order.begin()));
}

TEST_F(DexOutputTest, TEST_SIMILARITY_ORDERER_PERF_SENSITIVE) {
  std::vector<SortMode> sort_modes{SortMode::METHOD_PROFILED_ORDER,
                                   SortMode::METHOD_SIMILARITY};

  Json::Value cfg;
  std::istringstream temp_json(
      "{\"method_similarity_order\":{\"use_class_level_perf_sensitivity\":true}"
      "}");
  temp_json >> cfg;

  ConfigFiles config_files(cfg);
  config_files.parse_global_config();
  std::unique_ptr<PositionMapper> pos_mapper(PositionMapper::make(""));

  (*classes)[1]->set_perf_sensitive(PerfSensitiveGroup::BETAMAP_ORDERED);
  (*classes)[2]->set_perf_sensitive(PerfSensitiveGroup::BETAMAP_ORDERED);

  auto scope = build_class_scope(stores);

  // Lower the code
  instruction_lowering::normalize_cfg(stores);
  walk::parallel::methods<>(
      scope, [](DexMethod* m) { instruction_lowering::lower(m); });

  auto gtypes = std::make_shared<GatheredTypes>(&*classes);
  DexOutput dout("", &*classes, std::move(gtypes), true, 0, nullptr, 0,
                 DebugInfoKind::NoCustomSymbolication, nullptr, config_files,
                 pos_mapper.get(), nullptr, nullptr, DexOutputConfig(), 25);

  dout.prepare(SortMode::DEFAULT, sort_modes, config_files, "dex\n039");
  auto code_items = get_ordered_methods(dout);

  uint32_t i = 0;
  std::vector<std::string> method_names(code_items.size());
  for (auto* m : code_items) {
    method_names[i++] = show(m);
  }

  std::vector<std::string> expected_order = {
      "LDexOutputTest$PerfSensitiveClass;.<init>:(LDexOutputTest;)V",
      "LDexOutputTest$PerfSensitiveClass;.EjustReturnFive:()I",
      "LDexOutputTest$PerfSensitiveClass;.FsomeLogic:(I)I",
      "LDexOutputTest$SecondPerfSensitiveClass;.<init>:(LDexOutputTest;)V",
      "LDexOutputTest$SecondPerfSensitiveClass;.EjustReturnFive:()I",
      "LDexOutputTest$SecondPerfSensitiveClass;.FsomeLogic:(I)I",
      "LDexOutputTest$NonPerfSensitiveClass;.<init>:(LDexOutputTest;)V",
      "LDexOutputTest;.<init>:()V",
      "LDexOutputTest$NonPerfSensitiveClass;.EjustReturnFive:()I",
      "LDexOutputTest;.AjustReturnFive:()I",
      "LDexOutputTest;.EjustReturnFive:()I",
      "LDexOutputTest;.DgetSixpublic:()I",
      "LDexOutputTest$NonPerfSensitiveClass;.FsomeLogic:(I)I",
      "LDexOutputTest;.CsomeLogic:(I)I",
      "LDexOutputTest;.FsomeLogic:(I)I",
      "LDexOutputTest;.HsomeLogic:(I)I",
      "LDexOutputTest;.BjustCallSixpublic:()I",
      "LDexOutputTest;.GjustCallSixpublic:()I"};

  EXPECT_TRUE(std::equal(method_names.begin(), method_names.end(),
                         expected_order.begin()));
}

TEST_F(DexOutputTest, TEST_COMPRESSION_ORDERER) {
  std::vector<SortMode> sort_modes{SortMode::METHOD_PROFILED_ORDER,
                                   SortMode::METHOD_SIMILARITY};

  Json::Value cfg;
  std::istringstream temp_json(
      "{\"method_similarity_order\":{\"use_compression_conscious_order\":true}"
      "}");
  temp_json >> cfg;

  ConfigFiles config_files(cfg);
  config_files.parse_global_config();
  std::unique_ptr<PositionMapper> pos_mapper(PositionMapper::make(""));
  auto scope = build_class_scope(stores);

  // Lower the code
  instruction_lowering::normalize_cfg(stores);
  walk::parallel::methods<>(
      scope, [](DexMethod* m) { instruction_lowering::lower(m); });

  auto gtypes = std::make_shared<GatheredTypes>(&*classes);
  DexOutput dout("", &*classes, std::move(gtypes), true, 0, nullptr, 0,
                 DebugInfoKind::NoCustomSymbolication, nullptr, config_files,
                 pos_mapper.get(), nullptr, nullptr, DexOutputConfig(), 25);

  dout.prepare(SortMode::DEFAULT, sort_modes, config_files, "dex\n039");
  auto code_items = get_ordered_methods(dout);

  uint32_t i = 0;
  std::vector<std::string> method_names(code_items.size());
  for (auto* m : code_items) {
    method_names[i++] = show(m);
  }

  std::vector<std::string> expected_order = {
      "LDexOutputTest$NonPerfSensitiveClass;.EjustReturnFive:()I",
      "LDexOutputTest$PerfSensitiveClass;.EjustReturnFive:()I",
      "LDexOutputTest$SecondPerfSensitiveClass;.EjustReturnFive:()I",
      "LDexOutputTest;.DgetSixpublic:()I",
      "LDexOutputTest;.AjustReturnFive:()I",
      "LDexOutputTest;.EjustReturnFive:()I",
      "LDexOutputTest;.BjustCallSixpublic:()I",
      "LDexOutputTest;.GjustCallSixpublic:()I",
      "LDexOutputTest$NonPerfSensitiveClass;.FsomeLogic:(I)I",
      "LDexOutputTest$PerfSensitiveClass;.FsomeLogic:(I)I",
      "LDexOutputTest$SecondPerfSensitiveClass;.FsomeLogic:(I)I",
      "LDexOutputTest;.CsomeLogic:(I)I",
      "LDexOutputTest;.FsomeLogic:(I)I",
      "LDexOutputTest;.HsomeLogic:(I)I",
      "LDexOutputTest$NonPerfSensitiveClass;.<init>:(LDexOutputTest;)V",
      "LDexOutputTest$PerfSensitiveClass;.<init>:(LDexOutputTest;)V",
      "LDexOutputTest$SecondPerfSensitiveClass;.<init>:(LDexOutputTest;)V",
      "LDexOutputTest;.<init>:()V"};

  EXPECT_TRUE(std::equal(method_names.begin(), method_names.end(),
                         expected_order.begin()));
}

TEST_F(DexOutputTest, TEST_COMPRESSION_ORDERER_PERF_SENSITIVE) {
  std::vector<SortMode> sort_modes{SortMode::METHOD_PROFILED_ORDER,
                                   SortMode::METHOD_SIMILARITY};

  Json::Value cfg;
  std::istringstream temp_json(
      "{\"method_similarity_order\":{\"use_class_level_perf_sensitivity\":true,"
      "\"use_compression_conscious_order\":true}"
      "}");
  temp_json >> cfg;

  ConfigFiles config_files(cfg);
  config_files.parse_global_config();
  std::unique_ptr<PositionMapper> pos_mapper(PositionMapper::make(""));

  (*classes)[1]->set_perf_sensitive(PerfSensitiveGroup::BETAMAP_ORDERED);
  (*classes)[2]->set_perf_sensitive(PerfSensitiveGroup::BETAMAP_ORDERED);

  auto scope = build_class_scope(stores);

  // Lower the code
  instruction_lowering::normalize_cfg(stores);
  walk::parallel::methods<>(
      scope, [](DexMethod* m) { instruction_lowering::lower(m); });

  auto gtypes = std::make_shared<GatheredTypes>(&*classes);
  DexOutput dout("", &*classes, std::move(gtypes), true, 0, nullptr, 0,
                 DebugInfoKind::NoCustomSymbolication, nullptr, config_files,
                 pos_mapper.get(), nullptr, nullptr, DexOutputConfig(), 25);

  dout.prepare(SortMode::DEFAULT, sort_modes, config_files, "dex\n039");
  auto code_items = get_ordered_methods(dout);

  uint32_t i = 0;
  std::vector<std::string> method_names(code_items.size());
  for (auto* m : code_items) {
    method_names[i++] = show(m);
  }

  std::vector<std::string> expected_order = {
      "LDexOutputTest$PerfSensitiveClass;.<init>:(LDexOutputTest;)V",
      "LDexOutputTest$PerfSensitiveClass;.EjustReturnFive:()I",
      "LDexOutputTest$PerfSensitiveClass;.FsomeLogic:(I)I",
      "LDexOutputTest$SecondPerfSensitiveClass;.<init>:(LDexOutputTest;)V",
      "LDexOutputTest$SecondPerfSensitiveClass;.EjustReturnFive:()I",
      "LDexOutputTest$SecondPerfSensitiveClass;.FsomeLogic:(I)I",
      "LDexOutputTest$NonPerfSensitiveClass;.FsomeLogic:(I)I",
      "LDexOutputTest;.CsomeLogic:(I)I",
      "LDexOutputTest;.FsomeLogic:(I)I",
      "LDexOutputTest;.HsomeLogic:(I)I",
      "LDexOutputTest$NonPerfSensitiveClass;.<init>:(LDexOutputTest;)V",
      "LDexOutputTest;.<init>:()V",
      "LDexOutputTest$NonPerfSensitiveClass;.EjustReturnFive:()I",
      "LDexOutputTest;.DgetSixpublic:()I",
      "LDexOutputTest;.AjustReturnFive:()I",
      "LDexOutputTest;.EjustReturnFive:()I",
      "LDexOutputTest;.BjustCallSixpublic:()I",
      "LDexOutputTest;.GjustCallSixpublic:()I"};

  EXPECT_TRUE(std::equal(method_names.begin(), method_names.end(),
                         expected_order.begin()));
}

TEST_F(DexOutputTest, TEST_COLDSTART_ORDER) {
  std::vector<SortMode> sort_modes{SortMode::METHOD_COLDSTART_ORDER,
                                   SortMode::METHOD_SIMILARITY};
  std::string profile_path = std::getenv("coldstart_methods_file");

  Json::Value cfg;
  std::istringstream temp_json("{\"coldstart_methods_file\":\"" + profile_path +
                               "\"}");
  temp_json >> cfg;

  ConfigFiles config_files(cfg);
  config_files.parse_global_config();
  std::unique_ptr<PositionMapper> pos_mapper(PositionMapper::make(""));

  (*classes)[1]->set_perf_sensitive(PerfSensitiveGroup::BETAMAP_ORDERED);
  (*classes)[2]->set_perf_sensitive(PerfSensitiveGroup::BETAMAP_ORDERED);

  DexMethod::make_method("LDexOutputTest2$Class;.someRandomMethodNotInDex:(I)I")
      ->make_concrete(ACC_PUBLIC, false);

  auto scope = build_class_scope(stores);

  // Lower the code
  instruction_lowering::normalize_cfg(stores);
  walk::parallel::methods<>(
      scope, [](DexMethod* m) { instruction_lowering::lower(m); });

  auto gtypes = std::make_shared<GatheredTypes>(&*classes);
  DexOutput dout("", &*classes, std::move(gtypes), true, 0, nullptr, 0,
                 DebugInfoKind::NoCustomSymbolication, nullptr, config_files,
                 pos_mapper.get(), nullptr, nullptr, DexOutputConfig(), 25);

  dout.prepare(SortMode::DEFAULT, sort_modes, config_files, "dex\n039");
  auto code_items = get_ordered_methods(dout);

  uint32_t i = 0;
  std::vector<std::string> method_names(code_items.size());
  for (auto* m : code_items) {
    method_names[i++] = show(m);
  }

  std::vector<std::string> expected_order = {
      "LDexOutputTest$PerfSensitiveClass;.<init>:(LDexOutputTest;)V",
      "LDexOutputTest$SecondPerfSensitiveClass;.<init>:(LDexOutputTest;)V",
      "LDexOutputTest$PerfSensitiveClass;.EjustReturnFive:()I",
      "LDexOutputTest$SecondPerfSensitiveClass;.EjustReturnFive:()I",
      "LDexOutputTest$SecondPerfSensitiveClass;.FsomeLogic:(I)I",
      "LDexOutputTest$PerfSensitiveClass;.FsomeLogic:(I)I",
      "LDexOutputTest$NonPerfSensitiveClass;.<init>:(LDexOutputTest;)V",
      "LDexOutputTest;.<init>:()V",
      "LDexOutputTest$NonPerfSensitiveClass;.EjustReturnFive:()I",
      "LDexOutputTest;.AjustReturnFive:()I",
      "LDexOutputTest;.EjustReturnFive:()I",
      "LDexOutputTest;.DgetSixpublic:()I",
      "LDexOutputTest$NonPerfSensitiveClass;.FsomeLogic:(I)I",
      "LDexOutputTest;.CsomeLogic:(I)I",
      "LDexOutputTest;.FsomeLogic:(I)I",
      "LDexOutputTest;.HsomeLogic:(I)I",
      "LDexOutputTest;.BjustCallSixpublic:()I",
      "LDexOutputTest;.GjustCallSixpublic:()I"};

  EXPECT_TRUE(std::equal(method_names.begin(), method_names.end(),
                         expected_order.begin()));
}

TEST_F(DexOutputTest, TEST_COLDSTART_ORDER_EMPTY_FILE) {
  std::vector<SortMode> sort_modes{SortMode::METHOD_COLDSTART_ORDER,
                                   SortMode::METHOD_SIMILARITY};
  Json::Value cfg;
  ConfigFiles config_files(cfg);
  config_files.parse_global_config();
  std::unique_ptr<PositionMapper> pos_mapper(PositionMapper::make(""));

  (*classes)[1]->set_perf_sensitive(PerfSensitiveGroup::BETAMAP_ORDERED);
  (*classes)[2]->set_perf_sensitive(PerfSensitiveGroup::BETAMAP_ORDERED);

  auto scope = build_class_scope(stores);

  // Lower the code
  instruction_lowering::normalize_cfg(stores);
  walk::parallel::methods<>(
      scope, [](DexMethod* m) { instruction_lowering::lower(m); });

  auto gtypes = std::make_shared<GatheredTypes>(&*classes);
  DexOutput dout("", &*classes, std::move(gtypes), true, 0, nullptr, 0,
                 DebugInfoKind::NoCustomSymbolication, nullptr, config_files,
                 pos_mapper.get(), nullptr, nullptr, DexOutputConfig(), 25);

  dout.prepare(SortMode::DEFAULT, sort_modes, config_files, "dex\n039");
  auto code_items = get_ordered_methods(dout);

  uint32_t i = 0;
  std::vector<std::string> method_names(code_items.size());
  for (auto* m : code_items) {
    method_names[i++] = show(m);
  }

  std::vector<std::string> expected_order = {
      "LDexOutputTest$NonPerfSensitiveClass;.<init>:(LDexOutputTest;)V",
      "LDexOutputTest$PerfSensitiveClass;.<init>:(LDexOutputTest;)V",
      "LDexOutputTest$SecondPerfSensitiveClass;.<init>:(LDexOutputTest;)V",
      "LDexOutputTest;.<init>:()V",
      "LDexOutputTest$NonPerfSensitiveClass;.EjustReturnFive:()I",
      "LDexOutputTest$PerfSensitiveClass;.EjustReturnFive:()I",
      "LDexOutputTest$SecondPerfSensitiveClass;.EjustReturnFive:()I",
      "LDexOutputTest;.AjustReturnFive:()I",
      "LDexOutputTest;.EjustReturnFive:()I",
      "LDexOutputTest;.DgetSixpublic:()I",
      "LDexOutputTest$NonPerfSensitiveClass;.FsomeLogic:(I)I",
      "LDexOutputTest$PerfSensitiveClass;.FsomeLogic:(I)I",
      "LDexOutputTest$SecondPerfSensitiveClass;.FsomeLogic:(I)I",
      "LDexOutputTest;.CsomeLogic:(I)I",
      "LDexOutputTest;.FsomeLogic:(I)I",
      "LDexOutputTest;.HsomeLogic:(I)I",
      "LDexOutputTest;.BjustCallSixpublic:()I",
      "LDexOutputTest;.GjustCallSixpublic:()I"};

  EXPECT_TRUE(std::equal(method_names.begin(), method_names.end(),
                         expected_order.begin()));
}
