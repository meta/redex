/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <memory>
#include <string>
#include <utility>
#include <vector>

#include <boost/filesystem/operations.hpp>
#include <gtest/gtest.h>

#include "ConfigFiles.h"
#include "DexClass.h"
#include "DexLoader.h"
#include "DexOutput.h"
#include "DexPosition.h"
#include "DexStore.h"
#include "InstructionLowering.h"

// Loads the dex file at `path`, which must have version `dex_version`.
inline DexClasses load_dex_file(const std::string& path, int dex_version) {
  int input_dex_version = 0;
  auto classes = load_classes_from_dex(DexLocation::make_location("dex", path),
                                       /* stats */ nullptr, &input_dex_version,
                                       /* balloon */ true,
                                       /* throw_on_balloon_error */ true,
                                       /* support_dex_version */ dex_version);
  EXPECT_EQ(input_dex_version, dex_version);
  return classes;
}

// Writes `classes` as a dex file of version `dex_version` in `dir` and returns
// its path.
inline std::string write_dex_file(DexClasses classes,
                                  const std::string& dir,
                                  int dex_version) {
  DexMetadata dm;
  dm.set_id("classes");
  DexStore store(dm);
  store.add_classes(std::move(classes));
  std::vector<DexStore> stores;
  stores.emplace_back(std::move(store));
  instruction_lowering::normalize_cfg(stores);
  instruction_lowering::run(stores);

  std::unique_ptr<PositionMapper> pos_mapper(PositionMapper::make(""));
  UnorderedMap<DexMethod*, uint64_t> method_to_id;
  UnorderedMap<DexCode*, std::vector<DebugLineItem>> code_debug_lines;
  ConfigFiles config(Json::nullValue, dir);
  // The writer records offsets in a metafile.
  boost::filesystem::create_directories(dir + "/meta");
  auto path = dir + "/output.dex";
  auto& dex = stores[0].get_dexen().back();
  auto magic = "dex\n0" + std::to_string(dex_version);
  magic.push_back('\0');
  write_classes_to_dex(path, &dex, std::make_shared<GatheredTypes>(&dex), 0,
                       nullptr, 0, config, pos_mapper.get(),
                       DebugInfoKind::NoCustomSymbolication, &method_to_id,
                       &code_debug_lines, nullptr, magic);
  return path;
}
