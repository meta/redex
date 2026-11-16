/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "BundleResources.h"
#include "DedupResourceNamePrefixesVerifyHelper.h"

TEST_F(PreVerify, BundleDedupResourceNamePrefixesTest) {
  const auto& resource_pb_file = resources.at("base/resources.pb");
  auto res_table = ResourcesPbFile();
  res_table.collect_resource_data_for_file(resource_pb_file);
  dedupresource_name_prefixes_preverify(classes, &res_table);
}

TEST_F(PostVerify, BundleDedupResourceNamePrefixesTest) {
  const auto& resource_pb_file = resources.at("base/resources.pb");
  auto res_table = ResourcesPbFile();
  res_table.collect_resource_data_for_file(resource_pb_file);
  dedupresource_name_prefixes_postverify(classes, &res_table);
}
