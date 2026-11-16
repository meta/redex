/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "ApkResources.h"
#include "DedupResourceNamePrefixesVerifyHelper.h"

TEST_F(PreVerify, ApkDedupResourceNamePrefixesTest) {
  auto res_table = ResourcesArscFile(writable_resource("resources.arsc"));
  dedupresource_name_prefixes_preverify(classes, &res_table);
}

TEST_F(PostVerify, ApkDedupResourceNamePrefixesTest) {
  auto res_table = ResourcesArscFile(writable_resource("resources.arsc"));
  dedupresource_name_prefixes_postverify(classes, &res_table);
}
