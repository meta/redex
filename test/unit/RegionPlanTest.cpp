/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

// The region plan on its own: the shapes `RegionPlan::make` refuses.

#include <gtest/gtest.h>

#include <vector>

#include "RedexTest.h"
#include "RegionPlan.h"
#include "SwitchFixture.h"

namespace msi = method_splitting_impl;
using method_splitting_test::region_closure;
using method_splitting_test::SwitchFixture;

class RegionPlanTest : public RedexTest {};

TEST_F(RegionPlanTest, MakeRefusesSeveralRegions) {
  SwitchFixture f;
  auto c0 = region_closure(f.case0, SwitchFixture::rejoin_of(f.case0));
  auto c1 = region_closure(f.case1, SwitchFixture::rejoin_of(f.case1));
  EXPECT_NO_THROW(msi::RegionPlan::make({&c0}));
  EXPECT_THROW(msi::RegionPlan::make({&c0, &c1}), RedexException);
}
