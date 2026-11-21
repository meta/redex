/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <thread>
#include <vector>

#include <gtest/gtest.h>

#include "DexClass.h"
#include "RedexTest.h"
#include "SingleImplDefs.h"

namespace {

class SingleImplEscapeTest : public RedexTest {};

// Gives tests access to the analysis' interfaces.
struct TestAnalysis : SingleImplAnalysis {
  SingleImpls& interfaces() { return single_impls; }
};

} // namespace

// The analysis escapes interfaces from parallel walks, so threads that escape
// one interface for different reasons must not race; a build with
// ThreadSanitizer reports the race if they do.
TEST_F(SingleImplEscapeTest, concurrentEscapesOfOneInterface) {
  const auto* intf = DexType::make_type("LI;");
  TestAnalysis analysis;
  auto& data = analysis.interfaces()[intf];
  data.cls = DexType::make_type("LImpl;");
  data.escape = NO_ESCAPE;
  const std::vector<EscapeReason> reasons{CONST_CLS, UNKNOWN_MREF,
                                          HAS_FIELD_REF, NEXT_PASS};

  std::vector<std::thread> threads;
  threads.reserve(reasons.size());
  for (auto reason : reasons) {
    threads.emplace_back([&analysis, intf, reason] {
      for (int i = 0; i < 1000; ++i) {
        analysis.escape_interface(intf, reason);
      }
    });
  }
  for (auto& thread : threads) {
    thread.join();
  }

  auto all_reasons = NO_ESCAPE;
  for (auto reason : reasons) {
    all_reasons |= reason;
  }
  EXPECT_EQ(analysis.interfaces().at(intf).escape, all_reasons);
}
