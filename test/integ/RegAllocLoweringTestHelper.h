/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <vector>

#include <gtest/gtest.h>

#include "DexClass.h"
#include "IRCode.h"
#include "IRTypeChecker.h"
#include "InstructionLowering.h"
#include "RegisterAllocation.h"
#include "Show.h"

// Expects IRTypeChecker to accept the code of every method of `classes`, both
// as it is and after register allocation, and the allocated code to lower to
// encodable instructions (lowering asserts that range calls get consecutive
// registers).
inline void expect_type_correct_through_register_allocation_and_lowering(
    const std::vector<DexClass*>& classes) {
  auto expect_type_correct = [](DexMethod* method) {
    IRTypeChecker checker(method);
    checker.run();
    EXPECT_TRUE(checker.good()) << show(method) << ": " << checker.what();
  };
  for (const auto* cls : classes) {
    for (auto* method : cls->get_all_methods()) {
      auto* code = method->get_code();
      if (code == nullptr) {
        continue;
      }
      expect_type_correct(method);
      code->build_cfg();
      regalloc::graph_coloring::allocate({}, method);
      code->clear_cfg();
      expect_type_correct(method);
      instruction_lowering::lower(method);
    }
  }
}
