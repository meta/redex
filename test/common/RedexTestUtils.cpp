/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "RedexTestUtils.h"

#include "Debug.h"
#include "DexClass.h"
#include "IRCode.h"
#include "Show.h"

#include <iostream>

namespace redex {
bool are_files_equal(const std::string& p1, const std::string& p2) {
  std::ifstream f1(p1, std::ifstream::binary | std::ifstream::ate);
  std::ifstream f2(p2, std::ifstream::binary | std::ifstream::ate);
  always_assert_log(!f1.fail(), "Failed to read path %s", p1.c_str());
  always_assert_log(!f2.fail(), "Failed to read path %s", p2.c_str());
  if (f1.tellg() != f2.tellg()) {
    std::cerr << "File length mismatch. " << f1.tellg() << " != " << f2.tellg()
              << "\n";
    return false;
  }
  f1.seekg(0, std::ifstream::beg);
  f2.seekg(0, std::ifstream::beg);
  return std::equal(std::istreambuf_iterator<char>(f1.rdbuf()),
                    std::istreambuf_iterator<char>(),
                    std::istreambuf_iterator<char>(f2.rdbuf()));
}

std::map<std::string, std::vector<std::string>> show_instructions_by_method(
    const std::vector<DexClass*>& classes) {
  std::map<std::string, std::vector<std::string>> result;
  for (const auto* cls : classes) {
    for (const auto* method : cls->get_all_methods()) {
      const auto* code = method->get_code();
      if (code == nullptr) {
        continue;
      }
      always_assert(!code->cfg_built());
      auto& instructions = result[show(method)];
      for (const auto& mie : InstructionIterable(code)) {
        instructions.push_back(show(mie.insn));
      }
    }
  }
  return result;
}
} // namespace redex
