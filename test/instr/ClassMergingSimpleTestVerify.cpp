/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <boost/regex.hpp>

#include "Show.h"
#include "verify/VerifyUtil.h"

TEST_F(PostVerify, MergeablesRemoval) {
  auto* cls_a = find_class_named(classes, "Lcom/facebook/redextest/A;");
  auto* cls_b = find_class_named(classes, "Lcom/facebook/redextest/B;");
  auto* cls_c = find_class_named(classes, "Lcom/facebook/redextest/C;");
  auto* cls_d = find_class_named(classes, "Lcom/facebook/redextest/D;");
  verify_class_merged(cls_a);
  verify_class_merged(cls_b);
  verify_class_merged(cls_c);
  verify_class_merged(cls_d);
}

TEST_F(PostVerify, ArrayInstanceOfKeepsElementClasses) {
  auto* cls_a = find_class_named(classes, "Lcom/facebook/redextest/ArrayA;");
  auto* cls_b = find_class_named(classes, "Lcom/facebook/redextest/ArrayB;");
  ASSERT_NE(cls_a, nullptr);
  ASSERT_NE(cls_b, nullptr);
  EXPECT_NE(find_method_named(*cls_a, "<init>"), nullptr);
  EXPECT_NE(find_method_named(*cls_b, "<init>"), nullptr);
}

TEST_F(PostVerify, PlainInstanceOfStillMerges) {
  verify_class_merged(
      find_class_named(classes, "Lcom/facebook/redextest/ArrayC;"));
  verify_class_merged(
      find_class_named(classes, "Lcom/facebook/redextest/ArrayD;"));
}

TEST_F(PostVerify, SinkCommonCtorInvocation) {
  boost::regex shape_name_pattern(
      "^Lcom/facebook/redextest/SimpleBaseShape_S0000000_\\w+;$");
  auto* cls =
      find_class_named(classes, [&shape_name_pattern](const char* name) {
        return boost::regex_match(name, shape_name_pattern);
      });

  for (auto* dm : cls->get_dmethods()) {
    if (!dm->get_deobfuscated_name_or_empty().ends_with(
            ".<init>:(Ljava/lang/String;I)V")) {
      continue;
    }

    int invocation_count = 0;
    auto param_insns = InstructionIterable(dm->get_code());
    for (auto param_it = param_insns.begin(); param_it != param_insns.end();
         ++param_it) {
      invocation_count +=
          opcode::is_invoke_direct(param_it->insn->opcode()) ? 1 : 0;
    }
    EXPECT_EQ(invocation_count, 1);
  }
}
