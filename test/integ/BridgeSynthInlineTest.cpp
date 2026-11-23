/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <cstdlib>
#include <gtest/gtest.h>
#include <iostream>
#include <string>

#include "ControlFlow.h"
#include "DexClass.h"
#include "IRCode.h"
#include "RedexTest.h"

#include "BridgeSynthInlinePass.h"
#include "LocalDcePass.h"
#include "ReBindRefs.h"
#include "Show.h"
#include "Trace.h"

#include "Match.h"

// NOTE: this is not really a unit test.

/*
 To understand this test one needs to also look at the file
 Java source files BridgeSynthInline*.java in the same directory.
 These Java source files is compiled and a corresponding Dex file
 is created which is an input to this test.

 The Alpha class has an inner class Beta and there is an access
 inside Beta to a static field of Alpha which induces a synthetic
 wrapper. This test makes sure this wrapper method is removed.

 The Gamma class has an inner class Delta which has a non-concrete
 access to a field that is declared elesewhere. This test checks
 to make sure we do not optimize such synthetic getters.

 */

class SynthTest1 : public RedexIntegrationTest {
 protected:
  template <typename P>
  bool assert_classes(const DexClasses& classes,
                      const m::match_t<DexClass*, P>& p) {
    for (const auto& cls : classes) {
      if (p.matches(cls)) {
        return true;
      }
    }
    return false;
  }
};

TEST_F(SynthTest1, synthetic) {
  std::vector<Pass*> passes = {
      new ReBindRefsPass(),
      new LocalDcePass(),
      new BridgeSynthInlinePass(),
      new LocalDcePass(),
  };

  run_passes(passes);

  // Make sure synthetic method is removed from class Alpha.
  for (const auto& cls : *classes) {
    const auto* const class_name = cls->get_type()->get_name()->c_str();
    // Make sure the synthetic method has been removed.
    if (strcmp(class_name, "Lcom/facebook/redextest/Alpha;") == 0) {
      for (const auto& method : cls->get_dmethods()) {
        ASSERT_STRNE("access$000", method->get_name()->c_str());
      }
    }

    // Make sure there are no references to the synthetic method.
    if (strcmp(class_name, "Lcom/facebook/redextest/Alpha$Beta;") == 0) {
      for (const auto& method : cls->get_vmethods()) {
        auto* code = method->get_code();
        code->build_cfg();
        for (auto& mie : InstructionIterable(code->cfg())) {
          auto* insn = mie.insn;
          std::cout << SHOW(insn) << "\n";
          if (opcode::is_a_method_invoke(insn->opcode())) {
            const auto* const clazz =
                insn->get_method()->get_class()->get_name()->c_str();
            const auto* const n = insn->get_method()->get_name()->c_str();
            auto invocation = std::string(clazz) + "." + std::string(n);
            ASSERT_STRNE("Lcom/facebook/redextest/Alpha;.access$000",
                         invocation.c_str());
          }
        }
        code->clear_cfg();
      }
    }

    // Make sure we don't apply the optimization in cases where the field
    // is not concrete.
    if (strcmp(class_name, "Lcom/facebook/redextest/Gamma;") == 0) {
      bool gamma_synth_found = false;
      for (const auto& method : cls->get_dmethods()) {
        if (strcmp(method->get_name()->c_str(), "access$000") == 0) {
          gamma_synth_found = true;
          break;
        }
      }
      ASSERT_TRUE(gamma_synth_found);
    }

    // Make sure the const_4 insn before the call to synthetic constructor is
    // removed
    if (strcmp(class_name,
               "Lcom/facebook/redextest/SyntheticConstructor$InnerClass;") ==
        0) {
      for (const auto& method : cls->get_dmethods()) {
        if (strcmp(method->get_name()->c_str(), "<init>") == 0) {
          TRACE(DCE, 2, "dmethod: %s", SHOW(method->get_code()));
          for (auto& mie : InstructionIterable(method->get_code())) {
            auto* instruction = mie.insn;
            // Make sure there is no const-4 in the optimized method.
            ASSERT_NE(instruction->opcode(), OPCODE_CONST);
          }
        }
      }
    }

    // Tests re-expressed using the match library.

    auto has_alpha_access_gone =
        m::named<DexClass>("Lcom/facebook/redextest/Alpha;") &&
        !m::any_dmethods(m::named<DexMethod>("access$000"));

    ASSERT_TRUE(assert_classes(*classes, has_alpha_access_gone));
  }
}
