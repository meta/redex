/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "TypeAnalysisRuntimeAssert.h"

#include <string>

#include "Creators.h"
#include "GlobalTypeAnalyzer.h"
#include "IRAssembler.h"
#include "RedexTest.h"
#include "Walkers.h"

using namespace type_analyzer;

struct TypeAnalysisRuntimeAssertTest : public RedexTest {};

namespace {

// Java-like, with `p.Box.make()` returning a `p.Hidden[]` as an `Object[]`,
// where `p.Hidden` is package-private:
//
//   static void run() { Object[] items = p.Box.make(); }
//
// Returns how many type checks the transform inserts into `run` in `host`.
size_t type_checks_inserted_in(DexClass* box, const char* host) {
  auto* run = assembler::method_from_string(std::string(R"(
    (method (public static) ")") + host + R"(.run:()V"
      (
        (invoke-static () "Lp/Box;.make:()[Ljava/lang/Object;")
        (move-result-object v0)
        (return-void)
      )
    )
  )");
  run->rstate.set_root();
  ClassCreator user(run->get_class());
  user.set_super(type::java_lang_Object());
  user.add_method(run);
  Scope scope{box, user.create()};
  walk::code(scope, [](DexMethod*, IRCode& code) {
    if (!code.cfg_built()) {
      code.build_cfg();
    }
  });

  global::GlobalTypeAnalysis analysis;
  auto gta = analysis.analyze(scope);
  auto wps = gta->get_whole_program_state();
  always_assert(
      wps.get_return_type(box->get_dmethods().front()).get_dex_type() ==
      DexType::get_type("[Lp/Hidden;"));

  RuntimeAssertTransform::Config config;
  config.return_value_assert_fail_handler =
      DexMethod::make_method("LAssert;.fail:(Ljava/lang/String;)V");
  RuntimeAssertTransform transform(config);
  auto stats =
      transform.apply(*gta->get_replayable_local_analysis(run), wps, run);
  return stats.return_type_check_inserted;
}

DexClass* make_box(bool hidden_is_external) {
  ClassCreator hidden(DexType::make_type("Lp/Hidden;"));
  hidden.set_super(type::java_lang_Object());
  hidden.set_access(DexAccessFlags(0));
  if (hidden_is_external) {
    hidden.set_external();
  }
  hidden.create();
  ClassCreator box(DexType::make_type("Lp/Box;"));
  box.set_super(type::java_lang_Object());
  box.add_method(assembler::method_from_string(R"(
    (method (public static) "Lp/Box;.make:()[Ljava/lang/Object;"
      (
        (const v0 1)
        (new-array v0 "[Lp/Hidden;")
        (move-result-pseudo-object v1)
        (return-object v1)
      )
    )
  )"));
  return box.create();
}

} // namespace

// The type check is an `instance-of p.Hidden[]`, and the device checks access
// to an array type through its element class: only a method of package `p` may
// name it.
TEST_F(TypeAnalysisRuntimeAssertTest, no_check_of_an_inaccessible_array_type) {
  auto* box_cls = make_box(/* hidden_is_external */ false);
  EXPECT_EQ(type_checks_inserted_in(box_cls, "Lp/User;"), 1u);
  EXPECT_EQ(type_checks_inserted_in(box_cls, "Lq/User;"), 0u);
}

TEST_F(TypeAnalysisRuntimeAssertTest,
       no_check_of_an_inaccessible_external_class) {
  auto* box_cls = make_box(/* hidden_is_external */ true);
  EXPECT_EQ(type_checks_inserted_in(box_cls, "Lq/User;"), 0u);
}
