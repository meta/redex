/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "ControlFlow.h"
#include "Creators.h"
#include "IRAssembler.h"
#include "IRCode.h"
#include "RedexTest.h"
#include "SourceBlocks.h"
#include "Walkers.h"

#include "InsertSourceBlocks.h"
#include "PartialApplication.h"
#include "ReachableNatives.h"
#include "RedexContext.h"

static IRCode* get_code(const std::string& s) {
  auto* method = DexMethod::get_method(s);
  return method->as_def()->get_code();
}

namespace {

// Stamps a known execution count of 1 onto every source block, so that a
// helper method's derived count is exactly the number of call-sites it serves.
// Without profile files InsertSourceBlocksPass leaves no interaction slots at
// all, so there would otherwise be no counts to sum.
class SetSourceBlockCountsPass : public Pass {
 public:
  SetSourceBlockCountsPass() : Pass("SetSourceBlockCountsPass") {}

  redex_properties::PropertyInteractions get_property_interactions()
      const override {
    using namespace redex_properties::interactions;
    using namespace redex_properties::names;
    return {{HasSourceBlocks, RequiresAndPreserves}};
  }

  void run_pass(DexStoresVector& stores, ConfigFiles&, PassManager&) override {
    walk::code(build_class_scope(stores), [](DexMethod*, IRCode& code) {
      for (auto* block : code.cfg().blocks()) {
        for (auto& mie : *block) {
          if (mie.type == MFLOW_SOURCE_BLOCK) {
            mie.src_block = with_unit_count(mie.src_block.get());
          }
        }
      }
    });
  }

 private:
  // `vals_size` is immutable, so a source block carrying an interaction has to
  // be built rather than filled in place.
  static std::unique_ptr<SourceBlock> with_unit_count(const SourceBlock* sb) {
    if (sb == nullptr) {
      return nullptr;
    }
    auto res = std::make_unique<SourceBlock>(
        sb->src, sb->id,
        std::vector<SourceBlock::Val>{SourceBlock::Val(1.0f, 100.0f)});
    res->next = with_unit_count(sb->next.get());
    return res;
  }
};

} // namespace

class PartialApplicationTest : public RedexIntegrationTest {
 public:
  PartialApplicationTest() {
    ClassCreator creator(DexType::make_type("Ljava/lang/Integer;"));
    creator.set_super(type::java_lang_Object());
    creator.set_external();

    auto* valueof = dynamic_cast<DexMethod*>(DexMethod::make_method(
        "Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;"));
    valueof->set_external();
    valueof->make_concrete(ACC_PUBLIC | ACC_STATIC, true);
    creator.add_method(valueof);

    auto* value = dynamic_cast<DexMethod*>(
        DexMethod::make_method("Ljava/lang/Integer;.intValue:()I"));
    value->set_external();
    value->make_concrete(ACC_PUBLIC, true);
    creator.add_method(value);

    creator.create();
  }

 protected:
  // Runs InsertSourceBlocksPass, then `middle`, then PartialApplicationPass
  // with source-block derivation enabled.
  void run_with_source_blocks(const std::vector<Pass*>& middle) {
    // The loading code in integ-test does not insert deobfuscated names, which
    // InsertSourceBlocksPass needs.
    walk::methods(*classes, [](auto* m) { m->set_deobfuscated_name(show(m)); });

    Json::Value config(Json::objectValue);
    config["PartialApplicationPass"] = Json::objectValue;
    config["PartialApplicationPass"]["fix_missing_source_blocks"] = true;

    std::vector<Pass*> passes = {new InsertSourceBlocksPass()};
    passes.insert(passes.end(), middle.begin(), middle.end());
    passes.push_back(new PartialApplicationPass());
    run_passes(passes, /* pg_config */ nullptr, config);
  }
};

TEST_F(PartialApplicationTest, basic) {
  std::vector<Pass*> passes = {
      new PartialApplicationPass(),
  };

  run_passes(passes);

  // call_fooX gets foo$spa$
  auto expected_code = assembler::ircode_from_string(R"(
    (
     (.pos:dbg_0 "Lcom/facebook/redextest/PartialApplication;.call_foo4:()V" PartialApplication.java 30)
     (invoke-static () "Lcom/facebook/redextest/PartialApplication$Callees;.foo$spa$0$3b9e1bb0b5617ee4$0:()V")
     (.pos:dbg_1 "Lcom/facebook/redextest/PartialApplication;.call_foo4:()V" PartialApplication.java 31)
     (return-void)
    )
)");
  EXPECT_CODE_EQ(
      get_code("Lcom/facebook/redextest/PartialApplication;.call_foo4:()V"),
      expected_code.get());

  expected_code = assembler::ircode_from_string(R"(
    (
     (.pos:dbg_0 "Lcom/facebook/redextest/PartialApplication$Callees;.foo$spa$0$3b9e1bb0b5617ee4$0:()V" RedexGenerated 0)
     (const v0 0)
     (const v1 1)
     (const v2 2)
     (const v3 3)
     (const v4 4)
     (const v5 5)
     (const v6 6)
     (const v7 7)
     (invoke-static (v0 v1 v2 v3 v4 v5 v6 v7) "Lcom/facebook/redextest/PartialApplication$Callees;.foo:(IIIIIIII)V")
     (return-void)
    )
)");
  EXPECT_CODE_EQ(
      get_code("Lcom/facebook/redextest/"
               "PartialApplication$Callees;.foo$spa$0$3b9e1bb0b5617ee4$0:()V"),
      expected_code.get());

  // call_barX gets bar$spa$
  expected_code = assembler::ircode_from_string(R"(
    (
     (.pos:dbg_0 "Lcom/facebook/redextest/PartialApplication;.call_bar4:()V" PartialApplication.java 52)
     (const v0 1)
     (invoke-static (v0) "Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;")
     (invoke-static () "Lcom/facebook/redextest/PartialApplication$Callees;.bar$spa$0$8477e08f7d55cc6f$0:()V")
     (.pos:dbg_1 "Lcom/facebook/redextest/PartialApplication;.call_bar4:()V" PartialApplication.java 53)
     (return-void)
    )
)");
  EXPECT_CODE_EQ(
      get_code("Lcom/facebook/redextest/PartialApplication;.call_bar4:()V"),
      expected_code.get());

  expected_code = assembler::ircode_from_string(R"(
    (
     (.pos:dbg_0 "Lcom/facebook/redextest/PartialApplication$Callees;.bar$spa$0$8477e08f7d55cc6f$0:()V" RedexGenerated 0)
     (const v0 0)
     (const v1 65)
     (const v2 1)
     (invoke-static (v2) "Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;")
     (move-result-object v3)
     (const v4 0)
     (const v5 3)
     (const v6 4)
     (const v7 5)
     (const v8 6)
     (invoke-static (v0 v1 v3 v4 v5 v6 v7 v8) "Lcom/facebook/redextest/PartialApplication$Callees;.bar:(SCLjava/lang/Integer;Ljava/lang/String;IIII)I")
     (return-void)
    )
)");
  EXPECT_CODE_EQ(
      get_code("Lcom/facebook/redextest/"
               "PartialApplication$Callees;.bar$spa$0$8477e08f7d55cc6f$0:()V"),
      expected_code.get());

  // call_bazX gets baz$spa$
  expected_code = assembler::ircode_from_string(R"(
    (
     (.pos:dbg_0 "Lcom/facebook/redextest/PartialApplication;.call_baz4:()I" PartialApplication.java 80)
     (new-instance "Lcom/facebook/redextest/PartialApplication$MoreCallees;")
     (move-result-pseudo-object v0)
     (invoke-direct (v0) "Lcom/facebook/redextest/PartialApplication$MoreCallees;.<init>:()V")
     (.pos:dbg_1 "Lcom/facebook/redextest/PartialApplication;.call_baz4:()I" PartialApplication.java 81)
     (.dbg DBG_START_LOCAL 0 "mc" "Lcom/facebook/redextest/PartialApplication$MoreCallees;")
     (const v8 203)
     (const v1 103)
     (invoke-virtual (v0 v1 v8) "Lcom/facebook/redextest/PartialApplication$MoreCallees;.baz$ipa$0$310a286dd75824f4$0:(II)I")
     (move-result v1)
     (return v1)
    )
)");
  EXPECT_CODE_EQ(
      get_code("Lcom/facebook/redextest/PartialApplication;.call_baz4:()I"),
      expected_code.get());

  expected_code = assembler::ircode_from_string(R"(
    (
     (load-param-object v7)
     (load-param v8)
     (load-param v9)
     (.pos:dbg_0 "Lcom/facebook/redextest/PartialApplication$MoreCallees;.baz$ipa$0$310a286dd75824f4$0:(II)I" RedexGenerated 0)
     (const v0 1111)
     (const v1 2222)
     (const v2 3333)
     (const v3 4444)
     (const v4 5555)
     (const v5 6666)
     (invoke-virtual (v7 v8 v0 v1 v2 v3 v4 v5 v9) "Lcom/facebook/redextest/PartialApplication$MoreCallees;.baz:(IIIIIIII)I")
     (move-result v6)
     (return v6)
    )
)");
  EXPECT_CODE_EQ(
      get_code(
          "Lcom/facebook/redextest/"
          "PartialApplication$MoreCallees;.baz$ipa$0$310a286dd75824f4$0:(II)I"),
      expected_code.get());
}

// The generated helper methods sit on the path of every call-site they serve,
// so with the fix enabled each one gets a synthetic source block (id
// 4294967295 is SourceBlock::kSyntheticId) attributed to the helper itself.
//
// Its count is the SUM of the counts of the call-sites it serves, because the
// helper runs once per execution of any of them. SetSourceBlockCountsPass
// gives every call-site a count of 1, so the counts below are exactly the
// number of call-sites each helper serves -- 7, 5 and 6. Maxing over the
// call-sites instead of summing would make all three 1. `appear100` is a
// probability, so it maxes rather than accumulating, and stays at 100.
TEST_F(PartialApplicationTest, generated_methods_sum_call_site_counts) {
  run_with_source_blocks({new SetSourceBlockCountsPass()});

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (.pos:dbg_0 "Lcom/facebook/redextest/PartialApplication$Callees;.foo$spa$0$3b9e1bb0b5617ee4$0:()V" RedexGenerated 0)
     (.src_block "Lcom/facebook/redextest/PartialApplication$Callees;.foo$spa$0$3b9e1bb0b5617ee4$0:()V" 4294967295 (7.0 100.0))
     (const v0 0)
     (const v1 1)
     (const v2 2)
     (const v3 3)
     (const v4 4)
     (const v5 5)
     (const v6 6)
     (const v7 7)
     (invoke-static (v0 v1 v2 v3 v4 v5 v6 v7) "Lcom/facebook/redextest/PartialApplication$Callees;.foo:(IIIIIIII)V")
     (return-void)
    )
)");
  EXPECT_CODE_EQ(
      get_code("Lcom/facebook/redextest/"
               "PartialApplication$Callees;.foo$spa$0$3b9e1bb0b5617ee4$0:()V"),
      expected_code.get());

  expected_code = assembler::ircode_from_string(R"(
    (
     (.pos:dbg_0 "Lcom/facebook/redextest/PartialApplication$Callees;.bar$spa$0$8477e08f7d55cc6f$0:()V" RedexGenerated 0)
     (.src_block "Lcom/facebook/redextest/PartialApplication$Callees;.bar$spa$0$8477e08f7d55cc6f$0:()V" 4294967295 (5.0 100.0))
     (const v0 0)
     (const v1 65)
     (const v2 1)
     (invoke-static (v2) "Ljava/lang/Integer;.valueOf:(I)Ljava/lang/Integer;")
     (move-result-object v3)
     (const v4 0)
     (const v5 3)
     (const v6 4)
     (const v7 5)
     (const v8 6)
     (invoke-static (v0 v1 v3 v4 v5 v6 v7 v8) "Lcom/facebook/redextest/PartialApplication$Callees;.bar:(SCLjava/lang/Integer;Ljava/lang/String;IIII)I")
     (return-void)
    )
)");
  EXPECT_CODE_EQ(
      get_code("Lcom/facebook/redextest/"
               "PartialApplication$Callees;.bar$spa$0$8477e08f7d55cc6f$0:()V"),
      expected_code.get());

  // Instance helper: the source block goes after the parameter loads.
  expected_code = assembler::ircode_from_string(R"(
    (
     (load-param-object v7)
     (load-param v8)
     (load-param v9)
     (.pos:dbg_0 "Lcom/facebook/redextest/PartialApplication$MoreCallees;.baz$ipa$0$310a286dd75824f4$0:(II)I" RedexGenerated 0)
     (.src_block "Lcom/facebook/redextest/PartialApplication$MoreCallees;.baz$ipa$0$310a286dd75824f4$0:(II)I" 4294967295 (6.0 100.0))
     (const v0 1111)
     (const v1 2222)
     (const v2 3333)
     (const v3 4444)
     (const v4 5555)
     (const v5 6666)
     (invoke-virtual (v7 v8 v0 v1 v2 v3 v4 v5 v9) "Lcom/facebook/redextest/PartialApplication$MoreCallees;.baz:(IIIIIIII)I")
     (move-result v6)
     (return v6)
    )
)");
  EXPECT_CODE_EQ(
      get_code(
          "Lcom/facebook/redextest/"
          "PartialApplication$MoreCallees;.baz$ipa$0$310a286dd75824f4$0:(II)I"),
      expected_code.get());
}

// The fix is off by default, so that turning it on -- which makes the helper
// methods visible to profile-guided decisions such as inlining -- is a
// separate, measurable change. Source blocks exist everywhere else here, but
// the helper method gets none.
TEST_F(PartialApplicationTest, source_blocks_are_off_by_default) {
  walk::methods(*classes, [](auto* m) { m->set_deobfuscated_name(show(m)); });

  std::vector<Pass*> passes = {
      new InsertSourceBlocksPass(),
      new PartialApplicationPass(),
  };

  run_passes(passes);

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (.pos:dbg_0 "Lcom/facebook/redextest/PartialApplication$Callees;.foo$spa$0$3b9e1bb0b5617ee4$0:()V" RedexGenerated 0)
     (const v0 0)
     (const v1 1)
     (const v2 2)
     (const v3 3)
     (const v4 4)
     (const v5 5)
     (const v6 6)
     (const v7 7)
     (invoke-static (v0 v1 v2 v3 v4 v5 v6 v7) "Lcom/facebook/redextest/PartialApplication$Callees;.foo:(IIIIIIII)V")
     (return-void)
    )
)");
  EXPECT_CODE_EQ(
      get_code("Lcom/facebook/redextest/"
               "PartialApplication$Callees;.foo$spa$0$3b9e1bb0b5617ee4$0:()V"),
      expected_code.get());
}

TEST_F(PartialApplicationTest, preserves_no_outlining_static_callee) {
  auto* callee =
      DexMethod::get_method(
          "Lcom/facebook/redextest/PartialApplication$Callees;.foo:(IIIIIIII)V")
          ->as_def();
  callee->rstate.set_no_outlining();
  auto* caller =
      get_code("Lcom/facebook/redextest/PartialApplication;.call_foo4:()V");
  auto expected = assembler::ircode_from_s_expr(assembler::to_s_expr(caller));

  run_passes({new PartialApplicationPass()});

  EXPECT_CODE_EQ(caller, expected.get());
  EXPECT_EQ(nullptr, DexMethod::get_method(
                         "Lcom/facebook/redextest/PartialApplication$Callees;"
                         ".foo$spa$0$3b9e1bb0b5617ee4$0:()V"));
  EXPECT_NE(nullptr, DexMethod::get_method(
                         "Lcom/facebook/redextest/PartialApplication$Callees;"
                         ".bar$spa$0$8477e08f7d55cc6f$0:()V"));
}

TEST_F(PartialApplicationTest, preserves_no_outlining_virtual_callee) {
  auto* callee = DexMethod::get_method(
                     "Lcom/facebook/redextest/PartialApplication$MoreCallees;"
                     ".baz:(IIIIIIII)I")
                     ->as_def();
  callee->rstate.set_no_outlining();
  auto* caller =
      get_code("Lcom/facebook/redextest/PartialApplication;.call_baz4:()I");
  auto expected = assembler::ircode_from_s_expr(assembler::to_s_expr(caller));

  run_passes({new PartialApplicationPass()});

  EXPECT_CODE_EQ(caller, expected.get());
  EXPECT_EQ(nullptr,
            DexMethod::get_method(
                "Lcom/facebook/redextest/PartialApplication$MoreCallees;"
                ".baz$ipa$0$310a286dd75824f4$0:(II)I"));
}

TEST_F(PartialApplicationTest, preserves_constant_load_library_names) {
  auto* string_type = type::java_lang_String();
  auto* loader_type = DexType::make_type("Lcom/facebook/soloader/SoLoader;");
  ClassCreator loader(loader_type);
  loader.set_super(type::java_lang_Object());
  for (const auto* name : {"loadLibrary", "loadLibraryUnsafe"}) {
    for (bool with_flags : {false, true}) {
      auto* args =
          with_flags ? DexTypeList::make_type_list({string_type, type::_int()})
                     : DexTypeList::make_type_list({string_type});
      auto* method =
          DexMethod::make_method(loader_type, DexString::make_string(name),
                                 DexProto::make_proto(type::_boolean(), args))
              ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
      method->set_code(assembler::ircode_from_string(
          with_flags ? "((load-param-object v0) (load-param v1) "
                       "(const v2 0) (return v2))"
                     : "((load-param-object v0) (const v1 0) (return v1))"));
      loader.add_method(method);
    }
  }
  classes->push_back(loader.create());

  auto* caller_type = DexType::make_type("LNativeLoaders;");
  ClassCreator callers(caller_type);
  callers.set_super(type::java_lang_Object());
  for (size_t i = 0; i < 7; ++i) {
    auto* method = DexMethod::make_method(
                       caller_type,
                       DexString::make_string("load" + std::to_string(i)),
                       DexProto::make_proto(type::_void(),
                                            DexTypeList::make_type_list({})))
                       ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
    method->rstate.set_root();
    method->set_code(assembler::ircode_from_string(
        "((const-string \"library" + std::to_string(i) +
        "\") (move-result-pseudo-object v0) (const v1 16) "
        "(invoke-static (v0 v1) \"Lcom/facebook/soloader/SoLoader;"
        ".loadLibrary:(Ljava/lang/String;I)Z\") (return-void))"));
    callers.add_method(method);
  }
  auto* callers_class = callers.create();
  callers_class->rstate.set_root();
  classes->push_back(callers_class);

  Json::Value config(Json::objectValue);
  config["ReachableNativesPass"]["analyze_load_library"] = true;
  config["PartialApplicationPass"]["cost_method"] = 0;
  auto* reachable_natives = new ReachableNativesPass();
  auto* partial_application = new PartialApplicationPass();
  run_passes({reachable_natives, partial_application, partial_application,
              reachable_natives},
             nullptr, config);

  EXPECT_EQ(7u, g_redex->library_names.size());
  const auto& metrics = pass_manager->get_pass_info().back().metrics;
  EXPECT_EQ(7, metrics.at("initial_library_names"));
  EXPECT_EQ(7, metrics.at("final_library_names"));
  for (auto* method : type_class(loader_type)->get_dmethods()) {
    EXPECT_EQ(std::string_view::npos, method->get_name()->str().find("$spa$"));
  }
}

TEST_F(PartialApplicationTest, does_not_bind_unproven_constant) {
  std::vector<Pass*> passes = {
      new PartialApplicationPass(),
  };
  Json::Value config;
  config["PartialApplicationPass"]["cost_method"] = 0;

  run_passes(passes, nullptr, config);

  auto* code = get_code(
      "Lcom/facebook/redextest/PartialApplication;.call_regression_c1:(II)V");
  std::vector<IRInstruction*> invokes;
  for (const auto& mie : InstructionIterable(code)) {
    if (opcode::is_a_method_invoke(mie.insn->opcode())) {
      invokes.push_back(mie.insn);
    }
  }

  ASSERT_EQ(1u, invokes.size());
  const auto* invoke = invokes.front();
  EXPECT_EQ(2u, invoke->srcs_size());
  EXPECT_EQ(2u, invoke->get_method()->get_proto()->get_args()->size());
}
