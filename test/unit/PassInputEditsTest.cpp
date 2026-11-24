/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "PassInputEdits.h"

#include <gtest/gtest-spi.h>
#include <gtest/gtest.h>

#include "Creators.h"
#include "IRAssembler.h"
#include "RedexTest.h"
#include "Show.h"
#include "Walkers.h"

using namespace pass_input_edits;

namespace {

/*
 * class Base { static int base() { return 1; } }
 * class Sub extends Base {}
 * class Foo {
 *   static int sink;          // written, never read
 *   static { sink = 1; }
 *   static int helper() { return 42; }
 *   static int use() { return helper() + Sub.base(); }
 *   private static void unused() {}
 * }
 */
DexStoresVector make_input() {
  ClassCreator base(DexType::make_type("LBase;"));
  base.set_super(type::java_lang_Object());
  base.add_method(assembler::method_from_string(R"(
    (method (public static) "LBase;.base:()I"
      (
        (const v0 1)
        (return v0)
      )
    )
  )"));
  ClassCreator sub(DexType::make_type("LSub;"));
  sub.set_super(DexType::make_type("LBase;"));

  ClassCreator foo(DexType::make_type("LFoo;"));
  foo.set_super(type::java_lang_Object());
  auto* sink = DexField::make_field("LFoo;.sink:I")
                   ->make_concrete(ACC_PUBLIC | ACC_STATIC);
  foo.add_field(sink);
  foo.add_method(assembler::method_from_string(R"(
    (method (public static constructor) "LFoo;.<clinit>:()V"
      (
        (const v0 1)
        (sput v0 "LFoo;.sink:I")
        (return-void)
      )
    )
  )"));
  foo.add_method(assembler::method_from_string(R"(
    (method (public static) "LFoo;.helper:()I"
      (
        (const v0 42)
        (return v0)
      )
    )
  )"));
  foo.add_method(assembler::method_from_string(R"(
    (method (public static) "LFoo;.use:()I"
      (
        (invoke-static () "LFoo;.helper:()I")
        (move-result v0)
        (invoke-static () "LSub;.base:()I")
        (move-result v1)
        (add-int v0 v0 v1)
        (return v0)
      )
    )
  )"));
  foo.add_method(assembler::method_from_string(R"(
    (method (private static) "LFoo;.unused:()V"
      (
        (return-void)
      )
    )
  )"));
  DexMetadata metadata;
  metadata.set_id("classes");
  DexStore store(metadata);
  store.add_classes({base.create(), sub.create(), foo.create()});
  DexStoresVector stores;
  stores.emplace_back(std::move(store));
  walk::code(build_class_scope(stores),
             [](DexMethod*, IRCode& code) { code.build_cfg(); });
  return stores;
}

std::vector<std::unique_ptr<Pass>> no_passes() { return {}; }

// Aborts unless `LFoo;.sink` is still declared, like a pass that assumes a
// field it found once is always there.
class RequiresSinkPass : public Pass {
 public:
  RequiresSinkPass() : Pass("RequiresSinkPass") {}

  redex_properties::PropertyInteractions get_property_interactions()
      const override {
    return redex_properties::simple::preserves_all();
  }

  void run_pass(DexStoresVector&, ConfigFiles&, PassManager&) override {
    auto* sink = DexField::get_field("LFoo;.sink:I");
    always_assert_log(sink != nullptr && sink->is_def(),
                      "LFoo;.sink is not declared");
  }
};

// Leaves the input alone when `LFoo;.sink` is missing, and records in
// `rejected` whether it did. The harness destroys the pass after its run, so
// the verdict lives outside it.
class RejectsMissingSinkPass : public Pass {
 public:
  explicit RejectsMissingSinkPass(bool& rejected)
      : Pass("RejectsMissingSinkPass"), m_rejected(rejected) {}

  redex_properties::PropertyInteractions get_property_interactions()
      const override {
    return redex_properties::simple::preserves_all();
  }

  void run_pass(DexStoresVector&, ConfigFiles&, PassManager&) override {
    auto* sink = DexField::get_field("LFoo;.sink:I");
    m_rejected = sink == nullptr || !sink->is_def();
  }

 private:
  bool& m_rejected;
};

} // namespace

class PassInputEditsTest : public RedexTest {
 protected:
  PassInputEditsTest() : m_conf(Json::nullValue) {
    m_conf.parse_global_config();
    m_conf.set_outdir(m_dir.path);
  }

  redex::TempDir m_dir{redex::make_tmp_dir("PassInputEditsTest%%%%%%%%")};
  ConfigFiles m_conf;
};

TEST_F(PassInputEditsTest, countsEachEditsSites) {
  auto stores = make_input();
  // `Foo.use` and `Foo.unused`; `Base.base` is called through `Sub`.
  EXPECT_EQ(
      describe_sites(Edit::DeleteUnreferencedMethod, stores, m_conf).size(), 2);
  EXPECT_EQ(
      describe_sites(Edit::RemoveUnreadFieldWrites, stores, m_conf).size(), 1);
  EXPECT_EQ(describe_sites(Edit::DeleteUnreadFields, stores, m_conf).size(), 1);
  EXPECT_EQ(describe_sites(Edit::InlineCall, stores, m_conf).size(), 2);
}

// class Holder {
//   volatile int v;
//   private static void touch(Holder h) { h.v = 1; }
// }
TEST_F(PassInputEditsTest, deletingAMethodKeepsVolatileInstanceFields) {
  ClassCreator holder(DexType::make_type("LHolder;"));
  holder.set_super(type::java_lang_Object());
  holder.add_field(DexField::make_field("LHolder;.v:I")
                       ->make_concrete(ACC_PUBLIC | ACC_VOLATILE));
  holder.add_method(assembler::method_from_string(R"(
    (method (private static) "LHolder;.touch:(LHolder;)V"
      (
        (load-param-object v0)
        (const v1 1)
        (iput v1 v0 "LHolder;.v:I")
        (return-void)
      )
    )
  )"));
  DexMetadata metadata;
  metadata.set_id("classes");
  DexStore store(metadata);
  store.add_classes({holder.create()});
  DexStoresVector stores;
  stores.emplace_back(std::move(store));
  walk::code(build_class_scope(stores),
             [](DexMethod*, IRCode& code) { code.build_cfg(); });

  EXPECT_EQ(apply(Edit::DeleteUnreferencedMethod, 0, stores, m_conf),
            "delete LHolder;.touch:(LHolder;)V");
  EXPECT_NE(DexField::get_field("LHolder;.v:I"), nullptr);
}

TEST_F(PassInputEditsTest, describesEachInlinableCall) {
  auto stores = make_input();
  EXPECT_EQ(describe_sites(Edit::InlineCall, stores, m_conf),
            (std::vector<std::string>{
                "inline LFoo;.helper:()I into LFoo;.use:()I, call 1",
                "inline LBase;.base:()I into LFoo;.use:()I, call 2",
            }));
}

// class Twice {
//   static int one() { return 1; }
//   static int two() { return one() + one(); }
// }
TEST_F(PassInputEditsTest, numbersTheCallsOfOneMethodInACaller) {
  ClassCreator twice(DexType::make_type("LTwice;"));
  twice.set_super(type::java_lang_Object());
  twice.add_method(assembler::method_from_string(R"(
    (method (public static) "LTwice;.one:()I"
      (
        (const v0 1)
        (return v0)
      )
    )
  )"));
  twice.add_method(assembler::method_from_string(R"(
    (method (public static) "LTwice;.two:()I"
      (
        (invoke-static () "LTwice;.one:()I")
        (move-result v0)
        (invoke-static () "LTwice;.one:()I")
        (move-result v1)
        (add-int v0 v0 v1)
        (return v0)
      )
    )
  )"));
  DexMetadata metadata;
  metadata.set_id("classes");
  DexStore store(metadata);
  store.add_classes({twice.create()});
  DexStoresVector stores;
  stores.emplace_back(std::move(store));
  walk::code(build_class_scope(stores),
             [](DexMethod*, IRCode& code) { code.build_cfg(); });

  EXPECT_EQ(describe_sites(Edit::InlineCall, stores, m_conf),
            (std::vector<std::string>{
                "inline LTwice;.one:()I into LTwice;.two:()I, call 1",
                "inline LTwice;.one:()I into LTwice;.two:()I, call 2",
            }));
}

// class Keeper {
//   static Object o;  // never read
//   static void keep(Object x) { o = x; }
// }
// RemoveUnusedFieldsPass keeps `o = x`, which may be what keeps `x` alive, so
// there is no unread field write to remove.
TEST_F(PassInputEditsTest, unreadFieldSitesAreWritesThePassRemoves) {
  ClassCreator keeper(DexType::make_type("LKeeper;"));
  keeper.set_super(type::java_lang_Object());
  keeper.add_field(DexField::make_field("LKeeper;.o:Ljava/lang/Object;")
                       ->make_concrete(ACC_PUBLIC | ACC_STATIC));
  keeper.add_method(assembler::method_from_string(R"(
    (method (public static) "LKeeper;.keep:(Ljava/lang/Object;)V"
      (
        (load-param-object v0)
        (sput-object v0 "LKeeper;.o:Ljava/lang/Object;")
        (return-void)
      )
    )
  )"));
  DexMetadata metadata;
  metadata.set_id("classes");
  DexStore store(metadata);
  store.add_classes({keeper.create()});
  DexStoresVector stores;
  stores.emplace_back(std::move(store));
  walk::code(build_class_scope(stores),
             [](DexMethod*, IRCode& code) { code.build_cfg(); });

  EXPECT_TRUE(
      describe_sites(Edit::RemoveUnreadFieldWrites, stores, m_conf).empty());
  EXPECT_TRUE(describe_sites(Edit::DeleteUnreadFields, stores, m_conf).empty());
}

TEST_F(PassInputEditsTest, inlineCallReplacesTheCallAndTheLastCallee) {
  auto stores = make_input();
  EXPECT_EQ(apply(Edit::InlineCall, 0, stores, m_conf),
            "inline LFoo;.helper:()I into LFoo;.use:()I, call 1");
  auto* use = DexMethod::get_method("LFoo;.use:()I")->as_def();
  for (const auto& mie : cfg::InstructionIterable(use->get_code()->cfg())) {
    EXPECT_FALSE(mie.insn->has_method() &&
                 mie.insn->get_method()->get_name()->str() == "helper")
        << show(mie.insn);
  }
  EXPECT_EQ(DexMethod::get_method("LFoo;.helper:()I"), nullptr);
}

TEST_F(PassInputEditsTest, removeUnreadFieldWritesKeepsTheField) {
  auto stores = make_input();
  EXPECT_EQ(apply(Edit::RemoveUnreadFieldWrites, 0, stores, m_conf),
            "remove the writes of the unread fields of LFoo;");
  auto* sink = DexField::get_field("LFoo;.sink:I");
  ASSERT_NE(sink, nullptr);
  EXPECT_TRUE(sink->is_def());
  auto* clinit = DexMethod::get_method("LFoo;.<clinit>:()V")->as_def();
  for (const auto& mie : cfg::InstructionIterable(clinit->get_code()->cfg())) {
    EXPECT_FALSE(opcode::is_an_sput(mie.insn->opcode())) << show(mie.insn);
  }
}

TEST_F(PassInputEditsTest, deleteUnreadFieldsDeletesTheField) {
  auto stores = make_input();
  EXPECT_EQ(apply(Edit::DeleteUnreadFields, 0, stores, m_conf),
            "delete the unread fields of LFoo;");
  EXPECT_EQ(DexField::get_field("LFoo;.sink:I"), nullptr);
}

TEST_F(PassInputEditsTest, deletingAMethodDeletesWhatOnlyItUsed) {
  auto stores = make_input();
  EXPECT_EQ(apply(Edit::DeleteUnreferencedMethod, 1, stores, m_conf),
            "delete LFoo;.use:()I");
  EXPECT_EQ(DexMethod::get_method("LFoo;.use:()I"), nullptr);
  EXPECT_EQ(DexMethod::get_method("LFoo;.helper:()I"), nullptr);
  EXPECT_EQ(DexMethod::get_method("LBase;.base:()I"), nullptr);
  // `unused` and `sink` were unreferenced before the edit, so they stay.
  EXPECT_NE(DexMethod::get_method("LFoo;.unused:()V"), nullptr);
  EXPECT_NE(DexField::get_field("LFoo;.sink:I"), nullptr);
}

TEST_F(PassInputEditsTest, abortIsReportedWithItsEdit) {
  EXPECT_NONFATAL_FAILURE(
      check_passes_never_abort(make_input,
                               {.before_edits = no_passes,
                                .after_edits =
                                    [] {
                                      std::vector<std::unique_ptr<Pass>> passes;
                                      passes.push_back(
                                          std::make_unique<RequiresSinkPass>());
                                      return passes;
                                    }},
                               Json::nullValue, {}),
      "Aborted after DeleteUnreadFields site 0: delete the unread fields of "
      "LFoo;");
}

// Deletes `LFoo;.unused` in the first RedexContext of the process only, like
// a pass that keeps a method of an earlier context in a static. Each test uses
// its own instantiation.
template <int>
class FirstContextOnlyPass : public Pass {
 public:
  FirstContextOnlyPass() : Pass("FirstContextOnlyPass") {}

  redex_properties::PropertyInteractions get_property_interactions()
      const override {
    return redex_properties::simple::preserves_all();
  }

  void run_pass(DexStoresVector&, ConfigFiles&, PassManager&) override {
    static bool s_ran = false;
    if (!s_ran) {
      s_ran = true;
      auto* unused = DexMethod::get_method("LFoo;.unused:()V")->as_def();
      type_class(unused->get_class())->remove_method(unused);
    }
  }
};

template <typename P>
std::vector<std::unique_ptr<Pass>> make_pass() {
  std::vector<std::unique_ptr<Pass>> passes;
  passes.push_back(std::make_unique<P>());
  return passes;
}

TEST_F(PassInputEditsTest, earlierPassThatDiffersInANewContextIsReported) {
  EXPECT_NONFATAL_FAILURE(
      check_passes_never_abort(
          make_input,
          {.before_edits = make_pass<FirstContextOnlyPass<0>>,
           .after_edits = no_passes},
          Json::nullValue, {}, {Edit::DeleteUnreferencedMethod}),
      "gave a different input than the first time");
}

TEST_F(PassInputEditsTest, passUnderTestThatDiffersInANewContextIsReported) {
  EXPECT_NONFATAL_FAILURE(
      check_passes_never_abort(
          make_input,
          {.before_edits = no_passes,
           .after_edits = make_pass<FirstContextOnlyPass<1>>},
          Json::nullValue, {}, {}),
      "The passes under test gave a different output in a new RedexContext");
}

TEST_F(PassInputEditsTest, everyRunWithoutAbortIsChecked) {
  std::vector<std::string> checked;
  size_t rejections = 0;
  bool rejected = false;
  check_passes_never_abort(
      make_input,
      {.before_edits = no_passes,
       .after_edits =
           [&] {
             std::vector<std::unique_ptr<Pass>> passes;
             passes.push_back(
                 std::make_unique<RejectsMissingSinkPass>(rejected));
             return passes;
           }},
      Json::nullValue,
      {.before = nullptr,
       .after = [&](DexStoresVector&, ConfigFiles&,
                    const std::string& description) {
         checked.push_back(description);
         rejections += rejected ? 1 : 0;
       }});
  EXPECT_EQ(
      checked,
      std::vector<std::string>({
          "no edit: input as built",
          "DeleteUnreferencedMethod site 0: delete LFoo;.unused:()V",
          "DeleteUnreferencedMethod site 1: delete LFoo;.use:()I",
          ("RemoveUnreadFieldWrites site 0: remove the writes of the "
           "unread fields of LFoo;"),
          "DeleteUnreadFields site 0: delete the unread fields of LFoo;",
          ("InlineCall site 0: inline LFoo;.helper:()I into LFoo;.use:()I, "
           "call 1"),
          ("InlineCall site 1: inline LBase;.base:()I into LFoo;.use:()I, "
           "call 2"),
      }));
  EXPECT_EQ(rejections, 1);
}
