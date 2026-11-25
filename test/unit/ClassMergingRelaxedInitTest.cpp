/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "ClassAssemblingUtils.h"
#include "ClassMergingTestFixture.h"
#include "Creators.h"
#include "IRTypeChecker.h"
#include "MethodUtil.h"
#include "ScopeHelper.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "TypeUtil.h"

using namespace class_merging_test;

namespace {

// Relaxed init inlining turns `new A()`, with `A() { super(); }`, into
//
//   new-instance A
//   invoke-direct Base.<init>()V
//
// and deletes A's constructor once no caller is left. These tests check how
// class merging handles such sites.
class ClassMergingRelaxedInitTest : public ClassMergingTest {
 protected:
  void SetUp() override {
    m_scope = create_empty_scope();
    m_base = make_class("Lcom/redex/test/Base;", type::java_lang_Object());
    add_ctor(m_base);
    add_virtual(m_base, "run");
    m_use = make_class("Lcom/redex/test/Use;", type::java_lang_Object());
    add_method(m_use, R"(
      (method (public static) "Lcom/redex/test/Use;.log:()V"
       ((return-void)))
    )");
  }

  // A subclass of Base whose constructors were all inlined.
  DexClass* make_relaxed_mergeable(const char* name) {
    auto* cls = make_class(name, m_base->get_type());
    add_virtual(cls, "run");
    return cls;
  }

  // Adds `static make<n>()` to `owner` (by default Use), which instantiates
  // `cls` with the given constructor and calls run() on it, preceded by a
  // source block with the given value.
  DexMethod* add_site(const DexClass* cls,
                      const std::string& init,
                      float value = 1.0,
                      DexClass* owner = nullptr) {
    if (owner == nullptr) {
      owner = m_use;
    }
    auto name = "make" + std::to_string(m_num_sites++);
    auto method_name = owner->get_type()->str_copy() + "." + name + ":()V";
    std::string args = init.find("(I)") != std::string::npos ? " v1" : "";
    return add_method(owner,
                      ir(R"(
      (method (public static) "$METHOD"
       (
        (.src_block "$METHOD" 0 ($VALUE 1.0))
        (const v1 0)
        (new-instance "$CLS")
        (move-result-pseudo-object v0)
        (invoke-direct (v0$ARGS) "$INIT")
        (invoke-virtual (v0) "$CLS.run:()V")
        (return-void)
       )
      )
    )",
                         {{"$METHOD", method_name},
                          {"$VALUE", std::to_string(value)},
                          {"$CLS", cls->get_type()->str_copy()},
                          {"$ARGS", args},
                          {"$INIT", init}}));
  }

  std::string base_init() const {
    return m_base->get_type()->str_copy() + ".<init>:()V";
  }

  Json::Value model(const char* type_tag_config = "generate") {
    Json::Value model;
    model["enabled"] = true;
    model["name"] = "Relaxed";
    model["class_name_prefix"] = "Relaxed";
    model["roots"].append(m_base->get_type()->str_copy());
    model["interdex_grouping"] = "disabled";
    model["include_primary_dex"] = true;
    model["type_tag_config"] = type_tag_config;
    return model;
  }

  static int64_t metric(const UnorderedMap<std::string, int64_t>& metrics,
                        const std::string& name) {
    auto it = metrics.find("Relaxed_" + name);
    return it == metrics.end() ? -1 : it->second;
  }

  bool in_scope(const DexClass* cls) const {
    return std::find(m_scope.begin(), m_scope.end(), cls) != m_scope.end();
  }

  // The pass manager leaves the code in linear form.
  static cfg::ControlFlowGraph& cfg_of(const DexMethod* method) {
    auto* code = const_cast<DexMethod*>(method)->get_code();
    if (!code->cfg_built()) {
      code->build_cfg();
    }
    return code->cfg();
  }

  // The constructor that the given Use method's (only) constructor call
  // invokes.
  static DexMethodRef* invoked_ctor(const DexMethod* use_method) {
    DexMethodRef* ctor = nullptr;
    for (const auto& mie : cfg::InstructionIterable(cfg_of(use_method))) {
      if (mie.insn->has_method() && method::is_init(mie.insn->get_method())) {
        EXPECT_EQ(ctor, nullptr);
        ctor = mie.insn->get_method();
      }
    }
    return ctor;
  }

  static std::vector<float> source_block_values(const DexMethodRef* ctor) {
    std::vector<float> values;
    for (auto* block : cfg_of(ctor->as_def()).blocks()) {
      for (auto* sb : source_blocks::gather_source_blocks(block)) {
        if (sb->get_val(0)) {
          values.push_back(*sb->get_val(0));
        }
      }
    }
    std::sort(values.begin(), values.end());
    values.erase(std::unique(values.begin(), values.end()), values.end());
    return values;
  }

  void expect_type_correct() {
    for (auto* cls : m_scope) {
      for (auto* method : cls->get_all_methods()) {
        if (method->get_code() == nullptr) {
          continue;
        }
        cfg_of(method);
        IRTypeChecker checker(method);
        checker.relaxed_init_check();
        checker.run();
        EXPECT_TRUE(checker.good()) << show(method) << ": " << checker.what();
      }
    }
  }

  DexClass* m_use{nullptr};
  size_t m_num_sites{0};
};

TEST_F(ClassMergingRelaxedInitTest, ClassesWithOnlyRelaxedInitsMerge) {
  add_method(m_base, R"(
    (method (public constructor) "Lcom/redex/test/Base;.<init>:(I)V"
     (
      (load-param-object v0)
      (load-param v1)
      (invoke-direct (v0) "Lcom/redex/test/Base;.<init>:()V")
      (return-void)
     )
    )
  )");
  auto* a = make_relaxed_mergeable("Lcom/redex/test/A;");
  auto* b = make_relaxed_mergeable("Lcom/redex/test/B;");
  auto* make_a = add_site(a, base_init(), 3.0);
  auto* make_b =
      add_site(b, m_base->get_type()->str_copy() + ".<init>:(I)V", 5.0);

  auto metrics = run_merging({model()});

  EXPECT_EQ(metric(metrics, "class_merged"), 2);
  EXPECT_EQ(metric(metrics, "relaxed_init_ctors_created"), 2);
  EXPECT_EQ(metric(metrics, "relaxed_init_ctors_reused"), 0);
  EXPECT_EQ(metric(metrics, "relaxed_init_sites_rewritten"), 2);
  EXPECT_FALSE(in_scope(a));
  EXPECT_FALSE(in_scope(b));
  // Both sites call a constructor of the merged class, which stores the type
  // tag its callers pass.
  auto* ctor_a = invoked_ctor(make_a);
  auto* ctor_b = invoked_ctor(make_b);
  ASSERT_NE(ctor_a, nullptr);
  ASSERT_NE(ctor_b, nullptr);
  EXPECT_EQ(ctor_a->get_class(), ctor_b->get_class());
  auto* merged_cls = type_class(ctor_a->get_class());
  ASSERT_NE(merged_cls, nullptr);
  EXPECT_TRUE(merged_cls->rstate.is_generated());
  EXPECT_EQ(merged_cls->get_super_class(), m_base->get_type());
  EXPECT_EQ(show(ctor_a->get_proto()), "(I)V");
  EXPECT_EQ(show(ctor_b->get_proto()), "(II)V");
  // Each merged constructor carries the hotness of its site.
  EXPECT_EQ(source_block_values(ctor_a), std::vector<float>{3.0});
  EXPECT_EQ(source_block_values(ctor_b), std::vector<float>{5.0});
  expect_type_correct();
}

TEST_F(ClassMergingRelaxedInitTest, RelaxedAndOrdinaryConstructorsMerge) {
  auto* a = make_mergeable("Lcom/redex/test/A;");
  auto* b = make_relaxed_mergeable("Lcom/redex/test/B;");
  auto* make_a = add_site(a, a->get_type()->str_copy() + ".<init>:()V");
  auto* make_b = add_site(b, base_init());

  auto metrics = run_merging({model()});

  EXPECT_EQ(metric(metrics, "class_merged"), 2);
  EXPECT_EQ(metric(metrics, "relaxed_init_ctors_created"), 1);
  EXPECT_EQ(metric(metrics, "relaxed_init_sites_rewritten"), 1);
  // A's constructor and B's forwarding constructor are the same code.
  EXPECT_EQ(metric(metrics, "ctor_dedupped"), 1);
  EXPECT_EQ(invoked_ctor(make_a), invoked_ctor(make_b));
  expect_type_correct();
}

TEST_F(ClassMergingRelaxedInitTest, ExistingForwardingConstructorIsReused) {
  auto* a = make_mergeable("Lcom/redex/test/A;");
  auto* b = make_relaxed_mergeable("Lcom/redex/test/B;");
  auto* make_a = add_site(a, base_init());
  add_site(b, base_init());

  auto metrics = run_merging({model()});

  EXPECT_EQ(metric(metrics, "class_merged"), 2);
  EXPECT_EQ(metric(metrics, "relaxed_init_ctors_created"), 1);
  EXPECT_EQ(metric(metrics, "relaxed_init_ctors_reused"), 1);
  EXPECT_EQ(metric(metrics, "relaxed_init_sites_rewritten"), 2);
  EXPECT_NE(invoked_ctor(make_a)->get_class(), m_base->get_type());
  expect_type_correct();
}

TEST_F(ClassMergingRelaxedInitTest, DifferentConstructorWithSameProtoExcludes) {
  auto* a = make_relaxed_mergeable("Lcom/redex/test/A;");
  add_method(a, R"(
    (method (public constructor) "Lcom/redex/test/A;.<init>:()V"
     (
      (load-param-object v0)
      (invoke-direct (v0) "Lcom/redex/test/Base;.<init>:()V")
      (invoke-static () "Lcom/redex/test/Use;.log:()V")
      (return-void)
     )
    )
  )");
  auto* b = make_relaxed_mergeable("Lcom/redex/test/B;");
  auto* c = make_relaxed_mergeable("Lcom/redex/test/C;");
  auto* make_a = add_site(a, base_init());
  add_site(b, base_init());
  add_site(c, base_init());

  auto metrics = run_merging({model()});

  EXPECT_EQ(metric(metrics, "relaxed_init_excluded_ctor_conflict"), 1);
  EXPECT_EQ(metric(metrics, "class_merged"), 2);
  EXPECT_TRUE(in_scope(a));
  EXPECT_EQ(show(invoked_ctor(make_a)), base_init());
  expect_type_correct();
}

TEST_F(ClassMergingRelaxedInitTest, UnresolvedConstructorExcludes) {
  auto* a = make_relaxed_mergeable("Lcom/redex/test/A;");
  auto* b = make_relaxed_mergeable("Lcom/redex/test/B;");
  auto* c = make_relaxed_mergeable("Lcom/redex/test/C;");
  add_site(a, m_base->get_type()->str_copy() + ".<init>:(I)V");
  add_site(b, base_init());
  add_site(c, base_init());

  auto metrics = run_merging({model()});

  EXPECT_EQ(metric(metrics, "relaxed_init_excluded_unsupported"), 1);
  EXPECT_EQ(metric(metrics, "class_merged"), 2);
  EXPECT_TRUE(in_scope(a));
}

// A class that another check already excludes is not also counted as a
// relaxed-init exclusion.
TEST_F(ClassMergingRelaxedInitTest, ExcludedClassIsNotCountedAgain) {
  auto* a = make_relaxed_mergeable("Lcom/redex/test/A;");
  auto* b = make_relaxed_mergeable("Lcom/redex/test/B;");
  auto* c = make_relaxed_mergeable("Lcom/redex/test/C;");
  add_site(a, m_base->get_type()->str_copy() + ".<init>:(I)V");
  add_site(b, base_init());
  add_site(c, base_init());
  add_method(m_use, R"(
    (method (public static) "Lcom/redex/test/Use;.cls:()Ljava/lang/Class;"
     ((const-class "Lcom/redex/test/A;")
      (move-result-pseudo-object v0)
      (return-object v0)))
  )");

  auto metrics = run_merging({model()});

  EXPECT_EQ(metric(metrics, "relaxed_init_excluded_unsupported"), 0);
  EXPECT_EQ(metric(metrics, "class_merged"), 2);
  EXPECT_TRUE(in_scope(a));
}

TEST_F(ClassMergingRelaxedInitTest, InaccessibleExternalConstructorExcludes) {
  // An external super type whose constructor is package-private.
  auto* ext_type = DexType::make_type("Lext/Ext;");
  ClassCreator creator(ext_type);
  creator.set_super(type::java_lang_Object());
  creator.set_external();
  auto* ext_init =
      dynamic_cast<DexMethod*>(DexMethod::make_method("Lext/Ext;.<init>:()V"));
  ext_init->set_access(ACC_CONSTRUCTOR);
  ext_init->set_external();
  creator.add_method(ext_init);
  creator.create();
  m_base->set_super_class(ext_type);

  auto* a = make_relaxed_mergeable("Lcom/redex/test/A;");
  auto* b = make_relaxed_mergeable("Lcom/redex/test/B;");
  add_site(a, "Lext/Ext;.<init>:()V");
  add_site(b, "Lext/Ext;.<init>:()V");

  auto metrics = run_merging({model()});

  EXPECT_EQ(metric(metrics, "relaxed_init_excluded_inaccessible"), 2);
  EXPECT_EQ(metric(metrics, "class_merged"), 0);
  EXPECT_TRUE(in_scope(a));
  EXPECT_TRUE(in_scope(b));
}

TEST_F(ClassMergingRelaxedInitTest, NoTypeTagExcludes) {
  auto* a = make_relaxed_mergeable("Lcom/redex/test/A;");
  auto* b = make_relaxed_mergeable("Lcom/redex/test/B;");
  add_site(a, base_init());
  add_site(b, base_init());

  auto metrics = run_merging({model("none")});

  EXPECT_EQ(metric(metrics, "relaxed_init_excluded_type_tag_not_generated"), 2);
  EXPECT_TRUE(in_scope(a));
  EXPECT_TRUE(in_scope(b));
}

TEST_F(ClassMergingRelaxedInitTest, InputHandledTypeTagExcludes) {
  auto* a = make_relaxed_mergeable("Lcom/redex/test/A;");
  auto* b = make_relaxed_mergeable("Lcom/redex/test/B;");
  add_site(a, base_init());
  add_site(b, base_init());

  auto metrics = run_merging({model("input-handled")});

  EXPECT_EQ(metric(metrics, "relaxed_init_excluded_type_tag_not_generated"), 2);
  EXPECT_TRUE(in_scope(a));
  EXPECT_TRUE(in_scope(b));
}

// When the input passes the type tag to the constructors, no merged
// constructor stores the tag that a forwarding constructor would pass.
TEST_F(ClassMergingRelaxedInitTest, InputPassTypeTagExcludes) {
  auto* a = make_relaxed_mergeable("Lcom/redex/test/A;");
  auto* b = make_relaxed_mergeable("Lcom/redex/test/B;");
  add_site(a, base_init());
  add_site(b, base_init());

  auto metrics = run_merging({model("input-pass-type-tag-to-ctor")});

  EXPECT_EQ(metric(metrics, "relaxed_init_excluded_type_tag_not_generated"), 2);
  EXPECT_TRUE(in_scope(a));
  EXPECT_TRUE(in_scope(b));
}

// A constructor without code with the forwarder's proto cannot be reused.
TEST_F(ClassMergingRelaxedInitTest, ConstructorWithoutCodeConflicts) {
  auto* a = make_relaxed_mergeable("Lcom/redex/test/A;");
  auto* b = make_relaxed_mergeable("Lcom/redex/test/B;");
  auto* c = make_relaxed_mergeable("Lcom/redex/test/C;");
  auto* native_ctor =
      DexMethod::make_method("Lcom/redex/test/A;.<init>:()V")
          ->make_concrete(ACC_PUBLIC | ACC_CONSTRUCTOR | ACC_NATIVE, false);
  a->add_method(native_ctor);
  add_site(a, base_init());
  add_site(b, base_init());
  add_site(c, base_init());

  auto metrics = run_merging({model()});

  EXPECT_EQ(metric(metrics, "relaxed_init_excluded_ctor_conflict"), 1);
  EXPECT_TRUE(in_scope(a));
}

// One constructor call that initializes objects of two types, depending on the
// path, cannot point at either type's forwarding constructor.
TEST_F(ClassMergingRelaxedInitTest, SharedConstructorCallExcludes) {
  auto* a = make_relaxed_mergeable("Lcom/redex/test/A;");
  auto* b = make_relaxed_mergeable("Lcom/redex/test/B;");
  auto* c = make_relaxed_mergeable("Lcom/redex/test/C;");
  auto* d = make_relaxed_mergeable("Lcom/redex/test/D;");
  add_method(m_use, R"(
    (method (public static) "Lcom/redex/test/Use;.either:(Z)V"
     ((load-param v1)
      (if-eqz v1 :b)
      (new-instance "Lcom/redex/test/A;")
      (move-result-pseudo-object v0)
      (goto :init)
      (:b)
      (new-instance "Lcom/redex/test/B;")
      (move-result-pseudo-object v0)
      (:init)
      (invoke-direct (v0) "Lcom/redex/test/Base;.<init>:()V")
      (return-void)))
  )");
  add_site(c, base_init());
  add_site(d, base_init());

  auto metrics = run_merging({model()});

  EXPECT_EQ(metric(metrics, "relaxed_init_excluded_unsupported"), 2);
  EXPECT_EQ(metric(metrics, "class_merged"), 2);
  EXPECT_TRUE(in_scope(a));
  EXPECT_TRUE(in_scope(b));
}

// Class merging models treat their classes as generated code by default, and
// skip most bytecode checks in their methods, but not the relaxed init ones.
TEST_F(ClassMergingRelaxedInitTest, RelaxedInitInGeneratedCodeMerges) {
  auto* a = make_mergeable("Lcom/redex/test/A;");
  auto* b = make_mergeable("Lcom/redex/test/B;");
  make_mergeable("Lcom/redex/test/C;");
  auto* make_a = add_site(a, base_init(), 1.0, /* owner */ b);

  auto metrics = run_merging({model()});

  EXPECT_FALSE(in_scope(a));
  EXPECT_EQ(metric(metrics, "class_merged"), 3);
  EXPECT_EQ(metric(metrics, "relaxed_init_ctors_reused"), 1);
  EXPECT_EQ(metric(metrics, "relaxed_init_sites_rewritten"), 1);
  EXPECT_NE(invoked_ctor(make_a)->get_class(), m_base->get_type());
  expect_type_correct();
}

TEST_F(ClassMergingRelaxedInitTest, UnmergedClassIsLeftAlone) {
  auto* a = make_relaxed_mergeable("Lcom/redex/test/A;");
  auto* make_a = add_site(a, base_init());

  auto metrics = run_merging({model()});

  EXPECT_EQ(metric(metrics, "class_merged"), 0);
  EXPECT_EQ(metric(metrics, "relaxed_init_ctors_created"), 0);
  EXPECT_TRUE(in_scope(a));
  EXPECT_TRUE(a->get_ctors().empty());
  EXPECT_EQ(show(invoked_ctor(make_a)), base_init());
}

TEST_F(ClassMergingRelaxedInitTest, IsForwardingCtor) {
  auto* super_ctor =
      DexMethod::make_method("Lcom/redex/test/Base;.<init>:(JI)V");
  auto ctor = [&](const char* name, const char* body) {
    auto* method = assembler::method_from_string(
        std::string("(method (public constructor) \"Lcom/redex/test/A;.") +
        name + ":(JI)V\" " + body + ")");
    method->get_code()->build_cfg();
    return method;
  };
  // The methods get distinct names so that they can coexist; only the body and
  // the proto matter.
  EXPECT_TRUE(class_merging::is_forwarding_ctor(ctor("<init>", R"(
        ((load-param-object v0)
         (load-param-wide v1)
         (load-param v2)
         (invoke-direct (v0 v1 v2) "Lcom/redex/test/Base;.<init>:(JI)V")
         (return-void)))"),
                                                super_ctor));
  EXPECT_FALSE(class_merging::is_forwarding_ctor(ctor("other1", R"(
        ((load-param-object v0)
         (load-param-wide v1)
         (load-param v2)
         (invoke-direct (v0 v1 v2) "Lcom/redex/test/Base;.<init>:(JI)V")
         (invoke-static () "Lcom/redex/test/Use;.log:()V")
         (return-void)))"),
                                                 super_ctor));
  EXPECT_FALSE(class_merging::is_forwarding_ctor(ctor("other2", R"(
        ((load-param-object v0)
         (load-param-wide v1)
         (load-param v2)
         (const v2 0)
         (invoke-direct (v0 v1 v2) "Lcom/redex/test/Base;.<init>:(JI)V")
         (return-void)))"),
                                                 super_ctor));
  EXPECT_FALSE(class_merging::is_forwarding_ctor(ctor("other3", R"(
        ((load-param-object v0)
         (load-param-wide v1)
         (load-param v2)
         (return-void)))"),
                                                 super_ctor));
  // A handler with no instructions of its own still catches what the super
  // constructor throws.
  EXPECT_FALSE(class_merging::is_forwarding_ctor(ctor("other4", R"(
        ((load-param-object v0)
         (load-param-wide v1)
         (load-param v2)
         (.try_start a)
         (invoke-direct (v0 v1 v2) "Lcom/redex/test/Base;.<init>:(JI)V")
         (.try_end a)
         (:ret)
         (return-void)
         (.catch (a))
         (goto :ret)))"),
                                                 super_ctor));
}

} // namespace
