/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "Debug.h"
#include "InsertSourceBlocks.h"

#include <algorithm>
#include <array>
#include <cinttypes>
#include <cstdio>
#include <fstream>
#include <string>
#include <string_view>

#include <gtest/gtest.h>

#include "DeterministicContainers.h"
#include "DexClass.h"
#include "Inliner.h"
#include "InlinerConfig.h"
#include "RedexContext.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"
#include "ScopedCFG.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "SourceBlocksViolations.h"
#include "Walkers.h"

class SourceBlocksTest : public RedexIntegrationTest {
 public:
  SourceBlocksTest() {
    // The loading code in integ-test does not insert deobfuscated names.
    walk::methods(*classes, [](auto* m) {
      always_assert(m->get_deobfuscated_name_or_null() == nullptr);
      m->set_deobfuscated_name(show(m));
    });
  }

  ConfigFiles config_files = ConfigFiles(Json::nullValue);

 protected:
  void enable_pass(InsertSourceBlocksPass& isbp) { isbp.m_force_run = true; }
  void enable_always_inject(InsertSourceBlocksPass& isbp) {
    isbp.m_always_inject = true;
  }
  void disable_always_inject(InsertSourceBlocksPass& isbp) {
    isbp.m_always_inject = false;
  }
  void set_insert_after_excs(InsertSourceBlocksPass& isbp, bool val) {
    isbp.m_insert_after_excs = val;
  }
  void set_profile(InsertSourceBlocksPass& isbp, std::string&& val) {
    isbp.m_profile_files = val;
  }
  void set_force_serialize(InsertSourceBlocksPass& isbp) {
    isbp.m_force_serialize = true;
  }
  void set_fix_violations(InsertSourceBlocksPass& isbp) {
    isbp.m_fix_violations = true;
  }

  template <bool kFull>
  std::string get_blocks_as_txt_impl(const cfg::ControlFlowGraph& cfg) {
    std::ostringstream oss;
    bool first = true;
    for (auto* block : cfg.blocks()) {
      if (first) {
        first = false;
      } else {
        oss << "\n";
      }
      oss << "B" << block->id() << ":";
      auto vec = source_blocks::gather_source_blocks(block);
      for (auto* sb : vec) {
        oss << " ";
        if (kFull) {
          oss << sb->src->str() << "@";
        }
        oss << sb->id;
        if (sb->vals_size > 0) {
          oss << "(";
          bool first_val = true;
          for (size_t i = 0; i < sb->vals_size; i++) {
            const auto& val = sb->get_at(i);
            if (!first_val) {
              oss << "|";
            }
            first_val = false;
            if (val) {
              oss << val->val << ":" << val->appear100;
            } else {
              oss << "x";
            }
          }
          oss << ")";
        }
      }
    }
    return oss.str();
  }

  std::string get_blocks_as_txt(const cfg::ControlFlowGraph& cfg) {
    return get_blocks_as_txt_impl<false>(cfg);
  }

  std::string get_blocks_as_txt_full(const cfg::ControlFlowGraph& cfg) {
    return get_blocks_as_txt_impl<true>(cfg);
  }

  void insert_source_block_vals(DexMethod* method,
                                const SourceBlock::Val& val) {
    cfg::ScopedCFG cfg{method->get_code()};
    uint32_t id = 0;
    for (auto* b : cfg->blocks()) {
      std::vector<SourceBlock::Val> vals{val};
      source_blocks::impl::BlockAccessor::push_source_block(
          b,
          std::make_unique<SourceBlock>(method->get_deobfuscated_name_or_null(),
                                        id++, std::move(vals)));
    }
  }

  bool has_any_source_block_positive_val(DexMethod* method) {
    for (auto& mie : *method->get_code()) {
      if (mie.type == MFLOW_SOURCE_BLOCK &&
          source_blocks::has_source_block_positive_val(mie.src_block.get())) {
        return true;
      }
    }
    return false;
  }

  bool have_all_source_block_positive_val(DexMethod* method) {
    for (auto& mie : *method->get_code()) {
      if (mie.type == MFLOW_SOURCE_BLOCK &&
          !source_blocks::has_source_block_positive_val(mie.src_block.get())) {
        return false;
      }
    }
    return true;
  }
};

TEST_F(SourceBlocksTest, source_blocks) {
  auto* type = DexType::get_type("Lcom/facebook/redextest/SourceBlocksTest;");
  ASSERT_NE(type, nullptr);
  auto* cls = type_class(type);
  ASSERT_NE(cls, nullptr);

  // Check that no code has source blocks so far.
  {
    for (const auto* m : cls->get_all_methods()) {
      if (m->get_code() == nullptr) {
        continue;
      }
      for (const auto& mie : *m->get_code()) {
        ASSERT_NE(mie.type, MFLOW_SOURCE_BLOCK);
      }
    }
  }

  // Run the pass, check that each block has a SourceBlock.
  {
    InsertSourceBlocksPass isbp{};
    run_passes({&isbp}, nullptr, Json::nullValue, [&](const auto&) {
      enable_pass(isbp);
      enable_always_inject(isbp);
      set_insert_after_excs(isbp, false);
    });

    for (auto* m : cls->get_all_methods()) {
      if (m->get_code() == nullptr) {
        continue;
      }
      cfg::ScopedCFG cfg{m->get_code()};
      UnorderedSet<uint32_t> seen_ids;
      for (const auto* b : cfg->blocks()) {
        bool seen_source_block_in_b{false};
        for (const auto& mie : *b) {
          if (mie.type != MFLOW_SOURCE_BLOCK) {
            continue;
          }

          EXPECT_FALSE(seen_source_block_in_b);
          seen_source_block_in_b = true;

          ASSERT_TRUE(mie.src_block != nullptr);

          EXPECT_EQ(seen_ids.count(mie.src_block->id), 0u);
          seen_ids.insert(mie.src_block->id);

          if (m->get_name()->str().substr(0, 7) != "access$") {
            EXPECT_EQ(mie.src_block->src, m->get_deobfuscated_name_or_null());
          }
        }
        EXPECT_TRUE(seen_source_block_in_b);
      }
    }
  }

  // Run inliner, check that we have mix now.
  {
    inliner::InlinerConfig conf{};
    auto scope = build_class_scope(stores);
    walk::parallel::code(scope, [&](auto*, IRCode& code) { code.build_cfg(); });
    conf.populate(scope);
    init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
        scope, /* create_init_class_insns */ false);

    ConcurrentMethodResolverDeprecated concurrent_method_resolver;

    auto* baz_ref = DexMethod::get_method(
        "Lcom/facebook/redextest/SourceBlocksTest;.baz:(Ljava/lang/"
        "String;)V");
    ASSERT_NE(baz_ref, nullptr);
    auto* baz = baz_ref->as_def();
    ASSERT_NE(baz, nullptr);
    UnorderedSet<DexMethod*> def_inlinables{baz};

    int min_sdk = 0;
    MultiMethodInliner inliner(scope, init_classes_with_side_effects, stores,
                               config_files, def_inlinables,
                               std::ref(concurrent_method_resolver), conf,
                               min_sdk, MultiMethodInlinerMode::IntraDex);
    inliner.inline_methods();
    walk::parallel::code(scope, [&](auto*, IRCode& code) { code.clear_cfg(); });

    ASSERT_EQ(inliner.get_inlined().size(), 1u);

    auto* bar_ref = DexMethod::get_method(
        "Lcom/facebook/redextest/SourceBlocksTest;.bar:()V");
    ASSERT_NE(bar_ref, nullptr);
    auto* bar = bar_ref->as_def();
    ASSERT_NE(bar, nullptr);

    UnorderedSet<DexMethodRef*> seen_methods;
    {
      cfg::ScopedCFG cfg{bar->get_code()};
      for (const auto* b : cfg->blocks()) {
        for (const auto& mie : *b) {
          if (mie.type != MFLOW_SOURCE_BLOCK) {
            continue;
          }
          ASSERT_TRUE(mie.src_block != nullptr);
          seen_methods.insert(
              DexMethod::get_method(mie.src_block->src->str_copy()));
        }
      }
    }
    EXPECT_EQ(seen_methods.size(), 2);
    EXPECT_EQ(seen_methods.count(bar_ref), 1);
    EXPECT_EQ(seen_methods.count(baz_ref), 1);

    std::string bar_str = assembler::to_string(bar->get_code());
    EXPECT_EQ(bar_str,
              "((load-param-object v1) (.pos:dbg_0 "
              "\"Lcom/facebook/redextest/SourceBlocksTest;.bar:()V\" "
              "SourceBlocksTest.java 18) (.src_block "
              "\"Lcom/facebook/redextest/SourceBlocksTest;.bar:()V\" 0)"
              " (const-string World) (move-result-pseudo-object v0) "
              "(move-object v2 v1) (move-object v3 v0) (.pos:dbg_1 "
              "\"Lcom/facebook/redextest/SourceBlocksTest;.baz:(Ljava/lang/"
              "String;)V\" SourceBlocksTest.java 22 dbg_0) (.src_block "
              "\"Lcom/facebook/redextest/SourceBlocksTest;.baz:(Ljava/lang/"
              "String;)V\" 0) (iput-object v3 v2 "
              "\"Lcom/facebook/redextest/SourceBlocksTest;.mHello:Ljava/lang/"
              "String;\") (.pos:dbg_2 "
              "\"Lcom/facebook/redextest/SourceBlocksTest;.bar:()V\" "
              "SourceBlocksTest.java 19) (return-void))");

    // Also check the assembler in a full-circle check.
    auto code = assembler::ircode_from_string(bar_str);
    auto code_str = assembler::to_string(code.get());
    EXPECT_EQ(bar_str, code_str);
  }
}

TEST_F(SourceBlocksTest, source_blocks_insert_after_exc) {
  auto* type = DexType::get_type("Lcom/facebook/redextest/SourceBlocksTest;");
  ASSERT_NE(type, nullptr);
  auto* cls = type_class(type);
  ASSERT_NE(cls, nullptr);

  // Check that no code has source blocks so far.
  {
    for (const auto* m : cls->get_all_methods()) {
      if (m->get_code() == nullptr) {
        continue;
      }
      for (const auto& mie : *m->get_code()) {
        ASSERT_NE(mie.type, MFLOW_SOURCE_BLOCK);
      }
    }
  }

  // Run the pass, check that each block has some SourceBlocks.
  {
    InsertSourceBlocksPass isbp{};
    run_passes({&isbp}, nullptr, Json::nullValue, [&](const auto&) {
      enable_pass(isbp);
      enable_always_inject(isbp);
      set_insert_after_excs(isbp, true);
    });
  }

  const UnorderedMap<std::string, size_t> kMaxSeen = {
      {"Lcom/facebook/redextest/SourceBlocksTest;.bar:()V", 3},
      {"Lcom/facebook/redextest/SourceBlocksTest;.foo:()V", 4},
      {"Lcom/facebook/redextest/SourceBlocksTest;.<init>:()V", 3},
      {"Lcom/facebook/redextest/SourceBlocksTest;.baz:(Ljava/lang/String;)V",
       2},
      {"Lcom/facebook/redextest/SourceBlocksTest;.bazz:()V", 2},
      {"Lcom/facebook/redextest/SourceBlocksTest;.bazzz:()V", 3},
      {"Lcom/facebook/redextest/SourceBlocksTest;.access$002:(Ljava/lang/"
       "String;)Ljava/lang/String;",
       2},
      {"Lcom/facebook/redextest/SourceBlocksTest;.access$100:()V", 2},
      // D8 desugars javac 11+ nestmates into these bridges; javac 8 emits the
      // access$NNN pair above instead. Both forms are listed so the map stays
      // exhaustive whichever javac target the fixture is compiled with.
      {"Lcom/facebook/redextest/SourceBlocksTest;.-$$Nest$sfputmWorld:(Ljava/"
       "lang/String;)V",
       2},
      {"Lcom/facebook/redextest/SourceBlocksTest;.-$$Nest$smbazzz:()V", 2},
  };

  for (auto* m : cls->get_all_methods()) {
    if (m->get_code() == nullptr) {
      continue;
    }
    cfg::ScopedCFG cfg{m->get_code()};
    UnorderedSet<uint32_t> seen_ids;
    size_t max_seen{0};
    for (const auto* b : cfg->blocks()) {
      size_t b_seen{0};
      for (const auto& mie : *b) {
        if (mie.type != MFLOW_SOURCE_BLOCK) {
          continue;
        }

        ++b_seen;

        ASSERT_TRUE(mie.src_block != nullptr);

        EXPECT_EQ(seen_ids.count(mie.src_block->id), 0u);
        seen_ids.insert(mie.src_block->id);

        if (m->get_name()->str().substr(0, 7) != "access$") {
          EXPECT_EQ(mie.src_block->src, m->get_deobfuscated_name_or_null());
        }
      }
      EXPECT_GT(b_seen, 0u);
      max_seen = std::max(max_seen, b_seen);
    }
    auto it = kMaxSeen.find(show(m));
    if (it == kMaxSeen.end()) {
      ADD_FAILURE() << "Could not find expectation for " << show(m) << ": "
                    << max_seen;
      continue;
    }
  }
}

TEST_F(SourceBlocksTest, scaling) {
  g_redex->set_sb_interaction_index({{"Fake", 0}});

  auto* type =
      DexType::get_type("Lcom/facebook/redextest/SourceBlocksTest$Scaling;");
  ASSERT_NE(type, nullptr);
  auto* cls = type_class(type);
  ASSERT_NE(cls, nullptr);

  // Check that no code has source blocks so far.
  {
    for (const auto* m : cls->get_all_methods()) {
      if (m->get_code() == nullptr) {
        continue;
      }
      for (const auto& mie : *m->get_code()) {
        ASSERT_NE(mie.type, MFLOW_SOURCE_BLOCK);
      }
    }
  }

  // The incoming profile doesn't actually matter, we tweak here what matters:

  auto* no_source_blocks_method_ref = DexMethod::get_method(
      "Lcom/facebook/redextest/SourceBlocksTest$Scaling;.no_source_blocks:()V");
  ASSERT_NE(no_source_blocks_method_ref, nullptr);
  auto* no_source_blocks_method = no_source_blocks_method_ref->as_def();
  ASSERT_NE(no_source_blocks_method, nullptr);
  ASSERT_FALSE(has_any_source_block_positive_val(no_source_blocks_method));

  auto* nan_source_blocks_method_ref = DexMethod::get_method(
      "Lcom/facebook/redextest/"
      "SourceBlocksTest$Scaling;.nan_source_blocks:()V");
  ASSERT_NE(nan_source_blocks_method_ref, nullptr);
  auto* nan_source_blocks_method = nan_source_blocks_method_ref->as_def();
  ASSERT_NE(nan_source_blocks_method, nullptr);
  insert_source_block_vals(
      nan_source_blocks_method,
      SourceBlock::Val(/* value */ NAN, /* appear100 */ 0.0f));
  ASSERT_FALSE(has_any_source_block_positive_val(nan_source_blocks_method));

  auto* zero_source_blocks_method_ref = DexMethod::get_method(
      "Lcom/facebook/redextest/"
      "SourceBlocksTest$Scaling;.zero_source_blocks:()V");
  ASSERT_NE(zero_source_blocks_method_ref, nullptr);
  auto* zero_source_blocks_method = zero_source_blocks_method_ref->as_def();
  ASSERT_NE(zero_source_blocks_method, nullptr);
  insert_source_block_vals(
      zero_source_blocks_method,
      SourceBlock::Val(/* value */ 0.0f, /* appear100 */ 0.0f));
  ASSERT_FALSE(has_any_source_block_positive_val(zero_source_blocks_method));

  auto* hot_source_blocks_method_ref = DexMethod::get_method(
      "Lcom/facebook/redextest/"
      "SourceBlocksTest$Scaling;.hot_source_blocks:()V");
  ASSERT_NE(hot_source_blocks_method_ref, nullptr);
  auto* hot_source_blocks_method = hot_source_blocks_method_ref->as_def();
  ASSERT_NE(hot_source_blocks_method, nullptr);
  insert_source_block_vals(
      hot_source_blocks_method,
      SourceBlock::Val(/* value */ 1.0f, /* appear100 */ 0.0f));
  ASSERT_TRUE(has_any_source_block_positive_val(hot_source_blocks_method));
  ASSERT_TRUE(have_all_source_block_positive_val(hot_source_blocks_method));

  auto* hot_source_blocks_inlined_method_ref = DexMethod::get_method(
      "Lcom/facebook/redextest/"
      "SourceBlocksTest$Scaling;.hot_source_blocks_inlined:(Z)V");
  ASSERT_NE(hot_source_blocks_inlined_method_ref, nullptr);
  auto* hot_source_blocks_inlined_method =
      hot_source_blocks_inlined_method_ref->as_def();
  ASSERT_NE(hot_source_blocks_inlined_method, nullptr);
  insert_source_block_vals(
      hot_source_blocks_inlined_method,
      SourceBlock::Val(/* value */ 1.0f, /* appear100 */ 0.0f));
  ASSERT_TRUE(
      has_any_source_block_positive_val(hot_source_blocks_inlined_method));
  ASSERT_TRUE(
      have_all_source_block_positive_val(hot_source_blocks_inlined_method));
  hot_source_blocks_inlined_method->rstate.set_force_inline();

  // Run inliner, check that we have mix now.
  {
    inliner::InlinerConfig conf{};
    auto scope = build_class_scope(stores);
    walk::parallel::code(scope, [&](auto*, IRCode& code) { code.build_cfg(); });
    conf.populate(scope);
    init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
        scope, /* create_init_class_insns */ false);

    ConcurrentMethodResolverDeprecated concurrent_method_resolver;

    UnorderedSet<DexMethod*> def_inlinables{hot_source_blocks_inlined_method};

    int min_sdk = 0;
    MultiMethodInliner inliner(scope, init_classes_with_side_effects, stores,
                               config_files, def_inlinables,
                               std::ref(concurrent_method_resolver), conf,
                               min_sdk, MultiMethodInlinerMode::IntraDex);
    inliner.inline_methods();
    walk::parallel::code(scope, [&](auto*, IRCode& code) { code.clear_cfg(); });

    ASSERT_EQ(inliner.get_inlined().size(), 1u);
    ASSERT_EQ(inliner.get_info().calls_inlined, 4u);

    ASSERT_FALSE(has_any_source_block_positive_val(no_source_blocks_method));
    ASSERT_FALSE(has_any_source_block_positive_val(nan_source_blocks_method));
    ASSERT_FALSE(has_any_source_block_positive_val(zero_source_blocks_method));
    ASSERT_TRUE(has_any_source_block_positive_val(hot_source_blocks_method));
    ASSERT_TRUE(have_all_source_block_positive_val(hot_source_blocks_method));
  }
}

TEST_F(SourceBlocksTest, source_blocks_profile) {
  auto* profile_path = std::getenv("profile");
  ASSERT_NE(profile_path, nullptr) << "Missing profile path.";

  auto* type = DexType::get_type("Lcom/facebook/redextest/SourceBlocksTest;");
  ASSERT_NE(type, nullptr);
  auto* cls = type_class(type);
  ASSERT_NE(cls, nullptr);

  // Check that no code has source blocks so far.
  {
    for (const auto* m : cls->get_all_methods()) {
      if (m->get_code() == nullptr) {
        continue;
      }
      for (const auto& mie : *m->get_code()) {
        ASSERT_NE(mie.type, MFLOW_SOURCE_BLOCK);
      }
    }
  }

  // Run the pass, check that each block has a SourceBlock.
  InsertSourceBlocksPass isbp{};
  run_passes({&isbp}, nullptr, Json::nullValue, [&](const auto&) {
    enable_pass(isbp);
    set_insert_after_excs(isbp, false);
    set_profile(isbp, profile_path);
    set_force_serialize(isbp);
  });

  UnorderedMap<std::string, std::string> kExpectations = {
      {"Lcom/facebook/redextest/SourceBlocksTest;.bar:()V", "B0: 0(0.1:0.2)"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.foo:()V", "B0: 0(0.2:0.3)"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.<init>:()V",
       "B0: 0(0.3:0.4)"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.baz:(Ljava/lang/String;)V",
       "B0: 0(0.4:0.5)"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.bazz:()V", "B0: 0(0:0)"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.bazzz:()V", "B0: 0(0:0)"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.access$002:(Ljava/lang/"
       "String;)Ljava/lang/String;",
       "B0: 0(0:0)"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.access$100:()V",
       "B0: 0(0:0)"},
      // D8 desugars javac 11+ nestmates into these bridges; javac 8 emits the
      // access$NNN pair above instead. Both forms are listed so the map stays
      // exhaustive whichever javac target the fixture is compiled with.
      {"Lcom/facebook/redextest/SourceBlocksTest;.-$$Nest$sfputmWorld:(Ljava/"
       "lang/String;)V",
       "B0: 0(0:0)"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.-$$Nest$smbazzz:()V",
       "B0: 0(0:0)"},
  };

  for (auto* m : cls->get_all_methods()) {
    if (m->get_code() == nullptr) {
      continue;
    }
    cfg::ScopedCFG cfg{m->get_code()};
    auto actual = get_blocks_as_txt(*cfg);
    auto it = kExpectations.find(show(m));
    if (it == kExpectations.end()) {
      EXPECT_TRUE(false) << "No expectation for " << show(m) << ": " << actual;
      continue;
    }
    EXPECT_EQ(actual, it->second) << show(m);
  }
}

TEST_F(SourceBlocksTest, source_blocks_profile_no_always_inject) {
  auto* profile_path = std::getenv("profile");
  ASSERT_NE(profile_path, nullptr) << "Missing profile path.";

  auto* type = DexType::get_type("Lcom/facebook/redextest/SourceBlocksTest;");
  ASSERT_NE(type, nullptr);
  auto* cls = type_class(type);
  ASSERT_NE(cls, nullptr);

  // Check that no code has source blocks so far.
  {
    for (const auto* m : cls->get_all_methods()) {
      if (m->get_code() == nullptr) {
        continue;
      }
      for (const auto& mie : *m->get_code()) {
        ASSERT_NE(mie.type, MFLOW_SOURCE_BLOCK);
      }
    }
  }

  // Run the pass, check that each block has a SourceBlock.
  InsertSourceBlocksPass isbp{};
  run_passes({&isbp}, nullptr, Json::nullValue, [&](const auto&) {
    enable_pass(isbp);
    disable_always_inject(isbp);
    set_insert_after_excs(isbp, false);
    set_profile(isbp, profile_path);
  });

  UnorderedMap<std::string, std::string> kExpectations = {
      {"Lcom/facebook/redextest/SourceBlocksTest;.bar:()V", "B0: 0(0.1:0.2)"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.foo:()V", "B0: 0(0.2:0.3)"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.<init>:()V",
       "B0: 0(0.3:0.4)"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.baz:(Ljava/lang/String;)V",
       "B0: 0(0.4:0.5)"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.bazz:()V", "B0:"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.bazzz:()V", "B0:"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.access$002:(Ljava/lang/"
       "String;)Ljava/lang/String;",
       "B0:"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.access$100:()V", "B0:"},
      // D8 desugars javac 11+ nestmates into these bridges; javac 8 emits the
      // access$NNN pair above instead. Both forms are listed so the map stays
      // exhaustive whichever javac target the fixture is compiled with.
      {"Lcom/facebook/redextest/SourceBlocksTest;.-$$Nest$sfputmWorld:(Ljava/"
       "lang/String;)V",
       "B0:"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.-$$Nest$smbazzz:()V", "B0:"},
  };

  for (auto* m : cls->get_all_methods()) {
    if (m->get_code() == nullptr) {
      continue;
    }
    cfg::ScopedCFG cfg{m->get_code()};
    auto actual = get_blocks_as_txt(*cfg);
    auto it = kExpectations.find(show(m));
    if (it == kExpectations.end()) {
      EXPECT_TRUE(false) << "No expectation for " << show(m) << ": " << actual;
      continue;
    }
    EXPECT_EQ(actual, it->second) << show(m);
  }
}

TEST_F(SourceBlocksTest, source_blocks_profile_exc) {
  auto* profile_path = std::getenv("profile2");
  ASSERT_NE(profile_path, nullptr) << "Missing profile2 path.";

  auto* type = DexType::get_type("Lcom/facebook/redextest/SourceBlocksTest;");
  ASSERT_NE(type, nullptr);
  auto* cls = type_class(type);
  ASSERT_NE(cls, nullptr);

  // Check that no code has source blocks so far.
  {
    for (const auto* m : cls->get_all_methods()) {
      if (m->get_code() == nullptr) {
        continue;
      }
      for (const auto& mie : *m->get_code()) {
        ASSERT_NE(mie.type, MFLOW_SOURCE_BLOCK);
      }
    }
  }

  // Run the pass, check that each block has a SourceBlock.
  InsertSourceBlocksPass isbp{};
  run_passes({&isbp}, nullptr, Json::nullValue, [&](const auto&) {
    enable_pass(isbp);
    set_insert_after_excs(isbp, true);
    set_profile(isbp, profile_path);
    set_force_serialize(isbp);
  });

  UnorderedMap<std::string, std::string> kExpectations = {
      {"Lcom/facebook/redextest/SourceBlocksTest;.bar:()V",
       "B0: 0(0.4:0.6) 1(0.5:0.5) 2(0.6:0.4)"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.foo:()V",
       "B0: 0(0:0.3) 1(0.1:0.2) 2(0.2:0.1) 3(0.3:0)"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.<init>:()V",
       "B0: 0(0.1:0.3) 1(0.2:0.2) 2(0.3:0.1)"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.baz:(Ljava/lang/String;)V",
       "B0: 0(0.7:0.1) 1(0.8:0.2)"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.bazz:()V",
       "B0: 0(0:0) 1(0:0)"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.bazzz:()V",
       "B0: 0(0:0) 1(0:0) 2(0:0)"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.access$002:(Ljava/lang/"
       "String;)Ljava/lang/String;",
       "B0: 0(0:0) 1(0:0)"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.access$100:()V",
       "B0: 0(0:0) 1(0:0)"},
      // D8 desugars javac 11+ nestmates into these bridges; javac 8 emits the
      // access$NNN pair above instead. Both forms are listed so the map stays
      // exhaustive whichever javac target the fixture is compiled with.
      {"Lcom/facebook/redextest/SourceBlocksTest;.-$$Nest$sfputmWorld:(Ljava/"
       "lang/String;)V",
       "B0: 0(0:0) 1(0:0)"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.-$$Nest$smbazzz:()V",
       "B0: 0(0:0) 1(0:0)"},
  };

  for (auto* m : cls->get_all_methods()) {
    if (m->get_code() == nullptr) {
      continue;
    }
    cfg::ScopedCFG cfg{m->get_code()};
    auto actual = get_blocks_as_txt(*cfg);
    auto it = kExpectations.find(show(m));
    if (it == kExpectations.end()) {
      EXPECT_TRUE(false) << "No expectation for " << show(m) << ": " << actual;
      continue;
    }
    EXPECT_EQ(actual, it->second) << show(m);
  }
}

TEST_F(SourceBlocksTest, source_blocks_profile_exc_no_always_inject) {
  auto* profile_path = std::getenv("profile2");
  ASSERT_NE(profile_path, nullptr) << "Missing profile2 path.";

  auto* type = DexType::get_type("Lcom/facebook/redextest/SourceBlocksTest;");
  ASSERT_NE(type, nullptr);
  auto* cls = type_class(type);
  ASSERT_NE(cls, nullptr);

  // Check that no code has source blocks so far.
  {
    for (const auto* m : cls->get_all_methods()) {
      if (m->get_code() == nullptr) {
        continue;
      }
      for (const auto& mie : *m->get_code()) {
        ASSERT_NE(mie.type, MFLOW_SOURCE_BLOCK);
      }
    }
  }

  // Run the pass, check that each block has a SourceBlock.
  InsertSourceBlocksPass isbp{};
  run_passes({&isbp}, nullptr, Json::nullValue, [&](const auto&) {
    enable_pass(isbp);
    disable_always_inject(isbp);
    set_insert_after_excs(isbp, true);
    set_profile(isbp, profile_path);
  });

  UnorderedMap<std::string, std::string> kExpectations = {
      {"Lcom/facebook/redextest/SourceBlocksTest;.bar:()V",
       "B0: 0(0.4:0.6) 1(0.5:0.5) 2(0.6:0.4)"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.foo:()V",
       "B0: 0(0:0.3) 1(0.1:0.2) 2(0.2:0.1) 3(0.3:0)"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.<init>:()V",
       "B0: 0(0.1:0.3) 1(0.2:0.2) 2(0.3:0.1)"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.baz:(Ljava/lang/String;)V",
       "B0: 0(0.7:0.1) 1(0.8:0.2)"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.bazz:()V", "B0:"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.bazzz:()V", "B0:"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.access$002:(Ljava/lang/"
       "String;)Ljava/lang/String;",
       "B0:"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.access$100:()V", "B0:"},
      // D8 desugars javac 11+ nestmates into these bridges; javac 8 emits the
      // access$NNN pair above instead. Both forms are listed so the map stays
      // exhaustive whichever javac target the fixture is compiled with.
      {"Lcom/facebook/redextest/SourceBlocksTest;.-$$Nest$sfputmWorld:(Ljava/"
       "lang/String;)V",
       "B0:"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.-$$Nest$smbazzz:()V", "B0:"},
  };

  for (auto* m : cls->get_all_methods()) {
    if (m->get_code() == nullptr) {
      continue;
    }
    cfg::ScopedCFG cfg{m->get_code()};
    auto actual = get_blocks_as_txt(*cfg);
    auto it = kExpectations.find(show(m));
    if (it == kExpectations.end()) {
      EXPECT_TRUE(false) << "No expectation for " << show(m) << ": " << actual;
      continue;
    }
    EXPECT_EQ(actual, it->second) << show(m);
  }
}

TEST_F(SourceBlocksTest, source_blocks_profile_always_inject_method_profiles) {
  auto* profile_path = std::getenv("profile3");
  ASSERT_NE(profile_path, nullptr) << "Missing profile path.";

  auto* method_profile_path = std::getenv("method-profile");
  ASSERT_NE(method_profile_path, nullptr) << "Missing method-profile path.";

  auto* type = DexType::get_type("Lcom/facebook/redextest/SourceBlocksTest;");
  ASSERT_NE(type, nullptr);
  auto* cls = type_class(type);
  ASSERT_NE(cls, nullptr);

  // Check that no code has source blocks so far.
  {
    for (const auto* m : cls->get_all_methods()) {
      if (m->get_code() == nullptr) {
        continue;
      }
      for (const auto& mie : *m->get_code()) {
        ASSERT_NE(mie.type, MFLOW_SOURCE_BLOCK);
      }
    }
  }

  // Need to set up a configuration that will load method profiles.
  Json::Value mp_val = Json::arrayValue;
  mp_val.resize(1);
  mp_val[0] = method_profile_path;
  Json::Value conf_val = Json::objectValue;
  conf_val["agg_method_stats_files"] = mp_val;

  // Run the pass, check that each block has a SourceBlock.
  InsertSourceBlocksPass isbp{};
  run_passes({&isbp}, nullptr, conf_val, [&](const auto&) {
    enable_pass(isbp);
    enable_always_inject(isbp);
    set_insert_after_excs(isbp, false);
    set_profile(isbp, profile_path);
  });

  UnorderedMap<std::string, std::string> kExpectations = {
      {"Lcom/facebook/redextest/SourceBlocksTest;.bar:()V", "B0: 0(0.1:0.2)"},
      // This comes from method profiles.
      {"Lcom/facebook/redextest/SourceBlocksTest;.foo:()V", "B0: 0(1:99)"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.<init>:()V",
       "B0: 0(0.3:0.4)"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.baz:(Ljava/lang/String;)V",
       "B0: 0(0.4:0.5)"},
      // This comes from method profiles.
      {"Lcom/facebook/redextest/SourceBlocksTest;.bazz:()V", "B0: 0(1:98)"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.bazzz:()V", "B0: 0(0:0)"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.access$002:(Ljava/lang/"
       "String;)Ljava/lang/String;",
       "B0: 0(0:0)"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.access$100:()V",
       "B0: 0(0:0)"},
      // D8 desugars javac 11+ nestmates into these bridges; javac 8 emits the
      // access$NNN pair above instead. Both forms are listed so the map stays
      // exhaustive whichever javac target the fixture is compiled with.
      {"Lcom/facebook/redextest/SourceBlocksTest;.-$$Nest$sfputmWorld:(Ljava/"
       "lang/String;)V",
       "B0: 0(0:0)"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.-$$Nest$smbazzz:()V",
       "B0: 0(0:0)"},
  };

  for (auto* m : cls->get_all_methods()) {
    if (m->get_code() == nullptr) {
      continue;
    }
    cfg::ScopedCFG cfg{m->get_code()};
    auto actual = get_blocks_as_txt(*cfg);
    auto it = kExpectations.find(show(m));
    if (it == kExpectations.end()) {
      EXPECT_TRUE(false) << "No expectation for " << show(m) << ": " << actual;
      continue;
    }
    EXPECT_EQ(actual, it->second) << show(m);
  }
}

TEST_F(SourceBlocksTest,
       stable_hash_traverses_real_edges_and_ignores_ghost_edges) {
  auto first_code = assembler::ircode_from_string(R"((
    (const v0 0)
    (if-eqz v0 :second_return)
    (const v1 1)
    (return-void)
    (:second_return)
    (const v1 2)
    (return-void)
  ))");
  auto second_code = assembler::ircode_from_string(R"((
    (const v0 0)
    (if-eqz v0 :second_return)
    (const v1 3)
    (return-void)
    (:second_return)
    (const v1 2)
    (return-void)
  ))");
  first_code->build_cfg();
  second_code->build_cfg();
  auto& first_cfg = first_code->cfg();
  auto& second_cfg = second_code->cfg();

  auto first_hash = insert_source_blocks::testing::stable_hash(first_cfg);
  auto second_hash = insert_source_blocks::testing::stable_hash(second_cfg);
  EXPECT_NE(first_hash, second_hash);

  for (auto* graph : {&first_cfg, &second_cfg}) {
    auto hash_without_exit_block =
        insert_source_blocks::testing::stable_hash(*graph);
    graph->calculate_exit_block();

    size_t ghost_edges = 0;
    for (auto* block : graph->blocks()) {
      for (auto* edge : block->succs()) {
        if (edge->type() == cfg::EDGE_GHOST) {
          ++ghost_edges;
        }
      }
    }
    ASSERT_EQ(ghost_edges, 2);
    EXPECT_EQ(hash_without_exit_block,
              insert_source_blocks::testing::stable_hash(*graph));
  }
}

namespace {

uint64_t stable_hash_of(IRCode* code) {
  code->build_cfg();
  return insert_source_blocks::testing::stable_hash(code->cfg());
}

uint64_t stable_hash_of(const std::string& ir) {
  auto code = assembler::ircode_from_string(ir);
  return stable_hash_of(code.get());
}

// Reaches a switch, a loop back-edge and a typed catch only after the entry
// block, so every edge kind is hashed somewhere other than the entry block.
constexpr const char* kAllEdgeKindsIR = R"((
  (load-param v0)
  (if-eqz v0 :throwing)

  (:loop)
  (switch v0 (:a :b))
  (return v0)

  (:a 1)
  (add-int/lit v0 v0 -1)
  (goto :loop)

  (:b 2)
  (const v0 7)
  (return v0)

  (:throwing)
  (.try_start t)
  (invoke-static (v0) "Lcom/facebook/redextest/SourceBlocksTest;.hashCallee:(I)I")
  (move-result v0)
  (.try_end t)
  (return v0)

  (.catch (t) "Ljava/lang/ArithmeticException;")
  (const v0 0)
  (return v0)
))";

} // namespace

// The hash is persisted in profiles as `access$redex<hash>$NN`, so any change
// in what it covers or how it walks the CFG silently drops profile matches for
// multi-block access methods until the profiles are regenerated.
TEST_F(SourceBlocksTest, stable_hash_multi_block_value_is_pinned) {
  EXPECT_EQ(stable_hash_of(kAllEdgeKindsIR), 0xbcb0fbec281563acULL);
}

TEST_F(SourceBlocksTest, stable_hash_covers_edges_past_the_entry_block) {
  auto base = stable_hash_of(kAllEdgeKindsIR);

  auto variant = [](std::string_view from, std::string_view to) {
    std::string ir{kAllEdgeKindsIR};
    auto pos = ir.find(from);
    always_assert_log(pos != std::string::npos, "%s not in IR",
                      std::string(from).c_str());
    ir.replace(pos, from.size(), to);
    return stable_hash_of(ir);
  };

  EXPECT_NE(base, variant("(:b 2)", "(:b 3)")) << "switch case key";
  EXPECT_NE(base,
            variant("Ljava/lang/ArithmeticException;",
                    "Ljava/lang/IllegalStateException;"))
      << "catch type";
  EXPECT_NE(base, variant("(goto :loop)", "(return v0)")) << "loop back-edge";
  EXPECT_NE(base, variant("(const v0 7)", "(const v0 8)"))
      << "instruction in a block behind the switch";
}

TEST_F(SourceBlocksTest, stable_hash_covers_method_constants) {
  auto handle = [](const std::string& method) {
    return stable_hash_of(
        R"(((const-method-handle invoke-static ")" + method +
        R"(") (move-result-pseudo-object v0) (return-object v0)))");
  };
  EXPECT_NE(handle("LFoo;.a:()V"), handle("LFoo;.b:()V"));

  auto type = [](const std::string& proto) {
    return stable_hash_of(
        R"(((const-method-type ")" + proto +
        R"(") (move-result-pseudo-object v0) (return-object v0)))");
  };
  EXPECT_NE(type("(I)V"), type("(J)V"));
}

TEST_F(SourceBlocksTest, stable_hash_covers_call_site_prototype) {
  auto call = [](const std::string& proto) {
    return stable_hash_of(
        R"(((load-param-object v0) (load-param v1) (invoke-polymorphic (v0 v1) "Ljava/lang/invoke/MethodHandle;.invokeExact:([Ljava/lang/Object;)Ljava/lang/Object;" ")" +
        proto + R"(") (return-void)))");
  };
  EXPECT_NE(call("(I)V"), call("(F)V"));
}

TEST_F(SourceBlocksTest, stable_hash_covers_call_sites) {
  auto call = [](std::string_view method_name) {
    auto code = assembler::ircode_from_string(
        R"(((invoke-static () "LFoo;.placeholder:()V") (return-void)))");
    // The `invoke-static` becomes an `invoke-custom`.
    redex::make_invoke_custom(code.get(), method_name, "()V");
    return stable_hash_of(code.get());
  };
  EXPECT_NE(call("a"), call("b"));
}

// Method handles and call sites with the same content hash alike, even when
// they are separate objects, as in two builds.
TEST_F(SourceBlocksTest, stable_hash_of_equal_method_constants_is_equal) {
  auto handle = [] {
    auto code = assembler::ircode_from_string(
        R"(((const-method-handle invoke-static "LFoo;.placeholder:()V") (move-result-pseudo-object v0) (return-object v0)))");
    for (auto& mie : InstructionIterable(*code)) {
      if (mie.insn->has_methodhandle()) {
        // A separate object with the same content.
        mie.insn->set_methodhandle(redex::make_method_handle(
            METHOD_HANDLE_TYPE_INVOKE_STATIC, "LFoo;.placeholder:()V"));
      }
    }
    return stable_hash_of(code.get());
  };
  EXPECT_EQ(handle(), handle());

  auto call = [] {
    auto code = assembler::ircode_from_string(
        R"(((invoke-static () "LFoo;.placeholder:()V") (return-void)))");
    // Each call makes a new call site.
    redex::make_invoke_custom(code.get(), "a", "()V");
    return stable_hash_of(code.get());
  };
  EXPECT_EQ(call(), call());
}

TEST_F(SourceBlocksTest, stable_hash_does_not_depend_on_block_layout) {
  // Same CFG, with the join block placed before and after the branch target.
  auto join_first = stable_hash_of(R"((
    (load-param v0)
    (if-eqz v0 :a)
    (const v1 1)
    (:join)
    (return v1)
    (:a)
    (const v1 2)
    (goto :join)
  ))");
  auto join_last = stable_hash_of(R"((
    (load-param v0)
    (if-eqz v0 :a)
    (const v1 1)
    (goto :join)
    (:a)
    (const v1 2)
    (:join)
    (return v1)
  ))");
  EXPECT_EQ(join_first, join_last);
}

// Two javac-style access methods in one class, with the same access-flag
// suffix and the same entry block, differing only after the branch. The
// profile has a hashed row for `access$202` only, so `access$302` must not
// pick up its values.
TEST_F(SourceBlocksTest, access_method_profile_row_does_not_match_other_body) {
  auto* type = DexType::get_type("Lcom/facebook/redextest/SourceBlocksTest;");
  ASSERT_NE(type, nullptr);
  auto* cls = type_class(type);
  ASSERT_NE(cls, nullptr);

  auto make_access_method = [cls](const std::string& name,
                                  const std::string& fallthrough_literal) {
    auto* m = DexMethod::make_method(
                  "Lcom/facebook/redextest/SourceBlocksTest;." + name + ":(I)I")
                  ->make_concrete(ACC_STATIC | ACC_SYNTHETIC,
                                  assembler::ircode_from_string(
                                      "((load-param v0) (if-eqz v0 :zero) "
                                      "(const v1 " +
                                      fallthrough_literal +
                                      ") (return v1) (:zero) (const v1 2) "
                                      "(return v1))"),
                                  /*is_virtual=*/false);
    m->set_deobfuscated_name(show(m));
    cls->add_method(m);
    return m;
  };
  auto* profiled = make_access_method("access$202", "1");
  auto* other = make_access_method("access$302", "3");

  auto hash_of = [](DexMethod* m) {
    m->get_code()->build_cfg();
    auto hash =
        insert_source_blocks::testing::stable_hash(m->get_code()->cfg());
    m->get_code()->clear_cfg();
    return hash;
  };
  auto profiled_hash = hash_of(profiled);

  std::array<char, 17> hex{};
  snprintf(hex.data(), hex.size(), "%016" PRIx64, profiled_hash);
  auto profile_path = get_configfiles_out_dir() + "/access_profile.csv";
  {
    std::ofstream out(profile_path);
    out << "interaction,appear#\n"
        << "ColdStart,4\n"
        << "name,profiled_srcblks_exprs\n"
        << "Lcom/facebook/redextest/SourceBlocksTest;.access$redex"
        << hex.data() << "$02:(I)I,(0.5:0.6 g(0.1:0.2) b(0.3:0.4))\n";
  }

  InsertSourceBlocksPass isbp{};
  run_passes({&isbp}, nullptr, Json::nullValue, [&](const auto&) {
    enable_pass(isbp);
    enable_always_inject(isbp);
    set_insert_after_excs(isbp, false);
    set_profile(isbp, std::string(profile_path));
  });

  auto blocks_of = [this](DexMethod* m) {
    cfg::ScopedCFG cfg{m->get_code()};
    return get_blocks_as_txt(*cfg);
  };
  EXPECT_EQ(blocks_of(profiled),
            "B0: 0(0.5:0.6)\nB1: 1(0.1:0.2)\nB2: 2(0.3:0.4)");
  // No row of its own: always-inject falls back to the (absent) method profile.
  EXPECT_EQ(blocks_of(other), "B0: 0(0:0)\nB1: 1(0:0)\nB2: 2(0:0)");
}

TEST_F(SourceBlocksTest, source_blocks_access_methods) {
  auto* type = DexType::get_type("Lcom/facebook/redextest/SourceBlocksTest;");
  ASSERT_NE(type, nullptr);
  auto* cls = type_class(type);
  ASSERT_NE(cls, nullptr);

  // Check that no code has source blocks so far.
  {
    for (const auto* m : cls->get_all_methods()) {
      if (m->get_code() == nullptr) {
        continue;
      }
      for (const auto& mie : *m->get_code()) {
        ASSERT_NE(mie.type, MFLOW_SOURCE_BLOCK);
      }
    }
  }

  // Run the pass, check that each block has a SourceBlock.
  InsertSourceBlocksPass isbp{};
  run_passes({&isbp}, nullptr, Json::nullValue, [&](const auto&) {
    enable_pass(isbp);
    enable_always_inject(isbp);
    set_insert_after_excs(isbp, false);
  });

  UnorderedMap<std::string, std::string> kExpectations = {
      {"Lcom/facebook/redextest/SourceBlocksTest;.access$002:(Ljava/lang/"
       "String;)Ljava/lang/String;",
       "B0: "
       "Lcom/facebook/redextest/"
       "SourceBlocksTest;.access$redex5be80c743d1d526b$02:(Ljava/lang/"
       "String;)Ljava/lang/String;@0"},
      {"Lcom/facebook/redextest/SourceBlocksTest;.access$100:()V",
       "B0: "
       "Lcom/facebook/redextest/"
       "SourceBlocksTest;.access$redex1bc24000ccc37110$00:()V@0"},
  };

  for (auto* m : cls->get_all_methods()) {
    if (m->get_code() == nullptr) {
      continue;
    }
    if (m->get_name()->str().substr(0, 7) != "access$") {
      continue;
    }
    cfg::ScopedCFG cfg{m->get_code()};
    auto actual = get_blocks_as_txt_full(*cfg);
    auto it = kExpectations.find(show(m));
    if (it == kExpectations.end()) {
      EXPECT_TRUE(false) << "No expectation for " << show(m) << ": " << actual;
      continue;
    }
    EXPECT_EQ(actual, it->second) << show(m);
  }
}

TEST_F(SourceBlocksTest, fix_hot_method_cold_entry_violations_test) {
  auto* profile_path = std::getenv("hot-method-cold-entry");
  ASSERT_NE(profile_path, nullptr) << "Missing profile path.";

  auto* type = DexType::get_type(
      "Lcom/facebook/redextest/SourceBlocksTest$ViolationsFixTest;");
  ASSERT_NE(type, nullptr);
  auto* cls = type_class(type);
  ASSERT_NE(cls, nullptr);

  // Check that no code has source blocks so far.
  {
    for (const auto* m : cls->get_all_methods()) {
      if (m->get_code() == nullptr) {
        continue;
      }
      for (const auto& mie : *m->get_code()) {
        ASSERT_NE(mie.type, MFLOW_SOURCE_BLOCK);
      }
    }
  }

  // Run the pass, check that each block has a SourceBlock.
  InsertSourceBlocksPass isbp{};
  run_passes({&isbp}, nullptr, Json::nullValue, [&](const auto&) {
    enable_pass(isbp);
    set_insert_after_excs(isbp, false);
    set_profile(isbp, profile_path);
    set_force_serialize(isbp);
    set_fix_violations(isbp);
  });

  {
    for (auto* m : cls->get_all_methods()) {
      if (m->get_code() == nullptr) {
        continue;
      }
      m->get_code()->build_cfg();
    }
  }

  UnorderedMap<std::string, std::string> kExpectations = {
      {"Lcom/facebook/redextest/"
       "SourceBlocksTest$ViolationsFixTest;.hot_method:()V",
       "B0: 0(1:0.5)"},
      {"Lcom/facebook/redextest/"
       "SourceBlocksTest$ViolationsFixTest;.cold_method:()V",
       "B0: 0(0:0)"},
      {"Lcom/facebook/redextest/"
       "SourceBlocksTest$ViolationsFixTest;.hot_method_2:()V",
       "B0: 0(1:0.5)"},
      {"Lcom/facebook/redextest/"
       "SourceBlocksTest$ViolationsFixTest;.idom_branch:()V",
       "B0: 0(0:0)\nB1: 1(0:0)\nB2: 2(0:0)\nB3: 3(0:0)"},
      {"Lcom/facebook/redextest/"
       "SourceBlocksTest$ViolationsFixTest;.branch_1:()V",
       "B0: 0(0:0)"},
      {"Lcom/facebook/redextest/"
       "SourceBlocksTest$ViolationsFixTest;.branch_2:()V",
       "B0: 0(0:0)"},
      {"Lcom/facebook/redextest/"
       "SourceBlocksTest$ViolationsFixTest;.<init>:()V",
       "B0: 0(0:0)"},

  };

  for (auto* m : cls->get_all_methods()) {
    if (m->get_code() == nullptr) {
      continue;
    }
    cfg::ScopedCFG cfg{m->get_code()};
    auto actual = get_blocks_as_txt(*cfg);
    auto it = kExpectations.find(show(m));
    if (it == kExpectations.end()) {
      EXPECT_TRUE(false) << "No expectation for " << show(m) << ": " << actual;
      continue;
    }
    EXPECT_EQ(actual, it->second) << show(m);
  }
}

TEST_F(SourceBlocksTest, fix_idom_test) {
  auto* profile_path = std::getenv("idom");
  ASSERT_NE(profile_path, nullptr) << "Missing profile path.";

  auto* type = DexType::get_type(
      "Lcom/facebook/redextest/SourceBlocksTest$ViolationsFixTest;");
  ASSERT_NE(type, nullptr);
  auto* cls = type_class(type);
  ASSERT_NE(cls, nullptr);

  // Check that no code has source blocks so far.
  {
    for (const auto* m : cls->get_all_methods()) {
      if (m->get_code() == nullptr) {
        continue;
      }
      for (const auto& mie : *m->get_code()) {
        ASSERT_NE(mie.type, MFLOW_SOURCE_BLOCK);
      }
    }
  }

  // Run the pass, check that each block has a SourceBlock.
  InsertSourceBlocksPass isbp{};
  run_passes({&isbp}, nullptr, Json::nullValue, [&](const auto&) {
    enable_pass(isbp);
    set_insert_after_excs(isbp, false);
    set_profile(isbp, profile_path);
    set_force_serialize(isbp);
    set_fix_violations(isbp);
  });

  UnorderedMap<std::string, std::string> kExpectations = {
      {"Lcom/facebook/redextest/"
       "SourceBlocksTest$ViolationsFixTest;.hot_method:()V",
       "B0: 0(0:0)"},
      {"Lcom/facebook/redextest/"
       "SourceBlocksTest$ViolationsFixTest;.cold_method:()V",
       "B0: 0(0:0)"},
      {"Lcom/facebook/redextest/"
       "SourceBlocksTest$ViolationsFixTest;.hot_method_2:()V",
       "B0: 0(0:0)"},
      {"Lcom/facebook/redextest/"
       "SourceBlocksTest$ViolationsFixTest;.idom_branch:()V",
       "B0: 0(1:0)\nB1: 1(1:0.1)\nB2: 2(0:0)\nB3: 3(0:0)"},
      {"Lcom/facebook/redextest/"
       "SourceBlocksTest$ViolationsFixTest;.branch_1:()V",
       "B0: 0(0:0)"},
      {"Lcom/facebook/redextest/"
       "SourceBlocksTest$ViolationsFixTest;.branch_2:()V",
       "B0: 0(1:0.5)"},
      {"Lcom/facebook/redextest/"
       "SourceBlocksTest$ViolationsFixTest;.<init>:()V",
       "B0: 0(0:0)"},
  };

  for (auto* m : cls->get_all_methods()) {
    if (m->get_code() == nullptr) {
      continue;
    }
    cfg::ScopedCFG cfg{m->get_code()};
    auto actual = get_blocks_as_txt(*cfg);
    auto it = kExpectations.find(show(m));
    if (it == kExpectations.end()) {
      EXPECT_TRUE(false) << "No expectation for " << show(m) << ": " << actual;
      continue;
    }
    EXPECT_EQ(actual, it->second) << show(m);
  }
}

TEST_F(SourceBlocksTest, chain_and_dom_fix_chain_test) {
  auto* profile_path = std::getenv("chain-and-dom");
  ASSERT_NE(profile_path, nullptr) << "Missing profile path.";

  auto* type = DexType::get_type(
      "Lcom/facebook/redextest/SourceBlocksTest$ChainAndDomClass;");
  ASSERT_NE(type, nullptr);
  auto* cls = type_class(type);
  ASSERT_NE(cls, nullptr);

  // Check that no code has source blocks so far.
  {
    for (const auto* m : cls->get_all_methods()) {
      if (m->get_code() == nullptr) {
        continue;
      }
      for (const auto& mie : *m->get_code()) {
        ASSERT_NE(mie.type, MFLOW_SOURCE_BLOCK);
      }
    }
  }

  // Run the pass, check that each block has a SourceBlock.
  InsertSourceBlocksPass isbp{};
  run_passes({&isbp}, nullptr, Json::nullValue, [&](const auto&) {
    enable_pass(isbp);
    set_insert_after_excs(isbp, true);
    set_profile(isbp, profile_path);
    set_force_serialize(isbp);
    set_fix_violations(isbp);
  });

  for (auto* m : cls->get_all_methods()) {
    if (m->get_code() == nullptr) {
      continue;
    }
    if (m->get_name()->str().substr(0, 6) == "chains") {
      cfg::ScopedCFG cfg{m->get_code()};
      // After fix_chain_violations, check if all source blocks now have values
      // of (1:0)
      for (auto* b : cfg->blocks()) {
        for (const auto& mie : *b) {
          if (mie.type == MFLOW_SOURCE_BLOCK) {
            auto* sb = mie.src_block.get();
            ASSERT_EQ(sb->get_at(0)->val, 1.0f);
          }
        }
      }
    }
  }
}

TEST_F(SourceBlocksTest, chain_and_dom_fix_thrower_test) {
  auto* profile_path = std::getenv("chain-and-dom");
  ASSERT_NE(profile_path, nullptr) << "Missing profile path.";

  auto* type = DexType::get_type(
      "Lcom/facebook/redextest/SourceBlocksTest$ChainAndDomClass;");
  ASSERT_NE(type, nullptr);
  auto* cls = type_class(type);
  ASSERT_NE(cls, nullptr);

  // Check that no code has source blocks so far.
  {
    for (const auto* m : cls->get_all_methods()) {
      if (m->get_code() == nullptr) {
        continue;
      }
      for (const auto& mie : *m->get_code()) {
        ASSERT_NE(mie.type, MFLOW_SOURCE_BLOCK);
      }
    }
  }

  // Run the pass, check that each block has a SourceBlock.
  InsertSourceBlocksPass isbp{};
  run_passes({&isbp}, nullptr, Json::nullValue, [&](const auto&) {
    enable_pass(isbp);
    set_insert_after_excs(isbp, true);
    set_profile(isbp, profile_path);
    set_force_serialize(isbp);
    set_fix_violations(isbp);
  });

  for (auto* m : cls->get_all_methods()) {
    if (m->get_code() == nullptr) {
      continue;
    }
    if (m->get_name()->str().substr(0, 7) == "thrower") {
      cfg::ScopedCFG cfg{m->get_code()};

      // should expect the (0:0) blocks to be converted into (1:1) unless
      // there is a throw exception
      std::vector<int> expected_vals{1, 0};
      int idx = 0;
      for (auto* b : cfg->blocks()) {
        for (const auto& mie : *b) {
          if (mie.type == MFLOW_SOURCE_BLOCK) {
            auto* sb = mie.src_block.get();
            ASSERT_EQ(sb->get_at(0)->val, expected_vals[idx]);
            idx++;
          }
        }
      }
    }
  }
}

TEST_F(SourceBlocksTest, test_counting_with_idom_violations) {
  auto* profile_path = std::getenv("idom-counting-violations");
  ASSERT_NE(profile_path, nullptr) << "Missing profile path.";

  auto* type = DexType::get_type(
      "Lcom/facebook/redextest/SourceBlocksTest$IDomBlockCounting;");
  ASSERT_NE(type, nullptr);
  auto* cls = type_class(type);
  ASSERT_NE(cls, nullptr);

  InsertSourceBlocksPass isbp{};
  run_passes({&isbp}, nullptr, Json::nullValue, [&](const auto&) {
    enable_pass(isbp);
    set_insert_after_excs(isbp, false);
    set_profile(isbp, profile_path);
    set_force_serialize(isbp);
  });

  auto* method = cls->find_method_from_simple_deobfuscated_name("idom");
  method->get_code()->build_cfg();
  auto violations = source_blocks::compute(
      source_blocks::ViolationsHelper::Violation::kChainAndDom,
      method->get_code()->cfg());

  // The fixture is a plain if/else diamond (see `IDomBlockCounting.idom`) --
  // there is no loop in it. The synthetic profile gives the branch block val 1
  // and one arm val 2, and an arm of an `if` has exactly one predecessor, which
  // is also its immediate dominator. An arm cannot run more often than the
  // branch that guards it, so this is a genuine inconsistency rather than the
  // loop amplification `dom_cold_block_hot` was introduced to stop
  // false-positiving on.
  //
  // The straight-line magnitude check therefore fires here, and should: with a
  // single predecessor there is no back edge to amplify the block.
  ASSERT_EQ(violations, 1);
}

// Positive counterpart to test_counting_with_idom_violations: a genuine
// cold->hot coverage inversion (the entry, i.e. the immediate dominator, is
// UNCOVERED while a block it dominates is covered) MUST still be reported by
// the boolean-ized kChainAndDom check. Guards against the fix silencing real
// violations.
TEST_F(SourceBlocksTest, test_counting_with_idom_chain_dom_violation) {
  auto* profile_path = std::getenv("idom-chain-dom-violation");
  ASSERT_NE(profile_path, nullptr) << "Missing profile path.";

  auto* type = DexType::get_type(
      "Lcom/facebook/redextest/SourceBlocksTest$IDomBlockCounting;");
  ASSERT_NE(type, nullptr);
  auto* cls = type_class(type);
  ASSERT_NE(cls, nullptr);

  InsertSourceBlocksPass isbp{};
  run_passes({&isbp}, nullptr, Json::nullValue, [&](const auto&) {
    enable_pass(isbp);
    set_insert_after_excs(isbp, false);
    set_profile(isbp, profile_path);
    set_force_serialize(isbp);
  });

  auto* method = cls->find_method_from_simple_deobfuscated_name("idom");
  method->get_code()->build_cfg();
  auto violations = source_blocks::compute(
      source_blocks::ViolationsHelper::Violation::kChainAndDom,
      method->get_code()->cfg());

  // Exactly one inversion: the single covered (val 1) block whose immediate
  // dominator (the entry) is uncovered (val 0). The other blocks are uncovered,
  // so the boolean predicate does not fire for them.
  ASSERT_EQ(violations, 1);
}

TEST_F(SourceBlocksTest, test_counting_with_hot_no_hot_pred_violations) {
  auto* profile_path = std::getenv("hot-no-hot-pred-counting-violations");
  ASSERT_NE(profile_path, nullptr) << "Missing profile path.";

  auto* type = DexType::get_type(
      "Lcom/facebook/redextest/SourceBlocksTest$IDomBlockCounting;");
  ASSERT_NE(type, nullptr);
  auto* cls = type_class(type);
  ASSERT_NE(cls, nullptr);

  InsertSourceBlocksPass isbp{};
  run_passes({&isbp}, nullptr, Json::nullValue, [&](const auto&) {
    enable_pass(isbp);
    set_insert_after_excs(isbp, false);
    set_profile(isbp, profile_path);
    set_force_serialize(isbp);
  });

  auto* method = cls->find_method_from_simple_deobfuscated_name("idom");
  method->get_code()->build_cfg();
  auto violations = source_blocks::compute(
      source_blocks::ViolationsHelper::Violation::kHotNoHotPred,
      method->get_code()->cfg());

  ASSERT_EQ(violations, 2);
}

TEST_F(SourceBlocksTest, test_hot_all_children_cold_counting_violations) {
  auto* profile_path = std::getenv("hot-all-children-cold-counting-violations");
  ASSERT_NE(profile_path, nullptr) << "Missing profile path.";

  auto* type = DexType::get_type(
      "Lcom/facebook/redextest/SourceBlocksTest$IDomBlockCounting;");
  ASSERT_NE(type, nullptr);
  auto* cls = type_class(type);
  ASSERT_NE(cls, nullptr);

  InsertSourceBlocksPass isbp{};
  run_passes({&isbp}, nullptr, Json::nullValue, [&](const auto&) {
    enable_pass(isbp);
    set_insert_after_excs(isbp, false);
    set_profile(isbp, profile_path);
    set_force_serialize(isbp);
  });

  auto* method = cls->find_method_from_simple_deobfuscated_name("idom");
  method->get_code()->build_cfg();
  auto violations = source_blocks::compute(
      source_blocks::ViolationsHelper::Violation::KHotAllChildrenCold,
      method->get_code()->cfg());

  ASSERT_EQ(violations, 1);
}

TEST_F(SourceBlocksTest, test_methods_with_intermethod_violations) {
  auto* profile_path = std::getenv("intermethod-violations");
  ASSERT_NE(profile_path, nullptr) << "Missing profile path.";

  auto* type = DexType::get_type(
      "Lcom/facebook/redextest/SourceBlocksTest$IntermethodViolationsClass;");
  ASSERT_NE(type, nullptr);
  auto* cls = type_class(type);
  ASSERT_NE(cls, nullptr);

  // Check that no code has source blocks so far.
  {
    for (const auto* m : cls->get_all_methods()) {
      if (m->get_code() == nullptr) {
        continue;
      }
      for (const auto& mie : *m->get_code()) {
        ASSERT_NE(mie.type, MFLOW_SOURCE_BLOCK);
      }
    }
  }

  // Run the pass, check that each block has a SourceBlock.
  InsertSourceBlocksPass isbp{};
  run_passes({&isbp}, nullptr, Json::nullValue, [&](const auto&) {
    enable_pass(isbp);
    set_insert_after_excs(isbp, true);
    set_profile(isbp, profile_path);
    set_force_serialize(isbp);
  });

  const auto& metric = pass_manager->get_pass_info().at(0).metrics;
  ASSERT_EQ(metric.at("method~violation~hot~callee~cold~callers"), 1);
}

TEST_F(SourceBlocksTest, test_methods_without_intermethod_violations) {
  auto* profile_path = std::getenv("no-intermethod-violations");
  ASSERT_NE(profile_path, nullptr) << "Missing profile path.";

  auto* type = DexType::get_type(
      "Lcom/facebook/redextest/SourceBlocksTest$IntermethodViolationsClass;");
  ASSERT_NE(type, nullptr);
  auto* cls = type_class(type);
  ASSERT_NE(cls, nullptr);

  // Check that no code has source blocks so far.
  {
    for (const auto* m : cls->get_all_methods()) {
      if (m->get_code() == nullptr) {
        continue;
      }
      for (const auto& mie : *m->get_code()) {
        ASSERT_NE(mie.type, MFLOW_SOURCE_BLOCK);
      }
    }
  }

  // Run the pass, check that each block has a SourceBlock.
  InsertSourceBlocksPass isbp{};
  run_passes({&isbp}, nullptr, Json::nullValue, [&](const auto&) {
    enable_pass(isbp);
    set_insert_after_excs(isbp, true);
    set_profile(isbp, profile_path);
    set_force_serialize(isbp);
  });

  const auto& metric = pass_manager->get_pass_info().at(0).metrics;
  ASSERT_EQ(metric.at("method~violation~hot~callee~cold~callers"), 0);
}

namespace {
namespace access_methods {

struct Data {
  const char* profile;
  const char* field_access;
  const char* method_access;
};

} // namespace access_methods
} // namespace

class SourceBlocksAccessMethodsTest
    : public SourceBlocksTest,
      public testing::WithParamInterface<access_methods::Data> {};

TEST_P(SourceBlocksAccessMethodsTest, profile) {
  const auto& param = GetParam();
  auto* profile_path = std::getenv(param.profile);
  ASSERT_NE(profile_path, nullptr) << "Missing profile path.";

  auto* type = DexType::get_type("Lcom/facebook/redextest/SourceBlocksTest;");
  ASSERT_NE(type, nullptr);
  auto* cls = type_class(type);
  ASSERT_NE(cls, nullptr);

  // Check that no code has source blocks so far.
  {
    for (const auto* m : cls->get_all_methods()) {
      if (m->get_code() == nullptr) {
        continue;
      }
      for (const auto& mie : *m->get_code()) {
        ASSERT_NE(mie.type, MFLOW_SOURCE_BLOCK);
      }
    }
  }

  // Run the pass, check that each block has a SourceBlock.
  InsertSourceBlocksPass isbp{};

  run_passes({&isbp}, nullptr, Json::nullValue, [&](const auto&) {
    enable_pass(isbp);
    enable_always_inject(isbp);
    set_insert_after_excs(isbp, false);
    set_profile(isbp, profile_path);
  });

  UnorderedMap<std::string, std::string> kExpectations = {
      {"Lcom/facebook/redextest/SourceBlocksTest;.access$002:(Ljava/lang/"
       "String;)Ljava/lang/String;",
       param.field_access},
      {"Lcom/facebook/redextest/SourceBlocksTest;.access$100:()V",
       param.method_access},
  };

  for (auto* m : cls->get_all_methods()) {
    if (m->get_code() == nullptr) {
      continue;
    }
    if (m->get_name()->str().substr(0, 7) != "access$") {
      continue;
    }
    cfg::ScopedCFG cfg{m->get_code()};
    auto actual = get_blocks_as_txt_full(*cfg);
    auto it = kExpectations.find(show(m));
    if (it == kExpectations.end()) {
      EXPECT_TRUE(false) << "No expectation for " << show(m) << ": " << actual;
      continue;
    }
    EXPECT_EQ(actual, it->second) << show(m);
  }
}

INSTANTIATE_TEST_SUITE_P(
    AccessMethodsGroup,
    SourceBlocksAccessMethodsTest,
    testing::ValuesIn(std::vector<access_methods::Data>{
        {"profile_access_exact",
         "B0: "
         "Lcom/facebook/redextest/"
         "SourceBlocksTest;.access$redex5be80c743d1d526b$02:(Ljava/lang/"
         "String;)Ljava/lang/String;@0(0.1:0.2)",
         "B0: "
         "Lcom/facebook/redextest/"
         "SourceBlocksTest;.access$redex1bc24000ccc37110$00:()V@0(0.3:0."
         "4)"},
        {"profile_access_hash",
         "B0: "
         "Lcom/facebook/redextest/"
         "SourceBlocksTest;.access$redex5be80c743d1d526b$02:(Ljava/lang/"
         "String;)Ljava/lang/String;@0(0.6:0.7)",
         "B0: "
         "Lcom/facebook/redextest/"
         "SourceBlocksTest;.access$redex1bc24000ccc37110$00:()V@0(0.8:0."
         "9)"},
        {"profile_access_both",
         // When both are available prefer hash.
         "B0: "
         "Lcom/facebook/redextest/"
         "SourceBlocksTest;.access$redex5be80c743d1d526b$02:(Ljava/lang/"
         "String;)Ljava/lang/String;@0(0.6:0.7)",
         "B0: "
         "Lcom/facebook/redextest/"
         "SourceBlocksTest;.access$redex1bc24000ccc37110$00:()V@0(0.8:0."
         "9)"}}),
    [](const auto& info) { return info.param.profile; });

// End-to-end check that `violations_tracking.enabled` reaches the per-pass
// metrics through PassManager: config -> ViolationsTracking -> the per-pass
// Handler -> ScopedMetrics -> PassManager::set_metric.
TEST_F(SourceBlocksTest, violations_tracking_emits_per_pass_metrics) {
  Json::Value tracking = Json::objectValue;
  tracking["enabled"] = true;
  Json::Value conf_val = Json::objectValue;
  conf_val["violations_tracking"] = tracking;

  InsertSourceBlocksPass isbp{};
  run_passes({&isbp}, nullptr, conf_val, [&](const auto&) {
    enable_pass(isbp);
    enable_always_inject(isbp);
  });

  const auto& pass_info = pass_manager->get_pass_info();
  ASSERT_EQ(pass_info.size(), 1u);
  const auto& metrics = pass_info.front().metrics;
  EXPECT_NE(metrics.find("~violation~tracking.new_violations"), metrics.end());
  EXPECT_NE(metrics.find("~violation~tracking.new_method_violations"),
            metrics.end());
}

// The same run without the flag must not report anything, so that enabling
// tracking is what adds the metrics rather than the other way around.
TEST_F(SourceBlocksTest, violations_tracking_is_off_by_default) {
  InsertSourceBlocksPass isbp{};
  run_passes({&isbp}, nullptr, Json::nullValue, [&](const auto&) {
    enable_pass(isbp);
    enable_always_inject(isbp);
  });

  const auto& pass_info = pass_manager->get_pass_info();
  ASSERT_EQ(pass_info.size(), 1u);
  const auto& metrics = pass_info.front().metrics;
  EXPECT_EQ(metrics.find("~violation~tracking.new_violations"), metrics.end());
}
