/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "StringBuilderOutliner.h"

#include <gtest/gtest.h>

#include "Creators.h"
#include "IRAssembler.h"
#include "JarLoader.h"
#include "RedexTest.h"
#include "SourceBlocks.h"
#include "UsedVarsAnalysis.h"

using namespace stringbuilder_outliner;

namespace ptrs = local_pointers;
namespace uv = used_vars;

class StringBuilderOutlinerTest : public RedexTest {
 public:
  void SetUp() override {
    std::string sdk_jar = android_sdk_jar_path();
    // StringBuilderOutliner requires bunch of java.lang.* classes to be
    // defined. Loading the SDK JAR here ensures that.
    ASSERT_TRUE(load_jar_file(DexLocation::make_location("", sdk_jar)));

    m_config.min_outline_count = 1;

    m_stores.emplace_back("classes");
    m_stores[0].get_dexen().emplace_back();

    auto* init_method =
        DexMethod::get_method("Ljava/lang/StringBuilder;.<init>:()V");
    ASSERT_NE(init_method, nullptr);
    m_escape_summary_map.emplace(init_method, ptrs::EscapeSummary{});
    m_effect_summary_map.emplace(init_method, side_effects::Summary({0}));

    auto* init_string_method = DexMethod::get_method(
        "Ljava/lang/StringBuilder;.<init>:(Ljava/lang/String;)V");
    ASSERT_NE(init_string_method, nullptr);
    m_escape_summary_map.emplace(init_string_method, ptrs::EscapeSummary{});
    m_effect_summary_map.emplace(init_string_method,
                                 side_effects::Summary({0}));

    auto* append_string_method = DexMethod::get_method(
        "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/"
        "StringBuilder;");
    ASSERT_NE(append_string_method, nullptr);
    m_escape_summary_map.emplace(append_string_method,
                                 ptrs::EscapeSummary(ptrs::ParamSet{0}, {}));
    m_effect_summary_map.emplace(append_string_method,
                                 side_effects::Summary({0}));

    auto* append_long_method = DexMethod::get_method(
        "Ljava/lang/StringBuilder;.append:(J)Ljava/lang/StringBuilder;");
    ASSERT_NE(append_long_method, nullptr);
    m_escape_summary_map.emplace(append_long_method,
                                 ptrs::EscapeSummary(ptrs::ParamSet{0}, {}));
    m_effect_summary_map.emplace(append_long_method,
                                 side_effects::Summary({0}));

    auto* tostring_method = DexMethod::get_method(
        "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;");
    ASSERT_NE(tostring_method, nullptr);
    m_escape_summary_map.emplace(
        tostring_method,
        ptrs::EscapeSummary(ptrs::ParamSet{ptrs::FRESH_RETURN}, {}));
    m_effect_summary_map.emplace(tostring_method, side_effects::Summary());
  }

 protected:
  using Profile = std::vector<SourceBlock::Val>;

  DexMethod* make_profiled_caller(
      const char* name,
      const Profile& entry,
      const std::vector<std::optional<Profile>>& sites) {
    auto* caller_type = DexType::make_type("LStrings;");
    auto* cls = type_class(caller_type);
    if (cls == nullptr) {
      ClassCreator creator(caller_type);
      creator.set_super(type::java_lang_Object());
      cls = creator.create();
      m_stores.front().get_dexen().front().push_back(cls);
    }
    auto* method =
        DexMethod::make_method(std::string("LStrings;.") + name +
                               ":(ILjava/lang/String;)Ljava/lang/String;")
            ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
    std::string body = R"((
      (load-param v2)
      (load-param-object v1)
      (if-eqz v2 :concat)
      (return-object v1)
      (:concat)
    )";
    for (size_t i = 0; i < sites.size(); ++i) {
      body += R"(
        (new-instance "Ljava/lang/StringBuilder;")
        (move-result-pseudo-object v0)
        (invoke-direct (v0) "Ljava/lang/StringBuilder;.<init>:()V")
        (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
        (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
        (invoke-virtual (v0) "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;")
        (move-result-object v1)
      )";
    }
    body += "(return-object v1))";
    method->set_code(assembler::ircode_from_string(body));
    method->set_deobfuscated_name(show(method));
    cls->add_method(method);
    method->get_code()->build_cfg();
    auto& cfg = method->get_code()->cfg();
    const auto* src = method->get_deobfuscated_name_or_null();
    source_blocks::impl::BlockAccessor::push_source_block(
        cfg.entry_block(), std::make_unique<SourceBlock>(src, 0, entry));
    size_t i = 0;
    for (auto& mie : InstructionIterable(cfg)) {
      if (mie.insn->opcode() != OPCODE_NEW_INSTANCE) {
        continue;
      }
      auto it = cfg.find_insn(mie.insn);
      if (sites.at(i)) {
        it.block()->insert_before(
            it.unwrap(), std::make_unique<SourceBlock>(src, i + 1, *sites[i]));
      }
      ++i;
    }
    EXPECT_EQ(i, sites.size());
    return method;
  }

  std::unique_ptr<Outliner> outline_callers(
      const std::vector<DexMethod*>& callers) {
    auto outliner = std::make_unique<Outliner>(m_config);
    for (auto* method : callers) {
      outliner->analyze(*method->get_code());
    }
    outliner->create_outline_helpers(&m_stores);
    for (auto* method : callers) {
      outliner->transform(method, method->get_code());
    }
    return outliner;
  }

  DexMethod* profile_helper() {
    auto* ref = DexMethod::get_method(
        "Lcom/redex/OutlinedStringBuilders;.concat:(Ljava/lang/String;Ljava/"
        "lang/String;)Ljava/lang/String;");
    return ref == nullptr ? nullptr : ref->as_def();
  }

  void expect_helper_profile(const Profile& expected) {
    auto* helper = profile_helper();
    ASSERT_NE(helper, nullptr);
    size_t blocks = 0;
    for (auto* block : helper->get_code()->cfg().blocks()) {
      auto* sb = source_blocks::get_first_source_block(block);
      ASSERT_NE(sb, nullptr);
      EXPECT_EQ(sb->src, helper->get_deobfuscated_name_or_null());
      EXPECT_EQ(sb->id, SourceBlock::kSyntheticId);
      EXPECT_EQ(sb->next, nullptr);
      ASSERT_EQ(sb->vals_size, expected.size());
      for (size_t i = 0; i < expected.size(); ++i) {
        EXPECT_EQ(sb->get_at(i), expected[i]);
      }
      ++blocks;
    }
    EXPECT_GT(blocks, 0u);
  }

  Stats run_outliner(IRCode* code) {
    code->build_cfg();
    Outliner outliner(m_config);
    outliner.analyze(*code);
    outliner.create_outline_helpers(&m_stores);
    outliner.transform(nullptr, code);

    // Use OSDCE to remove any unused new-instance StringBuilder opcodes. When
    // running this pass against an app, the app's redex config should always
    // contain a run of OSDCE after StringBuilderOutlinerPass.
    remove_dead_instructions(code);
    code->clear_cfg();
    return outliner.get_stats();
  }

  void populate_summary_maps(
      const IRCode& code,
      ptrs::InvokeToSummaryMap* invoke_to_esc_summary_map,
      side_effects::InvokeToSummaryMap* invoke_to_eff_summary_map) {
    const auto& cfg = code.cfg();
    for (const auto* block : cfg.blocks()) {
      for (const auto& mie : InstructionIterable(block)) {
        const auto* insn = mie.insn;
        if (!opcode::is_an_invoke(insn->opcode())) {
          continue;
        }
        auto* method = insn->get_method();
        if (m_escape_summary_map.count(method) == 0u) {
          continue;
        }
        invoke_to_esc_summary_map->emplace(insn,
                                           m_escape_summary_map.at(method));
        invoke_to_eff_summary_map->emplace(insn,
                                           m_effect_summary_map.at(method));
      }
    }
  }

  void remove_dead_instructions(IRCode* code) {
    auto& cfg = code->cfg();
    ptrs::InvokeToSummaryMap invoke_to_esc_summary_map;
    side_effects::InvokeToSummaryMap invoke_to_eff_summary_map;
    populate_summary_maps(*code, &invoke_to_esc_summary_map,
                          &invoke_to_eff_summary_map);

    ptrs::FixpointIterator fp_iter(cfg, invoke_to_esc_summary_map);
    fp_iter.run(ptrs::Environment());
    uv::FixpointIterator used_vars_fp_iter(fp_iter, invoke_to_eff_summary_map,
                                           cfg);
    used_vars_fp_iter.run(uv::UsedVarsSet());

    for (const auto& it : uv::get_dead_instructions(cfg, used_vars_fp_iter)) {
      cfg.remove_insn(it);
    }
  }

  Config m_config;
  DexStoresVector m_stores;

  std::unordered_map<const DexMethodRef*, ptrs::EscapeSummary>
      m_escape_summary_map;
  std::unordered_map<const DexMethodRef*, side_effects::Summary>
      m_effect_summary_map;
};

TEST_F(StringBuilderOutlinerTest, ColdCallSitesDoNotInheritHotMethodEntries) {
  m_config.min_outline_count = Config{}.min_outline_count;
  std::vector<std::optional<Profile>> sites(5, Profile{{0, 0}});
  auto* a = make_profiled_caller("a", {{1, 100}}, sites);
  auto* b = make_profiled_caller("b", {{1, 100}}, sites);
  ASSERT_TRUE(source_blocks::method_is_hot(a));
  ASSERT_TRUE(source_blocks::method_is_hot(b));
  auto outliner = outline_callers({a, b});
  ASSERT_EQ(outliner->get_stats().helper_methods_created, 1u);
  ASSERT_EQ(outliner->get_stats().stringbuilders_removed, 10u);
  ASSERT_EQ(outliner->get_outlined_methods().size(), 1u);
  for (const auto& [helper, sources] :
       UnorderedIterable(outliner->get_outlined_methods())) {
    ASSERT_EQ(sources.size(), 10u);
    size_t invokes = 0;
    for (auto* caller : {a, b}) {
      for (const auto& mie : InstructionIterable(caller->get_code()->cfg())) {
        if (mie.insn->has_method() && mie.insn->get_method() == helper) {
          ++invokes;
          auto it = caller->get_code()->cfg().find_insn(mie.insn);
          auto* sb = source_blocks::get_last_source_block_before(it.block(),
                                                                 it.unwrap());
          ASSERT_NE(sb, nullptr);
          EXPECT_EQ(sb->get_at(0), (SourceBlock::Val{0, 0}));
        }
      }
    }
    ASSERT_EQ(invokes, 10u);
  }
  outliner->set_hot_method_from_callsite();
  expect_helper_profile({{0, 0}});
  EXPECT_FALSE(source_blocks::method_is_hot(profile_helper()));
}

TEST_F(StringBuilderOutlinerTest, HotCallSiteDoesNotRequireHotMethodEntry) {
  auto* caller = make_profiled_caller("a", {{0, 0}}, {Profile{{3, 40}}});
  ASSERT_FALSE(source_blocks::method_is_hot(caller));
  auto outliner = outline_callers({caller});
  outliner->set_hot_method_from_callsite();
  expect_helper_profile({{3, 40}});
}

TEST_F(StringBuilderOutlinerTest, RepeatedSitesSumCountsAndMaxAppearances) {
  auto* a = make_profiled_caller(
      "a", {{100, 100}, {100, 100}},
      {Profile{{2, 30}, SourceBlock::Val::none()}, Profile{{5, 60}, {4, 25}}});
  auto* b = make_profiled_caller("b", {{100, 100}, {100, 100}},
                                 {Profile{{0, 80}, {3, 50}}});
  auto outliner = outline_callers({a, b});
  ASSERT_EQ(outliner->get_outlined_methods().size(), 1u);
  for (const auto& [helper, sources] :
       UnorderedIterable(outliner->get_outlined_methods())) {
    EXPECT_EQ(sources.size(), 3u);
  }
  outliner->set_hot_method_from_callsite();
  expect_helper_profile({{7, 80}, {7, 50}});
}

TEST_F(StringBuilderOutlinerTest, NearestSourceBlockSurvivesCallerChanges) {
  auto* caller = make_profiled_caller("a", {{100, 100}}, {Profile{{9, 90}}});
  auto& cfg = caller->get_code()->cfg();
  for (auto& mie : InstructionIterable(cfg)) {
    if (!mie.insn->has_method() ||
        mie.insn->get_method() !=
            DexMethod::get_method(
                "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;")) {
      continue;
    }
    auto it = cfg.find_insn(mie.insn);
    auto* before =
        source_blocks::get_last_source_block_before(it.block(), it.unwrap());
    ASSERT_NE(before, nullptr);
    before->next = std::make_unique<SourceBlock>(
        caller->get_deobfuscated_name_or_null(), 2, Profile{{2, 20}});
    it.block()->insert_after(
        it.unwrap(),
        std::make_unique<SourceBlock>(caller->get_deobfuscated_name_or_null(),
                                      3, Profile{{99, 99}}));
  }
  auto outliner = outline_callers({caller});
  for (auto* block : cfg.blocks()) {
    source_blocks::foreach_source_block(
        block, [](auto* sb) { sb->fill({1000, 100}); });
  }
  caller->get_code()->clear_cfg();
  outliner->set_hot_method_from_callsite();
  expect_helper_profile({{2, 20}});
}

TEST_F(StringBuilderOutlinerTest, MissingSiteDoesNotFallBackToMethodEntry) {
  auto* caller = make_profiled_caller("a", {{100, 100}}, {std::nullopt});
  auto outliner = outline_callers({caller});
  ASSERT_EQ(outliner->get_stats().helper_methods_created, 1u);
  outliner->set_hot_method_from_callsite();
  ASSERT_NE(profile_helper(), nullptr);
  EXPECT_EQ(source_blocks::get_first_source_block(
                profile_helper()->get_code()->cfg().entry_block()),
            nullptr);
}

TEST_F(StringBuilderOutlinerTest, UnknownSiteValuesRemainUnknown) {
  auto* caller =
      make_profiled_caller("a", {{100, 100}, {100, 100}},
                           {Profile{SourceBlock::Val::none(), {0, 0}}});
  auto outliner = outline_callers({caller});
  outliner->set_hot_method_from_callsite();
  expect_helper_profile({SourceBlock::Val::none(), {0, 0}});
}

TEST_F(StringBuilderOutlinerTest, UnselectedHotSitesDoNotContribute) {
  m_config.max_outline_length = 1;
  auto* caller = make_profiled_caller("a", {{100, 100}}, {Profile{{3, 40}}});
  auto outliner = outline_callers({caller});
  outliner->set_hot_method_from_callsite();
  EXPECT_EQ(outliner->get_stats().helper_methods_created, 0u);
  EXPECT_TRUE(outliner->get_outlined_methods().empty());
  EXPECT_EQ(profile_helper(), nullptr);
}

TEST_F(StringBuilderOutlinerTest, DistinctHelpersUseOnlyTheirOwnSites) {
  auto* a = make_profiled_caller("a", {{100, 100}}, {Profile{{2, 20}}});
  auto* b = make_profiled_caller("b", {{100, 100}}, {Profile{{7, 70}}});
  auto& cfg = b->get_code()->cfg();
  IRInstruction* second_append = nullptr;
  size_t appends = 0;
  for (auto& mie : InstructionIterable(cfg)) {
    if (mie.insn->has_method() &&
        mie.insn->get_method() ==
            DexMethod::get_method("Ljava/lang/StringBuilder;.append:(Ljava/"
                                  "lang/String;)Ljava/lang/StringBuilder;")) {
      if (++appends == 2) {
        second_append = mie.insn;
      }
    }
  }
  ASSERT_NE(second_append, nullptr);
  cfg.remove_insn(cfg.find_insn(second_append));
  auto outliner = outline_callers({a, b});
  ASSERT_EQ(outliner->get_stats().helper_methods_created, 2u);
  ASSERT_EQ(outliner->get_outlined_methods().size(), 2u);
  outliner->set_hot_method_from_callsite();
  for (const auto& [helper, sources] :
       UnorderedIterable(outliner->get_outlined_methods())) {
    ASSERT_EQ(sources.size(), 1u);
    const bool two_args = helper->get_proto()->get_args()->size() == 2;
    EXPECT_EQ(sources.front(), two_args ? a : b);
    auto* sb = source_blocks::get_first_source_block(
        helper->get_code()->cfg().entry_block());
    ASSERT_NE(sb, nullptr);
    EXPECT_EQ(sb->get_at(0),
              two_args ? (SourceBlock::Val{2, 20}) : (SourceBlock::Val{7, 70}));
  }
}

TEST_F(StringBuilderOutlinerTest, outlineTwo) {
  auto code = assembler::ircode_from_string(R"(
    (
      (new-instance "Ljava/lang/StringBuilder;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "Ljava/lang/StringBuilder;.<init>:()V")
      (const-string "foo")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (invoke-virtual (v0) "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;")
      (move-result-object v0)
      (return-object v0)
    )
  )");

  run_outliner(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const-string "foo")
      (move-result-pseudo-object v1)
      (move-object v2 v1)
      (move-object v3 v1)
      (invoke-static (v2 v3) "Lcom/redex/OutlinedStringBuilders;.concat:(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;")
      (move-result-object v0)
      (return-object v0)
    )
  )");
  EXPECT_CODE_EQ(expected_code.get(), code.get());
}

/*
 * Check that we handle the StringBuilder(String) constructor correctly.
 */
TEST_F(StringBuilderOutlinerTest, stringArgBuilderConstructor) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const-string "foo")
      (move-result-pseudo-object v1)
      (new-instance "Ljava/lang/StringBuilder;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0 v1) "Ljava/lang/StringBuilder;.<init>:(Ljava/lang/String;)V")
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (invoke-virtual (v0) "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;")
      (move-result-object v0)
      (return-object v0)
    )
  )");

  run_outliner(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const-string "foo")
      (move-result-pseudo-object v1)
      (move-object v2 v1)
      (move-object v3 v1)
      (invoke-static (v2 v3) "Lcom/redex/OutlinedStringBuilders;.concat:(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;")
      (move-result-object v0)
      (return-object v0)
    )
  )");
  EXPECT_CODE_EQ(expected_code.get(), code.get());
}

TEST_F(StringBuilderOutlinerTest, trackReturnedStringBuilders) {
  auto code = assembler::ircode_from_string(R"(
    (
      (new-instance "Ljava/lang/StringBuilder;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "Ljava/lang/StringBuilder;.<init>:()V")
      (const-string "foo")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (move-result-object v0) ; make sure we track StringBuilder instances as they get returned
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (move-result-object v0)
      (invoke-virtual (v0) "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;")
      (move-result-object v0)
      (return-object v0)
    )
  )");

  run_outliner(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const-string "foo")
      (move-result-pseudo-object v1)
      (move-object v2 v1)
      (move-object v3 v1)
      (invoke-static (v2 v3) "Lcom/redex/OutlinedStringBuilders;.concat:(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;")
      (move-result-object v0)
      (return-object v0)
    )
  )");
  EXPECT_CODE_EQ(expected_code.get(), code.get());
}

TEST_F(StringBuilderOutlinerTest, outlineThree) {
  auto code = assembler::ircode_from_string(R"(
    (
      (new-instance "Ljava/lang/StringBuilder;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "Ljava/lang/StringBuilder;.<init>:()V")
      (const-string "foo")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (invoke-virtual (v0) "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;")
      (move-result-object v0)
      (return-object v0)
    )
  )");

  run_outliner(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const-string "foo")
      (move-result-pseudo-object v1)
      (move-object v2 v1)
      (move-object v3 v1)
      (move-object v4 v1)
      (invoke-static (v2 v3 v4) "Lcom/redex/OutlinedStringBuilders;.concat:(Ljava/lang/String;Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;")
      (move-result-object v0)
      (return-object v0)
    )
  )");
  EXPECT_CODE_EQ(expected_code.get(), code.get());

  auto* outline_cls =
      type_class(DexType::get_type("Lcom/redex/OutlinedStringBuilders;"));
  ASSERT_EQ(outline_cls->get_dmethods().size(), 1);

  auto* outline_helper_method = outline_cls->get_dmethods().at(0);
  auto expected_outlined_code = assembler::ircode_from_string(R"(
    (
      (load-param-object v1)
      (load-param-object v2)
      (load-param-object v3)
      (new-instance "Ljava/lang/StringBuilder;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "Ljava/lang/StringBuilder;.<init>:()V")
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (invoke-virtual (v0 v2) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (invoke-virtual (v0 v3) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (invoke-virtual (v0) "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;")
      (move-result-object v0)
      (return-object v0)
    )
  )");

  // Check that OSDCE recognizes the outline helper as side-effect-free. This
  // ensures that running StringBuilderOutlinerPass before OSDCE won't
  // inadvertently cause dead code to be retained.
  auto* outline_helper_code = outline_helper_method->get_code();
  // When outline_helper_method was created, it generated cfg.
  // Therefore, need to be cleared before comparing code.
  outline_helper_code->clear_cfg();
  EXPECT_CODE_EQ(expected_outlined_code.get(), outline_helper_code);

  outline_helper_code->build_cfg();
  auto& outline_helper_cfg = outline_helper_code->cfg();
  outline_helper_cfg.calculate_exit_block();

  ptrs::InvokeToSummaryMap invoke_to_esc_summary_map;
  side_effects::InvokeToSummaryMap invoke_to_eff_summary_map;
  populate_summary_maps(*outline_helper_code,
                        &invoke_to_esc_summary_map,
                        &invoke_to_eff_summary_map);

  ptrs::FixpointIterator ptrs_fp_iter(outline_helper_cfg,
                                      invoke_to_esc_summary_map);
  ptrs_fp_iter.run(ptrs::Environment());
  bool result_may_be_pointer = true;
  auto esc_summary = ptrs::get_escape_summary(
      ptrs_fp_iter, *outline_helper_code, result_may_be_pointer);
  EXPECT_EQ(esc_summary.returned_parameters,
            ptrs::ParamSet{ptrs::FRESH_RETURN});
  EXPECT_EQ(esc_summary.escaping_parameters.size(), 0);

  uv::FixpointIterator used_vars_fp_iter(
      ptrs_fp_iter, invoke_to_eff_summary_map, outline_helper_cfg);
  used_vars_fp_iter.run(uv::UsedVarsSet());

  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      {}, /* create_init_class_insns */ false);
  auto eff_summary = side_effects::analyze_code(
      init_classes_with_side_effects, invoke_to_eff_summary_map, ptrs_fp_iter,
      outline_helper_code);
  EXPECT_EQ(eff_summary, side_effects::Summary(side_effects::EFF_NONE, {}));
}

TEST_F(StringBuilderOutlinerTest, outlineWide) {
  auto code = assembler::ircode_from_string(R"(
    (
      (new-instance "Ljava/lang/StringBuilder;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "Ljava/lang/StringBuilder;.<init>:()V")
      (const-wide v1 123)
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(J)Ljava/lang/StringBuilder;")
      (const-string "foo")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (invoke-virtual (v0) "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;")
      (move-result-object v0)
      (return-object v0)
    )
  )");

  run_outliner(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const-wide v1 123)
      (move-wide v3 v1)
      (const-string "foo")
      (move-result-pseudo-object v1)
      (move-object v5 v1)
      (invoke-static (v3 v5) "Lcom/redex/OutlinedStringBuilders;.concat:(JLjava/lang/String;)Ljava/lang/String;")
      (move-result-object v0)
      (return-object v0)
    )
  )");
  EXPECT_CODE_EQ(expected_code.get(), code.get());
}

TEST_F(StringBuilderOutlinerTest, builderUsedInBranches) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v2)
      (new-instance "Ljava/lang/StringBuilder;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "Ljava/lang/StringBuilder;.<init>:()V")
      (const-string "foo") ; this value is reused by the two toString() calls
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")

      (if-eqz v2 :true-label)
      (const-string "bar")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (invoke-virtual (v0) "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;")
      (move-result-object v0)

      (:done)
      (return-object v0)

      (:true-label)
      (const-string "baz")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (invoke-virtual (v0) "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;")
      (move-result-object v0)
      (goto :done)
    )
  )");

  run_outliner(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v2)
      (const-string "foo")
      (move-result-pseudo-object v1)
      (move-object v3 v1)

      (if-eqz v2 :true-label)
      (const-string "bar")
      (move-result-pseudo-object v1)
      (move-object v4 v1)
      (invoke-static (v3 v4) "Lcom/redex/OutlinedStringBuilders;.concat:(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;")
      (move-result-object v0)

      (:done)
      (return-object v0)

      (:true-label)
      (const-string "baz")
      (move-result-pseudo-object v1)
      (move-object v5 v1)
      (invoke-static (v3 v5) "Lcom/redex/OutlinedStringBuilders;.concat:(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;")
      (move-result-object v0)
      (goto :done)
    )
  )");
  EXPECT_CODE_EQ(expected_code.get(), code.get());
}

/*
 * Check that we do not try to outline a StringBuilder if it is being appended
 * to in a loop.
 */
TEST_F(StringBuilderOutlinerTest, builderUsedinLoop) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v2)
      (new-instance "Ljava/lang/StringBuilder;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "Ljava/lang/StringBuilder;.<init>:()V")
      (const-string "foo")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")

      (:loop)
      (if-eqz v2 :end-loop)
      (const-string "bar")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (add-int/lit v2 v2 1)
      (goto :loop)
      (:end-loop)

      (invoke-virtual (v0) "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;")
      (move-result-object v0)
      (return-object v0)
    )
  )");

  auto expected = assembler::to_s_expr(code.get());
  run_outliner(code.get());
  EXPECT_EQ(expected, assembler::to_s_expr(code.get()));
}

/*
 * Check that do outline a StringBuilder even in the presence of a loop, as long
 * as that loop does not mutate it.
 */
TEST_F(StringBuilderOutlinerTest, builderNotUsedinLoop) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v2)
      (new-instance "Ljava/lang/StringBuilder;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "Ljava/lang/StringBuilder;.<init>:()V")
      (const-string "foo")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (const-string "bar")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")

      ; This loop does not mutate the StringBuilder, so the toString() call
      ; below can still be outlined.
      (:loop)
      (if-eqz v2 :end-loop)
      (add-int/lit v2 v2 1)
      (goto :loop)
      (:end-loop)

      (invoke-virtual (v0) "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;")
      (move-result-object v0)
      (return-object v0)
    )
  )");

  run_outliner(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v2)
      (const-string "foo")
      (move-result-pseudo-object v1)
      (move-object v3 v1)
      (const-string "bar")
      (move-result-pseudo-object v1)
      (move-object v4 v1)

      (:loop)
      (if-eqz v2 :end-loop)
      (add-int/lit v2 v2 1)
      (goto :loop)
      (:end-loop)

      (invoke-static (v3 v4) "Lcom/redex/OutlinedStringBuilders;.concat:(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;")
      (move-result-object v0)
      (return-object v0)
    )
  )");
  EXPECT_CODE_EQ(expected_code.get(), code.get());
}

/*
 * Check that we do not try to outline a StringBuilder if it is being passed a
 * mutable value.
 */
TEST_F(StringBuilderOutlinerTest, mutableCharSequence) {
  auto code = assembler::ircode_from_string(R"(
    (
      (new-instance "Ljava/lang/StringBuilder;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "Ljava/lang/StringBuilder;.<init>:()V")

      (const-string "foo")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")

      (new-instance "Ljava/lang/StringBuilder;")
      (move-result-pseudo-object v1)
      (invoke-direct (v1) "Ljava/lang/StringBuilder;.<init>:()V")
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/CharSequence;)Ljava/lang/StringBuilder;")

      (invoke-static (v1) "Lcom/test/Foo;.unknownMutation:(Ljava/lang/StringBuilder;)V")

      ; If we replaced this toString() call with an outlined helper method
      ; taking the string "foo" and the StringBuilder instance in v1, we would
      ; get incorrect results at runtime. The StringBuilder in v0 is reading the
      ; contents of the StringBuilder in v1 before the unknownMutation() call,
      ; but those contents may have changed by the time our outline helper
      ; method is called.
      (invoke-virtual (v0) "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;")
      (move-result-object v0)
      (return-object v0)
    )
  )");

  auto expected = assembler::to_s_expr(code.get());
  run_outliner(code.get());
  EXPECT_EQ(expected, assembler::to_s_expr(code.get()));
}

/*
 * Check that we do not outline `x.toString()` when an `append` call may target
 * either `x` or another StringBuilder `y`. Depending on `c`, `sb.append("b")`
 * appends to `y` or `x`, so `x` contains "a" on one branch and "ab" on the
 * other and cannot be replaced with a fixed `concat()` call.
 *
 *   static String f(boolean c) {
 *     StringBuilder x = new StringBuilder();
 *     StringBuilder y = new StringBuilder();
 *     StringBuilder sb = x;
 *     sb = sb.append("a");
 *     if (c) {
 *       sb = y;
 *     }
 *     sb.append("b");
 *     return x.toString();      // "a" if c, else "ab"
 *   }
 */
TEST_F(StringBuilderOutlinerTest, appendToEitherOfTwoBuildersNotOutlined) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v5)
      (new-instance "Ljava/lang/StringBuilder;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "Ljava/lang/StringBuilder;.<init>:()V")
      (new-instance "Ljava/lang/StringBuilder;")
      (move-result-pseudo-object v2)
      (invoke-direct (v2) "Ljava/lang/StringBuilder;.<init>:()V")
      (move-object v3 v0)
      (const-string "a")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (move-result-object v0)
      (if-eqz v5 :join)
      (move-object v0 v2)
      (:join)
      (const-string "b")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (invoke-virtual (v3) "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;")
      (move-result-object v4)
      (return-object v4)
    )
  )");

  auto expected = assembler::to_s_expr(code.get());
  run_outliner(code.get());
  EXPECT_EQ(expected, assembler::to_s_expr(code.get()));
}

/*
 * Check that we do not create invalid code if the builder is live-out. We will
 * will still outline the code but we won't remove the append instructions. This
 * does indeed cause code bloat instead of code reduction, but it's a pretty
 * rare case.
 */
TEST_F(StringBuilderOutlinerTest, builderAliasIsLiveOut) {
  auto code = assembler::ircode_from_string(R"(
    (
      (new-instance "Ljava/lang/StringBuilder;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "Ljava/lang/StringBuilder;.<init>:()V")
      (move-object v2 v0) ; create alias

      (const-string "foo")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")

      (const-string "baz")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")

      (invoke-virtual (v0) "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;")
      (move-result-object v0)

      ; v2 is live-out after the toString() call
      (invoke-static (v2) "Lcom/redex/Unknown;.foo:(Ljava/lang/StringBuilder;)V")

      (return-object v0)
    )
  )");

  run_outliner(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (new-instance "Ljava/lang/StringBuilder;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "Ljava/lang/StringBuilder;.<init>:()V")
      (move-object v2 v0)

      (const-string "foo")
      (move-result-pseudo-object v1)
      (move-object v3 v1)
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")

      (const-string "baz")
      (move-result-pseudo-object v1)
      (move-object v4 v1)
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")

      (invoke-static (v3 v4) "Lcom/redex/OutlinedStringBuilders;.concat:(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;")
      (move-result-object v0)

      (invoke-static (v2) "Lcom/redex/Unknown;.foo:(Ljava/lang/StringBuilder;)V")
      (return-object v0)
    )
  )");
  EXPECT_CODE_EQ(expected_code.get(), code.get());
}

/*
 * We don't handle multiple toString() calls on the same StringBuilder
 * efficiently, but that's a rare case anyway. However, this unit test at least
 * ensures that we don't generate invalid code.
 */
TEST_F(StringBuilderOutlinerTest, multipleToStringCalls) {
  auto code = assembler::ircode_from_string(R"(
    (
      (new-instance "Ljava/lang/StringBuilder;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "Ljava/lang/StringBuilder;.<init>:()V")

      (const-string "foo")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")

      (const-string "baz")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")

      (invoke-virtual (v0) "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;")
      (move-result-object v1)
      (invoke-virtual (v0) "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;")
      (move-result-object v2)

      (invoke-static (v1 v2) "Lcom/redex/Unknown;.foo:(Ljava/lang/String;Ljava/lang/String;)V")
      (return-void)
    )
  )");

  run_outliner(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (new-instance "Ljava/lang/StringBuilder;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "Ljava/lang/StringBuilder;.<init>:()V")

      (const-string "foo")
      (move-result-pseudo-object v1)
      (move-object v3 v1)
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")

      (const-string "baz")
      (move-result-pseudo-object v1)
      (move-object v4 v1)
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")

      (invoke-static (v3 v4) "Lcom/redex/OutlinedStringBuilders;.concat:(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;")
      (move-result-object v1)
      (invoke-virtual (v0) "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;")
      (move-result-object v2)

      (invoke-static (v1 v2) "Lcom/redex/Unknown;.foo:(Ljava/lang/String;Ljava/lang/String;)V")
      (return-void)
    )
  )");
  EXPECT_CODE_EQ(expected_code.get(), code.get());
}

/*
 * Check that the min_outline_count config setting is respected.
 */
TEST_F(StringBuilderOutlinerTest, minCount) {
  auto code = assembler::ircode_from_string(R"(
    (
      (new-instance "Ljava/lang/StringBuilder;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "Ljava/lang/StringBuilder;.<init>:()V")
      (const-string "foo")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (invoke-virtual (v0) "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;")
      (move-result-object v0)
      (return-object v0)
    )
  )");

  auto original = assembler::to_s_expr(code.get());
  m_config.min_outline_count = 2;
  run_outliner(code.get());
  EXPECT_EQ(original, assembler::to_s_expr(code.get()));

  m_config.min_outline_count = 1;
  run_outliner(code.get());
  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const-string "foo")
      (move-result-pseudo-object v1)
      (move-object v2 v1)
      (move-object v3 v1)
      (move-object v4 v1)
      (invoke-static (v2 v3 v4) "Lcom/redex/OutlinedStringBuilders;.concat:(Ljava/lang/String;Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;")
      (move-result-object v0)
      (return-object v0)
    )
  )");
  EXPECT_CODE_EQ(expected_code.get(), code.get());
}

/*
 * Check that the max_outline_length config setting is respected.
 */
TEST_F(StringBuilderOutlinerTest, maxLength) {
  auto code = assembler::ircode_from_string(R"(
    (
      (new-instance "Ljava/lang/StringBuilder;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "Ljava/lang/StringBuilder;.<init>:()V")
      (const-string "foo")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (invoke-virtual (v0) "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;")
      (move-result-object v0)
      (return-object v0)
    )
  )");

  auto original = assembler::to_s_expr(code.get());
  m_config.max_outline_length = 3;
  run_outliner(code.get());
  EXPECT_EQ(original, assembler::to_s_expr(code.get()));

  m_config.max_outline_length = 4;
  run_outliner(code.get());
  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const-string "foo")
      (move-result-pseudo-object v1)
      (move-object v2 v1)
      (move-object v3 v1)
      (move-object v4 v1)
      (move-object v5 v1)
      (invoke-static (v2 v3 v4 v5) "Lcom/redex/OutlinedStringBuilders;.concat:(Ljava/lang/String;Ljava/lang/String;Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;")
      (move-result-object v0)
      (return-object v0)
    )
  )");
  EXPECT_CODE_EQ(expected_code.get(), code.get());
}

/*
 * Ensure Ljava/lang/StringBuilder;.<init>:(Ljava/lang/String;)V is outlined
 * properly.
 */
TEST_F(StringBuilderOutlinerTest, stringArgConstructorBecomesAppendInHelper) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const-string "foo")
      (move-result-pseudo-object v1)
      (new-instance "Ljava/lang/StringBuilder;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0 v1) "Ljava/lang/StringBuilder;.<init>:(Ljava/lang/String;)V")
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (invoke-virtual (v0) "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;")
      (move-result-object v0)
      (return-object v0)
    )
  )");

  run_outliner(code.get());

  auto* helper_ref = DexMethod::get_method(
      "Lcom/redex/OutlinedStringBuilders;.concat:(Ljava/lang/String;Ljava/"
      "lang/String;)Ljava/lang/String;");
  ASSERT_NE(helper_ref, nullptr);
  ASSERT_TRUE(helper_ref->is_def());
  auto* helper_code = helper_ref->as_def()->get_code();
  ASSERT_NE(helper_code, nullptr);
  if (helper_code->cfg_built()) {
    helper_code->clear_cfg();
  }

  auto expected_helper = assembler::ircode_from_string(R"(
    (
      (load-param-object v1)
      (load-param-object v2)
      (new-instance "Ljava/lang/StringBuilder;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "Ljava/lang/StringBuilder;.<init>:()V")
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (invoke-virtual (v0 v2) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (invoke-virtual (v0) "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;")
      (move-result-object v0)
      (return-object v0)
    )
  )");
  EXPECT_CODE_EQ(expected_helper.get(), helper_code);
}

/*
 * Ensure it doesn't conflate two interwining StringBuilder-append-toString
 * chains.
 */
TEST_F(StringBuilderOutlinerTest, buildersSharingARegisterDoNotConflate) {
  auto code = assembler::ircode_from_string(R"(
    (
      (new-instance "Ljava/lang/StringBuilder;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "Ljava/lang/StringBuilder;.<init>:()V")
      (const-string "a")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (new-instance "Ljava/lang/StringBuilder;")
      (move-result-pseudo-object v2)
      (invoke-direct (v2) "Ljava/lang/StringBuilder;.<init>:()V")
      (const-string "b")
      (move-result-pseudo-object v3)
      (invoke-virtual (v2 v3) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (move-object v0 v2)
      (const-string "c")
      (move-result-pseudo-object v4)
      (invoke-virtual (v0 v4) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (invoke-virtual (v0) "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;")
      (move-result-object v0)
      (return-object v0)
    )
  )");

  run_outliner(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const-string "b")
      (move-result-pseudo-object v3)
      (move-object v5 v3)
      (const-string "c")
      (move-result-pseudo-object v4)
      (move-object v6 v4)
      (invoke-static (v5 v6) "Lcom/redex/OutlinedStringBuilders;.concat:(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;")
      (move-result-object v0)
      (return-object v0)
    )
  )");
  EXPECT_CODE_EQ(expected_code.get(), code.get());
}

TEST_F(StringBuilderOutlinerTest, hotOutlinedCallSiteIsCountedAsHot) {
  auto code = assembler::ircode_from_string(R"(
    (
      (.src_block "LFoo;.bar:()V" 0 (1.0 1.0))
      (new-instance "Ljava/lang/StringBuilder;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "Ljava/lang/StringBuilder;.<init>:()V")
      (const-string "foo")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (invoke-virtual (v0) "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;")
      (move-result-object v0)
      (return-object v0)
    )
  )");

  auto stats = run_outliner(code.get());

  EXPECT_EQ(stats.tostring_outlined_hot.load(), 1);
}

TEST_F(StringBuilderOutlinerTest, coldOutlinedCallSiteIsNotCountedAsHot) {
  auto code = assembler::ircode_from_string(R"(
    (
      (.src_block "LFoo;.bar:()V" 0 (0.0 0.0))
      (new-instance "Ljava/lang/StringBuilder;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "Ljava/lang/StringBuilder;.<init>:()V")
      (const-string "foo")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (invoke-virtual (v0) "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;")
      (move-result-object v0)
      (return-object v0)
    )
  )");

  auto stats = run_outliner(code.get());

  EXPECT_EQ(stats.tostring_outlined_hot.load(), 0);
}

TEST_F(StringBuilderOutlinerTest, hotCallSiteLeftInlineIsNotCountedAsOutlined) {
  auto code = assembler::ircode_from_string(R"(
    (
      (.src_block "LFoo;.bar:()V" 0 (1.0 1.0))
      (new-instance "Ljava/lang/StringBuilder;")
      (move-result-pseudo-object v0)
      (invoke-direct (v0) "Ljava/lang/StringBuilder;.<init>:()V")
      (const-string "foo")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;")
      (invoke-virtual (v0) "Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;")
      (move-result-object v0)
      (return-object v0)
    )
  )");

  m_config.min_outline_count = 2;
  auto stats = run_outliner(code.get());

  EXPECT_EQ(stats.tostring_outlined_hot.load(), 0);
}
