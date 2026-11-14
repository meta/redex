/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>
#include <string>
#include <unordered_map>
#include <unordered_set>

#include "ApiLevelChecker.h"
#include "BaselineProfile.h"
#include "Creators.h"
#include "Debug.h"
#include "DexClass.h"
#include "DexStore.h"
#include "Dominators.h"
#include "IRAssembler.h"
#include "MethodProfiles.h"
#include "PassManager.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"
#include "ScopedCFG.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "VirtualMerging.h"

class VirtualMergingTest : public RedexTest {
 public:
  void SetUp() override {
    // Hierarchy:
    //                          LA;
    //        LA1;              LA2;               LA3;
    // LA11; LA12; LA13;  LA21; LA22; LA23;  LA31; LA32; LA33;

    auto make_class = [&](size_t idx,
                          const DexClass* super_class,
                          const char* name,
                          int32_t foo_val,
                          int32_t bar_val) {
      auto* const type = DexType::make_type(name);
      ClassCreator cls_creator(type);
      cls_creator.set_super(super_class != nullptr ? super_class->get_type()
                                                   : type::java_lang_Object());
      auto* ctor = DexMethod::make_method(std::string(name) + ".<init>:()V")
                       ->make_concrete(ACC_PUBLIC, false);
      cls_creator.add_method(ctor);
      if (ctor->get_code() != nullptr) {
        ctor->get_code()->build_cfg();
      }
      // Should add a super call here, but...

      auto make_code = [](int32_t val, auto mref, float sb_val) {
        std::string src = R"(
            (
              (load-param-object v1)
              (.src_block "Y" 0 (Z Z))
              (const v0 X)
              (return v0)
            ))";
        src.replace(src.find('X'), 1, std::to_string(val));
        src.replace(src.find('Z'), 1, std::to_string(sb_val));
        src.replace(src.find('Z'), 1, std::to_string(sb_val));
        src.replace(src.find('Y'), 1, show(mref));
        return assembler::ircode_from_string(src);
      };
      auto* foo_ref = DexMethod::make_method(std::string(name) + ".foo:()I");
      auto* foo =
          foo_ref->make_concrete(ACC_PUBLIC,
                                 make_code(foo_val, foo_ref, idx / 100.0f),
                                 /*is_virtual=*/true);
      cls_creator.add_method(foo);
      foo->get_code()->build_cfg();
      auto* bar_ref = DexMethod::make_method(std::string(name) + ".bar:()I");
      auto* bar =
          bar_ref->make_concrete(ACC_PUBLIC,
                                 make_code(bar_val, bar_ref, idx / 100.0f),
                                 /*is_virtual=*/true);
      cls_creator.add_method(bar);
      bar->get_code()->build_cfg();
      DexClass* res = cls_creator.create();
      if (super_class != nullptr) {
        subtypes[super_class].push_back(res);
      }
      auto it = types.emplace(idx, res);
      redex_assert(it.second);
      return res;
    };

    auto* a = make_class(0, nullptr, "LA;", 0, 0);

    auto* a1 = make_class(1, a, "LA1;", 1, -1);
    /* auto a11 = */ make_class(11, a1, "LA11;", 11, -11);
    /* auto a12 = */ make_class(12, a1, "LA12;", 12, -12);
    /* auto a13 = */ make_class(13, a1, "LA13;", 13, -13);

    auto* a2 = make_class(2, a, "LA2;", 2, -2);
    /* auto a21 = */ make_class(21, a2, "LA21;", 21, -21);
    /* auto a22 = */ make_class(22, a2, "LA22;", 22, -22);
    /* auto a23 = */ make_class(23, a2, "LA23;", 23, -23);

    auto* a3 = make_class(3, a, "LA3;", 3, -3);
    /* auto a31 = */ make_class(31, a3, "LA31;", 31, -31);
    /* auto a32 = */ make_class(32, a3, "LA32;", 32, -32);
    /* auto a33 = */ make_class(33, a3, "LA33;", 33, -33);

    stores = DexStoresVector{};
    stores.emplace_back("store");
    // Need to be in one vector to be "same dex.""
    std::vector<DexClass*> tmp;
    std::transform(
        types.begin(), types.end(), std::back_inserter(tmp), [](const auto& p) {
          return const_cast<DexClass*>(p.second);
        });
    stores[0].add_classes(tmp);
  }

  const DexMethod* get_method(size_t idx, const char* name) {
    for (auto* m : types.at(idx)->get_vmethods()) {
      if (m->get_name()->str() == name) {
        return m;
      }
    }
    return nullptr;
  }

  const DexType* get_type(size_t idx) { return types.at(idx)->get_type(); }

  struct OptFail {
    std::optional<::testing::AssertionResult> fail{std::nullopt};

    ::testing::AssertionResult& add_fail() {
      if (!fail) {
        fail = ::testing::AssertionFailure();
      }
      return *fail;
    }

    // NOLINTNEXTLINE(google-explicit-constructor)
    operator bool() const { return fail.operator bool(); }

    ::testing::AssertionResult result() {
      if (fail) {
        return *fail;
      }
      return ::testing::AssertionSuccess();
    }
  };

  // A dominator check tests ordering without having to be totally explicit and
  // at the whim of block linearization.
  ::testing::AssertionResult instanceof_dominators(
      const DexMethod* m,
      const std::vector<std::vector<const DexType*>>& order) {
    cfg::ScopedCFG cfg(const_cast<DexMethod*>(m)->get_code());

    auto all_types = [&]() {
      std::unordered_set<const DexType*> ret;
      for (const auto& v : order) {
        ret.insert(v.begin(), v.end());
      }
      return ret;
    }();

    std::unordered_map<const DexType*, cfg::Block*> all_blocks;
    {
      std::unordered_set<const DexType*> found;
      for (auto it = cfg::ConstInstructionIterator(*cfg, true); !it.is_end();
           ++it) {
        if (it->insn->opcode() == OPCODE_INSTANCE_OF) {
          auto* t = it->insn->get_type();
          if (all_types.count(t) != 0) {
            if (found.count(t) != 0u) {
              return ::testing::AssertionFailure()
                     << "Found type " << show(t) << " twice";
            }
            found.insert(t);
            all_blocks.emplace(t, it.block());
          }
        }
      }
      auto missing = all_types;
      std::erase_if(missing, [&found](auto t) { return found.count(t) != 0; });
      if (!missing.empty()) {
        auto ret = ::testing::AssertionFailure();
        ret << "Did not find type-check(s) for";
        for (const auto* t : missing) {
          ret << " " << show(t);
        }
        return ret;
      }
    };

    auto dom = dominators::SimpleFastDominators<cfg::GraphInterface>(*cfg);

    OptFail fail;

    for (const auto& v : order) {
      cfg::Block* last_block = nullptr;
      const DexType* last_type = nullptr;
      for (const auto* t : v) {
        auto* b = all_blocks.at(t);
        if (last_block == nullptr) {
          last_block = b;
          last_type = t;
          continue;
        }
        if (last_block == b) {
          fail.add_fail() << "\n"
                          << show(last_type) << " & " << show(t)
                          << " in same block";
          continue;
        }

        while (b != nullptr && last_block != b) {
          auto* next = dom.get_idom(b);
          if (next == b) {
            next = nullptr;
          }
          b = next;
        }

        if (last_block != b) {
          fail.add_fail() << "\n"
                          << show(last_type) << " does not dominate "
                          << show(t);
          continue;
        }

        last_block = all_blocks.at(t);
        last_type = t;
      }
    }

    return fail.result();
  }

  // Test that all `if` instructions after `instance-of` or the given opcode.
  ::testing::AssertionResult test_if_direction(const DexMethod* m,
                                               IROpcode expected) {
    cfg::ScopedCFG cfg(const_cast<DexMethod*>(m)->get_code());
    OptFail fail;
    for (auto* b : cfg->blocks()) {
      // Check if there's an INSTANCE_OF here.
      if (!b->contains_opcode(OPCODE_INSTANCE_OF)) {
        continue;
      }
      if (b->get_last_insn()->insn->opcode() != expected) {
        fail.add_fail() << "\nBlock " << b->id() << " ends with "
                        << show(b->get_last_insn()->insn);
      }
    }
    return fail.result();
  }

  ConfigFiles conf = ConfigFiles(Json::nullValue);

 protected:
  std::unordered_map<size_t, const DexClass*> types;
  std::unordered_map<const DexClass*, std::vector<const DexClass*>> subtypes;

  DexStoresVector stores;
};

TEST_F(VirtualMergingTest, DedupPreservesOverrideProfile) {
  auto* ancestor = const_cast<DexMethod*>(get_method(0, "foo"));
  auto* override = const_cast<DexMethod*>(get_method(1, "foo"));
  override->set_code(assembler::ircode_from_string(R"(
    ((load-param-object v1) (const v0 0) (return v0))
  )"));
  override->get_code()->build_cfg();
  method_profiles::Stats hot_stats{100.0, 10.0, 0.0, 21};
  Json::Value json;
  json["update_method_profiles_stats"] = true;
  ConfigFiles config(json);
  config.get_method_profiles() = method_profiles::MethodProfiles::initialize(
      "manual_hot", {{override, hot_stats}});
  config.parse_global_config();
  auto tmp_dir = redex::make_tmp_dir("virtual_dedup_profiles_test_%%%%%%%%");
  config.set_outdir(tmp_dir.path);
  VirtualMergingPass pass;
  PassManager manager({&pass}, config, RedexOptions{});

  manager.run_passes(stores, config);

  EXPECT_EQ(get_method(1, "foo"), nullptr);
  auto profile =
      config.get_method_profiles().get_method_stat("manual_hot", ancestor);
  ASSERT_TRUE(profile.has_value());
  EXPECT_EQ(*profile, hot_stats);
  auto baseline = baseline_profiles::get_default_baseline_profile(
      build_class_scope(stores),
      {{"default", {}}},
      config.get_method_profiles());
  EXPECT_TRUE(baseline_profiles::is_compiled(baseline, ancestor));
}

TEST_F(VirtualMergingTest, Armv7HardLimitSkipsLateMerge) {
  auto scope = build_class_scope(stores);
  auto count_virtual_methods = [&]() {
    size_t count{0};
    for (const auto& [_, cls] : types) {
      count += cls->get_vmethods().size();
    }
    return count;
  };
  auto methods_before = count_virtual_methods();

  api::LevelChecker::init(19, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.armv7_hard_max_instruction_size = 100;
  inliner_config.set_architecture(Architecture::ARMV7);
  inliner_config.populate(scope);

  VirtualMerging vm{stores, conf, inliner_config, 100};
  vm.run(method_profiles::MethodProfiles{},
         VirtualMerging::Strategy::kLexicographical,
         VirtualMerging::InsertionStrategy::kJumpTo);

  const auto& stats = vm.get_stats();
  EXPECT_GT(stats.removed_virtual_methods, 0);
  EXPECT_GT(stats.late_caller_too_large_methods, 0);
  EXPECT_EQ(stats.uninlinable_methods, 0);
  EXPECT_EQ(stats.caller_size_removed_methods, 0);
  EXPECT_EQ(methods_before - count_virtual_methods(),
            stats.removed_virtual_methods);
  EXPECT_EQ(stats.mergeable_pairs,
            stats.huge_methods + stats.uninlinable_methods +
                stats.caller_size_removed_methods +
                stats.late_caller_too_large_methods +
                stats.removed_virtual_methods);
}

TEST_F(VirtualMergingTest, MergedFooNoProfiles) {
  auto scope = build_class_scope(stores);

  api::LevelChecker::init(19, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);

  UnorderedMap<const DexMethodRef*, method_profiles::Stats> profile_data;
  auto make_call_count_stat = [](double call_count) {
    method_profiles::Stats stats{};
    stats.call_count = call_count;
    return stats;
  };
  // Normal order 3->2->1, reorder to 2->1->3.
  profile_data.emplace(get_method(23, "foo"), make_call_count_stat(100));
  profile_data.emplace(get_method(21, "foo"), make_call_count_stat(50));
  profile_data.emplace(get_method(1, "foo"), make_call_count_stat(100));

  VirtualMerging vm{stores, conf, inliner_config, 100};
  vm.run(method_profiles::MethodProfiles::initialize(
             method_profiles::COLD_START, std::move(profile_data)),
         VirtualMerging::Strategy::kLexicographical,
         VirtualMerging::InsertionStrategy::kJumpTo);

  const auto* a_foo = get_method(0, "foo");
  ASSERT_NE(nullptr, a_foo);

  EXPECT_TRUE(instanceof_dominators(
      a_foo,
      {
          {get_type(3), get_type(2), get_type(1)}, // Head block.
          {get_type(13), get_type(12), get_type(11)}, // A1 sub-block
          {get_type(23), get_type(22), get_type(21)}, // A2 sub-block
          {get_type(33), get_type(32), get_type(31)}, // A3 sub-block
      }));
  EXPECT_TRUE(test_if_direction(a_foo, OPCODE_IF_NEZ));

  // Check that we got source blocks inserted correctly.
  {
    cfg::ScopedCFG cfg(const_cast<DexMethod*>(a_foo)->get_code());
    auto blocks = cfg->blocks();
    bool all = std::all_of(blocks.begin(), blocks.end(), [](auto* b) {
      return source_blocks::has_source_blocks(b);
    });
    EXPECT_TRUE(all) << show(*cfg);
  }
}

TEST_F(VirtualMergingTest, MergedBarNoProfiles) {
  auto scope = build_class_scope(stores);

  api::LevelChecker::init(19, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);

  UnorderedMap<const DexMethodRef*, method_profiles::Stats> profile_data;
  auto make_call_count_stat = [](double call_count) {
    method_profiles::Stats stats{};
    stats.call_count = call_count;
    return stats;
  };
  // Normal order 3->2->1, reorder to 2->1->3.
  profile_data.emplace(get_method(23, "foo"), make_call_count_stat(100));
  profile_data.emplace(get_method(21, "foo"), make_call_count_stat(50));
  profile_data.emplace(get_method(1, "foo"), make_call_count_stat(100));

  VirtualMerging vm{stores, conf, inliner_config, 100};
  vm.run(method_profiles::MethodProfiles::initialize(
             method_profiles::COLD_START, std::move(profile_data)),
         VirtualMerging::Strategy::kLexicographical,
         VirtualMerging::InsertionStrategy::kJumpTo);

  const auto* a_bar = get_method(0, "bar");
  ASSERT_NE(nullptr, a_bar);

  EXPECT_TRUE(instanceof_dominators(
      a_bar,
      {
          {get_type(3), get_type(2), get_type(1)}, // Head block.
          {get_type(13), get_type(12), get_type(11)}, // A1 sub-block
          {get_type(23), get_type(22), get_type(21)}, // A2 sub-block
          {get_type(33), get_type(32), get_type(31)}, // A3 sub-block
      }));
}

TEST_F(VirtualMergingTest, MergedFooProfiles) {
  auto scope = build_class_scope(stores);

  api::LevelChecker::init(19, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);

  UnorderedMap<const DexMethodRef*, method_profiles::Stats> profile_data;
  auto make_call_count_stat = [](double call_count) {
    method_profiles::Stats stats{};
    stats.call_count = call_count;
    return stats;
  };
  // Normal order 3->2->1, reorder to 2->1->3.
  profile_data.emplace(get_method(23, "foo"), make_call_count_stat(100));
  profile_data.emplace(get_method(21, "foo"), make_call_count_stat(50));
  profile_data.emplace(get_method(1, "foo"), make_call_count_stat(100));

  VirtualMerging vm{stores, conf, inliner_config, 100};
  vm.run(method_profiles::MethodProfiles::initialize(
             method_profiles::COLD_START, std::move(profile_data)),
         VirtualMerging::Strategy::kProfileCallCount,
         VirtualMerging::InsertionStrategy::kJumpTo);

  const auto* a_foo = get_method(0, "foo");
  ASSERT_NE(nullptr, a_foo);

  EXPECT_TRUE(instanceof_dominators(
      a_foo,
      {
          {get_type(2), get_type(1), get_type(3)}, // Head block.
          {get_type(13), get_type(12), get_type(11)}, // A1 sub-block
          {get_type(23), get_type(21), get_type(22)}, // A2 sub-block
          {get_type(33), get_type(32), get_type(31)}, // A3 sub-block
      }));
}

TEST_F(VirtualMergingTest, MergedBarFooProfiles) {
  auto scope = build_class_scope(stores);

  api::LevelChecker::init(19, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);

  UnorderedMap<const DexMethodRef*, method_profiles::Stats> profile_data;
  auto make_call_count_stat = [](double call_count) {
    method_profiles::Stats stats{};
    stats.call_count = call_count;
    return stats;
  };
  // Normal order 3->2->1, reorder to 2->1->3.
  profile_data.emplace(get_method(23, "foo"), make_call_count_stat(100));
  profile_data.emplace(get_method(21, "foo"), make_call_count_stat(50));
  profile_data.emplace(get_method(1, "foo"), make_call_count_stat(100));

  VirtualMerging vm{stores, conf, inliner_config, 100};
  vm.run(method_profiles::MethodProfiles::initialize(
             method_profiles::COLD_START, std::move(profile_data)),
         VirtualMerging::Strategy::kProfileCallCount,
         VirtualMerging::InsertionStrategy::kJumpTo);

  const auto* a_bar = get_method(0, "bar");
  ASSERT_NE(nullptr, a_bar);

  EXPECT_TRUE(instanceof_dominators(
      a_bar,
      {
          {get_type(3), get_type(2), get_type(1)}, // Head block.
          {get_type(13), get_type(12), get_type(11)}, // A1 sub-block
          {get_type(23), get_type(22), get_type(21)}, // A2 sub-block
          {get_type(33), get_type(32), get_type(31)}, // A3 sub-block
      }));
}

TEST_F(VirtualMergingTest, MergedFooProfilesAppearBucketsAllAppear100) {
  auto scope = build_class_scope(stores);

  api::LevelChecker::init(19, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);

  UnorderedMap<const DexMethodRef*, method_profiles::Stats> profile_data;
  auto make_call_count_stat = [](double call_count, double appear100) {
    method_profiles::Stats stats{};
    stats.call_count = call_count;
    stats.appear_percent = appear100;
    return stats;
  };
  // Normal order 3->2->1, call-count 2->1->3, same appear..
  profile_data.emplace(get_method(23, "foo"), make_call_count_stat(100, 100));
  profile_data.emplace(get_method(21, "foo"), make_call_count_stat(50, 100));
  profile_data.emplace(get_method(1, "foo"), make_call_count_stat(100, 100));

  VirtualMerging vm{stores, conf, inliner_config, 100};
  vm.run(method_profiles::MethodProfiles::initialize(
             method_profiles::COLD_START, std::move(profile_data)),
         VirtualMerging::Strategy::kProfileCallCount,
         VirtualMerging::InsertionStrategy::kJumpTo);

  const auto* a_foo = get_method(0, "foo");
  ASSERT_NE(nullptr, a_foo);

  EXPECT_TRUE(instanceof_dominators(
      a_foo,
      {
          {get_type(2), get_type(1), get_type(3)}, // Head block.
          {get_type(13), get_type(12), get_type(11)}, // A1 sub-block
          {get_type(23), get_type(21), get_type(22)}, // A2 sub-block
          {get_type(33), get_type(32), get_type(31)}, // A3 sub-block
      }));
}

TEST_F(VirtualMergingTest, MergedFooProfilesAppearBucketsDiffAppear100) {
  auto scope = build_class_scope(stores);

  api::LevelChecker::init(19, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);

  UnorderedMap<const DexMethodRef*, method_profiles::Stats> profile_data;
  auto make_call_count_stat = [](double call_count, double appear100) {
    method_profiles::Stats stats{};
    stats.call_count = call_count;
    stats.appear_percent = appear100;
    return stats;
  };
  // Normal order 3->2->1, call-count 2->1->3, but with appear now 1->2->3.
  profile_data.emplace(get_method(23, "foo"), make_call_count_stat(90, 80));
  profile_data.emplace(get_method(22, "foo"), make_call_count_stat(100, 80));
  profile_data.emplace(get_method(21, "foo"), make_call_count_stat(50, 100));
  profile_data.emplace(get_method(1, "foo"), make_call_count_stat(90, 90));

  VirtualMerging vm{stores, conf, inliner_config, 100};
  vm.run(method_profiles::MethodProfiles::initialize(
             method_profiles::COLD_START, std::move(profile_data)),
         VirtualMerging::Strategy::kProfileAppearBucketsAndCallCount,
         VirtualMerging::InsertionStrategy::kJumpTo);

  const auto* a_foo = get_method(0, "foo");
  ASSERT_NE(nullptr, a_foo);

  EXPECT_TRUE(instanceof_dominators(
      a_foo,
      {
          {get_type(2), get_type(1), get_type(3)}, // Head block.
          {get_type(13), get_type(12), get_type(11)}, // A1 sub-block
          {get_type(21), get_type(22), get_type(23)}, // A2 sub-block
          {get_type(33), get_type(32), get_type(31)}, // A3 sub-block
      }));
}

TEST_F(VirtualMergingTest, MergedFooNoProfilesFallthrough) {
  auto scope = build_class_scope(stores);

  api::LevelChecker::init(19, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);

  UnorderedMap<const DexMethodRef*, method_profiles::Stats> profile_data;
  auto make_call_count_stat = [](double call_count) {
    method_profiles::Stats stats{};
    stats.call_count = call_count;
    return stats;
  };
  // Normal order 3->2->1, reorder to 2->1->3.
  profile_data.emplace(get_method(23, "foo"), make_call_count_stat(100));
  profile_data.emplace(get_method(21, "foo"), make_call_count_stat(50));
  profile_data.emplace(get_method(1, "foo"), make_call_count_stat(100));

  VirtualMerging vm{stores, conf, inliner_config, 100};
  vm.run(method_profiles::MethodProfiles::initialize(
             method_profiles::COLD_START, std::move(profile_data)),
         VirtualMerging::Strategy::kLexicographical,
         VirtualMerging::InsertionStrategy::kFallthrough);

  const auto* a_foo = get_method(0, "foo");
  ASSERT_NE(nullptr, a_foo);

  EXPECT_TRUE(instanceof_dominators(
      a_foo,
      {
          {get_type(3), get_type(2), get_type(1)}, // Head block.
          {get_type(13), get_type(12), get_type(11)}, // A1 sub-block
          {get_type(23), get_type(22), get_type(21)}, // A2 sub-block
          {get_type(33), get_type(32), get_type(31)}, // A3 sub-block
      }));
  EXPECT_TRUE(test_if_direction(a_foo, OPCODE_IF_EQZ));
}

TEST_F(VirtualMergingTest, PerfConfig) {
  auto scope = build_class_scope(stores);

  api::LevelChecker::init(19, scope);
  inliner::InlinerConfig inliner_config;
  inliner_config.populate(scope);

  UnorderedMap<const DexMethodRef*, method_profiles::Stats> profile_data;
  auto make_call_count_stat = [](double appear100, double call_count) {
    method_profiles::Stats stats{};
    stats.appear_percent = appear100;
    stats.call_count = call_count;
    return stats;
  };

  //                          LA;
  //        LA1;              LA2;               LA3;
  // LA11; LA12; LA13;  LA21; LA22; LA23;  LA31; LA32; LA33;
  //
  // Block LA12 & LA2.

  profile_data.emplace(get_method(12, "foo"), make_call_count_stat(100, 100));
  profile_data.emplace(get_method(2, "foo"), make_call_count_stat(95, 100));
  profile_data.emplace(get_method(1, "foo"), make_call_count_stat(89, 100));

  VirtualMerging::PerfConfig pc{90, 1};

  VirtualMerging vm{stores, conf, inliner_config, 100, nullptr, pc};
  vm.run(method_profiles::MethodProfiles::initialize(
             method_profiles::COLD_START, std::move(profile_data)),
         VirtualMerging::Strategy::kProfileCallCount,
         VirtualMerging::InsertionStrategy::kJumpTo);

  EXPECT_NE(get_method(0, "foo"), nullptr);

  EXPECT_EQ(get_method(1, "foo"), nullptr);
  EXPECT_NE(get_method(2, "foo"), nullptr);
  EXPECT_EQ(get_method(3, "foo"), nullptr);

  EXPECT_EQ(get_method(11, "foo"), nullptr);
  EXPECT_NE(get_method(12, "foo"), nullptr);
  EXPECT_EQ(get_method(13, "foo"), nullptr);

  EXPECT_NE(get_method(21, "foo"), nullptr);
  EXPECT_NE(get_method(22, "foo"), nullptr);
  EXPECT_NE(get_method(23, "foo"), nullptr);

  EXPECT_EQ(get_method(31, "foo"), nullptr);
  EXPECT_EQ(get_method(32, "foo"), nullptr);
  EXPECT_EQ(get_method(33, "foo"), nullptr);
}
