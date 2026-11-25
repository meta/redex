/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <algorithm>

#include <boost/filesystem/directory.hpp>
#include <boost/filesystem/operations.hpp>
#include <boost/filesystem/path.hpp>
#include <gtest/gtest.h>

#include "ApkResources.h"
#include "Creators.h"
#include "DexAnnotation.h"
#include "DexClass.h"
#include "GlobalConfig.h"
#include "IRAssembler.h"
#include "ReachableResources.h"
#include "RedexMappedFile.h"
#include "RedexResources.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"
#include "ResourcesTestDefs.h"
#include "ResourcesValidationHelper.h"
#include "Styles.h"
#include "androidfw/ResourceTypes.h"
#include "arsc/TestStructures.h"
#include "utils/Serialize.h"

using namespace boost::filesystem;

namespace {
// Make a temp dir and copy of input manifest file. Used to allow test cases
// to modify the file without interfering with other runs of the test.
void setup_resources_and_run(
    const std::function<void(const std::string& extract_dir, ApkResources*)>&
        callback) {
  auto tmp_dir = redex::make_tmp_dir("ApkResourcesTest%%%%%%%%");
  boost::filesystem::path p(tmp_dir.path);
  redex::copy_file(get_env("test_manifest_path"),
                   (p / "AndroidManifest.xml").string());
  redex::copy_file(get_env("test_res_path"), (p / "resources.arsc").string());

  auto layout_dir = p / "res/layout";
  create_directories(layout_dir);
  auto layout_dest = layout_dir.string() + "/activity_main.xml";
  redex::copy_file(get_env("test_layout_path"), layout_dest);

  auto raw_dir = p / "res/raw/";
  create_directories(raw_dir);

  path test_raw_path(get_env("test_raw_path"));
  for (const auto& entry :
       boost::filesystem::directory_iterator(test_raw_path)) {
    auto file = entry.path().filename().string();
    auto file_dest = raw_dir.string() + file;
    auto file_source = entry.path().string();
    redex::copy_file(file_source, file_dest);
  }

  ApkResources resources(tmp_dir.path);
  callback(tmp_dir.path, &resources);
}

DexStoresVector make_empty_stores() {
  DexStoresVector stores;
  DexStore store("classes");
  store.add_classes({});
  stores.emplace_back(store);
  return stores;
}

// Asserts that the given loaded resources.arsc file has an overlayable entry
// with two policies.
#define ASSERT_OVERLAYABLES(res_table)                                         \
  ({                                                                           \
    auto _arsc_file = (ResourcesArscFile*)(res_table).get();                   \
    auto& _table_parser = _arsc_file->get_table_snapshot().get_parsed_table(); \
    EXPECT_EQ(_table_parser.m_package_overlayables.size(), 1)                  \
        << "Package expected to have two <overlayable> elements!";             \
    EXPECT_EQ(_table_parser.m_package_overlayables.begin()->second.size(), 2)  \
        << "Package expected to have two <overlayable> elements!";             \
  })
} // namespace

TEST(ApkResources, TestReadManifest) {
  setup_resources_and_run(
      [&](const std::string& /*extract_dir*/, ApkResources* resources) {
        auto result = resources->get_min_sdk();
        EXPECT_EQ(*result, 21);

        auto package_name = resources->get_manifest_package_name();
        EXPECT_STREQ(package_name->c_str(), "com.fb.bundles");
      });
}

TEST(ApkResources, ReadLayoutResolveRefs) {
  setup_resources_and_run(
      [&](const std::string& /* unused */, ApkResources* resources) {
        UnorderedSet<std::string> layout_classes;
        UnorderedSet<std::string> attrs_to_read;
        attrs_to_read.emplace(ONCLICK_ATTRIBUTE);
        std::unordered_multimap<std::string, std::string> attribute_values;
        resources->collect_layout_classes_and_attributes(
            attrs_to_read, &layout_classes, &attribute_values);

        EXPECT_EQ(layout_classes.size(), 4);
        EXPECT_EQ(attribute_values.size(), 2);

        // One reference should have been resolved to two possible classes.
        EXPECT_EQ(layout_classes.count("A"), 1);
        EXPECT_EQ(layout_classes.count("B"), 1);
        EXPECT_EQ(layout_classes.count("com.fb.bundles.WickedCoolButton"), 1);
        EXPECT_EQ(layout_classes.count("com.fb.bundles.NiftyViewGroup"), 1);
      });
}

TEST(ApkResources, TestReadingWritingOverlays) {
  setup_resources_and_run([&](const std::string& temp_dir_path,
                              ApkResources* resources) {
    // Stash the original for comparisons.
    auto arsc_path =
        (boost::filesystem::path(temp_dir_path) / "resources.arsc").string();
    redex::copy_file(arsc_path, arsc_path + ".orig");
    auto res_table = resources->load_res_table();
    ASSERT_OVERLAYABLES(res_table);
    // Check the correct ids are returned as roots.
    auto overlayables = res_table->get_overlayable_id_roots();
    EXPECT_EQ(overlayables.size(),
              sample_app::EXPECTED_OVERLAYABLE_RESOURCES.size());
    for (auto& name : sample_app::EXPECTED_OVERLAYABLE_RESOURCES) {
      EXPECT_TRUE(is_overlayable(name, res_table.get()))
          << name << " is not overlayable!";
    }
    // Make a remapping that doesn't change anything, just to ensure builder
    // code is emitting the same file as was given.
    std::map<uint32_t, uint32_t> no_change_remapping;
    for (auto id : res_table->sorted_res_ids) {
      no_change_remapping.emplace(id, id);
    }
    res_table->remap_res_ids_and_serialize({}, no_change_remapping);
    EXPECT_TRUE(redex::are_files_equal(arsc_path, arsc_path + ".orig"))
        << "Round trip serialization is not equivalent!";
  });
}

TEST(ApkResources, TestRemappingOverlays) {
  setup_resources_and_run([&](const std::string& temp_dir_path,
                              ApkResources* resources) {
    // Stash the original for comparisons.
    auto arsc_path =
        (boost::filesystem::path(temp_dir_path) / "resources.arsc").string();
    auto arsc_size = boost::filesystem::file_size(arsc_path);
    auto res_table = resources->load_res_table();
    ASSERT_OVERLAYABLES(res_table);
    // Make a remapping that changes the last value in the binary file.
    std::map<uint32_t, uint32_t> remapping;
    for (auto id : res_table->sorted_res_ids) {
      remapping.emplace(id, id);
    }
    auto id = res_table->name_to_ids["yummy_orange"][0];
    constexpr uint32_t expected_value = 0x7f999999;
    remapping[id] = expected_value;
    res_table->remap_res_ids_and_serialize({}, remapping);
    // Verify the remapping took effect, which should rewrite the last 4 bytes
    // of the file.
    auto mapped_file = RedexMappedFile::open(arsc_path);
    auto* id_ptr =
        (uint32_t*)(mapped_file.const_data() + arsc_size - sizeof(uint32_t));
    EXPECT_EQ(*id_ptr, expected_value) << "Last ID was not remapped!";
  });
}

TEST(ApkResources, TestDeleteOverlayableIds) {
  // Make a hypothetical .arsc file with 3 dimensions, two of which are
  // overlayable. In a few steps the overlayable ids will be deleted, to verify
  // the overlayable header and policy shrinks, and is removed entirely.
  //
  // According to aapt2, it looks like the following:
  //
  // Binary APK
  // Package name=foo id=7f
  //   type dimen id=01 entryCount=3
  //     resource 0x7f010000 dimen/one
  //       () 10.000000dp
  //     resource 0x7f010001 dimen/two OVERLAYABLE
  //       () 20.000000dp
  //     resource 0x7f010002 dimen/three OVERLAYABLE
  //       () 30.000000dp
  auto global_strings_builder = std::make_shared<arsc::ResStringPoolBuilder>(
      android::ResStringPool_header::UTF8_FLAG);
  auto key_strings_builder = std::make_shared<arsc::ResStringPoolBuilder>(
      android::ResStringPool_header::UTF8_FLAG);
  key_strings_builder->add_string("one");
  key_strings_builder->add_string("two");
  key_strings_builder->add_string("three");
  auto type_strings_builder = std::make_shared<arsc::ResStringPoolBuilder>(0);
  type_strings_builder->add_string("dimen");

  auto package_builder =
      std::make_shared<arsc::ResPackageBuilder>(&foo_package);
  package_builder->set_key_strings(key_strings_builder);
  package_builder->set_type_strings(type_strings_builder);

  auto table_builder = std::make_shared<arsc::ResTableBuilder>();
  table_builder->set_global_strings(global_strings_builder);
  table_builder->add_package(package_builder);

  // dimen
  std::vector<android::ResTable_config*> dimen_configs{&default_config};
  std::vector<uint32_t> dimen_flags{0, 0, 0};
  auto dimen_type_definer = std::make_shared<arsc::ResTableTypeDefiner>(
      foo_package.id,
      1,
      dimen_configs,
      dimen_flags,
      false /* enable_canonical_entries */,
      false /* enable_sparse_encoding */);
  package_builder->add_type(dimen_type_definer);

  // Add the three entries
  EntryAndValue one(0, android::Res_value::TYPE_DIMENSION, 0xa01 /* 10dp */);
  EntryAndValue two(1, android::Res_value::TYPE_DIMENSION, 0x1401 /* 20dp */);
  EntryAndValue three(2, android::Res_value::TYPE_DIMENSION, 0x1e01 /* 30dp */);
  dimen_type_definer->add(&default_config, &one);
  dimen_type_definer->add(&default_config, &two);
  dimen_type_definer->add(&default_config, &three);

  // Basic info to describe two overlayable ids.
  uint32_t initial_ids[2] = {0x7f010001, 0x7f010002};
  uint32_t policy_size =
      sizeof(android::ResTable_overlayable_policy_header) + sizeof(initial_ids);

  android::ResTable_overlayable_policy_header policy{};
  policy.header.type = android::RES_TABLE_OVERLAYABLE_POLICY_TYPE;
  policy.header.headerSize =
      sizeof(android::ResTable_overlayable_policy_header);
  policy.header.size = policy_size;
  policy.entry_count = 2;
  policy.policy_flags = android::ResTable_overlayable_policy_header::SIGNATURE;

  android::ResTable_overlayable_header overlayable{};
  overlayable.header.type = android::RES_TABLE_OVERLAYABLE_TYPE;
  overlayable.header.headerSize = sizeof(android::ResTable_overlayable_header);
  overlayable.header.size =
      sizeof(android::ResTable_overlayable_header) + policy_size;
  overlayable.name[0] = 'y';
  overlayable.name[1] = 'o';

  arsc::OverlayInfo overlay_info(&overlayable);
  overlay_info.policies.emplace(&policy, initial_ids);
  package_builder->add_overlay(overlay_info);

  android::Vector<char> table_data;
  table_builder->serialize(&table_data);

  // Simple function to assert the number of overlayable related headers parsed.
  auto run_verify = [](ResourceTableFile* res_table,
                       size_t overlayable_count,
                       size_t policy_count,
                       const std::vector<uint32_t>& expected_ids) {
    auto* arsc_table = dynamic_cast<ResourcesArscFile*>(res_table);
    auto& parsed_table = arsc_table->get_table_snapshot().get_parsed_table();
    auto& parsed_overlays_map =
        parsed_table.m_package_overlayables.begin()->second;
    EXPECT_EQ(parsed_overlays_map.size(), overlayable_count)
        << "Incorrect size of overlayable headers";
    if (overlayable_count > 0) {
      auto* header = parsed_overlays_map.begin()->first;
      auto& parsed_info = parsed_overlays_map.begin()->second;
      EXPECT_EQ(parsed_info.policies.size(), policy_count)
          << "Incorrect size of policy headers";
      auto* policy_header = parsed_info.policies.begin()->first;
      EXPECT_EQ(policy_header->entry_count, expected_ids.size())
          << "Incorrect number of overlayable ids!";
      EXPECT_EQ(policy_header->header.size,
                sizeof(android::ResTable_overlayable_policy_header) +
                    expected_ids.size() * sizeof(uint32_t))
          << "Policy header size is incorrect.";
      EXPECT_EQ(header->header.size,
                sizeof(android::ResTable_overlayable_header) +
                    policy_header->header.size)
          << "Overlayable header size is incorrect.";
      auto* parsed_ids = parsed_info.policies.begin()->second;
      for (size_t i = 0; i < expected_ids.size(); i++) {
        EXPECT_EQ(parsed_ids[i], expected_ids[i])
            << "Incorrect ID at index " << i;
      }
    }
  };

  // Parse the above file and start deleting from it.
  auto tmp_dir = redex::make_tmp_dir("ApkResourcesTest%%%%%%%%");
  boost::filesystem::path tmp_path(tmp_dir.path);
  arsc::write_bytes_to_file(table_data, (tmp_path / "resources.arsc").string());

  // Base state
  {
    ApkResources resources(tmp_dir.path);
    auto res_table = resources.load_res_table();
    run_verify(res_table.get(), 1, 1, {0x7f010001, 0x7f010002});

    // Delete 0x7f010002
    res_table->delete_resource(0x7f010002);
    std::map<uint32_t, uint32_t> remapping{{0x7f010000, 0x7f010000},
                                           {0x7f010001, 0x7f010001}};
    res_table->remap_res_ids_and_serialize({}, remapping);
  }

  // After first deletion, file should look like this:
  //
  // Binary APK
  // Package name=foo id=7f
  //   type dimen id=01 entryCount=2
  //     resource 0x7f010000 dimen/one
  //       () 10.000000dp
  //     resource 0x7f010001 dimen/two OVERLAYABLE
  //       () 20.000000dp
  {
    ApkResources resources(tmp_dir.path);
    auto res_table = resources.load_res_table();
    run_verify(res_table.get(), 1, 1, {0x7f010001});

    // Delete 0x7f010001
    res_table->delete_resource(0x7f010001);
    std::map<uint32_t, uint32_t> remapping{{0x7f010000, 0x7f010000}};
    res_table->remap_res_ids_and_serialize({}, remapping);
  }

  // After second deletion, file should look like this:
  //
  // Binary APK
  // Package name=foo id=7f
  //   type dimen id=01 entryCount=1
  //     resource 0x7f010000 dimen/one
  //       () 10.000000dp
  {
    ApkResources resources(tmp_dir.path);
    auto res_table = resources.load_res_table();
    run_verify(res_table.get(), 0, 0, {});
  }
}

TEST(ApkResources, TestReachableRoots) {
  std::unordered_set<std::string> expected_resource_roots{
      "keep_me_unused_color", "keep_me_unused_str", "red", "welcome", "plate"};
  setup_resources_and_run(
      [&](const std::string& temp_dir_path, ApkResources* resources) {
        ResourceConfig global_resources_config;
        resources::ReachabilityOptions options;
        options.assume_reachable_prefixes.emplace_back("keep_me_");
        options.assume_reachable_names.insert("red");
        options.assume_reachable_names.insert("welcome");
        options.assume_reachable_names.insert("plate");
        auto res_table = resources->load_res_table();
        resources::ReachableResources reachable_resources(
            temp_dir_path, global_resources_config, options);
        // For this test, no roots from code are applicable.
        DexStoresVector stores = make_empty_stores();
        auto roots = reachable_resources.get_resource_roots(stores);
        for (const auto& name : expected_resource_roots) {
          auto expected_id = res_table->name_to_ids.at(name).at(0);
          EXPECT_EQ(roots.count(expected_id), 1)
              << name << " (0x" << std::hex << expected_id << std::dec
              << ") should have been returned as a reachable root!";
        }
      });
}

TEST(ApkResources, TestKeepResources) {
  UnorderedSet<std::string> expected_keep_resources{
      "CronetProviderClassName", "FooProviderClassName",
      "BarProviderClassName",    "AnakinProviderClassName",
      "YodaProviderClassName",   "PadmeProviderClassName",
      "NabooProviderClassName",  "ObiWanProviderClassName"};
  setup_resources_and_run(
      [&](const std::string& /* unused */, ApkResources* resources) {
        auto keep_resources_found = resources->get_all_keep_resources();
        EXPECT_EQ(expected_keep_resources, keep_resources_found);
      });
}

TEST(ApkResources, TestNames) {
  setup_resources_and_run(
      [&](const std::string& /* unused */, ApkResources* resources) {
        auto res_table = resources->load_res_table();
        EXPECT_TRUE(res_table->is_type_named(0x1, "array"));
        EXPECT_TRUE(res_table->is_type_named(0x2, "attr"));
      });
}

TEST(ApkResources, WalkReferences) {
  setup_resources_and_run(
      [&](const std::string& /* unused */, ApkResources* resources) {
        auto res_table = resources->load_res_table();
        validate_walk_references_for_resource(res_table.get());
      });
}

TEST(ApkResources, StyleAnalysis) {
  setup_resources_and_run(
      [&](const std::string& temp_dir_path, ApkResources* resources) {
        auto res_table = resources->load_res_table();
        std::vector<std::string> ambiguous_style_names{
            "AmbiguousBig", "AmbiguousParent", "AmbiguousSmall", "Confusing",
            "DupTheme1",    "DupTheme2",       "NightParent",    "Unclear"};

        DexStoresVector stores = make_empty_stores();
        resources::ReachabilityOptions options;
        UnorderedSet<uint32_t> additional_roots;
        ResourceConfig global_resource_config;
        StyleAnalysis style_analysis(temp_dir_path,
                                     global_resource_config,
                                     options,
                                     stores,
                                     additional_roots);
        auto ambiguous = style_analysis.ambiguous_styles();
        EXPECT_EQ(ambiguous.size(), ambiguous_style_names.size());
        for (auto& name : ambiguous_style_names) {
          auto id = res_table->name_to_ids.at(name).at(0);
          EXPECT_EQ(ambiguous.count(id), 1)
              << "Resource " << name << " should be marked as ambiguous";
        }
      });
}

class ApkResourcesCodeRootsTest : public RedexTest {};

// A static-get method handle of an R field reads the resource id, so the
// resource is a root like one whose field an sget reads. The method handle is
// tool-generated bytecode.
TEST_F(ApkResourcesCodeRootsTest, RFieldReadThroughMethodHandleIsRoot) {
  setup_resources_and_run(
      [&](const std::string& temp_dir_path, ApkResources* resources) {
        ResourceConfig global_resources_config;
        resources::ReachabilityOptions options;
        auto res_table = resources->load_res_table();
        auto get_roots = [&](DexStoresVector& stores) {
          resources::ReachableResources reachable_resources(
              temp_dir_path, global_resources_config, options);
          return reachable_resources.get_resource_roots(stores);
        };
        auto stores_without_code = make_empty_stores();
        auto roots_without_code = get_roots(stores_without_code);
        const auto& ids = res_table->sorted_res_ids;
        auto it = std::find_if(ids.begin(), ids.end(), [&](uint32_t id) {
          return roots_without_code.count(id) == 0;
        });
        ASSERT_NE(it, ids.end());
        uint32_t id = *it;

        ClassCreator r_creator(DexType::make_type("Lcom/example/R$color;"));
        r_creator.set_super(type::java_lang_Object());
        r_creator.set_access(ACC_PUBLIC | ACC_FINAL);
        auto* r_field =
            DexField::make_field("Lcom/example/R$color;.unused:I")
                ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL,
                                DexEncodedValue::zero_for_type(type::_int()));
        r_field->get_static_value()->value(id);
        r_creator.add_field(r_field);

        ClassCreator user_creator(DexType::make_type("Lcom/example/User;"));
        user_creator.set_super(type::java_lang_Object());
        user_creator.add_method(assembler::method_from_string(R"(
      (method (public static) "Lcom/example/User;.handle:()Ljava/lang/invoke/MethodHandle;"
        (
          (const-method-handle static-get "Lcom/example/R$color;.unused:I")
          (move-result-pseudo-object v0)
          (return-object v0)
        )
      )
    )"));

        DexStoresVector stores;
        DexStore store("classes");
        store.add_classes({r_creator.create(), user_creator.create()});
        stores.emplace_back(std::move(store));
        auto roots = get_roots(stores);
        EXPECT_EQ(roots.count(id), 1);
      });
}

// With `check_string_for_name` and `assume_id_inlined`, a resource whose name
// or id a string of code spells out, or whose id an integer of code holds, is a
// root, since code can look the resource up by it. The strings and integers
// among the bootstrap arguments of a call site count like those of other
// instructions.
TEST_F(ApkResourcesCodeRootsTest, CallSiteArgumentsAreRoots) {
  setup_resources_and_run([&](const std::string& temp_dir_path,
                              ApkResources* resources) {
    ResourceConfig global_resources_config;
    resources::ReachabilityOptions options;
    options.check_string_for_name = true;
    options.assume_id_inlined = true;
    auto res_table = resources->load_res_table();
    auto get_roots = [&](DexStoresVector& stores) {
      resources::ReachableResources reachable_resources(
          temp_dir_path, global_resources_config, options);
      return reachable_resources.get_resource_roots(stores);
    };
    auto stores_without_code = make_empty_stores();
    auto roots_without_code = get_roots(stores_without_code);
    // Four resources that are not roots without code: one named by its
    // name, one by its id in a string, and two by their ids as an int and as
    // a long.
    std::string name;
    uint32_t named_id{0};
    for (const auto& [resource_name, ids] : res_table->name_to_ids) {
      if (ids.size() == 1 && roots_without_code.count(ids[0]) == 0) {
        name = resource_name;
        named_id = ids[0];
        break;
      }
    }
    ASSERT_FALSE(name.empty());
    const auto& sorted_ids = res_table->sorted_res_ids;
    auto it =
        std::find_if(sorted_ids.begin(), sorted_ids.end(), [&](uint32_t id) {
          return id != named_id && roots_without_code.count(id) == 0;
        });
    ASSERT_NE(it, sorted_ids.end());
    uint32_t spelled_id = *it;
    auto it2 = std::find_if(std::next(it), sorted_ids.end(), [&](uint32_t id) {
      return id != named_id && roots_without_code.count(id) == 0;
    });
    ASSERT_NE(it2, sorted_ids.end());
    uint32_t integer_id = *it2;
    auto it3 = std::find_if(std::next(it2), sorted_ids.end(), [&](uint32_t id) {
      return id != named_id && roots_without_code.count(id) == 0;
    });
    ASSERT_NE(it3, sorted_ids.end());
    uint32_t long_id = *it3;

    ClassCreator user_creator(DexType::make_type("Lcom/example/User;"));
    user_creator.set_super(type::java_lang_Object());
    auto* use = assembler::method_from_string(R"(
      (method (public static) "Lcom/example/User;.use:()V"
        (
          (invoke-static () "Lcom/example/User;.placeholder:()V")
          (return-void)
        )
      )
    )");
    user_creator.add_method(use);
    std::vector<std::unique_ptr<DexEncodedValue>> args;
    args.emplace_back(new DexEncodedValueString(DexString::make_string(name)));
    args.emplace_back(new DexEncodedValueString(
        DexString::make_string(std::to_string(spelled_id))));
    args.emplace_back(new DexEncodedValuePrimitive(DEVT_INT, integer_id));
    args.emplace_back(new DexEncodedValuePrimitive(DEVT_LONG, long_id));
    redex::make_invoke_custom(use->get_code(), "run", "()V", std::move(args));

    DexStoresVector stores;
    DexStore store("classes");
    store.add_classes({user_creator.create()});
    stores.emplace_back(std::move(store));
    auto roots = get_roots(stores);
    EXPECT_EQ(roots.count(named_id), 1);
    EXPECT_EQ(roots.count(spelled_id), 1);
    EXPECT_EQ(roots.count(integer_id), 1);
    EXPECT_EQ(roots.count(long_id), 1);
  });
}
