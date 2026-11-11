/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ResourcesInliningPass.h"

#include <cstdint>
#include <gtest/gtest.h>
#include <sstream>

#include "ApkResources.h"
#include "ConfigFiles.h"
#include "Creators.h"
#include "IRAssembler.h"
#include "JarLoader.h"
#include "PassManager.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"
#include "Walkers.h"
#include "arsc/TestStructures.h"
#include "utils/Serialize.h"

class ResourcesInliningPassTest : public RedexTest {
 public:
  DexClass* class1;
  std::unordered_set<DexMethodRef*> dex_method_refs;
  Scope scope;
  UnorderedMap<uint32_t, resources::InlinableValue> inlinable_resources;

  ResourcesInliningPassTest() {
    std::string sdk_jar = android_sdk_jar_path();
    load_jar_file(DexLocation::make_location("", sdk_jar));

    class1 = assembler::class_from_string(R"(
      (class (public) "Lcom/facebook/R$bool;"
        (field (public static final) "Lcom/facebook/R$bool;.should_log:I" #123)
      )
    )");

    scope.push_back(class1);
  }
};

MethodTransformsMap build_test(
    const Scope& scope,
    const UnorderedMap<uint32_t, resources::InlinableValue>&
        inlinable_resources,
    const std::map<uint32_t, std::string>& id_to_name = {},
    const std::vector<std::string>& type_names = {},
    const std::optional<std::string>& package_name = std::nullopt) {
  walk::code(scope, [&](DexMethod*, IRCode& code) { code.build_cfg(); });

  auto transforms = ResourcesInliningPass::find_transformations(
      scope, inlinable_resources, id_to_name, type_names, package_name);
  return transforms;
}

TEST_F(ResourcesInliningPassTest, TestOptimizationHappy_Sad) {
  std::string code_class = R"(
    (class (public) "LBoo;"
      (method (public) "LBoo;.testMethod:()V"
        (
          (load-param-object v7)
          (invoke-virtual (v7)
          "Lcom/fb/resources/MainActivity;.getResources:()Landroid/content/res/Resources;")
          (move-result-pseudo-object v0)
          (sget "Lcom/facebook/R$bool;.should_log:I")
          (move-result-pseudo-object v1)
          (invoke-virtual (v0 v1) "Landroid/content/res/Resources;.getBoolean:(I)Z")
          (move-result-pseudo-object v1)
        )
      )
    )
  )";

  // TEST 1: Good! Should find 1
  resources::InlinableValue inlinable_value1;
  inlinable_value1.type = android::Res_value::TYPE_INT_BOOLEAN;
  inlinable_value1.bool_value = true;
  inlinable_resources.insert({123, inlinable_value1});
  DexClass* class2 = assembler::class_from_string(code_class);
  scope.push_back(class2);
  auto transforms1 = build_test(scope, inlinable_resources);
  EXPECT_EQ(transforms1.size(), 1);
  for (auto& val : UnorderedIterable(transforms1)) {
    for (auto& vec : val.second) {
      auto* insn = vec.insn;
      auto inlinable_data = std::get<resources::InlinableValue>(vec.inlinable);
      EXPECT_TRUE(insn->opcode() == OPCODE_INVOKE_VIRTUAL);
      EXPECT_EQ(insn->get_method(),
                DexMethod::get_method(
                    "Landroid/content/res/Resources;.getBoolean:(I)Z"));
      EXPECT_EQ(inlinable_data.bool_value, true);
      EXPECT_EQ(inlinable_data.type, android::Res_value::TYPE_INT_BOOLEAN);
    }
  }

  // TEST 2: Bad! Since no inlinable resources, should not find any
  inlinable_resources = {};
  auto transforms2 = build_test(scope, inlinable_resources);
  EXPECT_EQ(transforms2.size(), 0);
}

// TEST 3: Bad! No invoke-virtual on supported API calls
TEST_F(ResourcesInliningPassTest, TestOptimizationBad) {
  std::string code_class = R"(
    (class (public) "LBoo;"
      (method (public) "LBoo;.testMethod:()V"
        (
          (load-param-object v7)
          (invoke-virtual (v7)
          "Lcom/fb/resources/MainActivity;.getResources:()Landroid/content/res/Resources;")
          (move-result-pseudo-object v0)
          (sget "Lcom/facebook/R$bool;.should_log:I")
          (move-result-pseudo-object v1)
        )
      )
    )
  )";

  resources::InlinableValue inlinable_value1;
  inlinable_resources.insert({123, inlinable_value1});
  DexClass* class2 = assembler::class_from_string(code_class);
  scope.push_back(class2);
  auto transforms = build_test(scope, inlinable_resources);
  EXPECT_EQ(transforms.size(), 0);
}

namespace {

std::string get_resource_name_class(const std::string& class_name,
                                    uint32_t resource_id) {
  std::ostringstream oss;
  oss << "(class (public) \"L" << class_name << ";\"\n"
      << "  (method (public) \"L" << class_name << ";.testMethod:()V\"\n"
      << "    (\n"
      << "      (load-param-object v7)\n"
      << "      (invoke-virtual (v7) "
         "\"Lcom/fb/resources/MainActivity;.getResources:()Landroid/content/"
         "res/Resources;\")\n"
      << "      (move-result-pseudo-object v0)\n"
      << "      (const v1 " << resource_id << ")\n"
      << "      (invoke-virtual (v0 v1) "
         "\"Landroid/content/res/Resources;.getResourceName:(I)Ljava/lang/"
         "String;\")\n"
      << "      (move-result-pseudo-object v2)\n"
      << "    )\n"
      << "  )\n"
      << ")";
  return oss.str();
}

} // namespace

// A resource id read out of bytecode can name any package, but type_names
// describes the application package only, so its type id is not an index that
// vector is guaranteed to hold.
TEST_F(ResourcesInliningPassTest, TestTypeIdOutOfRangeIsSkipped) {
  // Element i is type id i + 1, so this table describes type id 0x01 alone.
  const std::vector<std::string> type_names = {"bool"};
  const std::optional<std::string> package_name = "com.fb.resources";

  // 0x7f0a0001 has type id 0x0a, past the end; 0x7f000001 has type id 0, which
  // would underflow the numbering.
  for (uint32_t resource_id : {0x7f0a0001u, 0x7f000001u}) {
    const std::map<uint32_t, std::string> id_to_name = {
        {resource_id, "should_log"}};
    Scope out_of_range_scope;
    out_of_range_scope.push_back(
        assembler::class_from_string(get_resource_name_class(
            "Boo" + std::to_string(resource_id), resource_id)));
    auto transforms = build_test(out_of_range_scope, inlinable_resources,
                                 id_to_name, type_names, package_name);
    EXPECT_EQ(transforms.size(), 0) << "resource id " << resource_id;
  }

  // A type id the table does describe still transforms.
  const uint32_t in_range_id = 0x7f010001;
  const std::map<uint32_t, std::string> id_to_name = {
      {in_range_id, "should_log"}};
  Scope in_range_scope;
  in_range_scope.push_back(assembler::class_from_string(
      get_resource_name_class("Yay", in_range_id)));
  auto transforms = build_test(in_range_scope, inlinable_resources, id_to_name,
                               type_names, package_name);
  EXPECT_EQ(transforms.size(), 1);
}

TEST_F(ResourcesInliningPassTest, GetStringCoercesSignedIntegerResources) {
  struct Case {
    uint8_t type;
    uint32_t data;
    std::string_view expected;
  };
  const std::vector<Case> cases = {
      {android::Res_value::TYPE_INT_DEC, 0xffffffffu, "-1"},
      {android::Res_value::TYPE_INT_DEC, 0x80000000u, "-2147483648"},
      {android::Res_value::TYPE_INT_DEC, 0, "0"},
      {android::Res_value::TYPE_INT_DEC, 0x7fffffffu, "2147483647"},
      {android::Res_value::TYPE_INT_HEX, 0xffffffffu, "0xffffffff"},
      {android::Res_value::TYPE_INT_HEX, 0, "0x0"},
      {android::Res_value::TYPE_INT_COLOR_ARGB8, 0xffffffffu, "#ffffffff"},
      {android::Res_value::TYPE_INT_COLOR_RGB8, 0x00aabbccu, "#aabbcc"},
      {android::Res_value::TYPE_INT_COLOR_ARGB4, 0, "#0"},
      {android::Res_value::TYPE_INT_BOOLEAN, 0xffffffffu, "true"},
      {android::Res_value::TYPE_INT_BOOLEAN, 0, "false"},
  };

  auto strings = std::make_shared<arsc::ResStringPoolBuilder>(
      android::ResStringPool_header::UTF8_FLAG);
  auto keys = std::make_shared<arsc::ResStringPoolBuilder>(
      android::ResStringPool_header::UTF8_FLAG);
  auto types = std::make_shared<arsc::ResStringPoolBuilder>(0);
  types->add_string("integer");
  auto package = std::make_shared<arsc::ResPackageBuilder>(&foo_package);
  package->set_key_strings(keys);
  package->set_type_strings(types);
  auto type = std::make_shared<arsc::ResTableTypeDefiner>(
      foo_package.id, 1,
      std::vector<android::ResTable_config*>{&default_config},
      std::vector<uint32_t>(cases.size(), 0), false, false);
  package->add_type(type);
  std::vector<EntryAndValue> entries;
  entries.reserve(cases.size());
  std::vector<DexMethod*> methods;
  for (size_t i = 0; i < cases.size(); ++i) {
    keys->add_string("value" + std::to_string(i));
    entries.emplace_back(i, cases[i].type, cases[i].data);
    type->add(&default_config, &entries.back());
    auto* method = DexMethod::make_method(
                       "LResourceCoercion;.value" + std::to_string(i) +
                       ":(Landroid/content/res/Resources;)Ljava/lang/String;")
                       ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
    std::ostringstream code;
    code << "((load-param-object v0) (const v1 " << (0x7f010000u + i)
         << ") (invoke-virtual (v0 v1) "
            "\"Landroid/content/res/Resources;.getString:(I)Ljava/lang/"
            "String;\")"
            " (move-result-object v2) (return-object v2))";
    method->set_code(assembler::ircode_from_string(code.str()));
    methods.push_back(method);
  }
  arsc::ResTableBuilder table;
  table.set_global_strings(strings);
  table.add_package(package);
  android::Vector<char> bytes;
  table.serialize(&bytes);
  auto tmp = redex::make_tmp_dir("ResourceCoercion%%%%%%%%");
  arsc::write_bytes_to_file(bytes, tmp.path + "/resources.arsc");

  ClassCreator creator(DexType::make_type("LResourceCoercion;"));
  creator.set_super(DexType::make_type("Ljava/lang/Object;"));
  for (auto* method : methods) {
    creator.add_method(method);
  }
  DexStore store("classes");
  store.add_classes({creator.create()});
  DexStoresVector stores;
  stores.push_back(std::move(store));
  Json::Value json;
  json["apk_dir"] = tmp.path;
  json["redex"]["passes"].append("ResourcesInliningPass");
  json["ResourcesInliningPass"]["resource_type_names"].append("integer");
  ConfigFiles config(json);
  config.parse_global_config();
  ResourcesInliningPass pass;
  PassManager manager({&pass}, config);
  manager.run_passes(stores, config);

  for (size_t i = 0; i < cases.size(); ++i) {
    methods[i]->get_code()->build_cfg();
    size_t string_count = 0;
    for (auto& mie : cfg::InstructionIterable(methods[i]->get_code()->cfg())) {
      EXPECT_NE(mie.insn->opcode(), OPCODE_INVOKE_VIRTUAL);
      if (mie.insn->opcode() == OPCODE_CONST_STRING) {
        ++string_count;
        EXPECT_EQ(mie.insn->get_string()->str(), cases[i].expected)
            << "case " << i;
      }
    }
    EXPECT_EQ(string_count, 1) << "case " << i;
  }
}
