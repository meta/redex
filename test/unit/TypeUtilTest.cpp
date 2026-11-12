/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "TypeUtil.h"

#include "RedexTest.h"

class TypeUtilTest : public RedexTest {

 protected:
  const std::array<char, 9> PRIMS{
      {'Z', 'B', 'S', 'C', 'I', 'J', 'F', 'D', 'V'}};
};

TEST_F(TypeUtilTest, test_reference_type_wrappers) {
  EXPECT_EQ(type::get_boxed_reference_type(DexType::make_type("Z")),
            DexType::make_type("Ljava/lang/Boolean;"));
  EXPECT_EQ(type::get_boxed_reference_type(DexType::make_type("B")),
            DexType::make_type("Ljava/lang/Byte;"));
  EXPECT_EQ(type::get_boxed_reference_type(DexType::make_type("S")),
            DexType::make_type("Ljava/lang/Short;"));
  EXPECT_EQ(type::get_boxed_reference_type(DexType::make_type("C")),
            DexType::make_type("Ljava/lang/Character;"));
  EXPECT_EQ(type::get_boxed_reference_type(DexType::make_type("I")),
            DexType::make_type("Ljava/lang/Integer;"));
  EXPECT_EQ(type::get_boxed_reference_type(DexType::make_type("J")),
            DexType::make_type("Ljava/lang/Long;"));
  EXPECT_EQ(type::get_boxed_reference_type(DexType::make_type("F")),
            DexType::make_type("Ljava/lang/Float;"));
  EXPECT_EQ(type::get_boxed_reference_type(DexType::make_type("D")),
            DexType::make_type("Ljava/lang/Double;"));
}

TEST_F(TypeUtilTest, is_valid_empty) {
  using namespace type;

  EXPECT_FALSE(is_valid(""));
}

TEST_F(TypeUtilTest, is_valid_primitive) {
  using namespace type;

  for (char c : PRIMS) {
    std::string str(1, c);
    EXPECT_TRUE(is_valid(str)) << str;
    str.append("X");
    EXPECT_FALSE(is_valid(str)) << str;
  }
}

TEST_F(TypeUtilTest, is_valid_primitive_array) {
  using namespace type;

  EXPECT_FALSE(is_valid("["));

  std::string prefix = "[";

  for (char c : PRIMS) {
    std::string ok = prefix + c;
    EXPECT_TRUE(is_valid(ok)) << ok;

    std::string not_ok = ok + 'X';
    EXPECT_FALSE(is_valid(not_ok)) << not_ok;

    std::string nested_ok = prefix + ok;
    EXPECT_TRUE(is_valid(nested_ok)) << nested_ok;

    std::string nested_not_ok = nested_ok + 'X';
    EXPECT_FALSE(is_valid(nested_not_ok)) << nested_not_ok;
  }
}

namespace {

std::array<std::pair<std::string, bool>, 8> REF_SAMPLES = {
    std::make_pair<std::string, bool>("Foo", false),
    std::make_pair<std::string, bool>("LFoo", false),
    std::make_pair<std::string, bool>("LFoo;", true),
    std::make_pair<std::string, bool>("LFoo;;", false),

    std::make_pair<std::string, bool>("LFoo_Bar-Baz$A0123;", true),

    std::make_pair<std::string, bool>("Lfoo/bar/Baz;", true),
    std::make_pair<std::string, bool>("Lfoo;bar/Baz;", false),
    std::make_pair<std::string, bool>("Lfoo//Baz;", false),
};

} // namespace

TEST_F(TypeUtilTest, is_valid_reference) {
  using namespace type;

  for (const auto& p : REF_SAMPLES) {
    EXPECT_EQ(p.second, is_valid(p.first)) << p.first;
  }
}

TEST_F(TypeUtilTest, is_valid_reference_array) {
  using namespace type;

  std::string prefix = "[";

  for (const auto& p : REF_SAMPLES) {
    std::string single = prefix + p.first;
    EXPECT_EQ(p.second, is_valid(single)) << single;

    std::string not_ok = single + 'X';
    EXPECT_FALSE(is_valid(not_ok)) << not_ok;

    std::string nested = prefix + single;
    EXPECT_EQ(p.second, is_valid(nested)) << nested;

    std::string nested_not_ok = nested + 'X';
    EXPECT_FALSE(is_valid(nested_not_ok)) << nested_not_ok;
  }
}

TEST_F(TypeUtilTest, is_valid_array) {
  using namespace type;

  // Invalid arrays.
  EXPECT_FALSE(is_valid("["));
  EXPECT_FALSE(is_valid("[["));
  EXPECT_FALSE(is_valid("[o"));
  EXPECT_FALSE(is_valid("[L;"));
  EXPECT_FALSE(is_valid("[;"));
}

TEST_F(TypeUtilTest, check_cast_array) {
  using namespace type;

  EXPECT_FALSE(check_cast(DexType::make_type("[I"), DexType::make_type("[J")));
  EXPECT_FALSE(check_cast(DexType::make_type("[Z"), DexType::make_type("[B")));
  EXPECT_FALSE(check_cast(DexType::make_type("[F"), DexType::make_type("[D")));
  EXPECT_TRUE(check_cast(DexType::make_type("[I"),
                         DexType::make_type("Ljava/lang/Object;")));

  EXPECT_TRUE(check_cast(DexType::make_type("[Ljava/lang/Object;"),
                         DexType::make_type("[Ljava/lang/Object;")));
  EXPECT_TRUE(check_cast(DexType::make_type("[Ljava/lang/Object;"),
                         DexType::make_type("Ljava/lang/Object;")));
  EXPECT_TRUE(check_cast(DexType::make_type("[[Ljava/lang/Object;"),
                         DexType::make_type("[[Ljava/lang/Object;")));
  EXPECT_FALSE(check_cast(DexType::make_type("[Ljava/lang/Object;"),
                          DexType::make_type("[[Ljava/lang/Object;")));
  EXPECT_TRUE(check_cast(DexType::make_type("[[Ljava/lang/Object;"),
                         DexType::make_type("[Ljava/lang/Object;")));
}

TEST_F(TypeUtilTest, same_package) {
  using namespace type;

  EXPECT_TRUE(same_package(DexType::make_type("Ljava/lang/Object;"),
                           DexType::make_type("Ljava/lang/Object;")));

  EXPECT_TRUE(same_package(DexType::make_type("Ljava/lang/Object;"),
                           DexType::make_type("Ljava/lang/String;")));

  EXPECT_FALSE(same_package(DexType::make_type("Ljava/lang/Object;"),
                            DexType::make_type("Ljava/util/List;")));
}

TEST_F(TypeUtilTest, same_package_sub_package) {
  using namespace type;

  EXPECT_TRUE(same_package(DexType::make_type("Ljava/lang/Object;"),
                           DexType::make_type("Ljava/lang/Object;")));

  EXPECT_FALSE(same_package(DexType::make_type("Ljava/lang/Object;"),
                            DexType::make_type("Ljava/lang/reflect/Method;")));
}

TEST_F(TypeUtilTest, array_lookups_return_existing_types) {
  using namespace type;

  auto* object = DexType::make_type("Ljava/lang/Object;");
  auto* array = DexType::make_type("[Ljava/lang/Object;");
  auto* nested = DexType::make_type("[[Ljava/lang/Object;");

  EXPECT_EQ(get_array_component_type(array), object);
  EXPECT_EQ(get_array_component_type(nested), array);
  EXPECT_EQ(get_array_element_type(nested), object);
  EXPECT_EQ(get_element_type_if_array(nested), object);
}

TEST_F(TypeUtilTest, array_lookups_do_not_create_types) {
  using namespace type;

  auto* nested = DexType::make_type("[[Lmissing/T;");

  EXPECT_EQ(get_array_component_type(nested), nullptr);
  EXPECT_EQ(get_array_element_type(nested), nullptr);
  EXPECT_EQ(get_element_type_if_array(nested), nullptr);
  EXPECT_EQ(DexType::get_type("[Lmissing/T;"), nullptr);
  EXPECT_EQ(DexType::get_type("Lmissing/T;"), nullptr);
}

TEST_F(TypeUtilTest, array_lookups_on_non_array_types) {
  using namespace type;

  auto* object = DexType::make_type("Ljava/lang/Object;");

  EXPECT_EQ(get_array_component_type(object), nullptr);
  EXPECT_EQ(get_array_element_type(object), nullptr);
  EXPECT_EQ(get_element_type_if_array(object), object);
}

TEST_F(TypeUtilTest, array_checks_do_not_create_component_types) {
  using namespace type;

  auto* array = DexType::make_type("[Lmissing/T;");

  EXPECT_FALSE(is_java_lang_object_array(array));
  EXPECT_FALSE(is_enum_array(array));
  EXPECT_TRUE(is_reference_array(array));
  EXPECT_EQ(DexType::get_type("Lmissing/T;"), nullptr);
}

TEST_F(TypeUtilTest, array_checks) {
  using namespace type;

  EXPECT_TRUE(
      is_java_lang_object_array(DexType::make_type("[Ljava/lang/Object;")));
  EXPECT_FALSE(
      is_java_lang_object_array(DexType::make_type("[[Ljava/lang/Object;")));
  EXPECT_FALSE(is_java_lang_object_array(java_lang_Object()));
  EXPECT_TRUE(is_enum_array(DexType::make_type("[Ljava/lang/Enum;")));
  EXPECT_FALSE(is_enum_array(java_lang_Enum()));
  EXPECT_TRUE(is_reference_array(DexType::make_type("[[I")));
  EXPECT_FALSE(is_reference_array(DexType::make_type("[I")));
  EXPECT_FALSE(is_reference_array(java_lang_Object()));
}
