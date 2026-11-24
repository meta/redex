/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "TypeUtil.h"

#include <latch>
#include <thread>
#include <vector>

#include "Creators.h"
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

// A fresh context loads its well-known pointers on first use, which may come
// from several threads at once.
TEST_F(TypeUtilTest, concurrent_first_use_of_well_known_types) {
  constexpr size_t kThreads = 8;
  std::latch start(kThreads);
  std::vector<DexType*> objects(kThreads);
  std::vector<std::thread> threads;
  threads.reserve(kThreads);
  for (size_t i = 0; i < kThreads; i++) {
    threads.emplace_back([&start, &objects, i] {
      start.arrive_and_wait();
      objects[i] = type::java_lang_Object();
    });
  }
  for (auto& thread : threads) {
    thread.join();
  }
  auto* object = DexType::get_type("Ljava/lang/Object;");
  ASSERT_NE(object, nullptr);
  for (auto* loaded : objects) {
    EXPECT_EQ(loaded, object);
  }
}

TEST_F(TypeUtilTest, is_instance_of_if_known) {
  using namespace type;
  auto* object = java_lang_Object();
  auto* serializable = DexType::make_type("Ljava/io/Serializable;");
  auto* number = DexType::make_type("Ljava/lang/Number;");
  auto* integer = java_lang_Integer();
  // Unlike `check_cast`, no answer while Integer's hierarchy is unknown.
  EXPECT_EQ(is_instance_of_if_known(integer, serializable), std::nullopt);

  ClassCreator(object).create();
  ClassCreator sc(serializable);
  sc.set_super(object);
  sc.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
  sc.create();
  ClassCreator nc(number);
  nc.set_super(object);
  nc.add_interface(serializable);
  nc.create();
  ClassCreator ic(integer);
  ic.set_super(number);
  ic.create();

  EXPECT_EQ(is_instance_of_if_known(integer, serializable), true);
  EXPECT_EQ(is_instance_of_if_known(integer, java_lang_String()), false);
  EXPECT_EQ(is_instance_of_if_known(number, integer), false);

  // class Bar implements LibMarker {}  // LibMarker is not loaded
  // Only interfaces lie behind LibMarker, so Bar is no Number, but may be
  // Serializable.
  auto* bar = DexType::make_type("LBar;");
  ClassCreator bc(bar);
  bc.set_super(object);
  bc.add_interface(DexType::make_type("LLibMarker;"));
  bc.create();
  EXPECT_EQ(is_instance_of_if_known(bar, number), false);
  EXPECT_EQ(is_instance_of_if_known(bar, serializable), std::nullopt);

  // class Baz extends LibBase implements Serializable {}  // LibBase unloaded
  // Serializable, as every interface, leads to Object.
  auto* baz = DexType::make_type("LBaz;");
  ClassCreator zc(baz);
  zc.set_super(DexType::make_type("LLibBase;"));
  zc.add_interface(serializable);
  zc.create();
  EXPECT_EQ(is_instance_of_if_known(baz, object), true);
  EXPECT_EQ(is_instance_of_if_known(baz, number), std::nullopt);
}

// I0 extends A1 and B1, A1 and B1 extend both A2 and B2, and so on: an
// interface hierarchy with 2^40 paths to its top, which a walk that visits an
// interface more than once does not finish.
TEST_F(TypeUtilTest, is_instance_of_if_known_shared_interface_ancestors) {
  using namespace type;
  ClassCreator(java_lang_Object()).create();
  auto make_interface = [](const std::string& name,
                           const std::vector<DexType*>& supers) {
    ClassCreator creator(DexType::make_type(name));
    creator.set_super(java_lang_Object());
    creator.set_access(ACC_PUBLIC | ACC_INTERFACE | ACC_ABSTRACT);
    for (auto* super : supers) {
      creator.add_interface(super);
    }
    return creator.create()->get_type();
  };
  constexpr int kLayers = 40;
  std::vector<DexType*> layer;
  for (int i = kLayers; i > 0; --i) {
    auto n = std::to_string(i);
    layer = {make_interface("LA" + n + ";", layer),
             make_interface("LB" + n + ";", layer)};
  }
  auto* top = make_interface("LI0;", layer);
  auto* unrelated = make_interface("LJ;", {});
  ClassCreator cc(DexType::make_type("LC;"));
  cc.set_super(java_lang_Object());
  cc.add_interface(top);
  auto* c = cc.create()->get_type();

  EXPECT_EQ(is_instance_of_if_known(top, unrelated), false);
  EXPECT_FALSE(check_cast(c, unrelated));
  EXPECT_TRUE(check_cast(c, DexType::make_type("LB40;")));
}

// A method may name a class that is public or in its own package, as on the
// device; the private flag of a class does not matter.
TEST_F(TypeUtilTest, can_access_a_class) {
  auto make_class = [](const char* name, DexAccessFlags access) {
    ClassCreator creator(DexType::make_type(name));
    creator.set_super(type::java_lang_Object());
    creator.set_access(access);
    return creator.create();
  };
  auto make_method = [](const char* name) {
    return DexMethod::make_method(name)->make_concrete(ACC_PUBLIC | ACC_STATIC,
                                                       false);
  };
  auto* hidden = make_class("Lp/Hidden;", DexAccessFlags(0));
  auto* nested = make_class("Lp/Outer$Nested;", ACC_PRIVATE);
  auto* open = make_class("Lp/Open;", ACC_PUBLIC);
  auto* in_p = make_method("Lp/User;.run:()V");
  auto* in_q = make_method("Lq/User;.run:()V");

  EXPECT_TRUE(type::can_access(in_p, hidden));
  EXPECT_TRUE(type::can_access(in_p, nested));
  EXPECT_TRUE(type::can_access(in_p, open));
  EXPECT_FALSE(type::can_access(in_q, hidden));
  EXPECT_FALSE(type::can_access(in_q, nested));
  EXPECT_TRUE(type::can_access(in_q, open));
  EXPECT_TRUE(type::can_access(in_q, static_cast<const DexClass*>(nullptr)));
}

// Code a pass adds may name any app class when a later pass makes every app
// class public; a class outside the app keeps its access. An array is named by
// its element class.
TEST_F(TypeUtilTest, can_name_a_type) {
  auto make_class = [](const char* name, bool external) {
    ClassCreator creator(DexType::make_type(name));
    creator.set_super(type::java_lang_Object());
    creator.set_access(DexAccessFlags(0));
    if (external) {
      creator.set_external();
    }
    return creator.create()->get_type();
  };
  auto* app = make_class("Lp/AppHidden;", /* external */ false);
  auto* framework = make_class("Lp/FrameworkHidden;", /* external */ true);
  auto* app_array = DexType::make_type("[[Lp/AppHidden;");
  auto* in_q = DexMethod::make_method("Lq/Adder;.run:()V")
                   ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);

  EXPECT_FALSE(type::can_name_type(in_q, app, false));
  EXPECT_FALSE(type::can_name_type(in_q, app_array, false));
  EXPECT_FALSE(type::can_name_type(in_q, framework, false));
  EXPECT_TRUE(type::can_name_type(in_q, app, true));
  EXPECT_TRUE(type::can_name_type(in_q, app_array, true));
  EXPECT_FALSE(type::can_name_type(in_q, framework, true));
}

// Code a pass adds may not name a class Redex has no definition of, while a
// check of existing code assumes such a class accessible. Primitive types are
// always nameable.
TEST_F(TypeUtilTest, can_name_only_a_type_redex_can_see) {
  auto* unknown = DexType::make_type("Lp/Unknown;");
  auto* unknown_array = DexType::make_type("[Lp/Unknown;");
  auto* in_q = DexMethod::make_method("Lq/Adder2;.run:()V")
                   ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);

  EXPECT_TRUE(type::can_access_type(in_q, unknown));
  EXPECT_FALSE(type::can_name_type(in_q, unknown, false));
  EXPECT_FALSE(type::can_name_type(in_q, unknown, true));
  EXPECT_FALSE(type::can_name_type(in_q, unknown_array, true));
  EXPECT_TRUE(type::can_name_type(in_q, type::_int(), false));
  EXPECT_TRUE(type::can_name_type(in_q, DexType::make_type("[I"), false));
}
