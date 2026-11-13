/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "DexClass.h"

#include "IRAssembler.h"
#include "RedexContext.h"
#include "RedexTest.h"
#include "SimpleClassHierarchy.h"

class DexClassTest : public RedexTest {};

TEST_F(DexClassTest, walk_types) {
  auto* foo = DexType::make_type("LFoo;");
  auto* bar = DexType::make_type("LBar;");
  // After a rename, the old name still maps to the type.
  foo->set_name(DexString::make_string("LRenamedFoo;"));
  ASSERT_EQ(DexType::get_type("LFoo;"), foo);
  g_redex->alias_type_name(bar, DexString::make_string("LAliasOfBar;"));
  ASSERT_EQ(DexType::get_type("LAliasOfBar;"), bar);

  UnorderedMap<DexType*, size_t> visits;
  g_redex->walk_types([&](DexType* type) { ++visits[type]; });

  EXPECT_EQ(visits.at(foo), 1);
  EXPECT_EQ(visits.at(bar), 1);
  EXPECT_TRUE(unordered_all_of(
      visits, [](const auto& entry) { return entry.second == 1; }));
}

TEST_F(DexClassTest, testUniqueMethodName) {
  auto* method = assembler::class_with_method("LFoo;",
                                              R"(
      (method (private) "LFoo;.bar:(I)V"
       (
        (return-void)
       )
      )
    )");
  auto* type = DexType::make_type("LFoo;");
  const auto* newname = DexMethod::get_unique_name(
      type, DexString::make_string("bar"), method->get_proto());
  EXPECT_EQ(newname->str(), "barr$0");
  DexMethod::make_method("LFoo;.barr$0:(I)V");
  newname = DexMethod::get_unique_name(type, DexString::make_string("bar"),
                                       method->get_proto());
  EXPECT_EQ(newname->str(), "barr$1");

  newname = DexMethod::get_unique_name(type, DexString::make_string("baz"),
                                       method->get_proto());
  EXPECT_EQ(newname->str(),
            "baz"); // no conflict, expect baz not to be suffixed
}

TEST_F(DexClassTest, testUniqueFieldName) {
  auto* class_type = DexType::make_type(DexString::make_string("LFoo;"));
  ClassCreator class_creator(class_type);
  class_creator.set_super(type::java_lang_Object());
  class_creator.create();
  auto* type = DexType::make_type("LFoo;");
  const auto* newname = DexField::get_unique_name(
      type, DexString::make_string("bar"), DexType::make_type("I"));
  EXPECT_EQ(newname->str(), "bar"); // no conflict, should not be renamed
  DexField::make_field("LFoo;.bar:I");
  newname = DexField::get_unique_name(type, DexString::make_string("bar"),
                                      DexType::make_type("I"));
  EXPECT_EQ(newname->str(), "barr$0");
  DexField::make_field("LFoo;.barr$0:I");
  newname = DexField::get_unique_name(type, DexString::make_string("bar"),
                                      DexType::make_type("I"));
  EXPECT_EQ(newname->str(), "barr$1");
}

TEST_F(DexClassTest, testUniqueTypeName) {
  DexType::make_type("LFoo;");
  auto* bar_type = DexType::make_unique_type("LBar;");
  auto* foor0_type = DexType::make_unique_type("LFoo;");
  auto* foor1_type = DexType::make_unique_type("LFoo;");
  auto* foor0r0_type = DexType::make_unique_type("LFoor$0;");

  EXPECT_EQ(bar_type->str(), "LBar;"); // no conflict, should not be renamed
  EXPECT_EQ(foor0_type->str(), "LFoor$0;");
  EXPECT_EQ(foor1_type->str(), "LFoor$1;");
  EXPECT_EQ(foor0r0_type->str(), "LFoor$0r$0;");
}

TEST_F(DexClassTest, gather_load_types) {
  auto helper = redex::test::SimpleClassHierarchy{};

  auto make_expected_type_set = [](std::initializer_list<DexClass*> l) {
    UnorderedSet<const DexType*> ret;
    for (auto* c : l) {
      ret.emplace(c->get_type());
    }
    return ret;
  };

  // Test that (internal) superclasses and interfaces are in, but
  // field and method types are not.

  {
    UnorderedSet<const DexType*> types;
    helper.foo->gather_load_types(types);
    auto expected = make_expected_type_set({helper.foo});
    EXPECT_EQ(expected, types);
  }

  {
    UnorderedSet<const DexType*> types;
    helper.bar->gather_load_types(types);
    auto expected = make_expected_type_set({helper.foo, helper.bar});
    EXPECT_EQ(expected, types);
  }

  {
    UnorderedSet<const DexType*> types;
    helper.baz->gather_load_types(types);
    auto expected =
        make_expected_type_set({helper.foo, helper.bar, helper.baz});
    EXPECT_EQ(expected, types);
  }

  {
    UnorderedSet<const DexType*> types;
    helper.qux->gather_load_types(types);
    auto expected = make_expected_type_set(
        {helper.foo, helper.bar, helper.baz, helper.qux});
    EXPECT_EQ(expected, types);
  }

  {
    UnorderedSet<const DexType*> types;
    helper.iquux->gather_load_types(types);
    auto expected = make_expected_type_set({helper.iquux});
    EXPECT_EQ(expected, types);
  }

  {
    UnorderedSet<const DexType*> types;
    helper.quuz->gather_load_types(types);
    auto expected =
        make_expected_type_set({helper.iquux, helper.foo, helper.quuz});
    EXPECT_EQ(expected, types);
  }

  {
    UnorderedSet<const DexType*> types;
    helper.xyzzy->gather_load_types(types);
    auto expected = make_expected_type_set({helper.xyzzy});
    EXPECT_EQ(expected, types);
  }
}

TEST_F(DexClassTest, testObfuscatedNames) {
  auto* method = assembler::class_with_method("LX/001;",
                                              R"(
      (method (private) "LX/001;.A01:(I)V"
       (
        (return-void)
       )
      )
    )");

  auto* type = DexType::get_type("LX/001;");
  auto* clazz = type_class(type);
  auto* field =
      DexField::make_field("LX/001;.A00:I")->make_concrete(ACC_PUBLIC);

  EXPECT_EQ(clazz->get_deobfuscated_name_or_empty(), "LX/001;");
  EXPECT_EQ(method->get_deobfuscated_name_or_empty(), "");
  EXPECT_EQ(field->get_deobfuscated_name_or_empty(), "");

  clazz->set_deobfuscated_name("Lbaz;");
  method->set_deobfuscated_name("Lbaz;.foo:(I)V");
  field->set_deobfuscated_name("Lbaz;.bar:I");

  EXPECT_EQ(clazz->get_deobfuscated_name_or_empty(), "Lbaz;");
  EXPECT_EQ(clazz->str(), "LX/001;");
  EXPECT_EQ(type->str(), "LX/001;");

  EXPECT_EQ(method->str(), "A01");
  EXPECT_EQ(method->get_deobfuscated_name_or_empty(), "Lbaz;.foo:(I)V");
  EXPECT_EQ(method->get_simple_deobfuscated_name(), "foo");

  EXPECT_EQ(field->str(), "A00");
  EXPECT_EQ(field->get_deobfuscated_name_or_empty(), "Lbaz;.bar:I");
  EXPECT_EQ(field->get_simple_deobfuscated_name(), "bar");
}

TEST_F(DexClassTest, testShowStructure) {
  auto* c = assembler::class_with_methods("LShowStructure;",
                                          {
                                              // Constructor.
                                              assembler::method_from_string(R"(
(method (public constructor) "LShowStructure;.<init>:()V"
  ((load-param-object v0)
   (return-void))
))"),
                                              // Direct
                                              assembler::method_from_string(R"(
(method (private) "LShowStructure;.foo:()V"
  ((load-param-object v0)
   (return-void))
))"),
                                              // Virtual
                                              assembler::method_from_string(R"(
(method (public) "LShowStructure;.bar:()V"
  ((load-param-object v0)
   (return-void))
))"),
                                          });
  // Static field.
  c->add_field(DexField::make_field("LShowStructure;.staticField:I")
                   ->make_concrete(ACC_STATIC));
  // Instance field.
  c->add_field(DexField::make_field("LShowStructure;.staticField:I")
                   ->make_concrete(ACC_PUBLIC));

  const auto* expected = R"(ShowStructure
Fields:
  static LShowStructure;.staticField:I
  instance LShowStructure;.staticField:I
Constructors:
  LShowStructure;.<init>:()V
Methods:
  direct LShowStructure;.foo:()V
  virtual LShowStructure;.bar:()V)";

  EXPECT_EQ(c->show_structure(), expected);
}
