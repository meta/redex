/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "DexTypeEnvironment.h"

#include <sparta/PatriciaTreeSet.h>

#include "Creators.h"
#include "RedexTest.h"

using TypeSet = sparta::PatriciaTreeSet<const DexType*>;

struct DexTypeEnvironmentTest : public RedexTest {
 public:
  /*
   *   Ljava/lang/Object;
   *   |
   *   A
   *  / \
   * A1  A2
   *     \
   *     A21
   *      \
   *      A211
   *
   *   Ljava/lang/Object;
   *   |
   *   B
   *   |
   *   B1
   *
   *   Ljava/lang/Object;
   *   |               \
   *   C                D
   *  /  \   \   \   \
   * C1  C2  C3  C4  C5
   *
   *
   *  Ljava/lang/Object;
   *  |
   *  Base
   *  |         \
   *  Sub1(If1) Sub2(If2)
   *  |           \
   *  Sub3(If1)   Sub4(If1, If2)
   *
   *  Ljava/lang/Object;
   *  |            |           |
   *  ImplIf1If2A  ImplIf1If2B ImplIf1Only
   *  (If1, If2)   (If1, If2)  (If1)
   *
   *  These three are Object-rooted, unlike every Sub*, so a join between them
   *  has no common super class below Object and has to fall through to the
   *  interfaces. That is what SingletonJoinIsNotAssociativeTest needs: two
   *  classes sharing several incomparable interfaces have an intersection type
   *  as their bound, which no single DexType can hold.
   *
   *  Ljava/lang/Object;
   *  |
   *  AbstractMapEntry(MapEntry)
   *  |
   *  ImmutableEntry
   *  |
   *  ImmutableMapEntry
   *
   *
   *  D1 through D5 represent typedef annotation types for
   *  the TypedefAnnotationDomain
   *
   *  Ljava/lang/Object;
   *  |  \   \   \   \
   *  D1  D2  D3  D4  D5
   *
   */
  DexTypeEnvironmentTest() {
    // Synthesizing Ljava/lang/Object;
    ClassCreator creator = ClassCreator(type::java_lang_Object());
    creator.create();

    m_type_a = DexType::make_type("LA;");
    creator = ClassCreator(m_type_a);
    creator.set_super(type::java_lang_Object());
    creator.create();

    m_type_a1 = DexType::make_type("LA1;");
    creator = ClassCreator(m_type_a1);
    creator.set_super(m_type_a);
    creator.create();

    m_type_a2 = DexType::make_type("LA2;");
    creator = ClassCreator(m_type_a2);
    creator.set_super(m_type_a);
    creator.create();

    m_a_array = type::make_array_type(m_type_a);
    m_a1_array = type::make_array_type(m_type_a1);
    m_a2_array = type::make_array_type(m_type_a2);

    m_type_a21 = DexType::make_type("LA21;");
    creator = ClassCreator(m_type_a21);
    creator.set_super(m_type_a2);
    creator.create();

    m_type_a211 = DexType::make_type("LA211;");
    creator = ClassCreator(m_type_a211);
    creator.set_super(m_type_a21);
    creator.create();

    m_type_b = DexType::make_type("LB;");
    creator = ClassCreator(m_type_b);
    creator.set_super(type::java_lang_Object());
    creator.create();

    m_type_b1 = DexType::make_type("LB1;");
    creator = ClassCreator(m_type_b1);
    creator.set_super(m_type_b);
    creator.create();

    m_type_c = DexType::make_type("LC;");
    creator = ClassCreator(m_type_c);
    creator.set_super(type::java_lang_Object());
    creator.create();

    m_type_c1 = DexType::make_type("LC1;");
    creator = ClassCreator(m_type_c1);
    creator.set_super(m_type_c);
    creator.create();

    m_type_c2 = DexType::make_type("LC2;");
    creator = ClassCreator(m_type_c2);
    creator.set_super(m_type_c);
    creator.create();

    m_type_c3 = DexType::make_type("LC3;");
    creator = ClassCreator(m_type_c3);
    creator.set_super(m_type_c);
    creator.create();

    m_type_c4 = DexType::make_type("LC4;");
    creator = ClassCreator(m_type_c4);
    creator.set_super(m_type_c);
    creator.create();

    m_type_c5 = DexType::make_type("LC5;");
    creator = ClassCreator(m_type_c5);
    creator.set_super(m_type_c);
    creator.create();

    m_type_d = DexType::make_type("LD;");
    creator = ClassCreator(m_type_d);
    creator.set_super(type::java_lang_Object());
    creator.create();

    m_type_base = DexType::make_type("LBase;");
    creator = ClassCreator(m_type_base);
    creator.set_super(type::java_lang_Object());
    creator.create();

    m_type_if1 = DexType::make_type("LIf1;");
    creator = ClassCreator(m_type_if1);
    creator.set_super(type::java_lang_Object());
    creator.set_access(ACC_PUBLIC | ACC_INTERFACE);
    creator.create();
    m_type_if2 = DexType::make_type("LIf2;");
    creator = ClassCreator(m_type_if2);
    creator.set_super(type::java_lang_Object());
    creator.set_access(ACC_PUBLIC | ACC_INTERFACE);
    creator.create();

    m_type_sub1 = DexType::make_type("LSub1;");
    creator = ClassCreator(m_type_sub1);
    creator.set_super(m_type_base);
    creator.add_interface(m_type_if1);
    creator.create();

    m_type_sub2 = DexType::make_type("LSub2;");
    creator = ClassCreator(m_type_sub2);
    creator.set_super(m_type_base);
    creator.add_interface(m_type_if2);
    creator.create();

    m_type_sub3 = DexType::make_type("LSub3;");
    creator = ClassCreator(m_type_sub3);
    creator.set_super(m_type_sub1);
    creator.add_interface(m_type_if1);
    creator.create();

    m_type_sub4 = DexType::make_type("LSub4;");
    creator = ClassCreator(m_type_sub4);
    creator.set_super(m_type_sub2);
    creator.add_interface(m_type_if1);
    creator.add_interface(m_type_if2);
    creator.create();

    m_type_ij1 = DexType::make_type("LImplIf1If2A;");
    creator = ClassCreator(m_type_ij1);
    creator.set_super(type::java_lang_Object());
    creator.add_interface(m_type_if1);
    creator.add_interface(m_type_if2);
    creator.create();

    m_type_ij2 = DexType::make_type("LImplIf1If2B;");
    creator = ClassCreator(m_type_ij2);
    creator.set_super(type::java_lang_Object());
    creator.add_interface(m_type_if1);
    creator.add_interface(m_type_if2);
    creator.create();

    m_type_i_only = DexType::make_type("LImplIf1Only;");
    creator = ClassCreator(m_type_i_only);
    creator.set_super(type::java_lang_Object());
    creator.add_interface(m_type_if1);
    creator.create();

    m_string_array = DexType::make_type("[Ljava/lang/String;");
    m_int_array = type::make_array_type(type::_int());
    m_sub1_array = type::make_array_type(m_type_sub1);
    m_sub2_array = type::make_array_type(m_type_sub2);
    m_sub3_array = type::make_array_type(m_type_sub3);

    m_map_entry = DexType::make_type("LMapEntry;");
    creator = ClassCreator(m_map_entry);
    creator.set_super(type::java_lang_Object());
    creator.set_access(ACC_PUBLIC | ACC_INTERFACE);
    creator.create();

    m_abs_map_entry = DexType::make_type("LAbstractMapEntry;");
    creator = ClassCreator(m_abs_map_entry);
    creator.set_super(type::java_lang_Object());
    creator.add_interface(m_map_entry);
    creator.create();

    m_im_entry = DexType::make_type("LImmutableEntry;");
    creator = ClassCreator(m_im_entry);
    creator.set_super(m_abs_map_entry);
    creator.create();

    m_im_map_entry = DexType::make_type("LImmutableMapEntry;");
    creator = ClassCreator(m_im_map_entry);
    creator.set_super(m_im_entry);
    creator.create();

    m_type_d1 = DexType::make_type("LD1;");
    creator = ClassCreator(m_type_d1);
    creator.set_super(type::java_lang_Object());
    creator.create();

    m_type_d2 = DexType::make_type("LD2;");
    creator = ClassCreator(m_type_d2);
    creator.set_super(type::java_lang_Object());
    creator.create();

    m_type_d3 = DexType::make_type("LD3;");
    creator = ClassCreator(m_type_d3);
    creator.set_super(type::java_lang_Object());
    creator.create();

    m_type_d4 = DexType::make_type("LD4;");
    creator = ClassCreator(m_type_d4);
    creator.set_super(type::java_lang_Object());
    creator.create();

    m_type_d5 = DexType::make_type("LD5;");
    creator = ClassCreator(m_type_d5);
    creator.set_super(type::java_lang_Object());
    creator.create();

    m_anno_d1 = new DexAnnoType(m_type_d1);
    m_anno_d2 = new DexAnnoType(m_type_d2);
    m_anno_d3 = new DexAnnoType(m_type_d3);
    m_anno_d4 = new DexAnnoType(m_type_d4);
    m_anno_d5 = new DexAnnoType(m_type_d5);

    m_map_entry_array = type::make_array_type(m_map_entry);
    m_im_map_entry_array = type::make_array_type(m_im_map_entry);
  }

  TypeSet get_type_set(std::initializer_list<DexType*> l) {
    TypeSet s;
    for (auto* const elem : l) {
      s.insert(const_cast<const DexType*>(elem));
    }
    return s;
  }

 protected:
  DexType* m_type_a;
  DexType* m_type_a1;
  DexType* m_type_a2;
  DexType* m_type_a21;
  DexType* m_type_a211;
  DexType* m_a_array;
  DexType* m_a1_array;
  DexType* m_a2_array;

  DexType* m_type_b;
  DexType* m_type_b1;

  DexType* m_type_c;
  DexType* m_type_c1;
  DexType* m_type_c2;
  DexType* m_type_c3;
  DexType* m_type_c4;
  DexType* m_type_c5;
  DexType* m_type_d;

  DexType* m_type_base;
  DexType* m_type_sub1;
  DexType* m_type_sub2;
  DexType* m_type_sub3;
  DexType* m_type_sub4;
  DexType* m_type_ij1;
  DexType* m_type_ij2;
  DexType* m_type_i_only;
  DexType* m_type_if1;
  DexType* m_type_if2;

  DexType* m_string_array;
  DexType* m_int_array;
  DexType* m_sub1_array;
  DexType* m_sub2_array;
  DexType* m_sub3_array;

  DexType* m_map_entry;
  DexType* m_abs_map_entry;
  DexType* m_im_entry;
  DexType* m_im_map_entry;
  DexType* m_map_entry_array;
  DexType* m_im_map_entry_array;

  DexType* m_type_d1;
  DexType* m_type_d2;
  DexType* m_type_d3;
  DexType* m_type_d4;
  DexType* m_type_d5;

  DexAnnoType* m_anno_d1;
  DexAnnoType* m_anno_d2;
  DexAnnoType* m_anno_d3;
  DexAnnoType* m_anno_d4;
  DexAnnoType* m_anno_d5;
};

TEST_F(DexTypeEnvironmentTest, BasicTest) {
  auto env = DexTypeEnvironment();
  EXPECT_TRUE(env.is_top());
  const auto& reg_env = env.get_reg_environment();
  EXPECT_TRUE(reg_env.is_top());
  const auto& field_env = env.get_field_environment();
  EXPECT_TRUE(field_env.is_top());
}

TEST_F(DexTypeEnvironmentTest, RegisterEnvTest) {
  auto env = DexTypeEnvironment();
  reg_t v0 = 0;
  auto type = env.get(v0);
  EXPECT_TRUE(type.is_top());

  env.set(v0, DexTypeDomain::create_not_null(m_type_a));
  EXPECT_EQ(env.get(v0), DexTypeDomain::create_not_null(m_type_a));

  reg_t v1 = 1;
  env.set(v1, DexTypeDomain::create_not_null(m_type_a1));
  EXPECT_EQ(env.get(v1), DexTypeDomain::create_not_null(m_type_a1));

  auto a_join_a1 = DexTypeDomain::create_not_null(m_type_a);
  a_join_a1.join_with(env.get(v1));
  EXPECT_EQ(a_join_a1.get_single_domain(), SingletonDexTypeDomain(m_type_a));
  EXPECT_EQ(a_join_a1.get_annotation_domain(), TypedefAnnotationDomain::top());
  EXPECT_EQ(a_join_a1.get_type_set(), get_type_set({m_type_a, m_type_a1}));

  auto a1_join_a = DexTypeDomain::create_not_null(m_type_a1);
  a1_join_a.join_with(env.get(v0));
  EXPECT_EQ(a1_join_a.get_single_domain(), SingletonDexTypeDomain(m_type_a));
  EXPECT_EQ(a1_join_a.get_annotation_domain(), TypedefAnnotationDomain::top());
  EXPECT_EQ(a1_join_a.get_type_set(), get_type_set({m_type_a, m_type_a1}));
}

TEST_F(DexTypeEnvironmentTest, AnnotationRegisterEnvTest) {
  auto env = DexTypeEnvironment();
  reg_t v0 = 0;
  auto type = env.get(v0);
  EXPECT_TRUE(type.is_top());

  env.set(v0, DexTypeDomain::create_nullable(m_type_a, m_anno_d1));
  EXPECT_EQ(env.get(v0), DexTypeDomain::create_nullable(m_type_a, m_anno_d1));

  reg_t v1 = 1;
  env.set(v1, DexTypeDomain::create_nullable(m_type_a1, m_anno_d2));
  EXPECT_EQ(env.get(v1), DexTypeDomain::create_nullable(m_type_a1, m_anno_d2));

  auto a_join_a1 = DexTypeDomain::create_nullable(m_type_a, m_anno_d1);
  a_join_a1.join_with(env.get(v1));
  EXPECT_EQ(a_join_a1.get_single_domain(), SingletonDexTypeDomain(m_type_a));
  EXPECT_EQ(a_join_a1.get_annotation_domain(),
            TypedefAnnotationDomain(type::java_lang_Object()));

  EXPECT_TRUE(a_join_a1.get_set_domain().is_top());

  auto a1_join_a = DexTypeDomain::create_nullable(m_type_a1, m_anno_d1);
  a1_join_a.join_with(env.get(v0));
  EXPECT_EQ(a1_join_a.get_single_domain(), SingletonDexTypeDomain(m_type_a));
  EXPECT_EQ(a1_join_a.get_annotation_domain(),
            TypedefAnnotationDomain(m_type_d1));

  EXPECT_TRUE(a1_join_a.get_set_domain().is_top());
}

TEST_F(DexTypeEnvironmentTest, FieldEnvTest) {
  auto env = DexTypeEnvironment();
  DexField* f1 = (DexField*)1;
  auto type = env.get(f1);
  EXPECT_TRUE(type.is_top());

  env.set(f1, DexTypeDomain::create_not_null(m_type_a1));
  EXPECT_EQ(env.get(f1), DexTypeDomain::create_not_null(m_type_a1));

  DexField* f2 = (DexField*)2;
  EXPECT_TRUE(env.get(f2).is_top());
  env.set(f2, DexTypeDomain::create_not_null(m_type_a));
  EXPECT_EQ(env.get(f2), DexTypeDomain::create_not_null(m_type_a));

  auto a_join_a1 = env.get(f2);
  a_join_a1.join_with(env.get(f1));
  EXPECT_EQ(a_join_a1.get_single_domain(), SingletonDexTypeDomain(m_type_a));
  EXPECT_EQ(a_join_a1.get_annotation_domain(), TypedefAnnotationDomain::top());
  EXPECT_EQ(a_join_a1.get_type_set(), get_type_set({m_type_a, m_type_a1}));
  EXPECT_EQ(env.get(f1), DexTypeDomain::create_not_null(m_type_a1));
  EXPECT_EQ(env.get(f2), DexTypeDomain::create_not_null(m_type_a));

  auto a1_join_a = env.get(f1);
  a1_join_a.join_with(env.get(f2));
  EXPECT_EQ(a1_join_a.get_single_domain(), SingletonDexTypeDomain(m_type_a));
  EXPECT_EQ(a1_join_a.get_annotation_domain(), TypedefAnnotationDomain::top());
  EXPECT_EQ(a1_join_a.get_type_set(), get_type_set({m_type_a, m_type_a1}));
  EXPECT_EQ(env.get(f1), DexTypeDomain::create_not_null(m_type_a1));
  EXPECT_EQ(env.get(f2), DexTypeDomain::create_not_null(m_type_a));
}

TEST_F(DexTypeEnvironmentTest, JoinWithTest) {
  auto domain_a1 = DexTypeDomain::create_not_null(m_type_a1);
  auto domain_a2 = DexTypeDomain::create_not_null(m_type_a2);
  domain_a1.join_with(domain_a2);
  EXPECT_EQ(domain_a1.get_single_domain(), SingletonDexTypeDomain(m_type_a));
  EXPECT_EQ(domain_a1.get_type_set(), get_type_set({m_type_a1, m_type_a2}));

  domain_a1 = DexTypeDomain::create_not_null(m_type_a1);
  auto domain_a21 = DexTypeDomain::create_not_null(m_type_a21);
  domain_a1.join_with(domain_a21);
  EXPECT_EQ(domain_a1.get_single_domain(), SingletonDexTypeDomain(m_type_a));
  EXPECT_EQ(domain_a1.get_type_set(), get_type_set({m_type_a1, m_type_a21}));

  domain_a1 = DexTypeDomain::create_not_null(m_type_a1);
  auto domain_a211 = DexTypeDomain::create_not_null(m_type_a211);
  domain_a1.join_with(domain_a211);
  EXPECT_EQ(domain_a1.get_single_domain(), SingletonDexTypeDomain(m_type_a));
  EXPECT_EQ(domain_a1.get_type_set(), get_type_set({m_type_a1, m_type_a211}));

  auto domain_a = DexTypeDomain::create_not_null(m_type_a);
  domain_a211 = DexTypeDomain::create_not_null(m_type_a211);
  domain_a.join_with(domain_a211);
  EXPECT_EQ(domain_a.get_single_domain(), SingletonDexTypeDomain(m_type_a));
  EXPECT_EQ(domain_a.get_type_set(), get_type_set({m_type_a, m_type_a211}));

  auto top1 = DexTypeDomain::top();
  auto top2 = DexTypeDomain::top();
  top1.join_with(top2);
  EXPECT_TRUE(top1.is_top());
  EXPECT_TRUE(top2.is_top());

  domain_a = DexTypeDomain::create_not_null(m_type_a);
  auto domain_b = DexTypeDomain::create_not_null(m_type_b);
  domain_a.join_with(domain_b);
  EXPECT_EQ(domain_a.get_single_domain(),
            SingletonDexTypeDomain(type::java_lang_Object()));
  EXPECT_EQ(domain_a.get_type_set(), get_type_set({m_type_a, m_type_b}));

  domain_a1 = DexTypeDomain::create_not_null(m_type_a1);
  domain_b = DexTypeDomain::create_not_null(m_type_b);
  domain_a1.join_with(domain_b);
  EXPECT_EQ(domain_a1.get_single_domain(),
            SingletonDexTypeDomain(type::java_lang_Object()));
  EXPECT_EQ(domain_a1.get_type_set(), get_type_set({m_type_a1, m_type_b}));

  domain_a21 = DexTypeDomain::create_not_null(m_type_a21);
  domain_b = DexTypeDomain::create_not_null(m_type_b);
  domain_a21.join_with(domain_b);
  EXPECT_EQ(domain_a21.get_single_domain(),
            SingletonDexTypeDomain(type::java_lang_Object()));
  EXPECT_EQ(domain_a21.get_type_set(), get_type_set({m_type_a21, m_type_b}));

  domain_a211 = DexTypeDomain::create_not_null(m_type_a211);
  domain_b = DexTypeDomain::create_not_null(m_type_b);
  domain_a211.join_with(domain_b);
  EXPECT_EQ(domain_a211.get_single_domain(),
            SingletonDexTypeDomain(type::java_lang_Object()));
  EXPECT_EQ(domain_a211.get_type_set(), get_type_set({m_type_a211, m_type_b}));

  domain_a1 = DexTypeDomain::create_not_null(m_type_a1);
  auto domain_b1 = DexTypeDomain::create_not_null(m_type_b1);
  domain_a1.join_with(domain_b1);
  EXPECT_EQ(domain_a1.get_single_domain(),
            SingletonDexTypeDomain(type::java_lang_Object()));
  EXPECT_EQ(domain_a1.get_type_set(), get_type_set({m_type_a1, m_type_b1}));
  EXPECT_FALSE(domain_a1.get_single_domain().is_top());
  EXPECT_FALSE(domain_b1.get_single_domain().is_top());

  domain_a1 = DexTypeDomain::create_not_null(m_type_a1);
  domain_b1.join_with(domain_a1);
  EXPECT_EQ(domain_b1.get_single_domain(),
            SingletonDexTypeDomain(type::java_lang_Object()));
  EXPECT_EQ(domain_b1.get_type_set(), get_type_set({m_type_a1, m_type_b1}));
  EXPECT_FALSE(domain_a1.get_single_domain().is_top());
  EXPECT_FALSE(domain_b1.get_single_domain().is_top());
}

TEST_F(DexTypeEnvironmentTest, AnnotationJoinWithTest) {
  auto domain_a1 = DexTypeDomain::create_nullable(m_type_a1, m_anno_d1);
  auto domain_a2 = DexTypeDomain::create_nullable(m_type_a2, m_anno_d2);
  domain_a1.join_with(domain_a2);
  EXPECT_EQ(domain_a1.get_annotation_domain(),
            TypedefAnnotationDomain(type::java_lang_Object()));

  domain_a1 = DexTypeDomain::create_nullable(m_type_a1, m_anno_d3);
  auto domain_a21 = DexTypeDomain::create_nullable(m_type_a21, nullptr);
  domain_a1.join_with(domain_a21);
  EXPECT_EQ(domain_a1.get_annotation_domain(), TypedefAnnotationDomain::top());

  EXPECT_TRUE(domain_a1.get_set_domain().is_top());

  domain_a1 = DexTypeDomain::create_nullable(m_type_a1, nullptr);
  auto domain_a211 = DexTypeDomain::create_nullable(m_type_a211, m_anno_d3);
  domain_a1.join_with(domain_a211);
  EXPECT_EQ(domain_a1.get_annotation_domain(), TypedefAnnotationDomain::top());

  EXPECT_TRUE(domain_a1.get_set_domain().is_top());

  auto domain_a = DexTypeDomain::create_nullable(m_type_a, m_anno_d4);
  domain_a211 = DexTypeDomain::create_nullable(m_type_a211, m_anno_d4);
  domain_a.join_with(domain_a211);
  EXPECT_EQ(domain_a.get_annotation_domain(),
            TypedefAnnotationDomain(m_type_d4));

  auto top1 = DexTypeDomain::top();
  auto top2 = DexTypeDomain::top();
  top1.join_with(top2);
  EXPECT_TRUE(top1.is_top());
  EXPECT_TRUE(top2.is_top());

  domain_a = DexTypeDomain::create_nullable(m_type_a);
  auto domain_b = DexTypeDomain::create_nullable(m_type_b);
  domain_a.join_with(domain_b);
  EXPECT_EQ(domain_a.get_annotation_domain(), TypedefAnnotationDomain::top());

  domain_a1 = DexTypeDomain::create_nullable(m_type_a1, nullptr);
  domain_b = DexTypeDomain::create_nullable(m_type_b, nullptr);
  domain_a1.join_with(domain_b);
  EXPECT_EQ(domain_a1.get_annotation_domain(), TypedefAnnotationDomain::top());
}

TEST_F(DexTypeEnvironmentTest, InterfaceJoinTest) {
  // Sub1 and Sub2 implement different interfaces, so nothing survives the
  // merge but their common super class.
  auto sub1 = SingletonDexTypeDomain(m_type_sub1);
  auto sub2 = SingletonDexTypeDomain(m_type_sub2);
  sub1.join_with(sub2);
  EXPECT_EQ(sub1, SingletonDexTypeDomain(m_type_base));
  EXPECT_FALSE(sub2.is_top());

  sub1 = SingletonDexTypeDomain(m_type_sub1);
  sub2.join_with(sub1);
  EXPECT_EQ(sub2, SingletonDexTypeDomain(m_type_base));
  EXPECT_FALSE(sub1.is_top());

  sub1 = SingletonDexTypeDomain(m_type_sub1);
  auto sub3 = SingletonDexTypeDomain(m_type_sub3);
  sub1.join_with(sub3);
  EXPECT_EQ(sub1, SingletonDexTypeDomain(m_type_sub1));
  EXPECT_FALSE(sub1.is_top());
  EXPECT_FALSE(sub3.is_top());

  sub1 = SingletonDexTypeDomain(m_type_sub1);
  sub3.join_with(sub1);
  EXPECT_EQ(sub3, SingletonDexTypeDomain(m_type_sub1));
  EXPECT_FALSE(sub3.is_top());
  EXPECT_FALSE(sub1.is_top());

  // Sub4 adds If1 on top of the If2 it inherits from Sub2. Sub2 is still a
  // super class of Sub4, so it is the answer; only the extra If1 is dropped,
  // and no super type of both could have kept it.
  sub2 = SingletonDexTypeDomain(m_type_sub2);
  auto sub4 = SingletonDexTypeDomain(m_type_sub4);
  sub2.join_with(sub4);
  EXPECT_EQ(sub2, SingletonDexTypeDomain(m_type_sub2));
  EXPECT_FALSE(sub4.is_top());

  sub2 = SingletonDexTypeDomain(m_type_sub2);
  sub4.join_with(sub2);
  EXPECT_EQ(sub4, SingletonDexTypeDomain(m_type_sub2));
  EXPECT_FALSE(sub2.is_top());

  auto base = SingletonDexTypeDomain(m_type_base);
  sub4 = SingletonDexTypeDomain(m_type_sub4);
  base.join_with(sub4);
  EXPECT_EQ(base, SingletonDexTypeDomain(m_type_base));
  EXPECT_FALSE(sub4.is_top());

  base = SingletonDexTypeDomain(m_type_base);
  sub4.join_with(base);
  EXPECT_EQ(sub4, SingletonDexTypeDomain(m_type_base));
  EXPECT_FALSE(base.is_top());
}

// `join_with` is an upper-bound operator, not a least-upper-bound one, and it
// is neither associative nor commutative. Folding it over a collection gives an
// answer that depends on the visit order, which is why callers that fold over
// an unordered container must impose one.
//
// The mechanism, on the types below: when the common super class walk reaches
// Object, `find_common_type` resolves through the interfaces the two operands
// share. Sharing exactly one is representable. Sharing several incomparable
// ones is not -- the bound is an intersection type -- so the join gives up to
// Top, and Top absorbs every operand that follows.
TEST_F(DexTypeEnvironmentTest, SingletonJoinIsNotAssociativeTest) {
  // Two classes sharing If1 and If2 have no representable bound: the least
  // upper bound is the intersection type If1 & If2, which one DexType cannot
  // hold, so the join gives up to Top and stays there.
  auto both_first = SingletonDexTypeDomain(m_type_ij1);
  both_first.join_with(SingletonDexTypeDomain(m_type_ij2));
  EXPECT_TRUE(both_first.is_top());
  both_first.join_with(SingletonDexTypeDomain(m_type_i_only));
  EXPECT_TRUE(both_first.is_top());

  // Folding the same three types in a different order never reaches that
  // state: the first join shares only If1, which is representable, and the
  // remaining operand implements it.
  auto single_first = SingletonDexTypeDomain(m_type_ij1);
  single_first.join_with(SingletonDexTypeDomain(m_type_i_only));
  EXPECT_EQ(single_first, SingletonDexTypeDomain(m_type_if1));
  single_first.join_with(SingletonDexTypeDomain(m_type_ij2));
  EXPECT_EQ(single_first, SingletonDexTypeDomain(m_type_if1));
  EXPECT_FALSE(single_first.is_top());

  // The two fold orders disagree, which is the property the fix rests on.
  EXPECT_NE(both_first, single_first);

  // A single join is still commutative; only the fold order matters.
  auto swapped = SingletonDexTypeDomain(m_type_i_only);
  swapped.join_with(SingletonDexTypeDomain(m_type_ij1));
  EXPECT_EQ(swapped, SingletonDexTypeDomain(m_type_if1));
}

/*
 * `find_common_interfaces` intersects the interfaces of the two operands, so
 * it has to see the same candidate set whichever way round they arrive.
 * `collect_interfaces` reports what a type DECLARES, while the other side is
 * tested with `check_cast`, which also admits the reflexive case -- so an
 * interface operand contributed nothing about itself and the intersection was
 * silently one-sided. `LNestedJ;` extends `LNestedI;`, so the fast path above
 * cannot rescue it either: `implements` walks super classes, not
 * interface-extends.
 */
TEST_F(DexTypeEnvironmentTest, JoinIsCommutativeAcrossInheritedInterfaces) {
  auto* t_i = DexType::make_type("LNestedI;");
  ClassCreator i_creator(t_i);
  i_creator.set_super(type::java_lang_Object());
  i_creator.set_access(ACC_PUBLIC | ACC_INTERFACE);
  i_creator.create();

  auto* t_j = DexType::make_type("LNestedJ;");
  ClassCreator j_creator(t_j);
  j_creator.set_super(type::java_lang_Object());
  j_creator.set_access(ACC_PUBLIC | ACC_INTERFACE);
  j_creator.add_interface(t_i);
  j_creator.create();

  auto* t_c = DexType::make_type("LNestedImpl;");
  ClassCreator c_creator(t_c);
  c_creator.set_super(type::java_lang_Object());
  c_creator.add_interface(t_j);
  c_creator.create();

  // Both operand orders must reach LNestedI;. Before the fix, join(I, C) gave
  // Ljava/lang/Object; while join(C, I) gave LNestedI;.
  auto ic = SingletonDexTypeDomain(t_i);
  ic.join_with(SingletonDexTypeDomain(t_c));
  auto ci = SingletonDexTypeDomain(t_c);
  ci.join_with(SingletonDexTypeDomain(t_i));
  EXPECT_EQ(ic, ci);
  EXPECT_EQ(ic, SingletonDexTypeDomain(t_i));
}

TEST_F(DexTypeEnvironmentTest, ExtendedInterfaceJoinTest) {
  auto sub1 = SingletonDexTypeDomain(m_type_sub1);
  auto if1 = SingletonDexTypeDomain(m_type_if1);
  sub1.join_with(if1);
  EXPECT_FALSE(sub1.is_top());
  EXPECT_EQ(sub1, SingletonDexTypeDomain(m_type_if1));
  EXPECT_FALSE(if1.is_top());

  // Sub1 does not implement If2 and they share no interface, so Object really
  // is the least upper bound here.
  sub1 = SingletonDexTypeDomain(m_type_sub1);
  auto if2 = SingletonDexTypeDomain(m_type_if2);
  sub1.join_with(if2);
  EXPECT_EQ(sub1, SingletonDexTypeDomain(type::java_lang_Object()));
  EXPECT_FALSE(if2.is_top());
}

TEST_F(DexTypeEnvironmentTest, ArrayJoinTest) {
  // The element join drives the array join, so Sub1[] and Sub2[] merge to
  // Base[] for the same reason Sub1 and Sub2 merge to Base.
  auto sub1_array = SingletonDexTypeDomain(m_sub1_array);
  auto sub2_array = SingletonDexTypeDomain(m_sub2_array);
  sub1_array.join_with(sub2_array);
  EXPECT_EQ(sub1_array,
            SingletonDexTypeDomain(type::make_array_type(m_type_base)));
  EXPECT_FALSE(sub2_array.is_top());

  sub1_array = SingletonDexTypeDomain(m_sub1_array);
  auto sub3_array = SingletonDexTypeDomain(m_sub3_array);
  sub1_array.join_with(sub3_array);
  EXPECT_FALSE(sub1_array.is_top());
  EXPECT_EQ(sub1_array, SingletonDexTypeDomain(m_sub1_array));
  EXPECT_FALSE(sub3_array.is_top());

  auto str_array = SingletonDexTypeDomain(m_string_array);
  auto int_array = SingletonDexTypeDomain(m_int_array);
  str_array.join_with(int_array);
  EXPECT_TRUE(str_array.is_top());
  EXPECT_FALSE(int_array.is_top());

  sub1_array = SingletonDexTypeDomain(m_sub1_array);
  auto sub3_nested_array =
      SingletonDexTypeDomain(type::make_array_type(m_type_sub3, 2));
  sub1_array.join_with(sub3_nested_array);
  EXPECT_TRUE(sub1_array.is_top());
  EXPECT_FALSE(sub3_nested_array.is_top());
}

TEST_F(DexTypeEnvironmentTest, ArrayJoinCreatesNoElementTypeTest) {
  // A dex file can name an array type without its element type, e.g. when
  // the element class is missing from the input and only arrays of it are
  // used.
  auto missing = SingletonDexTypeDomain(DexType::make_type("[Lmissing/T;"));
  ASSERT_EQ(DexType::get_type("Lmissing/T;"), nullptr);
  missing.join_with(SingletonDexTypeDomain(m_sub1_array));
  EXPECT_TRUE(missing.is_top());
  EXPECT_EQ(DexType::get_type("Lmissing/T;"), nullptr);

  // Different levels join to Top without looking at the element types.
  auto missing_nested =
      SingletonDexTypeDomain(DexType::make_type("[[Lmissing/U;"));
  ASSERT_EQ(DexType::get_type("Lmissing/U;"), nullptr);
  auto sub1_array = SingletonDexTypeDomain(m_sub1_array);
  sub1_array.join_with(missing_nested);
  EXPECT_TRUE(sub1_array.is_top());
  EXPECT_EQ(DexType::get_type("Lmissing/U;"), nullptr);
}

TEST_F(DexTypeEnvironmentTest, SingletonDexTypeDomainLeqTest) {
  // top and bottom
  auto top = SingletonDexTypeDomain::top();
  auto domain_a = SingletonDexTypeDomain(m_type_a);
  EXPECT_TRUE(top.is_top());
  EXPECT_FALSE(top.is_bottom());
  EXPECT_TRUE(domain_a.leq(top));
  EXPECT_TRUE(SingletonDexTypeDomain::bottom().leq(domain_a));
  domain_a.set_to_bottom();
  EXPECT_TRUE(domain_a.is_bottom());
  EXPECT_FALSE(domain_a.is_top());
  EXPECT_TRUE(domain_a.leq(SingletonDexTypeDomain::top()));

  // classes
  domain_a = SingletonDexTypeDomain(m_type_a);
  auto domain_a1 = SingletonDexTypeDomain(m_type_a1);
  EXPECT_FALSE(domain_a.is_bottom());
  EXPECT_FALSE(domain_a.is_top());
  EXPECT_TRUE(domain_a1.leq(domain_a));
  EXPECT_FALSE(domain_a.leq(domain_a1));

  auto domain_a21 = SingletonDexTypeDomain(m_type_a21);
  EXPECT_FALSE(domain_a21.is_bottom());
  EXPECT_FALSE(domain_a21.is_top());
  EXPECT_TRUE(domain_a21.leq(domain_a));
  EXPECT_FALSE(domain_a.leq(domain_a21));

  // interfaces
  auto sub1 = SingletonDexTypeDomain(m_type_sub1);
  auto if1 = SingletonDexTypeDomain(m_type_if1);
  EXPECT_FALSE(sub1.is_bottom());
  EXPECT_FALSE(sub1.is_top());
  EXPECT_FALSE(if1.is_bottom());
  EXPECT_FALSE(if1.is_top());
  auto join = sub1.join(if1);
  EXPECT_EQ(join, SingletonDexTypeDomain(if1));
  EXPECT_TRUE(sub1.leq(if1));
  EXPECT_TRUE(sub1.leq(join));
  join = if1.join(sub1);
  EXPECT_EQ(join, SingletonDexTypeDomain(if1));
  EXPECT_TRUE(if1.leq(join));
  EXPECT_FALSE(if1.leq(sub1));
  auto obj = SingletonDexTypeDomain(type::java_lang_Object());
  EXPECT_TRUE(sub1.leq(obj));
  EXPECT_TRUE(if1.leq(obj));

  // none
  auto none = SingletonDexTypeDomain(nullptr);
  EXPECT_FALSE(none.is_bottom());
  EXPECT_FALSE(none.is_top());
  EXPECT_TRUE(none.is_none());
  EXPECT_TRUE(none.leq(obj));
  EXPECT_FALSE(obj.leq(none));

  // array
  auto a_array = SingletonDexTypeDomain(m_a_array);
  auto a1_array = SingletonDexTypeDomain(m_a1_array);
  auto array_join = a_array.join(a1_array);
  EXPECT_EQ(array_join, SingletonDexTypeDomain(m_a_array));
  EXPECT_TRUE(a_array.leq(array_join));

  a1_array = SingletonDexTypeDomain(m_a1_array);
  auto a2_array = SingletonDexTypeDomain(m_a2_array);
  array_join = a1_array.join(a2_array);
  EXPECT_EQ(array_join, SingletonDexTypeDomain(m_a_array));
  EXPECT_TRUE(a1_array.leq(array_join));
}

TEST_F(DexTypeEnvironmentTest, TypedefAnnotationDomainLeqTest) {
  // top and bottom
  auto top = TypedefAnnotationDomain::top();
  auto domain_a = TypedefAnnotationDomain(m_type_a);
  EXPECT_TRUE(top.is_top());
  EXPECT_FALSE(top.is_bottom());
  EXPECT_TRUE(domain_a.leq(top));
  EXPECT_TRUE(TypedefAnnotationDomain::bottom().leq(domain_a));
  domain_a.set_to_bottom();
  EXPECT_TRUE(domain_a.is_bottom());
  EXPECT_FALSE(domain_a.is_top());
  EXPECT_TRUE(domain_a.leq(TypedefAnnotationDomain::top()));

  // classes
  domain_a = TypedefAnnotationDomain(m_type_a);
  auto domain_a1 = TypedefAnnotationDomain(m_type_a1);
  EXPECT_FALSE(domain_a.is_bottom());
  EXPECT_FALSE(domain_a.is_top());
  EXPECT_TRUE(domain_a1.leq(domain_a));
  EXPECT_FALSE(domain_a.leq(domain_a1));

  auto domain_a21 = TypedefAnnotationDomain(m_type_a21);
  EXPECT_FALSE(domain_a21.is_bottom());
  EXPECT_FALSE(domain_a21.is_top());
  EXPECT_TRUE(domain_a21.leq(domain_a));
  EXPECT_FALSE(domain_a.leq(domain_a21));

  // interfaces
  auto sub1 = TypedefAnnotationDomain(m_type_sub1);
  auto if1 = TypedefAnnotationDomain(m_type_if1);
  EXPECT_FALSE(sub1.is_bottom());
  EXPECT_FALSE(sub1.is_top());
  EXPECT_FALSE(if1.is_bottom());
  EXPECT_FALSE(if1.is_top());
  auto join = sub1.join(if1);
  EXPECT_EQ(join, TypedefAnnotationDomain(if1));
  EXPECT_TRUE(sub1.leq(if1));
  EXPECT_TRUE(sub1.leq(join));
  join = if1.join(sub1);
  EXPECT_EQ(join, TypedefAnnotationDomain(if1));
  EXPECT_TRUE(if1.leq(join));
  EXPECT_FALSE(if1.leq(sub1));
  auto obj = TypedefAnnotationDomain(type::java_lang_Object());
  EXPECT_TRUE(sub1.leq(obj));
  EXPECT_TRUE(if1.leq(obj));

  // none
  auto none = TypedefAnnotationDomain(nullptr);
  EXPECT_FALSE(none.is_bottom());
  EXPECT_FALSE(none.is_top());
  EXPECT_TRUE(none.is_none());
  EXPECT_TRUE(none.leq(obj));
  EXPECT_FALSE(obj.leq(none));

  // array
  auto a_array = TypedefAnnotationDomain(m_a_array);
  auto a1_array = TypedefAnnotationDomain(m_a1_array);
  auto array_join = a_array.join(a1_array);
  EXPECT_EQ(array_join, TypedefAnnotationDomain(m_a_array));
  EXPECT_TRUE(a_array.leq(array_join));

  a1_array = TypedefAnnotationDomain(m_a1_array);
  auto a2_array = TypedefAnnotationDomain(m_a2_array);
  array_join = a1_array.join(a2_array);
  EXPECT_EQ(array_join, TypedefAnnotationDomain(m_a_array));
  EXPECT_TRUE(a1_array.leq(array_join));
}

TEST_F(DexTypeEnvironmentTest, NullableDexTypeDomainTest) {
  auto null1 = DexTypeDomain::null();
  EXPECT_FALSE(null1.is_bottom());
  EXPECT_FALSE(null1.is_top());
  EXPECT_TRUE(null1.get_single_domain().is_none());
  EXPECT_TRUE(null1.get_annotation_domain().is_none());

  auto type_a = DexTypeDomain::create_nullable(m_type_a, m_anno_d1);
  null1.join_with(type_a);
  EXPECT_FALSE(null1.is_null());
  EXPECT_FALSE(null1.is_not_null());
  EXPECT_TRUE(null1.is_nullable());
  // Both Nullalbe
  EXPECT_EQ(null1, DexTypeDomain::create_nullable(m_type_a, m_anno_d1));
  EXPECT_EQ(*null1.get_dex_type(), m_type_a);
  EXPECT_EQ(*null1.get_annotation_type(), m_type_d1);
  EXPECT_EQ(type_a, DexTypeDomain::create_nullable(m_type_a, m_anno_d1));
  EXPECT_FALSE(null1.get_single_domain().is_none());
  EXPECT_FALSE(type_a.get_single_domain().is_none());
  EXPECT_FALSE(null1.get_annotation_domain().is_none());
  EXPECT_FALSE(type_a.get_annotation_domain().is_none());

  type_a = DexTypeDomain::create_nullable(m_type_a, m_anno_d1);
  null1 = DexTypeDomain::null();
  type_a.join_with(null1);
  EXPECT_FALSE(type_a.is_null());
  EXPECT_FALSE(type_a.is_not_null());
  EXPECT_TRUE(type_a.is_nullable());
  // Both Nullalbe
  EXPECT_EQ(type_a, DexTypeDomain::create_nullable(m_type_a, m_anno_d1));
  EXPECT_EQ(*type_a.get_dex_type(), m_type_a);
  EXPECT_EQ(*type_a.get_annotation_type(), m_type_d1);
  EXPECT_EQ(null1, DexTypeDomain::null());
  EXPECT_FALSE(type_a.get_single_domain().is_none());
  EXPECT_TRUE(null1.get_single_domain().is_none());
  EXPECT_FALSE(type_a.get_annotation_domain().is_none());
  EXPECT_TRUE(null1.get_annotation_domain().is_none());

  auto top1 = DexTypeDomain::top();
  auto top2 = DexTypeDomain::top();
  top1.join_with(top2);
  EXPECT_TRUE(top1.is_top());
  EXPECT_TRUE(top2.is_top());
  EXPECT_FALSE(top1.get_single_domain().is_none());
  EXPECT_FALSE(top2.get_single_domain().is_none());
  EXPECT_FALSE(top1.get_annotation_domain().is_none());
  EXPECT_FALSE(top2.get_annotation_domain().is_none());

  top1 = DexTypeDomain::top();
  auto bottom = DexTypeDomain::bottom();
  top1.join_with(bottom);
  EXPECT_TRUE(top1.is_top());
  EXPECT_TRUE(bottom.is_bottom());
  EXPECT_FALSE(top1.get_single_domain().is_none());
  EXPECT_FALSE(bottom.get_single_domain().is_none());
  EXPECT_FALSE(top1.get_annotation_domain().is_none());
  EXPECT_FALSE(bottom.get_annotation_domain().is_none());

  bottom = DexTypeDomain::bottom();
  top1 = DexTypeDomain::top();
  bottom.join_with(top1);
  EXPECT_TRUE(bottom.is_top());
  EXPECT_TRUE(top1.is_top());
  EXPECT_FALSE(bottom.get_single_domain().is_none());
  EXPECT_FALSE(top1.get_single_domain().is_none());
  EXPECT_FALSE(bottom.get_annotation_domain().is_none());
  EXPECT_FALSE(top1.get_annotation_domain().is_none());
}

TEST_F(DexTypeEnvironmentTest, SmallSetDexTypeDomainDeepHierarchyTest) {
  // 1 join with 1
  auto domain_a1 = SmallSetDexTypeDomain(m_type_a1);
  auto domain_a2 = SmallSetDexTypeDomain(m_type_a2);
  domain_a1.join_with(domain_a2);
  EXPECT_FALSE(domain_a1.is_top());
  EXPECT_FALSE(domain_a1.is_bottom());
  EXPECT_EQ(domain_a1.get_types(), get_type_set({m_type_a1, m_type_a2}));
  EXPECT_FALSE(domain_a2.is_top());
  EXPECT_FALSE(domain_a2.is_bottom());

  // 2 join with 1
  auto domain_a21 = SmallSetDexTypeDomain(m_type_a21);
  domain_a1.join_with(domain_a21);
  EXPECT_FALSE(domain_a1.is_top());
  EXPECT_FALSE(domain_a1.is_bottom());
  EXPECT_EQ(domain_a1.get_types(),
            get_type_set({m_type_a1, m_type_a2, m_type_a21}));
  EXPECT_FALSE(domain_a21.is_top());
  EXPECT_FALSE(domain_a21.is_bottom());

  // 3 join with 1
  auto domain_a211 = SmallSetDexTypeDomain(m_type_a211);
  domain_a1.join_with(domain_a211);
  EXPECT_FALSE(domain_a1.is_top());
  EXPECT_FALSE(domain_a1.is_bottom());
  EXPECT_EQ(domain_a1.get_types(),
            get_type_set({m_type_a1, m_type_a2, m_type_a21, m_type_a211}));
  EXPECT_FALSE(domain_a211.is_top());
  EXPECT_FALSE(domain_a211.is_bottom());

  // 4 => top
  auto domain_a = SmallSetDexTypeDomain(m_type_a);
  domain_a1.join_with(domain_a);
  EXPECT_TRUE(domain_a1.is_top());
  EXPECT_FALSE(domain_a1.is_bottom());
  EXPECT_FALSE(domain_a.is_top());
  EXPECT_FALSE(domain_a.is_bottom());

  // top and bottom
  domain_a1.set_to_top();
  EXPECT_TRUE(domain_a1.is_top());
  EXPECT_FALSE(domain_a1.is_bottom());
  EXPECT_TRUE(domain_a2.leq(domain_a1));
  EXPECT_TRUE(SmallSetDexTypeDomain::bottom().leq(domain_a1));
  domain_a1.set_to_bottom();
  EXPECT_TRUE(domain_a1.is_bottom());
  EXPECT_FALSE(domain_a1.is_top());
  EXPECT_TRUE(domain_a1.leq(SmallSetDexTypeDomain::top()));

  // leq and equals
  EXPECT_FALSE(domain_a2.leq(domain_a21));
  EXPECT_FALSE(domain_a21.leq(domain_a2));
  EXPECT_TRUE(domain_a2.leq(SmallSetDexTypeDomain::top()));
  EXPECT_TRUE(domain_a21.leq(SmallSetDexTypeDomain::top()));
  EXPECT_TRUE(SmallSetDexTypeDomain::bottom().leq(domain_a2));
  EXPECT_TRUE(SmallSetDexTypeDomain::bottom().leq(domain_a21));
  EXPECT_FALSE(domain_a2.equals(domain_a21));
  EXPECT_FALSE(domain_a21.equals(domain_a2));
  EXPECT_FALSE(domain_a2.equals(SmallSetDexTypeDomain::top()));
  EXPECT_FALSE(SmallSetDexTypeDomain::top().equals(domain_a21));
  EXPECT_FALSE(domain_a2.equals(SmallSetDexTypeDomain::bottom()));
  EXPECT_FALSE(SmallSetDexTypeDomain::bottom().equals(domain_a21));
  EXPECT_FALSE(
      SmallSetDexTypeDomain::top().equals(SmallSetDexTypeDomain::bottom()));
  EXPECT_FALSE(
      SmallSetDexTypeDomain::bottom().equals(SmallSetDexTypeDomain::top()));

  auto domain_set1 = SmallSetDexTypeDomain(m_type_a1);
  domain_set1.join_with(domain_a2);
  domain_set1.join_with(domain_a21);
  domain_set1.join_with(domain_a211);
  EXPECT_TRUE(domain_a2.leq(domain_set1));
  EXPECT_FALSE(domain_set1.leq(domain_a2));
  EXPECT_FALSE(domain_set1.equals(domain_a1));
  EXPECT_FALSE(domain_a1.equals(domain_set1));
  auto domain_set2 = SmallSetDexTypeDomain(m_type_a1);
  domain_set2.join_with(domain_a2);
  EXPECT_TRUE(domain_set2.leq(domain_set1));
  EXPECT_FALSE(domain_set1.leq(domain_set2));
  EXPECT_FALSE(domain_set1.equals(domain_set2));
  EXPECT_FALSE(domain_set2.equals(domain_set1));

  domain_set1.join_with(domain_a);
  EXPECT_TRUE(domain_a2.leq(domain_set1));
  EXPECT_FALSE(domain_set1.leq(domain_a2));
  EXPECT_TRUE(domain_set2.leq(domain_set1));
  EXPECT_FALSE(domain_set1.leq(domain_set2));
  EXPECT_FALSE(domain_set1.equals(domain_set2));
  EXPECT_FALSE(domain_set2.equals(domain_set1));

  domain_set1 = SmallSetDexTypeDomain(m_type_a1);
  domain_set2 = SmallSetDexTypeDomain(m_type_a1);
  EXPECT_TRUE(domain_set1.equals(domain_set2));
  EXPECT_TRUE(domain_set2.equals(domain_set1));
  domain_set1.join_with(domain_a2);
  domain_set2.join_with(domain_a2);
  EXPECT_TRUE(domain_set1.equals(domain_set2));
  EXPECT_TRUE(domain_set2.equals(domain_set1));
  domain_set1.join_with(domain_a21);
  domain_set1.join_with(domain_a211);
  domain_set1.join_with(domain_a);
  domain_set2.join_with(domain_a21);
  domain_set2.join_with(domain_a211);
  domain_set2.join_with(domain_a);
  EXPECT_TRUE(domain_set1.equals(domain_set2));
  EXPECT_TRUE(domain_set2.equals(domain_set1));
}

TEST_F(DexTypeEnvironmentTest, SmallSetDexTypeDomainFlatHierarchyTest) {
  auto domain_c1 = SmallSetDexTypeDomain(m_type_c1);
  auto domain_c2 = SmallSetDexTypeDomain(m_type_c2);
  domain_c1.join_with(domain_c2);
  EXPECT_FALSE(domain_c1.is_top());
  EXPECT_FALSE(domain_c1.is_bottom());
  EXPECT_EQ(domain_c1.get_types(), get_type_set({m_type_c1, m_type_c2}));

  auto domain_c3 = SmallSetDexTypeDomain(m_type_c3);
  domain_c1.join_with(domain_c3);
  EXPECT_FALSE(domain_c1.is_top());
  EXPECT_FALSE(domain_c1.is_bottom());
  EXPECT_EQ(domain_c1.get_types(),
            get_type_set({m_type_c1, m_type_c2, m_type_c3}));

  auto domain_c4 = SmallSetDexTypeDomain(m_type_c4);
  domain_c1.join_with(domain_c4);
  EXPECT_FALSE(domain_c1.is_top());
  EXPECT_FALSE(domain_c1.is_bottom());
  EXPECT_EQ(domain_c1.get_types(),
            get_type_set({m_type_c1, m_type_c2, m_type_c3, m_type_c4}));

  auto domain_c5 = SmallSetDexTypeDomain(m_type_c5);
  domain_c1.join_with(domain_c5);
  EXPECT_TRUE(domain_c1.is_top());
  EXPECT_FALSE(domain_c1.is_bottom());

  // set join with top => top
  auto domain_d = SmallSetDexTypeDomain(m_type_d);
  auto domain_top = domain_c1;
  EXPECT_TRUE(domain_top.is_top());
  domain_top.join_with(domain_d);
  EXPECT_TRUE(domain_top.is_top());
  EXPECT_FALSE(domain_top.is_bottom());
  EXPECT_FALSE(domain_d.is_top());
  EXPECT_FALSE(domain_d.is_bottom());
  EXPECT_EQ(domain_d.get_types(), get_type_set({m_type_d}));

  domain_top = domain_c1;
  EXPECT_TRUE(domain_top.is_top());
  domain_d.join_with(domain_top);
  EXPECT_TRUE(domain_d.is_top());
  EXPECT_FALSE(domain_d.is_bottom());
}

TEST_F(DexTypeEnvironmentTest, SmallSetDexTypeDomainMixedHierarchyTest) {
  auto domain_c1 = SmallSetDexTypeDomain(m_type_c1);
  auto domain_c2 = SmallSetDexTypeDomain(m_type_c2);
  auto domain_c3 = SmallSetDexTypeDomain(m_type_c3);
  domain_c1.join_with(domain_c2);
  domain_c1.join_with(domain_c3);
  EXPECT_EQ(domain_c1.get_types(),
            get_type_set({m_type_c1, m_type_c2, m_type_c3}));

  auto domain_b = SmallSetDexTypeDomain(m_type_b);
  auto domain_b1 = SmallSetDexTypeDomain(m_type_b1);
  domain_c1.join_with(domain_b);
  EXPECT_EQ(domain_c1.get_types(),
            get_type_set({m_type_c1, m_type_c2, m_type_c3, m_type_b}));
  domain_c1.join_with(domain_b1);
  EXPECT_TRUE(domain_c1.is_top());
}

TEST_F(DexTypeEnvironmentTest, DexTypeDomainReduceProductTest) {
  auto domain = DexTypeDomain::create_not_null(type::java_lang_Object());

  domain.join_with(DexTypeDomain::create_not_null(
      type::make_array_type(type::java_lang_String())));
  EXPECT_TRUE(domain.get_single_domain().is_top());
  EXPECT_TRUE(domain.get_annotation_domain().is_top());
  EXPECT_FALSE(domain.get_set_domain().is_top());
  EXPECT_EQ(domain.get_type_set(),
            get_type_set({type::java_lang_Object(),
                          type::make_array_type(type::java_lang_String())}));

  auto domain_c1 = DexTypeDomain::create_nullable(m_type_c1, m_anno_d1);
  domain_c1.join_with(DexTypeDomain::create_nullable(m_type_c2, m_anno_d2));
  domain_c1.join_with(DexTypeDomain::create_nullable(m_type_c3, m_anno_d3));
  domain_c1.join_with(DexTypeDomain::create_nullable(m_type_c4, m_anno_d4));
  domain_c1.join_with(DexTypeDomain::create_nullable(m_type_c5, m_anno_d5));
  EXPECT_FALSE(domain_c1.get_single_domain().is_top());
  EXPECT_FALSE(domain_c1.get_annotation_domain().is_top());
  EXPECT_TRUE(domain_c1.get_set_domain().is_top());

  domain_c1 = DexTypeDomain::create_nullable(m_type_c1, m_anno_d1);
  auto domain_c2 = DexTypeDomain::create_nullable(m_type_c2, m_anno_d2);
  domain_c2.join_with(DexTypeDomain::create_nullable(m_type_c3, m_anno_d3));
  domain_c2.join_with(DexTypeDomain::create_nullable(m_type_c4, m_anno_d4));
  domain_c2.join_with(DexTypeDomain::create_nullable(m_type_c5, m_anno_d5));
  EXPECT_FALSE(domain_c2.get_single_domain().is_top());
  EXPECT_FALSE(domain_c2.get_annotation_domain().is_top());
  EXPECT_TRUE(domain_c2.get_set_domain().is_top());
  domain_c1.join_with(domain_c2);
  EXPECT_FALSE(domain_c1.get_single_domain().is_top());
  EXPECT_FALSE(domain_c1.get_annotation_domain().is_top());
  EXPECT_TRUE(domain_c1.get_set_domain().is_top());
}

TEST_F(DexTypeEnvironmentTest, BaseClassInterfaceJoinTest) {
  auto abs_me = SingletonDexTypeDomain(m_abs_map_entry);
  auto intf = SingletonDexTypeDomain(m_map_entry);
  abs_me.join_with(intf);
  EXPECT_FALSE(abs_me.is_top());
  EXPECT_EQ(abs_me, SingletonDexTypeDomain(m_map_entry));
  EXPECT_FALSE(intf.is_top());

  auto im_e = SingletonDexTypeDomain(m_im_entry);
  im_e.join_with(intf);
  EXPECT_FALSE(im_e.is_top());
  EXPECT_EQ(im_e, SingletonDexTypeDomain(m_map_entry));
  EXPECT_FALSE(intf.is_top());

  auto im_me = SingletonDexTypeDomain(m_im_map_entry);
  im_me.join_with(intf);
  EXPECT_FALSE(im_me.is_top());
  EXPECT_EQ(im_me, SingletonDexTypeDomain(m_map_entry));
  EXPECT_FALSE(intf.is_top());

  auto intf_array = SingletonDexTypeDomain(m_map_entry_array);
  auto im_me_array = SingletonDexTypeDomain(m_im_map_entry_array);
  im_me_array.join_with(intf_array);
  EXPECT_FALSE(im_me_array.is_top());
  EXPECT_EQ(im_me_array, SingletonDexTypeDomain(m_map_entry_array));
  EXPECT_FALSE(intf_array.is_top());
}

/*
 * A framework interface is often referenced by name without its definition
 * being available -- Lorg/apache/http/HttpEntity; left the Android SDK at API
 * 23, for instance. The implementing class still names it in its own
 * interface list, so joining the two is answerable even though the interface
 * has no DexClass of its own.
 */
TEST_F(DexTypeEnvironmentTest, ExternalInterfaceWithoutClassJoinTest) {
  auto* external_intf = DexType::make_type("Lorg/example/ExternalIntf;");
  ASSERT_EQ(nullptr, type_class(external_intf));

  auto* impl_type = DexType::make_type("LExternalIntfImpl;");
  ClassCreator impl_creator(impl_type);
  impl_creator.set_super(type::java_lang_Object());
  impl_creator.add_interface(external_intf);
  impl_creator.create();

  auto intf = SingletonDexTypeDomain(external_intf);
  auto impl = SingletonDexTypeDomain(impl_type);
  intf.join_with(impl);
  EXPECT_EQ(intf, SingletonDexTypeDomain(external_intf));
  EXPECT_FALSE(impl.is_top());

  intf = SingletonDexTypeDomain(external_intf);
  impl.join_with(intf);
  EXPECT_EQ(impl, SingletonDexTypeDomain(external_intf));
  EXPECT_FALSE(intf.is_top());

  // An unrelated class shares nothing with it, and the interface has no class
  // to walk, so there is still no answer.
  auto unrelated = SingletonDexTypeDomain(m_type_a);
  intf = SingletonDexTypeDomain(external_intf);
  unrelated.join_with(intf);
  EXPECT_TRUE(unrelated.is_top());
}

namespace {

// A class extending Object directly, implementing the given interfaces. The
// shared fixture's Sub* types all extend Base, so their common super class is
// never Object and the shared-interface path is never reached.
DexType* make_object_rooted_impl(const char* name,
                                 std::initializer_list<DexType*> intfs) {
  auto* type = DexType::make_type(name);
  ClassCreator creator(type);
  creator.set_super(type::java_lang_Object());
  for (auto* intf : intfs) {
    creator.add_interface(intf);
  }
  creator.create();
  return type;
}

DexType* make_interface(const char* name,
                        std::initializer_list<DexType*> supers) {
  auto* type = DexType::make_type(name);
  ClassCreator creator(type);
  creator.set_super(type::java_lang_Object());
  creator.set_access(ACC_PUBLIC | ACC_INTERFACE);
  for (auto* super : supers) {
    creator.add_interface(super);
  }
  creator.create();
  return type;
}

} // namespace

/*
 * Two classes related only by an interface. The super class walk reaches
 * Object and stops there, but Object is not the least upper bound -- the
 * shared interface is. This is the shape behind the media3 HttpEntity merge.
 */
TEST_F(DexTypeEnvironmentTest, SharedInterfaceJoinTest) {
  auto* shared = make_interface("LShared;", {});
  auto* impl_a = make_object_rooted_impl("LSharedImplA;", {shared});
  auto* impl_b = make_object_rooted_impl("LSharedImplB;", {shared});

  auto a = SingletonDexTypeDomain(impl_a);
  auto b = SingletonDexTypeDomain(impl_b);
  a.join_with(b);
  EXPECT_EQ(a, SingletonDexTypeDomain(shared));

  // Commutative.
  b = SingletonDexTypeDomain(impl_b);
  auto a2 = SingletonDexTypeDomain(impl_a);
  b.join_with(a2);
  EXPECT_EQ(b, SingletonDexTypeDomain(shared));

  // An interface only one of them implements is not a bound for both, so the
  // answer stays the shared one.
  auto* extra = make_interface("LExtraOnA;", {});
  auto* impl_a_extra =
      make_object_rooted_impl("LSharedImplAExtra;", {shared, extra});
  auto ae = SingletonDexTypeDomain(impl_a_extra);
  auto b2 = SingletonDexTypeDomain(impl_b);
  ae.join_with(b2);
  EXPECT_EQ(ae, SingletonDexTypeDomain(shared));
}

/*
 * Sharing several incomparable interfaces has no single answer: the least
 * upper bound is an intersection type, which one DexType cannot hold. Top is
 * the honest result -- reporting Object instead would be read as an exact
 * type by IRTypeChecker and reject legal code.
 */
TEST_F(DexTypeEnvironmentTest, MultipleSharedInterfacesJoinToTopTest) {
  auto* i = make_interface("LBothI;", {});
  auto* j = make_interface("LBothJ;", {});
  auto* x = make_object_rooted_impl("LBothX;", {i, j});
  auto* y = make_object_rooted_impl("LBothY;", {i, j});

  auto dx = SingletonDexTypeDomain(x);
  auto dy = SingletonDexTypeDomain(y);
  dx.join_with(dy);
  EXPECT_TRUE(dx.is_top());
}

/*
 * When one shared interface extends another, only the most specific one is
 * the bound. This also covers the transitive walk: LDeepBase; is reached only
 * through LDeepSub;, which the local `implements` helper cannot do.
 */
TEST_F(DexTypeEnvironmentTest, MostSpecificSharedInterfaceJoinTest) {
  auto* base_intf = make_interface("LDeepBase;", {});
  auto* sub_intf = make_interface("LDeepSub;", {base_intf});
  auto* x = make_object_rooted_impl("LDeepX;", {sub_intf});
  auto* y = make_object_rooted_impl("LDeepY;", {sub_intf});

  auto dx = SingletonDexTypeDomain(x);
  auto dy = SingletonDexTypeDomain(y);
  dx.join_with(dy);
  EXPECT_EQ(dx, SingletonDexTypeDomain(sub_intf));

  // Sharing only the base interface resolves to it.
  auto* z = make_object_rooted_impl("LDeepZ;", {base_intf});
  auto dx2 = SingletonDexTypeDomain(x);
  auto dz = SingletonDexTypeDomain(z);
  dx2.join_with(dz);
  EXPECT_EQ(dx2, SingletonDexTypeDomain(base_intf));
}

/*
 * A class hierarchy takes precedence over a shared interface: the common
 * super class is more specific than anything both merely implement.
 */
TEST_F(DexTypeEnvironmentTest, CommonSuperClassPreferredOverInterfaceTest) {
  auto* shared = make_interface("LPreferShared;", {});
  auto* common = make_object_rooted_impl("LPreferCommon;", {shared});

  auto* left = DexType::make_type("LPreferLeft;");
  ClassCreator left_creator(left);
  left_creator.set_super(common);
  left_creator.create();

  auto* right = DexType::make_type("LPreferRight;");
  ClassCreator right_creator(right);
  right_creator.set_super(common);
  right_creator.create();

  auto dl = SingletonDexTypeDomain(left);
  auto dr = SingletonDexTypeDomain(right);
  dl.join_with(dr);
  EXPECT_EQ(dl, SingletonDexTypeDomain(common));
}

TEST_F(DexTypeEnvironmentTest, TypedefAnnotationDomain) {
  auto d1 = DexTypeDomain::create_for_anno(m_anno_d1);
  EXPECT_FALSE(d1.is_top());
  EXPECT_EQ(*d1.get_annotation_type(), m_type_d1);

  auto d2 = DexTypeDomain::create_for_anno(m_anno_d2);
  d1.join_with(d2);
  EXPECT_EQ(d1.get_annotation_domain(),
            TypedefAnnotationDomain(type::java_lang_Object()));
}

/*
 * `find_common_type` resolves two classes with no common super class below
 * Object through the interfaces they share. Sharing exactly one is
 * representable; sharing several incomparable ones is not, because the least
 * upper bound is an intersection type that a single DexType cannot hold, so
 * the join gives up to Top. Whether a fold ever reaches that state depends on
 * the order, so callers folding over a set must impose one.
 */
TEST_F(DexTypeEnvironmentTest, JoinOverThreeTypesIsOrderDependent) {
  // Object-rooted, unlike every Sub*, so a join between them has no common
  // super class below Object and falls through to the interfaces.
  auto make = [this](const char* name, bool both) {
    auto* type = DexType::make_type(name);
    ClassCreator cc(type);
    cc.set_super(type::java_lang_Object());
    cc.add_interface(m_type_if1);
    if (both) {
      cc.add_interface(m_type_if2);
    }
    cc.create();
    return type;
  };
  auto* two_if_a = make("LTwoIfA;", true);
  auto* two_if_b = make("LTwoIfB;", true);
  auto* one_if = make("LOneIf;", false);

  auto join3 = [](const DexType* x, const DexType* y, const DexType* z) {
    auto acc = SingletonDexTypeDomain(x);
    acc.join_with(SingletonDexTypeDomain(y));
    acc.join_with(SingletonDexTypeDomain(z));
    return acc;
  };

  // The claim: two pairings of the same three types disagree.
  auto both_first = join3(two_if_a, two_if_b, one_if);
  auto single_first = join3(two_if_a, one_if, two_if_b);
  EXPECT_NE(both_first, single_first);

  // And which is which. Joining the two classes that share If1 and If2 has no
  // representable answer, and Top is absorbing thereafter.
  EXPECT_TRUE(both_first.is_top());
  // Taking the one-interface class first shares only If1, which is
  // representable, and the remaining operand implements it.
  EXPECT_EQ(single_first, SingletonDexTypeDomain(m_type_if1));

  // These two operands happen to commute. That is not general: when the LCA
  // reaches Object, `find_common_interfaces` collects the shared set from the
  // left operand only, so an interface joined with one of its implementors
  // answers differently depending on which side it sits.
  auto ab = SingletonDexTypeDomain(two_if_a);
  ab.join_with(SingletonDexTypeDomain(one_if));
  auto ba = SingletonDexTypeDomain(one_if);
  ba.join_with(SingletonDexTypeDomain(two_if_a));
  EXPECT_EQ(ab, ba);
}
