/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "DexStructure.h"
#include "Creators.h"
#include "DexLimits.h"
#include "DexUtil.h"
#include "IRAssembler.h"
#include "RedexTest.h"
#include <gtest/gtest.h>

class DexStructureTest : public RedexTest {};

DexClass* create_a_class(const char* description) {
  ClassCreator cc(DexType::make_type(description));
  cc.set_super(type::java_lang_Object());
  return cc.create();
}

TEST_F(DexStructureTest, remove_class) {
  DexStoresVector stores;
  auto* foo_cls = create_a_class("Lfoo;");
  auto* bar_cls = create_a_class("Lbar;");
  bar_cls->set_perf_sensitive(PerfSensitiveGroup::BETAMAP_ORDERED);

  {
    DexStore store("root");
    store.add_classes({foo_cls, bar_cls});
    stores.push_back(std::move(store));
  }
  auto scope = build_class_scope(stores);
  init_classes::InitClassesWithSideEffects init_classes_with_side_effects(
      scope, /* create_init_class_insns */ false);

  DexStructure dex1;

  DexType* ty = DexType::make_type("Lbaz;");
  DexProto* proto = DexProto::make_proto(ty, DexTypeList::make_type_list({}));
  const auto* str1 = DexString::make_string("m1");
  const auto* str2 = DexString::make_string("m2");
  const auto* str3 = DexString::make_string("m3");
  DexMethodRef* m1 = DexMethod::make_method(ty, str1, proto);
  DexMethodRef* m2 = DexMethod::make_method(ty, str2, proto);
  DexMethodRef* m3 = DexMethod::make_method(ty, str3, proto);
  DexFieldRef* f1 = DexField::make_field(ty, DexString::make_string("f1"), ty);
  DexFieldRef* f2 = DexField::make_field(ty, DexString::make_string("f2"), ty);
  DexFieldRef* f3 = DexField::make_field(ty, DexString::make_string("f3"), ty);

  dex1.add_class_no_checks({m1, m2}, {f2, f3}, {ty}, {}, {}, 0, foo_cls);
  dex1.add_class_no_checks({m1, m2, m3}, {f1}, {ty}, {}, {}, 0, bar_cls);
  EXPECT_EQ(dex1.get_mref_occurrences(m1), 2);
  EXPECT_EQ(dex1.get_mref_occurrences(m2), 2);
  EXPECT_EQ(dex1.get_mref_occurrences(m3), 1);

  EXPECT_EQ(dex1.get_fref_occurrences(f1), 1);
  EXPECT_EQ(dex1.get_fref_occurrences(f2), 1);
  EXPECT_EQ(dex1.get_fref_occurrences(f3), 1);

  EXPECT_EQ(dex1.get_tref_occurrences(ty), 2);

  // Check perf based classes sorting.
  auto classes = dex1.get_classes();
  EXPECT_EQ(classes.size(), 2);
  EXPECT_EQ(classes[0]->is_perf_sensitive(), false);
  EXPECT_EQ(classes[1]->is_perf_sensitive(), true);

  classes = dex1.get_classes(true);
  EXPECT_EQ(classes[0]->is_perf_sensitive(), true);
  EXPECT_EQ(classes[1]->is_perf_sensitive(), false);

  // Remove foo1_cls.
  dex1.remove_class(&init_classes_with_side_effects, {m1}, {f2}, {ty}, {}, {},
                    0, foo_cls);
  EXPECT_EQ(dex1.get_mref_occurrences(m1), 1);
  EXPECT_EQ(dex1.get_mref_occurrences(m2), 2);
  EXPECT_EQ(dex1.get_mref_occurrences(m3), 1);
  EXPECT_EQ(dex1.get_fref_occurrences(f1), 1);
  EXPECT_EQ(dex1.get_fref_occurrences(f2), 0);
  EXPECT_EQ(dex1.get_fref_occurrences(f3), 1);
  EXPECT_EQ(dex1.get_tref_occurrences(ty), 1);
  EXPECT_EQ(dex1.size(), 1);
}

TEST_F(DexStructureTest, method_ref_room) {
  // Room left: the 16-bit method index space minus held and reserved refs.
  EXPECT_EQ(MethodRefRoom(0, 0).left(), kMaxMethodRefs);
  EXPECT_EQ(MethodRefRoom(100, 20).left(), kMaxMethodRefs - 120);
  EXPECT_TRUE(MethodRefRoom(kMaxMethodRefs - 1, 0).can_add());
  EXPECT_FALSE(MethodRefRoom(kMaxMethodRefs - 1, 0).can_add(2));
  EXPECT_FALSE(MethodRefRoom(kMaxMethodRefs - 1, 1).can_add());
  EXPECT_FALSE(MethodRefRoom(kMaxMethodRefs, 0).can_add());
  EXPECT_TRUE(MethodRefRoom(kMaxMethodRefs, 0).can_add(0));
  // A dex already over the limit, for example because a reserved reference
  // was spent and is still counted as reserved, has no room.
  EXPECT_EQ(MethodRefRoom(kMaxMethodRefs, 1).left(), 0);

  MethodRefRoom room(kMaxMethodRefs - 3, 1);
  room.add();
  EXPECT_EQ(room.left(), 1);
  room.add();
  EXPECT_FALSE(room.can_add());
  EXPECT_ANY_THROW(room.add());
}

TEST_F(DexStructureTest, method_ref_room_for_dex) {
  // A dex's room counts each method it defines or references once.
  auto* foo_cls = create_a_class("Lfoo;");
  auto* m = DexMethod::make_method("Lfoo;.m:()V")
                ->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  m->set_code(assembler::ircode_from_string(R"((
    (invoke-static () "Lbar;.n:()V")
    (invoke-static () "Lbar;.n:()V")
    (return-void)
  ))"));
  foo_cls->add_method(m);
  EXPECT_EQ(MethodRefRoom::for_dex({foo_cls}, 5).left(),
            kMaxMethodRefs - 2 - 5);
}
