/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "AbstractDomainPropertyTest.h"
#include "ConstantEnvironment.h"
#include "RedexTest.h"

struct Constants {
  ConstantValue one{SignedConstantDomain(1)};

  ConstantValue zero{SignedConstantDomain(0)};

  ConstantValue nez{SignedConstantDomain::nez()};

  ConstantValue sod{SingletonObjectDomain(
      dynamic_cast<DexField*>(DexField::make_field("LFoo;.bar:LFoo;")))};

  ConstantValue owia{ObjectWithImmutAttrDomain(
      ObjectWithImmutAttr(DexType::make_type("LFoo;"), 0))};

  ConstantValue sd_a{StringDomain(DexString::make_string("A"))};

  ConstantValue sd_b{StringDomain(DexString::make_string("B"))};

  ConstantValue scd_not_only_nez =
      SignedConstantDomain::from_constants({-1, 1});

  Constants() { verifyConstantsSetup(); }

  void verifyConstantsSetup() const {
    ASSERT_TRUE(scd_not_only_nez.is_nez())
        << "scd_not_only_nez is intended to be nez";
    ASSERT_FALSE(scd_not_only_nez.is_nez_only())
        << "scd_not_only_nez is intended to be not nez only";
  }
};

INSTANTIATE_TYPED_TEST_SUITE_P(ConstantValue,
                               AbstractDomainPropertyTest,
                               ConstantValue);

template <>
void AbstractDomainPropertyTest<ConstantValue>::SetUpTestCase() {
  g_redex = new RedexContext();
}

template <>
void AbstractDomainPropertyTest<ConstantValue>::TearDownTestCase() {
  delete g_redex;
}

template <>
std::vector<ConstantValue>
AbstractDomainPropertyTest<ConstantValue>::non_extremal_values() {
  Constants constants;
  return {
      constants.one, constants.zero, constants.nez,
      constants.sod, constants.sd_a, constants.sd_b,
      // constants.owia FIXME. The meet of ObjectWithImmutAttrDomain with
      // itself, and with SingletonObjectDomain, can go to top(), which is
      // wrong.
  };
}

class ConstantValueTest : public RedexTest, public Constants {
 protected:
  static auto meet(const ConstantValue& x, const ConstantValue& y) {
    return x.meet(y);
  }
};

TEST_F(ConstantValueTest, meet) {
  using namespace sign_domain;

  EXPECT_EQ(meet(zero, sod), ConstantValue::bottom());
  EXPECT_EQ(meet(ConstantValue::top(), sod), sod);
  EXPECT_EQ(meet(sod, ConstantValue::top()), sod);

  EXPECT_EQ(meet(zero, owia), ConstantValue::bottom());
  EXPECT_EQ(meet(nez, owia), owia);
  EXPECT_EQ(meet(owia, nez), owia);
  EXPECT_EQ(meet(ConstantValue::top(), owia), owia);
  EXPECT_EQ(meet(owia, ConstantValue::top()), owia);

  EXPECT_EQ(meet(sod, owia), nez);
  EXPECT_EQ(meet(owia, sod), nez);

  EXPECT_EQ(meet(sd_a, sd_b), ConstantValue::bottom());
  EXPECT_EQ(meet(sd_b, sd_a), ConstantValue::bottom());
}

TEST_F(ConstantValueTest, meetNezOnlySCDWithSingletonResultsInSingleton) {
  EXPECT_EQ(meet(nez, sod), sod);
  EXPECT_EQ(meet(sod, nez), sod);
}

TEST_F(ConstantValueTest, meetNotOnlyNezSCDWithSingletonResultsInBottom) {
  EXPECT_EQ(meet(scd_not_only_nez, sod), ConstantValue::bottom());
  EXPECT_EQ(meet(sod, scd_not_only_nez), ConstantValue::bottom());
}

TEST_F(ConstantValueTest, SingletonLeqNezOnlySCD) {
  EXPECT_FALSE(nez.leq(sod));
  EXPECT_TRUE(sod.leq(nez));
}

TEST_F(ConstantValueTest, SingletonNotLeqNotOnlyNezSCD) {
  EXPECT_FALSE(sod.leq(scd_not_only_nez));
  EXPECT_FALSE(scd_not_only_nez.leq(sod));
}

TEST_F(ConstantValueTest, join) {
  using namespace sign_domain;

  auto join = [](const auto& x, const auto& y) { return x.join(y); };

  EXPECT_EQ(join(zero, sod), ConstantValue::top());
  EXPECT_EQ(join(nez, sod), nez);
  EXPECT_EQ(join(sod, nez), nez);
  EXPECT_EQ(join(ConstantValue::top(), sod), ConstantValue::top());
  EXPECT_EQ(join(sod, ConstantValue::top()), ConstantValue::top());

  EXPECT_EQ(join(zero, owia), ConstantValue::top());
  EXPECT_EQ(join(nez, owia), nez);
  EXPECT_EQ(join(owia, nez), nez);
  EXPECT_EQ(join(ConstantValue::top(), owia), ConstantValue::top());
  EXPECT_EQ(join(owia, ConstantValue::top()), ConstantValue::top());

  EXPECT_EQ(join(sod, owia), nez);
  EXPECT_EQ(join(owia, sod), nez);

  EXPECT_EQ(join(sd_a, sd_b), nez);
  EXPECT_EQ(join(sd_b, sd_a), nez);
}

TEST_F(ConstantValueTest, nonTopBitsetIsNotNezOnly) {
  ConstantValue non_top_bitset = meet(
      SignedConstantDomain(-1, 0xffff), // low6bit is top, but bitset is not.
      nez);
  EXPECT_TRUE(non_top_bitset.is_nez());
  EXPECT_FALSE(non_top_bitset.is_nez_only());
}

TEST_F(ConstantValueTest, nonTopLow6bitIsNotNezOnly) {
  ConstantValue non_top_low6bit =
      meet(SignedConstantDomain(-1, 1), // bitset is top, but low6bit is not.
           nez);
  EXPECT_TRUE(non_top_low6bit.is_nez());
  EXPECT_FALSE(non_top_low6bit.is_nez_only());
}

// Meeting two objects that are never the same object gives Bottom of the
// object kind, which no object is below.
TEST_F(ConstantValueTest, objectIsNotLeqBottomOfItsKind) {
  ObjectWithImmutAttrDomain object(
      ObjectWithImmutAttr(DexType::make_type("LFoo;"), 0));
  ObjectWithImmutAttrDomain bottom(
      ObjectWithImmutAttr(DexType::make_type("LFoo;"), 0));
  bottom.set_to_bottom();
  EXPECT_FALSE(object.leq(bottom));
  EXPECT_FALSE(ConstantValue(object).leq(ConstantValue(bottom)));
  EXPECT_TRUE(bottom.leq(object));
}
