/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <algorithm>
#include <string_view>
#include <utility>
#include <vector>

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

TEST_F(ConstantValueTest, SingletonNotLeqObjectWithImmutAttr) {
  EXPECT_FALSE(sod.leq(owia));
  EXPECT_FALSE(owia.leq(sod));
}

namespace {

ConstantValue make_object_with_immut_attr(
    std::string_view type,
    const std::vector<std::pair<std::string_view, int64_t>>& attrs,
    bool jvm_cached_singleton = false) {
  std::vector<ImmutableAttr> immutable_attrs;
  immutable_attrs.reserve(attrs.size());
  for (const auto& [field, value] : attrs) {
    immutable_attrs.emplace_back(ImmutableAttr::Attr(dynamic_cast<DexField*>(
                                     DexField::make_field(field))),
                                 SignedConstantDomain(value));
  }
  std::sort(immutable_attrs.begin(), immutable_attrs.end(),
            [](const auto& a, const auto& b) { return a.attr < b.attr; });
  ObjectWithImmutAttr object(DexType::make_type(type),
                             static_cast<uint32_t>(immutable_attrs.size()));
  object.jvm_cached_singleton = jvm_cached_singleton;
  for (const auto& immutable_attr : immutable_attrs) {
    object.write_value(immutable_attr.attr, immutable_attr.value);
  }
  return ObjectWithImmutAttrDomain(std::move(object));
}

} // namespace

TEST_F(ConstantValueTest, LeqAgreesWithJoin) {
  const std::vector<ConstantValue> values = {
      ConstantValue::top(),
      ConstantValue::bottom(),
      one,
      zero,
      nez,
      scd_not_only_nez,
      sod,
      SingletonObjectDomain(
          dynamic_cast<DexField*>(DexField::make_field("LFoo;.baz:LFoo;"))),
      sd_a,
      sd_b,
      owia,
      make_object_with_immut_attr("LBar;", {{"LBar;.ordinal:I", 3}}),
      make_object_with_immut_attr("LBar;", {{"LBar;.ordinal:I", 4}}),
      make_object_with_immut_attr(
          "LBar;", {{"LBar;.ordinal:I", 4}, {"LBar;.code:I", 7}}),
      make_object_with_immut_attr("Ljava/lang/Integer;",
                                  {{"Ljava/lang/Integer;.value:I", 5}},
                                  /* jvm_cached_singleton */ true),
      make_object_with_immut_attr("Ljava/lang/Integer;",
                                  {{"Ljava/lang/Integer;.value:I", 5}}),
  };
  for (const auto& a : values) {
    for (const auto& b : values) {
      EXPECT_EQ(a.leq(b), a.join(b) == b)
          << "leq(" << a << ", " << b << ") is " << a.leq(b)
          << ", but their join is " << a.join(b);
    }
  }
}

TEST_F(ConstantValueTest, MeetOfCachedAndUncachedBoxedIntegerIsCached) {
  auto cached = make_object_with_immut_attr(
      "Ljava/lang/Integer;", {{"Ljava/lang/Integer;.value:I", 5}},
      /* jvm_cached_singleton */ true);
  auto uncached = make_object_with_immut_attr(
      "Ljava/lang/Integer;", {{"Ljava/lang/Integer;.value:I", 5}});
  EXPECT_EQ(meet(cached, uncached), cached);
  EXPECT_EQ(meet(uncached, cached), cached);
  EXPECT_TRUE(meet(cached, uncached).leq(cached));
  EXPECT_TRUE(meet(cached, uncached).leq(uncached));
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
