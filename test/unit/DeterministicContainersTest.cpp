/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "DeterministicContainers.h"
#include "RedexTest.h"

#include <cstdlib>
#include <gmock/gmock.h>
#include <gtest/gtest.h>
#include <map>
#include <memory>
#include <set>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

using ::testing::ElementsAre;
using ::testing::ElementsAreArray;
using ::testing::SizeIs;
using ::testing::UnorderedElementsAre;
using ::testing::UnorderedElementsAreArray;

class DeterministicContainersTest : public RedexTest {
 protected:
  DeterministicContainersTest() {}
};

TEST_F(DeterministicContainersTest, unordered_any_map) {
  UnorderedMap<int, int> map{{1, 42}};
  EXPECT_EQ(1, unordered_any(map)->first);
  EXPECT_EQ(42, unordered_any(map)->second);
}

TEST_F(DeterministicContainersTest, unordered_any_multimap) {
  UnorderedMultiMap<int, int> map{{1, 42}};
  EXPECT_EQ(1, unordered_any(map)->first);
  EXPECT_EQ(42, unordered_any(map)->second);
}

TEST_F(DeterministicContainersTest, unordered_any_set) {
  UnorderedSet<int> set({23});
  EXPECT_EQ(23, *unordered_any(set));
}

TEST_F(DeterministicContainersTest, unordered_any_set_empty) {
  UnorderedSet<int> set;
  EXPECT_EQ(set.end(), unordered_any(set));
}

namespace {
template <class Collection>
concept CanGetOnly = requires(Collection&& collection) {
  only(std::forward<Collection>(collection));
};

static_assert(CanGetOnly<UnorderedMap<int, int>&>);
static_assert(CanGetOnly<const UnorderedMap<int, int>&>);
static_assert(!CanGetOnly<UnorderedMap<int, int>>);
static_assert(!CanGetOnly<const UnorderedMap<int, int>>);
static_assert(!CanGetOnly<UnorderedSet<int>>);
static_assert(!CanGetOnly<UnorderedBag<int>>);
static_assert(!CanGetOnly<std::vector<int>>);
static_assert(!CanGetOnly<const std::vector<int>>);
} // namespace

TEST_F(DeterministicContainersTest, only_map) {
  UnorderedMap<int, std::unique_ptr<int>> map;
  map.emplace(1, std::make_unique<int>(42));
  auto& entry = only(map);
  static_assert(std::is_same_v<decltype(entry),
                               std::pair<const int, std::unique_ptr<int>>&>);
  EXPECT_EQ(1, entry.first);
  EXPECT_EQ(&map.at(1), &entry.second);
  *entry.second = 23;
  EXPECT_EQ(23, *map.at(1));

  const auto& const_entry = only(std::as_const(map));
  static_assert(
      std::is_same_v<decltype(only(std::as_const(map))),
                     const std::pair<const int, std::unique_ptr<int>>&>);
  EXPECT_EQ(&entry, &const_entry);
}

TEST_F(DeterministicContainersTest, only_set) {
  UnorderedSet<int> set{23};
  static_assert(std::is_same_v<decltype(only(set)), const int&>);
  static_assert(std::is_same_v<decltype(only(std::as_const(set))), const int&>);
  EXPECT_EQ(23, only(set));
  EXPECT_EQ(&*unordered_any(set), &only(std::as_const(set)));
}

TEST_F(DeterministicContainersTest, only_bag) {
  UnorderedBag<std::unique_ptr<int>> bag;
  bag.insert(std::make_unique<int>(42));
  auto& value = only(bag);
  static_assert(std::is_same_v<decltype(value), std::unique_ptr<int>&>);
  EXPECT_EQ(&*unordered_any(bag), &value);
  *value = 23;
  EXPECT_EQ(23, **unordered_any(bag));
  static_assert(std::is_same_v<decltype(only(std::as_const(bag))),
                               const std::unique_ptr<int>&>);
  EXPECT_EQ(&value, &only(std::as_const(bag)));
}

TEST_F(DeterministicContainersTest, only_multimap) {
  UnorderedMultiMap<int, int> map{{1, 42}};
  auto& entry = only(map);
  static_assert(std::is_same_v<decltype(entry), std::pair<const int, int>&>);
  entry.second = 23;
  EXPECT_EQ(1, entry.first);
  EXPECT_EQ(23, unordered_any(map)->second);
  EXPECT_EQ(&entry, &only(std::as_const(map)));
}

TEST_F(DeterministicContainersTest, only_ordinary_containers) {
  std::vector<int> vector{23};
  std::set<int> set{23};
  std::unordered_set<int> hash_set{23};
  std::map<int, int> map{{1, 23}};
  std::unordered_map<int, int> hash_map{{1, 23}};
  static_assert(std::is_same_v<decltype(only(vector)), int&>);
  static_assert(
      std::is_same_v<decltype(only(std::as_const(vector))), const int&>);
  auto check = [](auto& collection) {
    EXPECT_EQ(&*collection.begin(), &only(collection));
    EXPECT_EQ(&*collection.begin(), &only(std::as_const(collection)));
  };
  check(vector);
  check(set);
  check(hash_set);
  check(map);
  check(hash_map);
  only(vector) = 42;
  EXPECT_EQ(42, vector.front());
}

TEST_F(DeterministicContainersTest, only_rejects_wrong_size) {
  auto check = [](auto collection) {
    const auto message = "only requires exactly one element, got " +
                         std::to_string(collection.size());
    EXPECT_THAT([&] { only(collection); },
                ::testing::ThrowsMessage<RedexException>(
                    ::testing::HasSubstr(message)));
    EXPECT_THAT([&] { only(std::as_const(collection)); },
                ::testing::ThrowsMessage<RedexException>(
                    ::testing::HasSubstr(message)));
  };
  check(UnorderedSet<int>{});
  check(UnorderedSet<int>{23, 42});
  check(UnorderedMap<int, int>{});
  check(UnorderedMap<int, int>{{1, 23}, {2, 42}});
  check(UnorderedBag<int>{});
  check(UnorderedBag<int>{23, 23});
  check(UnorderedMultiMap<int, int>{});
  check(UnorderedMultiMap<int, int>{{1, 23}, {1, 42}});
  check(std::vector<int>{});
  check(std::vector<int>{23, 42});
  check(std::set<int>{});
  check(std::set<int>{23, 42});
  check(std::unordered_set<int>{});
  check(std::unordered_set<int>{23, 42});
}

TEST_F(DeterministicContainersTest, UnorderedIterable_map) {
  constexpr std::array<std::pair<int, int>, 2u> map_values{{{1, 42}, {2, 23}}};
  UnorderedMap<int, int> map{map_values[0], map_values[1]};
  std::vector<std::pair<int, int>> vec;
  for (auto& p : UnorderedIterable(map)) {
    vec.emplace_back(p);
  }
  EXPECT_THAT(vec, UnorderedElementsAreArray(map_values));
}

TEST_F(DeterministicContainersTest, UnorderedIterable_multimap) {
  constexpr std::array<std::pair<int, int>, 3u> map_values{
      {{1, 42}, {1, 45}, {2, 23}}};
  UnorderedMultiMap<int, int> map{map_values[0], map_values[1], map_values[2]};
  std::vector<std::pair<int, int>> vec;
  for (auto& p : UnorderedIterable(map)) {
    vec.emplace_back(p);
  }
  EXPECT_THAT(vec, UnorderedElementsAreArray(map_values));
}

TEST_F(DeterministicContainersTest, UnorderedIterable_set) {
  constexpr std::array<int, 2u> set_values{23, 42};
  UnorderedSet<int> set({set_values[0], set_values[1]});
  std::vector<int> vec;
  for (int a : UnorderedIterable(set)) {
    vec.push_back(a);
  }
  EXPECT_THAT(vec, UnorderedElementsAreArray(set_values));
}

TEST_F(DeterministicContainersTest, unordered_to_ordered_map) {
  constexpr std::array<std::pair<int, int>, 2u> map_values{{{1, 42}, {2, 23}}};
  UnorderedMap<int, int> map{map_values[0], map_values[1]};
  auto ordered = unordered_to_ordered(
      map, [](const auto& p, const auto& q) { return p.first < q.first; });
  EXPECT_THAT(ordered, ElementsAreArray(map_values));
}

TEST_F(DeterministicContainersTest, unordered_to_ordered_multimap) {
  constexpr std::array<std::pair<int, int>, 3u> map_values{
      {{1, 42}, {1, 45}, {2, 23}}};
  UnorderedMultiMap<int, int> map{map_values[0], map_values[1], map_values[2]};
  auto ordered = unordered_to_ordered(map, [](const auto& a, const auto& b) {
    return a.first == b.first ? a.second < b.second : a.first < b.first;
  });
  EXPECT_THAT(ordered, ElementsAreArray(map_values));
}

TEST_F(DeterministicContainersTest, unordered_to_ordered_set) {
  constexpr std::array<int, 5u> set_values{1, 3, 5, 7, 11};
  UnorderedSet<int> set{set_values[0], set_values[1], set_values[2],
                        set_values[3], set_values[4]};
  auto ordered = unordered_to_ordered(set, [](int a, int b) { return a < b; });
  EXPECT_THAT(ordered, ElementsAreArray(set_values));
}

TEST_F(DeterministicContainersTest, unordered_to_ordered_keys) {
  constexpr std::array<int, 2u> key_values{1, 2};
  UnorderedMap<int, int> map{{key_values[0], 42}, {key_values[1], 23}};
  auto keys = unordered_to_ordered_keys(map);
  EXPECT_THAT(keys, ElementsAreArray(key_values));
}

TEST_F(DeterministicContainersTest, unordered_to_ordered_keys_multimap) {
  constexpr std::array<int, 3u> key_values{1, 1, 2};
  UnorderedMultiMap<int, int> map{
      {key_values[0], 42}, {key_values[1], 45}, {key_values[2], 23}};
  auto keys = unordered_to_ordered_keys(map);
  EXPECT_THAT(keys, ElementsAreArray(key_values));
}

TEST_F(DeterministicContainersTest, unordered_accumulate) {
  UnorderedMap<int, int> map{{1, 42}, {2, 23}};
  auto sum = unordered_accumulate(
      map, 0, [](int a, const auto& p) { return a + p.second; });
  EXPECT_EQ(42 + 23, sum);
}

TEST_F(DeterministicContainersTest, unordered_accumulate_multimap) {
  UnorderedMultiMap<int, int> map{{1, 42}, {1, 45}, {2, 23}, {2, 25}};
  auto sum = unordered_accumulate(
      map, 0, [](int a, const auto& p) { return a + p.second; });
  EXPECT_EQ(42 + 45 + 23 + 25, sum);
}

TEST_F(DeterministicContainersTest, unordered_all_of) {
  UnorderedMap<int, int> map{{1, 42}, {2, 23}};
  EXPECT_TRUE(unordered_all_of(map, [](auto& p) { return p.second >= 23; }));
  EXPECT_FALSE(unordered_all_of(map, [](auto& p) { return p.second < 23; }));
}

TEST_F(DeterministicContainersTest, unordered_all_of_multimap) {
  UnorderedMultiMap<int, int> map{{1, 42}, {1, 23}, {2, 23}, {2, 25}};
  EXPECT_TRUE(unordered_all_of(map, [](auto& p) { return p.second >= 23; }));
  EXPECT_FALSE(unordered_all_of(map, [](auto& p) { return p.second < 23; }));
}

TEST_F(DeterministicContainersTest, unordered_any_of) {
  UnorderedMap<int, int> map{{1, 42}, {2, 23}};
  EXPECT_TRUE(unordered_any_of(map, [](auto& p) { return p.second >= 42; }));
  EXPECT_TRUE(unordered_any_of(map, [](auto& p) { return p.second < 42; }));
}

TEST_F(DeterministicContainersTest, unordered_any_of_multimap) {
  UnorderedMultiMap<int, int> map{{1, 42}, {1, 45}, {2, 23}, {2, 25}};
  EXPECT_TRUE(unordered_any_of(map, [](auto& p) { return p.second >= 42; }));
  EXPECT_TRUE(unordered_any_of(map, [](auto& p) { return p.second < 42; }));
}

TEST_F(DeterministicContainersTest, unordered_none_of) {
  UnorderedMap<int, int> map{{1, 42}, {2, 23}};
  EXPECT_FALSE(unordered_none_of(map, [](auto& p) { return p.second >= 23; }));
  EXPECT_TRUE(unordered_none_of(map, [](auto& p) { return p.second < 23; }));
  EXPECT_FALSE(unordered_none_of(map, [](auto& p) { return p.second >= 42; }));
  EXPECT_FALSE(unordered_none_of(map, [](auto& p) { return p.second < 42; }));
}

TEST_F(DeterministicContainersTest, unordered_none_of_multimap) {
  UnorderedMultiMap<int, int> map{{1, 42}, {1, 45}, {2, 23}, {2, 25}};
  EXPECT_FALSE(unordered_none_of(map, [](auto& p) { return p.second >= 23; }));
  EXPECT_TRUE(unordered_none_of(map, [](auto& p) { return p.second < 23; }));
  EXPECT_FALSE(unordered_none_of(map, [](auto& p) { return p.second >= 42; }));
  EXPECT_FALSE(unordered_none_of(map, [](auto& p) { return p.second < 42; }));
}

TEST_F(DeterministicContainersTest, unordered_for_each) {
  constexpr std::array<std::pair<int, int>, 2u> map_values{{{1, 42}, {2, 23}}};
  UnorderedMap<int, int> map{map_values[0], map_values[1]};
  UnorderedMap<int, int> copy;
  unordered_for_each(map, [&](auto& p) { copy.insert(p); });
  ASSERT_THAT(copy, SizeIs(2u));
  EXPECT_EQ(copy.at(map_values[0].first), map_values[0].second);
  EXPECT_EQ(copy.at(map_values[1].first), map_values[1].second);
}

TEST_F(DeterministicContainersTest, unordered_for_each_multimap) {
  constexpr std::array<std::pair<int, int>, 4u> map_values{
      {{1, 42}, {1, 45}, {2, 23}, {2, 25}}};
  UnorderedMultiMap<int, int> map{map_values[0], map_values[1], map_values[2],
                                  map_values[3]};
  UnorderedMultiMap<int, int> copy;
  unordered_for_each(map, [&](auto& p) { copy.insert(p); });
  ASSERT_THAT(copy, SizeIs(4u));
  auto iterator_key_1 = unordered_equal_range(copy, 1);
  const std::vector<std::pair<int, int>> key_1{iterator_key_1.first,
                                               iterator_key_1.second};
  EXPECT_THAT(key_1, UnorderedElementsAreArray({map_values[0], map_values[1]}));
  auto iterator_key_2 = unordered_equal_range(copy, 2);
  const std::vector<std::pair<int, int>> key_2{iterator_key_2.first,
                                               iterator_key_2.second};
  EXPECT_THAT(key_2, UnorderedElementsAreArray({map_values[2], map_values[3]}));
}

TEST_F(DeterministicContainersTest, unordered_copy) {
  constexpr std::array<std::pair<int, int>, 2u> map_values{{{1, 42}, {2, 23}}};
  UnorderedMap<int, int> map{map_values[0], map_values[1]};
  std::vector<std::pair<int, int>> copy(2);
  unordered_copy(map, copy.begin());
  EXPECT_THAT(copy, UnorderedElementsAreArray(map_values));
}

TEST_F(DeterministicContainersTest, unordered_copy_multimap) {
  constexpr std::array<std::pair<int, int>, 4u> map_values{
      {{1, 42}, {1, 45}, {2, 23}, {2, 25}}};
  UnorderedMultiMap<int, int> map{map_values[0], map_values[1], map_values[2],
                                  map_values[3]};
  std::vector<std::pair<int, int>> copy(4);
  unordered_copy(map, copy.begin());
  EXPECT_THAT(copy, UnorderedElementsAreArray(map_values));
}

TEST_F(DeterministicContainersTest, unordered_copy_if) {
  constexpr int threshold = 42;
  constexpr std::array<std::pair<int, int>, 1u> int_over_equal_threshold{
      {{1, 42}}};
  UnorderedMap<int, int> map{int_over_equal_threshold[0], {2, 23}};
  std::vector<std::pair<int, int>> copy(1);
  unordered_copy_if(map, copy.begin(),
                    [](auto& p) { return p.second >= threshold; });
  EXPECT_THAT(copy, UnorderedElementsAreArray(int_over_equal_threshold));
}

TEST_F(DeterministicContainersTest, unordered_copy_if_multimap) {
  constexpr int threshold = 42;
  constexpr std::array<std::pair<int, int>, 3u> int_over_equal_threshold{
      {{1, 42}, {1, 45}, {2, 55}}};
  UnorderedMultiMap<int, int> map{int_over_equal_threshold[0],
                                  int_over_equal_threshold[1],
                                  {1, 25},
                                  {2, 23},
                                  int_over_equal_threshold[2]};
  std::vector<std::pair<int, int>> copy(3);
  unordered_copy_if(map, copy.begin(),
                    [](auto& p) { return p.second >= threshold; });
  EXPECT_THAT(copy, UnorderedElementsAreArray(int_over_equal_threshold));
}

TEST_F(DeterministicContainersTest, unordered_erase_if) {
  constexpr int threshold = 42;
  UnorderedMap<int, int> map{{1, 42}, {2, 23}};
  unordered_erase_if(map, [](auto& p) { return p.second >= threshold; });
  ASSERT_THAT(map, SizeIs(1u));
  EXPECT_EQ(2, unordered_any(map)->first);
  EXPECT_EQ(23, unordered_any(map)->second);
}

TEST_F(DeterministicContainersTest, unordered_erase_if_multimap) {
  std::array<int, 3u> removed_values{42, 45, 25};
  UnorderedMultiMap<int, int> map{{1, removed_values[0]},
                                  {1, removed_values[1]},
                                  {2, 23},
                                  {2, removed_values[2]}};
  for (const int& value : removed_values) {
    unordered_erase_if(map, [&](auto& p) { return p.second == value; });
  }
  ASSERT_THAT(map, SizeIs(1u));
  EXPECT_EQ(2, unordered_any(map)->first);
  EXPECT_EQ(23, unordered_any(map)->second);
}

TEST_F(DeterministicContainersTest, unordered_transform) {
  UnorderedMap<int, int> map{{1, 42}, {2, 23}};
  constexpr std::array<std::pair<int, int>, 2u> transformed_values{
      {{1 + 1, 42 + 1}, {2 + 1, 23 + 1}}};
  std::vector<std::pair<int, int>> copy(2);
  unordered_transform(map, copy.begin(), [](auto& p) {
    return std::make_pair(p.first + 1, p.second + 1);
  });
  EXPECT_THAT(copy, UnorderedElementsAreArray(transformed_values));
}

TEST_F(DeterministicContainersTest, unordered_transform_multimap) {
  UnorderedMultiMap<int, int> map{{1, 42}, {1, 45}, {2, 23}, {2, 25}};
  constexpr std::array<std::pair<int, int>, 4u> transformed_values{
      {{1 + 1, 42 + 1}, {1 + 1, 45 + 1}, {2 + 1, 23 + 1}, {2 + 1, 25 + 1}}};
  std::vector<std::pair<int, int>> copy(4);
  unordered_transform(map, copy.begin(), [](auto& p) {
    return std::make_pair(p.first + 1, p.second + 1);
  });
  EXPECT_THAT(copy, UnorderedElementsAreArray(transformed_values));
}

TEST_F(DeterministicContainersTest, insert_unordered_iterable) {
  constexpr std::array<std::pair<int, int>, 2u> map_values{{{1, 42}, {2, 23}}};
  UnorderedMap<int, int> map{map_values[0], map_values[1]};
  UnorderedMap<int, int> copy;
  insert_unordered_iterable(copy, map);
  std::vector<std::pair<int, int>> copied_values;
  unordered_for_each(copy, [&](auto& p) { copied_values.push_back(p); });
  ASSERT_THAT(copy, SizeIs(2u));
  EXPECT_THAT(copied_values, UnorderedElementsAreArray(map_values));
}

TEST_F(DeterministicContainersTest, insert_unordered_iterable_multimap) {
  constexpr std::array<std::pair<int, int>, 4u> map_values{
      {{1, 42}, {1, 45}, {2, 23}, {2, 25}}};
  UnorderedMultiMap<int, int> map{map_values[0], map_values[1], map_values[2],
                                  map_values[3]};
  UnorderedMultiMap<int, int> copy;
  insert_unordered_iterable(copy, map);
  std::vector<std::pair<int, int>> copied_values;
  unordered_for_each(copy, [&](auto& p) { copied_values.push_back(p); });
  ASSERT_THAT(copy, SizeIs(4u));
  EXPECT_THAT(copied_values, UnorderedElementsAreArray(map_values));
}

TEST_F(DeterministicContainersTest, insert_unordered_iterable_vector) {
  constexpr std::array<int, 5u> set_values{{1, 11, 7, 3, 5}};
  UnorderedSet<int> set{set_values[0], set_values[1], set_values[2],
                        set_values[3], set_values[4]};
  std::vector<int> copy;
  insert_unordered_iterable(copy, copy.end(), set);
  EXPECT_THAT(copy, UnorderedElementsAreArray(set_values));
}

TEST_F(DeterministicContainersTest, unordered_min_element_set) {
  UnorderedSet<int> set{42, 23, 7, 11, 5};
  auto min = unordered_min_element(set);
  EXPECT_EQ(5, *min);
}

TEST_F(DeterministicContainersTest, unordered_min_element_map) {
  UnorderedMap<int, int> map{{1, 42}, {2, 23}, {3, 7}};
  auto min = unordered_min_element(
      map, [](const auto& a, const auto& b) { return a.second < b.second; });
  EXPECT_EQ(3, min->first);
  EXPECT_EQ(7, min->second);
}

TEST_F(DeterministicContainersTest, unordered_min_element_multimap) {
  UnorderedMultiMap<int, int> map{{1, 42}, {1, 45}, {2, 23}, {2, 25}, {3, 55}};
  auto min = unordered_min_element(
      map, [](const auto& a, const auto& b) { return a.second < b.second; });
  EXPECT_EQ(2, min->first);
  EXPECT_EQ(23, min->second);
}

TEST_F(DeterministicContainersTest, unordered_min_element_set_custom) {
  UnorderedSet<int> set{-5, 4, -3, 2, -1};
  auto min = unordered_min_element(
      set, [](int a, int b) { return std::abs(a) < std::abs(b); });
  EXPECT_EQ(-1, *min);
}

TEST_F(DeterministicContainersTest, unordered_min_element_map_custom) {
  UnorderedMap<std::string, int> map{{"abc", 1}, {"a", 2}, {"abcd", 3}};
  auto min = unordered_min_element(map, [](const auto& a, const auto& b) {
    return a.first.length() < b.first.length();
  });
  EXPECT_EQ("a", min->first);
  EXPECT_EQ(2, min->second);
}

TEST_F(DeterministicContainersTest, unordered_min_element_multimap_custom) {
  UnorderedMultiMap<std::string, int> map{
      {"abc", 1}, {"a", 5}, {"a", 2}, {"abcd", 3}};
  auto min = unordered_min_element(map, [](const auto& a, const auto& b) {
    return a.first.length() == b.first.length()
               ? a.second < b.second
               : a.first.length() < b.first.length();
  });
  EXPECT_EQ("a", min->first);
  EXPECT_EQ(2, min->second);
}

TEST_F(DeterministicContainersTest, unordered_max_element_set) {
  UnorderedSet<int> set{42, 23, 7, 11, 5};
  auto max = unordered_max_element(set);
  EXPECT_EQ(42, *max);
}

TEST_F(DeterministicContainersTest, unordered_max_element_map) {
  UnorderedMap<int, int> map{{1, 42}, {2, 23}, {3, 7}};
  auto max = unordered_max_element(
      map, [](const auto& a, const auto& b) { return a.second < b.second; });
  EXPECT_EQ(1, max->first);
  EXPECT_EQ(42, max->second);
}

TEST_F(DeterministicContainersTest, unordered_max_element_multimap) {
  UnorderedMultiMap<int, int> map{{1, 42}, {1, 45}, {2, 23}, {2, 25}};
  auto max = unordered_max_element(
      map, [](const auto& a, const auto& b) { return a.second < b.second; });
  EXPECT_EQ(1, max->first);
  EXPECT_EQ(45, max->second);
}

TEST_F(DeterministicContainersTest, unordered_max_element_set_custom) {
  UnorderedSet<int> set{-5, 4, -3, 2, -1};
  auto max = unordered_max_element(
      set, [](int a, int b) { return std::abs(a) < std::abs(b); });
  EXPECT_EQ(-5, *max);
}

TEST_F(DeterministicContainersTest, unordered_min_element_stdmap) {
  std::map<int, int> map{{1, 42}, {2, 23}, {3, 7}};
  auto min = unordered_min_element(
      map, [](const auto& a, const auto& b) { return a.second < b.second; });
  EXPECT_EQ(3, min->first);
  EXPECT_EQ(7, min->second);
}

TEST_F(DeterministicContainersTest, unordered_min_element_stdmap_custom) {
  std::map<std::string, int> map{{"abc", 1}, {"a", 2}, {"abcd", 3}};
  auto min = unordered_min_element(map, [](const auto& a, const auto& b) {
    return a.first.length() < b.first.length();
  });
  EXPECT_EQ("a", min->first);
  EXPECT_EQ(2, min->second);
}

TEST_F(DeterministicContainersTest, unordered_max_element_stdmap) {
  std::map<int, int> map{{1, 42}, {2, 23}, {3, 7}};
  auto max = unordered_max_element(
      map, [](const auto& a, const auto& b) { return a.second < b.second; });
  EXPECT_EQ(1, max->first);
  EXPECT_EQ(42, max->second);
}

TEST_F(DeterministicContainersTest, unordered_max_element_stdmap_custom) {
  std::map<std::string, int> map{{"abc", 1}, {"a", 2}, {"abcd", 3}};
  auto max = unordered_max_element(map, [](const auto& a, const auto& b) {
    return a.first.length() < b.first.length();
  });
  EXPECT_EQ("abcd", max->first);
  EXPECT_EQ(3, max->second);
}

TEST_F(DeterministicContainersTest, unordered_min_element_vector) {
  std::vector<int> vec{42, 23, 7, 11, 5};
  auto min = unordered_min_element(vec);
  EXPECT_EQ(5, *min);
}

TEST_F(DeterministicContainersTest, unordered_min_element_vector_custom) {
  std::vector<int> vec{-5, 4, -3, 2, -1};
  auto min = unordered_min_element(
      vec, [](int a, int b) { return std::abs(a) < std::abs(b); });
  EXPECT_EQ(-1, *min);
}

TEST_F(DeterministicContainersTest, unordered_max_element_vector) {
  std::vector<int> vec{42, 23, 7, 11, 5};
  auto max = unordered_max_element(vec);
  EXPECT_EQ(42, *max);
}

TEST_F(DeterministicContainersTest, unordered_max_element_vector_custom) {
  std::vector<int> vec{-5, 4, -3, 2, -1};
  auto max = unordered_max_element(
      vec, [](int a, int b) { return std::abs(a) < std::abs(b); });
  EXPECT_EQ(-5, *max);
}

TEST_F(DeterministicContainersTest, UnorderedBag_construction) {
  UnorderedBag<int> bag{1, 2, 3};
  ASSERT_THAT(bag, SizeIs(3u));
  EXPECT_FALSE(bag.empty());

  UnorderedBag<int> empty_bag;
  ASSERT_THAT(empty_bag, SizeIs(0u));
  EXPECT_TRUE(empty_bag.empty());
}

TEST_F(DeterministicContainersTest, UnorderedBag_basic_operations) {
  UnorderedBag<int> bag;
  EXPECT_TRUE(bag.empty());

  bag.emplace(42);
  ASSERT_THAT(bag, SizeIs(1u));
  EXPECT_FALSE(bag.empty());

  bag.emplace(23);
  ASSERT_THAT(bag, SizeIs(2u));

  bag.emplace(15);
  bag.emplace(7);
  ASSERT_THAT(bag, SizeIs(4u));
}

TEST_F(DeterministicContainersTest, UnorderedBag_unordered_any) {
  UnorderedBag<int> bag;
  bag.emplace(42);
  bag.emplace(23);
  auto any = *unordered_any(bag);
  EXPECT_TRUE(any == 42 || any == 23);

  UnorderedBag<int> empty_bag;
  EXPECT_EQ(empty_bag.end(), unordered_any(empty_bag));
}

TEST_F(DeterministicContainersTest, UnorderedBag_unordered_accumulate) {
  UnorderedBag<int> bag{1, 2, 3, 4, 5};
  int sum =
      unordered_accumulate(bag, 0, [](int acc, int val) { return acc + val; });
  EXPECT_EQ(15, sum);
}

TEST_F(DeterministicContainersTest, UnorderedBag_unordered_transform) {
  UnorderedBag<int> bag{1, 2, 3};
  constexpr std::array<int, 3u> transformed_values{1 * 2, 2 * 2, 3 * 2};
  std::vector<int> result(3);
  unordered_transform(bag, result.begin(), [](int val) { return val * 2; });
  EXPECT_THAT(result, UnorderedElementsAreArray(transformed_values));
}

TEST_F(DeterministicContainersTest, UnorderedBag_unordered_copy) {
  constexpr std::array<int, 4u> bag_values{1, 2, 3, 4};
  UnorderedBag<int> bag{bag_values[0], bag_values[1], bag_values[2],
                        bag_values[3]};
  std::vector<int> copy(4);
  unordered_copy(bag, copy.begin());
  EXPECT_THAT(copy, UnorderedElementsAreArray(bag_values));
}

TEST_F(DeterministicContainersTest, UnorderedBag_unordered_min_element) {
  UnorderedBag<int> bag{42, 23, 7, 11, 5};
  auto min = unordered_min_element(bag);
  EXPECT_EQ(5, *min);
}

TEST_F(DeterministicContainersTest, UnorderedBag_unordered_max_element) {
  UnorderedBag<int> bag{42, 23, 7, 11, 5};
  auto max = unordered_max_element(bag);
  EXPECT_EQ(42, *max);
}

TEST_F(DeterministicContainersTest, UnorderedBag_unordered_erase_if) {
  constexpr int threshold = 20;
  constexpr std::array<int, 3u> int_below_equal_threshold{5, 7, 11};
  UnorderedBag<int> bag{int_below_equal_threshold[0],
                        int_below_equal_threshold[1],
                        int_below_equal_threshold[2], 42, 23};
  std::vector<int> bag_values;
  unordered_erase_if(bag, [](int x) { return x > threshold; });
  unordered_for_each(bag, [&](auto& x) { bag_values.push_back(x); });
  ASSERT_THAT(bag, SizeIs(3u));
  EXPECT_THAT(bag_values, UnorderedElementsAreArray(int_below_equal_threshold));
}

TEST_F(DeterministicContainersTest, UnorderedBag_unordered_min_element_custom) {
  UnorderedBag<int> bag{-5, 4, -3, 2, -1};
  auto min = unordered_min_element(
      bag, [](int a, int b) { return std::abs(a) < std::abs(b); });
  EXPECT_EQ(-1, *min);
}

TEST_F(DeterministicContainersTest, UnorderedBag_unordered_max_element_custom) {
  UnorderedBag<int> bag{-5, 4, -3, 2, -1};
  auto max = unordered_max_element(
      bag, [](int a, int b) { return std::abs(a) < std::abs(b); });
  EXPECT_EQ(-5, *max);
}

TEST_F(DeterministicContainersTest, UnorderedBag_unordered_to_ordered) {
  UnorderedBag<int> bag{5, 2, 8, 1, 9, 3};
  auto ordered = unordered_to_ordered(bag, [](int a, int b) { return a < b; });
  EXPECT_EQ(std::vector<int>({1, 2, 3, 5, 8, 9}), ordered);
}

TEST_F(DeterministicContainersTest,
       UnorderedBag_unordered_erase_if_divisible_by_3) {
  UnorderedBag<int> bag{1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
  unordered_erase_if(bag, [](int x) { return x % 3 == 0; });
  ASSERT_THAT(bag, SizeIs(7u));
  auto ordered = unordered_to_ordered(bag, [](int a, int b) { return a < b; });
  EXPECT_THAT(ordered, ElementsAre(1, 2, 4, 5, 7, 8, 10))
      << "Output of unordered_to_ordered is expected to contain only integers "
         "that are within the range of 1 to 10 and not divisible by 3 in "
         "ascending order";
}

TEST_F(DeterministicContainersTest, unordered_find_map) {
  UnorderedMap<int, std::string> map{{1, "one"}, {2, "two"}, {3, "three"}};

  // Test finding an existing pair
  auto found = unordered_find(map, std::pair<const int, std::string>(2, "two"));
  EXPECT_NE(map.end(), found);
  EXPECT_EQ(2, found->first);
  EXPECT_EQ("two", found->second);

  // Test finding a non-existent pair (existing key, wrong value)
  auto not_found1 =
      unordered_find(map, std::pair<const int, std::string>(2, "three"));
  EXPECT_EQ(map.end(), not_found1);

  // Test finding a non-existent pair (non-existent key)
  auto not_found2 =
      unordered_find(map, std::pair<const int, std::string>(4, "four"));
  EXPECT_EQ(map.end(), not_found2);
}

TEST_F(DeterministicContainersTest, unordered_find_multimap) {
  UnorderedMultiMap<int, std::string> map{
      {1, "one"}, {1, "uno"}, {1, "une"}, {2, "two"}};

  // Test finding an existing pair
  auto found = unordered_find(map, std::pair<const int, std::string>(2, "two"));
  EXPECT_NE(map.end(), found);
  EXPECT_EQ(2, found->first);
  EXPECT_EQ("two", found->second);

  // Test finding a non-existent pair (existing key, wrong value)
  auto not_found1 =
      unordered_find(map, std::pair<const int, std::string>(2, "three"));
  EXPECT_EQ(map.end(), not_found1);

  // Test finding a non-existent pair (non-existent key)
  auto not_found2 =
      unordered_find(map, std::pair<const int, std::string>(4, "four"));
  EXPECT_EQ(map.end(), not_found2);
}

TEST_F(DeterministicContainersTest, unordered_find_set) {
  UnorderedSet<int> set{1, 2, 3, 4, 5};
  auto found = unordered_find(set, 3);
  EXPECT_NE(set.end(), found);
  EXPECT_EQ(3, *found);

  auto not_found = unordered_find(set, 6);
  EXPECT_EQ(set.end(), not_found);
}

TEST_F(DeterministicContainersTest, unordered_find_if_map) {
  UnorderedMap<int, int> map{{1, 10}, {2, 20}, {3, 30}};
  auto found =
      unordered_find_if(map, [](const auto& p) { return p.second > 25; });
  EXPECT_NE(map.end(), found);
  EXPECT_EQ(30, found->second);

  auto not_found =
      unordered_find_if(map, [](const auto& p) { return p.second > 50; });
  EXPECT_EQ(map.end(), not_found);
}

TEST_F(DeterministicContainersTest, unordered_find_if_multimap) {
  UnorderedMultiMap<int, int> map{{1, 42}, {1, 45}, {2, 23}, {2, 25}};
  auto found =
      unordered_find_if(map, [](const auto& p) { return p.second == 25; });
  EXPECT_NE(map.end(), found);
  EXPECT_EQ(2, found->first);
  EXPECT_EQ(25, found->second);

  auto not_found =
      unordered_find_if(map, [](const auto& p) { return p.second > 50; });
  EXPECT_EQ(map.end(), not_found);
}

TEST_F(DeterministicContainersTest, unordered_find_if_set) {
  UnorderedSet<int> set{1, 2, 3, 4, 5};
  auto found = unordered_find_if(set, [](int x) { return x > 3; });
  EXPECT_NE(set.end(), found);
  EXPECT_TRUE(*found == 4 || *found == 5);

  auto not_found = unordered_find_if(set, [](int x) { return x > 10; });
  EXPECT_EQ(set.end(), not_found);
}

TEST_F(DeterministicContainersTest, unordered_find_if_not_map) {
  UnorderedMap<int, int> map{{1, 10}, {2, 20}, {3, 30}};
  auto found =
      unordered_find_if_not(map, [](const auto& p) { return p.second > 25; });
  EXPECT_NE(map.end(), found);
  EXPECT_TRUE(found->second <= 25);

  auto not_found =
      unordered_find_if_not(map, [](const auto& p) { return p.second > 0; });
  EXPECT_EQ(map.end(), not_found);
}

TEST_F(DeterministicContainersTest, unordered_find_if_not_multimap) {
  UnorderedMultiMap<int, int> map{{1, 42}, {1, 45}, {2, 23}, {2, 25}};
  auto found =
      unordered_find_if_not(map, [](const auto& p) { return p.second > 24; });
  EXPECT_NE(map.end(), found);
  EXPECT_EQ(2, found->first);
  EXPECT_TRUE(found->second <= 23);

  auto not_found =
      unordered_find_if_not(map, [](const auto& p) { return p.second > 0; });
  EXPECT_EQ(map.end(), not_found);
}

TEST_F(DeterministicContainersTest, unordered_find_if_not_set) {
  UnorderedSet<int> set{1, 2, 3, 4, 5};
  auto found = unordered_find_if_not(set, [](int x) { return x > 3; });
  EXPECT_NE(set.end(), found);
  EXPECT_TRUE(*found <= 3);

  auto not_found = unordered_find_if_not(set, [](int x) { return x > 0; });
  EXPECT_EQ(set.end(), not_found);
}

TEST_F(DeterministicContainersTest, unordered_multimap_equal_range) {
  UnorderedMultiMap<int, std::string> map{
      {1, "one"}, {1, "uno"}, {1, "une"}, {2, "two"}};
  auto range = map.equal_range(1);
  EXPECT_NE(range.first, range.second);

  auto empty_range = map.equal_range(3);
  EXPECT_EQ(empty_range.first, empty_range.second);
}

TEST_F(DeterministicContainersTest, unordered_multimap_unordered_equal_range) {
  UnorderedMultiMap<int, std::string> map{
      {1, "one"}, {1, "uno"}, {1, "une"}, {2, "two"}};
  auto range = unordered_equal_range(map, 1);
  std::vector<std::string> values;
  for (auto it = range.first; it != range.second; ++it) {
    values.push_back(it->second);
  }
  ASSERT_THAT(values, UnorderedElementsAre("one", "une", "uno"));

  auto empty_range = unordered_equal_range(map, 3);
  EXPECT_EQ(empty_range.first, empty_range.second);
}

TEST_F(DeterministicContainersTest,
       unordered_for_each_returns_applied_functor) {
  UnorderedSet<int> set{1, 2, 3, 4, 5};
  struct Sum {
    int total = 0;
    void operator()(int x) { total += x; }
  };
  // std::for_each accumulates state in the functor it returns; the helper must
  // forward that object rather than the moved-from original.
  auto result = unordered_for_each(set, Sum{});
  EXPECT_EQ(1 + 2 + 3 + 4 + 5, result.total);
}

TEST_F(DeterministicContainersTest, UnorderedMap_insert_with_hint) {
  UnorderedMap<int, std::string> map{{1, "one"}};
  // rvalue-pair hint overload returns a FixedIterator to the inserted element;
  // mutable end() is accepted as the hint (implicit FixedIterator ->
  // ConstFixedIterator conversion).
  auto it_rvalue = map.insert(map.end(), std::pair<int, std::string>{2, "two"});
  EXPECT_EQ(2, it_rvalue->first);
  EXPECT_EQ("two", it_rvalue->second);
  // forwarding (P&&) template hint overload: the arg type
  // (pair<int, const char*>) differs from value_type, so the template overload
  // is strictly the best match (the non-template pair&& one would need a
  // conversion).
  auto it_fwd = map.insert(map.end(), std::make_pair(3, "three"));
  EXPECT_EQ(3, it_fwd->first);
  EXPECT_EQ("three", it_fwd->second);
  // const-lvalue hint overload
  const std::pair<int, std::string> value{4, "four"};
  auto it_const = map.insert(map.end(), value);
  EXPECT_EQ(4, it_const->first);
  ASSERT_THAT(map, SizeIs(4u));
}

TEST_F(DeterministicContainersTest, UnorderedMultiMap_insert_with_hint) {
  UnorderedMultiMap<int, std::string> map{{1, "one"}};
  auto it = map.insert(map.end(), std::pair<int, std::string>{1, "uno"});
  EXPECT_EQ(1, it->first);
  ASSERT_THAT(map, SizeIs(2u));
  EXPECT_EQ(2u, map.count(1));
}

TEST_F(DeterministicContainersTest, UnorderedMap_insert_initializer_list) {
  UnorderedMap<int, int> map;
  map.insert({{1, 10}, {2, 20}});
  ASSERT_THAT(map, SizeIs(2u));
  EXPECT_EQ(10, map.at(1));
  EXPECT_EQ(20, map.at(2));
}

TEST_F(DeterministicContainersTest, UnorderedMultiMap_insert_initializer_list) {
  UnorderedMultiMap<int, int> map;
  map.insert({{1, 10}, {1, 11}, {2, 20}});
  ASSERT_THAT(map, SizeIs(3u));
  EXPECT_EQ(2u, map.count(1));
  EXPECT_EQ(1u, map.count(2));
}

TEST_F(DeterministicContainersTest, UnorderedSet_contains_present_key_is_true) {
  const UnorderedSet<int> set{1, 2, 3};
  EXPECT_TRUE(set.contains(2));
}

TEST_F(DeterministicContainersTest, UnorderedSet_contains_absent_key_is_false) {
  const UnorderedSet<int> set{1, 2, 3};
  EXPECT_FALSE(set.contains(4));
}

TEST_F(DeterministicContainersTest, unordered_equal_bag_hashing_form) {
  UnorderedBag<int> a{1, 2, 3};
  UnorderedBag<int> same_other_order{3, 1, 2};
  UnorderedBag<int> different_element{1, 2, 4};
  UnorderedBag<int> different_size{1, 2};
  EXPECT_TRUE(unordered_equal(a, same_other_order));
  EXPECT_FALSE(unordered_equal(a, different_element));
  EXPECT_FALSE(unordered_equal(a, different_size));
  // Multiset semantics: same elements and size but different multiplicities.
  UnorderedBag<int> two_ones{1, 1, 2};
  UnorderedBag<int> two_twos{1, 2, 2};
  EXPECT_FALSE(unordered_equal(two_ones, two_twos));
}

TEST_F(DeterministicContainersTest, unordered_equal_comparator_form) {
  UnorderedBag<int> a{1, 2, 3};
  UnorderedBag<int> same_other_order{3, 1, 2};
  UnorderedBag<int> different_element{1, 2, 4};
  auto less = [](int x, int y) { return x < y; };
  EXPECT_TRUE(unordered_equal(a, same_other_order, less));
  EXPECT_FALSE(unordered_equal(a, different_element, less));
}

TEST_F(DeterministicContainersTest, unordered_equal_generic_over_set) {
  UnorderedSet<int> a{1, 2, 3};
  UnorderedSet<int> b{3, 2, 1};
  UnorderedSet<int> c{1, 2, 4};
  EXPECT_TRUE(unordered_equal(a, b));
  EXPECT_FALSE(unordered_equal(a, c));
}

TEST_F(DeterministicContainersTest, unordered_equal_generic_over_map) {
  // Maps use the associative fast-path (native order-independent operator==);
  // their element type isn't hashable, so the default form must not go through
  // the hashing path.
  UnorderedMap<int, int> a{{1, 10}, {2, 20}};
  UnorderedMap<int, int> same_other_order{{2, 20}, {1, 10}};
  UnorderedMap<int, int> different_value{{1, 10}, {2, 21}};
  EXPECT_TRUE(unordered_equal(a, same_other_order));
  EXPECT_FALSE(unordered_equal(a, different_value));
}

TEST_F(DeterministicContainersTest, UnorderedEqual_functor) {
  UnorderedBag<int> a{1, 2, 3};
  UnorderedBag<int> same_other_order{3, 1, 2};
  UnorderedBag<int> different_element{1, 2, 4};
  // Default (hashing) form, usable as a default-constructible ValueEqual.
  UnorderedEqual<UnorderedBag<int>> equal;
  EXPECT_TRUE(equal(a, same_other_order));
  EXPECT_FALSE(equal(a, different_element));
  // Comparator form via the second template parameter.
  UnorderedEqual<UnorderedBag<int>, std::less<int>> equal_by;
  EXPECT_TRUE(equal_by(a, same_other_order));
  EXPECT_FALSE(equal_by(a, different_element));
}

// --- Perturbation (REDEX_PERTURB_UNORDERED) ----------------------------------

#if !REDEX_PERTURB_UNORDERED
// With perturbation OFF the wrappers must be byte-identical to plain std: the
// effective hasher is exactly the template Hash (zero-cost).
static_assert(std::is_same_v<EffectiveHash_t<std::hash<int>>, std::hash<int>>,
              "perturb OFF must leave EffectiveHash_t equal to the plain Hash");
#endif

// The internal hasher may be salted (a different salt per container), but
// set/map equality must stay order- and salt-independent. This is the
// regression that catches a dropped `noexcept` on PerturbHasher::operator()
// (which would let libstdc++ cache salted hash codes and break cross-container
// ==).
TEST_F(DeterministicContainersTest, perturb_cross_container_equality) {
  UnorderedMap<int, int> a;
  UnorderedMap<int, int> b;
  for (int i = 0; i < 64; i++) {
    a.emplace(i, i * 2);
    b.emplace(i, i * 2);
  }
  EXPECT_TRUE(a == b);

  UnorderedSet<std::string> s1;
  UnorderedSet<std::string> s2;
  for (int i = 0; i < 64; i++) {
    s1.insert("k" + std::to_string(i));
    s2.insert("k" + std::to_string(i));
  }
  EXPECT_TRUE(s1 == s2);

  b.emplace(999, 1);
  EXPECT_TRUE(a != b);
}

// REDEX_PERTURB_SEED, when set, is parsed verbatim (base 0: decimal and 0x-hex)
// and used as the salt-stream base seed, dropping the thread-id term so a
// single-threaded run is reproducible.
TEST_F(DeterministicContainersTest, perturb_seed_env_is_honored) {
  ::setenv("REDEX_PERTURB_SEED", "0x1234", /* overwrite */ 1);
  EXPECT_EQ(det_perturb::perturb_base_seed(), 0x1234u);
  ::setenv("REDEX_PERTURB_SEED", "42", /* overwrite */ 1);
  EXPECT_EQ(det_perturb::perturb_base_seed(), 42u);
  ::unsetenv("REDEX_PERTURB_SEED");
}

// Guardrail for the perturbation CI job: REDEX_PERTURB_ASSERT_ON is set via a
// config independent of redex.perturb_unordered, so if the perturb mode is ever
// dropped from the job this fails to compile rather than silently testing
// perturbation OFF.
#ifndef REDEX_PERTURB_ASSERT_ON
#define REDEX_PERTURB_ASSERT_ON 0
#endif
#if REDEX_PERTURB_ASSERT_ON
static_assert(kPerturbUnordered,
              "REDEX_PERTURB_ASSERT_ON is set but perturbation is OFF: the "
              "redex.perturb_unordered wiring was dropped from the CI job");
#endif

#if REDEX_PERTURB_UNORDERED
// With perturbation ON, two independently-constructed containers holding the
// same elements iterate in different orders (per-container salt) while still
// comparing equal.
TEST_F(DeterministicContainersTest, perturb_on_scrambles_order_per_container) {
  auto iteration_order = [](const UnorderedSet<int>& s) {
    std::vector<int> v;
    for (int x : UnorderedIterable(s)) {
      v.push_back(x);
    }
    return v;
  };
  UnorderedSet<int> a;
  UnorderedSet<int> b;
  for (int i = 0; i < 64; i++) {
    a.insert(i);
    b.insert(i);
  }
  EXPECT_TRUE(a == b);
  EXPECT_NE(iteration_order(a), iteration_order(b));
}

// A bag has no hasher to salt, so it carries its own per-bag salt:
// unordered_any is no longer pinned to the first inserted element.
TEST_F(DeterministicContainersTest, perturb_on_bag_unordered_any_varies) {
  bool saw_non_first = false;
  for (int t = 0; t < 100 && !saw_non_first; t++) {
    UnorderedBag<int> bag;
    for (int i = 0; i < 64; i++) {
      bag.insert(i);
    }
    if (*unordered_any(bag) != 0) {
      saw_non_first = true;
    }
  }
  EXPECT_TRUE(saw_non_first);
}

// The full bag iteration (UnorderedIterable) is perturbed via a per-bag salted
// rotation: every element is still visited exactly once, but starting from a
// salted offset, so at least some bags iterate in a non-insertion order.
TEST_F(DeterministicContainersTest, perturb_on_bag_iteration_rotates) {
  std::vector<int> inserted;
  for (int i = 0; i < 64; i++) {
    inserted.push_back(i);
  }
  bool saw_rotation = false;
  for (int t = 0; t < 100 && !saw_rotation; t++) {
    UnorderedBag<int> bag;
    for (int i : inserted) {
      bag.insert(i);
    }
    std::vector<int> order;
    for (int x : UnorderedIterable(bag)) {
      order.push_back(x);
    }
    EXPECT_THAT(order, UnorderedElementsAreArray(inserted));
    if (order != inserted) {
      saw_rotation = true;
    }
  }
  EXPECT_TRUE(saw_rotation);
}

// The rotated (forward-only) bag view must not break the single-pass helpers:
// find locates the right element, a miss maps back to end(), and min/max are
// still correct.
TEST_F(DeterministicContainersTest,
       perturb_on_bag_helpers_correct_under_rotation) {
  UnorderedBag<int> bag;
  for (int i = 0; i < 64; i++) {
    bag.insert(i);
  }
  auto it = unordered_find(bag, 37);
  ASSERT_TRUE(it != bag.end());
  EXPECT_EQ(*it, 37);
  EXPECT_TRUE(unordered_find(bag, 999) == bag.end());
  EXPECT_EQ(*unordered_min_element(bag), 0);
  EXPECT_EQ(*unordered_max_element(bag), 63);
}
#endif
