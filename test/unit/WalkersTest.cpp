/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "Walkers.h"

#include <mutex>

#include <gmock/gmock.h>

#include "Creators.h"
#include "DexAnnotation.h"
#include "RedexTest.h"
#include "Show.h"

struct WalkersTest : public RedexTest {};

TEST_F(WalkersTest, accumlate) {
  ClassCreator cc(DexType::make_type("LFoo;"));
  cc.set_super(type::java_lang_Object());
  cc.add_method(DexMethod::make_method("LFoo;.bar:()V")
                    ->make_concrete(ACC_PUBLIC | ACC_STATIC, false));
  cc.add_method(DexMethod::make_method("LFoo;.baz:()V")
                    ->make_concrete(ACC_PUBLIC | ACC_STATIC, false));
  cc.add_method(DexMethod::make_method("LFoo;.qux:()V")
                    ->make_concrete(ACC_PUBLIC | ACC_STATIC, false));
  cc.add_method(DexMethod::make_method("LFoo;.quux:()V")
                    ->make_concrete(ACC_PUBLIC | ACC_STATIC, false));

  using StringSet = std::unordered_set<std::string>;
  constexpr size_t num_threads = 2;
  Scope scope{cc.create()};
  auto strings = walk::parallel::methods<StringSet, MergeContainers<StringSet>>(
      scope, [&](DexMethod* m) { return StringSet{show(m)}; }, num_threads);
  EXPECT_THAT(strings,
              ::testing::UnorderedElementsAre("LFoo;.bar:()V", "LFoo;.baz:()V",
                                              "LFoo;.qux:()V",
                                              "LFoo;.quux:()V"));
}

// A non-identity `init` must be folded in exactly once, whatever the thread
// count. Seeding the per-thread slots with `init` instead of the identity
// folds it once per thread plus once at the end, which makes the result vary
// with the host's core count.
TEST_F(WalkersTest, accumulate_with_init_is_thread_count_independent) {
  ClassCreator cc(DexType::make_type("LInit;"));
  cc.set_super(type::java_lang_Object());
  cc.add_method(DexMethod::make_method("LInit;.a:()V")
                    ->make_concrete(ACC_PUBLIC | ACC_STATIC, false));
  cc.add_method(DexMethod::make_method("LInit;.b:()V")
                    ->make_concrete(ACC_PUBLIC | ACC_STATIC, false));
  cc.add_method(DexMethod::make_method("LInit;.c:()V")
                    ->make_concrete(ACC_PUBLIC | ACC_STATIC, false));

  Scope scope{cc.create()};
  constexpr size_t kInit = 100;
  for (size_t num_threads : {size_t(1), size_t(2), size_t(8)}) {
    auto sum = walk::parallel::methods<size_t>(
        scope, [](DexMethod*) { return size_t(1); }, num_threads, kInit);
    EXPECT_EQ(sum, kInit + 3) << "methods, " << num_threads << " threads";

    // The `classes` overload seeds its slots the same way.
    auto class_sum = walk::parallel::classes<size_t>(
        scope, [](DexClass*) { return size_t(1); }, num_threads, kInit);
    EXPECT_EQ(class_sum, kInit + 1) << "classes, " << num_threads << " threads";

    // A non-arithmetic Accumulator with a non-trivial identity: the empty set.
    using StringSet = std::unordered_set<std::string>;
    StringSet seed{"seed"};
    auto merged =
        walk::parallel::methods<StringSet, MergeContainers<StringSet>>(
            scope, [](DexMethod* m) { return StringSet{show(m)}; }, num_threads,
            seed);
    EXPECT_EQ(merged.size(), 4u) << "merge, " << num_threads << " threads";
    EXPECT_EQ(merged.count("seed"), 1u);
  }
}

namespace {

std::unique_ptr<DexAnnotationSet> make_annotation_set(const char* marker) {
  auto annotation = std::make_unique<DexAnnotation>(
      DexType::make_type("LAnno;"), DAV_RUNTIME);
  annotation->add_element(
      "value",
      std::make_unique<DexEncodedValueString>(DexString::make_string(marker)));
  auto annotation_set = std::make_unique<DexAnnotationSet>();
  annotation_set->add_annotation(std::move(annotation));
  return annotation_set;
}

} // namespace

// Every static field value and every annotation of a class, its fields, its
// methods and their parameters is visited once.
TEST_F(WalkersTest, encoded_values) {
  ClassCreator cc(DexType::make_type("LValues;"));
  cc.set_super(type::java_lang_Object());
  cc.add_field(DexField::make_field("LValues;.with_value:Ljava/lang/String;")
                   ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL,
                                   std::make_unique<DexEncodedValueString>(
                                       DexString::make_string("static"))));
  cc.add_field(DexField::make_field("LValues;.zero_value:I")
                   ->make_concrete(ACC_PUBLIC | ACC_STATIC));
  auto* field = DexField::make_field("LValues;.instance:I")
                    ->make_concrete(ACC_PUBLIC | ACC_SYNTHETIC);
  ASSERT_TRUE(field->attach_annotation_set(make_annotation_set("field")));
  cc.add_field(field);
  auto* method =
      DexMethod::make_method("LValues;.m:(I)V")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_SYNTHETIC, false);
  ASSERT_TRUE(method->attach_annotation_set(make_annotation_set("method")));
  method->attach_param_annotation_set(0, make_annotation_set("parameter"));
  cc.add_method(method);
  auto* cls = cc.create();
  ASSERT_TRUE(cls->attach_annotation_set(make_annotation_set("class")));

  std::mutex mutex;
  std::vector<std::string> strings;
  walk::parallel::encoded_values(Scope{cls}, [&](const Gatherable& value) {
    std::vector<const DexString*> value_strings;
    value.gather_strings(value_strings);
    std::lock_guard<std::mutex> lock(mutex);
    for (const auto* string : value_strings) {
      if (string->str() != "value") {
        strings.emplace_back(string->str());
      }
    }
  });
  EXPECT_THAT(strings,
              ::testing::UnorderedElementsAre("static", "field", "method",
                                              "parameter", "class"));
}
