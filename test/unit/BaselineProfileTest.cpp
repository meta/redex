/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include <sstream>

#include "BaselineProfile.h"
#include "ConfigFiles.h"
#include "ControlFlow.h"
#include "Creators.h"
#include "DexAnnotation.h"
#include "GlobalConfig.h"
#include "IRAssembler.h"
#include "RedexTest.h"
#include "Show.h"
#include "TypeUtil.h"

namespace bp = baseline_profiles;

namespace {

// A body of exactly `code_units` 2-byte code units: `nop` and `return-void`
// are one each.
std::string body_with_code_units(uint32_t code_units) {
  always_assert(code_units >= 1);
  std::ostringstream ss;
  ss << "(";
  for (uint32_t i = 1; i < code_units; ++i) {
    ss << "(nop)";
  }
  ss << "(return-void))";
  return ss.str();
}

} // namespace

class BaselineProfileTest : public RedexTest {
 public:
  // Creates `LC<n>;` holding a single method, so each method under test gets
  // its own class and the scope stays easy to read.
  DexMethod* create_method(const std::string& name,
                           DexAccessFlags access,
                           uint32_t code_units,
                           bool never_compile = false) {
    auto type_name = "LC" + std::to_string(m_classes.size()) + ";";
    ClassCreator creator(DexType::make_type(type_name));
    creator.set_super(type::java_lang_Object());

    auto* method = dynamic_cast<DexMethod*>(
        DexMethod::make_method(type_name + "." + name + ":()V"));
    always_assert(method != nullptr);
    if (never_compile) {
      // attach_annotation_set rejects a method that is already concrete.
      method->set_access(access);
      auto anno_set = std::make_unique<DexAnnotationSet>();
      anno_set->add_annotation(std::make_unique<DexAnnotation>(
          type::dalvik_annotation_optimization_NeverCompile(),
          DexAnnotationVisibility::DAV_BUILD));
      always_assert(method->attach_annotation_set(std::move(anno_set)));
    }
    // The access flags have to be read from the argument: the method is not a
    // def yet, so is_static() and friends would assert.
    bool is_virtual =
        (access & (ACC_STATIC | ACC_CONSTRUCTOR | ACC_PRIVATE)) == 0;
    method->make_concrete(access, is_virtual);
    if (code_units > 0) {
      method->set_code(
          assembler::ircode_from_string(body_with_code_units(code_units)));
      method->get_code()->build_cfg();
    }
    method->set_deobfuscated_name(show(method));

    creator.add_method(method);
    m_classes.push_back(creator.create());
    return method;
  }

  // A one-code-unit method that hands back a reference instead of returning
  // void, which is the shape the return-kind ranking key has to separate.
  DexMethod* create_object_returning_method(const std::string& name) {
    auto type_name = "LC" + std::to_string(m_classes.size()) + ";";
    ClassCreator creator(DexType::make_type(type_name));
    creator.set_super(type::java_lang_Object());

    auto* method =
        DexMethod::make_method(type_name + "." + name + ":()Ljava/lang/Object;")
            ->make_concrete(ACC_PUBLIC, /* is_virtual */ true);
    method->set_code(assembler::ircode_from_string("((return-object v0))"));
    method->get_code()->build_cfg();
    method->set_deobfuscated_name(show(method));

    creator.add_method(method);
    m_classes.push_back(creator.create());
    return method;
  }

  // Puts every method in one class, so deobfuscated-name ordering is the
  // method-name ordering and is decoupled from creation order. `sizes` is
  // parallel to `names`.
  void create_methods_in_one_class(const std::vector<std::string>& names,
                                   const std::vector<uint32_t>& sizes) {
    always_assert(names.size() == sizes.size());
    ClassCreator creator(DexType::make_type("LMulti;"));
    creator.set_super(type::java_lang_Object());
    for (size_t i = 0; i < names.size(); ++i) {
      auto* method = DexMethod::make_method("LMulti;." + names[i] + ":()V")
                         ->make_concrete(ACC_PUBLIC, /* is_virtual */ true);
      method->set_code(
          assembler::ircode_from_string(body_with_code_units(sizes[i])));
      method->get_code()->build_cfg();
      method->set_deobfuscated_name(show(method));
      creator.add_method(method);
    }
    m_classes.push_back(creator.create());
  }

  const Scope& scope() const { return m_classes; }

 private:
  Scope m_classes;
};

// ---------------------------------------------------------------------------
// uncompilable_reason: one test per gate dex2oat applies.
// ---------------------------------------------------------------------------

TEST_F(BaselineProfileTest, plain_method_is_compilable) {
  auto* m = create_method("plain", ACC_PUBLIC, /* code_units */ 4);
  EXPECT_EQ(bp::uncompilable_reason(m, bp::DEFAULT_ART_HUGE_METHOD_MAX),
            bp::UncompilableReason::kNone);
}

TEST_F(BaselineProfileTest, abstract_method_has_no_code) {
  auto* m = create_method("abs", ACC_PUBLIC | ACC_ABSTRACT, /* none */ 0);
  EXPECT_EQ(bp::uncompilable_reason(m, bp::DEFAULT_ART_HUGE_METHOD_MAX),
            bp::UncompilableReason::kNoCode);
}

TEST_F(BaselineProfileTest, native_method_has_no_code) {
  auto* m = create_method("nat", ACC_PUBLIC | ACC_NATIVE, /* none */ 0);
  EXPECT_EQ(bp::uncompilable_reason(m, bp::DEFAULT_ART_HUGE_METHOD_MAX),
            bp::UncompilableReason::kNoCode);
}

TEST_F(BaselineProfileTest, static_constructor_is_clinit) {
  auto* m = create_method("<clinit>", ACC_STATIC | ACC_CONSTRUCTOR, 4);
  EXPECT_EQ(bp::uncompilable_reason(m, bp::DEFAULT_ART_HUGE_METHOD_MAX),
            bp::UncompilableReason::kClinit);
}

// dex2oat's gate is ACC_CONSTRUCTOR *and* ACC_STATIC. An instance constructor
// carries ACC_CONSTRUCTOR alone and is compiled normally. Instance
// constructors are a large fraction of a real profile, so a gate that keyed on
// ACC_CONSTRUCTOR would silently throw them away.
TEST_F(BaselineProfileTest, instance_constructor_is_compilable) {
  auto* m = create_method("<init>", ACC_PUBLIC | ACC_CONSTRUCTOR, 4);
  EXPECT_EQ(bp::uncompilable_reason(m, bp::DEFAULT_ART_HUGE_METHOD_MAX),
            bp::UncompilableReason::kNone);
}

TEST_F(BaselineProfileTest, never_compile_annotation_is_honored) {
  auto* m = create_method("nc", ACC_PUBLIC, 4, /* never_compile */ true);
  EXPECT_EQ(bp::uncompilable_reason(m, bp::DEFAULT_ART_HUGE_METHOD_MAX),
            bp::UncompilableReason::kNeverCompile);
}

// ART's IsHugeMethod is a strict `>`, so a method sitting exactly on the
// threshold still compiles.
TEST_F(BaselineProfileTest, huge_method_gate_is_strictly_greater_than) {
  auto* at_limit = create_method("at_limit", ACC_PUBLIC, 10);
  auto* over_limit = create_method("over_limit", ACC_PUBLIC, 11);

  EXPECT_EQ(bp::uncompilable_reason(at_limit, /* huge_method_max */ 10),
            bp::UncompilableReason::kNone);
  EXPECT_EQ(bp::uncompilable_reason(over_limit, /* huge_method_max */ 10),
            bp::UncompilableReason::kHugeMethod);
  // The same method passes once the gate is raised above it.
  EXPECT_EQ(bp::uncompilable_reason(over_limit, /* huge_method_max */ 11),
            bp::UncompilableReason::kNone);
}

// Pins the constant the gate defaults to. ART's kDefaultHugeMethodThreshold is
// 10000; Redex's unrelated assessments::HUGE_METHOD_THRESHOLD is 9000, and
// reaching for that one instead would strip methods dex2oat compiles fine.
TEST_F(BaselineProfileTest, global_huge_method_max) {
  ConfigFiles unparsed(Json::nullValue);
  EXPECT_EQ(bp::get_huge_method_max(unparsed), bp::DEFAULT_ART_HUGE_METHOD_MAX);

  ConfigFiles defaults(Json::nullValue);
  defaults.parse_global_config();
  EXPECT_EQ(bp::get_huge_method_max(defaults), bp::DEFAULT_ART_HUGE_METHOD_MAX);

  Json::Value json;
  json["dex2oat"]["huge_method_max"] = 123;
  ConfigFiles overridden(json);
  overridden.parse_global_config();
  EXPECT_EQ(bp::get_huge_method_max(overridden), 123);
}

TEST_F(BaselineProfileTest, default_huge_method_max_matches_art) {
  EXPECT_EQ(bp::DEFAULT_ART_HUGE_METHOD_MAX, 10000u);

  auto* under = create_method("under", ACC_PUBLIC, 10000);
  auto* over = create_method("over", ACC_PUBLIC, 10001);
  EXPECT_EQ(bp::uncompilable_reason(under, bp::DEFAULT_ART_HUGE_METHOD_MAX),
            bp::UncompilableReason::kNone);
  EXPECT_EQ(bp::uncompilable_reason(over, bp::DEFAULT_ART_HUGE_METHOD_MAX),
            bp::UncompilableReason::kHugeMethod);
}

// ---------------------------------------------------------------------------
// flags_request_compilation
// ---------------------------------------------------------------------------

TEST_F(BaselineProfileTest, flags_request_compilation_matches_art_gate) {
  auto flags = [](bool hot, bool startup, bool post_startup) {
    bp::MethodFlags f;
    f.hot = hot;
    f.startup = startup;
    f.post_startup = post_startup;
    return f;
  };
  // IsHotMethod() || (!IsLowMemoryMode() && IsStartupMethod())
  EXPECT_TRUE(bp::flags_request_compilation(flags(true, false, false)));
  EXPECT_TRUE(bp::flags_request_compilation(flags(false, true, false)));
  EXPECT_TRUE(bp::flags_request_compilation(flags(true, true, true)));
  // Post-startup alone is never compiled anywhere.
  EXPECT_FALSE(bp::flags_request_compilation(flags(false, false, true)));
  EXPECT_FALSE(bp::flags_request_compilation(flags(false, false, false)));
}

// ---------------------------------------------------------------------------
// select_smallest_topoff_methods
// ---------------------------------------------------------------------------

namespace {

std::vector<std::string> names_of(const std::vector<DexMethod*>& methods) {
  std::vector<std::string> names;
  names.reserve(methods.size());
  for (auto* m : methods) {
    names.push_back(show_deobfuscated(m));
  }
  std::sort(names.begin(), names.end());
  return names;
}

} // namespace

// Size decides, and it outranks the name tie-break: the two selected here are
// the two that sort LAST by name.
TEST_F(BaselineProfileTest, topoff_picks_the_smallest_methods) {
  create_methods_in_one_class({"a", "b", "y", "z"}, {30, 20, 10, 1});

  bp::BaselineProfile profile;
  auto selection = bp::select_smallest_topoff_methods(
      scope(), profile, /* count */ 2, bp::DEFAULT_ART_HUGE_METHOD_MAX);

  EXPECT_EQ(selection.candidates, 4u);
  EXPECT_EQ(names_of(selection.methods),
            (std::vector<std::string>{"LMulti;.y:()V", "LMulti;.z:()V"}));
}

TEST_F(BaselineProfileTest, topoff_skips_methods_already_in_the_profile) {
  auto* tiny = create_method("tiny", ACC_PUBLIC, 1);
  auto* small = create_method("small", ACC_PUBLIC, 2);
  auto* medium = create_method("medium", ACC_PUBLIC, 3);

  bp::BaselineProfile profile;
  bp::MethodFlags hot;
  hot.hot = true;
  profile.methods.emplace(tiny, hot);

  auto selection = bp::select_smallest_topoff_methods(
      scope(), profile, /* count */ 2, bp::DEFAULT_ART_HUGE_METHOD_MAX);

  EXPECT_EQ(selection.candidates, 2u);
  EXPECT_EQ(names_of(selection.methods), names_of({small, medium}));
}

// The candidate scope is how the caller says "these are the classes that ship
// alongside the profile". Anything outside it is dropped when the profile is
// converted to binary form, so it must never be selected -- not even when it is
// the smallest method available, which is exactly when the ranking wants it.
TEST_F(BaselineProfileTest, topoff_only_draws_from_the_candidate_scope) {
  auto* in_scope = create_method("in_scope", ACC_PUBLIC, 5);
  create_method("out_of_scope", ACC_PUBLIC, 1);

  Scope candidate_scope{type_class(in_scope->get_class())};
  bp::BaselineProfile profile;
  auto selection = bp::select_smallest_topoff_methods(
      candidate_scope, profile,
      /* count */ 10, bp::DEFAULT_ART_HUGE_METHOD_MAX);

  EXPECT_EQ(selection.candidates, 1u);
  EXPECT_EQ(names_of(selection.methods), names_of({in_scope}));
}

// Padding must clear the same gates the profile's own entries do. An
// uncompilable padding entry would occupy an entry without ever becoming
// compiled code, so the AOT output would not actually be held steady.
TEST_F(BaselineProfileTest, topoff_skips_uncompilable_candidates) {
  create_method("<clinit>", ACC_STATIC | ACC_CONSTRUCTOR, 1);
  create_method("abs", ACC_PUBLIC | ACC_ABSTRACT, 0);
  create_method("nat", ACC_PUBLIC | ACC_NATIVE, 0);
  create_method("nc", ACC_PUBLIC, 1, /* never_compile */ true);
  create_method("huge", ACC_PUBLIC, 11);
  auto* ok = create_method("ok", ACC_PUBLIC, 5);

  bp::BaselineProfile profile;
  auto selection = bp::select_smallest_topoff_methods(
      scope(), profile, /* count */ 100, /* huge_method_max */ 10);

  EXPECT_EQ(selection.candidates, 1u);
  EXPECT_EQ(names_of(selection.methods), names_of({ok}));
}

TEST_F(BaselineProfileTest, topoff_stops_at_the_pool_size) {
  auto* a = create_method("a", ACC_PUBLIC, 1);
  auto* b = create_method("b", ACC_PUBLIC, 2);

  bp::BaselineProfile profile;
  auto selection = bp::select_smallest_topoff_methods(
      scope(), profile, /* count */ 50, bp::DEFAULT_ART_HUGE_METHOD_MAX);

  EXPECT_EQ(selection.candidates, 2u);
  EXPECT_EQ(names_of(selection.methods), names_of({a, b}));
}

TEST_F(BaselineProfileTest, topoff_of_zero_selects_nothing) {
  create_method("a", ACC_PUBLIC, 1);

  bp::BaselineProfile profile;
  auto selection = bp::select_smallest_topoff_methods(
      scope(), profile, /* count */ 0, bp::DEFAULT_ART_HUGE_METHOD_MAX);

  EXPECT_EQ(selection.candidates, 0u);
  EXPECT_TRUE(selection.methods.empty());
}

// Top-off is only a measurement aid if it is reproducible, so a tie on size
// must not resolve differently between runs. Every candidate here is the same
// size, which forces the tie-break, and it is taken on the deobfuscated
// name.
TEST_F(BaselineProfileTest, topoff_breaks_size_ties_by_deobfuscated_name) {
  // Creation order is deliberately not name order: picking by creation order
  // would select d and b.
  create_methods_in_one_class({"d", "b", "a", "c"}, {3, 3, 3, 3});

  bp::BaselineProfile profile;
  auto selection = bp::select_smallest_topoff_methods(
      scope(), profile, /* count */ 2, bp::DEFAULT_ART_HUGE_METHOD_MAX);

  ASSERT_EQ(selection.methods.size(), 2u);
  EXPECT_EQ(names_of(selection.methods),
            (std::vector<std::string>{"LMulti;.a:()V", "LMulti;.b:()V"}));
}

// Every void one-code-unit body compiles to the same instruction, so void
// padding collapses into a single shared body under identical code folding
// where a value return needs its own. The non-void candidate is created first,
// so it sorts ahead by deobfuscated name: only the return-kind key can pass it
// over.
TEST_F(BaselineProfileTest, topoff_prefers_void_returns_over_value_returns) {
  create_object_returning_method("returns_object");
  auto* returns_void = create_method("returns_void", ACC_PUBLIC, 1);

  bp::BaselineProfile profile;
  auto selection = bp::select_smallest_topoff_methods(
      scope(), profile, /* count */ 1, bp::DEFAULT_ART_HUGE_METHOD_MAX);

  EXPECT_EQ(selection.candidates, 2u);
  EXPECT_EQ(selection.candidates_returning_void, 1u);
  EXPECT_EQ(names_of(selection.methods), names_of({returns_void}));
  EXPECT_EQ(selection.methods_returning_void, 1u);
}

// Among candidates equal on size and return kind, the narrower frame wins. The
// wide one is created first and so sorts ahead by name; only the register key
// can pass it over.
TEST_F(BaselineProfileTest, topoff_prefers_the_narrower_frame) {
  auto* wide = create_method("wide", ACC_PUBLIC, 1);
  auto* narrow = create_method("narrow", ACC_PUBLIC, 1);
  wide->get_code()->cfg().set_registers_size(9);
  narrow->get_code()->cfg().set_registers_size(1);

  bp::BaselineProfile profile;
  auto selection = bp::select_smallest_topoff_methods(
      scope(), profile, /* count */ 1, bp::DEFAULT_ART_HUGE_METHOD_MAX);

  EXPECT_EQ(names_of(selection.methods), names_of({narrow}));
}

// A never-compile analysis drops a method from a profile without marking it,
// so afterwards the method looks like a perfectly good padding candidate.
// Padding it back in would silently reinstate what that analysis just decided
// against, so the caller's exclusion set has to outrank eligibility.
TEST_F(BaselineProfileTest, topoff_honors_the_exclusion_set) {
  auto* rejected = create_method("rejected", ACC_PUBLIC, 1);
  auto* ok = create_method("ok", ACC_PUBLIC, 1);

  UnorderedSet<const DexMethod*> excluded;
  excluded.insert(rejected);

  bp::BaselineProfile profile;
  auto selection = bp::select_smallest_topoff_methods(
      scope(), profile, /* count */ 10, bp::DEFAULT_ART_HUGE_METHOD_MAX,
      &excluded);

  EXPECT_EQ(selection.candidates, 1u);
  EXPECT_EQ(selection.excluded_candidates, 1u);
  EXPECT_EQ(names_of(selection.methods), names_of({ok}));
}

// Selection must not depend on hash or thread ordering. The pool here is large
// enough that the tie-break decides most of the answer.
TEST_F(BaselineProfileTest, topoff_selection_is_stable_across_runs) {
  std::vector<std::string> names;
  std::vector<uint32_t> sizes;
  for (int i = 0; i < 12; ++i) {
    names.push_back("m" + std::to_string(i));
    sizes.push_back(3);
  }
  // One strictly smaller method, which must be selected unconditionally.
  names.emplace_back("zz_smallest");
  sizes.push_back(1);
  create_methods_in_one_class(names, sizes);

  bp::BaselineProfile profile;
  auto first =
      names_of(bp::select_smallest_topoff_methods(
                   scope(), profile, 5, bp::DEFAULT_ART_HUGE_METHOD_MAX)
                   .methods);
  ASSERT_EQ(first.size(), 5u);
  EXPECT_NE(std::find(first.begin(), first.end(), "LMulti;.zz_smallest:()V"),
            first.end());
  for (int i = 0; i < 5; ++i) {
    EXPECT_EQ(names_of(bp::select_smallest_topoff_methods(
                           scope(), profile, 5, bp::DEFAULT_ART_HUGE_METHOD_MAX)
                           .methods),
              first);
  }
}

TEST_F(BaselineProfileTest,
       size_before_unreachable_lowering_counts_each_unreachable) {
  ClassCreator creator(DexType::make_type("LUnreachable;"));
  creator.set_super(type::java_lang_Object());
  auto* method =
      DexMethod::make_method("LUnreachable;.f:(Ljava/lang/Object;)V")
          ->make_concrete(ACC_PUBLIC | ACC_STATIC, /* is_virtual */ false);
  method->set_code(assembler::ircode_from_string(R"(
    (
      (load-param-object v0)
      (if-nez v0 :other)
      (unreachable v1)
      (throw v1)
      (:other)
      (unreachable v2)
      (throw v2)
    )
  )"));
  method->set_deobfuscated_name(show(method));
  creator.add_method(method);
  creator.create();

  EXPECT_EQ(bp::dex2oat_code_units_before_unreachable_lowering(method),
            bp::dex2oat_code_units(method) +
                2 * bp::lowered_unreachable_extra_code_units());
  method->get_code()->build_cfg();
  EXPECT_EQ(bp::dex2oat_code_units_before_unreachable_lowering(method),
            bp::dex2oat_code_units(method) +
                2 * bp::lowered_unreachable_extra_code_units());
}
