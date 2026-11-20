/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include <memory>
#include <set>
#include <sstream>
#include <string>

#include "DexClass.h"
#include "MethodOverrideGraph.h"
#include "Reachability.h"
#include "RedexTest.h"
#include "TypeUtil.h"
#include "Walkers.h"

using namespace reachability;

namespace {

constexpr const char* kKeepRule = R"(
  -keepclasseswithmembers public class LiveReachabilityGraphTest {
    public void entry();
  }
)";

std::string label(const ReachableObject& obj) {
  std::ostringstream os;
  os << obj;
  return os.str();
}

} // namespace

class LiveReachabilityGraphTest : public RedexIntegrationTest {
 protected:
  void SetUp() override {
    create_object_class();
    auto* cls = type_class(type::java_lang_Object());
    // To make the assertion in reachability analysis happy.
    cls->set_external();
  }

  // Marks the code the keep rule reaches, recording the live graph.
  std::unique_ptr<ReachableObjects> compute_live_graph(
      bool prune_unreferenced_interfaces = false,
      bool prune_uninstantiable_insns = false) {
    auto pg_config =
        process_and_get_proguard_config(stores[0].get_dexen(), kKeepRule);
    always_assert(pg_config->ok);

    int num_ignore_check_strings = 0;
    IgnoreSets ig_sets;
    ReachableAspects reachable_aspects;
    auto scope = build_class_scope(stores);
    walk::parallel::code(scope, [&](auto*, auto& code) { code.build_cfg(); });
    auto mog = method_override_graph::build_graph(scope);
    auto reachables = compute_reachable_objects(
        scope, *mog, ig_sets, &num_ignore_check_strings, &reachable_aspects,
        /* record_reachability */ true, /* relaxed_keep_class_members */ false,
        /* relaxed_keep_interfaces */ prune_unreferenced_interfaces,
        /* cfg_gathering_check_instantiable */ prune_uninstantiable_insns);
    walk::parallel::code(scope, [&](auto*, auto& code) { code.clear_cfg(); });
    return reachables;
  }

  // The retainers the live graph records for the method named `name`.
  std::set<std::string> retainers_of_method(const ReachableObjects& reachables,
                                            const std::string& name) {
    const auto* method = DexMethod::get_method(name);
    always_assert_log(method != nullptr, "No method %s", name.c_str());
    return retainers_of(reachables, ReachableObject(method));
  }

  // The retainers the live graph records for the class named `descriptor`.
  std::set<std::string> retainers_of_class(const ReachableObjects& reachables,
                                           const std::string& descriptor) {
    const auto* cls = type_class(DexType::get_type(descriptor));
    always_assert_log(cls != nullptr, "No class %s", descriptor.c_str());
    return retainers_of(reachables, ReachableObject(cls));
  }

  std::set<std::string> retainers_of(const ReachableObjects& reachables,
                                     const ReachableObject& object) {
    const auto& graph = reachables.retainers_of();
    std::set<std::string> result;
    if (graph.count(object) == 0u) {
      return result;
    }
    for (const auto& retainer : UnorderedIterable(graph.at_unsafe(object))) {
      result.insert(label(retainer));
    }
    return result;
  }
};

TEST_F(LiveReachabilityGraphTest, SeedWithoutKeepReasonHasSeedRetainer) {
  auto reachables = compute_live_graph();

  // The test records no keep reasons. The kept methods of the kept class
  // retain it, so only the generic seed connects it to a root.
  EXPECT_EQ(retainers_of_class(*reachables, "LLiveReachabilityGraphTest;")
                .count("<SEED>"),
            1u);
}

TEST_F(LiveReachabilityGraphTest, MembersRetainTheirOwnClass) {
  auto reachables = compute_live_graph();

  // The annotation keeps the field Severity.HIGH, and a live field keeps its
  // class: Severity is retained only by its own members. Without the edge
  // from Severity.HIGH, Severity and its members would sit in a loop that no
  // root reaches.
  auto severity = retainers_of_class(*reachables, "LSeverity;");
  EXPECT_EQ(severity.count("LSeverity;.HIGH:LSeverity;"), 1u);
  for (const auto& retainer : severity) {
    EXPECT_EQ(retainer.rfind("LSeverity;.", 0), 0u) << retainer;
  }

  // A live method reference keeps the class it names, here one that only
  // inherits the method.
  EXPECT_EQ(
      retainers_of_class(*reachables, "LChild;").count("LChild;.inherited:()V"),
      1u);
}

TEST_F(LiveReachabilityGraphTest,
       ConditionalRetainerDoesNotDependOnMarkingOrder) {
  auto reachables = compute_live_graph();

  // call() is kept because Target is instantiable and entry() calls it. The
  // call marks it first, and the class must still be recorded as a retainer.
  EXPECT_EQ(
      retainers_of_method(*reachables, "LTarget;.call:()V").count("LTarget;"),
      1u);
}

TEST_F(LiveReachabilityGraphTest, InstanceOfRetainsTheClassItNames) {
  // prune_uninstantiable_insns makes the walk step over the instance-of, and
  // prune_unreferenced_interfaces keeps CheckedImpl from retaining Checked.
  auto reachables = compute_live_graph(/* prune_unreferenced_interfaces */ true,
                                       /* prune_uninstantiable_insns */ true);

  // Checked is kept because checks() tests for it and CheckedImpl is
  // instantiable. The walk reaches the instance-of before make() makes
  // Checked instantiable, and must still record checks() as its retainer.
  EXPECT_EQ(retainers_of_class(*reachables, "LChecked;"),
            std::set<std::string>{
                "LLiveReachabilityGraphTest;.checks:(Ljava/lang/Object;)Z"});
}

TEST_F(LiveReachabilityGraphTest, CheckCastRetainsTheMarkedClassItNames) {
  // As above, for a check-cast of a class that is already marked.
  auto reachables = compute_live_graph(/* prune_unreferenced_interfaces */ true,
                                       /* prune_uninstantiable_insns */ true);

  // entry() marks Cast with an array of it. casts() still retains Cast once
  // makeCast() makes it instantiable.
  EXPECT_EQ(retainers_of_class(*reachables, "LCast;"),
            (std::set<std::string>{
                "LLiveReachabilityGraphTest;.casts:(Ljava/lang/Object;)"
                "Ljava/lang/Object;",
                "LLiveReachabilityGraphTest;.entry:()V"}));
}
