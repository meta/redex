/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include <cstdint>
#include <fstream>
#include <string>

#include <boost/filesystem/operations.hpp>
#include <boost/filesystem/path.hpp>
#include <json/value.h>

#include "DexClass.h"
#include "DexUtil.h"
#include "GlobalTypeAnalysisPass.h"
#include "RedexException.h"
#include "RedexTest.h"
#include "RemoveUnreachable.h"
#include "TypeAnalysisAwareRemoveUnreachable.h"
#include "TypeUtil.h"

namespace {

constexpr const char* kArtifact = "redex-removed-reachability-graph";

/*
 * The emission selectors are process-wide statics. The test runner currently
 * gives each case its own process, so this is insurance rather than a present
 * requirement -- but a case inheriting a previous one's selector would trip the
 * mutual-exclusion check for no visible reason. Reaching the statics needs a
 * subclass, since they are protected.
 */
class StaticsResetter : public RemoveUnreachablePass {
 public:
  static void reset() {
    s_emit_graph_on_last_run = false;
    s_emit_removed_graph_on_run = false;
    s_emit_removed_graph_on_last_run = false;
    s_all_reachability_runs = 0;
    s_all_reachability_run = 0;
  }
};

Json::Value pass_config(const std::string& option, const Json::Value& value) {
  Json::Value config(Json::objectValue);
  config["redex"] = Json::objectValue;
  config["redex"]["passes"] = Json::arrayValue;
  config["redex"]["passes"].append("RemoveUnreachablePass");
  config["RemoveUnreachablePass"] = Json::objectValue;
  if (!option.empty()) {
    config["RemoveUnreachablePass"][option] = value;
  }
  return config;
}

} // namespace

class RemovedReachabilityGraphPlumbingTest : public RedexIntegrationTest {
  void SetUp() override {
    StaticsResetter::reset();
    create_object_class();
    auto* cls = type_class(type::java_lang_Object());
    // To make the assertion in reachability analysis happy.
    cls->set_external();
  }
};

TEST_F(RemovedReachabilityGraphPlumbingTest, DisabledEmitsNoArtifact) {
  auto pg_config = process_and_get_proguard_config(stores[0].get_dexen(), R"(
    -keepclasseswithmembers public class RemoveUnreachableTest {
      public void testMethod();
    }
  )");
  ASSERT_TRUE(pg_config->ok);

  run_passes({new RemoveUnreachablePass()}, std::move(pg_config),
             pass_config("", Json::Value()));

  EXPECT_FALSE(boost::filesystem::exists(
      boost::filesystem::path(get_configfiles_out_dir()) / "meta" / kArtifact));
}

TEST_F(RemovedReachabilityGraphPlumbingTest, OnRunEmitsAWellFormedArtifact) {
  auto pg_config = process_and_get_proguard_config(stores[0].get_dexen(), R"(
    -keepclasseswithmembers public class RemoveUnreachableTest {
      public void testMethod();
    }
  )");
  ASSERT_TRUE(pg_config->ok);

  run_passes({new RemoveUnreachablePass()}, std::move(pg_config),
             pass_config("emit_removed_graph_on_run", 1));

  auto meta = boost::filesystem::path(get_configfiles_out_dir()) / "meta";
  auto path = meta / kArtifact;
  ASSERT_TRUE(boost::filesystem::exists(path));

  // The removed-graph switch is independent of the live-graph ones.
  EXPECT_FALSE(boost::filesystem::exists(meta / "reachability-graph"));
  EXPECT_FALSE(boost::filesystem::exists(meta / "method-override-graph"));

  // Header of the version-2 binary graph format, the same as the live
  // reachability graph's.
  std::ifstream is(path.string(), std::ios::binary);
  ASSERT_TRUE(is.is_open());
  uint32_t magic = 0;
  uint32_t version = 0;
  uint32_t node_count = 0;
  is.read(reinterpret_cast<char*>(&magic), sizeof(magic));
  is.read(reinterpret_cast<char*>(&version), sizeof(version));
  is.read(reinterpret_cast<char*>(&node_count), sizeof(node_count));
  ASSERT_TRUE(is.good());
  EXPECT_EQ(magic, 0xfaceb000);
  EXPECT_EQ(version, 2u);
  EXPECT_GT(node_count, 0u);

  // The reported node count has to describe the file that was written.
  int64_t nodes_metric = 0;
  for (const auto& info : pass_manager->get_pass_info()) {
    auto it = info.metrics.find("removed_graph_nodes");
    if (it != info.metrics.end()) {
      nodes_metric = it->second;
    }
  }
  EXPECT_EQ(nodes_metric, static_cast<int64_t>(node_count));
}

TEST_F(RemovedReachabilityGraphPlumbingTest, OnLastRunEmitsAnArtifact) {
  auto pg_config = process_and_get_proguard_config(stores[0].get_dexen(), R"(
    -keepclasseswithmembers public class RemoveUnreachableTest {
      public void testMethod();
    }
  )");
  ASSERT_TRUE(pg_config->ok);

  run_passes({new RemoveUnreachablePass()}, std::move(pg_config),
             pass_config("emit_removed_graph_on_last_run", true));

  EXPECT_TRUE(boost::filesystem::exists(
      boost::filesystem::path(get_configfiles_out_dir()) / "meta" / kArtifact));
}

TEST_F(RemovedReachabilityGraphPlumbingTest, BothSelectorsTogetherIsRejected) {
  auto pg_config = process_and_get_proguard_config(stores[0].get_dexen(), R"(
    -keepclasseswithmembers public class RemoveUnreachableTest {
      public void testMethod();
    }
  )");
  ASSERT_TRUE(pg_config->ok);

  // The two options are mutually exclusive: each picks a run that writes the
  // single metafile, so one would truncate the other's output. Because the
  // selectors are shared statics, this is rejected whether both are set on one
  // pass or spread across two.
  auto config = pass_config("emit_removed_graph_on_run", 1);
  config["RemoveUnreachablePass"]["emit_removed_graph_on_last_run"] = true;

  EXPECT_THROW(
      run_passes({new RemoveUnreachablePass()}, std::move(pg_config), config),
      RedexException);
}

TEST_F(RemovedReachabilityGraphPlumbingTest,
       TheTwoSelectorsConflictAcrossPasses) {
  auto pg_config = process_and_get_proguard_config(stores[0].get_dexen(), R"(
    -keepclasseswithmembers public class RemoveUnreachableTest {
      public void testMethod();
    }
  )");
  ASSERT_TRUE(pg_config->ok);

  // One option on each of two passes. The selectors are shared statics, so the
  // last pass to be configured sees both and rejects the combination. Two
  // passes both naming a run is a different matter and stays allowed.
  //
  // GlobalTypeAnalysisPass is in the list because
  // TypeAnalysisAwareRemoveUnreachablePass declares a hard analysis dependency
  // on it; without it `run_passes` throws over the unsatisfied dependency and
  // this would pass for the wrong reason.
  auto config = pass_config("emit_removed_graph_on_run", 1);
  config["redex"]["passes"].append("GlobalTypeAnalysisPass");
  config["redex"]["passes"].append("TypeAnalysisAwareRemoveUnreachablePass");
  config["TypeAnalysisAwareRemoveUnreachablePass"] = Json::objectValue;
  config["TypeAnalysisAwareRemoveUnreachablePass"]
        ["emit_removed_graph_on_last_run"] = true;

  EXPECT_THROW(
      run_passes({new RemoveUnreachablePass(), new GlobalTypeAnalysisPass(),
                  new TypeAnalysisAwareRemoveUnreachablePass()},
                 std::move(pg_config), config),
      RedexException);
}

TEST_F(RemovedReachabilityGraphPlumbingTest, TheLiveGraphSwitchStillWorks) {
  // Retaining RemovedReachabilityGraphPlumbingTest keeps its @PlumbingAnno, so
  // the marker records an ANNO node for it, while nothing marks the
  // annotation's value() accessor.
  auto pg_config = process_and_get_proguard_config(stores[0].get_dexen(), R"(
    -keepclasseswithmembers public class RemoveUnreachableTest {
      public void testMethod();
    }
    -keepclasseswithmembers public class RemovedReachabilityGraphPlumbingTest {
      public void annotatedEntry();
    }
  )");
  ASSERT_TRUE(pg_config->ok);

  // `sweep` drops the unmarked accessor, then `sweep_annotation_elements`
  // rewrites every annotation naming it -- freeing the DexAnnotation the graph
  // still points at. Dumping after that read freed memory; under ASAN this is
  // the regression guard for the ordering.
  auto config = pass_config("emit_graph_on_run", 1);
  config["RemoveUnreachablePass"]["sweep_annotation_elements"] = true;

  run_passes({new RemoveUnreachablePass()}, std::move(pg_config), config);

  // Without this the case is a smoke test: if nothing is swept, no annotation
  // is freed and the buggy ordering would pass too.
  int64_t removed_annotation_elements = 0;
  for (const auto& info : pass_manager->get_pass_info()) {
    auto it = info.metrics.find("removed_annotation_elements");
    if (it != info.metrics.end()) {
      removed_annotation_elements += it->second;
    }
  }
  EXPECT_GT(removed_annotation_elements, 0);

  // The two selectors are independent and share only the run counters.
  auto meta = boost::filesystem::path(get_configfiles_out_dir()) / "meta";
  ASSERT_TRUE(boost::filesystem::exists(meta / "reachability-graph"));
  EXPECT_TRUE(boost::filesystem::exists(meta / "method-override-graph"));
  EXPECT_FALSE(boost::filesystem::exists(meta / kArtifact));

  std::ifstream is((meta / "reachability-graph").string(), std::ios::binary);
  ASSERT_TRUE(is.is_open());
  uint32_t magic = 0;
  uint32_t version = 0;
  uint32_t node_count = 0;
  is.read(reinterpret_cast<char*>(&magic), sizeof(magic));
  is.read(reinterpret_cast<char*>(&version), sizeof(version));
  is.read(reinterpret_cast<char*>(&node_count), sizeof(node_count));
  ASSERT_TRUE(is.good());
  EXPECT_EQ(magic, 0xfaceb000);
  EXPECT_EQ(version, 2u);
  EXPECT_GT(node_count, 0u);
}
