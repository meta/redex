/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <boost/filesystem/operations.hpp>
#include <boost/filesystem/path.hpp>
#include <fstream>
#include <gtest/gtest.h>

#include "Creators.h"
#include "IRAssembler.h"
#include "RedexTest.h"
#include "Verifier.h"

namespace fs = boost::filesystem;

constexpr const char* ARTIFACTS_FILENAME = "redex-class-dependencies.txt";

class VerifierArtifactsTest : public RedexIntegrationTest {
 protected:
  std::vector<std::string> read_artifact_lines() {
    fs::path out_dir(get_configfiles_out_dir());
    fs::path artifacts_path = out_dir / "meta" / ARTIFACTS_FILENAME;
    std::vector<std::string> lines;
    std::ifstream infile(artifacts_path.c_str());
    std::string line;
    while (std::getline(infile, line)) {
      lines.emplace_back(line);
    }
    std::sort(lines.begin(), lines.end());
    return lines;
  }
};

TEST_F(VerifierArtifactsTest, file_exists) {
  auto scope = build_class_scope(stores);
  run_passes({
      new VerifierPass(),
  });
  fs::path out_dir(get_configfiles_out_dir());
  fs::path artifacts_path = out_dir / "meta" / ARTIFACTS_FILENAME;
  ASSERT_TRUE(boost::filesystem::exists(artifacts_path));
  // Simple sanity check on file contents
  std::vector<std::string> lines;
  std::ifstream infile(artifacts_path.c_str());
  std::string line;
  while (std::getline(infile, line)) {
    lines.emplace_back(line);
  }
  EXPECT_EQ(lines.size(), 2) << "Expected only two class refs";
  std::sort(lines.begin(), lines.end());
  EXPECT_TRUE(lines[0].find("Lredex/B;") < lines[0].find("Lredex/A;"));
  EXPECT_TRUE(lines[1].find("Lredex/VerifierTest;") <
              lines[1].find("Lredex/B;"));
}

// The classes that a method handle and a method type name are referenced like
// the class of a called method.
TEST_F(VerifierArtifactsTest, method_handle_and_method_type_refs) {
  ClassCreator creator(DexType::make_type("LUser;"));
  creator.set_super(type::java_lang_Object());
  creator.add_method(assembler::method_from_string(R"(
    (method (public static) "LUser;.use:()V"
      (
        (const-method-handle invoke-static "Lredex/A;.foo:()V")
        (move-result-pseudo-object v0)
        (const-method-type "(Lredex/B;)V")
        (move-result-pseudo-object v0)
        (return-void)
      )
    )
  )"));
  stores[0].add_classes({creator.create()});
  run_passes({
      new VerifierPass(),
  });
  auto lines = read_artifact_lines();
  EXPECT_NE(std::find(lines.begin(), lines.end(),
                      "classes:LUser;->classes:Lredex/A;"),
            lines.end());
  EXPECT_NE(std::find(lines.begin(), lines.end(),
                      "classes:LUser;->classes:Lredex/B;"),
            lines.end());
}
