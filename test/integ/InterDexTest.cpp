/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <fstream>
#include <gtest/gtest.h>
#include <json/json.h>

#include "Debug.h"
#include "DexClass.h"
#include "DexLimits.h"
#include "IRAssembler.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"

#include "InterDexPass.h"

#include "CleanupDynamicallyDead.h"

class InterDexTest : public RedexIntegrationTest {
 public:
  void define_test(const std::vector<std::string>& betmap,
                   const std::string& expected_manifest,
                   bool minimize_cross_dex_refs_explore_alternatives = false,
                   bool order_interdex = true,
                   bool define_dynamically_dead_classes = false,
                   bool last_dexes_only = false,
                   bool fill_last_coldstart_dex = false,
                   bool static_prune = false) {
    if (define_dynamically_dead_classes) {
      for (auto& cls : *classes) {
        if (cls->get_name() ==
            DexString::make_string("Lcom/facebook/redextest/C7;")) {
          cls->set_dynamically_dead();
        }
      }
    }

    std::cout << "Loaded classes: " << classes->size() << "\n";

    auto tmp_dir = redex::make_tmp_dir("redex_interdex_test_%%%%%%%%");

    auto betmap_file = make_betmap_file(tmp_dir.path, betmap);
    auto* config_file_env = std::getenv("config_file");
    always_assert_log(config_file_env,
                      "Config file must be specified to InterDexTest.\n");

    std::ifstream config_file(config_file_env, std::ifstream::binary);
    Json::Value cfg;
    config_file >> cfg;
    cfg["apk_dir"] = tmp_dir.path;
    cfg["coldstart_classes"] = betmap_file;
    if (minimize_cross_dex_refs_explore_alternatives) {
      cfg["InterDexPass"]["minimize_cross_dex_refs"] = true;
      cfg["InterDexPass"]["reorder_dynamically_dead_classes"] = true;
      cfg["InterDexPass"]["reserved_trefs"] =
          static_cast<uint64_t>(kOldMaxTypeRefs) - 16;
      cfg["InterDexPass"]["minimize_cross_dex_refs_explore_alternatives"] = 24;
      cfg["InterDexPass"]["order_interdex"] = order_interdex;
    }

    if (fill_last_coldstart_dex) {
      cfg["InterDexPass"]["fill_last_coldstart_dex"] = true;
    }

    if (static_prune) {
      cfg["InterDexPass"]["static_prune"] = true;
    }

    if (define_dynamically_dead_classes && last_dexes_only) {
      cfg["InterDexPass"]["reorder_dynamically_dead_classes"] = true;
      cfg["CleanupDynamicallyDeadPass"]["last_dexes_only"] = true;
    }

    auto path = boost::filesystem::path(tmp_dir.path);
    path += boost::filesystem::path::preferred_separator;
    path += "assets";
    path += boost::filesystem::path::preferred_separator;
    path += "secondary-program-dex-jars";
    boost::filesystem::create_directories(path);

    Pass* pass = nullptr;
    pass = new interdex::InterDexPass(/* register_plugins = */ false);
    std::vector<Pass*> passes = {pass};
    if (last_dexes_only) {
      passes.push_back(new CleanupDynamicallyDeadPass());
    }

    run_passes(passes, nullptr, cfg);

    std::ifstream manifest_in(path.string() + "/dex_manifest.txt");
    std::stringstream buffer;
    buffer << manifest_in.rdbuf();

    EXPECT_EQ(expected_manifest, buffer.str());
  }

  void define_throwing_test(
      const std::vector<std::string>& betmap,
      const std::string& expected_manifest,
      bool minimize_cross_dex_refs_explore_alternatives = false) {
    EXPECT_THROW(
        try {
          define_test(betmap,
                      expected_manifest,
                      minimize_cross_dex_refs_explore_alternatives);
        } catch (RedexException& e) {
          EXPECT_EQ(e.type, RedexError::INVALID_BETAMAP);
          throw;
        },
        RedexException);
  }

  std::string make_betmap_file(const std::string& tmp,
                               const std::vector<std::string>& betamap) {
    std::ofstream betamap_out;
    std::string path = tmp + "/classes.txt";
    betamap_out.open(path.c_str(), std::ios::out);
    for (const std::string& cls : betamap) {
      betamap_out << cls;
      betamap_out << "\n";
    }
    return path;
  }
};

/* clang-format off */

TEST_F(InterDexTest, interdex_noscroll_nobg_noext) {
  define_test({
      "com/facebook/redextest/InterDexPrimary.class",
      "com/facebook/redextest/C0.class",
      "DexEndMarker0.class",
      "com/facebook/redextest/C1.class",
      "com/facebook/redextest/C2.class",
      "DexEndMarker1.class",
      "com/facebook/redextest/C3.class",
      "com/facebook/redextest/C4.class",
      "com/facebook/redextest/C5.class",
      "com/facebook/redextest/C6.class",
      "com/facebook/redextest/C7.class",
      "com/facebook/redextest/C8.class",
      "com/facebook/redextest/C9.class"
    },
    "Lsecondary/dex00/Canary;,ordinal=0,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex01/Canary;,ordinal=1,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex02/Canary;,ordinal=2,coldstart=0,extended=0,primary=0,scroll=0,background=0\n"
  );

  EXPECT_EQ(stores.size(), 1);
  EXPECT_EQ(stores[0].get_dexen().size(), 3);
  // The last dex end marker terminates dex01 right where it appears, so only
  // C1 and C2 (plus the canary) land there. Contrast
  // interdex_fill_last_coldstart_dex below.
  EXPECT_EQ(stores[0].get_dexen()[1].size(), 3);
}

// Same betamap as interdex_noscroll_nobg_noext with fill_last_coldstart_dex on.
// The last dex end marker no longer flushes where it appears; the dex keeps
// filling with the rest of the betamap and is flushed once the betamap runs
// out, so it ends up holding C3..C9 as well. It is still the last dex of the
// cold-start set, and the dex after it is still the first that is not -- the
// deferral moves the boundary, it does not remove or duplicate it.
TEST_F(InterDexTest, interdex_fill_last_coldstart_dex) {
  define_test({
      "com/facebook/redextest/InterDexPrimary.class",
      "com/facebook/redextest/C0.class",
      "DexEndMarker0.class",
      "com/facebook/redextest/C1.class",
      "com/facebook/redextest/C2.class",
      "DexEndMarker1.class",
      "com/facebook/redextest/C3.class",
      "com/facebook/redextest/C4.class",
      "com/facebook/redextest/C5.class",
      "com/facebook/redextest/C6.class",
      "com/facebook/redextest/C7.class",
      "com/facebook/redextest/C8.class",
      "com/facebook/redextest/C9.class"
    },
    "Lsecondary/dex00/Canary;,ordinal=0,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex01/Canary;,ordinal=1,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex02/Canary;,ordinal=2,coldstart=0,extended=0,primary=0,scroll=0,background=0\n",
    /* minimize_cross_dex_refs_explore_alternatives */ false,
    /* order_interdex */ true,
    /* define_dynamically_dead_classes */ false,
    /* last_dexes_only */ false,
    /* fill_last_coldstart_dex */ true
  );

  EXPECT_EQ(stores.size(), 1);
  EXPECT_EQ(stores[0].get_dexen().size(), 3);
  // C1, C2, C3..C9 and the canary: the deferred marker let the dex keep
  // filling instead of ending it at 3 classes.
  EXPECT_EQ(stores[0].get_dexen()[1].size(), 10);
}

// fill_last_coldstart_dex where the dex overflows before the betamap ends. The
// overflow supplies the boundary the deferred marker was owed, so reaching the
// end of the betamap must not flush a second time -- that would cut an extra,
// nearly empty dex. Dexes are shrunk here to force the overflow.
TEST_F(InterDexTest, interdex_fill_last_coldstart_dex_overflow) {
  define_test({
      "com/facebook/redextest/InterDexPrimary.class",
      "com/facebook/redextest/C0.class",
      "DexEndMarker0.class",
      "com/facebook/redextest/C1.class",
      "com/facebook/redextest/C2.class",
      "DexEndMarker1.class",
      "com/facebook/redextest/C3.class",
      "com/facebook/redextest/C4.class",
      "com/facebook/redextest/C5.class",
      "com/facebook/redextest/C6.class",
      "com/facebook/redextest/C7.class",
      "com/facebook/redextest/C8.class",
      "com/facebook/redextest/C9.class",
      "com/facebook/redextest/C10.class",
      "com/facebook/redextest/C11.class",
      "com/facebook/redextest/C12.class"
    },
    "Lsecondary/dex00/Canary;,ordinal=0,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex01/Canary;,ordinal=1,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex02/Canary;,ordinal=2,coldstart=0,extended=0,primary=0,scroll=0,background=0\n",
    /* minimize_cross_dex_refs_explore_alternatives */ true,
    /* order_interdex */ true,
    /* define_dynamically_dead_classes */ false,
    /* last_dexes_only */ false,
    /* fill_last_coldstart_dex */ true
  );

  EXPECT_EQ(stores.size(), 1);
  // Three dexes, not four: the end of the betamap added no boundary of its own.
  EXPECT_EQ(stores[0].get_dexen().size(), 3);
}

TEST_F(InterDexTest, interdex_noscroll_nobg_ext) {
  define_test({
      "com/facebook/redextest/InterDexPrimary.class",
      "com/facebook/redextest/C0.class",
      "DexEndMarker0.class",
      "com/facebook/redextest/C1.class",
      "com/facebook/redextest/C2.class",
      "DexEndMarker1.class",
      "com/facebook/redextest/C3.class",
      "com/facebook/redextest/C4.class",
      "com/facebook/redextest/C5.class",
      "com/facebook/redextest/C6.class",
      "com/facebook/redextest/C7.class",
      "com/facebook/redextest/C8.class",
      "com/facebook/redextest/C9.class",
      "com/facebook/redextest/C10.class",
      "com/facebook/redextest/C11.class",
      "com/facebook/redextest/C12.class"
    },
    "Lsecondary/dex00/Canary;,ordinal=0,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex01/Canary;,ordinal=1,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex02/Canary;,ordinal=2,coldstart=0,extended=0,primary=0,scroll=0,background=0\n"
  );
}

TEST_F(InterDexTest, interdex_noscroll_bg_noext) {
  define_test({
      "com/facebook/redextest/InterDexPrimary.class",
      "com/facebook/redextest/C0.class",
      "DexEndMarker0.class",
      "com/facebook/redextest/C1.class",
      "com/facebook/redextest/C2.class",
      "DexEndMarker1.class",
      "com/facebook/redextest/C3.class",
      "com/facebook/redextest/C4.class",
      "BackgroundSetStart0.class",
      "com/facebook/redextest/C5.class",
      "com/facebook/redextest/C6.class",
      "com/facebook/redextest/C7.class",
      "com/facebook/redextest/C8.class",
      "com/facebook/redextest/C9.class",
      "com/facebook/redextest/C10.class",
      "com/facebook/redextest/C11.class",
      "com/facebook/redextest/C12.class",
      "BackgroundSetEnd0.class"
    },
    "Lsecondary/dex00/Canary;,ordinal=0,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex01/Canary;,ordinal=1,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex02/Canary;,ordinal=2,coldstart=0,extended=0,primary=0,scroll=0,background=1\n"
  );
}

TEST_F(InterDexTest, interdex_noscroll_bg_ext) {
  define_test({
      "com/facebook/redextest/InterDexPrimary.class",
      "com/facebook/redextest/C0.class",
      "DexEndMarker0.class",
      "com/facebook/redextest/C1.class",
      "com/facebook/redextest/C2.class",
      "DexEndMarker1.class",
      "com/facebook/redextest/C3.class",
      "com/facebook/redextest/C4.class",
      "BackgroundSetStart0.class",
      "com/facebook/redextest/C5.class",
      "com/facebook/redextest/C6.class",
      "BackgroundSetEnd0.class",
      "com/facebook/redextest/C7.class",
      "com/facebook/redextest/C8.class",
      "com/facebook/redextest/C9.class"
    },
    "Lsecondary/dex00/Canary;,ordinal=0,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex01/Canary;,ordinal=1,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex02/Canary;,ordinal=2,coldstart=0,extended=1,primary=0,scroll=0,background=1\n"
  );
}

TEST_F(InterDexTest, interdex_scroll_nobg_noext) {
  define_test({
      "com/facebook/redextest/InterDexPrimary.class",
      "com/facebook/redextest/C0.class",
      "DexEndMarker0.class",
      "com/facebook/redextest/C1.class",
      "com/facebook/redextest/C2.class",
      "DexEndMarker1.class",
      "ScrollSetStart0.class",
      "com/facebook/redextest/C3.class",
      "com/facebook/redextest/C4.class",
      "com/facebook/redextest/C5.class",
      "ScrollSetEnd0.class",
      "com/facebook/redextest/C6.class",
      "com/facebook/redextest/C7.class",
      "com/facebook/redextest/C8.class",
      "com/facebook/redextest/C9.class"
    },
    "Lsecondary/dex00/Canary;,ordinal=0,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex01/Canary;,ordinal=1,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex02/Canary;,ordinal=2,coldstart=0,extended=0,primary=0,scroll=1,background=0\n"
  );
}

TEST_F(InterDexTest, interdex_scroll_nobg_ext) {
  define_test({
      "com/facebook/redextest/InterDexPrimary.class",
      "com/facebook/redextest/C0.class",
      "DexEndMarker0.class",
      "com/facebook/redextest/C1.class",
      "com/facebook/redextest/C2.class",
      "DexEndMarker1.class",
      "ScrollSetStart0.class",
      "com/facebook/redextest/C3.class",
      "com/facebook/redextest/C4.class",
      "com/facebook/redextest/C5.class",
      "ScrollSetEnd0.class",
      "com/facebook/redextest/C6.class",
      "com/facebook/redextest/C7.class",
      "com/facebook/redextest/C8.class",
      "com/facebook/redextest/C9.class",
      "com/facebook/redextest/C10.class",
      "com/facebook/redextest/C11.class",
      "com/facebook/redextest/C12.class"
    },
    "Lsecondary/dex00/Canary;,ordinal=0,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex01/Canary;,ordinal=1,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex02/Canary;,ordinal=2,coldstart=0,extended=0,primary=0,scroll=1,background=0\n"
  );
}

TEST_F(InterDexTest, interdex_scroll_bg_noext) {
  define_test({
      "com/facebook/redextest/InterDexPrimary.class",
      "com/facebook/redextest/C0.class",
      "DexEndMarker0.class",
      "com/facebook/redextest/C1.class",
      "com/facebook/redextest/C2.class",
      "DexEndMarker1.class",
      "ScrollSetStart0.class",
      "com/facebook/redextest/C3.class",
      "com/facebook/redextest/C4.class",
      "com/facebook/redextest/C5.class",
      "ScrollSetEnd0.class",
      "BackgroundSetStart0.class",
      "com/facebook/redextest/C6.class",
      "com/facebook/redextest/C7.class",
      "com/facebook/redextest/C8.class",
      "com/facebook/redextest/C9.class",
      "com/facebook/redextest/C10.class",
      "com/facebook/redextest/C11.class",
      "com/facebook/redextest/C12.class",
      "BackgroundSetEnd0.class"
    },
    "Lsecondary/dex00/Canary;,ordinal=0,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex01/Canary;,ordinal=1,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex02/Canary;,ordinal=2,coldstart=0,extended=0,primary=0,scroll=1,background=1\n"
  );
}

TEST_F(InterDexTest, interdex_scroll_bg_ext) {
  define_test({
      "com/facebook/redextest/InterDexPrimary.class",
      "com/facebook/redextest/C0.class",
      "DexEndMarker0.class",
      "com/facebook/redextest/C1.class",
      "com/facebook/redextest/C2.class",
      "DexEndMarker1.class",
      "ScrollSetStart0.class",
      "com/facebook/redextest/C3.class",
      "com/facebook/redextest/C4.class",
      "com/facebook/redextest/C5.class",
      "ScrollSetEnd0.class",
      "BackgroundSetStart0.class",
      "com/facebook/redextest/C6.class",
      "BackgroundSetEnd0.class",
      "com/facebook/redextest/C7.class",
      "com/facebook/redextest/C8.class",
      "com/facebook/redextest/C9.class"
    },
    "Lsecondary/dex00/Canary;,ordinal=0,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex01/Canary;,ordinal=1,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex02/Canary;,ordinal=2,coldstart=0,extended=1,primary=0,scroll=1,background=1\n"
  );
}

// Control for interdex_coldstart_end_marker_without_dex_end_markers: with no
// marker at all, nothing ever ends the cold-start set, so every emitted dex
// stays coldstart=1. This is the pre-fix Instagram behavior.
TEST_F(InterDexTest, interdex_no_end_markers_at_all) {
  define_test({
      "INTERACTION_ID_ColdStart_Start.class",
      "com/facebook/redextest/InterDexPrimary.class",
      "com/facebook/redextest/C0.class",
      "com/facebook/redextest/C1.class",
      "com/facebook/redextest/C2.class",
      "com/facebook/redextest/C3.class",
      "com/facebook/redextest/C4.class",
      "com/facebook/redextest/C5.class",
      "com/facebook/redextest/C6.class",
      "com/facebook/redextest/C7.class",
      "com/facebook/redextest/C8.class",
      "com/facebook/redextest/C9.class"
    },
    "Lsecondary/dex00/Canary;,ordinal=0,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
  );
}

// Betamaps without any DexEndMarker (e.g. Instagram) end the cold-start set
// with the ColdStart interaction end marker instead. The marker forces no dex
// boundary, so with dexes large enough to hold everything the layout is exactly
// the one produced without it: same single dex, byte-identical manifest to
// interdex_no_end_markers_at_all above. There is no dex after the marker for
// the reset to land on, and the only dex there is holds cold-start classes, so
// it stays coldstart=1.
TEST_F(InterDexTest, interdex_coldstart_end_marker_without_dex_end_markers) {
  define_test({
      "INTERACTION_ID_ColdStart_Start.class",
      "com/facebook/redextest/InterDexPrimary.class",
      "com/facebook/redextest/C0.class",
      "com/facebook/redextest/C1.class",
      "com/facebook/redextest/C2.class",
      "INTERACTION_ID_ColdStart_End.class",
      "com/facebook/redextest/C3.class",
      "com/facebook/redextest/C4.class",
      "com/facebook/redextest/C5.class",
      "com/facebook/redextest/C6.class",
      "com/facebook/redextest/C7.class",
      "com/facebook/redextest/C8.class",
      "com/facebook/redextest/C9.class"
    },
    "Lsecondary/dex00/Canary;,ordinal=0,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
  );

  EXPECT_EQ(stores.size(), 1);
  EXPECT_EQ(stores[0].get_dexen().size(), 1);
  // Every class plus the canary: neither the marker nor the end of the betamap
  // split them.
  EXPECT_EQ(stores[0].get_dexen()[0].size(), 16);
}

// The marker only ends the cold-start set once a dex boundary comes along on
// its own. Here dexes are small enough that the betamap still overflows after
// the marker: the dex in flight when the marker is hit stays coldstart=1
// because it holds classes from before it, and the dex that overflow opens is
// the first that is not. Both boundaries come from overflow, never from the
// marker.
TEST_F(InterDexTest, interdex_coldstart_end_marker_overflow) {
  define_test({
      "INTERACTION_ID_ColdStart_Start.class",
      "com/facebook/redextest/InterDexPrimary.class",
      "com/facebook/redextest/C0.class",
      "com/facebook/redextest/C1.class",
      "com/facebook/redextest/C2.class",
      "com/facebook/redextest/C3.class",
      "com/facebook/redextest/C4.class",
      "com/facebook/redextest/C5.class",
      "com/facebook/redextest/C6.class",
      "com/facebook/redextest/C7.class",
      "com/facebook/redextest/C8.class",
      "INTERACTION_ID_ColdStart_End.class",
      "com/facebook/redextest/C9.class",
      "com/facebook/redextest/C10.class",
      "com/facebook/redextest/C11.class",
      "com/facebook/redextest/C12.class"
    },
    "Lsecondary/dex00/Canary;,ordinal=0,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex01/Canary;,ordinal=1,coldstart=0,extended=0,primary=0,scroll=0,background=0\n",
    /* minimize_cross_dex_refs_explore_alternatives */ true
  );
}

// Same betamap and same small dexes, but the marker now sits past the point
// where the classes overflow, so the only boundary precedes it. Both dexes hold
// cold-start classes and both stay coldstart=1, and -- the regression this
// guards -- running out of betamap with the reset still pending adds no third
// dex of its own.
TEST_F(InterDexTest, interdex_coldstart_end_marker_overflow_before_marker) {
  define_test({
      "INTERACTION_ID_ColdStart_Start.class",
      "com/facebook/redextest/InterDexPrimary.class",
      "com/facebook/redextest/C0.class",
      "com/facebook/redextest/C1.class",
      "com/facebook/redextest/C2.class",
      "com/facebook/redextest/C3.class",
      "com/facebook/redextest/C4.class",
      "com/facebook/redextest/C5.class",
      "com/facebook/redextest/C6.class",
      "com/facebook/redextest/C7.class",
      "com/facebook/redextest/C8.class",
      "com/facebook/redextest/C9.class",
      "com/facebook/redextest/C10.class",
      "com/facebook/redextest/C11.class",
      "INTERACTION_ID_ColdStart_End.class",
      "com/facebook/redextest/C12.class"
    },
    "Lsecondary/dex00/Canary;,ordinal=0,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex01/Canary;,ordinal=1,coldstart=1,extended=0,primary=0,scroll=0,background=0\n",
    /* minimize_cross_dex_refs_explore_alternatives */ true
  );
}

// The fblite shape, and the case the deferred reset exists for: the marker sits
// near the end of a betamap that is too short to overflow again, so nothing
// ends the cold-start set before emit_interdex_classes returns. The reset must
// survive that and land on the first dex the remaining classes overflow into.
// Reaching the end of the betamap must not flush by itself -- dex00 keeps
// filling with classes that are not in the betamap at all, which is what pins
// down that no boundary was introduced there.
TEST_F(InterDexTest,
       interdex_coldstart_end_marker_overflow_in_remaining_classes) {
  define_test({
      "INTERACTION_ID_ColdStart_Start.class",
      "com/facebook/redextest/InterDexPrimary.class",
      "com/facebook/redextest/C0.class",
      "com/facebook/redextest/C1.class",
      "com/facebook/redextest/C2.class",
      "INTERACTION_ID_ColdStart_End.class"
    },
    "Lsecondary/dex00/Canary;,ordinal=0,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex01/Canary;,ordinal=1,coldstart=0,extended=0,primary=0,scroll=0,background=0\n",
    /* minimize_cross_dex_refs_explore_alternatives */ true
  );

  EXPECT_EQ(stores.size(), 1);
  EXPECT_EQ(stores[0].get_dexen().size(), 2);
  // 4 betamap classes plus the canary would be 5. Anything above that is a
  // class the betamap never mentioned, sharing the last cold-start dex.
  EXPECT_GT(stores[0].get_dexen()[0].size(), 5);
}

// When DexEndMarkers are present they keep defining the cold-start section, so
// the ColdStart interaction end marker is a no-op. Same expectation as
// interdex_noscroll_nobg_noext.
TEST_F(InterDexTest, interdex_coldstart_end_marker_with_dex_end_markers) {
  define_test({
      "INTERACTION_ID_ColdStart_Start.class",
      "com/facebook/redextest/InterDexPrimary.class",
      "com/facebook/redextest/C0.class",
      "DexEndMarker0.class",
      "com/facebook/redextest/C1.class",
      "com/facebook/redextest/C2.class",
      "DexEndMarker1.class",
      "INTERACTION_ID_ColdStart_End.class",
      "com/facebook/redextest/C3.class",
      "com/facebook/redextest/C4.class",
      "com/facebook/redextest/C5.class",
      "com/facebook/redextest/C6.class",
      "com/facebook/redextest/C7.class",
      "com/facebook/redextest/C8.class",
      "com/facebook/redextest/C9.class"
    },
    "Lsecondary/dex00/Canary;,ordinal=0,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex01/Canary;,ordinal=1,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex02/Canary;,ordinal=2,coldstart=0,extended=0,primary=0,scroll=0,background=0\n"
  );
}

TEST_F(InterDexTest, interdex_cross_dex_ref_minimization) {
  define_test({
      "com/facebook/redextest/InterDexPrimary.class",
      "DexEndMarker0.class",
    },
    "Lsecondary/dex00/Canary;,ordinal=0,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex01/Canary;,ordinal=1,coldstart=0,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex02/Canary;,ordinal=2,coldstart=0,extended=0,primary=0,scroll=0,background=0\n",
    /* minimize_cross_dex_refs_explore_alternatives */ true
  );

  EXPECT_EQ(stores.size(), 1);
  EXPECT_EQ(stores[0].get_dexen().size(), 3);
  EXPECT_EQ(stores[0].get_dexen()[0].size(), 2);
  EXPECT_EQ(stores[0].get_dexen()[1].size(), 12);
  EXPECT_EQ(stores[0].get_dexen()[2].size(), 4);

  // First regular class is the one with highest seed weight
  EXPECT_EQ(stores[0].get_dexen()[1].front()->get_name()->str(), "Lcom/facebook/redextest/C7;");
}

TEST_F(InterDexTest, interdex_dynamically_dead) {
  define_test({
      "com/facebook/redextest/InterDexPrimary.class",
      "DexEndMarker0.class",
    },
    "Lsecondary/dex00/Canary;,ordinal=0,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex01/Canary;,ordinal=1,coldstart=0,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex02/Canary;,ordinal=2,coldstart=0,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex03/Canary;,ordinal=3,coldstart=0,extended=0,primary=0,scroll=0,background=0\n",
    /* minimize_cross_dex_refs_explore_alternatives */ true, /* order_interdex*/ true, /* define_dynamically_dead_classes */true
  );

  EXPECT_EQ(stores.size(), 1);
  EXPECT_EQ(stores[0].get_dexen().size(), 4);
  EXPECT_EQ(stores[0].get_dexen()[0].size(), 2);
  EXPECT_EQ(stores[0].get_dexen()[1].size(), 12);
  EXPECT_EQ(stores[0].get_dexen()[2].size(), 3);
  EXPECT_EQ(stores[0].get_dexen()[3].size(), 2);

  // The dynamically_dead class should be in the last seconday dex.
  EXPECT_EQ(stores[0].get_dexen()[3].front()->get_name()->str(), "Lcom/facebook/redextest/C7;");
}

TEST_F(InterDexTest, interdex_test_validate_class_spec) {
  define_throwing_test({
      "com/facebook/redextest/InterDexPrimary.class",
      "com/facebook/redextest/C0.class",
      "DexEndMarker0.class",
      "com/facebook/redextest/C1.class",
      "Lcom/facebook/redextest/C2;", // bad
      "DexEndMarker1.class",
      "com/facebook/redextest/C3.class",
      "com/facebook/redextest/C4.class",
      "com/facebook/redextest/C5.class",
      "com/facebook/redextest/C6.class",
      "com/facebook/redextest/C7.class",
      "com/facebook/redextest/C8.class",
      "com/facebook/redextest/C9.class"
    },
    "Lsecondary/dex00/Canary;,ordinal=0,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex01/Canary;,ordinal=1,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex02/Canary;,ordinal=2,coldstart=0,extended=0,primary=0,scroll=0,background=0\n"
  );
}

TEST_F(InterDexTest, without_order_interdex) {
  // When order_interdex is off, classes are distributed across dexes in a way that's not guided by the betamap; however, within each dexes, betamap classes are still ordered according to the betamap.
  define_test({
      "com/facebook/redextest/InterDexPrimary.class",
      "com/facebook/redextest/C0.class",
      "com/facebook/redextest/C1.class",
      "com/facebook/redextest/C2.class",
      "com/facebook/redextest/C3.class",
      "com/facebook/redextest/C4.class",
      "com/facebook/redextest/C5.class",
      "com/facebook/redextest/C6.class",
      "com/facebook/redextest/C7.class",
      "com/facebook/redextest/C8.class",
      "com/facebook/redextest/C9.class",
      "com/facebook/redextest/C10.class",
      "com/facebook/redextest/C11.class",
      "com/facebook/redextest/C12.class",
      "DexEndMarker0.class",
    },
    "Lsecondary/dex00/Canary;,ordinal=0,coldstart=0,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex01/Canary;,ordinal=1,coldstart=0,extended=0,primary=0,scroll=0,background=0\n",
    /* minimize_cross_dex_refs_explore_alternatives */ true,
    /* order_interdex */ false
  );

  auto get_class = [&](size_t dex_idx, size_t idx) {
    return stores[0].get_dexen()[dex_idx][idx]->get_name()->str();
  };
  EXPECT_EQ(stores.size(), 1);
  EXPECT_EQ(stores[0].get_dexen().size(), 2);
  EXPECT_EQ(stores[0].get_dexen()[0].size(), 11);
  EXPECT_EQ(get_class(0, 0), "Lcom/facebook/redextest/InterDexPrimary;");
  EXPECT_EQ(get_class(0, 1), "Lcom/facebook/redextest/C0;");
  EXPECT_EQ(get_class(0, 2), "Lcom/facebook/redextest/C1;");
  EXPECT_EQ(get_class(0, 3), "Lcom/facebook/redextest/C2;");
  EXPECT_EQ(get_class(0, 4), "Lcom/facebook/redextest/C3;");
  EXPECT_EQ(get_class(0, 5), "Lcom/facebook/redextest/C4;");
  EXPECT_EQ(get_class(0, 6), "Lcom/facebook/redextest/C7;");
  EXPECT_EQ(get_class(0, 7), "Lcom/facebook/redextest/C10;");
  EXPECT_EQ(get_class(0, 8), "Lcom/facebook/redextest/C11;");
  EXPECT_EQ(get_class(0, 9), "Lcom/facebook/redextest/C12;");
  EXPECT_EQ(stores[0].get_dexen()[1].size(), 6);
  EXPECT_EQ(get_class(1, 0), "Lcom/facebook/redextest/C5;");
  EXPECT_EQ(get_class(1, 1), "Lcom/facebook/redextest/C6;");
  EXPECT_EQ(get_class(1, 2), "Lcom/facebook/redextest/C8;");
  EXPECT_EQ(get_class(1, 3), "Lcom/facebook/redextest/C9;");

  // First regular class is the one with highest seed weight
}

TEST_F(InterDexTest, last_dexes_halfnosis) {
  define_test({
      "com/facebook/redextest/InterDexPrimary.class",
      "DexEndMarker0.class",
    },
    "Lsecondary/dex00/Canary;,ordinal=0,coldstart=1,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex01/Canary;,ordinal=1,coldstart=0,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex02/Canary;,ordinal=2,coldstart=0,extended=0,primary=0,scroll=0,background=0\n"
    "Lsecondary/dex03/Canary;,ordinal=3,coldstart=0,extended=0,primary=0,scroll=0,background=0\n",
    /* minimize_cross_dex_refs_explore_alternatives */ true,
    /* order_interdex */ true,
    /* define_dynamically_dead_classes */ true,
    /* last_dexes_only */ true
  );

  // All classes remain in a single store (no Voltron separation).
  EXPECT_EQ(stores.size(), 1);
  // CDDP relocates dead classes: strips the trailing dead dex left by
  // InterDexPass and re-packs dead classes into new trailing dexes.
  EXPECT_EQ(stores[0].get_dexen().size(), 4);

  // The dynamically dead class (C7) ends up in the last dex.
  auto& last_dex = stores[0].get_dexen().back();
  bool found_c7 = std::any_of(last_dex.begin(), last_dex.end(),
      [](DexClass* cls) {
        return cls->get_name()->str() == "Lcom/facebook/redextest/C7;";
      });
  EXPECT_TRUE(found_c7);

  // C7 must not appear in any earlier dex.
  for (size_t i = 0; i + 1 < stores[0].get_dexen().size(); i++) {
    for (auto* cls : stores[0].get_dexen()[i]) {
      EXPECT_NE(cls->get_name()->str(), "Lcom/facebook/redextest/C7;");
    }
  }
}

// With static_prune, a cold-start class keeps its cold-start position only if
// a root or another kept cold-start class refers to it. C0 is a root (its name
// is used) whose method takes a C1, so C1 is kept. The only references to C2
// and C3 are a method handle of C2's constructor and a method type returning
// C3, held in C1's code, so they are kept as well. C4 is referenced by nothing
// and loses its position.
TEST_F(InterDexTest, static_prune_counts_references_in_method_handles_and_types) {
  auto* c0 = type_class(DexType::get_type("Lcom/facebook/redextest/C0;"));
  c0->rstate.set_name_used();
  c0->add_method(assembler::method_from_string(R"(
    (method (public static) "Lcom/facebook/redextest/C0;.take:(Lcom/facebook/redextest/C1;)V"
     (
      (load-param-object v0)
      (return-void)
     )
    )
  )"));
  type_class(DexType::get_type("Lcom/facebook/redextest/C1;"))
      ->add_method(assembler::method_from_string(R"(
    (method (public static) "Lcom/facebook/redextest/C1;.handles:()V"
     (
      (const-method-handle invoke-constructor "Lcom/facebook/redextest/C2;.<init>:()V")
      (move-result-pseudo-object v0)
      (const-method-type "()Lcom/facebook/redextest/C3;")
      (move-result-pseudo-object v1)
      (return-void)
     )
    )
  )"));

  define_test(
      {
          "com/facebook/redextest/InterDexPrimary.class",
          "com/facebook/redextest/C0.class",
          "com/facebook/redextest/C1.class",
          "com/facebook/redextest/C2.class",
          "com/facebook/redextest/C3.class",
          "com/facebook/redextest/C4.class",
      },
      "Lsecondary/dex00/Canary;,ordinal=0,coldstart=1,extended=0,primary=0,scroll=0,background=0\n",
      /* minimize_cross_dex_refs_explore_alternatives */ false,
      /* order_interdex */ true,
      /* define_dynamically_dead_classes */ false,
      /* last_dexes_only */ false,
      /* fill_last_coldstart_dex */ false,
      /* static_prune */ true);

  auto is_perf_sensitive = [](const char* name) {
    return type_class(DexType::get_type(name))->is_perf_sensitive();
  };
  EXPECT_TRUE(is_perf_sensitive("Lcom/facebook/redextest/C0;"));
  EXPECT_TRUE(is_perf_sensitive("Lcom/facebook/redextest/C1;"));
  EXPECT_TRUE(is_perf_sensitive("Lcom/facebook/redextest/C2;"));
  EXPECT_TRUE(is_perf_sensitive("Lcom/facebook/redextest/C3;"));
  EXPECT_FALSE(is_perf_sensitive("Lcom/facebook/redextest/C4;"));
}

/* clang-format on */
