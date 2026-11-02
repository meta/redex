/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include <fstream>
#include <functional>
#include <sstream>
#include <string>

#include "ConfigFiles.h"
#include "Creators.h"
#include "DexClass.h"
#include "DexUtil.h"
#include "IRAssembler.h"
#include "PassManager.h"
#include "ReachableClasses.h"
#include "ReachableNatives.h"
#include "RedexException.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"
#include "Show.h"
#include "Walkers.h"

namespace {

constexpr const char* kSoLoader = "Lcom/facebook/soloader/SoLoader;";
constexpr const char* kNativeLoader =
    "Lcom/facebook/soloader/nativeloader/NativeLoader;";

DexMethod* add_static_method(ClassCreator& creator,
                             DexType* owner,
                             const char* name,
                             DexProto* proto) {
  auto* method = dynamic_cast<DexMethod*>(
      DexMethod::make_method(owner, DexString::make_string(name), proto));
  always_assert(method != nullptr);
  method->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
  method->set_code(assembler::ircode_from_string("((const v0 0) (return v0))"));
  creator.add_method(method);
  return method;
}

DexMethod* add_instance_method(ClassCreator& creator,
                               DexType* owner,
                               const char* name,
                               DexProto* proto) {
  auto* method = dynamic_cast<DexMethod*>(
      DexMethod::make_method(owner, DexString::make_string(name), proto));
  always_assert(method != nullptr);
  method->make_concrete(ACC_PUBLIC, /* is_virtual */ true);
  method->set_code(assembler::ircode_from_string("((const v0 0) (return v0))"));
  creator.add_method(method);
  return method;
}

// Every load-library entry point the pass knows comes in these two shapes.
DexProto* string_proto() {
  return DexProto::make_proto(
      type::_boolean(),
      DexTypeList::make_type_list({DexType::make_type("Ljava/lang/String;")}));
}

DexProto* string_int_proto() {
  return DexProto::make_proto(
      type::_boolean(),
      DexTypeList::make_type_list(
          {DexType::make_type("Ljava/lang/String;"), type::_int()}));
}

} // namespace

class ReachableNativesTest : public RedexTest {
 protected:
  DexStoresVector stores;

  // A class with nothing to do with SoLoader, so the store is never empty. It
  // carries a method so that "the pass pinned nothing" is a claim about a
  // non-empty set of methods rather than a vacuous one.
  void add_unrelated_class(DexStore& store) {
    auto* owner = DexType::make_type("Lcom/example/App;");
    ClassCreator creator(owner);
    creator.set_super(type::java_lang_Object());
    add_static_method(creator, owner, "unrelated",
                      DexProto::make_proto(type::_boolean(),
                                           DexTypeList::make_type_list({})));
    store.add_classes({creator.create()});
  }

  // Every method anywhere in `stores` that the pass has pinned. Pinning is the
  // pass's only output, so counting it is how a "did nothing" case is checked.
  size_t count_pinned_methods() {
    size_t pinned = 0;
    walk::methods(build_class_scope(stores), [&](DexMethod* method) {
      if (root(method) || method->rstate.dont_inline() ||
          method->rstate.should_not_outline()) {
        ++pinned;
      }
    });
    return pinned;
  }

  // Both overloads of each named method, which is how the pass expects a
  // load-library class to be declared.
  std::vector<DexMethod*> add_load_library_class(
      DexStore& store,
      const char* class_name,
      const std::vector<const char*>& method_names) {
    auto* owner = DexType::make_type(class_name);
    ClassCreator creator(owner);
    creator.set_super(type::java_lang_Object());
    std::vector<DexMethod*> methods;
    for (const auto* method_name : method_names) {
      methods.push_back(
          add_static_method(creator, owner, method_name, string_proto()));
      methods.push_back(
          add_static_method(creator, owner, method_name, string_int_proto()));
    }
    store.add_classes({creator.create()});
    return methods;
  }

  std::vector<DexMethod*> add_soloader_class(DexStore& store) {
    return add_load_library_class(store, kSoLoader,
                                  {"loadLibraryUnsafe", "loadLibrary"});
  }

  std::vector<DexMethod*> add_nativeloader_class(DexStore& store) {
    return add_load_library_class(store, kNativeLoader, {"loadLibrary"});
  }

  // `analyze_load_library` is what takes eval_pass past its early return, so
  // every test here sets it; with it off there is nothing to exercise.
  //
  // It goes in the global config under the pass name rather than through a
  // direct parse_config call, because PassManager's constructor re-parses every
  // pass from the global config -- configuring the pass first would be silently
  // undone, leaving the option at its `false` default and every test here
  // passing vacuously.
  void run_eval_pass() {
    Json::Value global_config(Json::objectValue);
    global_config["ReachableNativesPass"]["analyze_load_library"] = true;
    ConfigFiles conf(global_config);

    ReachableNativesPass pass;
    std::vector<Pass*> passes{&pass};
    PassManager manager(passes, conf);
    pass.eval_pass(stores, conf, manager);
  }

  // A SoLoader whose entry points have code that passes the IR type checker,
  // for the tests that run the whole PassManager.
  void add_checkable_soloader_class(DexStore& store) {
    auto* owner = DexType::make_type(kSoLoader);
    ClassCreator creator(owner);
    creator.set_super(type::java_lang_Object());
    for (const auto* name : {"loadLibraryUnsafe", "loadLibrary"}) {
      add_static_method_with_code(creator, owner, name, string_proto(), R"(
        ((load-param-object v0) (const v1 1) (return v1))
      )");
      add_static_method_with_code(creator, owner, name, string_int_proto(), R"(
        ((load-param-object v0) (load-param v1) (const v2 1) (return v2))
      )");
    }
    store.add_classes({creator.create()});
  }

  static DexMethod* add_static_method_with_code(ClassCreator& creator,
                                                DexType* owner,
                                                const std::string& name,
                                                DexProto* proto,
                                                const std::string& code) {
    auto* method = dynamic_cast<DexMethod*>(
        DexMethod::make_method(owner, DexString::make_string(name), proto));
    method->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
    method->set_code(assembler::ircode_from_string(code));
    creator.add_method(method);
    return method;
  }

  // Adds `Lcom/example/Names;.foo:()Ljava/lang/String;`, which returns "foo"
  // where the analysis cannot see it.
  void add_names_class(DexStore& store) {
    auto* owner = DexType::make_type("Lcom/example/Names;");
    ClassCreator creator(owner);
    creator.set_super(type::java_lang_Object());
    add_static_method_with_code(
        creator, owner, "foo",
        DexProto::make_proto(type::java_lang_String(),
                             DexTypeList::make_type_list({})),
        R"(((const-string "foo") (move-result-pseudo-object v0) (return-object v0)))");
    store.add_classes({creator.create()});
  }

  // Adds `Lcom/example/Loader;` with one method per entry of `bodies`, each a
  // root, so that the reachability analysis of run_pass keeps them.
  std::vector<DexMethod*> add_loader_class(
      DexStore& store, const std::vector<std::string>& bodies) {
    auto* owner = DexType::make_type("Lcom/example/Loader;");
    ClassCreator creator(owner);
    creator.set_super(type::java_lang_Object());
    std::vector<DexMethod*> methods;
    for (size_t i = 0; i < bodies.size(); ++i) {
      auto* method = dynamic_cast<DexMethod*>(DexMethod::make_method(
          owner, DexString::make_string("load" + std::to_string(i)),
          DexProto::make_proto(type::_void(),
                               DexTypeList::make_type_list({}))));
      method->make_concrete(ACC_PUBLIC | ACC_STATIC, false);
      method->set_code(assembler::ircode_from_string(bodies[i]));
      method->rstate.set_root();
      creator.add_method(method);
      methods.push_back(method);
    }
    auto* cls = creator.create();
    // A root method is only a seed once its class is retained.
    cls->rstate.set_root();
    store.add_classes({cls});
    return methods;
  }

  // The library names the final analysis wrote out, one per line.
  struct LibraryNames {
    std::string live;
    std::string dead;
  };

  // Runs the pass the way an app config does: listed twice, so that the first
  // run analyzes the input and the second, after `in_between` has run, does
  // the final analysis of the live library names.
  LibraryNames run_pass_twice(const std::function<void()>& in_between) {
    Json::Value global_config(Json::objectValue);
    global_config["ReachableNativesPass"]["analyze_load_library"] = true;
    global_config["redex"]["passes"].append("ReachableNativesPass");
    global_config["redex"]["passes"].append("InBetweenPass");
    global_config["redex"]["passes"].append("ReachableNativesPass");
    ConfigFiles conf(global_config);
    conf.parse_global_config();
    auto tmp_dir = redex::make_tmp_dir("reachable_natives_%%%%%%%%");
    conf.set_outdir(tmp_dir.path);

    ReachableNativesPass pass;
    InBetweenPass in_between_pass(in_between);
    PassManager manager({&pass, &in_between_pass}, conf, RedexOptions{});
    manager.run_passes(stores, conf);

    auto read = [&](const std::string& file_name) {
      std::ifstream file(conf.metafile(file_name));
      std::stringstream contents;
      contents << file.rdbuf();
      return contents.str();
    };
    return {read("redex-live-load-library.txt"),
            read("redex-dead-load-library.txt")};
  }

 private:
  // Stands in for the passes that run between the two ReachableNativesPass
  // runs, and can rewrite the code the final analysis sees.
  class InBetweenPass : public Pass {
   public:
    explicit InBetweenPass(std::function<void()> fn)
        : Pass("InBetweenPass"), m_fn(std::move(fn)) {}

    redex_properties::PropertyInteractions get_property_interactions()
        const override {
      return {};
    }

    void run_pass(DexStoresVector&, ConfigFiles&, PassManager&) override {
      m_fn();
    }

   private:
    std::function<void()> m_fn;
  };
};

// An app that links no native libraries never pulls in SoLoader. That used to
// abort the build rather than skip the pass, whenever a shared config turned
// analyze_load_library on for the app.
TEST_F(ReachableNativesTest, evalPassSkipsInputWithoutSoLoader) {
  DexStore store("classes");
  add_unrelated_class(store);
  stores.emplace_back(std::move(store));

  run_eval_pass();

  // Skipping means pinning nothing. Surviving the call only shows the assert is
  // gone; it would also pass if the pass had started pinning arbitrary methods.
  EXPECT_EQ(count_pinned_methods(), 0);
}

TEST_F(ReachableNativesTest, evalPassPinsSoLoaderWhenPresent) {
  DexStore store("classes");
  add_unrelated_class(store);
  auto methods = add_soloader_class(store);
  stores.emplace_back(std::move(store));

  for (auto* method : methods) {
    ASSERT_FALSE(method->rstate.dont_inline());
    ASSERT_FALSE(method->rstate.should_not_outline());
  }

  run_eval_pass();

  // Pinned so a later pass cannot inline, outline or delete the entry point
  // out from under the native-reachability analysis.
  for (auto* method : methods) {
    EXPECT_TRUE(root(method));
    EXPECT_TRUE(method->rstate.dont_inline());
    EXPECT_TRUE(method->rstate.should_not_outline());
  }
  EXPECT_EQ(count_pinned_methods(), methods.size());
}

// NativeLoader is a standalone artifact: it does not depend on SoLoader, and
// libraries such as fbjni pull it in on its own. An app that carries only the
// facade is a legitimate input, so requiring both classes together would abort
// a build for no reason.
TEST_F(ReachableNativesTest, evalPassAcceptsNativeLoaderWithoutSoLoader) {
  DexStore store("classes");
  add_unrelated_class(store);
  auto methods = add_nativeloader_class(store);
  stores.emplace_back(std::move(store));

  run_eval_pass();

  for (auto* method : methods) {
    EXPECT_TRUE(root(method));
    EXPECT_TRUE(method->rstate.dont_inline());
    EXPECT_TRUE(method->rstate.should_not_outline());
  }
  EXPECT_EQ(count_pinned_methods(), methods.size());
}

// Referenced but not defined is a different shape from absent: the app
// demonstrably loads native libraries, the pass cannot pin the entry point, and
// silently skipping would under-approximate the live library set. It stays an
// assert.
TEST_F(ReachableNativesTest, evalPassRejectsReferencedButUndefinedSoLoader) {
  DexStore store("classes");
  add_unrelated_class(store);
  stores.emplace_back(std::move(store));

  // A ref with no definition: make_method without make_concrete, which is what
  // an input that calls into a library jar looks like.
  DexMethod::make_method(DexType::make_type(kSoLoader),
                         DexString::make_string("loadLibraryUnsafe"),
                         string_proto());

  EXPECT_THROW(run_eval_pass(), RedexException);
}

// Absence is all-or-nothing per class. A SoLoader that declares only some of
// the entry points has been rewritten by something, and the sibling that was
// renamed rather than removed still has call sites this pass would no longer
// recognize.
TEST_F(ReachableNativesTest, evalPassRejectsPartialSoLoader) {
  DexStore store("classes");
  add_unrelated_class(store);

  auto* owner = DexType::make_type(kSoLoader);
  ClassCreator creator(owner);
  creator.set_super(type::java_lang_Object());
  add_static_method(creator, owner, "loadLibraryUnsafe", string_proto());
  store.add_classes({creator.create()});
  stores.emplace_back(std::move(store));

  EXPECT_THROW(run_eval_pass(), RedexException);
}

// The same rule catches a SoLoader whose members have been renamed wholesale:
// the class is there, and none of it is recognizable.
TEST_F(ReachableNativesTest, evalPassRejectsUnrecognizableSoLoader) {
  DexStore store("classes");
  add_unrelated_class(store);

  auto* owner = DexType::make_type(kSoLoader);
  ClassCreator creator(owner);
  creator.set_super(type::java_lang_Object());
  add_static_method(creator, owner, "a", string_proto());
  store.add_classes({creator.create()});
  stores.emplace_back(std::move(store));

  EXPECT_THROW(run_eval_pass(), RedexException);
}

// The rule is per class, so it has to hold for NativeLoader on its own and not
// only for the class that happens to be checked first.
TEST_F(ReachableNativesTest, evalPassRejectsPartialNativeLoader) {
  DexStore store("classes");
  add_unrelated_class(store);

  auto* owner = DexType::make_type(kNativeLoader);
  ClassCreator creator(owner);
  creator.set_super(type::java_lang_Object());
  add_static_method(creator, owner, "loadLibrary", string_proto());
  store.add_classes({creator.create()});
  stores.emplace_back(std::move(store));

  EXPECT_THROW(run_eval_pass(), RedexException);
}

// An app that carries both classes is the ordinary shape, and the one where
// every entry point the pass knows has to be pinned.
TEST_F(ReachableNativesTest, evalPassPinsBothClassesWhenPresent) {
  DexStore store("classes");
  add_unrelated_class(store);
  auto soloader_methods = add_soloader_class(store);
  auto nativeloader_methods = add_nativeloader_class(store);
  stores.emplace_back(std::move(store));

  run_eval_pass();

  EXPECT_EQ(count_pinned_methods(),
            soloader_methods.size() + nativeloader_methods.size());
}

// A signature that matches but is not static belongs to some other class that
// happens to be named SoLoader, so the pass cannot reason about it.
TEST_F(ReachableNativesTest, evalPassRejectsNonStaticEntryPoint) {
  DexStore store("classes");
  add_unrelated_class(store);

  auto* owner = DexType::make_type(kSoLoader);
  ClassCreator creator(owner);
  creator.set_super(type::java_lang_Object());
  add_static_method(creator, owner, "loadLibraryUnsafe", string_proto());
  add_static_method(creator, owner, "loadLibraryUnsafe", string_int_proto());
  add_static_method(creator, owner, "loadLibrary", string_int_proto());
  add_instance_method(creator, owner, "loadLibrary", string_proto());
  store.add_classes({creator.create()});
  stores.emplace_back(std::move(store));

  EXPECT_THROW(run_eval_pass(), RedexException);
}

// A pass that rewrites a load-library call so that its library name is no
// longer a constant leaves the final analysis unable to tell which libraries
// stay live. The failure has to name the caller and what now defines the name,
// or nobody can tell which pass and which code to look at.
TEST_F(ReachableNativesTest, finalAnalysisNamesCallerOfNonConstantName) {
  DexStore store("classes");
  add_checkable_soloader_class(store);
  add_names_class(store);
  auto loaders = add_loader_class(store, {R"(
    (
      (const-string "foo")
      (move-result-pseudo-object v0)
      (const v1 16)
      (invoke-static (v0 v1) "Lcom/facebook/soloader/SoLoader;.loadLibrary:(Ljava/lang/String;I)Z")
      (return-void)
    )
  )"});
  stores.emplace_back(std::move(store));

  auto* loader = loaders.front();
  std::string message;
  try {
    run_pass_twice([&]() {
      loader->get_code()->clear_cfg();
      loader->set_code(assembler::ircode_from_string(R"(
        (
          (invoke-static () "Lcom/example/Names;.foo:()Ljava/lang/String;")
          (move-result-object v0)
          (const v1 16)
          (invoke-static (v0 v1) "Lcom/facebook/soloader/SoLoader;.loadLibrary:(Ljava/lang/String;I)Z")
          (return-void)
        )
      )"));
      loader->get_code()->build_cfg();
    });
  } catch (const RedexException& e) {
    message = e.what();
  }
  EXPECT_NE(message.find(show(loader)), std::string::npos) << message;
  EXPECT_NE(message.find("INVOKE_STATIC Lcom/example/Names;.foo"),
            std::string::npos)
      << message;
}
