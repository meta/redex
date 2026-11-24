/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "PassInputEdits.h"

#include <cstdio>
#include <exception>
#include <gtest/gtest.h>
#include <optional>

#include "ApiLevelChecker.h"
#include "ControlFlow.h"
#include "DexClass.h"
#include "DexHasher.h"
#include "DexUtil.h"
#include "GlobalConfig.h"
#include "IRCode.h"
#include "InitClassesWithSideEffects.h"
#include "Inliner.h"
#include "JsonWrapper.h"
#include "MethodUtil.h"
#include "PassManager.h"
#include "ReachableClasses.h"
#include "RedexContext.h"
#include "RedexTestUtils.h"
#include "RemoveUnusedFields.h"
#include "Resolver.h"
#include "Show.h"
#include "Walkers.h"

namespace pass_input_edits {

using hashing::DexHash;
using hashing::DexScopeHasher;

namespace {

bool is_editable(const DexMethod* method) {
  return !method->is_external() && !method->rstate.no_optimizations();
}

// Every method that code, annotations or static values in `scope` refer to,
// together with the definitions those references resolve to: inputs that
// tests build, or that javac compiled, may call a method through a subclass.
UnorderedSet<const DexMethodRef*> referenced_methods(const Scope& scope) {
  std::vector<DexMethodRef*> refs;
  for (const auto* cls : scope) {
    for (const auto* method : cls->get_all_methods()) {
      method->gather_methods(refs);
    }
    for (const auto* field : cls->get_all_fields()) {
      field->gather_methods(refs);
    }
    const auto* anno_set = cls->get_anno_set();
    if (anno_set != nullptr) {
      anno_set->gather_methods(refs);
    }
  }
  UnorderedSet<const DexMethodRef*> referenced;
  for (auto* ref : refs) {
    referenced.insert(ref);
    const auto* def = resolve_method(ref, MethodSearch::Any);
    if (def != nullptr) {
      referenced.insert(def);
    }
  }
  return referenced;
}

// Every field that code, annotations or static values in `scope` read, write
// or otherwise refer to, together with the definitions those references
// resolve to.
UnorderedSet<const DexFieldRef*> referenced_fields(const Scope& scope) {
  std::vector<DexFieldRef*> refs;
  for (const auto* cls : scope) {
    for (const auto* method : cls->get_all_methods()) {
      method->gather_fields(refs);
    }
    for (const auto* field : cls->get_all_fields()) {
      field->gather_fields(refs);
    }
    const auto* anno_set = cls->get_anno_set();
    if (anno_set != nullptr) {
      anno_set->gather_fields(refs);
    }
  }
  UnorderedSet<const DexFieldRef*> referenced;
  for (auto* ref : refs) {
    referenced.insert(ref);
    const auto* def = resolve_field(ref);
    if (def != nullptr) {
      referenced.insert(def);
    }
  }
  return referenced;
}

std::vector<DexMethod*> unreferenced_methods(const Scope& scope) {
  auto referenced = referenced_methods(scope);
  std::vector<DexMethod*> methods;
  for (auto* cls : scope) {
    if (cls->is_external()) {
      continue;
    }
    for (auto* method : cls->get_dmethods()) {
      if (!method::is_clinit(method) && !method::is_argless_init(method) &&
          can_delete(method) && is_editable(method) &&
          referenced.count(method) == 0) {
        methods.push_back(method);
      }
    }
  }
  return methods;
}

std::vector<DexField*> unreferenced_fields(const Scope& scope) {
  auto referenced = referenced_fields(scope);
  std::vector<DexField*> fields;
  for (auto* cls : scope) {
    if (cls->is_external()) {
      continue;
    }
    for (auto* field : cls->get_all_fields()) {
      // RemoveUnreachablePass keeps volatile instance fields even when nothing
      // refers to them.
      bool kept_volatile = is_volatile(field) && !is_static(field);
      if (can_delete(field) && !kept_volatile && referenced.count(field) == 0) {
        fields.push_back(field);
      }
    }
  }
  return fields;
}

void delete_method(DexMethod* method) {
  type_class(method->get_class())->remove_method(method);
  DexMethod::delete_method(method);
}

void delete_field(DexField* field) {
  type_class(field->get_class())->remove_field(field);
  DexField::delete_field_DO_NOT_USE(field);
}

// The members that are already unreferenced before an edit.
struct DeadMembers {
  UnorderedSet<const DexMethod*> methods;
  UnorderedSet<const DexField*> fields;

  explicit DeadMembers(const Scope& scope) {
    for (const auto* method : unreferenced_methods(scope)) {
      methods.insert(method);
    }
    for (const auto* field : unreferenced_fields(scope)) {
      fields.insert(field);
    }
  }
};

// Deletes the non-virtual methods and the fields that an edit left
// unreferenced, and what only they referred to. Members that were unreferenced
// before the edit stay.
void delete_newly_dead(const Scope& scope, const DeadMembers& before) {
  bool changed = true;
  while (changed) {
    changed = false;
    for (auto* method : unreferenced_methods(scope)) {
      if (before.methods.count(method) == 0) {
        delete_method(method);
        changed = true;
      }
    }
    for (auto* field : unreferenced_fields(scope)) {
      if (before.fields.count(field) == 0) {
        delete_field(field);
        changed = true;
      }
    }
  }
}

void build_cfgs(DexStoresVector& stores) {
  walk::code(build_class_scope(stores),
             [](DexMethod*, IRCode& code) { code.build_cfg(); });
}

// The config of `conf`, with RemoveUnusedFieldsPass set to remove only the
// writes of fields that nothing reads.
Json::Value write_removal_config(const ConfigFiles& conf) {
  Json::Value config = conf.get_json_config().unwrap();
  auto& pass_config = config["RemoveUnusedFieldsPass"];
  pass_config["remove_unwritten_fields"] = false;
  pass_config["remove_zero_written_fields"] = false;
  return config;
}

// The classes with a field write that RemoveUnusedFieldsPass, configured by
// `conf` as the edits run it, removes because nothing reads the field.
std::vector<DexClass*> classes_with_unread_fields(const Scope& scope,
                                                  const ConfigFiles& conf) {
  remove_unused_fields::PassImpl pass;
  pass.parse_config(
      JsonWrapper(write_removal_config(conf)["RemoveUnusedFieldsPass"]));
  auto fields = remove_unused_fields::fields_with_removable_unread_writes(
      pass.get_config(), scope);
  std::vector<DexClass*> classes;
  for (auto* cls : scope) {
    const auto& cls_fields = cls->get_all_fields();
    if (std::any_of(
            cls_fields.begin(), cls_fields.end(),
            [&](const DexField* field) { return fields.count(field) != 0; })) {
      classes.push_back(cls);
    }
  }
  return classes;
}

// Runs RemoveUnusedFieldsPass with every class but `cls` blocklisted, so that
// it removes only the writes of `cls`'s unread fields.
void remove_unread_field_writes(const DexClass* cls,
                                DexStoresVector& stores,
                                ConfigFiles& conf) {
  Json::Value config = write_removal_config(conf);
  auto& blocklist = config["RemoveUnusedFieldsPass"]["blocklist_classes"];
  blocklist = Json::arrayValue;
  for (const auto* other : build_class_scope(stores)) {
    if (other != cls) {
      blocklist.append(std::string(other->get_name()->str()));
    }
  }
  ConfigFiles edit_conf(config);
  edit_conf.parse_global_config();
  edit_conf.set_outdir(conf.get_outdir());
  remove_unused_fields::PassImpl pass;
  PassManager manager({&pass}, edit_conf);
  manager.run_passes(stores, edit_conf);
  build_cfgs(stores);
}

// The method inliner, configured as MethodInlinePass configures it, with what
// it needs.
class InlinerSetup {
 public:
  InlinerSetup(DexStoresVector& stores,
               ConfigFiles& conf,
               const UnorderedSet<DexMethod*>& candidates)
      : m_scope(build_class_scope(stores)),
        m_init_classes(m_scope, conf.create_init_class_insns()) {
    // What PassManager sets up before the first pass, with its default
    // min_sdk.
    api::LevelChecker::init(0, m_scope);
    conf.load(m_scope);
    m_config = *conf.get_global_config().get_config_by_name<::InlinerConfig>(
        "inliner");
    m_config.unique_inlined_registers = false;
    m_config.shrinker.analyze_constructors = m_config.shrinker.run_const_prop;
    m_inliner = std::make_unique<MultiMethodInliner>(
        m_scope, m_init_classes, stores, conf, candidates, std::ref(m_resolver),
        m_config, /* min_sdk */ 0);
  }

  MultiMethodInliner& get() { return *m_inliner; }

  const Scope& scope() const { return m_scope; }

  // The callee of `insn` in `caller`, as the inliner resolves it.
  DexMethod* resolve_callee(const DexMethod* caller, IRInstruction* insn) {
    return m_resolver(insn->get_method(), opcode_to_search(insn), caller);
  }

 private:
  Scope m_scope;
  inliner::InlinerConfig m_config;
  init_classes::InitClassesWithSideEffects m_init_classes;
  ConcurrentMethodResolverDeprecated m_resolver;
  std::unique_ptr<MultiMethodInliner> m_inliner;
};

struct CallSite {
  DexMethod* caller;
  IRInstruction* insn;
  DexMethod* callee;
  // Numbers, from 1 in instruction order, the static and direct calls in
  // `caller`, whether the inliner may inline them or not.
  size_t ordinal;
};

// The calls of static and direct methods that the method inliner may inline.
// Constructors are left out: the inliner inlines one only after making the
// fields it writes non-final, which MethodInlinePass does as a whole-program
// step. A pipeline that should see inlined constructors runs MethodInlinePass
// before the edits.
std::vector<CallSite> inlinable_calls(InlinerSetup& inliner) {
  std::vector<CallSite> sites;
  for (auto* caller : inliner.scope()) {
    for (auto* method : caller->get_all_methods()) {
      auto* code = method->get_code();
      if (code == nullptr || !is_editable(method)) {
        continue;
      }
      size_t calls = 0;
      for (auto& mie : cfg::InstructionIterable(code->cfg())) {
        auto* insn = mie.insn;
        if (insn->opcode() != OPCODE_INVOKE_STATIC &&
            insn->opcode() != OPCODE_INVOKE_DIRECT) {
          continue;
        }
        auto ordinal = ++calls;
        auto* callee = inliner.resolve_callee(method, insn);
        if (callee == nullptr || callee == method || !is_editable(callee) ||
            method::is_init(callee) || callee->get_code() == nullptr) {
          continue;
        }
        if (inliner.get().is_inlinable(
                method, callee, /* reduced_cfg */ nullptr, insn,
                code->cfg().estimate_code_units(),
                callee->get_code()->cfg().estimate_code_units())) {
          sites.push_back({method, insn, callee, ordinal});
        }
      }
    }
  }
  return sites;
}

std::string describe_inline(const CallSite& call) {
  return "inline " + show(call.callee) + " into " + show(call.caller) +
         ", call " + std::to_string(call.ordinal);
}

std::string inline_call(size_t site,
                        DexStoresVector& stores,
                        ConfigFiles& conf) {
  CallSite call;
  {
    InlinerSetup finder(stores, conf, {});
    call = inlinable_calls(finder).at(site);
  }
  auto description = describe_inline(call);
  DeadMembers before(build_class_scope(stores));
  InlinerSetup inliner(stores, conf, {call.callee});
  auto inlined = inliner.get().inline_callees(
      call.caller, UnorderedSet<IRInstruction*>{call.insn});
  inliner.get().flush();
  always_assert_log(inlined == 1, "The inliner did not %s",
                    description.c_str());
  delete_newly_dead(inliner.scope(), before);
  return description;
}

std::string describe_deletion(const DexMethod* method) {
  return "delete " + show(method);
}

std::string describe_write_removal(const DexClass* cls) {
  return "remove the writes of the unread fields of " + show(cls);
}

std::string describe_field_deletion(const DexClass* cls) {
  return "delete the unread fields of " + show(cls);
}

void reset_redex_context() {
  delete g_redex;
  g_redex = new RedexContext();
}

void run_passes(const MakePasses& make_passes,
                ConfigFiles& conf,
                DexStoresVector& stores) {
  auto passes = make_passes();
  std::vector<Pass*> pass_ptrs;
  pass_ptrs.reserve(passes.size());
  for (auto& pass : passes) {
    pass_ptrs.push_back(pass.get());
  }
  PassManager manager(pass_ptrs, conf);
  manager.run_passes(stores, conf);
}

DexHash hash_stores(DexStoresVector& stores) {
  return DexScopeHasher(build_class_scope(stores)).run();
}

bool same_hash(const DexHash& a, const DexHash& b) {
  return a.positions_hash == b.positions_hash &&
         a.registers_hash == b.registers_hash && a.code_hash == b.code_hash &&
         a.signature_hash == b.signature_hash;
}

// Checks `stores` the way PassManager checks the input of every Redex run, by
// running no passes on it.
void check_input(DexStoresVector& stores, ConfigFiles& conf) {
  PassManager manager({}, conf);
  manager.run_passes(stores, conf);
  build_cfgs(stores);
}

} // namespace

const std::vector<Edit>& all_edits() {
  static const std::vector<Edit> edits = {
      Edit::DeleteUnreferencedMethod,
      Edit::RemoveUnreadFieldWrites,
      Edit::DeleteUnreadFields,
      Edit::InlineCall,
  };
  return edits;
}

const char* edit_name(Edit edit) {
  switch (edit) {
  case Edit::DeleteUnreferencedMethod:
    return "DeleteUnreferencedMethod";
  case Edit::RemoveUnreadFieldWrites:
    return "RemoveUnreadFieldWrites";
  case Edit::DeleteUnreadFields:
    return "DeleteUnreadFields";
  case Edit::InlineCall:
    return "InlineCall";
  }
  not_reached();
}

std::vector<std::string> describe_sites(Edit edit,
                                        DexStoresVector& stores,
                                        ConfigFiles& conf) {
  auto scope = build_class_scope(stores);
  std::vector<std::string> sites;
  switch (edit) {
  case Edit::DeleteUnreferencedMethod:
    for (const auto* method : unreferenced_methods(scope)) {
      sites.push_back(describe_deletion(method));
    }
    return sites;
  case Edit::RemoveUnreadFieldWrites:
    for (const auto* cls : classes_with_unread_fields(scope, conf)) {
      sites.push_back(describe_write_removal(cls));
    }
    return sites;
  case Edit::DeleteUnreadFields:
    for (const auto* cls : classes_with_unread_fields(scope, conf)) {
      sites.push_back(describe_field_deletion(cls));
    }
    return sites;
  case Edit::InlineCall: {
    InlinerSetup inliner(stores, conf, {});
    for (const auto& call : inlinable_calls(inliner)) {
      sites.push_back(describe_inline(call));
    }
    return sites;
  }
  }
  not_reached();
}

std::string apply(Edit edit,
                  size_t site,
                  DexStoresVector& stores,
                  ConfigFiles& conf) {
  auto scope = build_class_scope(stores);
  switch (edit) {
  case Edit::DeleteUnreferencedMethod: {
    DeadMembers before(scope);
    auto* method = unreferenced_methods(scope).at(site);
    auto description = describe_deletion(method);
    before.methods.erase(method);
    delete_method(method);
    delete_newly_dead(scope, before);
    return description;
  }
  case Edit::RemoveUnreadFieldWrites: {
    const auto* cls = classes_with_unread_fields(scope, conf).at(site);
    remove_unread_field_writes(cls, stores, conf);
    return describe_write_removal(cls);
  }
  case Edit::DeleteUnreadFields: {
    const auto* cls = classes_with_unread_fields(scope, conf).at(site);
    DeadMembers before(scope);
    remove_unread_field_writes(cls, stores, conf);
    delete_newly_dead(build_class_scope(stores), before);
    return describe_field_deletion(cls);
  }
  case Edit::InlineCall:
    return inline_call(site, stores, conf);
  }
  not_reached();
}

void check_passes_never_abort(const LoadInput& load_input,
                              const Passes& passes,
                              const Json::Value& config,
                              const Checks& checks,
                              const std::vector<Edit>& edits) {
  Json::Value run_config = config;
  run_config["ir_type_checker"]["run_after_each_pass"] = true;
  run_config["ir_type_checker"]["verify_moves"] = true;
  // The edit step has checked the input already.
  Json::Value tested_config = run_config;
  tested_config["ir_type_checker"]["run_on_input"] = false;

  // Each step of a run has its own config and directory, so that the metafiles
  // the passes under test write are theirs alone.
  struct Step {
    redex::TempDir dir{redex::make_tmp_dir("PassInputEdits%%%%%%%%")};
    std::unique_ptr<ConfigFiles> conf;

    explicit Step(const Json::Value& json) {
      conf = std::make_unique<ConfigFiles>(json);
      conf->parse_global_config();
      conf->set_outdir(dir.path);
    }
  };

  // Builds the input in a new RedexContext and runs the earlier passes on it.
  auto prepare = [&](DexStoresVector& stores) {
    reset_redex_context();
    Step earlier(run_config);
    stores = load_input();
    // As redex-all does before the first pass, so that no edit deletes what
    // reflection reaches.
    init_reachable_classes(build_class_scope(stores),
                           ReachableClassesConfig(JsonWrapper(run_config)));
    if (passes.before_edits) {
      run_passes(passes.before_edits, *earlier.conf, stores);
    }
    build_cfgs(stores);
  };

  // Every run must prepare the same input. The first preparation records it.
  std::optional<DexHash> prepared;
  try {
    DexStoresVector stores;
    prepare(stores);
    prepared = hash_stores(stores);
  } catch (const std::exception& e) {
    ADD_FAILURE() << "Preparing the input aborted:\n" << e.what();
    return;
  }

  // Once a run finds a different input, every later run would too, so they
  // are skipped.
  bool input_differs = false;

  // Prepares the input, applies `apply_edit` to it, and runs the passes under
  // test. `apply_edit` returns a description of the edit it made. Returns a
  // hash of the output when no pass aborted.
  auto run = [&](const std::string& label,
                 const std::function<std::optional<std::string>(
                     DexStoresVector&, ConfigFiles&)>& apply_edit,
                 bool check) -> std::optional<DexHash> {
    if (input_differs) {
      return std::nullopt;
    }
    fprintf(stderr, "PassInputEdits: %s\n", label.c_str());
    DexStoresVector stores;
    try {
      prepare(stores);
    } catch (const std::exception& e) {
      ADD_FAILURE() << "Preparing the input for " << label << " aborted:\n"
                    << e.what();
      return std::nullopt;
    }
    if (!same_hash(hash_stores(stores), *prepared)) {
      ADD_FAILURE() << "Preparing the input for " << label
                    << " gave a different input than the first time: an "
                       "earlier pass behaves differently in a new "
                       "RedexContext, for example by keeping types or "
                       "methods of an earlier one in a static";
      input_differs = true;
      return std::nullopt;
    }
    Step edit_step(run_config);
    std::string description;
    try {
      auto applied = apply_edit(stores, *edit_step.conf);
      if (!applied) {
        return std::nullopt;
      }
      description = label + ": " + *applied;
    } catch (const std::exception& e) {
      ADD_FAILURE() << label << " aborted:\n" << e.what();
      return std::nullopt;
    }
    try {
      check_input(stores, *edit_step.conf);
    } catch (const std::exception& e) {
      ADD_FAILURE() << description << " left invalid input:\n" << e.what();
      return std::nullopt;
    }
    if (check && checks.before) {
      checks.before(build_class_scope(stores));
    }
    Step tested(tested_config);
    try {
      run_passes(passes.after_edits, *tested.conf, stores);
    } catch (const std::exception& e) {
      ADD_FAILURE() << "Aborted after " << description << ":\n" << e.what();
      return std::nullopt;
    }
    build_cfgs(stores);
    if (check && checks.after) {
      checks.after(stores, *tested.conf, description);
    }
    return hash_stores(stores);
  };

  auto no_edit = [](DexStoresVector&, ConfigFiles&) {
    return std::make_optional<std::string>("input as built");
  };
  auto first = run("no edit", no_edit, /* check */ true);
  // A second run in a new RedexContext must give the same output.
  auto second = run("no edit, again", no_edit, /* check */ false);
  if (first && second && !same_hash(*first, *second)) {
    ADD_FAILURE() << "The passes under test gave a different output in a new "
                     "RedexContext, for example by keeping types or methods "
                     "of an earlier one in a static";
  }

  if (input_differs) {
    return;
  }

  // The sites are found only after the runs without edits: finding them runs
  // the inliner's analyses, whose statics would otherwise hide a pass under
  // test that keeps state of an earlier RedexContext.
  // They are found twice, so that a difference shows even when one of the two
  // finds no site.
  auto find_sites = [&]() {
    DexStoresVector stores;
    prepare(stores);
    Step find(run_config);
    std::vector<std::vector<std::string>> found;
    found.reserve(edits.size());
    for (auto edit : edits) {
      found.push_back(describe_sites(edit, stores, *find.conf));
    }
    return found;
  };
  std::vector<std::vector<std::string>> sites;
  try {
    sites = find_sites();
    if (find_sites() != sites) {
      ADD_FAILURE() << "The sites of the edits differ in a new RedexContext: "
                       "the code that finds them keeps types or methods of "
                       "an earlier RedexContext in a static";
      return;
    }
  } catch (const std::exception& e) {
    ADD_FAILURE() << "Finding the sites of the edits aborted:\n" << e.what();
    return;
  }

  for (size_t i = 0; i < sites.size(); ++i) {
    auto edit = edits[i];
    for (size_t site = 0; site < sites[i].size(); ++site) {
      auto label =
          std::string(edit_name(edit)) + " site " + std::to_string(site);
      run(
          label,
          [&](DexStoresVector& stores,
              ConfigFiles& conf) -> std::optional<std::string> {
            if (describe_sites(edit, stores, conf) != sites[i]) {
              ADD_FAILURE() << label << ": the sites of " << edit_name(edit)
                            << " differ from those found in an earlier "
                               "RedexContext: the code that finds them keeps "
                               "types or methods of an earlier RedexContext "
                               "in a static";
              return std::nullopt;
            }
            return apply(edit, site, stores, conf);
          },
          /* check */ true);
    }
  }
}

} // namespace pass_input_edits
