/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "RenameClassesV2.h"

#include <boost/algorithm/string/predicate.hpp>
#include <boost/regex.hpp>
#include <map>
#include <string>
#include <vector>

#include "ClassUtil.h"
#include "ConfigFiles.h"
#include "Debug.h"
#include "DexClass.h"
#include "DexEncoding.h"
#include "DexUtil.h"
#include "IRInstruction.h"
#include "KeepReason.h"
#include "PassManager.h"
#include "ProguardConfiguration.h"
#include "ProguardMap.h"
#include "ReachableClasses.h"
#include "RedexResources.h"
#include "Show.h"
#include "TypeStringRewriter.h"
#include "TypeUtil.h"
#include "Walkers.h"

#include "Trace.h"
#include <locator.h>
using facebook::Locator;

#define MAX_DESCRIPTOR_LENGTH (1024)

static const char* METRIC_AVOIDED_COLLISIONS = "num_avoided_collisions";
static const char* METRIC_SKIPPED_INDICES = "num_skipped_indices";
static const char* METRIC_DIGITS = "num_digits";
static const char* METRIC_CLASSES_IN_SCOPE = "num_classes_in_scope";
static const char* METRIC_RENAMED_CLASSES = "**num_renamed**";
static const char* METRIC_FORCE_RENAMED_CLASSES = "num_force_renamed";
static const char* METRIC_REWRITTEN_CONST_STRINGS =
    "num_rewritten_const_strings";
static const char* METRIC_MISSING_HIERARCHY_TYPES =
    "num_missing_hierarchy_types";
static const char* METRIC_MISSING_HIERARCHY_CLASSES =
    "num_missing_hierarchy_classes";

static RenameClassesPassV2 s_pass;

namespace {

const char* dont_rename_reason_to_metric(DontRenameReasonCode reason) {
  switch (reason) {
  case DontRenameReasonCode::Annotated:
    return "num_dont_rename_annotated";
  case DontRenameReasonCode::Annotations:
    return "num_dont_rename_annotations";
  case DontRenameReasonCode::Specific:
    return "num_dont_rename_specific";
  case DontRenameReasonCode::Packages:
    return "num_dont_rename_packages";
  case DontRenameReasonCode::Hierarchy:
    return "num_dont_rename_hierarchy";
  case DontRenameReasonCode::Resources:
    return "num_dont_rename_resources";
  case DontRenameReasonCode::ClassNameLiterals:
    return "num_dont_rename_class_name_literals";
  case DontRenameReasonCode::Canaries:
    return "num_dont_rename_canaries";
  case DontRenameReasonCode::NativeBindings:
    return "num_dont_rename_native_bindings";
  case DontRenameReasonCode::ClassForTypesWithReflection:
    return "num_dont_rename_class_for_types_with_reflection";
  case DontRenameReasonCode::ProguardCantRename:
    return "num_dont_rename_pg_cant_rename";
  case DontRenameReasonCode::SerdeRelationships:
    return "num_dont_rename_serde_relationships";
  default:
    not_reached_log("Unexpected DontRenameReasonCode: %d", (int)reason);
  }
}

bool dont_rename_reason_to_metric_per_rule(DontRenameReasonCode reason) {
  switch (reason) {
  case DontRenameReasonCode::Annotated:
  case DontRenameReasonCode::Packages:
  case DontRenameReasonCode::Hierarchy:
    // Set to true to add more detailed metrics for renamer if needed
    return false;
  case DontRenameReasonCode::ProguardCantRename:
    return keep_reason::Reason::record_keep_reasons();
  default:
    return false;
  }
}

} // namespace

// Returns idx of the vector of packages if the given class name matches, or -1
// if not found.
ssize_t find_matching_package(
    const std::string_view classname,
    const std::vector<std::string>& allowed_packages) {
  for (size_t i = 0; i < allowed_packages.size(); i++) {
    if (classname.rfind("L" + allowed_packages[i]) == 0) {
      return static_cast<ssize_t>(i);
    }
  }
  return -1;
}

bool referenced_by_layouts(const DexClass* clazz) {
  return clazz->rstate.is_referenced_by_resource_xml();
}

// Returns true if this class is a layout, and allowed for renaming via config.
bool is_allowed_layout_class(
    const DexClass* clazz,
    const std::vector<std::string>& allow_layout_rename_packages) {
  always_assert(referenced_by_layouts(clazz));
  auto idx = find_matching_package(clazz->get_name()->str(),
                                   allow_layout_rename_packages);
  return idx != -1;
}

UnorderedSet<std::string>
RenameClassesPassV2::build_dont_rename_class_name_literals(Scope& scope) {
  using namespace boost::algorithm;
  UnorderedSet<const DexString*> all_strings;
  for (auto* clazz : scope) {
    clazz->gather_strings(all_strings);
  }
  UnorderedSet<std::string> result;
  boost::regex external_name_regex{
      "((org)|(com)|(android(x|\\.support)))\\."
      "([a-zA-Z][a-zA-Z\\d_$]*\\.)*"
      "[a-zA-Z][a-zA-Z\\d_$]*"};
  for (const auto* dex_str : UnorderedIterable(all_strings)) {
    const std::string_view s = dex_str->str();
    if (!ends_with(s, ".java") &&
        boost::regex_match(dex_str->c_str(), external_name_regex)) {
      std::string internal_name = java_names::external_to_internal(s);
      auto* cls = type_class(DexType::get_type(internal_name));
      if (cls != nullptr && !cls->is_external()) {
        result.insert(std::move(internal_name));
        TRACE(RENAME, 4, "Found %s in string pool before renaming",
              str_copy(s).c_str());
      }
    }
  }
  return result;
}

UnorderedSet<const DexString*>
RenameClassesPassV2::build_dont_rename_for_types_with_reflection(
    Scope& scope, const ProguardMap& pg_map) {
  UnorderedSet<const DexString*> dont_rename_class_for_types_with_reflection;
  UnorderedSet<DexType*> refl_map;
  for (auto const& refl_type_str : m_dont_rename_types_with_reflection) {
    auto deobf_cls_string = pg_map.translate_class(refl_type_str);
    TRACE(RENAME,
          4,
          "%s got translated to %s",
          refl_type_str.c_str(),
          deobf_cls_string.c_str());
    if (deobf_cls_string.empty()) {
      deobf_cls_string = refl_type_str;
    }
    DexType* type_with_refl = DexType::get_type(deobf_cls_string);
    if (type_with_refl != nullptr) {
      TRACE(RENAME, 4, "got DexType %s", SHOW(type_with_refl));
      refl_map.insert(type_with_refl);
    }
  }

  walk::opcodes(
      scope,
      [](DexMethod*) { return true; },
      [&](DexMethod* m, IRInstruction* insn) {
        if (insn->has_method()) {
          auto* callee = insn->get_method();
          if (callee == nullptr || !callee->is_concrete()) {
            return;
          }
          auto* callee_method_cls = callee->get_class();
          if (refl_map.count(callee_method_cls) == 0) {
            return;
          }
          const auto* classname = m->get_class()->get_name();
          TRACE(RENAME, 4,
                "Found %s with known reflection usage. marking reachable",
                classname->c_str());
          dont_rename_class_for_types_with_reflection.insert(classname);
        }
      });
  return dont_rename_class_for_types_with_reflection;
}

UnorderedSet<const DexString*> RenameClassesPassV2::build_dont_rename_canaries(
    Scope& scope) {
  UnorderedSet<const DexString*> dont_rename_canaries;
  // Gather canaries
  for (auto* clazz : scope) {
    if (strstr(clazz->get_name()->c_str(), "/Canary") != nullptr) {
      dont_rename_canaries.insert(clazz->get_name());
    }
  }
  return dont_rename_canaries;
}

UnorderedSet<const DexType*>
RenameClassesPassV2::build_force_rename_hierarchies(
    PassManager& mgr, Scope& scope, const ClassHierarchy& class_hierarchy) {
  UnorderedSet<const DexType*> force_rename_hierarchies;
  std::vector<DexClass*> base_classes;
  for (const auto& base : m_force_rename_hierarchies) {
    // skip comments
    if (base.c_str()[0] == '#') {
      continue;
    }
    auto* base_type = DexType::get_type(base);
    if (base_type != nullptr) {
      DexClass* base_class = type_class(base_type);
      if (base_class == nullptr) {
        TRACE(RENAME, 2, "Can't find class for force_rename_hierachy rule %s",
              base.c_str());
        mgr.incr_metric(METRIC_MISSING_HIERARCHY_CLASSES, 1);
      } else {
        base_classes.emplace_back(base_class);
      }
    } else {
      TRACE(RENAME, 2, "Can't find type for force_rename_hierachy rule %s",
            base.c_str());
      mgr.incr_metric(METRIC_MISSING_HIERARCHY_TYPES, 1);
    }
  }
  for (const auto& base_class : base_classes) {
    force_rename_hierarchies.insert(base_class->get_type());
    TypeSet children_and_implementors;
    get_all_children_or_implementors(class_hierarchy, scope, base_class,
                                     children_and_implementors);
    for (const auto& cls : children_and_implementors) {
      force_rename_hierarchies.insert(cls);
    }
  }
  return force_rename_hierarchies;
}

UnorderedMap<const DexType*, const DexString*>
RenameClassesPassV2::build_dont_rename_hierarchies(
    PassManager& mgr, Scope& scope, const ClassHierarchy& class_hierarchy) {
  UnorderedMap<const DexType*, const DexString*> dont_rename_hierarchies;
  std::vector<DexClass*> base_classes;
  for (const auto& base : m_dont_rename_hierarchies) {
    // skip comments
    if (base.c_str()[0] == '#') {
      continue;
    }
    auto* base_type = DexType::get_type(base);
    if (base_type != nullptr) {
      DexClass* base_class = type_class(base_type);
      if (base_class == nullptr) {
        TRACE(RENAME, 2, "Can't find class for dont_rename_hierachy rule %s",
              base.c_str());
        mgr.incr_metric(METRIC_MISSING_HIERARCHY_CLASSES, 1);
      } else {
        base_classes.emplace_back(base_class);
      }
    } else {
      TRACE(RENAME, 2, "Can't find type for dont_rename_hierachy rule %s",
            base.c_str());
      mgr.incr_metric(METRIC_MISSING_HIERARCHY_TYPES, 1);
    }
  }
  for (const auto& base_class : base_classes) {
    const auto* base_name = base_class->get_name();
    dont_rename_hierarchies[base_class->get_type()] = base_name;
    TypeSet children_and_implementors;
    get_all_children_or_implementors(class_hierarchy, scope, base_class,
                                     children_and_implementors);
    for (const auto& cls : children_and_implementors) {
      dont_rename_hierarchies[cls] = base_name;
    }
  }
  return dont_rename_hierarchies;
}

UnorderedSet<const DexType*>
RenameClassesPassV2::build_dont_rename_serde_relationships(Scope& scope) {
  UnorderedSet<const DexType*> dont_rename_serde_relationships;
  for (const auto& cls : scope) {
    klass::Serdes cls_serdes = klass::get_serdes(cls);
    std::string name = cls->get_name()->str_copy();
    name.pop_back();

    // Look for a class that matches one of the two deserializer patterns
    const auto* deser = cls_serdes.get_deser();
    const auto* flatbuf_deser = cls_serdes.get_flatbuf_deser();
    bool has_deser_finder = false;

    if ((deser != nullptr) || (flatbuf_deser != nullptr)) {
      for (const auto& method : cls->get_dmethods()) {
        if (strcmp("$$getDeserializerClass", method->get_name()->c_str()) ==
            0) {
          has_deser_finder = true;
          break;
        }
      }
    }

    // Look for a class that matches one of the two serializer patterns
    const auto* ser = cls_serdes.get_ser();
    const auto* flatbuf_ser = cls_serdes.get_flatbuf_ser();
    bool has_ser_finder = false;

    if ((ser != nullptr) || (flatbuf_ser != nullptr)) {
      for (const auto& method : cls->get_dmethods()) {
        if (strcmp("$$getSerializerClass", method->get_name()->c_str()) == 0) {
          has_ser_finder = true;
          break;
        }
      }
    }

    bool dont_rename =
        (((deser != nullptr) || (flatbuf_deser != nullptr)) &&
         !has_deser_finder) ||
        (((ser != nullptr) || (flatbuf_ser != nullptr)) && !has_ser_finder);

    if (dont_rename) {
      dont_rename_serde_relationships.insert(cls->get_type());
      if (deser != nullptr) {
        dont_rename_serde_relationships.insert(deser);
      }
      if (flatbuf_deser != nullptr) {
        dont_rename_serde_relationships.insert(flatbuf_deser);
      }
      if (ser != nullptr) {
        dont_rename_serde_relationships.insert(ser);
      }
      if (flatbuf_ser != nullptr) {
        dont_rename_serde_relationships.insert(flatbuf_ser);
      }
    }
  }

  return dont_rename_serde_relationships;
}

UnorderedSet<const DexType*>
RenameClassesPassV2::build_dont_rename_native_bindings(Scope& scope) {
  UnorderedSet<const DexType*> dont_rename_native_bindings;
  // find all classes with native methods, and all types mentioned
  // in protos of native methods
  for (auto* clazz : scope) {
    for (auto* meth : clazz->get_dmethods()) {
      if (is_native(meth)) {
        dont_rename_native_bindings.insert(clazz->get_type());
        auto* proto = meth->get_proto();
        auto* rtype = proto->get_rtype();
        dont_rename_native_bindings.insert(rtype);
        for (const auto* ptype : *proto->get_args()) {
          dont_rename_native_bindings.insert(
              type::make_element_type_if_array(ptype));
        }
      }
    }
    for (auto* meth : clazz->get_vmethods()) {
      if (is_native(meth)) {
        dont_rename_native_bindings.insert(clazz->get_type());
        auto* proto = meth->get_proto();
        auto* rtype = proto->get_rtype();
        dont_rename_native_bindings.insert(rtype);
        for (const auto* ptype : *proto->get_args()) {
          dont_rename_native_bindings.insert(
              type::make_element_type_if_array(ptype));
        }
      }
    }
  }
  return dont_rename_native_bindings;
}

UnorderedSet<const DexType*>
RenameClassesPassV2::build_dont_rename_annotated() {
  UnorderedSet<const DexType*> dont_rename_annotated;
  for (const auto& annotation : m_dont_rename_annotated) {
    DexType* anno = DexType::get_type(annotation);
    if (anno != nullptr) {
      dont_rename_annotated.insert(anno);
    }
  }
  return dont_rename_annotated;
}

static void sanity_check(const Scope& scope,
                         const rewriter::TypeStringMap& name_mapping) {
  std::vector<std::string> external_names_vec;
  // Class.forName() expects strings of the form "foo.bar.Baz". We should be
  // very suspicious if we see these strings in the string pool that
  // correspond to the old name of a class that we have renamed...
  for (const auto& it : UnorderedIterable(name_mapping.get_class_map())) {
    external_names_vec.push_back(
        java_names::internal_to_external(it.first->str()));
  }
  UnorderedSet<std::string_view> external_names;
  for (auto& s : external_names_vec) {
    external_names.insert(s);
  }
  UnorderedSet<const DexString*> all_strings;
  for (auto* clazz : scope) {
    clazz->gather_strings(all_strings);
  }
  int sketchy_strings = 0;
  for (const auto* s : UnorderedIterable(all_strings)) {
    if (external_names.find(s->str()) != external_names.end() ||
        (name_mapping.get_new_type_name(s) != nullptr)) {
      TRACE(RENAME, 2, "Found %s in string pool after renaming", s->c_str());
      sketchy_strings++;
    }
  }
  if (sketchy_strings > 0) {
    fprintf(stderr,
            "WARNING: Found a number of sketchy class-like strings after class "
            "renaming. Re-run with TRACE=RENAME:2 for more details.\n");
  }
}

std::string get_keep_rule(const DexClass* clazz) {
  if (keep_reason::Reason::record_keep_reasons()) {
    const auto& keep_reasons = clazz->rstate.keep_reasons();
    for (const auto* reason : UnorderedIterable(keep_reasons)) {
      if (reason->type == keep_reason::KEEP_RULE &&
          !reason->keep_rule->allowobfuscation) {
        return show(*reason);
      }
    }
  }
  return "";
}

void RenameClassesPassV2::eval_classes(Scope& scope,
                                       const ClassHierarchy& class_hierarchy,
                                       ConfigFiles& conf,
                                       bool rename_annotations,
                                       PassManager& mgr) {
  UnorderedSet<const DexType*> force_rename_hierarchies;
  UnorderedSet<const DexType*> dont_rename_serde_relationships;
  UnorderedSet<std::string> dont_rename_class_name_literals;
  UnorderedSet<const DexString*> dont_rename_class_for_types_with_reflection;
  UnorderedSet<const DexString*> dont_rename_canaries;
  UnorderedMap<const DexType*, const DexString*> dont_rename_hierarchies;
  UnorderedSet<const DexType*> dont_rename_native_bindings;
  UnorderedSet<const DexType*> dont_rename_annotated;

  std::vector<std::function<void()>> fns{
      [&] {
        force_rename_hierarchies =
            build_force_rename_hierarchies(mgr, scope, class_hierarchy);
      },
      [&] {
        dont_rename_serde_relationships =
            build_dont_rename_serde_relationships(scope);
      },
      [&] {
        dont_rename_class_name_literals =
            build_dont_rename_class_name_literals(scope);
      },
      [&] {
        dont_rename_class_for_types_with_reflection =
            build_dont_rename_for_types_with_reflection(
                scope, conf.get_proguard_map());
      },
      [&] { dont_rename_canaries = build_dont_rename_canaries(scope); },
      [&] {
        dont_rename_hierarchies =
            build_dont_rename_hierarchies(mgr, scope, class_hierarchy);
      },
      [&] {
        dont_rename_native_bindings = build_dont_rename_native_bindings(scope);
      },
      [&] { dont_rename_annotated = build_dont_rename_annotated(); }};

  workqueue_run<std::function<void()>>(
      [](const std::function<void()>& fn) { fn(); }, fns);

  std::string norule;

  auto on_class_renamable = [&](DexClass* clazz) {
    if (referenced_by_layouts(clazz)) {
      m_renamable_layout_classes.emplace(clazz->get_name());
    }
  };

  for (auto* clazz : scope) {
    // Short circuit force renames
    if (force_rename_hierarchies.count(clazz->get_type()) != 0u) {
      clazz->rstate.set_force_rename();
      on_class_renamable(clazz);
      continue;
    }

    // Don't rename annotations
    if (!rename_annotations && is_annotation(clazz)) {
      clazz->rstate.set_dont_rename();
      m_dont_rename_reasons[clazz] = {DontRenameReasonCode::Annotations,
                                      norule};
      continue;
    }

    // Don't rename types annotated with anything in dont_rename_annotated
    bool annotated = false;
    for (const auto& anno : UnorderedIterable(dont_rename_annotated)) {
      if (has_anno(clazz, anno)) {
        clazz->rstate.set_dont_rename();
        m_dont_rename_reasons[clazz] = {DontRenameReasonCode::Annotated,
                                        anno->str_copy()};
        annotated = true;
        break;
      }
    }
    if (annotated) {
      continue;
    }

    // Don't rename anything mentioned in resources. Two variants of checks here
    // to cover both configuration options (either we're relying on aapt to
    // compute resource reachability, or we're doing it ourselves).
    if (referenced_by_layouts(clazz) &&
        !is_allowed_layout_class(clazz, m_allow_layout_rename_packages)) {
      clazz->rstate.set_dont_rename();
      m_dont_rename_reasons[clazz] = {DontRenameReasonCode::Resources, norule};
      continue;
    }

    std::string strname = clazz->get_name()->str_copy();

    // Don't rename anythings in the direct name blocklist (hierarchy ignored)
    if (m_dont_rename_specific.count(strname) != 0u) {
      clazz->rstate.set_dont_rename();
      m_dont_rename_reasons[clazz] = {DontRenameReasonCode::Specific,
                                      std::move(strname)};
      continue;
    }

    // Don't rename anything if it falls in an excluded package
    bool package_blocklisted = false;
    for (const auto& pkg : m_dont_rename_packages) {
      if (strname.rfind("L" + pkg) == 0) {
        TRACE(RENAME, 2, "%s excluded by pkg rule %s", strname.c_str(),
              pkg.c_str());
        clazz->rstate.set_dont_rename();
        m_dont_rename_reasons[clazz] = {DontRenameReasonCode::Packages, pkg};
        package_blocklisted = true;
        break;
      }
    }
    if (package_blocklisted) {
      continue;
    }

    if (dont_rename_class_name_literals.count(strname) != 0u) {
      clazz->rstate.set_dont_rename();
      m_dont_rename_reasons[clazz] = {DontRenameReasonCode::ClassNameLiterals,
                                      norule};
      continue;
    }

    if (dont_rename_class_for_types_with_reflection.count(clazz->get_name()) !=
        0u) {
      clazz->rstate.set_dont_rename();
      m_dont_rename_reasons[clazz] = {
          DontRenameReasonCode::ClassForTypesWithReflection, norule};
      continue;
    }

    if (dont_rename_canaries.count(clazz->get_name()) != 0u) {
      clazz->rstate.set_dont_rename();
      m_dont_rename_reasons[clazz] = {DontRenameReasonCode::Canaries, norule};
      continue;
    }

    if (dont_rename_native_bindings.count(clazz->get_type()) != 0u) {
      clazz->rstate.set_dont_rename();
      m_dont_rename_reasons[clazz] = {DontRenameReasonCode::NativeBindings,
                                      norule};
      continue;
    }

    if (dont_rename_hierarchies.count(clazz->get_type()) != 0u) {
      const auto* rule = dont_rename_hierarchies[clazz->get_type()];
      clazz->rstate.set_dont_rename();
      m_dont_rename_reasons[clazz] = {DontRenameReasonCode::Hierarchy,
                                      rule->str_copy()};
      continue;
    }

    if (dont_rename_serde_relationships.count(clazz->get_type()) != 0u) {
      clazz->rstate.set_dont_rename();
      m_dont_rename_reasons[clazz] = {DontRenameReasonCode::SerdeRelationships,
                                      norule};
      continue;
    }

    if (!can_rename_if_also_renaming_xml(clazz)) {
      clazz->rstate.set_dont_rename();
      m_dont_rename_reasons[clazz] = {DontRenameReasonCode::ProguardCantRename,
                                      get_keep_rule(clazz)};
      continue;
    }

    // All above checks have passed, callback for a type which appears to be
    // renamable.
    on_class_renamable(clazz);
  }
}

/**
 * We re-evaluate a number of config rules again at pass running time.
 * The reason is that the types specified in those rules can be created in
 * previous Redex passes and did not exist when the initial evaluation happened.
 */
void RenameClassesPassV2::eval_classes_post(
    Scope& scope, const ClassHierarchy& class_hierarchy, PassManager& mgr) {
  Timer t("eval_classes_post");
  auto dont_rename_hierarchies =
      build_dont_rename_hierarchies(mgr, scope, class_hierarchy);
  for (auto* clazz : scope) {
    if (m_dont_rename_reasons.find(clazz) != m_dont_rename_reasons.end()) {
      continue;
    }

    std::string strname = clazz->get_name()->str_copy();

    // Don't rename anythings in the direct name blocklist (hierarchy ignored)
    if (m_dont_rename_specific.count(strname) != 0u) {
      m_dont_rename_reasons[clazz] = {DontRenameReasonCode::Specific,
                                      std::move(strname)};
      continue;
    }

    // Don't rename anything if it falls in an excluded package
    bool package_blocklisted = false;
    for (const auto& pkg : m_dont_rename_packages) {
      if (strname.rfind("L" + pkg) == 0) {
        TRACE(RENAME, 2, "%s excluded by pkg rule %s",
              str_copy(strname).c_str(), pkg.c_str());
        m_dont_rename_reasons[clazz] = {DontRenameReasonCode::Packages, pkg};
        package_blocklisted = true;
        break;
      }
    }
    if (package_blocklisted) {
      continue;
    }

    if (dont_rename_hierarchies.count(clazz->get_type()) != 0u) {
      const auto* rule = dont_rename_hierarchies[clazz->get_type()];
      m_dont_rename_reasons[clazz] = {DontRenameReasonCode::Hierarchy,
                                      rule->str_copy()};
      continue;
    }

    // Don't rename anything if something changed and the class cannot be
    // renamed anymore.
    if (!can_rename_if_also_renaming_xml(clazz)) {
      m_dont_rename_reasons[clazz] = {DontRenameReasonCode::ProguardCantRename,
                                      get_keep_rule(clazz)};
    }
  }
}

void RenameClassesPassV2::eval_pass(DexStoresVector& stores,
                                    ConfigFiles& conf,
                                    PassManager& mgr) {
  const auto& json = conf.get_json_config();
  json.get("apk_dir", "", m_apk_dir);
  TRACE(RENAME, 3, "APK Dir: %s", m_apk_dir.c_str());
  auto scope = build_class_scope(stores);
  ClassHierarchy class_hierarchy = build_type_hierarchy(scope);
  eval_classes(scope, class_hierarchy, conf, m_rename_annotations, mgr);
}

UnorderedSet<DexClass*> RenameClassesPassV2::get_renamable_classes(
    Scope& scope) {
  UnorderedSet<DexClass*> renamable_classes;
  for (auto* clazz : scope) {
    if (clazz->rstate.is_force_rename() ||
        (m_dont_rename_reasons.count(clazz) == 0u)) {
      renamable_classes.insert(clazz);
    }
  }
  return renamable_classes;
}

void RenameClassesPassV2::evolve_name_mapping(
    size_t digits,
    const DexClasses& dex,
    const UnorderedSet<DexClass*>& unrenamable_classes,
    rewriter::TypeStringMap* name_mapping,
    uint32_t* nextGlobalClassIndex) {
  for (size_t i = 0; i < dex.size(); i++) {
    auto* clazz = dex.at(i);
    if (unrenamable_classes.count(clazz) != 0u) {
      continue;
    }
    auto* dtype = clazz->get_type();
    const auto* oldname = dtype->get_name();

    uint32_t globalClassIndex =
        *nextGlobalClassIndex + static_cast<uint32_t>(i);
    std::array<char, Locator::encoded_global_class_index_max> array;
    char* descriptor = array.data();
    always_assert(globalClassIndex != Locator::invalid_global_class_index);
    Locator::encodeGlobalClassIndex(globalClassIndex, digits, descriptor);
    always_assert_log(facebook::Locator::decodeGlobalClassIndex(descriptor) ==
                          globalClassIndex,
                      "global class index didn't roundtrip; %s generated from "
                      "%u parsed to %u",
                      descriptor, globalClassIndex,
                      facebook::Locator::decodeGlobalClassIndex(descriptor));

    std::string prefixed_descriptor = prepend_package_prefix(descriptor);

    TRACE(RENAME, 3, "'%s' ->  %s (%u)'", oldname->c_str(),
          prefixed_descriptor.c_str(), globalClassIndex);

    const auto* dstring = DexString::make_string(prefixed_descriptor);
    name_mapping->add_type_name(oldname, dstring);
  }
  *nextGlobalClassIndex += dex.size();
}

UnorderedSet<DexClass*> RenameClassesPassV2::get_unrenamable_classes(
    Scope& scope,
    const UnorderedSet<DexClass*>& renamable_classes,
    PassManager& mgr) {
  UnorderedSet<DexClass*> unrenamable_classes;
  for (auto* clazz : scope) {
    auto* dtype = clazz->get_type();
    const auto* oldname = dtype->get_name();

    if (clazz->rstate.is_force_rename()) {
      TRACE(RENAME, 2, "Forced renamed: '%s'", oldname->c_str());
      mgr.incr_metric(METRIC_FORCE_RENAMED_CLASSES, 1);
    } else if (!clazz->rstate.is_renamable_initialized_and_renamable() ||
               clazz->rstate.is_generated()) {
      // Either cls is not renamble, or it is a Redex newly generated class.
      if (m_dont_rename_reasons.find(clazz) != m_dont_rename_reasons.end()) {
        auto reason = m_dont_rename_reasons[clazz];
        std::string metric = dont_rename_reason_to_metric(reason.code);
        mgr.incr_metric(metric, 1);
        if (dont_rename_reason_to_metric_per_rule(reason.code)) {
          std::string str = metric + "::" + std::string(reason.rule);
          mgr.incr_metric(str, 1);
          TRACE(RENAME, 2, "'%s' NOT RENAMED due to %s'", oldname->c_str(),
                str.c_str());
        } else {
          TRACE(RENAME, 2, "'%s' NOT RENAMED due to %s'", oldname->c_str(),
                metric.c_str());
        }
        always_assert(!renamable_classes.count(clazz));
        unrenamable_classes.insert(clazz);
        continue;
      }
    }

    always_assert(renamable_classes.count(clazz));
  }
  return unrenamable_classes;
}

rewriter::TypeStringMap RenameClassesPassV2::get_name_mapping(
    const DexStoresVector& stores,
    size_t digits,
    const UnorderedSet<DexClass*>& unrenamable_classes) {
  rewriter::TypeStringMap name_mapping;
  uint32_t nextGlobalClassIndex = 0;
  for (const auto& store : stores) {
    for (const auto& dex : store.get_dexen()) {
      evolve_name_mapping(digits, dex, unrenamable_classes, &name_mapping,
                          &nextGlobalClassIndex);
    }
  }
  return name_mapping;
}

ArtTypeLookupTable::ArtTypeLookupTable(
    uint32_t size, const std::vector<uint32_t>& initial_hashes) {
  uint32_t mask_bits = 1;
  while ((1u << mask_bits) < size) {
    mask_bits++;
  }
  m_mask = (1u << mask_bits) - 1;
  m_buckets.resize(m_mask + 1);

  UnorderedMap<uint32_t, uint32_t> entries; // Pos => NextDeltaPos
  entries.reserve(initial_hashes.size());
  std::vector<uint32_t> conflict_hashes;
  for (auto hash : initial_hashes) {
    auto insert_pos = GetPos(hash);
    if (entries.emplace(insert_pos, 0).second) {
      m_buckets[insert_pos] = true;
      continue;
    }
    conflict_hashes.push_back(hash);
  }
  TRACE(RENAME, 2,
        "Creating ArtTypeLookupTable for size: %u, mask_bits: %u, mask: %u, "
        "initial hashes: %zu, conflict_hashes: %zu",
        size, mask_bits, m_mask, initial_hashes.size(), conflict_hashes.size());
  for (auto hash : conflict_hashes) {
    auto tail_pos = GetPos(hash);
    auto* next_delta_pos = &entries.at(tail_pos);
    while (*next_delta_pos > 0) {
      tail_pos = (tail_pos + *next_delta_pos) & m_mask;
      next_delta_pos = &entries.at(tail_pos);
    }
    auto insert_pos = tail_pos;
    do {
      insert_pos = (insert_pos + 1) & m_mask;
    } while (!entries.emplace(insert_pos, 0).second);
    m_buckets[insert_pos] = true;
    *next_delta_pos = (insert_pos - tail_pos) & m_mask;
  }
}

bool ArtTypeLookupTable::has_bucket(uint32_t hash) const {
  return m_buckets[GetPos(hash)];
}

void ArtTypeLookupTable::insert(uint32_t hash) {
  always_assert(!m_buckets[GetPos(hash)]);
  m_buckets[GetPos(hash)] = true;
}

bool RenameClassesPassV2::evolve_name_mapping_avoiding_collisions(
    size_t digits,
    const DexClasses& dex,
    const UnorderedSet<DexClass*>& unrenamable_classes,
    uint32_t index_end,
    rewriter::TypeStringMap* name_mapping,
    uint32_t* next_index,
    std::set<uint32_t>* skipped_indices,
    size_t* avoided_collisions) {
  // We add a new type look-up table and pre-initialize it with all unrenamable
  // class name hashes. We'll later only use renamed class names whose immediate
  // buckets are not yet used, as to not interfere with the collision bucket
  // assignment of the unrenamable classes class names.
  std::vector<uint32_t> initial_hashes;
  for (auto* clazz : dex) {
    if (unrenamable_classes.count(clazz) != 0u) {
      int32_t java_hash = clazz->get_name()->java_hashcode();
      initial_hashes.push_back(static_cast<uint32_t>(java_hash));
    }
  }
  ArtTypeLookupTable current_table(static_cast<uint32_t>(dex.size()),
                                   initial_hashes);

  std::set<uint32_t> collision_indices;
  auto skipped_indices_it = skipped_indices->begin();
  for (auto* clazz : dex) {
    if (unrenamable_classes.count(clazz) != 0u) {
      continue;
    }

    auto* dtype = clazz->get_type();
    const auto* oldname = dtype->get_name();

    std::array<char, Locator::encoded_global_class_index_max> array;
    char* descriptor = array.data();
    std::string prefixed_descriptor;
    while (true) {
      uint32_t index;
      if (skipped_indices_it != skipped_indices->end()) {
        index = *skipped_indices_it;
        skipped_indices_it = skipped_indices->erase(skipped_indices_it);
      } else {
        index = (*next_index)++;
        if (index == index_end) {
          return false;
        }
      }

      always_assert(index != Locator::invalid_global_class_index);
      Locator::encodeGlobalClassIndex(index, digits, descriptor);
      always_assert_log(
          facebook::Locator::decodeGlobalClassIndex(descriptor) == index,
          "global class index didn't roundtrip; %s generated from "
          "%u parsed to %u",
          descriptor, index,
          facebook::Locator::decodeGlobalClassIndex(descriptor));

      prefixed_descriptor = prepend_package_prefix(descriptor);
      int32_t java_hash =
          java_hashcode_of_utf8_string(prefixed_descriptor.c_str());
      uint32_t hash = static_cast<uint32_t>(java_hash);
      if (current_table.has_bucket(hash)) {
        TRACE(RENAME, 2, "Avoided collision for '%s'",
              prefixed_descriptor.c_str());
        collision_indices.insert(index);
        continue;
      }
      current_table.insert(hash);
      break;
    }

    TRACE(RENAME, 3, "'%s' ->  %s (%u)'", oldname->c_str(),
          prefixed_descriptor.c_str(), *next_index);

    const auto* dstring = DexString::make_string(prefixed_descriptor);
    name_mapping->add_type_name(oldname, dstring);
  }

  TRACE(RENAME, 2,
        "Inserted %zu renamed classes while avoiding %zu collisions.",
        dex.size() - initial_hashes.size(), collision_indices.size());
  (*avoided_collisions) += collision_indices.size();
  skipped_indices->insert(collision_indices.begin(), collision_indices.end());
  return true;
}

rewriter::TypeStringMap
RenameClassesPassV2::get_name_mapping_avoiding_collisions(
    const DexStoresVector& stores,
    const UnorderedSet<DexClass*>& unrenamable_classes,
    size_t* digits,
    size_t* avoided_collisions,
    size_t* skipped_indices_count) {
  while (true) {
    always_assert_log(
        (*digits) <= Locator::global_class_index_digits_max,
        "exceeded maximum number of digits for global class index: %zu",
        *digits);

    uint32_t index_end = 1;
    for (size_t i = 0; i < *digits; i++) {
      index_end *= Locator::global_class_index_digits_base;
    }
    rewriter::TypeStringMap name_mapping;
    *avoided_collisions = 0;
    auto try_evolve_all_dexes = [&]() {
      uint32_t next_index = 0;
      std::set<uint32_t> skipped_indices;
      for (const auto& store : stores) {
        for (const auto& dex : store.get_dexen()) {
          if (!store.is_root_store()) {
            // VoltronModuleMetadataHelper has certain assumptions about the
            // consecutiveness of the global class indices for non-root stores,
            // so we are not doing anything fancy here.
            if (next_index + dex.size() > index_end) {
              return false;
            }
            evolve_name_mapping(*digits, dex, unrenamable_classes,
                                &name_mapping, &next_index);
          } else if (!evolve_name_mapping_avoiding_collisions(
                         *digits, dex, unrenamable_classes, index_end,
                         &name_mapping, &next_index, &skipped_indices,
                         avoided_collisions)) {
            return false;
          }
        }
      }
      *skipped_indices_count = skipped_indices.size();
      return true;
    };
    if (try_evolve_all_dexes()) {
      return name_mapping;
    }
    ++(*digits);
    TRACE(RENAME, 1, "Increasing digits to %zu", *digits);
  }
}

void RenameClassesPassV2::rename_classes(
    Scope& scope,
    const rewriter::TypeStringMap& name_mapping,
    PassManager& mgr) {
  const auto& class_map = name_mapping.get_class_map();
  for (auto* clazz : scope) {
    auto* dtype = clazz->get_type();
    const auto* oldname = dtype->get_name();
    auto it = class_map.find(oldname);
    if (it == class_map.end()) {
      continue;
    }
    const auto* dstring = it->second;
    dtype->set_name(dstring);
    m_base_strings_size += oldname->size();
    m_ren_strings_size += dstring->size();

    while (true) {
      std::string arrayop("[");
      arrayop += oldname->str();
      oldname = DexString::get_string(arrayop);
      if (oldname == nullptr) {
        break;
      }
      auto* arraytype = DexType::get_type(oldname);
      if (arraytype == nullptr) {
        break;
      }
      std::string newarraytype("[");
      newarraytype += dstring->str();
      dstring = DexString::make_string(newarraytype);
      arraytype->set_name(dstring);
    }
  }
  /* Now rewrite all const-string strings for force renamed classes. */
  rewriter::TypeStringMap force_rename_map;
  for (const auto& pair : UnorderedIterable(name_mapping.get_class_map())) {
    auto* type = DexType::get_type(pair.first);
    if (type == nullptr) {
      continue;
    }
    auto* clazz = type_class(type);
    if ((clazz != nullptr) && clazz->rstate.is_force_rename()) {
      force_rename_map.add_type_name(pair.first, pair.second);
    }
  }
  auto updated_instructions =
      rewriter::rewrite_string_literal_instructions(scope, force_rename_map);
  mgr.incr_metric(METRIC_REWRITTEN_CONST_STRINGS, updated_instructions);

  /* Now we need to re-write the Signature annotations.  They use
   * Strings rather than Type's, so they have to be explicitly
   * handled.
   */
  rewrite_dalvik_annotation_signature(scope, name_mapping);

  rename_classes_in_layouts(name_mapping, mgr);

  sanity_check(scope, name_mapping);
}

void RenameClassesPassV2::rename_classes_in_layouts(
    const rewriter::TypeStringMap& name_mapping, PassManager& /*mgr*/) {
  // Sync up ResStringPool entries in XML layouts. Class names should appear
  // in their "external" name, i.e. java.lang.String instead of
  // Ljava/lang/String;
  std::map<std::string, std::string> rename_map_for_layouts;
  for (auto&& [old_name, new_name] :
       UnorderedIterable(name_mapping.get_class_map())) {
    // Application should be configuring specific packages/class names to
    // prevent collisions/accidental rewrites of unrelated xml
    // elements/attributes/values; filter the given map to only be known View
    // classes.
    if (m_renamable_layout_classes.count(old_name) > 0) {
      rename_map_for_layouts.emplace(
          java_names::internal_to_external(old_name->str()),
          java_names::internal_to_external(new_name->str()));
    }
  }
  auto resources = create_resource_reader(m_apk_dir);
  resources->rename_classes_in_layouts(rename_map_for_layouts);
}

std::string RenameClassesPassV2::prepend_package_prefix(
    const char* descriptor) {
  always_assert_log(*descriptor == 'L',
                    "Class descriptor \"%s\" did not start with L!\n",
                    descriptor);
  descriptor++; // drop letter 'L'

  std::stringstream ss;
  ss << "L" << m_package_prefix << descriptor;
  return ss.str();
}

UnorderedSet<DexClass*> RenameClassesPassV2::get_renamable_classes(
    Scope& scope, ConfigFiles& /*conf*/, PassManager& mgr) {
  ClassHierarchy class_hierarchy = build_type_hierarchy(scope);
  eval_classes_post(scope, class_hierarchy, mgr);

  always_assert_log(scope.size() <
                        std::pow(Locator::global_class_index_digits_base,
                                 Locator::global_class_index_digits_max),
                    "scope size %zu too large", scope.size());
  mgr.incr_metric(METRIC_CLASSES_IN_SCOPE, scope.size());

  return get_renamable_classes(scope);
}

void RenameClassesPassV2::run_pass(DexStoresVector& stores,
                                   ConfigFiles& conf,
                                   PassManager& mgr) {
  auto scope = build_class_scope(stores);

  // encode the whole sequence as base 62: [0 - 9], [A - Z], [a - z]
  auto digits =
      (size_t)std::ceil(std::log(scope.size()) /
                        std::log(Locator::global_class_index_digits_base));
  TRACE(RENAME, 1,
        "Total classes in scope for renaming: %zu chosen number of digits: %zu",
        scope.size(), digits);

  auto renamable_classes = get_renamable_classes(scope, conf, mgr);
  auto unrenamable_classes =
      get_unrenamable_classes(scope, renamable_classes, mgr);

  auto avoid_type_lookup_table_collisions =
      m_avoid_type_lookup_table_collisions;

  size_t avoided_collisions = 0;
  size_t skipped_indices = 0;
  auto name_mapping =
      avoid_type_lookup_table_collisions
          ? get_name_mapping_avoiding_collisions(stores, unrenamable_classes,
                                                 &digits, &avoided_collisions,
                                                 &skipped_indices)
          : get_name_mapping(stores, digits, unrenamable_classes);

  if (avoid_type_lookup_table_collisions) {
    TRACE(RENAME, 1, "Avoided collisions: %zu, skipped indices: %zu",
          avoided_collisions, skipped_indices);
    mgr.incr_metric(METRIC_AVOIDED_COLLISIONS, avoided_collisions);
    mgr.incr_metric(METRIC_SKIPPED_INDICES, skipped_indices);
  }

  for (auto [_, dstring] : UnorderedIterable(name_mapping.get_class_map())) {
    always_assert_log(!DexType::get_type(dstring),
                      "Type name collision detected. %s already exists.",
                      dstring->c_str());
  }

  mgr.incr_metric(METRIC_RENAMED_CLASSES, name_mapping.get_class_map().size());

  rename_classes(scope, name_mapping, mgr);

  mgr.incr_metric(METRIC_DIGITS, digits);

  TRACE(RENAME, 1, "String savings, at least %u-%u = %u bytes ",
        m_base_strings_size, m_ren_strings_size,
        m_base_strings_size - m_ren_strings_size);
}
