/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <memory>
#include <string>

#include <vector>

#include "ClassUtil.h"
#include "ConfigFiles.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexStore.h"
#include "DexUtil.h"
#include "ProguardMap.h"
#include "ReachableClasses.h"
#include "Resolver.h"
#include "Show.h"
#include "SingleImpl.h"
#include "SingleImplDefs.h"
#include "Trace.h"
#include "Walkers.h"

namespace {

struct AnalysisImpl : SingleImplAnalysis {
  AnalysisImpl(const Scope& scope,
               const ProguardMap& pg_map,
               const DexStoresVector& stores,
               const ConfigFiles& conf)
      : scope(scope),
        pg_map(pg_map),
        xstores(stores, conf.normal_primary_dex()) {}

  void create_single_impl(const TypeMap& single_impl,
                          const TypeSet& intfs,
                          const SingleImplConfig& config);
  void collect_field_defs();
  void collect_method_defs();
  void analyze_opcodes();
  void escape_cross_stores();
  void remove_escaped();

 private:
  const DexType* get_and_check_single_impl(const DexType* type);
  void collect_children(const TypeSet& intfs);
  void check_impl_hierarchy();
  void escape_with_clinit();
  void escape_with_sfields();
  void filter_single_impl(const SingleImplConfig& config);
  void filter_proguard_special_interface();
  void filter_do_not_strip();
  void filter_list(const std::vector<std::string>& list, bool keep_match);
  void filter_by_annotations(const std::vector<std::string>& blocklist);

  const Scope& scope;
  const ProguardMap& pg_map;
  XStoreRefs xstores;
};

/**
 * Get the single impl if the type is a single impl or an array of it.
 * When an array mark the single impl as having an array type.
 * Return nullptr otherwise.
 */
const DexType* AnalysisImpl::get_and_check_single_impl(const DexType* type) {
  if (single_impls.count(type) != 0u) {
    return type;
  }
  if (type::is_array(type)) {
    auto* element_type = type::make_array_element_type(type);
    redex_assert(element_type);
    const auto sit = single_impls.find(element_type);
    if (sit != single_impls.end()) {
      escape_interface(sit->first, HAS_ARRAY_TYPE);
      return sit->first;
    }
  }
  return nullptr;
}

/**
 * Find all single implemented interfaces.
 */
void AnalysisImpl::create_single_impl(const TypeMap& single_impl,
                                      const TypeSet& intfs,
                                      const SingleImplConfig& config) {
  for (auto const& intf_it : UnorderedIterable(single_impl)) {
    const auto* intf = intf_it.first;
    auto* intf_cls = type_class(intf);
    always_assert(intf_cls && !intf_cls->is_external());
    if (is_annotation(intf_cls)) {
      continue;
    }
    const auto* impl = intf_it.second;
    auto* impl_cls = type_class(impl);
    always_assert(impl_cls && !impl_cls->is_external());
    if (is_annotation(impl_cls)) {
      continue;
    }
    single_impls[intf].cls = impl;
  }
  collect_children(intfs);
  check_impl_hierarchy();
  escape_with_clinit();
  escape_with_sfields();
  filter_single_impl(config);
  filter_do_not_strip();
}

/**
 * Filter common function for both white and black list.
 */
void AnalysisImpl::filter_list(const std::vector<std::string>& list,
                               bool keep_match) {
  if (list.empty()) {
    return;
  }

  auto find_in_list = [&](const std::string_view name) {
    for (const std::string& el_name : list) {
      if (name.compare(0, el_name.size(), el_name) == 0) {
        return true;
      }
    }
    return false;
  };

  for (const auto& intf_it : UnorderedIterable(single_impls)) {
    const auto* const intf = intf_it.first;
    auto* const intf_cls = type_class(intf);
    const auto intf_name = intf_cls->get_deobfuscated_name_or_empty();
    bool match = find_in_list(intf_name);
    if (match && keep_match) {
      continue;
    }
    if (!match && !keep_match) {
      continue;
    }
    escape_interface(intf, FILTERED);
  }
}

void AnalysisImpl::filter_proguard_special_interface() {
  for (const auto& intf_it : UnorderedIterable(single_impls)) {
    const auto* const intf = intf_it.first;
    auto* const intf_cls = type_class(intf);
    std::string intf_name = intf_cls->get_deobfuscated_name_or_empty_copy();
    if (pg_map.is_special_interface(intf_name)) {
      escape_interface(intf, FILTERED);
    }
  }
}

void AnalysisImpl::filter_by_annotations(
    const std::vector<std::string>& blocklist) {
  UnorderedSet<DexType*> anno_types;
  for (const auto& s : blocklist) {
    auto* ty = DexType::get_type(s);
    if (ty != nullptr) {
      anno_types.emplace(ty);
    }
  }

  for (const auto& intf_it : UnorderedIterable(single_impls)) {
    const auto* const intf = intf_it.first;
    auto* const intf_cls = type_class(intf);
    if (has_anno(intf_cls, anno_types)) {
      escape_interface(intf, FILTERED);
    }
  }
}

/**
 * Apply filters to the set of single impl found.
 * White lists come first, then black lists.
 */
void AnalysisImpl::filter_single_impl(const SingleImplConfig& config) {
  filter_list(config.allowlist, true);
  filter_list(config.package_allowlist, true);
  filter_list(config.blocklist, false);
  filter_list(config.package_blocklist, false);
  filter_by_annotations(config.anno_blocklist);
  // TODO(T33109158): Better way to eliminate VerifyError.
  if (config.filter_proguard_special_interfaces) {
    filter_proguard_special_interface();
  }
}

/**
 * Do not optimize DoNotStrip interfaces.
 */
void AnalysisImpl::filter_do_not_strip() {
  for (const auto& intf_it : UnorderedIterable(single_impls)) {
    if (!can_delete(type_class(intf_it.first))) {
      escape_interface(intf_it.first, DO_NOT_STRIP);
    }
  }
  walk::methods(scope, [this](DexMethod* method) {
    if (root(method)) {
      for (const auto* arg_type : *method->get_proto()->get_args()) {
        if (single_impls.count(arg_type) != 0u) {
          escape_interface(arg_type, DO_NOT_STRIP);
        }
      }
      if (single_impls.count(method->get_class()) != 0u) {
        escape_interface(method->get_class(), DO_NOT_STRIP);
      }
    }
  });
  walk::fields(scope, [this](DexField* field) {
    if (root(field)) {
      if (single_impls.count(field->get_type()) != 0u) {
        escape_interface(field->get_type(), DO_NOT_STRIP);
      }
      if (single_impls.count(field->get_class()) != 0u) {
        escape_interface(field->get_class(), DO_NOT_STRIP);
      }
    }
  });
}

/**
 * Collect direct children of interfaces.
 */
void AnalysisImpl::collect_children(const TypeSet& intfs) {
  for (const auto& intf : intfs) {
    for (const auto* super : *type_class(intf)->get_interfaces()) {
      auto super_it = single_impls.find(super);
      if (super_it != single_impls.end()) {
        super_it->second.children.insert(intf);
      }
    }
  }
}

/**
 * Escape if any parent is not known to redex.
 */
void AnalysisImpl::check_impl_hierarchy() {
  for (auto& intf_it : UnorderedIterable(single_impls)) {
    if (!klass::has_hierarchy_in_scope(type_class(intf_it.second.cls))) {
      escape_interface(intf_it.first, IMPL_PARENT_ESCAPED);
    }
  }
}

/**
 * Escape interfaces with static initializer.
 */
void AnalysisImpl::escape_with_clinit() {
  for (auto& intf_it : UnorderedIterable(single_impls)) {
    // strictly speaking this is not checking for a clinit but it's all the
    // same. Interfaces should not have static methods and even if so we
    // just escape them. From our analysis it turns out there are few with
    // clinit only and as expected none with static methods.
    if (!type_class(intf_it.first)->get_dmethods().empty()) {
      escape_interface(intf_it.first, CLINIT);
    }
  }
}

/**
 * Escape interfaces with static fields. Also escape the type of the field
 * if it is a single impl.
 * Interface fields may not be scoped to the interface itself and resolved
 * at runtime. So until we have an analysis that can spot those cases we
 * give up on interfaces with fields and the type of the field if it is
 * a single impl.
 */
void AnalysisImpl::escape_with_sfields() {
  for (auto const& intf_it : UnorderedIterable(single_impls)) {
    auto* intf_cls = type_class(intf_it.first);
    redex_assert(CONSTP(intf_cls)->get_ifields().empty());
    always_assert(!intf_cls->is_external());
    const auto& sfields = intf_cls->get_sfields();
    if (sfields.empty()) {
      continue;
    }
    escape_interface(intf_it.first, HAS_SFIELDS);
    for (auto* sfield : sfields) {
      auto* ftype = sfield->get_class();
      const auto* simpl = get_and_check_single_impl(ftype);
      if (simpl != nullptr) {
        escape_interface(simpl, HAS_SFIELDS);
      }
    }
  }
}

/**
 * If an interface in a store brings a class in a later store drop the
 * optimization.
 */
void AnalysisImpl::escape_cross_stores() {
  for (auto const& intf_it : UnorderedIterable(single_impls)) {
    if (xstores.illegal_ref(intf_it.first, intf_it.second.cls)) {
      escape_interface(intf_it.first, CROSS_STORES);
      continue;
    }
    // Be conservative: it is possible that the class has cross-store
    // references itself. Replacing the interface might increase the
    // chances of that blowing up.
    auto* cls = type_class(intf_it.second.cls);
    if (cls != nullptr) {
      if (xstores.illegal_ref_load_types(intf_it.first, cls)) {
        escape_interface(intf_it.first, CROSS_STORES);
        static bool warned = false;
        if (!warned) {
          warned = true;
          TRACE(INTF, 0,
                "Found transitive cross store violation! For details, run with "
                "TRACE=INTF:1.");
        }
        TRACE(INTF, 1,
              "Warning: found %s which is by itself not a cross-store "
              "violation for %s but depends on other types that are!",
              SHOW(cls), SHOW(intf_it.first));
        continue;
      }
    }
  }
}

/**
 * Clean up the single impl map.
 */
void AnalysisImpl::remove_escaped() {
  unordered_erase_if(single_impls,
                     [](auto& p) { return p.second.is_escaped(); });
}

/**
 * Find all fields typed with the single impl interface.
 */
void AnalysisImpl::collect_field_defs() {
  walk::fields(scope, [&](DexField* field) {
    auto* type = field->get_type();
    const auto* intf = get_and_check_single_impl(type);
    if (intf != nullptr) {
      single_impls[intf].fielddefs.push_back(field);
    }
  });
}

/**
 * Find all methods with a single impl interface in their signature.
 * Also if a method with the interface in the signature is native mark the
 * interface as "escaped".
 */
void AnalysisImpl::collect_method_defs() {

  auto check_method_arg = [&](const DexType* type, DexMethod* method,
                              bool native) {
    const auto* intf = get_and_check_single_impl(type);
    if (intf == nullptr) {
      return;
    }
    if (native) {
      escape_interface(intf, NATIVE_METHOD);
    }
    single_impls[intf].methoddefs.insert(method);
  };

  walk::methods(scope, [&](DexMethod* method) {
    auto* proto = method->get_proto();
    bool native = is_native(method);
    check_method_arg(proto->get_rtype(), method, native);
    for (const auto* const it : *proto->get_args()) {
      check_method_arg(it, method, native);
    }
  });
}

/**
 * Find all opcodes that reference a single implemented interface in a typeref,
 * fieldref or methodref.
 */
void AnalysisImpl::analyze_opcodes() {
  auto register_reference = [](SingleImplData& si, DexMethod* referrer,
                               IRInstruction* insn,
                               const cfg::InstructionIterator& insn_it) {
    auto& map = si.referencing_methods[referrer];
    auto [it, emplaced] = map.emplace(insn, insn_it);
    always_assert(emplaced || it->second == insn_it);
  };

  auto check_arg = [&](DexMethod* referrer,
                       const cfg::InstructionIterator& insn_it,
                       const DexType* type,
                       DexMethodRef* meth,
                       IRInstruction* insn) {
    const auto* intf = get_and_check_single_impl(type);
    if (intf != nullptr) {
      auto& si = single_impls.at(intf);
      std::lock_guard<std::mutex> lock(si.mutex);
      register_reference(si, referrer, insn, insn_it);
      si.methodrefs[meth].insert(insn);
    }
  };

  auto check_sig = [&](DexMethod* referrer,
                       const cfg::InstructionIterator& insn_it,
                       DexMethodRef* meth,
                       IRInstruction* insn) {
    // check the sig for single implemented interface
    auto* const proto = meth->get_proto();
    check_arg(referrer, insn_it, proto->get_rtype(), meth, insn);
    for (const auto* const arg : *proto->get_args()) {
      check_arg(referrer, insn_it, arg, meth, insn);
    }
  };

  auto check_field = [&](DexMethod* referrer,
                         const cfg::InstructionIterator& insn_it,
                         DexFieldRef* field,
                         IRInstruction* insn) {
    const auto* cls = field->get_class();
    cls = get_and_check_single_impl(cls);
    if (cls != nullptr) {
      escape_interface(cls, HAS_FIELD_REF);
    }
    auto* const type = field->get_type();
    const auto* intf = get_and_check_single_impl(type);
    if (intf != nullptr) {
      auto& si = single_impls.at(intf);
      std::lock_guard<std::mutex> lock(si.mutex);
      register_reference(si, referrer, insn, insn_it);
      si.fieldrefs[field].push_back(insn);
    }
  };

  auto check_return = [&](DexMethod* referrer,
                          const cfg::InstructionIterator& insn_it,
                          IRInstruction* insn) {
    auto* rtype = referrer->get_proto()->get_rtype();
    const auto* intf = get_and_check_single_impl(rtype);
    if (intf != nullptr) {
      auto& si = single_impls.at(intf);
      std::lock_guard<std::mutex> lock(si.mutex);
      register_reference(si, referrer, insn, insn_it);
    }
  };

  InsertOnlyConcurrentSet<const DexType*> const_class_types;
  walk::parallel::opcodes(scope,
                          [&](DexMethod* /*method*/, IRInstruction* insn) {
                            if (insn->opcode() == OPCODE_CONST_CLASS) {
                              const_class_types.insert(insn->get_type());
                            }
                          });
  // A coarse safety check: if intf is a single impl, and both it and its
  // implementor are involved in const-class instructions, this should be
  // considered unsafe (equality checks could be disrupted).
  auto implementor_used_as_const_class = [&](const DexType* intf) {
    auto search = single_impls.find(intf);
    if (search == single_impls.end()) {
      return false;
    }
    const auto* implementor = search->second.cls;
    return const_class_types.find(implementor) != const_class_types.end();
  };

  walk::parallel::code(scope, [&](DexMethod* method, IRCode& code) {
    redex_assert(code.cfg_built());
    auto ii = InstructionIterable(code.cfg());
    auto end = ii.end();
    for (auto it = ii.begin(); it != end; ++it) {
      auto* insn = it->insn;
      auto op = insn->opcode();
      switch (op) {
      // type ref
      case OPCODE_CONST_CLASS:
      case OPCODE_CHECK_CAST:
      case OPCODE_INSTANCE_OF:
      case OPCODE_NEW_INSTANCE:
      case OPCODE_NEW_ARRAY:
      case OPCODE_FILLED_NEW_ARRAY: {
        const auto* intf = get_and_check_single_impl(insn->get_type());
        if (intf != nullptr) {
          if (op == OPCODE_CONST_CLASS &&
              implementor_used_as_const_class(intf)) {
            escape_interface(intf, CONST_CLS);
          } else {
            auto& si = single_impls.at(intf);
            std::lock_guard<std::mutex> lock(si.mutex);
            register_reference(si, method, insn, it);
            si.typerefs.push_back(insn);
          }
        }
        break;
      }
      // field ref
      case OPCODE_IGET:
      case OPCODE_IGET_WIDE:
      case OPCODE_IGET_OBJECT:
      case OPCODE_IPUT:
      case OPCODE_IPUT_WIDE:
      case OPCODE_IPUT_OBJECT: {
        DexFieldRef* field =
            resolve_field(insn->get_field(), FieldSearch::Instance);
        if (field == nullptr) {
          field = insn->get_field();
        }
        check_field(method, it, field, insn);
        break;
      }
      case OPCODE_SGET:
      case OPCODE_SGET_WIDE:
      case OPCODE_SGET_OBJECT:
      case OPCODE_SPUT:
      case OPCODE_SPUT_WIDE:
      case OPCODE_SPUT_OBJECT: {
        DexFieldRef* field =
            resolve_field(insn->get_field(), FieldSearch::Static);
        if (field == nullptr) {
          field = insn->get_field();
        }
        check_field(method, it, field, insn);
        break;
      }
      // method ref
      case OPCODE_INVOKE_INTERFACE: {
        // if it is an invoke on the interface method, collect it as such
        auto* const meth = insn->get_method();
        auto* const owner = meth->get_class();
        const auto* const intf = get_and_check_single_impl(owner);
        if (intf != nullptr) {
          // if the method ref is not defined on the interface
          // itself drop the optimization
          const auto& meths = type_class(intf)->get_vmethods();
          if (std::find(meths.begin(), meths.end(), meth) == meths.end()) {
            escape_interface(intf, UNKNOWN_MREF);
          } else {
            auto& si = single_impls.at(intf);
            std::lock_guard<std::mutex> lock(si.mutex);
            register_reference(si, method, insn, it);
            si.intf_methodrefs[meth].insert(insn);
          }
        }
        check_sig(method, it, meth, insn);
        break;
      }

      case OPCODE_INVOKE_DIRECT:
      case OPCODE_INVOKE_STATIC:
      case OPCODE_INVOKE_VIRTUAL:
      case OPCODE_INVOKE_SUPER: {
        auto* const meth = insn->get_method();
        check_sig(method, it, meth, insn);
        break;
      }
      case OPCODE_RETURN_OBJECT: {
        check_return(method, it, insn);
        break;
      }
      default:
        break;
      }
    }
  });
}

} // namespace

/**
 * Main analysis method
 */
std::unique_ptr<SingleImplAnalysis> SingleImplAnalysis::analyze(
    const Scope& scope,
    const DexStoresVector& stores,
    const TypeMap& single_impl,
    const TypeSet& intfs,
    const ProguardMap& pg_map,
    const SingleImplConfig& config,
    const ConfigFiles& global_config) {
  std::unique_ptr<AnalysisImpl> single_impls(
      new AnalysisImpl(scope, pg_map, stores, global_config));
  single_impls->create_single_impl(single_impl, intfs, config);
  single_impls->collect_field_defs();
  single_impls->collect_method_defs();
  single_impls->analyze_opcodes();
  single_impls->escape_cross_stores();
  single_impls->remove_escaped();
  return std::move(single_impls);
}

void SingleImplAnalysis::escape_interface(const DexType* intf,
                                          EscapeReason reason) {
  auto sit = single_impls.find(intf);
  if (sit == single_impls.end()) {
    return;
  }
  if ((sit->second.escape & reason) != 0u) {
    return;
  }
  std::lock_guard<std::mutex> lock(sit->second.mutex);
  sit->second.escape |= reason;
  TRACE(INTF, 5, "(ESC) Escape %s => 0x%X", SHOW(intf), reason);
  auto* const intf_cls = type_class(intf);
  if (intf_cls != nullptr) {
    for (const auto* super_intf : *intf_cls->get_interfaces()) {
      escape_interface(super_intf, reason);
    }
  }
}

/**
 * Collect the interfaces to optimize for an optimization step.
 */
void SingleImplAnalysis::get_interfaces(TypeList& to_optimize) const {
  for (const auto& sit : UnorderedIterable(single_impls)) {
    const auto& data = sit.second;
    redex_assert(!data.is_escaped());
    if (data.children.empty()) {
      to_optimize.push_back(const_cast<DexType*>(sit.first));
    }
  }
  // make the optimizable list stable. It's extremely useful for debugging
  // and also avoids to get different optimizations on different runs on the
  // same apk.
  // Sort by vtable size and name
  std::sort(to_optimize.begin(),
            to_optimize.end(),
            [](const DexType* type1, const DexType* type2) {
              auto size1 = type_class(type1)->get_vmethods().size();
              auto size2 = type_class(type2)->get_vmethods().size();
              return size1 == size2 ? strcmp(type1->get_name()->c_str(),
                                             type2->get_name()->c_str()) < 0
                                    : size1 < size2;
            });
}
