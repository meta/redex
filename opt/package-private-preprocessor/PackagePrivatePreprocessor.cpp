/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

/*
 * Before Android 4.1, Dalvik did not honor package-private accessibility
 * restrictions when constructing vtables, see
 * https://developer.android.com/guide/practices/verifying-apps-art#Object_Model_Changes
 *
 * The original design of Redex somewhat reflected this attitude, not giving
 * proper considerations for package-private access rules. In particular, the
 * MethodOverrideGraph, the VirtualScope facitities, the RenameClasses*
 * transformation, but also many other aspects in Redex basically assume that
 * all members are public. For all internal classes, those assumptions are
 * largely "made true" by the aptly named MakePublicPass. However, there are a
 * few semantic problems, such as the following:
 * - By making everything public, the MakePublicPass may truely establish
 *   overriding relationships between methods that, due to original limited
 *   package private access, shouldn't actually be in an overriding
 *   relationship.
 * - By changing the package name of classes to just X, the RenameClasses*
 *   passes may break package-private access.
 *
 * This pass aims at working out those issues by performing certain
 * transformations upfront:
 * - For apparent overrides that are not actually overrides because of
 *   package-private access and different package names, we treat those as new
 *   virtual scope roots, and rename all involved methods uniquely.
 * - Where actual accesses to package private members occur, we make
 *   the members public, effectively making all accesses public accesses, so
 *   that existing Redex' optimizations are free to move around code and rename
 *   packages, and don't have to worry about package-private access rules.
 *
 * There are few limitations to this approach:
 * - New virtual scopes might implement interfaces, in which case renaming the
 *   methods might break the interface. We currently just give up, stopping
 *   Redex. (TODO: We could still handle this in some cases, renaming also
 *   interface methods, and possibly introducing some bridge methods.)
 * - Some public methods might override multiple (formerly package private)
 *   virtual roots. We don't currently support this.
 * - Some methods might be marked as do-not-rename.
 *
 * We don't currently hit any of those limitations.
 *
 * With these transformations, the MakePublicPass should no longer needed for
 * fixing up package private accesses (but it might still be needed to fix up
 * other effects of Redex transformation on visibility)
 */

#include "PackagePrivatePreprocessor.h"

#include <cinttypes>

#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexUtil.h"
#include "IROpcode.h"
#include "MethodOverrideGraph.h"
#include "PassManager.h"
#include "Resolver.h"
#include "Show.h"
#include "Trace.h"
#include "TypeUtil.h"
#include "Walkers.h"

namespace mog = method_override_graph;

namespace {
const DexString* gen_new_name(std::string_view org_name, size_t seed) {
  std::string name(org_name);
  name.append("$REDEX$PPP$");
  while (seed != 0u) {
    auto d = static_cast<int>(seed % 62);
    if (d < 10) {
      name.push_back(static_cast<char>(d + '0'));
    } else if (d < 36) {
      name.push_back(static_cast<char>(d - 10 + 'a'));
    } else {
      name.push_back(static_cast<char>(d - 36 + 'A'));
    }
    seed /= 62;
  }
  return DexString::make_string(name);
}

size_t hash_type(DexType* type) {
  size_t seed = 0;
  boost::hash_combine(seed, type->str());
  return seed;
}

// Given a non-interface method, find the (unique) non-interface (apparent)
// parent, if any. This does NOT take into account visibility, in particular
// package-private visibility.
const DexMethod* get_parent(const mog::Graph& graph, const DexMethod* method) {
  always_assert(!is_interface(type_class(method->get_class())));
  const auto& node = graph.get_node(method);
  for (auto* parent : UnorderedIterable(node.parents)) {
    if (parent->is_interface) {
      continue;
    }
    return parent->method;
  }
  return nullptr;
}

// Given a non-interface method, find the (unique) non-interface true parent, if
// any. This takes into account visibility, in particular package-private
// visibility.
const DexMethod* get_true_parent(const mog::Graph& graph,
                                 const DexMethod* method) {
  for (const auto* parent = get_parent(graph, method); parent != nullptr;) {
    if (is_public(parent) || is_protected(parent)) {
      return parent;
    }
    always_assert(is_package_private(parent));
    auto* parent_class = parent->get_class();
    if (type::same_package(parent_class, method->get_class()) &&
        !parent->is_external()) {
      return parent;
    }
    parent = get_parent(graph, parent);
  }
  return nullptr;
}

// Given a non-interface method, find the set of non-interface true roots, where
// each root spawns a virtual scope. This takes into account visibility, in
// particular package-private visibility. Note that a protected or public
// overriding method may have multiple package-private roots.
UnorderedSet<const DexMethod*> get_true_roots(const mog::Graph& graph,
                                              const DexMethod* method) {
  std::stack<const DexMethod*> stack;
  for (const auto* m = method; m != nullptr; m = get_parent(graph, m)) {
    stack.push(m);
  }
  UnorderedMap<std::string_view, const DexMethod*> package_private_roots;
  const DexMethod* public_or_protected_root{nullptr};
  UnorderedSet<const DexMethod*> res;
  while (!stack.empty()) {
    const auto* m = stack.top();
    stack.pop();
    auto package_name = type::get_package_name(m->get_class());
    if (is_package_private(m)) {
      package_private_roots.emplace(package_name, m);
      continue;
    }
    always_assert(is_public(m) || is_protected(m));
    auto it = package_private_roots.find(package_name);
    if (it != package_private_roots.end()) {
      if (public_or_protected_root == nullptr) {
        public_or_protected_root = it->second;
      } else {
        res.emplace(it->second);
      }
      package_private_roots.erase(it);
    } else if (public_or_protected_root == nullptr) {
      public_or_protected_root = m;
    }
  }
  if (public_or_protected_root == nullptr) {
    auto package_name = type::get_package_name(method->get_class());
    res.insert(package_private_roots.at(package_name));
  } else {
    res.insert(public_or_protected_root);
  }
  return res;
}

PackagePrivatePreprocessorPass::Stats analyze_class(
    DexClass* cls,
    ConcurrentSet<DexClass*>* package_private_accessed_classes,
    ConcurrentSet<DexMethod*>* package_private_accessed_methods,
    ConcurrentSet<DexField*>* package_private_accessed_fields,
    std::ostringstream* illegal_internal_accesses_stream,
    std::mutex* illegal_internal_accesses_stream_mutex) {
  PackagePrivatePreprocessorPass::Stats stats;
  auto visit_type = [&](const DexType* type) {
    type = type::make_element_type_if_array(type);
    if (type::is_primitive(type)) {
      return;
    }
    auto* resolved = type_class(type);
    if (resolved == nullptr) {
      if (!type->str().starts_with("Ldalvik/annotation/")) {
        TRACE(PPP, 5, "[%s] unresolved type: %s", SHOW(cls), SHOW(resolved));
        stats.unresolved_types++;
      }
      return;
    }
    if (is_public(resolved)) {
      return;
    }
    if (!type::same_package(type, cls->get_type()) || resolved->is_external()) {
      if (resolved->is_external()) {
        TRACE(PPP, 4, "[%s] access to invisible external type: %s", SHOW(cls),
              SHOW(resolved));
        stats.external_inaccessible_types++;
      } else {
        std::lock_guard lock(*illegal_internal_accesses_stream_mutex);
        *illegal_internal_accesses_stream << "ERROR - access to invisible type "
                                          << show(resolved) << " in "
                                          << show(cls) << "!\n";
        stats.internal_inaccessible_types++;
      }
      return;
    }
    package_private_accessed_classes->insert(resolved);
  };
  auto visit_field = [&](DexFieldRef* field, FieldSearch fs,
                         DexMethod* caller = nullptr) {
    auto* resolved = resolve_field(field, fs);
    if (resolved == nullptr) {
      TRACE(PPP, 5, "[%s] unresolved field: %s", SHOW(cls), SHOW(resolved));
      stats.unresolved_fields++;
      return;
    }
    if (is_public(resolved)) {
      return;
    }
    if (is_private(resolved)) {
      if (resolved->is_external()) {
        TRACE(PPP, 4, "[%s] access to invisible external external field: %s",
              SHOW(cls), SHOW(resolved));
        stats.external_inaccessible_private_fields++;
      }
      return;
    }
    if (is_protected(resolved) &&
        type::is_subclass(resolved->get_class(), cls->get_type())) {
      return;
    }
    if (!type::same_package(resolved->get_class(), cls->get_type()) ||
        resolved->is_external()) {
      if (resolved->is_external()) {
        TRACE(PPP, 4, "[%s] access to invisible external field: %s", SHOW(cls),
              SHOW(resolved));
        stats.external_inaccessible_fields++;
      } else {
        std::lock_guard lock(*illegal_internal_accesses_stream_mutex);
        *illegal_internal_accesses_stream
            << "ERROR - access to invisible field " << show(resolved) << " in "
            << (caller != nullptr ? show(caller) : show(cls)) << "!\n";
        stats.internal_inaccessible_fields++;
      }
      return;
    }
    package_private_accessed_fields->insert(resolved);
  };
  auto visit_method = [&](DexMethodRef* method,
                          MethodSearch ms,
                          DexMethod* caller = nullptr) {
    if (type::is_array(method->get_class()) &&
        method->get_name()->str() == "clone") {
      return;
    }
    auto* resolved = resolve_method_deprecated(method, ms, caller);
    if ((resolved == nullptr) && ms == MethodSearch::Virtual) {
      resolved = resolve_method_deprecated(
          method, MethodSearch::InterfaceVirtual, caller);
      if (resolved != nullptr) {
        // We resolved to an interface method. Interface methods are always
        // public, and we don't have a visibility problem. Just log.
        TRACE(PPP, 6, "[%s] virtual method resolved to interface: %s",
              SHOW(cls), SHOW(resolved));
        return;
      }
    }
    if (resolved == nullptr) {
      TRACE(PPP, 5, "[%s] unresolved method: %s", SHOW(cls), SHOW(resolved));
      stats.unresolved_methods++;
      return;
    }
    if (is_public(resolved)) {
      return;
    }
    if (is_private(resolved)) {
      if (resolved->is_external()) {
        TRACE(PPP, 4, "[%s] access to invisible external method: %s", SHOW(cls),
              SHOW(resolved));
        stats.external_inaccessible_private_methods++;
      }
      return;
    }
    if (is_protected(resolved) &&
        type::is_subclass(resolved->get_class(), cls->get_type())) {
      return;
    }
    if (!type::same_package(resolved->get_class(), cls->get_type()) ||
        resolved->is_external()) {
      if (resolved->is_external()) {
        TRACE(PPP, 4, "[%s] access to invisible external method: %s", SHOW(cls),
              SHOW(resolved));
        stats.external_inaccessible_methods++;
      } else {
        std::lock_guard lock(*illegal_internal_accesses_stream_mutex);
        *illegal_internal_accesses_stream
            << "ERROR - access to invisible method " << show(resolved) << " in "
            << (caller != nullptr ? show(caller) : show(cls)) << "!\n";
      }
      stats.internal_inaccessible_methods++;
      return;
    }
    package_private_accessed_methods->insert(resolved);
  };
  if (cls->get_super_class() != nullptr) {
    visit_type(cls->get_super_class());
  }
  for (auto* type : *cls->get_interfaces()) {
    visit_type(type);
  }
  walk::opcodes(
      std::vector<DexClass*>{cls},
      [](DexMethod*) { return true; },
      [&](DexMethod* caller, IRInstruction* insn) {
        if (insn->has_type()) {
          visit_type(insn->get_type());
        } else if (insn->has_field()) {
          auto fs = opcode::is_an_sfield_op(insn->opcode())
                        ? FieldSearch::Static
                        : FieldSearch::Instance;
          visit_field(insn->get_field(), fs, caller);
        } else if (insn->has_method()) {
          auto ms = opcode_to_search(insn->opcode());
          visit_method(insn->get_method(), ms, caller);
        }
      });
  walk::annotations(std::vector<DexClass*>{cls}, [&](DexAnnotation* anno) {
    std::vector<const DexType*> types;
    anno->gather_types(types);
    for (const auto* type : types) {
      visit_type(type);
    }
    std::vector<DexFieldRef*> fields;
    anno->gather_fields(fields);
    for (auto* field : fields) {
      visit_field(field, FieldSearch::Any);
    }
    std::vector<DexMethodRef*> methods;
    anno->gather_methods(methods);
    for (auto* method : methods) {
      visit_method(method, MethodSearch::Any);
    }
  });
  return stats;
}

// We don't bother with interface-based miranda methods here, as we'll later
// filter out all interactions with interface methods, which we don't support at
// this time.
struct TrueVirtualScope {
  UnorderedSet<DexMethod*> methods;
  bool unsupported{false};
};

PackagePrivatePreprocessorPass::Stats analyze_graph(
    const Scope& scope,
    const mog::Graph& graph,
    ConcurrentSet<DexMethod*>* package_private_accessed_methods,
    ConcurrentMap<const DexMethod*, TrueVirtualScope>* true_virtual_scopes,
    ConcurrentMap<const DexMethod*, const DexMethod*>* true_virtual_roots,
    std::ostringstream* unsupported_stream) {
  PackagePrivatePreprocessorPass::Stats stats;
  walk::classes(scope, [&](DexClass* cls) {
    if (is_interface(cls)) {
      return;
    }
    for (auto* method : cls->get_vmethods()) {
      const auto* parent = get_parent(graph, method);
      if (parent == nullptr) {
        continue;
      }
      auto true_roots = get_true_roots(graph, method);
      always_assert(!true_roots.empty());
      bool unsupported = true_roots.size() > 1;
      for (const auto* true_root : UnorderedIterable(true_roots)) {
        true_virtual_scopes->update(true_root, [&](auto*, auto& vs, auto) {
          vs.methods.insert(method);
          if (unsupported) {
            vs.unsupported = true;
          }
        });
        true_virtual_roots->emplace(method, true_root);
      }

      if (unsupported) {
        *unsupported_stream << "  Semantics will change! Cannot handle "
                               "overriding multiple package-private roots. "
                            << show(method) << " overrides ";
        auto ordered_true_roots =
            unordered_to_ordered(true_roots, compare_dexmethods);
        for (const auto* root : ordered_true_roots) {
          *unsupported_stream << show(root) << ", ";
        }
        *unsupported_stream << "\n";
        stats.unsupported_multiple_package_private_overrides++;
      }

      const auto* true_parent = get_true_parent(graph, method);
      if (true_parent == nullptr) {
        continue;
      }

      if (is_package_private(true_parent)) {
        package_private_accessed_methods->insert(
            const_cast<DexMethod*>(true_parent));
        stats.override_package_private_methods++;
        TRACE(PPP, 4, "[%s] package private override: %s", SHOW(method),
              SHOW(true_parent));
      }

      if (parent == true_parent) {
        continue;
      }

      stats.apparent_override_inaccessible_methods++;
      TRACE(PPP, 3, "[%s] apparent override: %s; true parent: %s", SHOW(method),
            SHOW(parent), SHOW(true_parent));
    }
  });
  return stats;
}

PackagePrivatePreprocessorPass::Stats transform(
    const Scope& scope,
    const mog::Graph& graph,
    const ConcurrentSet<DexClass*>& package_private_accessed_classes,
    const ConcurrentSet<DexMethod*>& package_private_accessed_methods,
    const ConcurrentSet<DexField*>& package_private_accessed_fields,
    const ConcurrentMap<const DexMethod*, TrueVirtualScope>&
        true_virtual_scopes,
    const ConcurrentMap<const DexMethod*, const DexMethod*>& true_virtual_roots,
    std::ostringstream* unsupported_stream) {
  PackagePrivatePreprocessorPass::Stats stats;

  // Make public all classes that are accessed via package-private accessibility
  // so that we can rename the packages.
  for (auto* cls : UnorderedIterable(package_private_accessed_classes)) {
    set_public(cls);
    stats.publicized_classes++;
  }

  // Make public all methods that are accessed via package-private accessibility
  // so that we can rename the packages.
  auto publicize_method = [&](auto* method) {
    if (!is_public(method)) {
      set_public(method);
      stats.publicized_methods++;
    }
  };
  UnorderedSet<const DexMethod*> roots_to_publicize;
  for (auto* method : UnorderedIterable(package_private_accessed_methods)) {
    auto it = true_virtual_roots.find(method);
    if (it != true_virtual_roots.end()) {
      roots_to_publicize.insert(it->second);
    } else {
      publicize_method(method);
    }
  }
  for (const auto* root : UnorderedIterable(roots_to_publicize)) {
    const auto& methods = true_virtual_scopes.at(root).methods;
    for (auto* method : UnorderedIterable(methods)) {
      publicize_method(method);
    }
  }

  // Make public all fields that are accessed via package-private accessibility
  // so that we can rename the packages.
  for (auto* field : UnorderedIterable(package_private_accessed_fields)) {
    set_public(field);
    stats.publicized_fields++;
  }

  UnorderedSet<const DexMethod*> new_true_virtual_scopes;
  UnorderedSet<const DexMethod*> new_true_virtual_scopes_methods;
  for (auto&& [root, vs] : UnorderedIterable(true_virtual_scopes)) {
    if (get_parent(graph, root) == nullptr) {
      // not a new root
      continue;
    }
    if (vs.unsupported) {
      continue;
    }
    new_true_virtual_scopes.insert(root);
    insert_unordered_iterable(new_true_virtual_scopes_methods, vs.methods);
  }
  stats.new_virtual_scope_roots =
      static_cast<int>(new_true_virtual_scopes.size());

  ConcurrentSet<const DexMethod*> may_be_interface_implementors;
  workqueue_run<const DexMethod*>(
      [&](const DexMethod* method) {
        auto is_interface_method = [&](const auto* m) {
          return is_interface(type_class(m->get_class()));
        };
        always_assert(!is_interface_method(method));
        if (mog::any_overriding_methods(graph, method, is_interface_method,
                                        /* include_interfaces */ true) ||
            mog::any_overridden_methods(graph, method, is_interface_method,
                                        /* include_interfaces */ true)) {
          may_be_interface_implementors.insert(method);
        }
      },
      new_true_virtual_scopes_methods);

  UnorderedBag<DexMethod*> methods_to_rename;
  UnorderedMap<DexMethod*, const DexString*> new_names;
  // Give unique names to all virtual scopes that apparently override
  // package-private methods, but truely don't. There might be cases where this
  // isn't possible; we can only report those.
  for (const auto* root : UnorderedIterable(new_true_virtual_scopes)) {
    const auto& methods = true_virtual_scopes.at_unsafe(root).methods;
    const auto* new_name =
        gen_new_name(root->get_name()->str(), hash_type(root->get_class()));
    TRACE(PPP, 1, "New virtual scope of size %zu with root %s for: %s",
          methods.size(), new_name->c_str(), SHOW(root));
    bool cannot_rename = false;
    for (auto* method : UnorderedIterable(methods)) {
      always_assert(!method->is_external());
      always_assert(!is_interface(type_class(method->get_class())));
      if (!can_rename(method)) {
        *unsupported_stream << "  Semantics will change! Cannot fix "
                               "package-private overriding as "
                               "the following method is not renamable: "
                            << SHOW(method) << "\n";
        cannot_rename = true;
        stats.unsupported_unrenamable_methods++;
      }
      if (may_be_interface_implementors.count_unsafe(method) != 0u) {
        // TODO: Maybe we can rename more here.
        *unsupported_stream
            << "  Semantics will change! Cannot fix package-private overriding "
               "as  the following method may implement an interface method: "
            << SHOW(method) << "\n";
        cannot_rename = true;
        stats.unsupported_interface_implementations++;
      }
    }
    if (cannot_rename) {
      continue;
    }
    if (!is_public(root)) {
      set_public(const_cast<DexMethod*>(root));
      stats.publicized_methods++;
    }

    for (auto* method : UnorderedIterable(methods)) {
      methods_to_rename.insert(method);
      new_names.emplace(method, new_name);
    }
  }

  ConcurrentMap<IRInstruction*, DexMethod*> insns_to_update;
  walk::parallel::opcodes(scope, [&](DexMethod*, IRInstruction* insn) {
    if (!insn->has_method()) {
      return;
    }
    auto* method = insn->get_method();
    auto* resolved = resolve_method_deprecated(method, opcode_to_search(insn));
    auto it = new_names.find(resolved);
    if (it == new_names.end()) {
      return;
    }
    insns_to_update.emplace(insn, resolved);
  });

  auto ordered_methods_to_rename =
      unordered_to_ordered(methods_to_rename, compare_dexmethods);
  for (auto* method : ordered_methods_to_rename) {
    const auto* new_name = new_names.at(method);
    always_assert(is_public(method));
    TRACE(PPP, 2, "  Renaming %s to %s", SHOW(method), new_name->c_str());
    DexMethodSpec spec;
    spec.name = new_name;
    method->change(spec, false /* rename on collision */);
  }
  stats.renamed_methods += static_cast<int>(ordered_methods_to_rename.size());

  workqueue_run<std::pair<IRInstruction*, DexMethod*>>(
      [&](const std::pair<IRInstruction*, DexMethod*>& p) {
        auto* insn = p.first;
        auto* resolved = p.second;
        const auto* new_name = new_names.at(resolved);
        auto* method = insn->get_method();
        auto* new_method = DexMethod::make_method(method->get_class(), new_name,
                                                  method->get_proto());
        insn->set_method(new_method);
      },
      insns_to_update);
  stats.updated_method_refs = static_cast<int>(insns_to_update.size());

  return stats;
}
} // namespace

void PackagePrivatePreprocessorPass::Stats::report(PassManager& mgr) {
#define REPORT(STAT)                                                        \
  do {                                                                      \
    mgr.incr_metric(#STAT, STAT);                                           \
    TRACE(PPP, 2, "  " #STAT ": %d/%" PRId64, STAT, mgr.get_metric(#STAT)); \
  } while (0)

  TRACE(PPP, 2, "PackagePrivatePreprocessorPass Stats:");

  REPORT(unresolved_types);
  REPORT(external_inaccessible_types);
  REPORT(internal_inaccessible_types);

  REPORT(unresolved_fields);
  REPORT(external_inaccessible_private_fields);
  REPORT(external_inaccessible_fields);
  REPORT(internal_inaccessible_fields);

  REPORT(unresolved_methods);
  REPORT(external_inaccessible_private_methods);
  REPORT(external_inaccessible_methods);
  REPORT(internal_inaccessible_methods);

  REPORT(apparent_override_inaccessible_methods);
  REPORT(override_package_private_methods);

  REPORT(package_private_accessed_classes);
  REPORT(package_private_accessed_methods);
  REPORT(package_private_accessed_fields);
  REPORT(new_virtual_scope_roots);

  REPORT(renamed_methods);
  REPORT(updated_method_refs);
  REPORT(publicized_classes);
  REPORT(publicized_methods);
  REPORT(publicized_fields);
  REPORT(unsupported_unrenamable_methods);
  REPORT(unsupported_interface_implementations);
  REPORT(unsupported_multiple_package_private_overrides);

  int unsupported = unsupported_unrenamable_methods +
                    unsupported_interface_implementations +
                    unsupported_multiple_package_private_overrides;
  if (unsupported > 0) {
    mgr.incr_metric("WARNING_UNSUPPORTED", unsupported);
  }
}

PackagePrivatePreprocessorPass::Stats&
PackagePrivatePreprocessorPass::Stats::operator+=(const Stats& that) {
  this->unresolved_types += that.unresolved_types;
  this->external_inaccessible_types += that.external_inaccessible_types;
  this->internal_inaccessible_types += that.internal_inaccessible_types;

  this->unresolved_fields += that.unresolved_fields;
  this->external_inaccessible_private_fields +=
      that.external_inaccessible_private_fields;
  this->external_inaccessible_fields += that.external_inaccessible_fields;
  this->internal_inaccessible_fields += that.internal_inaccessible_fields;

  this->unresolved_methods += that.unresolved_methods;
  this->external_inaccessible_private_methods +=
      that.external_inaccessible_private_methods;
  this->external_inaccessible_methods += that.external_inaccessible_methods;
  this->internal_inaccessible_methods += that.internal_inaccessible_methods;

  this->apparent_override_inaccessible_methods +=
      that.apparent_override_inaccessible_methods;
  this->override_package_private_methods +=
      that.override_package_private_methods;

  this->new_virtual_scope_roots += that.new_virtual_scope_roots;

  this->renamed_methods += that.renamed_methods;
  this->updated_method_refs += that.updated_method_refs;
  this->publicized_classes += that.publicized_classes;
  this->publicized_methods += that.publicized_methods;
  this->publicized_fields += that.publicized_fields;
  this->unsupported_unrenamable_methods += that.unsupported_unrenamable_methods;
  this->unsupported_interface_implementations +=
      that.unsupported_interface_implementations;
  this->unsupported_multiple_package_private_overrides +=
      that.unsupported_multiple_package_private_overrides;

  this->package_private_accessed_classes +=
      that.package_private_accessed_classes;
  this->package_private_accessed_methods +=
      that.package_private_accessed_methods;
  this->package_private_accessed_fields += that.package_private_accessed_fields;

  return *this;
}

void PackagePrivatePreprocessorPass::run_pass(DexStoresVector& stores,
                                              ConfigFiles& /* unused */,
                                              PassManager& mgr) {
  auto scope = build_class_scope(stores);
  auto graph = mog::build_graph(scope);

  ConcurrentSet<DexClass*> package_private_accessed_classes;
  ConcurrentSet<DexMethod*> package_private_accessed_methods;
  ConcurrentSet<DexField*> package_private_accessed_fields;
  std::ostringstream illegal_internal_accesses_stream;
  std::mutex illegal_internal_accesses_stream_mutex;
  m_stats = walk::parallel::classes<Stats>(scope, [&](DexClass* cls) {
    return analyze_class(cls, &package_private_accessed_classes,
                         &package_private_accessed_methods,
                         &package_private_accessed_fields,
                         &illegal_internal_accesses_stream,
                         &illegal_internal_accesses_stream_mutex);
  });
  TRACE(PPP, 1, "%s", illegal_internal_accesses_stream.str().c_str());
  always_assert_type_log(illegal_internal_accesses_stream.str().empty() ||
                             !m_fail_if_illegal_internal_refs,
                         RedexError::TYPE_CHECK_ERROR,
                         "Illegal input program:%s",
                         illegal_internal_accesses_stream.str().c_str());

  ConcurrentMap<const DexMethod*, TrueVirtualScope> true_virtual_scopes;
  ConcurrentMap<const DexMethod*, const DexMethod*> true_virtual_roots;
  std::ostringstream unsupported_stream;
  m_stats += analyze_graph(scope, *graph, &package_private_accessed_methods,
                           &true_virtual_scopes, &true_virtual_roots,
                           &unsupported_stream);

  m_stats += transform(scope, *graph, package_private_accessed_classes,
                       package_private_accessed_methods,
                       package_private_accessed_fields, true_virtual_scopes,
                       true_virtual_roots, &unsupported_stream);
  TRACE(PPP, 1, "%s", unsupported_stream.str().c_str());
  always_assert_type_log(unsupported_stream.str().empty() ||
                             !m_fail_if_unsupported_refs,
                         RedexError::TYPE_CHECK_ERROR, "Redex limitation:\n%s",
                         unsupported_stream.str().c_str());

  m_stats.report(mgr);
}

static PackagePrivatePreprocessorPass s_pass;
