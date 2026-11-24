/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "VirtualRenamer.h"

#include <set>

#include "ClassHierarchy.h"
#include "ConcurrentContainers.h"
#include "Debug.h"
#include "DexAccess.h"
#include "DexAnnotation.h"
#include "DexClass.h"
#include "DexUtil.h"
#include "ObfuscateUtils.h"
#include "Resolver.h"
#include "Show.h"
#include "Trace.h"
#include "TypeUtil.h"
#include "VirtualScopes.h"
#include "Walkers.h"

namespace {

/**
 * Legacy `can_rename_scope`: a scope is renamable only if it is not escaped (no
 * member's branch touches an unresolvable interface) and every member method
 * can be renamed.
 */
bool can_rename_scope(const virtual_scope::VirtualScope* scope) {
  if (scope->escaped()) {
    return false;
  }
  for (const auto* meth : scope->methods()) {
    if (!can_rename(meth)) {
      return false;
    }
  }
  return true;
}

/**
 * Find a method with the given (name, proto) in a class.
 */
DexMethod* find_method(const DexClass* cls,
                       const DexString* name,
                       const DexProto* proto) {
  for (const auto& vmeth : cls->get_vmethods()) {
    if (vmeth->get_name() == name && vmeth->get_proto() == proto) {
      return vmeth;
    }
  }
  return (DexMethod*)nullptr;
};

// keep a map from defs to all refs resolving to that def
using RefsMap =
    ConcurrentMap<DexMethod*, std::set<DexMethodRef*, dexmethods_comparator>>;

// Uncomment and use this as a prefix for virtual method
// names for debugging
// const std::string prefix = __Redex__";
const std::string prefix;

const DexString* get_name(int seed) {
  std::string name;
  obfuscate_utils::compute_identifier(seed, &name);
  if (!prefix.empty()) {
    name = prefix + name;
  }
  return DexString::make_string(name);
}

struct VirtualRenamer {
  VirtualRenamer(const virtual_scope::VirtualScopes& vscopes,
                 const ClassHierarchy& hierarchy,
                 const RefsMap& def_refs,
                 UnorderedMap<std::string, uint32_t>* elms,
                 UnorderedMap<const DexType*, std::string>* cache,
                 const UnorderedMap<const DexClass*, int>& next_dmethod_seeds)
      : vscopes(vscopes),
        hierarchy(hierarchy),
        def_refs(def_refs),
        stack_trace_elements(elms),
        external_name_cache(cache),
        next_dmethod_seeds(next_dmethod_seeds) {}

  int rename_virtual_scopes(const DexType* type, int& seed);
  int rename_interface_scopes(int& seed);

 private:
  const virtual_scope::VirtualScopes& vscopes;
  const ClassHierarchy& hierarchy;
  const RefsMap& def_refs;
  // When avoid_stack_trace_collision is true this is used to keep a ref count
  // of a given fully qualified method name (sans parameters); i.e. the line
  // that will be printed when the method appears in a stack trace (internally
  // in ART this is called a stack trace element). As methods are renamed
  // their ref counts get updated, and if the ref count drops to 0 then its
  // entry is erased. When avoid_stack_trace_collision is false then this is
  // null and collision avoidance is disabled.
  UnorderedMap<std::string, uint32_t>* stack_trace_elements;
  // Note these entries contain trailing periods
  UnorderedMap<const DexType*, std::string>* external_name_cache;
  const UnorderedMap<const DexClass*, int>& next_dmethod_seeds;
  mutable UnorderedMap<const virtual_scope::VirtualScope*, int>
      next_virtualscope_seeds;
  mutable UnorderedMap<const DexType*, TypeSet> hier_cache;

  const std::string& get_prefix(const DexType* type) const {
    always_assert(external_name_cache != nullptr);
    auto iter = external_name_cache->find(type);
    always_assert(iter != external_name_cache->end());
    return iter->second;
  }

  // Retrieves the next seed that won't overlap with dmethods, considering all
  // classes participating in the given virtual scope
  int get_next_virtualscope_seeds(
      const virtual_scope::VirtualScope* scope) const {
    auto it = next_virtualscope_seeds.find(scope);
    if (it != next_virtualscope_seeds.end()) {
      return it->second;
    }
    int seed = 0;
    for (const auto* m : scope->methods()) {
      auto it2 = next_dmethod_seeds.find(type_class(m->get_class()));
      if (it2 != next_dmethod_seeds.end()) {
        seed = std::max(seed, it2->second);
      }
    }
    next_virtualscope_seeds.emplace(scope, seed);
    return seed;
  }

  void rename(DexMethodRef* meth, const DexString* name);
  int rename_scope_ref(DexMethod* meth, const DexString* name);
  int rename_scope(const virtual_scope::VirtualScope* scope,
                   const DexString* name);

  const DexString* get_unescaped_name(
      const std::vector<const virtual_scope::VirtualScope*>& scopes,
      int& seed) const;
  const DexString* get_unescaped_name(const virtual_scope::VirtualScope* scope,
                                      int& seed) const;
  bool usable_name(const DexString* name,
                   const virtual_scope::VirtualScope* scope) const;
};

/**
 * Rename a given method with the given name.
 */
void VirtualRenamer::rename(DexMethodRef* meth, const DexString* name) {
  // redex_assert(meth->is_concrete() && !meth->is_external());
  DexMethodSpec spec;
  spec.cls = meth->get_class();
  spec.name = name;
  spec.proto = meth->get_proto();
  if (stack_trace_elements != nullptr) {
    std::string ste = get_prefix(meth->get_class()) + meth->str();
    auto iter = stack_trace_elements->find(ste);
    // We don't find this ste if it's a miranda method
    if (iter != stack_trace_elements->end()) {
      // We've found this ste, so let's decrement its ref count, and if it
      // reaches 0 then remove it so we don't have any empty entries
      iter->second -= 1;
      if (iter->second == 0) {
        stack_trace_elements->erase(iter);
      }
    }
  }
  meth->change(spec, false /* rename on collision */);

  if (stack_trace_elements != nullptr) {
    std::string ste = get_prefix(meth->get_class()) + name->str();
    auto res = stack_trace_elements->emplace(std::move(ste), 1);
    // Ideally we've picked a new name that doesn't collide with any other
    // method, so this assert should never fire. We leave this here in case
    // my human brain foobarred the logic (or in a refactor some other
    // assumption e.g. thread safety are changed)
    always_assert(res.second);
  }
}

/**
 * Rename all refs to the given method.
 */
int VirtualRenamer::rename_scope_ref(DexMethod* meth, const DexString* name) {
  int renamed = 0;
  const auto& refs = def_refs.find(meth);
  if (refs == def_refs.end()) {
    return renamed;
  }
  for (const auto& ref : refs->second) {
    rename(ref, name);
    renamed++;
  }
  return renamed;
}

/**
 * Rename an entire virtual scope.
 */
int VirtualRenamer::rename_scope(const virtual_scope::VirtualScope* scope,
                                 const DexString* name) {
  int renamed = 0;
  for (const auto* vmeth : scope->methods()) {
    rename(const_cast<DexMethod*>(vmeth), name);
    if (vmeth->is_concrete()) {
      renamed++;
    } else {
      TRACE(OBFUSCATE, 2, "not concrete %s", SHOW(vmeth));
    }
  }
  redex_assert(!scope->methods().empty());
  rename_scope_ref(const_cast<DexMethod*>(scope->top_def()), name);
  return renamed;
}

/**
 * A name is usable if it does not collide with an existing
 * one in the def and ref space.
 */
bool VirtualRenamer::usable_name(
    const DexString* name, const virtual_scope::VirtualScope* scope) const {
  const auto* const root = scope->root();
  auto it = hier_cache.find(root);
  if (it == hier_cache.end()) {
    auto hier = get_all_children(hierarchy, root);
    hier.insert(root);
    it = hier_cache.emplace(root, std::move(hier)).first;
  }
  const auto& hier = it->second;
  auto* const proto = scope->top_def()->get_proto();
  bool has_ste = stack_trace_elements != nullptr;
  for (const auto& type : hier) {
    if (DexMethod::get_method(type, name, proto) != nullptr) {
      return false;
    }
    if (has_ste) {
      auto ste = get_prefix(type) + name->str();
      if (stack_trace_elements->find(ste) != stack_trace_elements->end()) {
        return false;
      }
    }
  }
  return true;
}

/*
 * Operate on 'seed' and find a name for scope that does not
 * lead to any collision for all defs or refs.
 * * Update 'seed' *
 */
const DexString* VirtualRenamer::get_unescaped_name(
    const virtual_scope::VirtualScope* scope, int& seed) const {
  seed = std::max(seed, get_next_virtualscope_seeds(scope));
  const auto* name = get_name(seed++);
  while (!usable_name(name, scope)) {
    name = get_name(seed++);
  }
  return name;
}

/*
 * Operate on 'seed' and find a name for all scopes that does not
 * lead to any collision for all defs or refs.
 * * Update 'seed' *
 */
const DexString* VirtualRenamer::get_unescaped_name(
    const std::vector<const virtual_scope::VirtualScope*>& scopes,
    int& seed) const {
  // advance seed as necessary, skipping over dmethods
  for (const auto& scope : scopes) {
    seed = std::max(seed, get_next_virtualscope_seeds(scope));
  }
  while (true) {
    const auto* name = get_name(seed++);
    auto is_usable = [&]() {
      for (const auto& scope : scopes) {
        if (!usable_name(name, scope)) {
          return false;
        }
      }
      return true;
    }();
    if (!is_usable) {
      continue;
    }
    return name;
  }
}

int VirtualRenamer::rename_interface_scopes(int& seed) {
  int renamed = 0;
  vscopes.walk_interface_scopes(
      [&](const DexString* name,
          const DexProto* proto,
          const std::vector<const virtual_scope::VirtualScope*>& scopes,
          const TypeSet& intfs) {
        // if any scope cannot be renamed let it go, we don't
        // rename anything
        TRACE(OBFUSCATE, 5, "Got %zu scopes for %s%s", scopes.size(),
              SHOW(name), SHOW(proto));
        for (const auto& scope : scopes) {
          redex_assert(type_class(scope->root()) != nullptr);
          if (type_class(scope->root())->is_external()) {
            TRACE(OBFUSCATE, 5, "External impl scope %s",
                  SHOW(scope->top_def()));
            return;
          }
          if (!can_rename_scope(scope)) {
            TRACE(OBFUSCATE, 5, "Cannot rename impl scope %s",
                  SHOW(scope->top_def()));
            return;
          }
        }
        for (const auto& intf : intfs) {
          const auto& intf_cls = type_class(intf);
          if (intf_cls == nullptr) {
            TRACE(OBFUSCATE, 5, "No interface class %s", SHOW(intf));
            return;
          }
          if (intf_cls->is_external()) {
            TRACE(OBFUSCATE, 5, "External interface %s", SHOW(intf));
            return;
          }
        }
        // if any interface method that we are about to rename
        // cannot be renamed give up
        for (const auto& intf : intfs) {
          redex_assert(type_class(intf) != nullptr);
          auto* const meth = find_method(type_class(intf), name, proto);
          redex_assert(meth != nullptr);
          if (!can_rename(meth)) {
            TRACE(OBFUSCATE, 5, "Cannot rename %s", SHOW(meth));
            return;
          }
        }
        // all scopes can be renamed, go for it
        const auto* new_name = get_unescaped_name(scopes, seed);
        TRACE(OBFUSCATE, 5, "New name %s for %s%s", SHOW(new_name), SHOW(name),
              SHOW(proto));
        for (const auto& scope : scopes) {
          renamed += rename_scope(scope, new_name);
        }
        // rename interface method only
        for (const auto& intf : intfs) {
          auto* intf_cls = type_class(intf);
          redex_assert(intf_cls != nullptr);
          auto* intf_meth = find_method(intf_cls, name, proto);
          always_assert_log(intf_meth != nullptr,
                            "cannot find interface method for %s%s", SHOW(name),
                            SHOW(proto));
          TRACE(OBFUSCATE, 5, "New name %s for %s", SHOW(new_name),
                SHOW(intf_meth));
          rename(intf_meth, new_name);
          rename_scope_ref(intf_meth, new_name);
          renamed++;
        }
      });
  return renamed;
}

/**
 * Rename only scopes that are not interface and can_rename.
 */
int VirtualRenamer::rename_virtual_scopes(const DexType* type, int& seed) {
  int renamed = 0;
  auto* const cls = type_class(type);
  TRACE(OBFUSCATE, 5, "Attempting to rename %s", SHOW(type));
  // object or external classes are not renamable, move
  // to the children
  if (cls != nullptr && !cls->is_external()) {
    auto scopes_copy = vscopes.at(type);
    std::sort(scopes_copy.begin(), scopes_copy.end(),
              [&](const virtual_scope::VirtualScope* a,
                  const virtual_scope::VirtualScope* b) {
                // prefer scopes which have extra seed values available
                auto a_seed = std::max(seed, get_next_virtualscope_seeds(a));
                auto b_seed = std::max(seed, get_next_virtualscope_seeds(b));
                if (a_seed != b_seed) {
                  return a_seed < b_seed;
                }
                const auto* a_method = a->top_def();
                const auto* b_method = b->top_def();
                // then sort by scopes...
                if (a_method->get_proto() != b_method->get_proto()) {
                  return dexprotos_comparator()(a_method->get_proto(),
                                                b_method->get_proto());
                }
                // then by access...
                auto a_access =
                    a_method->is_def() ? (uint32_t)a_method->get_access() : 0;
                auto b_access =
                    b_method->is_def() ? (uint32_t)b_method->get_access() : 0;
                if (a_access != b_access) {
                  return a_access < b_access;
                }
                // otherwise, by root methods
                return dexmethods_comparator()(a_method, b_method);
              });
    // rename all scopes at this level that are not interface
    // and can be renamed
    TRACE(OBFUSCATE, 5, "Found %zu scopes in %s", scopes_copy.size(),
          SHOW(type));
    for (auto& scope : scopes_copy) {
      if (!can_rename_scope(scope)) {
        TRACE(OBFUSCATE, 5, "Cannot rename %s", SHOW(scope->top_def()));
        continue;
      }
      if (scope->implements_interface()) {
        TRACE(OBFUSCATE, 5, "Impl scope %s", SHOW(scope->top_def()));
        continue;
      }
      const auto* name = get_unescaped_name(scope, seed);
      TRACE(OBFUSCATE, 5, "New name %s for %s", SHOW(name),
            SHOW(scope->top_def()));
      renamed += rename_scope(scope, name);
    }
  }

  // will be used for interface renaming, effectively this
  // gets the last name (seed) for all virtual scopes and
  // interface are treated as all being at the same scope,
  // that is, they will all have different names irrespective
  // of where they are in the hierarchy
  int max_seed = seed;
  // recurse into children
  for (const auto& child : get_children(hierarchy, type)) {
    int base_seed = seed;
    renamed += rename_virtual_scopes(child, base_seed);
    max_seed = std::max(max_seed, base_seed);
  }
  seed = max_seed;
  return renamed;
}

/**
 * Collect all method refs to concrete methods (definitions).
 */
void collect_refs(Scope& scope, RefsMap& def_refs) {
  auto collect_ref = [&](DexMethodRef* callee) {
    if (callee->is_concrete()) {
      return;
    }
    auto* cls = type_class(callee->get_class());
    if (cls == nullptr || cls->is_external()) {
      return;
    }
    DexMethod* top = nullptr;
    if (is_interface(cls)) {
      top = resolve_method_deprecated(callee, MethodSearch::Interface);
    } else {
      top = find_top_impl(cls, callee->get_name(), callee->get_proto());
      if (top == nullptr) {
        TRACE(OBFUSCATE, 2, "Possible top miranda: %s", SHOW(callee));
        // see if it's a virtual call to an interface miranda method
        top = find_top_intf_impl(cls, callee->get_name(), callee->get_proto());
        if (top != nullptr) {
          TRACE(OBFUSCATE, 2, "Top miranda: %s", SHOW(top));
        }
      }
    }
    if (top == nullptr || top == callee) {
      return;
    }
    redex_assert(type_class(top->get_class()) != nullptr);
    if (type_class(top->get_class())->is_external()) {
      return;
    }
    // it's a top definition on an internal class, save it
    def_refs.update(top, [&](auto*, auto& set, bool) { set.insert(callee); });
  };
  walk::parallel::opcodes(
      scope, [](DexMethod*) { return true; },
      [&](DexMethod*, IRInstruction* insn) {
        for_each_invoke(insn,
                        [&](IROpcode /* opcode */, DexMethodRef* callee,
                            const DexMethodHandle* /* method_handle */) {
                          collect_ref(callee);
                        });
      });
  // The method handles that static field values and annotations hold call
  // methods too.
  auto collect_refs_of = [&](const Gatherable& value) {
    std::vector<DexMethodHandle*> method_handles;
    value.gather_methodhandles(method_handles);
    for (const auto* method_handle : method_handles) {
      if (DexMethodHandle::isInvokeType(method_handle->type())) {
        collect_ref(method_handle->methodref());
      }
    }
  };
  walk::parallel::fields(scope, [&](DexField* field) {
    if (auto* value = field->get_static_value()) {
      collect_refs_of(*value);
    }
  });
  walk::parallel::annotations(
      scope, [&](DexAnnotation* annotation) { collect_refs_of(*annotation); });
}

} // namespace

/**
 * Rename virtual methods.
 */
size_t rename_virtuals(
    Scope& scope,
    bool avoid_stack_trace_collision,
    const UnorderedMap<const DexClass*, int>& next_dmethod_seeds) {
  // build the VirtualScopes, a ClassHierarchy, a RefsMap and a VirtualRenamer
  virtual_scope::VirtualScopes vscopes(scope);
  ClassHierarchy hierarchy = build_type_hierarchy(scope);
  RefsMap def_refs;
  collect_refs(scope, def_refs);
  UnorderedMap<std::string, uint32_t> stack_trace_elements;
  UnorderedMap<const DexType*, std::string> external_cache;
  if (avoid_stack_trace_collision) {
    for (const auto& cls : scope) {
      std::string pref = java_names::internal_to_external(cls->str()) + ".";
      auto meths_visitor = [&](const std::vector<DexMethod*>& methods) {
        for (const DexMethod* method : methods) {
          std::string ste = pref + method->str();
          // We're 100% ok with the default construction of an entry here, since
          // after this line that would give said entry the correct ref count
          // of 1.
          stack_trace_elements[std::move(ste)] += 1;
        }
      };
      meths_visitor(cls->get_dmethods());
      meths_visitor(cls->get_vmethods());
      auto emp_res = external_cache.emplace(cls->get_type(), std::move(pref));
      always_assert(emp_res.second);
    }
  }
  VirtualRenamer vr(vscopes,
                    hierarchy,
                    def_refs,
                    avoid_stack_trace_collision ? &stack_trace_elements
                                                : nullptr,
                    avoid_stack_trace_collision ? &external_cache : nullptr,
                    next_dmethod_seeds);

  // rename virtual only first
  auto* const obj_t = type::java_lang_Object();
  int seed = 0;
  size_t renamed = vr.rename_virtual_scopes(obj_t, seed);
  TRACE(OBFUSCATE, 2, "Virtual renamed: %zu", renamed);

  // rename interfaces
  size_t intf_renamed = vr.rename_interface_scopes(seed);
  TRACE(OBFUSCATE, 2, "Interface renamed: %zu", intf_renamed);
  TRACE(OBFUSCATE, 2, "MAX seed: %d", seed);
  return renamed + intf_renamed;
}
