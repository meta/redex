/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "InitDeps.h"

#include <ostream>
#include <sstream>
#include <vector>

#include <sparta/WeakTopologicalOrdering.h>

#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexClass.h"
#include "DexMethodHandle.h"
#include "Resolver.h"
#include "Show.h"
#include "Timer.h"
#include "Trace.h"
#include "Walkers.h"

using namespace sparta;

namespace {

std::ostream& operator<<(std::ostream& o,
                         const sparta::WtoComponent<DexClass*>& c) {
  if (c.is_scc()) {
    o << "(" << show(c.head_node());
    for (const auto& sub : c) {
      o << " " << sub;
    }
    o << ")";
  } else {
    o << show(c.head_node());
  }
  return o;
}

auto compute_deps(const Scope& scope,
                  const UnorderedSet<const DexClass*>& scope_set) {
  InsertOnlyConcurrentMap<DexClass*, std::vector<DexClass*>> deps_parallel;
  ConcurrentMap<DexClass*, std::vector<DexClass*>> reverse_deps_parallel;
  ConcurrentSet<DexClass*> is_target;
  ConcurrentSet<DexClass*> maybe_roots;
  ConcurrentSet<DexClass*> all;
  walk::parallel::classes(scope, [&](DexClass* cls) {
    std::vector<DexClass*> deps_vec;
    auto add_dep = [&](auto* dependee_cls) {
      if (dependee_cls == nullptr || dependee_cls == cls ||
          scope_set.count(dependee_cls) == 0) {
        return;
      }
      reverse_deps_parallel.update(
          dependee_cls, [&](auto&, auto& v, auto) { v.push_back(cls); });
      maybe_roots.insert(dependee_cls);
      deps_vec.push_back(dependee_cls);
    };

    // A superclass must be initialized before a subclass.
    //
    // We are not considering externals here. This should be fine, as
    // a chain internal <- external <- internal should not exist.
    {
      auto* super_class = type_class_internal(cls->get_super_class());
      add_dep(super_class);
    }

    auto* clinit = cls->get_clinit();
    if (clinit != nullptr && clinit->get_code() != nullptr) {
      cfg_adapter::iterate_with_iterator(
          clinit->get_code(), [&](const IRList::iterator& it) {
            auto* insn = it->insn;
            // A method handle initializes the class of its member when it is
            // called, as the instruction it acts like does.
            for_each_field_access(insn,
                                  [&](IROpcode op, DexFieldRef* field,
                                      const DexMethodHandle* /* handle */) {
                                    if (opcode::is_an_sfield_op(op)) {
                                      add_dep(type_class(field->get_class()));
                                    }
                                  });
            for_each_invoke(insn,
                            [&](IROpcode op, DexMethodRef* method,
                                const DexMethodHandle* /* handle */) {
                              if (opcode::is_invoke_static(op)) {
                                add_dep(type_class(method->get_class()));
                              }
                            });
            if (opcode::is_new_instance(insn->opcode())) {
              add_dep(type_class(insn->get_type()));
            }
            // Unlike an invoke-direct of a constructor, an invoke-constructor
            // handle allocates an instance, as a new-instance does.
            for_each_method_handle(insn, [&](const DexMethodHandle* handle) {
              if (handle->type() == METHOD_HANDLE_TYPE_INVOKE_CONSTRUCTOR) {
                add_dep(type_class(handle->methodref()->get_class()));
              }
            });
            return cfg_adapter::LOOP_CONTINUE;
          });
    }

    if (!deps_vec.empty()) {
      is_target.insert(cls);
      deps_parallel.emplace(cls, std::move(deps_vec));
    } else {
      // Something with no deps - make it a root so it gets visited.
      maybe_roots.insert(cls);
    }
    all.insert(cls);
  });
  UnorderedMap<DexClass*, std::vector<DexClass*>> deps;
  for (auto& kv : UnorderedIterable(deps_parallel)) {
    deps[kv.first] = std::move(kv.second);
  }
  UnorderedMap<DexClass*, std::vector<DexClass*>> reverse_deps;
  for (auto& kv : UnorderedIterable(reverse_deps_parallel)) {
    reverse_deps[kv.first] = std::move(kv.second);
  }

  std::vector<DexClass*> roots;
  unordered_copy_if(maybe_roots, std::back_inserter(roots), [&](auto* cls) {
    return is_target.count_unsafe(cls) == 0;
  });
  return std::make_tuple(std::move(deps), std::move(reverse_deps),
                         std::move(roots), all.size());
}

} // namespace

namespace init_deps {

Scope reverse_tsort_by_clinit_deps(const Scope& scope, size_t& init_cycles) {
  Timer timer{"reverse_tsort_by_clinit_deps"};

  UnorderedSet<const DexClass*> scope_set(scope.begin(), scope.end());

  // Collect data for WTO.
  // NOTE: Doing this already also as reverse so we don't have to do that later.
  auto [deps, reverse_deps, roots, all_cnt] = compute_deps(scope, scope_set);

  // NOTE: Using nullptr for root node.
  auto wto = sparta::WeakTopologicalOrdering<DexClass*>(
      nullptr,
      [&_roots = roots, &_reverse_deps = reverse_deps](DexClass* const& cls) {
        if (cls == nullptr) {
          return _roots;
        }

        auto it = _reverse_deps.find(cls);
        if (it == _reverse_deps.end()) {
          return std::vector<DexClass*>();
        }

        return it->second;
      });

  auto it = wto.begin();
  auto it_end = wto.end();

  redex_assert(it != it_end);
  redex_assert(it->is_vertex());
  redex_assert(it->head_node() == nullptr);
  ++it;

  Scope result;
  UnorderedSet<DexClass*> taken;

  for (; it != it_end; ++it) {
    if (it->is_scc()) {
      // Cycle...
      ++init_cycles;

      TRACE(FINALINLINE, 1, "Init cycle detected in %s",
            [&]() {
              std::ostringstream oss;
              oss << *it;
              return oss.str();
            }()
                .c_str());

      continue;
    }

    auto* cls = it->head_node();
    auto deps_it = deps.find(cls);
    if (deps_it != deps.end() &&
        !std::all_of(deps_it->second.begin(), deps_it->second.end(),
                     [&](auto* cls) { return taken.count(cls) != 0; })) {
      TRACE(FINALINLINE, 1, "Skipping %s because of missing deps", SHOW(cls));
      continue;
    }

    result.emplace_back(cls);
    taken.insert(cls);
  }

  return result;
}

Scope reverse_tsort_by_init_deps(const Scope& scope, size_t& possible_cycles) {
  UnorderedSet<const DexClass*> scope_set(scope.begin(), scope.end());
  Scope result;
  UnorderedSet<const DexClass*> visiting;
  UnorderedSet<const DexClass*> visited;
  std::function<void(DexClass*)> visit = [&](DexClass* cls) {
    if (visited.count(cls) != 0 || scope_set.count(cls) == 0) {
      return;
    }
    if (visiting.count(cls) != 0) {
      ++possible_cycles;
      TRACE(FINALINLINE, 1, "Possible class init cycle (could be benign):");
      for (const auto* visiting_cls : UnorderedIterable(visiting)) {
        TRACE(FINALINLINE, 1, "  %s", SHOW(visiting_cls));
      }
      TRACE(FINALINLINE, 1, "  %s", SHOW(cls));
      if (!traceEnabled(FINALINLINE, 1)) {
        TRACE(FINALINLINE, 0,
              "WARNING: Possible class init cycle found in FinalInlineV2. To "
              "check re-run with TRACE=FINALINLINE:1.\n");
      }
      return;
    }
    visiting.emplace(cls);
    const auto& ctors = cls->get_ctors();
    if (ctors.size() == 1) {
      auto* ctor = ctors[0];
      if (ctor != nullptr && ctor->get_code() != nullptr) {
        cfg_adapter::iterate_with_iterator(
            ctor->get_code(), [&](const IRList::iterator& it) {
              auto* insn = it->insn;
              if (opcode::is_an_iget(insn->opcode())) {
                auto* dependee_cls = type_class(insn->get_field()->get_class());
                if (dependee_cls == nullptr || dependee_cls == cls) {
                  return cfg_adapter::LOOP_CONTINUE;
                }
                visit(dependee_cls);
              }
              return cfg_adapter::LOOP_CONTINUE;
            });
      }
    }
    visiting.erase(cls);
    result.emplace_back(cls);
    visited.emplace(cls);
  };
  for (DexClass* cls : scope) {
    visit(cls);
  }
  return result;
}

} // namespace init_deps
