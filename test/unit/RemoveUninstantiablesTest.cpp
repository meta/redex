/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <gtest/gtest.h>

#include "Creators.h"
#include "Debug.h"
#include "DexAnnotation.h"
#include "DexMethodHandle.h"
#include "IRAssembler.h"
#include "RedexTest.h"
#include "RedexTestUtils.h"
#include "RemoveUninstantiablesImpl.h"
#include "Resolver.h"
#include "ScopeHelper.h"
#include "SourceBlocks.h"
#include "TypeUtil.h"
#include "Walkers.h"

namespace {

/**
 * Whether the given type refers to a proper class that has no ctor,
 * and is not external or native. This function only makes a quick determination
 * without considering whether an interface or abstract class has any
 * implementations (see the RemoveUninstantiablesPass for a more complete
 * analysis).
 */
bool is_uninstantiable_class(DexType* type) {
  if (type == nullptr || type::is_array(type) || type::is_primitive(type)) {
    return false;
  }

  auto* cls = type_class(type);
  if (cls == nullptr || is_interface(cls) || cls->is_external() ||
      !cls->rstate.can_delete()) {
    return false;
  }
  return is_abstract(cls) || !cls->has_ctors();
}

struct VirtualScopeId {
  const DexString* name;
  DexProto* proto;
  static VirtualScopeId make(DexMethodRef* method) {
    return VirtualScopeId{method->get_name(), method->get_proto()};
  }
};

struct VirtualScopeIdHasher {
  size_t operator()(const VirtualScopeId& vs) const {
    return ((size_t)vs.name) * 27 + (size_t)vs.proto;
  }
};

bool operator==(const VirtualScopeId& a, const VirtualScopeId& b) {
  return a.name == b.name && a.proto == b.proto;
}

using VirtualScopeIdSet = UnorderedSet<VirtualScopeId, VirtualScopeIdHasher>;

// Helper analysis that determines if we need to keep the code of a method (or
// if it can never run)
class OverriddenVirtualScopesAnalysis {
 private:
  const UnorderedSet<const DexType*>& m_scoped_uninstantiable_types;

  UnorderedMap<const DexType*, VirtualScopeIdSet>
      m_transitively_defined_virtual_scopes;

  ConcurrentSet<const DexType*> m_instantiated_types;
  ConcurrentSet<VirtualScopeId, VirtualScopeIdHasher>
      m_unresolved_super_invoked_virtual_scopes;
  ConcurrentSet<DexMethod*> m_resolved_super_invoked_methods;

  // This helper method initializes
  // m_transitively_defined_virtual_scopes for a particular type
  // finding all virtual scopes which are defined by itself, if actually
  // instantiated, or all instantiable children of the given type.
  void compute_transitively_defined_virtual_scope(
      const UnorderedMap<const DexType*, UnorderedSet<const DexType*>>&
          instantiable_children,
      const InsertOnlyConcurrentMap<const DexType*, VirtualScopeIdSet>&
          defined_virtual_scopes,
      const DexType* t) {
    auto it = m_transitively_defined_virtual_scopes.find(t);
    if (it != m_transitively_defined_virtual_scopes.end()) {
      return;
    }
    auto& res = m_transitively_defined_virtual_scopes[t];
    if (is_instantiated(t)) {
      const auto& own_defined_virtual_scopes =
          defined_virtual_scopes.at_unsafe(t);
      insert_unordered_iterable(res, own_defined_virtual_scopes);
      return;
    }
    UnorderedMap<VirtualScopeId, size_t, VirtualScopeIdHasher> counted;
    auto children_it = instantiable_children.find(t);
    if (children_it != instantiable_children.end()) {
      const auto& children = children_it->second;
      for (const auto* child : UnorderedIterable(children)) {
        const auto& defined_virtual_scopes_of_child =
            defined_virtual_scopes.at_unsafe(child);
        for (const auto& virtual_scope :
             UnorderedIterable(defined_virtual_scopes_of_child)) {
          counted[virtual_scope]++;
        }
        compute_transitively_defined_virtual_scope(
            instantiable_children, defined_virtual_scopes, child);
        for (const auto& virtual_scope : UnorderedIterable(
                 m_transitively_defined_virtual_scopes.at(child))) {
          if (defined_virtual_scopes_of_child.count(virtual_scope) == 0u) {
            counted[virtual_scope]++;
          }
        }
      }
      auto children_size = children.size();
      for (auto& p : UnorderedIterable(counted)) {
        if (p.second == children_size) {
          res.insert(p.first);
        }
      }
    }
  }

  // Helper function that finds...
  // 1. all types that are actually instantiated via new-instance, and
  // 2. all targets of an invoke-super, i.e. methods that can be directly
  //    invoked even if overridden by all instantiable children
  void scan_code(const Scope& scope) {
    walk::parallel::code(scope, [&](DexMethod* method, IRCode& code) {
      cfg_adapter::iterate(&code, [&](MethodItemEntry& mie) {
        auto* insn = mie.insn;
        if (insn->opcode() == OPCODE_NEW_INSTANCE ||
            insn->opcode() == OPCODE_CONST_CLASS) {
          // occurrences of "const-class" doesn't actually mean that the class
          // can be instantiated, but since it's then possible via reflection,
          // we treat it as such
          m_instantiated_types.insert(insn->get_type());
        }
        if (insn->opcode() == OPCODE_INVOKE_SUPER) {
          auto* callee_ref = insn->get_method();
          auto* callee = resolve_method_deprecated(callee_ref,
                                                   MethodSearch::Super, method);
          if (callee == nullptr) {
            m_unresolved_super_invoked_virtual_scopes.insert(
                VirtualScopeId::make(callee_ref));
          } else {
            m_resolved_super_invoked_methods.insert(callee);
          }
        }
        return cfg_adapter::LOOP_CONTINUE;
      });
    });
  }

  bool is_instantiated(const DexType* t) const {
    auto* cls = type_class(t);
    return root(cls) || !can_rename(cls) ||
           (m_instantiated_types.count(t) != 0u);
  }

 public:
  OverriddenVirtualScopesAnalysis(
      const Scope& scope,
      const UnorderedSet<const DexType*>& scoped_uninstantiable_types,
      const UnorderedMap<const DexType*, UnorderedSet<const DexType*>>&
          instantiable_children)
      : m_scoped_uninstantiable_types(scoped_uninstantiable_types) {
    scan_code(scope);

    InsertOnlyConcurrentMap<const DexType*, VirtualScopeIdSet>
        defined_virtual_scopes;
    walk::parallel::classes(scope, [&](DexClass* cls) {
      VirtualScopeIdSet virtual_scopes;
      for (auto* method : cls->get_vmethods()) {
        VirtualScopeId virtual_scope = VirtualScopeId::make(method);
        virtual_scopes.emplace(virtual_scope);
      }
      defined_virtual_scopes.emplace(cls->get_type(),
                                     std::move(virtual_scopes));
    });

    for (auto* cls : scope) {
      compute_transitively_defined_virtual_scope(
          instantiable_children, defined_virtual_scopes, cls->get_type());
    }
  }

  bool keep_code(DexMethod* method) const {
    if (is_static(method)) {
      return true;
    }
    if (m_scoped_uninstantiable_types.count(method->get_class()) != 0u) {
      return false;
    }
    if (!method->is_virtual()) {
      return true;
    }
    if ((m_resolved_super_invoked_methods.count(method) != 0u) ||
        (m_unresolved_super_invoked_virtual_scopes.count(
             VirtualScopeId::make(method)) != 0u)) {
      return true;
    }
    if (is_instantiated(method->get_class())) {
      return true;
    }
    VirtualScopeId virtual_scope = VirtualScopeId::make(method);
    return m_transitively_defined_virtual_scopes.at(method->get_class())
               .count(virtual_scope) == 0u;
  }
};

// Computes set of uninstantiable types, also looking at the type system to
// find non-external (and non-native)...
// - interfaces that are not annotations, are not root (or unrenameable) and
//   do not contain root (or unrenameable) methods and have no non-abstract
//   classes implementing them, and
// - abstract (non-interface) classes that are not extended by any non-abstract
//   class
UnorderedSet<const DexType*> compute_scoped_uninstantiable_types(
    const Scope& scope,
    UnorderedMap<const DexType*, UnorderedSet<const DexType*>>*
        instantiable_children = nullptr) {
  // First, we compute types that might possibly be uninstantiable, and classes
  // that we consider instantiable.
  UnorderedSet<const DexType*> uninstantiable_types;
  UnorderedSet<const DexClass*> instantiable_classes;
  auto is_interface_instantiable = [](const DexClass* interface) {
    if (is_annotation(interface) || interface->is_external() ||
        root(interface) || !can_rename(interface)) {
      return true;
    }
    for (auto* method : interface->get_vmethods()) {
      if (root(method) || !can_rename(method)) {
        return true;
      }
    }
    return false;
  };
  walk::classes(scope, [&](const DexClass* cls) {
    if (is_uninstantiable_class(cls->get_type()) ||
        (is_interface(cls) && !is_interface_instantiable(cls))) {
      uninstantiable_types.insert(cls->get_type());
    } else {
      instantiable_classes.insert(cls);
    }
  });
  // Next, we prune the list of possibly uninstantiable types by looking at
  // what instantiable classes implement and extend.
  UnorderedSet<const DexClass*> visited;
  std::function<bool(const DexClass*)> visit;
  visit = [&](const DexClass* cls) {
    if (cls == nullptr || !visited.insert(cls).second) {
      return false;
    }
    if (instantiable_children != nullptr) {
      (*instantiable_children)[cls->get_super_class()].insert(cls->get_type());
    }
    uninstantiable_types.erase(cls->get_type());
    for (auto* interface : *cls->get_interfaces()) {
      visit(type_class(interface));
    }
    return true;
  };
  for (const auto* cls : UnorderedIterable(instantiable_classes)) {
    while (visit(cls)) {
      cls = type_class(cls->get_super_class());
    }
  }
  uninstantiable_types.insert(type::java_lang_Void());
  return uninstantiable_types;
}

remove_uninstantiables_impl::Stats run_remove_uninstantiables(
    DexStoresVector& stores) {
  Scope scope = build_class_scope(stores);
  walk::parallel::code(scope,
                       [&](DexMethod*, IRCode& code) { code.build_cfg(); });

  UnorderedMap<const DexType*, UnorderedSet<const DexType*>>
      instantiable_children;
  UnorderedSet<const DexType*> scoped_uninstantiable_types =
      compute_scoped_uninstantiable_types(scope, &instantiable_children);
  OverriddenVirtualScopesAnalysis overridden_virtual_scopes_analysis(
      scope, scoped_uninstantiable_types, instantiable_children);
  ConcurrentSet<DexMethod*> uncallable_instance_methods;
  auto stats = walk::parallel::methods<remove_uninstantiables_impl::Stats>(
      scope,
      [&scoped_uninstantiable_types, &overridden_virtual_scopes_analysis,
       &uncallable_instance_methods](DexMethod* method) {
        auto* code = method->get_code();
        if (code == nullptr) {
          return remove_uninstantiables_impl::Stats();
        }
        always_assert(code->cfg_built());
        if (overridden_virtual_scopes_analysis.keep_code(method)) {
          auto& cfg = code->cfg();
          return remove_uninstantiables_impl::replace_uninstantiable_refs(
              scoped_uninstantiable_types, cfg);
        }
        uncallable_instance_methods.insert(method);
        return remove_uninstantiables_impl::Stats();
      });

  stats += remove_uninstantiables_impl::reduce_uncallable_instance_methods(
      scope, uncallable_instance_methods,
      [&](const DexMethod*) { return false; });

  walk::parallel::code(scope,
                       [&](DexMethod*, IRCode& code) { code.clear_cfg(); });
  return stats;
}

struct RemoveUninstantiablesTest : public RedexTest {
  RemoveUninstantiablesTest() {
    always_assert(type_class(type::java_lang_Object()) == nullptr);
    always_assert(type_class(type::java_lang_Void()) == nullptr);
    ClassCreator cc_object(type::java_lang_Object());
    cc_object.set_access(ACC_PUBLIC);
    cc_object.create();
    ClassCreator cc_void(type::java_lang_Void());
    cc_void.set_access(ACC_PUBLIC | ACC_ABSTRACT);
    cc_void.set_super(type::java_lang_Object());
    cc_void.create();
  }
};

UnorderedSet<const DexType*> compute_uninstantiable_types() {
  Scope scope;
  g_redex->walk_type_class([&](const DexType*, const DexClass* cls) {
    scope.push_back(const_cast<DexClass*>(cls));
  });
  scope.push_back(type_class(type::java_lang_Void()));
  return compute_scoped_uninstantiable_types(scope);
}

remove_uninstantiables_impl::Stats replace_uninstantiable_refs(
    cfg::ControlFlowGraph& cfg) {
  return remove_uninstantiables_impl::replace_uninstantiable_refs(
      compute_uninstantiable_types(), cfg);
}

remove_uninstantiables_impl::Stats replace_all_with_unreachable_throw(
    cfg::ControlFlowGraph& cfg) {
  return remove_uninstantiables_impl::replace_all_with_unreachable_throw(cfg);
}

/// Expect \c run_remove_uninstantiables to convert \p ACTUAL into \p EXPECTED
/// where both parameters are strings containing IRCode in s-expression form.
/// Increments the stats returned from performing \p OPERATION to the variable
/// with identifier \p STATS.
#define EXPECT_CHANGE(OPERATION, STATS, ACTUAL, EXPECTED)             \
  do {                                                                \
    auto actual_ir = assembler::ircode_from_string(ACTUAL);           \
    const auto expected_ir = assembler::ircode_from_string(EXPECTED); \
                                                                      \
    actual_ir->build_cfg();                                           \
    (STATS) += (OPERATION)(actual_ir->cfg());                         \
    actual_ir->clear_cfg();                                           \
                                                                      \
    EXPECT_CODE_EQ(expected_ir.get(), actual_ir.get());               \
  } while (0)

/// Expect method with full signature \p SIGNATURE to exist, and have a
/// body corresponding to \p EXPECTED, a string containing IRCode in
/// s-expression form.
#define EXPECT_METHOD(SIGNATURE, EXPECTED)                            \
  do {                                                                \
    std::string signature = (SIGNATURE);                              \
    auto method = DexMethod::get_method(signature);                   \
    EXPECT_NE(nullptr, method) << "Method not found: " << signature;  \
                                                                      \
    auto actual_ir = method->as_def()->get_code();                    \
    const auto expected_ir = assembler::ircode_from_string(EXPECTED); \
    EXPECT_CODE_EQ(expected_ir.get(), actual_ir);                     \
  } while (0)

/// Expect method with full signature \p SIGNATURE to not exist.
#define EXPECT_NO_METHOD_DEF(SIGNATURE)             \
  do {                                              \
    std::string signature = (SIGNATURE);            \
    auto method = DexMethod::get_method(signature); \
    EXPECT_TRUE(!method || !method->is_def());      \
                                                    \
  } while (0)

/// Expect method with full signature \p SIGNATURE to exist, and be
/// abstract.
#define EXPECT_ABSTRACT_METHOD(SIGNATURE)                            \
  do {                                                               \
    std::string signature = (SIGNATURE);                             \
    auto method = DexMethod::get_method(signature);                  \
    EXPECT_NE(nullptr, method) << "Method not found: " << signature; \
    EXPECT_TRUE(is_abstract(method->as_def()));                      \
  } while (0)

/// Register a new class with \p name, and methods \p methods, given in
/// s-expression form.
template <typename... Methods>
DexClass* def_class(const char* name, Methods... methods) {
  return assembler::class_with_methods(
      name,
      {
          assembler::method_from_string(methods)...,
      });
}

const char* const Bar_init = R"(
(method (private) "LBar;.<init>:()V"
  ((load-param-object v0)
   (return-void))
))";

const char* const Bar_baz = R"(
(method (public) "LBar;.baz:()V"
  ((load-param-object v0)
   (return-void))
))";

const char* const Bar_qux = R"(
(method (public) "LBar;.qux:()I"
  ((load-param-object v0) ; this
   (iget-object v0 "LBar;.mFoo:LFoo;")
   (move-result-pseudo-object v1)
   (iput-object v1 v0 "LBar;.mFoo:LFoo;")
   (if-eqz v1 :else)
   (invoke-virtual (v1) "LFoo;.qux:()LFoo;")
   (move-result-object v2)
   (instance-of v2 "LFoo;")
   (move-result-pseudo v3)
   (return v3)
   (:else)
   (iget-object v1 "LFoo;.mBar:LBar;")
   (move-result-pseudo-object v3)
   (const v4 0)
   (return v4))
))";

const char* const BarBar_init = R"(
(method (private) "LBarBar;.<init>:()V"
  ((load-param-object v0)
   (invoke-direct (v0) "LBar;.<init>:()V")
   (return-void))
))";

const char* const BarBar_baz = R"(
(method (public) "LBarBar;.baz:()V"
  ((load-param-object v0)
   (new-instance "LBarBar;")
   (move-result-pseudo-object v1)
   (return-void))
))";

const char* const Foo_baz = R"(
(method (public) "LFoo;.baz:()V"
  ((load-param-object v0)
   (return-void))
))";

const char* const Foo_qux = R"(
(method (public) "LFoo;.qux:()LFoo;"
  ((load-param-object v0)
   (return-object v0))
))";

const char* const Foo_fox = R"(
(method (private) "LFoo;.fox:()LFoo;"
  ((load-param-object v0)
   (return-object v0))
))";

const char* const FooBar_baz = R"(
(method (public) "LFooBar;.baz:()V"
  ((load-param-object v0)
   (return-void))
))";

TEST_F(RemoveUninstantiablesTest, InstanceOf) {
  def_class("LFoo;");
  def_class("LBar;", Bar_init);

  ASSERT_TRUE(is_uninstantiable_class(DexType::get_type("LFoo;")));
  ASSERT_FALSE(is_uninstantiable_class(DexType::get_type("LBar;")));

  remove_uninstantiables_impl::Stats stats;
  EXPECT_CHANGE(replace_uninstantiable_refs,
                stats,
                /* ACTUAL */ R"((
                  (instance-of v0 "LFoo;")
                  (move-result-pseudo v1)
                  (instance-of v0 "LBar;")
                  (move-result-pseudo v1)
                ))",
                /* EXPECTED */ R"((
                  (const v1 0)
                  (instance-of v0 "LBar;")
                  (move-result-pseudo v1)
                ))");

  EXPECT_EQ(1, stats.instance_ofs);
}

TEST_F(RemoveUninstantiablesTest, InstanceOfUnimplementedInterface) {
  auto* cls = def_class("LFoo;");
  cls->set_access(cls->get_access() | ACC_INTERFACE | ACC_ABSTRACT);

  remove_uninstantiables_impl::Stats stats;
  EXPECT_CHANGE(replace_uninstantiable_refs,
                stats,
                /* ACTUAL */ R"((
                  (instance-of v0 "LFoo;")
                  (move-result-pseudo v1)
                ))",
                /* EXPECTED */ R"((
                  (const v1 0)
                ))");

  EXPECT_EQ(1, stats.instance_ofs);
}

TEST_F(RemoveUninstantiablesTest, Invoke) {
  def_class("LFoo;", Foo_baz, Foo_qux);
  def_class("LBar;", Bar_init, Bar_baz);

  ASSERT_TRUE(is_uninstantiable_class(DexType::get_type("LFoo;")));
  ASSERT_FALSE(is_uninstantiable_class(DexType::get_type("LBar;")));

  remove_uninstantiables_impl::Stats stats;
  EXPECT_CHANGE(replace_uninstantiable_refs,
                stats,
                /* ACTUAL */ R"((
                  (const v0 0)
                  (invoke-virtual (v0) "LFoo;.qux:()LFoo;")
                  (move-result-object v1)
                  (return-void)
                ))",
                /* EXPECTED */ R"((
                  (const v0 0)
                  (const-string "qux")
                  (move-result-pseudo-object v2)
                  (new-instance "Ljava/lang/NullPointerException;")
                  (move-result-pseudo-object v3)
                  (invoke-direct (v3 v2) "Ljava/lang/NullPointerException;.<init>:(Ljava/lang/String;)V")
                  (throw v3)
                ))");
  EXPECT_EQ(1, stats.invokes);

  EXPECT_CHANGE(replace_uninstantiable_refs,
                stats,
                /* ACTUAL */ R"((
                  (const v0 0)
                  (invoke-virtual (v0) "LFoo;.baz:()V")
                  (return-void)
                ))",
                /* EXPECTED */ R"((
                  (const v0 0)
                  (const-string "baz")
                  (move-result-pseudo-object v1)
                  (new-instance "Ljava/lang/NullPointerException;")
                  (move-result-pseudo-object v2)
                  (invoke-direct (v2 v1) "Ljava/lang/NullPointerException;.<init>:(Ljava/lang/String;)V")
                  (throw v2)
                ))");
  EXPECT_EQ(2, stats.invokes);

  EXPECT_CHANGE(replace_uninstantiable_refs,
                stats,
                /* ACTUAL */ R"((
                  (const v0 0)
                  (invoke-virtual (v0) "LBar;.baz:()V")
                  (return-void)
                ))",
                /* EXPECTED */ R"((
                  (const v0 0)
                  (invoke-virtual (v0) "LBar;.baz:()V")
                  (return-void)
                ))");
  EXPECT_EQ(2, stats.invokes);

  EXPECT_CHANGE(replace_uninstantiable_refs,
                stats,
                /* ACTUAL */ R"((
                  (const v0 0)
                  (invoke-direct (v0) "LFoo;.qux:()LFoo;")
                  (move-result-object v1)
                  (return-void)
                ))",
                /* EXPECTED */ R"((
                  (const v0 0)
                  (const-string "qux")
                  (move-result-pseudo-object v2)
                  (new-instance "Ljava/lang/NullPointerException;")
                  (move-result-pseudo-object v3)
                  (invoke-direct (v3 v2) "Ljava/lang/NullPointerException;.<init>:(Ljava/lang/String;)V")
                  (throw v3)
                ))");
  EXPECT_EQ(3, stats.invokes);

  EXPECT_CHANGE(replace_uninstantiable_refs,
                stats,
                /* ACTUAL */ R"((
                  (const v0 0)
                  (invoke-direct (v0) "LFoo;.baz:()V")
                  (return-void)
                ))",
                /* EXPECTED */ R"((
                  (const v0 0)
                  (const-string "baz")
                  (move-result-pseudo-object v1)
                  (new-instance "Ljava/lang/NullPointerException;")
                  (move-result-pseudo-object v2)
                  (invoke-direct (v2 v1) "Ljava/lang/NullPointerException;.<init>:(Ljava/lang/String;)V")
                  (throw v2)
                ))");
  EXPECT_EQ(4, stats.invokes);

  EXPECT_CHANGE(replace_uninstantiable_refs,
                stats,
                /* ACTUAL */ R"((
                  (const v0 0)
                  (invoke-direct (v0) "LBar;.baz:()V")
                  (return-void)
                ))",
                /* EXPECTED */ R"((
                  (const v0 0)
                  (invoke-direct (v0) "LBar;.baz:()V")
                  (return-void)
                ))");
  EXPECT_EQ(4, stats.invokes);
}

TEST_F(RemoveUninstantiablesTest, CheckCast) {
  def_class("LFoo;");
  def_class("LBar;", Bar_init);

  ASSERT_TRUE(is_uninstantiable_class(DexType::get_type("LFoo;")));
  ASSERT_FALSE(is_uninstantiable_class(DexType::get_type("LBar;")));

  remove_uninstantiables_impl::Stats stats;
  EXPECT_CHANGE(replace_uninstantiable_refs,
                stats,
                /* ACTUAL */ R"((
                  (const v0 0)
                  (check-cast v0 "LFoo;")
                  (move-result-pseudo-object v1)
                  (return-void)
                ))",
                /* EXPECTED */ R"((
                  (const v0 0)
                  (check-cast v0 "Ljava/lang/Void;")
                  (move-result-pseudo-object v1)
                  (const v0 0)
                  (const v1 0)
                  (return-void)
                ))");
  EXPECT_EQ(1, stats.check_casts);

  EXPECT_CHANGE(replace_uninstantiable_refs,
                stats,
                /* ACTUAL */ R"((
                  (const v0 0)
                  (check-cast v0 "LBar;")
                  (move-result-pseudo-object v1)
                  (return-void)
                ))",
                /* EXPECTED */ R"((
                  (const v0 0)
                  (check-cast v0 "LBar;")
                  (move-result-pseudo-object v1)
                  (return-void)
                ))");
  EXPECT_EQ(1, stats.check_casts);

  // Void is itself uninstantiable, so we can infer that following a check-cast,
  // the registers involved hold null.
  EXPECT_CHANGE(replace_uninstantiable_refs,
                stats,
                /* ACTUAL */ R"((
                  (const v0 0)
                  (check-cast v0 "Ljava/lang/Void;")
                  (move-result-pseudo-object v1)
                  (return-void)
                ))",
                /* EXPECTED */ R"((
                  (const v0 0)
                  (check-cast v0 "Ljava/lang/Void;")
                  (move-result-pseudo-object v1)
                  (const v0 0)
                  (const v1 0)
                  (return-void)
                ))");
  EXPECT_EQ(2, stats.check_casts);
}

TEST_F(RemoveUninstantiablesTest, GetField) {
  def_class("LFoo;");
  def_class("LBar;", Bar_init);

  DexField::make_field("LFoo;.a:I")->make_concrete(ACC_PUBLIC);
  DexField::make_field("LBar;.a:I")->make_concrete(ACC_PUBLIC);

  ASSERT_TRUE(is_uninstantiable_class(DexType::get_type("LFoo;")));
  ASSERT_FALSE(is_uninstantiable_class(DexType::get_type("LBar;")));

  remove_uninstantiables_impl::Stats stats;
  EXPECT_CHANGE(replace_uninstantiable_refs,
                stats,
                /* ACTUAL */ R"((
                  (const v0 0)
                  (iget v0 "LBar;.a:I")
                  (move-result-pseudo v1)
                  (iget v0 "LFoo;.a:I")
                  (move-result-pseudo v2)
                  (return-void)
                ))",
                /* EXPECTED */ R"((
                  (const v0 0)
                  (iget v0 "LBar;.a:I")
                  (move-result-pseudo v1)
                  (const-string "a")
                  (move-result-pseudo-object v3)
                  (new-instance "Ljava/lang/NullPointerException;")
                  (move-result-pseudo-object v4)
                  (invoke-direct (v4 v3) "Ljava/lang/NullPointerException;.<init>:(Ljava/lang/String;)V")
                  (throw v4)
                ))");
  EXPECT_EQ(1, stats.field_accesses_on_uninstantiable);
}

TEST_F(RemoveUninstantiablesTest, PutField) {
  def_class("LFoo;");
  def_class("LBar;", Bar_init);

  DexField::make_field("LFoo;.a:I")->make_concrete(ACC_PUBLIC);
  DexField::make_field("LBar;.a:I")->make_concrete(ACC_PUBLIC);

  ASSERT_TRUE(is_uninstantiable_class(DexType::get_type("LFoo;")));
  ASSERT_FALSE(is_uninstantiable_class(DexType::get_type("LBar;")));

  remove_uninstantiables_impl::Stats stats;
  EXPECT_CHANGE(replace_uninstantiable_refs,
                stats,
                /* ACTUAL */ R"((
                  (const v0 0)
                  (const v1 0)
                  (iput v0 v1 "LBar;.a:I")
                  (const v2 0)
                  (iput v0 v2 "LFoo;.a:I")
                  (return-void)
                ))",
                /* EXPECTED */ R"((
                  (const v0 0)
                  (const v1 0)
                  (iput v0 v1 "LBar;.a:I")
                  (const v2 0)
                  (const-string "a")
                  (move-result-pseudo-object v3)
                  (new-instance "Ljava/lang/NullPointerException;")
                  (move-result-pseudo-object v4)
                  (invoke-direct (v4 v3) "Ljava/lang/NullPointerException;.<init>:(Ljava/lang/String;)V")
                  (throw v4)
                ))");
  EXPECT_EQ(1, stats.field_accesses_on_uninstantiable);
}

TEST_F(RemoveUninstantiablesTest, GetUninstantiable) {
  def_class("LFoo;");
  def_class("LBar;", Bar_init);

  DexField::make_field("LBar;.mFoo:LFoo;")->make_concrete(ACC_PUBLIC);
  DexField::make_field("LBar;.sFoo:LFoo;")
      ->make_concrete(ACC_PUBLIC | ACC_STATIC);

  DexField::make_field("LBar;.mBar:LBar;")->make_concrete(ACC_PUBLIC);
  DexField::make_field("LBar;.sBar:LBar;")
      ->make_concrete(ACC_PUBLIC | ACC_STATIC);

  ASSERT_TRUE(is_uninstantiable_class(DexType::get_type("LFoo;")));
  ASSERT_FALSE(is_uninstantiable_class(DexType::get_type("LBar;")));

  remove_uninstantiables_impl::Stats stats;
  EXPECT_CHANGE(replace_uninstantiable_refs,
                stats,
                /* ACTUAL */ R"((
                  (const v0 0)
                  (iget-object v0 "LBar;.mFoo:LFoo;")
                  (move-result-pseudo v1)
                  (iget-object v0 "LBar;.mBar:LBar;")
                  (move-result-pseudo v2)
                  (sget-object "LBar.sFoo:LFoo;")
                  (move-result-pseudo v3)
                  (sget-object "LBar.sBar:LBar;")
                  (move-result-pseudo v4)
                  (return-void)
                ))",
                /* EXPECTED */ R"((
                  (const v0 0)
                  (const v1 0)
                  (iget-object v0 "LBar;.mBar:LBar;")
                  (move-result-pseudo v2)
                  (const v3 0)
                  (sget-object "LBar.sBar:LBar;")
                  (move-result-pseudo v4)
                  (return-void)
                ))");
  EXPECT_EQ(2, stats.get_uninstantiables);
}

TEST_F(RemoveUninstantiablesTest, InvokeUninstantiable) {
  def_class("LFoo;");
  def_class("LBar;", Bar_init);

  DexMethod::make_method("LBar;.sFoo:()LFoo;")
      ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_NATIVE,
                      /* is_virtual */ false);

  DexMethod::make_method("LBar;.sBar:()LBar;")
      ->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_NATIVE,
                      /* is_virtual */ false);

  ASSERT_TRUE(is_uninstantiable_class(DexType::get_type("LFoo;")));
  ASSERT_FALSE(is_uninstantiable_class(DexType::get_type("LBar;")));

  remove_uninstantiables_impl::Stats stats;
  EXPECT_CHANGE(replace_uninstantiable_refs,
                stats,
                /* ACTUAL */ R"((
                  (invoke-static () "LBar.sFoo:()LFoo;")
                  (move-result v0)
                  (invoke-static () "LBar.sBar:()LBar;")
                  (move-result v1)
                  (return-void)
                ))",
                /* EXPECTED */ R"((
                  (invoke-static () "LBar.sFoo:()LFoo;")
                  (const v0 0)
                  (invoke-static () "LBar.sBar:()LBar;")
                  (move-result v1)
                  (return-void)
                ))");
  EXPECT_EQ(1, stats.invoke_uninstantiables);
}

TEST_F(RemoveUninstantiablesTest, ReplaceAllWithThrow) {
  remove_uninstantiables_impl::Stats stats;
  EXPECT_CHANGE(replace_all_with_unreachable_throw,
                stats,
                /* ACTUAL */ R"((
                  (load-param-object v0)
                  (const v1 0)
                  (if-eqz v1 :l1)
                  (const v2 1)
                  (return-void)
                  (:l1)
                  (const v2 2)
                  (return-void)
                ))",
                /* EXPECTED */ R"((
                  (load-param-object v0)
                  (unreachable v3)
                  (throw v3)
                ))");
  EXPECT_EQ(1, stats.throw_null_methods);
}

TEST_F(RemoveUninstantiablesTest, RunPass) {
  DexStoresVector dss{DexStore{"test_store"}};

  auto* Foo = def_class("LFoo;", Foo_baz, Foo_qux, Foo_fox);
  auto* Bar = def_class("LBar;", Bar_init, Bar_baz, Bar_qux);
  auto* FooBar = def_class("LFooBar;", FooBar_baz);
  dss.back().add_classes({Foo, Bar, FooBar});
  FooBar->set_super_class(Foo->get_type());

  DexField::make_field("LBar;.mFoo:LFoo;")->make_concrete(ACC_PUBLIC);
  DexField::make_field("LFoo;.mBar:LBar;")->make_concrete(ACC_PUBLIC);

  auto stats = run_remove_uninstantiables(dss);

  EXPECT_ABSTRACT_METHOD("LFoo;.baz:()V");
  EXPECT_ABSTRACT_METHOD("LFoo;.qux:()LFoo;");
  EXPECT_NO_METHOD_DEF("LFooBar;.baz:()V");

  EXPECT_METHOD("LFoo;.fox:()LFoo;",
                R"((
                  (load-param-object v0)
                  (unreachable v1)
                  (throw v1)
                ))");

  EXPECT_METHOD("LBar;.baz:()V",
                R"((
                  (load-param-object v0)
                  (return-void)
                ))");

  EXPECT_METHOD("LBar;.qux:()I",
                R"((
                  (load-param-object v0) ; this
                  (const v1 0)
                  (iput-object v1 v0 "LBar;.mFoo:LFoo;")
                  (if-eqz v1 :else)
                  (const-string "qux")
                  (move-result-pseudo-object v5)
                  (new-instance "Ljava/lang/NullPointerException;")
                  (move-result-pseudo-object v6)
                  (invoke-direct (v6 v5) "Ljava/lang/NullPointerException;.<init>:(Ljava/lang/String;)V")
                  (throw v6)
                  (:else)
                  (const-string "mBar")
                  (move-result-pseudo-object v5)
                  (new-instance "Ljava/lang/NullPointerException;")
                  (move-result-pseudo-object v6)
                  (invoke-direct (v6 v5) "Ljava/lang/NullPointerException;.<init>:(Ljava/lang/String;)V")
                  (throw v6)
                ))");

  EXPECT_EQ(1, stats.instance_ofs);
  EXPECT_EQ(1, stats.invokes);
  EXPECT_EQ(1, stats.field_accesses_on_uninstantiable);
  EXPECT_EQ(1, stats.abstracted_classes);
  EXPECT_EQ(2, stats.abstracted_vmethods);
  EXPECT_EQ(1, stats.removed_vmethods);
  EXPECT_EQ(1, stats.throw_null_methods);
  EXPECT_EQ(1, stats.get_uninstantiables);
}

TEST_F(RemoveUninstantiablesTest, VoidIsUninstantiable) {
  auto uninstantiable_types = compute_uninstantiable_types();
  EXPECT_TRUE(uninstantiable_types.count(type::java_lang_Void()));
}

TEST_F(RemoveUninstantiablesTest, UnimplementedInterfaceIsUninstantiable) {
  auto* foo = def_class("LFoo;");
  foo->set_access(foo->get_access() | ACC_INTERFACE | ACC_ABSTRACT);
  auto uninstantiable_types = compute_uninstantiable_types();
  EXPECT_TRUE(uninstantiable_types.count(foo->get_type()));
}

TEST_F(RemoveUninstantiablesTest,
       UnimplementedInterfaceWithRootMethodIsNotUninstantiable) {
  auto* foo = def_class("LFoo;");
  foo->set_access(foo->get_access() | ACC_INTERFACE | ACC_ABSTRACT);
  auto* method =
      dynamic_cast<DexMethod*>(DexMethod::make_method("LFoo;.root:()Z"));
  method->make_concrete(ACC_PUBLIC | ACC_ABSTRACT, /* is_virtual */ true);
  method->rstate.set_root();
  foo->add_method(method);
  auto uninstantiable_types = compute_uninstantiable_types();
  EXPECT_FALSE(uninstantiable_types.count(foo->get_type()));
}

TEST_F(RemoveUninstantiablesTest,
       UnimplementedAnnotationInterfaceIsNotUninstantiable) {
  auto* foo = def_class("LFoo;");
  foo->set_access(foo->get_access() | ACC_INTERFACE | ACC_ABSTRACT |
                  ACC_ANNOTATION);
  auto uninstantiable_types = compute_uninstantiable_types();
  EXPECT_FALSE(uninstantiable_types.count(foo->get_type()));
}

TEST_F(RemoveUninstantiablesTest, ImplementedInterfaceIsNotUninstantiable) {
  auto* foo = def_class("LFoo;");
  foo->set_access(foo->get_access() | ACC_INTERFACE | ACC_ABSTRACT);
  auto* bar = def_class("LBar;", Bar_init, Bar_baz);
  bar->set_interfaces(DexTypeList::make_type_list({foo->get_type()}));
  auto uninstantiable_types = compute_uninstantiable_types();
  EXPECT_FALSE(uninstantiable_types.count(foo->get_type()));
  EXPECT_FALSE(uninstantiable_types.count(bar->get_type()));
}

TEST_F(RemoveUninstantiablesTest, AbstractClassIsUninstantiable) {
  auto* foo = def_class("LFoo;");
  foo->set_access(foo->get_access() | ACC_ABSTRACT);
  auto uninstantiable_types = compute_uninstantiable_types();
  EXPECT_TRUE(uninstantiable_types.count(foo->get_type()));
}

TEST_F(RemoveUninstantiablesTest, ExtendedAbstractClassIsNotUninstantiable) {
  auto* foo = def_class("LFoo;");
  foo->set_access(foo->get_access() | ACC_ABSTRACT);
  auto* bar = def_class("LBar;", Bar_init);
  bar->set_super_class(foo->get_type());
  auto uninstantiable_types = compute_uninstantiable_types();
  EXPECT_FALSE(uninstantiable_types.count(foo->get_type()));
  EXPECT_FALSE(uninstantiable_types.count(bar->get_type()));
}

TEST_F(RemoveUninstantiablesTest, InvokeInterfaceOnUninstantiable) {
  auto* foo = def_class("LFoo;");
  foo->set_access(foo->get_access() | ACC_INTERFACE | ACC_ABSTRACT);

  auto* void_t = type::_void();
  auto* void_void =
      DexProto::make_proto(void_t, DexTypeList::make_type_list({}));
  create_abstract_method(foo, "abs", void_void);

  remove_uninstantiables_impl::Stats stats;
  EXPECT_CHANGE(replace_uninstantiable_refs,
                stats,
                /* ACTUAL */ R"((
                  (const v0 0)
                  (invoke-interface (v0) "LFoo;.abs:()V;")
                  (return-void)
                ))",
                /* EXPECTED */ R"((
                  (const v0 0)
                  (const-string "abs")
                  (move-result-pseudo-object v1)
                  (new-instance "Ljava/lang/NullPointerException;")
                  (move-result-pseudo-object v2)
                  (invoke-direct (v2 v1) "Ljava/lang/NullPointerException;.<init>:(Ljava/lang/String;)V")
                  (throw v2)
                ))");
  EXPECT_EQ(1, stats.invokes);
}

TEST_F(RemoveUninstantiablesTest, InvokeSuperOnUninstantiable) {
  auto* foo = def_class("LFoo;");
  auto* void_t = type::_void();
  auto* void_void =
      DexProto::make_proto(void_t, DexTypeList::make_type_list({}));
  create_abstract_method(foo, "abs", void_void);

  auto* bar = def_class("LBar;");
  bar->set_super_class(foo->get_type());

  remove_uninstantiables_impl::Stats stats;
  EXPECT_CHANGE(replace_uninstantiable_refs,
                stats,
                /* ACTUAL */ R"((
                  (const v0 0)
                  (invoke-super (v0) "LBar;.abs:()V;")
                  (return-void)
                ))",
                /* EXPECTED */ R"((
                  (const v0 0)
                  (const-string "abs")
                  (move-result-pseudo-object v1)
                  (new-instance "Ljava/lang/NullPointerException;")
                  (move-result-pseudo-object v2)
                  (invoke-direct (v2 v1) "Ljava/lang/NullPointerException;.<init>:(Ljava/lang/String;)V")
                  (throw v2)
                ))");
  EXPECT_EQ(1, stats.invokes);
}

TEST_F(RemoveUninstantiablesTest, RunPassInstantiableChildrenDefined) {
  DexStoresVector dss{DexStore{"test_store"}};

  auto* Bar = def_class("LBar;", Bar_init, Bar_baz);
  DexMethod::get_method("LBar;.<init>:()V")->as_def()->set_access(ACC_PUBLIC);
  auto* BarBar = def_class("LBarBar;", BarBar_init, BarBar_baz);
  DexMethod::get_method("LBarBar;.<init>:()V")
      ->as_def()
      ->set_access(ACC_PUBLIC);
  dss.back().add_classes({Bar, BarBar});
  BarBar->set_super_class(Bar->get_type());

  auto stats = run_remove_uninstantiables(dss);

  EXPECT_ABSTRACT_METHOD("LBar;.baz:()V");

  EXPECT_EQ(1, stats.abstracted_classes);
  EXPECT_EQ(1, stats.abstracted_vmethods);
  EXPECT_EQ(0, stats.removed_vmethods);
  EXPECT_EQ(0, stats.throw_null_methods);
  EXPECT_EQ(0, stats.get_uninstantiables);
}

TEST_F(RemoveUninstantiablesTest, RemovePackagePrivateVMethod) {
  DexStoresVector dss{DexStore{"test_store"}};

  auto* Foo = def_class("LFoo;", Foo_baz, Foo_qux, Foo_fox);
  auto* Bar = def_class("LBar;", Bar_init, Bar_baz, Bar_qux);
  auto* FooBar = def_class("LFooBar;", FooBar_baz);
  dss.back().add_classes({Foo, Bar, FooBar});
  FooBar->set_super_class(Foo->get_type());

  DexField::make_field("LBar;.mFoo:LFoo;")->make_concrete(ACC_PUBLIC);
  DexField::make_field("LFoo;.mBar:LBar;")->make_concrete(ACC_PUBLIC);

  auto* Foo_baz_method = DexMethod::get_method("LFoo;.baz:()V")->as_def();
  auto* FooBar_baz_method = DexMethod::get_method("LFooBar;.baz:()V")->as_def();
  EXPECT_TRUE(is_public(Foo_baz_method));
  EXPECT_TRUE(is_public(FooBar_baz_method));
  set_package_private(Foo_baz_method);
  set_package_private(FooBar_baz_method);

  run_remove_uninstantiables(dss);

  EXPECT_NO_METHOD_DEF("LFooBar;.baz:()V");
}

TEST_F(RemoveUninstantiablesTest, NpeStubsGetSourceBlocks) {
  g_redex->instrument_mode = true;

  auto* foo = def_class("LFoo;");
  foo->set_access(foo->get_access() | ACC_INTERFACE | ACC_ABSTRACT);

  auto* void_t = type::_void();
  auto* void_void =
      DexProto::make_proto(void_t, DexTypeList::make_type_list({}));
  create_abstract_method(foo, "doStuff", void_void);

  auto actual_ir = assembler::ircode_from_string(R"((
    (load-param-object v0)
    (invoke-interface (v0) "LFoo;.doStuff:()V;")
    (return-void)
  ))");

  actual_ir->build_cfg();
  auto& cfg = actual_ir->cfg();

  // Insert source blocks so the method has profiling metadata.
  source_blocks::insert_source_blocks(DexString::make_string("LTest;.test:()V"),
                                      &cfg);

  // Run the replacement.
  auto stats = replace_uninstantiable_refs(cfg);
  EXPECT_EQ(1, stats.invokes);

  // Verify every non-exit block has a source block.
  for (auto* block : cfg.blocks()) {
    if (block == cfg.exit_block()) {
      continue;
    }

    auto* sb = source_blocks::get_first_source_block(block);
    EXPECT_NE(nullptr, sb) << "Block B" << block->id()
                           << " is missing source block";
  }

  // Additionally, verify that throw-delineated segments within blocks have
  // source blocks. Check that after NEW_INSTANCE NullPointerException, a
  // source block exists before the next throwing instruction.
  auto* npe_type = DexType::get_type("Ljava/lang/NullPointerException;");
  ASSERT_NE(nullptr, npe_type);

  for (auto* block : cfg.blocks()) {
    bool need_sb = false;
    for (auto it = block->begin(); it != block->end(); ++it) {
      if (it->type == MFLOW_SOURCE_BLOCK) {
        need_sb = false;
        continue;
      }
      if (it->type != MFLOW_OPCODE) {
        continue;
      }
      auto op = it->insn->opcode();
      // move_result_pseudo is part of the preceding instruction group.
      if (opcode::is_a_move_result_pseudo(op)) {
        continue;
      }
      EXPECT_FALSE(need_sb) << "Missing source block before instruction "
                            << show(it->insn) << " in block B" << block->id();
      need_sb =
          (op == OPCODE_NEW_INSTANCE && it->insn->get_type() == npe_type) ||
          (op == OPCODE_INVOKE_DIRECT &&
           it->insn->get_method()->get_class() == npe_type) ||
          opcode::is_throw(op);
    }
  }

  actual_ir->clear_cfg();
}

TEST_F(RemoveUninstantiablesTest, NpeStubsGetSourceBlocksFieldAccess) {
  g_redex->instrument_mode = true;

  def_class("LFoo;");
  def_class("LBar;", Bar_init);

  DexField::make_field("LFoo;.a:I")->make_concrete(ACC_PUBLIC);

  auto actual_ir = assembler::ircode_from_string(R"((
    (load-param-object v0)
    (iget v0 "LFoo;.a:I")
    (move-result-pseudo v1)
    (return-void)
  ))");

  actual_ir->build_cfg();
  auto& cfg = actual_ir->cfg();

  source_blocks::insert_source_blocks(
      DexString::make_string("LTest;.test2:()V"), &cfg);

  auto stats = replace_uninstantiable_refs(cfg);
  EXPECT_EQ(1, stats.field_accesses_on_uninstantiable);

  // Verify throw-delineated segments have source blocks.
  auto* npe_type = DexType::get_type("Ljava/lang/NullPointerException;");
  ASSERT_NE(nullptr, npe_type);

  for (auto* block : cfg.blocks()) {
    bool need_sb = false;
    for (auto it = block->begin(); it != block->end(); ++it) {
      if (it->type == MFLOW_SOURCE_BLOCK) {
        need_sb = false;
        continue;
      }
      if (it->type != MFLOW_OPCODE) {
        continue;
      }
      auto op = it->insn->opcode();
      // move_result_pseudo is part of the preceding instruction group.
      if (opcode::is_a_move_result_pseudo(op)) {
        continue;
      }
      EXPECT_FALSE(need_sb) << "Missing source block before instruction "
                            << show(it->insn) << " in block B" << block->id();
      need_sb =
          (op == OPCODE_NEW_INSTANCE && it->insn->get_type() == npe_type) ||
          (op == OPCODE_INVOKE_DIRECT &&
           it->insn->get_method()->get_class() == npe_type) ||
          opcode::is_throw(op);
    }
  }

  actual_ir->clear_cfg();
}

const char* const Base_init = R"(
(method (public) "LBase;.<init>:()V"
  ((load-param-object v0)
   (return-void))
))";

const char* const Base_m = R"(
(method (public) "LBase;.m:()V"
  ((load-param-object v0)
   (return-void))
))";

const char* const Sub_m = R"(
(method (public) "LSub;.m:()V"
  ((load-param-object v0)
   (return-void))
))";

const char* const User_newBase = R"(
(method (public static) "LUser;.newBase:()V"
  ((new-instance "LBase;")
   (move-result-pseudo-object v0)
   (invoke-direct (v0) "LBase;.<init>:()V")
   (return-void))
))";

// `Sub.m` overrides `Base.m`, and `Sub` is never instantiated, so `Sub.m` is
// deleted. `user`, or the value of the static field `field` of `User`, holds a
// method handle of `Sub.m`.
void run_with_handle_of_uncallable_override(DexMethod* user,
                                            DexField* field = nullptr) {
  DexStoresVector dss{DexStore{"test_store"}};
  auto* Base = def_class("LBase;", Base_init, Base_m);
  auto* Sub = def_class("LSub;", Sub_m);
  Sub->set_super_class(Base->get_type());
  auto* User = def_class("LUser;", User_newBase);
  User->add_method(user);
  if (field != nullptr) {
    User->add_field(field);
  }
  dss.back().add_classes({Base, Sub, User});

  auto stats = run_remove_uninstantiables(dss);

  EXPECT_NO_METHOD_DEF("LSub;.m:()V");
  EXPECT_EQ(1, stats.removed_vmethods);
}

// The methods that the method handles in the code of `method` name.
std::vector<DexMethodRef*> method_handle_methods(const DexMethod* method) {
  std::vector<DexMethodRef*> methods;
  for (const auto& mie : InstructionIterable(method->get_code())) {
    for_each_method_handle(mie.insn, [&](const DexMethodHandle* handle) {
      methods.push_back(handle->methodref());
    });
  }
  return methods;
}

// The handle's type takes its receiver type from the class of the method it
// names, so it keeps naming `Sub.m`, now through a reference that resolves to
// `Base.m`, unlike an invoke-virtual, which would name `Base.m`.
TEST_F(RemoveUninstantiablesTest, DeleteUncallableOverrideThatAHandleNames) {
  auto* user = assembler::method_from_string(R"(
    (method (public static) "LUser;.handle:()Ljava/lang/invoke/MethodHandle;"
     ((const-method-handle invoke-instance "LSub;.m:()V")
      (move-result-pseudo-object v0)
      (return-object v0)))
  )");

  run_with_handle_of_uncallable_override(user);

  auto* sub_m = DexMethod::get_method("LSub;.m:()V");
  ASSERT_NE(nullptr, sub_m);
  EXPECT_EQ(method_handle_methods(user), std::vector<DexMethodRef*>{sub_m});
  EXPECT_EQ(resolve_method_deprecated(sub_m, MethodSearch::Virtual),
            DexMethod::get_method("LBase;.m:()V"));
}

TEST_F(RemoveUninstantiablesTest,
       DeleteUncallableOverrideThatACallSiteArgumentNames) {
  auto* user = assembler::method_from_string(R"(
    (method (public static) "LUser;.run:()V"
     ((invoke-static () "LUser;.placeholder:()V")
      (return-void)))
  )");
  std::vector<std::unique_ptr<DexEncodedValue>> args;
  args.push_back(
      std::make_unique<DexEncodedValueMethodHandle>(redex::make_method_handle(
          METHOD_HANDLE_TYPE_INVOKE_INSTANCE, "LSub;.m:()V")));
  redex::make_invoke_custom(user->get_code(), "run", "()V", std::move(args));

  run_with_handle_of_uncallable_override(user);

  auto* sub_m = DexMethod::get_method("LSub;.m:()V");
  ASSERT_NE(nullptr, sub_m);
  auto methods = method_handle_methods(user);
  EXPECT_NE(std::find(methods.begin(), methods.end(), sub_m), methods.end());
}

TEST_F(RemoveUninstantiablesTest,
       DeleteUncallableOverrideThatAStaticFieldValueNames) {
  auto* user = assembler::method_from_string(R"(
    (method (public static) "LUser;.run:()V"
     ((return-void)))
  )");
  auto* field =
      DexField::make_field("LUser;.HANDLE:Ljava/lang/invoke/MethodHandle;")
          ->make_concrete(
              ACC_PUBLIC | ACC_STATIC | ACC_FINAL,
              std::make_unique<DexEncodedValueMethodHandle>(
                  redex::make_method_handle(METHOD_HANDLE_TYPE_INVOKE_INSTANCE,
                                            "LSub;.m:()V")));

  run_with_handle_of_uncallable_override(user, field);

  auto* sub_m = DexMethod::get_method("LSub;.m:()V");
  ASSERT_NE(nullptr, sub_m);
  EXPECT_EQ(redex::encoded_value_as<DexEncodedValueMethodHandle>(
                field->get_static_value())
                ->methodhandle()
                ->methodref(),
            sub_m);
}

} // namespace
