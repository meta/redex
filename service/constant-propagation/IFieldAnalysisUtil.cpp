/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "IFieldAnalysisUtil.h"

#include <algorithm>
#include <optional>

#include "ClassHierarchy.h"
#include "Debug.h"
#include "MethodOverrideGraph.h"
#include "Resolver.h"
#include "Walkers.h"

namespace {

/*
 * A virtual or interface call runs the method its receiver's class implements,
 * not necessarily the method it resolves to. When the receiver is an instance
 * of a given class, which `this` is in that class's constructor, the call can
 * also run the implementation the class inherits, or an override declared in
 * the class, in one of its subclasses, or as a default method of an interface
 * that one of them implements.
 */
class DispatchTargets {
 public:
  DispatchTargets(const method_override_graph::Graph& graph,
                  const ClassHierarchy& hierarchy,
                  const DexClass* cls)
      : m_graph(graph), m_hierarchy(hierarchy), m_type(cls->get_type()) {
    collect_inherited_candidates(cls);
  }

  // Whether `type` is the class, one of its superclasses or an interface they
  // implement, including those without a definition.
  bool is_supertype(const DexType* type) const {
    return m_supertypes.count(type) != 0u;
  }

  // Calls `f` on each method other than `callee` that `insn`, which resolves to
  // `callee`, may run on an instance of the class.
  template <typename F>
  void for_each_other_target(const IRInstruction* insn,
                             const DexMethod* callee,
                             const F& f) const {
    auto op = insn->opcode();
    if (callee == nullptr ||
        (op != OPCODE_INVOKE_VIRTUAL && op != OPCODE_INVOKE_INTERFACE)) {
      return;
    }
    for_each_inherited_implementation(callee, [&](const DexMethod* method) {
      if (method != callee) {
        f(method);
      }
    });
    // Abstract methods never run.
    method_override_graph::all_overriding_methods(
        m_graph,
        callee,
        [&](const DexMethod* method) {
          if (!is_abstract(method)) {
            f(method);
          }
          return true;
        },
        /* include_interfaces */ true,
        /* base_type */ m_type);
    for_each_overriding_default_method(callee, f);
  }

 private:
  // Calls `f` on each default method that overrides `callee` and may run on an
  // instance of the class: one whose interface the class or a subclass
  // implements. The `base_type` filter above keeps only methods whose class,
  // or a class they implement an interface method for, is the class or a
  // subclass, so it leaves these out. This ignores class methods that shadow
  // the default method, which only adds methods to check.
  template <typename F>
  void for_each_overriding_default_method(const DexMethod* callee,
                                          const F& f) const {
    // Only interface methods have default methods overriding them.
    if (!m_graph.get_node(callee).is_interface) {
      return;
    }
    method_override_graph::all_overriding_methods(
        m_graph,
        callee,
        [&](const DexMethod* method) {
          if (!is_abstract(method) && m_graph.get_node(method).is_interface &&
              is_implemented_in_hierarchy(method->get_class())) {
            f(method);
          }
          return true;
        },
        /* include_interfaces */ true);
  }

  // Whether the class or a subclass implements `intf`.
  bool is_implemented_in_hierarchy(const DexType* intf) const {
    auto types = get_all_children(m_hierarchy, m_type);
    types.insert(m_type);
    return std::any_of(types.begin(), types.end(), [&](const DexType* type) {
      return type::check_cast(type, intf);
    });
  }

  static bool matches(const DexMethod* method, const DexMethod* callee) {
    return method->get_name() == callee->get_name() &&
           method->get_proto() == callee->get_proto();
  }

  // Collects the classes of the superclass chain, the default methods of all
  // interfaces they implement, and the types of both. A superclass or
  // interface without a definition makes the class's inherited
  // implementations unknown.
  void collect_inherited_candidates(const DexClass* cls) {
    std::vector<const DexType*> interfaces;
    while (cls != nullptr) {
      m_superclass_chain.push_back(cls);
      m_supertypes.insert(cls->get_type());
      for (const auto* intf : *cls->get_interfaces()) {
        interfaces.push_back(intf);
      }
      const auto* super_type = cls->get_super_class();
      cls = super_type == nullptr ? nullptr : type_class(super_type);
      if (super_type != nullptr && cls == nullptr) {
        m_supertypes.insert(super_type);
        m_inherited_known = false;
      }
    }
    while (!interfaces.empty()) {
      const auto* intf = interfaces.back();
      interfaces.pop_back();
      if (!m_supertypes.insert(intf).second) {
        continue;
      }
      const auto* intf_cls = type_class(intf);
      if (intf_cls == nullptr) {
        m_inherited_known = false;
        continue;
      }
      for (const auto* method : intf_cls->get_vmethods()) {
        if (!is_abstract(method)) {
          m_default_methods.push_back(method);
        }
      }
      for (const auto* super_intf : *intf_cls->get_interfaces()) {
        interfaces.push_back(super_intf);
      }
    }
  }

  // Calls `f` on each implementation of `callee` that the class may inherit:
  // the method declared by the nearest class of its superclass chain, or else
  // a default method of an interface it implements. When a superclass or an
  // interface has no definition, that implementation is unknown, and `f` gets
  // nullptr, which callers treat as a method that may read every field.
  //
  // This does not use resolve_method: its search for default methods asserts
  // that every interface in the hierarchy is defined, and input apps can
  // implement interfaces whose definitions are absent.
  template <typename F>
  void for_each_inherited_implementation(const DexMethod* callee,
                                         const F& f) const {
    for (const auto* cls : m_superclass_chain) {
      for (const auto* method : cls->get_vmethods()) {
        if (matches(method, callee)) {
          // A class's method takes precedence over default methods; an
          // abstract one leaves the implementation to the subclasses.
          if (!is_abstract(method)) {
            f(method);
          }
          return;
        }
      }
    }
    if (!m_inherited_known) {
      f(nullptr);
      return;
    }
    for (const auto* method : m_default_methods) {
      if (matches(method, callee)) {
        f(method);
      }
    }
  }

  const method_override_graph::Graph& m_graph;
  const ClassHierarchy& m_hierarchy;
  const DexType* m_type;
  std::vector<const DexClass*> m_superclass_chain;
  std::vector<const DexMethod*> m_default_methods;
  bool m_inherited_known{true};
  UnorderedSet<const DexType*> m_supertypes;
};

namespace check_this {
using ThisDomain = sparta::ConstantAbstractDomain<bool>;
using ThisEnvironment =
    sparta::PatriciaTreeMapAbstractEnvironment<uint32_t, ThisDomain>;

/**
 * Fixpoint analysis to track register that may hold "this" object, so that we
 * can use this info to find methods that are invoked on "this" object.
 * TODO(suree404): Switch to use existed LocalPointerAnalysis.
 */
class ThisObjectAnalysis final
    : public sparta::MonotonicFixpointIterator<cfg::GraphInterface,
                                               ThisEnvironment> {
 public:
  explicit ThisObjectAnalysis(const cfg::ControlFlowGraph* cfg,
                              const DexMethod* method,
                              size_t this_param_reg)
      : MonotonicFixpointIterator(*cfg, cfg->num_blocks()),
        m_method(method),
        m_this_param_reg(this_param_reg) {}
  void analyze_node(const NodeId& node, ThisEnvironment* env) const override {
    for (auto& mie : InstructionIterable(*node)) {
      analyze_instruction(mie.insn, env);
    }
  }
  ThisEnvironment analyze_edge(
      cfg::Edge* const&,
      const ThisEnvironment& exit_state_at_source) const override {
    return exit_state_at_source;
  }

  std::optional<std::vector<const IRInstruction*>> collect_invokes_on_this() {
    std::vector<const IRInstruction*> invokes;
    const auto* code = m_method->get_code();
    const auto& cfg = code->cfg();
    for (cfg::Block* block : cfg.blocks()) {
      auto env = get_entry_state_at(block);

      auto ii = InstructionIterable(block);
      for (auto it = ii.begin(); it != ii.end(); it++) {
        IRInstruction* insn = it->insn;
        auto op = insn->opcode();
        if (opcode::is_an_invoke(op)) {
          bool use_this = false;
          for (auto src : insn->srcs()) {
            auto this_info = env.get(src).get_constant();
            if (!this_info || *this_info) {
              use_this = true;
              break;
            }
          }
          if (use_this) {
            invokes.push_back(insn);
          }
        } else if (op == OPCODE_IPUT_OBJECT || op == OPCODE_SPUT_OBJECT ||
                   op == OPCODE_APUT_OBJECT) {
          auto this_info = env.get(insn->src(0)).get_constant();
          if (!this_info || *this_info) {
            return std::nullopt;
          }
        } else if (op == OPCODE_FILLED_NEW_ARRAY) {
          for (auto src : insn->srcs()) {
            auto this_info = env.get(src).get_constant();
            if (!this_info || *this_info) {
              return std::nullopt;
            }
          }
        }
        analyze_instruction(insn, &env);
      }
    }
    return invokes;
  }

 private:
  void analyze_instruction(IRInstruction* insn, ThisEnvironment* env) const {
    auto default_case = [&]() {
      if (insn->has_dest()) {
        env->set(insn->dest(), ThisDomain(false));
      } else if (insn->has_move_result_any()) {
        env->set(RESULT_REGISTER, ThisDomain(false));
      }
    };
    switch (insn->opcode()) {
    case OPCODE_MOVE_OBJECT: {
      env->set(insn->dest(), env->get(insn->src(0)));
      break;
    }
    case IOPCODE_LOAD_PARAM_OBJECT: {
      if (insn->dest() == m_this_param_reg) {
        env->set(insn->dest(), ThisDomain(true));
      } else {
        env->set(insn->dest(), ThisDomain(false));
      }
      break;
    }
    case OPCODE_CHECK_CAST: {
      env->set(RESULT_REGISTER, env->get(insn->src(0)));
      break;
    }
    case IOPCODE_MOVE_RESULT_PSEUDO_OBJECT: {
      env->set(insn->dest(), env->get(RESULT_REGISTER));
      break;
    }
    default: {
      default_case();
      break;
    }
    }
  }
  const DexMethod* m_method;
  size_t m_this_param_reg;
};
} // namespace check_this

/**
 * Finds the instance fields of one class that code running during the
 * construction of an instance may read, and adds them to a blocklist.
 */
class EarlyReadFinder {
 public:
  EarlyReadFinder(const DispatchTargets& dispatch_targets,
                  const UnorderedSet<std::string>& allowlist_method_names,
                  const DexClass* ifield_cls,
                  InsertOnlyConcurrentSet<DexField*>* blocklist_ifields)
      : m_dispatch_targets(dispatch_targets),
        m_allowlist_method_names(allowlist_method_names),
        m_ifield_cls(ifield_cls),
        m_blocklist_ifields(blocklist_ifields) {}

  /**
   * Visits the methods that an invoke instruction may call. Returns false if
   * all ifields are excluded - no need to check further.
   */
  bool visit_invoke(const IRInstruction* insn, const DexMethod* caller) {
    auto* insn_method = insn->get_method();
    auto* callee =
        resolve_method_deprecated(insn_method, opcode_to_search(insn), caller);
    if (insn->opcode() == OPCODE_INVOKE_DIRECT ||
        insn->opcode() == OPCODE_INVOKE_STATIC) {
      // For invoke on a direct/static method, if we can't resolve them or
      // there is no code after resolved, those must be methods not
      // not implemented by us, so they won't access our instance fields
      // as well.
      if ((callee == nullptr) || (callee->get_code() == nullptr)) {
        return true;
      }
    } else {
      bool no_current_type = true;
      // No need to check on methods whose class/arguments are not
      // superclass or interface of ifield_cls.
      if (callee != nullptr &&
          !m_dispatch_targets.is_supertype(callee->get_class())) {
        for (const auto& type : *callee->get_proto()->get_args()) {
          if (m_dispatch_targets.is_supertype(type)) {
            no_current_type = false;
          }
        }
      } else if (callee == nullptr &&
                 !m_dispatch_targets.is_supertype(insn_method->get_class())) {
        for (const auto& type : *insn_method->get_proto()->get_args()) {
          if (m_dispatch_targets.is_supertype(type)) {
            no_current_type = false;
          }
        }
      } else {
        no_current_type = false;
      }
      if (no_current_type) {
        return true;
      }
    }
    return visit_dispatch_targets(insn, callee);
  }

  /**
   * Adds the instance fields of ifield_cls that the method reads, directly or
   * through its callees. Returns false if all ifields are excluded - no need
   * to check further.
   */
  bool visit_method(const DexMethod* method) {
    if (!m_visited.emplace(method).second) {
      return true;
    }
    if (method != nullptr) {
      for (const auto& name : UnorderedIterable(m_allowlist_method_names)) {
        // Allowed methods name from config, ignore.
        // We have this allowlist so that we can ignore some methods that
        // are safe and won't read instance field.
        // TODO: Switch to a proper interprocedural fixpoint analysis.
        if (method->get_name()->str() == name) {
          return true;
        }
      }
    }
    if (method == nullptr || method->get_code() == nullptr) {
      // We can't track down further, don't process any ifields from ifield_cls.
      return blocklist_all();
    }
    bool res = true;
    cfg_adapter::iterate_with_iterator(
        const_cast<IRCode*>(method->get_code()),
        [&](const IRList::iterator& it) {
          auto* insn = it->insn;
          if (opcode::is_an_iget(insn->opcode())) {
            // Meet accessing of a ifield in a method called from <init>, add
            // to blocklist.
            auto* field =
                resolve_field(insn->get_field(), FieldSearch::Instance);
            if (field != nullptr &&
                field->get_class() == m_ifield_cls->get_type()) {
              m_blocklist_ifields->insert(field);
            }
          } else if (opcode::is_an_invoke(insn->opcode()) &&
                     !insn->has_method()) {
            // invoke-polymorphic and invoke-custom run unknown code, which can
            // read the fields of an object passed to it.
            const auto* args = insn->get_callsite_proto()->get_args();
            if (std::any_of(args->begin(), args->end(), [&](const DexType* t) {
                  return m_dispatch_targets.is_supertype(t);
                })) {
              if (!visit_method(/* method */ nullptr)) {
                res = false;
                return cfg_adapter::LOOP_BREAK;
              }
            }
          } else if (opcode::is_a_method_invoke(insn->opcode())) {
            // Recusive check every methods accessed from <init>.
            if (!visit_invoke(insn, method)) {
              res = false;
              return cfg_adapter::LOOP_BREAK;
            }
          }
          return cfg_adapter::LOOP_CONTINUE;
        });
    return res;
  }

  /**
   * Adds the instance fields of ifield_cls that the constructor may read
   * before storing them.
   */
  void visit_constructor(const DexMethod* ctor) {
    const auto& cfg = ctor->get_code()->cfg();
    check_this::ThisObjectAnalysis fixpoint(
        &cfg, ctor, cfg.get_first_param_instruction()->dest());
    fixpoint.run(check_this::ThisEnvironment());
    // Only check on methods called with this object as arguments. They
    // include the superclass constructor and any constructor that gets
    // this as an argument: each can run code that reads this object's
    // fields.
    auto invokes = fixpoint.collect_invokes_on_this();
    if (!invokes) {
      // This object escaped to heap, blocklist all.
      blocklist_all();
      return;
    }
    for (const auto* insn : *invokes) {
      if (!insn->has_method()) {
        // invoke-polymorphic and invoke-custom run unknown code.
        blocklist_all();
        return;
      }
      auto* callee = resolve_method_deprecated(insn->get_method(),
                                               opcode_to_search(insn), ctor);
      if ((insn->opcode() == OPCODE_INVOKE_STATIC ||
           insn->opcode() == OPCODE_INVOKE_DIRECT) &&
          (callee == nullptr || callee->get_code() == nullptr)) {
        continue;
      }
      // A callee that did not resolve makes visit_method give up on the class.
      if (!visit_dispatch_targets(insn, callee)) {
        return;
      }
    }
  }

 private:
  /**
   * Visits the callee of the invoke instruction, and the other methods that
   * it may dispatch to on an instance of ifield_cls. Returns false if all
   * ifields are excluded - no need to check further.
   */
  bool visit_dispatch_targets(const IRInstruction* insn,
                              const DexMethod* callee) {
    bool keep_going = visit_method(callee);
    m_dispatch_targets.for_each_other_target(
        insn, callee, [&](const DexMethod* target) {
          keep_going = keep_going && visit_method(target);
        });
    return keep_going;
  }

  bool blocklist_all() {
    for (const auto& field : m_ifield_cls->get_ifields()) {
      m_blocklist_ifields->insert(field);
    }
    return false;
  }

  const DispatchTargets& m_dispatch_targets;
  const UnorderedSet<std::string>& m_allowlist_method_names;
  const DexClass* m_ifield_cls;
  InsertOnlyConcurrentSet<DexField*>* m_blocklist_ifields;
  UnorderedSet<const DexMethod*> m_visited;
};

/**
 * This function add ifields like x in following example in blocklist to avoid
 * inlining them.
 *   class Foo {
 *     final int x;
 *     Foo() {
 *       bar();
 *       x = 1;
 *     }
 *     bar() {
 *       // x is zero here, we don't want FinalInline to make it take value 1.
 *       if (x == 1) { ... }
 *     }
 *   }
 */
InsertOnlyConcurrentSet<DexField*> get_ifields_read_in_callees(
    const Scope& scope,
    const UnorderedSet<std::string>& allowlist_method_names,
    const method_override_graph::Graph& override_graph) {
  InsertOnlyConcurrentSet<DexField*> return_ifields;
  auto hierarchy = build_type_hierarchy(scope);
  std::vector<DexClass*> relevant_classes;
  for (auto* cls : scope) {
    if (cls->is_external()) {
      continue;
    }
    auto ctors = cls->get_ctors();
    if (ctors.size() != 1 || cls->get_ifields().empty()) {
      // We are not inlining ifields in multi-ctors class so can also ignore
      // them here.
      // Also no need to proceed if there is no ifields for a class.
      continue;
    }
    auto* ctor = ctors.front();
    auto* code = ctor->get_code();
    if (code != nullptr) {
      relevant_classes.push_back(cls);
    }
  }
  walk::parallel::classes(relevant_classes, [](DexClass* cls) {
    auto* ctor = cls->get_ctors().front();
    auto* code = ctor->get_code();
    code->cfg().calculate_exit_block();
  });
  walk::parallel::classes(
      relevant_classes,
      [&return_ifields, &override_graph, &hierarchy,
       &allowlist_method_names](DexClass* cls) {
        auto* ctor = cls->get_ctors().front();
        auto* code = ctor->get_code();
        always_assert(code != nullptr);
        DispatchTargets dispatch_targets(override_graph, hierarchy, cls);
        EarlyReadFinder finder(dispatch_targets, allowlist_method_names, cls,
                               &return_ifields);
        finder.visit_constructor(ctor);
      });
  return return_ifields;
}

} // namespace

namespace constant_propagation {

UnorderedSet<const DexField*> gather_ifields_written_only_by_constructors(
    const Scope& scope) {
  UnorderedSet<DexField*> ifields_candidates;
  walk::fields(scope, [&](DexField* field) {
    // Collect instance field candidates that are non external,
    // and can be deleted.
    if (is_static(field) || field->is_external() || !can_delete(field) ||
        is_volatile(field)) {
      return;
    }
    ifields_candidates.emplace(field);
  });

  InsertOnlyConcurrentSet<DexField*> invalid_candidates;
  walk::parallel::code(scope, [&](DexMethod* method, IRCode& code) {
    // Remove candidate field if it was written in code other than its class'
    // init function, or in an init function excluded from optimization.
    cfg_adapter::iterate_with_iterator(&code, [&](const IRList::iterator& it) {
      for_each_field_access(
          it->insn,
          [&](IROpcode op, DexFieldRef* field_ref,
              const DexMethodHandle* method_handle) {
            if (!opcode::is_an_iput(op)) {
              return;
            }
            // A method handle can be called anywhere, on any object.
            if (method_handle != nullptr) {
              if (auto* field = resolve_field_handle(method_handle)) {
                invalid_candidates.insert(field);
              }
              return;
            }
            auto* field = resolve_field(field_ref, FieldSearch::Instance);
            if (field == nullptr) {
              return;
            }
            if (method::is_init(method) &&
                method->get_class() == field->get_class()) {
              // See `ConstructorAccesses` on constructors excluded from
              // optimization.
              if (method->rstate.no_optimizations()) {
                invalid_candidates.insert(field);
              }
              return;
            }
            // We assert that final fields are not modified outside of <init>
            // methods. javac seems to enforce this, but it's unclear if the
            // JVM spec actually forbids that. Doing the check here simplifies
            // the constant propagation analysis later -- we can determine the
            // values of these fields without analyzing any methods invoked
            // from the <init> methods.
            always_assert_log(
                !is_final(field),
                "FinalInlinePassV2: encountered one final instance "
                "field been changed outside of its class's <init> "
                "file, for temporary solution set "
                "\"inline_instance_field\" in \"FinalInlinePassV2\" "
                "to be false. Field: %s",
                SHOW(field));
            invalid_candidates.insert(field);
          });
      return cfg_adapter::LOOP_CONTINUE;
    });
  });
  UnorderedSet<const DexField*> written_only_by_constructors;
  for (DexField* field : UnorderedIterable(ifields_candidates)) {
    if (invalid_candidates.count(field) == 0u) {
      written_only_by_constructors.emplace(field);
    }
  }
  return written_only_by_constructors;
}

UnorderedSet<const DexField*> gather_constructor_only_ifields(
    const Scope& scope,
    const local_pointers::ConstructorAccessesMap& constructor_accesses) {
  auto constructor_only_ifields =
      gather_ifields_written_only_by_constructors(scope);
  ConcurrentSet<const DexField*> stored_on_other_objects;
  walk::parallel::code(scope, [&](DexMethod* method, IRCode& code) {
    if (!method::is_init(method) || method->rstate.no_optimizations()) {
      return;
    }
    // Remove candidate field if its class's init function writes it to an
    // object other than the one it initializes.
    const local_pointers::ConstructorAccesses* accesses = nullptr;
    for (const auto& mie : cfg::InstructionIterable(code.cfg())) {
      auto* insn = mie.insn;
      if (!opcode::is_an_iput(insn->opcode())) {
        continue;
      }
      auto* field = resolve_field(insn->get_field(), FieldSearch::Instance);
      if (field == nullptr || field->get_class() != method->get_class() ||
          constructor_only_ifields.count(field) == 0u) {
        continue;
      }
      if (accesses == nullptr) {
        auto it = constructor_accesses.find(method);
        always_assert_log(it != constructor_accesses.end(),
                          "Unanalyzed constructor %s", SHOW(method));
        accesses = it->second.get();
      }
      // `ConstructorAccesses` records every access to a resolved field of
      // the constructor's class, so it knows this store.
      auto access = accesses->field_accesses().find(insn);
      always_assert_log(access != accesses->field_accesses().end(),
                        "Unclassified store to an own field in %s: %s",
                        SHOW(method), SHOW(insn));
      if (access->second.receiver != local_pointers::Receiver::This) {
        stored_on_other_objects.insert(field);
      }
    }
  });
  for (const auto* field : UnorderedIterable(stored_on_other_objects)) {
    constructor_only_ifields.erase(field);
  }
  return constructor_only_ifields;
}

EligibleIfields gather_safely_inferable_ifield_candidates(
    const Scope& scope,
    const UnorderedSet<const DexField*>& candidate_ifields,
    const UnorderedSet<std::string>& allowlist_method_names,
    const method_override_graph::Graph& method_override_graph) {
  EligibleIfields eligible_ifields;
  walk::fields(scope, [&](DexField* field) {
    if (candidate_ifields.count(field) == 0u) {
      return;
    }
    DexClass* field_cls = type_class(field->get_class());
    if (!is_final(field) && field_cls != nullptr &&
        field_cls->get_ctors().size() > 1) {
      // Class with multiple constructors, ignore it now.
      return;
    }
    eligible_ifields.emplace(field);
  });
  auto blocklist_ifields = get_ifields_read_in_callees(
      scope, allowlist_method_names, method_override_graph);
  for (DexField* field : UnorderedIterable(blocklist_ifields)) {
    eligible_ifields.erase(field);
  }
  return eligible_ifields;
}

} // namespace constant_propagation
