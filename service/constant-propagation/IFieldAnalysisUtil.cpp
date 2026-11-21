/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "IFieldAnalysisUtil.h"

#include <optional>

#include "Debug.h"
#include "TypeSystem.h"
#include "Walkers.h"

namespace {

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
  explicit ThisObjectAnalysis(cfg::ControlFlowGraph* cfg,
                              DexMethod* method,
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

  std::optional<UnorderedSet<DexMethod*>> collect_method_called_on_this() {
    UnorderedSet<DexMethod*> return_set;
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
            auto* insn_method = insn->get_method();
            auto* callee = resolve_method_deprecated(
                insn_method, opcode_to_search(insn), m_method);
            if (insn->opcode() == OPCODE_INVOKE_STATIC ||
                insn->opcode() == OPCODE_INVOKE_DIRECT) {
              if (callee != nullptr && callee->get_code() != nullptr) {
                return_set.emplace(callee);
              }
            } else {
              return_set.emplace(callee);
            }
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
    return return_set;
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
 * This function adds instance fields in cls_to_check that the method
 * accessed in blocklist_ifields.
 * Return false if all ifields are excluded - no need to check further.
 */
bool get_ifields_read(const UnorderedSet<std::string>& allowlist_method_names,
                      const UnorderedSet<const DexType*>& parent_intf_set,
                      const DexClass* ifield_cls,
                      const DexMethod* method,
                      ConcurrentSet<DexField*>* blocklist_ifields,
                      UnorderedSet<const DexMethod*>* visited) {
  if (visited->count(method) != 0u) {
    return true;
  }
  visited->emplace(method);
  if (method != nullptr) {
    if (method::is_init(method) &&
        (parent_intf_set.count(method->get_class()) != 0u)) {
      // For call on its parent's ctor, no need to proceed.
      return true;
    }
    for (const auto& name : UnorderedIterable(allowlist_method_names)) {
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
    for (const auto& field : ifield_cls->get_ifields()) {
      blocklist_ifields->emplace(field);
    }
    return false;
  }
  bool res = true;
  cfg_adapter::iterate_with_iterator(
      const_cast<IRCode*>(method->get_code()), [&](const IRList::iterator& it) {
        auto* insn = it->insn;
        if (opcode::is_an_iget(insn->opcode())) {
          // Meet accessing of a ifield in a method called from <init>, add
          // to blocklist.
          auto* field = resolve_field(insn->get_field(), FieldSearch::Instance);
          if (field != nullptr &&
              field->get_class() == ifield_cls->get_type()) {
            blocklist_ifields->emplace(field);
          }
        } else if (opcode::is_an_invoke(insn->opcode())) {
          auto* insn_method = insn->get_method();
          auto* callee = resolve_method_deprecated(
              insn_method, opcode_to_search(insn), method);
          if (insn->opcode() == OPCODE_INVOKE_DIRECT ||
              insn->opcode() == OPCODE_INVOKE_STATIC) {
            // For invoke on a direct/static method, if we can't resolve them or
            // there is no code after resolved, those must be methods not
            // not implemented by us, so they won't access our instance fields
            // as well.
            if ((callee == nullptr) || (callee->get_code() == nullptr)) {
              return cfg_adapter::LOOP_CONTINUE;
            }
          } else {
            bool no_current_type = true;
            // No need to check on methods whose class/arguments are not
            // superclass or interface of ifield_cls.
            if (callee != nullptr &&
                (parent_intf_set.count(callee->get_class()) == 0u)) {
              for (const auto& type : *callee->get_proto()->get_args()) {
                if (parent_intf_set.count(type) != 0u) {
                  no_current_type = false;
                }
              }
            } else if (callee == nullptr &&
                       (parent_intf_set.count(insn_method->get_class()) ==
                        0u)) {
              for (const auto& type : *insn_method->get_proto()->get_args()) {
                if (parent_intf_set.count(type) != 0u) {
                  no_current_type = false;
                }
              }
            } else {
              no_current_type = false;
            }
            if (no_current_type) {
              return cfg_adapter::LOOP_CONTINUE;
            }
          }
          // Recusive check every methods accessed from <init>.
          bool keep_going =
              get_ifields_read(allowlist_method_names, parent_intf_set,
                               ifield_cls, callee, blocklist_ifields, visited);
          if (!keep_going) {
            res = false;
            return cfg_adapter::LOOP_BREAK;
          }
        }
        return cfg_adapter::LOOP_CONTINUE;
      });
  return res;
}

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
ConcurrentSet<DexField*> get_ifields_read_in_callees(
    const Scope& scope,
    const UnorderedSet<std::string>& allowlist_method_names) {
  ConcurrentSet<DexField*> return_ifields;
  TypeSystem ts(scope);
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
      [&return_ifields, &ts, &allowlist_method_names](DexClass* cls) {
        auto* ctor = cls->get_ctors().front();
        auto* code = ctor->get_code();
        always_assert(code != nullptr);
        auto& cfg = code->cfg();
        check_this::ThisObjectAnalysis fixpoint(
            &cfg, ctor, cfg.get_first_param_instruction()->dest());
        fixpoint.run(check_this::ThisEnvironment());
        // Only check on methods called with this object as arguments.
        auto check_methods = fixpoint.collect_method_called_on_this();
        if (!check_methods) {
          // This object escaped to heap, blocklist all.
          for (const auto& field : cls->get_ifields()) {
            return_ifields.emplace(field);
          }
          return;
        }
        if (!check_methods->empty()) {
          UnorderedSet<const DexMethod*> visited;
          const auto& parent_chain = ts.parent_chain(cls->get_type());
          UnorderedSet<const DexType*> parent_intf_set{parent_chain.begin(),
                                                       parent_chain.end()};
          const auto& intf_set = ts.get_implemented_interfaces(cls->get_type());
          parent_intf_set.insert(intf_set.begin(), intf_set.end());
          for (auto* const method : UnorderedIterable(*check_methods)) {
            bool keep_going =
                get_ifields_read(allowlist_method_names, parent_intf_set, cls,
                                 method, &return_ifields, &visited);
            if (!keep_going) {
              break;
            }
          }
        }
      });
  return return_ifields;
}

} // namespace

namespace constant_propagation {

EligibleIfields gather_safely_inferable_ifield_candidates(
    const Scope& scope,
    const UnorderedSet<std::string>& allowlist_method_names) {
  EligibleIfields eligible_ifields;
  UnorderedSet<DexField*> ifields_candidates;
  walk::fields(scope, [&](DexField* field) {
    // Collect non-final instance field candidates that are non external,
    // and can be deleted.
    if (is_static(field) || field->is_external() || !can_delete(field) ||
        is_volatile(field)) {
      return;
    }
    if (is_final(field)) {
      eligible_ifields.emplace(field);
      return;
    }
    DexClass* field_cls = type_class(field->get_class());
    if (field_cls != nullptr && field_cls->get_ctors().size() > 1) {
      // Class with multiple constructors, ignore it now.
      return;
    }
    ifields_candidates.emplace(field);
  });

  ConcurrentSet<DexField*> invalid_candidates;
  walk::parallel::code(scope, [&](DexMethod* method, IRCode& code) {
    // Remove candidate field if it was written in code other than its class'
    // init function.
    cfg_adapter::iterate_with_iterator(&code, [&](const IRList::iterator& it) {
      auto* insn = it->insn;
      auto op = insn->opcode();
      if (opcode::is_an_iput(op)) {
        auto* field = resolve_field(insn->get_field(), FieldSearch::Instance);
        if (field == nullptr || (method::is_init(method) &&
                                 method->get_class() == field->get_class())) {
          // If couldn't resolve the field, or this method is this field's
          // class's init function, move on.
          return cfg_adapter::LOOP_CONTINUE;
        }
        // We assert that final fields are not modified outside of <init>
        // methods. javac seems to enforce this, but it's unclear if the JVM
        // spec actually forbids that. Doing the check here simplifies the
        // constant propagation analysis later -- we can determine the
        // values of these fields without analyzing any methods invoked from
        // the <init> methods.
        always_assert_log(!is_final(field),
                          "FinalInlinePassV2: encountered one final instance "
                          "field been changed outside of its class's <init> "
                          "file, for temporary solution set "
                          "\"inline_instance_field\" in \"FinalInlinePassV2\" "
                          "to be false. Field: %s",
                          SHOW(field));
        invalid_candidates.insert(field);
      }
      return cfg_adapter::LOOP_CONTINUE;
    });
  });
  for (DexField* field : UnorderedIterable(ifields_candidates)) {
    if (invalid_candidates.count(field) == 0u) {
      eligible_ifields.emplace(field);
    }
  }
  auto blocklist_ifields =
      get_ifields_read_in_callees(scope, allowlist_method_names);
  for (DexField* field : UnorderedIterable(blocklist_ifields)) {
    eligible_ifields.erase(field);
  }
  return eligible_ifields;
}

} // namespace constant_propagation
