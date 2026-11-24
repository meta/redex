/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ConstructorAccesses.h"

#include "ConcurrentContainers.h"
#include "ControlFlow.h"
#include "IRInstruction.h"
#include "MethodUtil.h"
#include "Resolver.h"
#include "ScopedCFG.h"
#include "Show.h"
#include "TypeUtil.h"
#include "Walkers.h"

namespace local_pointers {

namespace {

Receiver get_receiver(const PointerSet& pointers,
                      const IRInstruction* this_param) {
  if (pointers.is_value() && pointers.elements().size() == 1 &&
      pointers.contains(this_param)) {
    return Receiver::This;
  }
  if (pointers.is_top() || pointers.contains(this_param)) {
    return Receiver::MaybeThis;
  }
  return Receiver::Other;
}

// A call of a constructor that keeps its receiver: the other arguments may
// escape.
EscapeSummary keeps_receiver(const DexMethodRef* ctor) {
  EscapeSummary summary;
  uint16_t idx{1};
  for (const auto* arg : *ctor->get_proto()->get_args()) {
    if (!type::is_primitive(arg)) {
      summary.escaping_parameters.emplace(idx);
    }
    ++idx;
  }
  return summary;
}

// A constructor's first parameter is `this`.
const IRInstruction* get_this_param(const cfg::ControlFlowGraph& cfg) {
  auto params = cfg.get_param_instructions();
  always_assert_log(params.begin() != params.end() &&
                        params.begin()->insn->opcode() ==
                            IOPCODE_LOAD_PARAM_OBJECT,
                    "A constructor must start by loading `this`");
  return params.begin()->insn;
}

} // namespace

ConstructorAccesses::ConstructorAccesses(
    const cfg::ControlFlowGraph& cfg,
    const DexClass* cls,
    const UnorderedSet<const DexMethod*>& constructors_keeping_this) {
  // Only Object.<init> and analyzed constructors keep `this`, so a Throwable
  // has already escaped through Throwable.<init> when it can throw `this`.
  const auto callee_keeps_this = [&](const DexMethodRef* ctor) {
    const auto* def = ctor->as_def();
    return ctor == method::java_lang_Object_ctor() ||
           (def != nullptr && constructors_keeping_this.count(def) != 0u);
  };
  InvokeToSummaryMap summaries;
  for (auto* block : cfg.blocks()) {
    for (const auto& mie : InstructionIterable(block)) {
      const auto* callee = mie.insn->opcode() == OPCODE_INVOKE_DIRECT
                               ? mie.insn->get_method()
                               : nullptr;
      if (callee != nullptr && method::is_init(callee) &&
          callee_keeps_this(callee)) {
        summaries.emplace(mie.insn, keeps_receiver(callee));
      }
    }
  }
  const auto* this_param = get_this_param(cfg);
  FixpointIterator pointers(cfg, std::move(summaries));
  pointers.run(Environment());
  for (auto* block : cfg.blocks()) {
    auto env = pointers.get_entry_state_at(block);
    auto insns = InstructionIterable(block);
    if (insns.begin() != insns.end() && env.may_have_escaped(this_param)) {
      m_escapes.insert(insns.begin()->insn);
    }
    for (const auto& mie : insns) {
      const auto* insn = mie.insn;
      auto op = insn->opcode();
      const bool escaped_before = env.may_have_escaped(this_param);
      if (opcode::is_an_iget(op) || opcode::is_an_iput(op)) {
        const auto* field =
            resolve_field(insn->get_field(), FieldSearch::Instance);
        const auto receiver = get_receiver(
            env.get_pointers(insn->src(opcode::is_an_iput(op) ? 1 : 0)),
            this_param);
        // A reference that does not resolve can still only name a field of
        // the class it names or of that class's ancestors.
        const auto* owner = field != nullptr ? field->get_class()
                                             : insn->get_field()->get_class();
        if (field != nullptr && field->get_class() == cls->get_type()) {
          m_field_accesses.emplace(
              insn, FieldAccess{field, receiver, escaped_before});
        } else if (receiver != Receiver::Other &&
                   !type::check_cast(cls->get_type(), owner)) {
          m_accesses_other_fields = true;
        }
      } else if (op == OPCODE_INVOKE_DIRECT &&
                 method::is_init(insn->get_method())) {
        const auto* callee = insn->get_method();
        auto receiver =
            get_receiver(env.get_pointers(insn->src(0)), this_param);
        if (receiver != Receiver::Other &&
            callee->get_class() == cls->get_type()) {
          m_delegating_calls.emplace(
              insn, DelegatingCall{callee, receiver, escaped_before});
        }
      }
      pointers.analyze_instruction(insn, &env);
      if (!escaped_before && env.may_have_escaped(this_param)) {
        m_escapes.insert(insn);
      }
    }
  }
}

ConstructorAccessesMap analyze_constructors(
    const Scope& scope,
    const UnorderedSet<const DexMethod*>& constructors_keeping_this) {
  ConcurrentMap<const DexMethod*, std::unique_ptr<const ConstructorAccesses>>
      analyzed;
  walk::parallel::code(scope, [&](DexMethod* method, IRCode& code) {
    if (method::is_init(method)) {
      always_assert_log(code.cfg_built(), "No CFG for %s", SHOW(method));
      analyzed.emplace(method,
                       std::make_unique<const ConstructorAccesses>(
                           code.cfg(), type_class(method->get_class()),
                           constructors_keeping_this));
    }
  });
  ConstructorAccessesMap result;
  for (auto&& [method, accesses] : UnorderedIterable(analyzed)) {
    result.emplace(method, std::move(accesses));
  }
  return result;
}

UnorderedSet<const DexMethod*> get_constructors_keeping_this(
    const Scope& scope) {
  // Whether a constructor keeps `this` depends on the ancestor constructor it
  // calls, so each class comes after its ancestors in `scope`: classes are
  // grouped by how many of their ancestors are in `scope`, counting past
  // ancestors outside it.
  UnorderedSet<const DexType*> in_scope;
  for (const auto* cls : scope) {
    in_scope.insert(cls->get_type());
  }
  std::vector<std::vector<DexClass*>> levels;
  for (auto* cls : scope) {
    size_t depth = 0;
    for (const auto* super = type_class(cls->get_super_class());
         super != nullptr;
         super = type_class(super->get_super_class())) {
      if (in_scope.count(super->get_type()) != 0u) {
        ++depth;
      }
    }
    if (levels.size() <= depth) {
      levels.resize(depth + 1);
    }
    levels.at(depth).push_back(cls);
  }
  ConcurrentSet<const DexMethod*> keeping;
  for (const auto& level : levels) {
    walk::parallel::classes(level, [&](DexClass* cls) {
      // A constructor may call another constructor of its class, so iterate
      // until no more constructors are found to keep `this`. Cycles stay
      // escaping.
      // A constructor may call the constructor of any ancestor once Redex
      // has inlined the ones in between.
      UnorderedSet<const DexMethod*> known;
      for (const auto* ancestor = type_class(cls->get_super_class());
           ancestor != nullptr;
           ancestor = type_class(ancestor->get_super_class())) {
        for (const auto* ctor : ancestor->get_ctors()) {
          if (keeping.count(ctor) != 0u) {
            known.insert(ctor);
          }
        }
      }
      UnorderedSet<const DexMethod*> own;
      bool changed = true;
      while (changed) {
        changed = false;
        for (auto* ctor : cls->get_ctors()) {
          auto* code = ctor->get_code();
          // The code of a constructor excluded from optimization may differ
          // at runtime.
          if (!method::is_optimizable(ctor) || own.count(ctor) != 0u) {
            continue;
          }
          cfg::ScopedCFG cfg(code);
          if (ConstructorAccesses(*cfg, cls, known).keeps_this()) {
            own.insert(ctor);
            known.insert(ctor);
            changed = true;
          }
        }
      }
      insert_unordered_iterable(keeping, own);
    });
  }
  UnorderedSet<const DexMethod*> result;
  insert_unordered_iterable(result, keeping);
  return result;
}

} // namespace local_pointers
