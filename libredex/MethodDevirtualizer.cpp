/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "MethodDevirtualizer.h"

#include "AnnoUtils.h"
#include "Debug.h"
#include "MethodOverrideGraph.h"
#include "MethodUtil.h"
#include "Mutators.h"
#include "Resolver.h"
#include "Show.h"
#include "Trace.h"
#include "Walkers.h"

namespace mog = method_override_graph;

namespace {

using CallSiteReferences =
    std::map<const DexMethod*, std::vector<IRInstruction*>>;

struct CallCounter {
  uint32_t virtuals{0};
  uint32_t supers{0};
  uint32_t directs{0};

  CallCounter& operator+=(const CallCounter& that) {
    virtuals += that.virtuals;
    supers += that.supers;
    directs += that.directs;
    return *this;
  }
};

void patch_call_site(DexMethod* callee,
                     IRInstruction* method_inst,
                     CallCounter& counter) {
  auto op = method_inst->opcode();
  if (opcode::is_invoke_virtual(op)) {
    method_inst->set_opcode(OPCODE_INVOKE_STATIC);
    counter.virtuals++;
  } else if (opcode::is_invoke_super(op)) {
    method_inst->set_opcode(OPCODE_INVOKE_STATIC);
    counter.supers++;
  } else {
    redex_assert(opcode::is_invoke_direct(op));
    method_inst->set_opcode(OPCODE_INVOKE_STATIC);
    counter.directs++;
  }

  method_inst->set_method(callee);
}

void fix_call_sites(const std::vector<DexClass*>& scope,
                    const UnorderedSet<DexMethod*>& target_methods,
                    DevirtualizerMetrics& metrics,
                    bool drop_this = false) {
  const auto fixer = [&target_methods, drop_this](DexMethod* m) -> CallCounter {
    CallCounter call_counter;
    IRCode* code = m->get_code();
    if (code == nullptr) {
      return call_counter;
    }

    always_assert(code->cfg_built());
    auto& cfg = code->cfg();
    for (const MethodItemEntry& mie : InstructionIterable(cfg)) {
      IRInstruction* insn = mie.insn;
      if (!insn->has_method()) {
        continue;
      }

      MethodSearch type = drop_this ? MethodSearch::Any : MethodSearch::Virtual;
      auto* method = resolve_method_deprecated(insn->get_method(), type);
      if (method == nullptr || (target_methods.count(method) == 0u)) {
        continue;
      }

      always_assert(drop_this || !opcode::is_invoke_static(insn->opcode()));
      patch_call_site(method, insn, call_counter);

      if (drop_this) {
        auto nargs = insn->srcs_size();
        for (uint16_t i = 0; i < nargs - 1; i++) {
          insn->set_src(i, insn->src(i + 1));
        }
        insn->set_srcs_size(nargs - 1);
      }
    }

    return call_counter;
  };

  CallCounter call_counter = walk::parallel::methods<CallCounter>(scope, fixer);

  metrics.num_virtual_calls += call_counter.virtuals;
  metrics.num_super_calls += call_counter.supers;
  metrics.num_direct_calls += call_counter.directs;
}

void make_methods_static(const UnorderedSet<DexMethod*>& methods,
                         bool keep_this) {
  // TODO: Change callers to pass this as a sorted vector or an ordered set.
  auto meth_list = unordered_to_ordered(methods, compare_dexmethods);

  for (auto* method : meth_list) {
    TRACE(VIRT,
          2,
          "Staticized method: %s, keep this: %d",
          SHOW(method),
          keep_this);
    mutators::make_static(
        method, keep_this ? mutators::KeepThis::Yes : mutators::KeepThis::No);
  }
}

bool uses_this(const DexMethod* method) {
  auto* code = (const_cast<DexMethod*>(method))->get_code();
  always_assert_log(!is_static(method) && code != nullptr, "%s", SHOW(method));

  always_assert(code->cfg_built());
  auto& cfg = code->cfg();
  auto first = cfg.entry_block()->get_first_insn();
  always_assert(first != cfg.entry_block()->end());
  auto* this_insn = first->insn;
  always_assert(this_insn->opcode() == IOPCODE_LOAD_PARAM_OBJECT);
  auto const this_reg = this_insn->dest();
  for (const auto& mie : cfg::InstructionIterable(cfg)) {
    auto* insn = mie.insn;
    for (unsigned i = 0; i < insn->srcs_size(); i++) {
      if (this_reg == insn->src(i)) {
        return true;
      }
    }
  }
  return false;
}

std::vector<DexMethod*> get_devirtualizable_vmethods(
    const std::vector<DexClass*>& scope,
    const std::vector<DexClass*>& targets,
    const UnorderedSet<DexType*>& do_not_devirt_anno) {
  std::vector<DexMethod*> ret;
  const auto& override_graph = mog::build_graph(scope);
  auto vmethods = mog::get_non_true_virtuals(*override_graph, scope);
  auto targets_set = UnorderedSet<DexClass*>(targets.begin(), targets.end());

  for (auto* m : UnorderedIterable(vmethods)) {
    auto* cls = type_class(m->get_class());
    if (!has_any_annotation(m, do_not_devirt_anno) &&
        targets_set.count(cls) > 0) {
      ret.push_back(m);
    }
  }
  return ret;
}

std::vector<DexMethod*> get_devirtualizable_dmethods(
    const std::vector<DexClass*>& scope,
    const std::vector<DexClass*>& targets,
    const UnorderedSet<DexType*>& do_not_devirt_anno) {
  std::vector<DexMethod*> ret;
  auto targets_set = UnorderedSet<DexClass*>(targets.begin(), targets.end());
  for (auto* cls : scope) {
    if (targets_set.count(cls) == 0) {
      continue;
    }
    for (auto* m : cls->get_dmethods()) {
      if (method::is_any_init(m) || is_static(m)) {
        continue;
      }
      if (!has_any_annotation(m, do_not_devirt_anno)) {
        ret.push_back(m);
      }
    }
  }
  return ret;
}

} // namespace

void MethodDevirtualizer::verify_and_split(
    const std::vector<DexMethod*>& candidates,
    const InsertOnlyConcurrentSet<const DexMethod*>& method_handle_methods,
    UnorderedSet<DexMethod*>& using_this,
    UnorderedSet<DexMethod*>& not_using_this) {
  for (auto* const m : candidates) {
    if (!m_config.ignore_keep && !can_rename(m)) {
      TRACE(VIRT, 2, "failed to devirt method %s: keep", SHOW(m));
      continue;
    }
    if (m->rstate.no_optimizations()) {
      TRACE(VIRT, 2, "failed to devirt method %s: no_optimizations", SHOW(m));
      continue;
    }
    // A method handle that names or calls the method passes it the receiver.
    // Dropping the receiver changes the handle's method type, and so does
    // keeping it as the first parameter of an invoke-static handle when the
    // handle names the method through a subclass.
    if (method_handle_methods.count(m) != 0u) {
      TRACE(VIRT, 2, "failed to devirt method %s: method handle", SHOW(m));
      continue;
    }
    if (m->is_external() || is_abstract(m) || is_native(m)) {
      TRACE(VIRT,
            2,
            "failed to devirt method %s: external %d, abstract %d, native %d",
            SHOW(m),
            m->is_external(),
            is_abstract(m),
            is_native(m));
      continue;
    }
    if (uses_this(m)) {
      using_this.insert(m);
    } else {
      not_using_this.insert(m);
    }
  }
}

void MethodDevirtualizer::staticize_methods_not_using_this(
    const std::vector<DexClass*>& scope,
    const UnorderedSet<DexMethod*>& methods) {
  fix_call_sites(scope, methods, m_metrics, true /* drop_this */);
  make_methods_static(methods, false);
  TRACE(VIRT, 1, "Staticized %zu methods not using this", methods.size());
  m_metrics.num_methods_not_using_this += methods.size();
}

void MethodDevirtualizer::staticize_methods_using_this(
    const std::vector<DexClass*>& scope,
    const UnorderedSet<DexMethod*>& methods) {
  fix_call_sites(scope, methods, m_metrics, false /* drop_this */);
  make_methods_static(methods, true);
  TRACE(VIRT, 1, "Staticized %zu methods using this", methods.size());
  m_metrics.num_methods_using_this += methods.size();
}

DevirtualizerMetrics MethodDevirtualizer::devirtualize_methods(
    const Scope& scope, const std::vector<DexClass*>& target_classes) {
  reset_metrics();
  const auto method_handle_methods =
      method::gather_methods_named_by_method_handles(scope);
  auto vmethods = get_devirtualizable_vmethods(
      scope, target_classes, m_config.do_not_devirt_anno);
  UnorderedSet<DexMethod*> using_this, not_using_this;
  verify_and_split(vmethods, method_handle_methods, using_this, not_using_this);
  TRACE(VIRT,
        2,
        " VIRT to devirt vmethods using this %zu, not using this %zu",
        using_this.size(),
        not_using_this.size());

  if (m_config.vmethods_not_using_this) {
    staticize_methods_not_using_this(scope, not_using_this);
  }

  if (m_config.vmethods_using_this) {
    staticize_methods_using_this(scope, using_this);
  }

  auto dmethods = get_devirtualizable_dmethods(
      scope, target_classes, {m_config.do_not_devirt_anno});
  using_this.clear();
  not_using_this.clear();
  verify_and_split(dmethods, method_handle_methods, using_this, not_using_this);
  TRACE(VIRT,
        2,
        " VIRT to devirt dmethods using this %zu, not using this %zu",
        using_this.size(),
        not_using_this.size());

  if (m_config.dmethods_not_using_this) {
    staticize_methods_not_using_this(scope, not_using_this);
  }

  if (m_config.dmethods_using_this) {
    staticize_methods_using_this(scope, using_this);
  }

  return m_metrics;
}
