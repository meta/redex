/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "InlineEnumValues.h"

#include <atomic>

#include "ControlFlow.h"
#include "Debug.h"
#include "DexClass.h"
#include "IRInstruction.h"
#include "Inliner.h"
#include "Resolver.h"
#include "ScopedCFG.h"
#include "Show.h"
#include "Trace.h"
#include "TypeUtil.h"
#include "Walkers.h"

namespace inline_enum_values {

namespace {

constexpr const char* DOLLAR_VALUES = "$values";

// Find the synthetic `private static E[] $values()` method javac 15+ emits for
// an enum, or nullptr if the class does not have one.
DexMethod* find_dollar_values(DexClass* cls) {
  for (auto* dm : cls->get_dmethods()) {
    if (dm->get_name()->str() != DOLLAR_VALUES) {
      continue;
    }
    // `$values` is private, static and synthetic. Requiring all three keeps the
    // match to compiler-generated methods and guarantees (via `private`) that
    // every caller lives in this class.
    if (!is_static(dm) || !is_private(dm) || !is_synthetic(dm)) {
      continue;
    }
    auto* proto = dm->get_proto();
    if (!proto->get_args()->empty()) {
      continue;
    }
    auto* rtype = proto->get_rtype();
    if (!type::is_array(rtype) ||
        type::make_array_component_type(rtype) != cls->get_type()) {
      continue;
    }
    return dm;
  }
  return nullptr;
}

// Returns true if `method`'s code contains an invoke-static resolving to
// `callee`.
bool calls(DexMethod* method, DexMethod* callee) {
  auto* code = method->get_code();
  if (code == nullptr) {
    return false;
  }
  cfg::ScopedCFG cfg(code);
  for (auto& mie : cfg::InstructionIterable(*cfg)) {
    auto* insn = mie.insn;
    if (insn->opcode() == OPCODE_INVOKE_STATIC &&
        resolve_method(insn->get_method(), MethodSearch::Static) == callee) {
      return true;
    }
  }
  return false;
}

} // namespace

Result run(DexClass* cls) {
  auto* clinit = cls->get_clinit();
  if (clinit == nullptr || clinit->get_code() == nullptr ||
      clinit->rstate.no_optimizations()) {
    return Result::kIneligible;
  }

  auto* dollar_values = find_dollar_values(cls);
  if (dollar_values == nullptr || dollar_values->get_code() == nullptr ||
      dollar_values->rstate.no_optimizations()) {
    return Result::kIneligible;
  }

  // `$values` is private, so only methods of this class can reference it. If
  // anything other than `<clinit>` calls it, inlining + deleting is unsafe.
  for (auto* dm : cls->get_dmethods()) {
    if (dm != clinit && dm != dollar_values && calls(dm, dollar_values)) {
      return Result::kIneligible;
    }
  }
  for (auto* vm : cls->get_vmethods()) {
    if (calls(vm, dollar_values)) {
      return Result::kIneligible;
    }
  }

  // Inline the single `$values()` call in `<clinit>` and drop the method.
  bool inlined = false;
  {
    cfg::ScopedCFG clinit_cfg(clinit->get_code());
    cfg::ScopedCFG dollar_values_cfg(dollar_values->get_code());

    IRInstruction* callsite = nullptr;
    for (auto& mie : cfg::InstructionIterable(*clinit_cfg)) {
      auto* insn = mie.insn;
      if (insn->opcode() == OPCODE_INVOKE_STATIC &&
          resolve_method(insn->get_method(), MethodSearch::Static) ==
              dollar_values) {
        // The above caller checks guarantee `<clinit>` is the sole caller of
        // `$values()`; javac emits exactly one call. Fail loudly rather than
        // silently inlining only the first if that ever stops holding.
        always_assert_log(callsite == nullptr,
                          "Multiple $values() callsites in %s.<clinit>",
                          SHOW(cls->get_type()));
        callsite = insn;
      }
    }
    if (callsite == nullptr) {
      return Result::kIneligible;
    }

    inlined = inliner::inline_with_cfg(clinit, dollar_values, callsite,
                                       /* needs_receiver_cast */ nullptr,
                                       /* needs_init_class */ nullptr,
                                       clinit_cfg->get_registers_size());
  }

  if (!inlined) {
    return Result::kInlineFailed;
  }

  // remove_method only detaches from the class's method list; the DexMethod
  // stays interned in RedexContext and resolvable by signature. delete_method
  // erases the ref and drops its IR, matching the inliner's post-inline
  // cleanup.
  cls->remove_method(dollar_values);
  DexMethod::delete_method(dollar_values);
  return Result::kChanged;
}

Stats run(const std::vector<DexClass*>& scope) {
  std::atomic<size_t> enums{0};
  std::atomic<size_t> changed{0};
  std::atomic<size_t> ineligible{0};
  std::atomic<size_t> inline_failed{0};

  // Safe to run per-class in parallel: each task owns a distinct enum class, so
  // the CFG edits, `remove_method` (per-class method list) and `delete_method`
  // (distinct method, plus the concurrent RedexContext maps) never collide, and
  // `inline_with_cfg` only touches the caller/callee CFGs and thread-safe
  // globals.
  walk::parallel::classes(scope, [&](DexClass* cls) {
    if (cls->is_external() || !is_enum(cls)) {
      return;
    }
    enums.fetch_add(1, std::memory_order_relaxed);

    switch (run(cls)) {
    case Result::kIneligible:
      ineligible.fetch_add(1, std::memory_order_relaxed);
      break;
    case Result::kInlineFailed:
      inline_failed.fetch_add(1, std::memory_order_relaxed);
      break;
    case Result::kChanged:
      changed.fetch_add(1, std::memory_order_relaxed);
      break;
    }
  });

  Stats stats;
  stats.enums = enums.load();
  stats.changed = changed.load();
  stats.ineligible = ineligible.load();
  stats.inline_failed = inline_failed.load();

  TRACE(ENUM, 1, "InlineEnumValues: inlined %zu of %zu enums", stats.changed,
        stats.enums);
  return stats;
}

} // namespace inline_enum_values
