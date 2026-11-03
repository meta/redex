/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "RearrangeEnumClinit.h"
#include "ControlFlow.h"

#include <atomic>
#include <optional>

#include "AtomicStatCounter.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexUtil.h"
#include "IRCode.h"
#include "LiveRange.h"
#include "MethodUtil.h"
#include "PassManager.h"
#include "ScopedCFG.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "TypeUtil.h"
#include "Walkers.h"

namespace rearrange_enum_clinit {
namespace {

struct Rearranger {
  DexMethod* m;
  cfg::ControlFlowGraph& cfg;
  cfg::Block* b;

  live_range::MoveAwareChains mac;
  live_range::DefUseChains def_use;
  live_range::UseDefChains use_def;

  UnorderedMap<const IRInstruction*, IRList::iterator> insn_map;

  IRInstruction* array_sput{nullptr};
  IRList::iterator array_new_array;
  reg_t alloc_reg;
  MethodStats method_stats;

  Rearranger(DexMethod* m, cfg::ControlFlowGraph& cfg)
      : m(m),
        cfg(cfg),
        b(cfg.entry_block()),
        mac(cfg),
        def_use(mac.get_def_use_chains()),
        use_def(mac.get_use_def_chains()),
        insn_map([](auto* block)
                     -> UnorderedMap<const IRInstruction*, IRList::iterator> {
          UnorderedMap<const IRInstruction*, IRList::iterator> map;
          for (auto it = block->begin(); it != block->end(); ++it) {
            if (it->type == MFLOW_OPCODE) {
              map.emplace(it->insn, it);
            }
          }
          return map;
        }(cfg.entry_block())) {}

  IRInstruction* find_values_sput() {
    // Optimistically look for the `$VALUES` field and accept it.
    for (auto it = b->rbegin(); it != b->rend(); ++it) {
      if (it->type == MFLOW_OPCODE &&
          it->insn->opcode() == OPCODE_SPUT_OBJECT) {
        auto* f = it->insn->get_field();
        if (f->get_class() == m->get_class() &&
            f->get_name()->str() == "$VALUES") {
          return it->insn;
        }
      }
    }

    // Look for the `values()` function and analyze it.
    auto* c = type_class(m->get_class());
    redex_assert(c != nullptr);

    auto* values_method = [&c]() -> DexMethod* {
      for (auto* dm : c->get_dmethods()) {
        if (dm->get_name()->str() == "values") {
          auto* p = dm->get_proto();
          if (p->get_args()->empty() && type::is_array(p->get_rtype())) {
            return dm;
          }
        }
      }
      return nullptr;
    }();

    if (values_method == nullptr) {
      return nullptr;
    }
    if (values_method->get_code() == nullptr) {
      ++method_stats.values_without_code;
      return nullptr;
    }

    auto* field = analyze_values_method(values_method, method_stats);
    if (field == nullptr) {
      return nullptr;
    }

    for (auto it = b->rbegin(); it != b->rend(); ++it) {
      if (it->type == MFLOW_OPCODE &&
          it->insn->opcode() == OPCODE_SPUT_OBJECT) {
        if (field == it->insn->get_field()) {
          return it->insn;
        }
      }
    }

    return nullptr;
  }

  static DexFieldRef* analyze_values_method(DexMethod* values_method,
                                            MethodStats& method_stats) {
    cfg::ScopedCFG cfg(values_method->get_code());

    std::optional<IRInstruction*> ret_opt{};
    for (auto& mie : cfg::InstructionIterable(*cfg)) {
      if (mie.insn->opcode() == OPCODE_RETURN_OBJECT) {
        if (ret_opt) {
          return nullptr; // Single return only.
        }
        ret_opt = mie.insn;
      }
    }
    if (!ret_opt) {
      ++method_stats.values_without_return;
      return nullptr;
    }

    using namespace live_range;
    MoveAwareChains mac(*cfg);
    auto use_def = mac.get_use_def_chains();

    auto get_singleton = [&use_def](IRInstruction* insn,
                                    src_index_t idx) -> IRInstruction* {
      auto it = use_def.find(Use{insn, idx});
      if (it == use_def.end()) {
        return nullptr;
      }
      if (it->second.size() != 1) {
        return nullptr;
      }
      return *it->second.begin();
    };

    for (IRInstruction* insn = *ret_opt; insn != nullptr;) {
      // Written this way to ensure safe coding, always make progress.
      src_index_t use_idx;
      switch (insn->opcode()) {
      case OPCODE_RETURN_OBJECT:
      case OPCODE_CHECK_CAST:
        use_idx = 0;
        break;

      case OPCODE_SGET_OBJECT: {
        auto* f = insn->get_field();
        if (f->get_class() == values_method->get_class() &&
            type::get_element_type_if_array(f->get_type()) == f->get_class()) {
          return f;
        }
        return nullptr;
      }

      case OPCODE_INVOKE_VIRTUAL: {
        auto* mref = insn->get_method();
        // Only support `clone()`.
        if (mref->get_name()->str() != "clone" ||
            mref->get_proto()->get_rtype() != type::java_lang_Object()) {
          return nullptr;
        }
        use_idx = 0;
      } break;

      // Unsupported opcodes.
      default:
        return nullptr;
      }

      insn = get_singleton(insn, use_idx);
    }

    return nullptr;
  }

  reg_t move_new_array_to_front() {
    redex_assert(array_new_array != CONSTP(b)->begin());

    auto size_def_it = use_def.find({array_new_array->insn, 0});
    redex_assert(size_def_it != std::as_const(use_def).end());
    redex_assert(size_def_it->second.size() == 1);
    auto orig_new_array_size_cfg_it =
        cfg.find_insn(*size_def_it->second.begin(), b);
    redex_assert(!orig_new_array_size_cfg_it.is_end());
    redex_assert(orig_new_array_size_cfg_it.block() == b);
    auto orig_new_array_size_it = orig_new_array_size_cfg_it.unwrap();
    always_assert(orig_new_array_size_it->insn->opcode() == OPCODE_CONST);

    auto new_array_it = b->begin();
    while (new_array_it->type != MFLOW_OPCODE) {
      ++new_array_it;
    }

    // Should not be necessary, but for safety.
    reg_t size_reg = cfg.allocate_temp();

    reg_t new_reg = cfg.allocate_temp();

    b->insert_before(
        b->to_cfg_instruction_iterator(new_array_it),
        {
            (new IRInstruction(*orig_new_array_size_it->insn))
                ->set_dest(size_reg),
            (new IRInstruction(*array_new_array->insn))->set_src(0, size_reg),
            (new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT))
                ->set_dest(new_reg),
        });

    // NEW_ARRAY is throwable — insert a source block after its
    // MOVE_RESULT_PSEUDO to cover the new throw-delineated segment.
    auto* first_sb = source_blocks::get_first_source_block(b);
    if (first_sb != nullptr) {
      auto mrp_it = new_array_it;
      --mrp_it;
      source_blocks::impl::BlockAccessor::insert_source_block_after(
          b, mrp_it, source_blocks::clone_as_synthetic(first_sb));
    }

    // Leave the size around in case it was referenced for something else.
    // Will be cleaned up by shrinker.

    return new_reg;
  }

  IRInstruction* find_singleton_def(IRInstruction* use_insn,
                                    src_index_t src_index) {
    auto it = use_def.find(live_range::Use{use_insn, src_index});
    redex_assert(it != use_def.cend());
    redex_assert(it->second.size() == 1);
    return *it->second.begin();
  }

  std::pair<IRList::iterator, reg_t> find_move_point_new_instance(
      IRInstruction* object_insn) {
    auto it = def_use.find(object_insn);
    redex_assert(it != def_use.cend());
    std::optional<reg_t> which_reg{};
    std::optional<IRList::iterator> which_it{};
    for (const auto& obj_use : UnorderedIterable(it->second)) {
      if (obj_use.src_index == 0 &&
          opcode::is_an_invoke(obj_use.insn->opcode()) &&
          method::is_constructor(obj_use.insn->get_method())) {
        redex_assert(!which_reg);
        which_reg = obj_use.insn->src(0);
        which_it = insn_map.at(obj_use.insn);
      }
    }
    redex_assert(which_reg);
    return std::make_pair(*which_it, *which_reg);
  }

  std::pair<IRList::iterator, reg_t> find_move_point(
      IRInstruction* object_insn) {
    if (object_insn->opcode() != OPCODE_NEW_INSTANCE) {
      auto object_it = insn_map.at(object_insn);

      if (object_insn->has_move_result_any()) {
        ++object_it;
        while (object_it->type != MFLOW_OPCODE) {
          ++object_it;
        }
        redex_assert(opcode::is_move_result_any(object_it->insn->opcode()));
      }
      return std::make_pair(object_it, object_it->insn->dest());
    }
    return find_move_point_new_instance(object_insn);
  }

  bool validate_array_uses() {
    auto uses = def_use.find(array_new_array->insn);
    if (uses == def_use.end()) {
      return false;
    }
    method_stats.unsupported_uses = static_cast<size_t>(
        unordered_count_if(uses->second, [&](const live_range::Use& use) {
          if (use.insn == array_sput ||
              use.insn->opcode() == OPCODE_MOVE_OBJECT) {
            return use.src_index != 0;
          }
          return use.insn->opcode() != OPCODE_APUT_OBJECT || use.src_index != 1;
        }));
    // Observers can see partial contents; changing their register is not
    // enough.
    return method_stats.unsupported_uses == 0;
  }

  bool run() {
    // Find a sput-object for `$VALUES`.
    array_sput = find_values_sput();
    if (array_sput == nullptr) {
      return false;
    }
    redex_assert(array_sput->opcode() == OPCODE_SPUT_OBJECT);

    // Find the definition of the field object.
    array_new_array = insn_map.at(find_singleton_def(array_sput, 0));

    if (array_new_array->insn->opcode() != OPCODE_NEW_ARRAY) {
      // Possibly Kotlin enum with `.$values()` not inlined, yet.
      return false;
    }

    if (!validate_array_uses()) {
      return false;
    }
    const auto& uses = def_use.at(array_new_array->insn);

    bool moved_new_array{false};
    auto move_array = [&]() {
      if (moved_new_array) {
        return;
      }
      alloc_reg = move_new_array_to_front();
      for (const auto& use : UnorderedIterable(uses)) {
        use.insn->set_src(use.src_index, alloc_reg);
      }
      moved_new_array = true;
    };
    size_t retained_field_stores = 0;

    // Move array to front, use a new register.

    // Find all the users of the array. This should be aput-object things.
    {
      std::optional<reg_t> extra_reg{};
      for (const auto& use : UnorderedIterable(uses)) {
        // Skip the sput.
        if (use.insn == array_sput ||
            use.insn->opcode() == OPCODE_MOVE_OBJECT) {
          continue;
        }
        assert_log(use.insn->opcode() == OPCODE_APUT_OBJECT,
                   "Unexpected opcode %x",
                   use.insn->opcode());

        // Check what the definition is.
        IRInstruction* object_insn = find_singleton_def(use.insn, 0);
        if (object_insn->opcode() == OPCODE_SGET_OBJECT) {
          // Field read style, does not really benefit from moving.
          ++retained_field_stores;
          continue;
        }

        // OK, may be beneficial.
        move_array();

        if (!extra_reg) {
          extra_reg = cfg.allocate_temp();
        }

        // See if we can hoist it. Check the input parameters.
        // 1. First parameter is object. Already checked above.

        // 2. Third parameter is index, should be const.
        IRInstruction* index_insn = find_singleton_def(use.insn, 2);
        redex_assert(index_insn->opcode() == OPCODE_CONST);

        // We need to find the point where the object is fully
        // constructed. If the object_insn is a NEW_INSTANCE, search for the
        // following <init> call. Otherwise just use the result.
        auto [insert_after_it, obj_reg] = find_move_point(object_insn);

        b->insert_after(
            b->to_cfg_instruction_iterator(insert_after_it),
            {
                (new IRInstruction(*index_insn))->set_dest(*extra_reg),
                (new IRInstruction(*use.insn))
                    ->set_src(0, obj_reg)
                    ->set_src(1, alloc_reg)
                    ->set_src(2, *extra_reg),
            });

        // INVOKE_DIRECT is throwable — insert a source block after it
        // to cover the segment up to APUT_OBJECT.
        {
          auto* sb = source_blocks::find_between(
              IRList::reverse_iterator(insert_after_it), b->rend());
          if (sb != nullptr) {
            source_blocks::impl::BlockAccessor::insert_source_block_after(
                b, insert_after_it, source_blocks::clone_as_synthetic(sb));
          }
        }

        // Remove the old aput.
        b->remove_insn(cfg.find_insn(use.insn, b).unwrap());
      }
    }

    if (!moved_new_array) {
      return false;
    }
    method_stats.retained_field_stores = retained_field_stores;
    method_stats.aliases =
        static_cast<size_t>(unordered_count_if(uses, [](const auto& use) {
          return use.insn->opcode() == OPCODE_MOVE_OBJECT;
        }));

    // Finally remove the old new-array. Do it late so there's no undefined
    // behavior with deleted things.
    b->remove_insn(array_new_array);

    return true;
  }
};

} // namespace

MethodResult RearrangeEnumClinitPass::run(DexMethod* m,
                                          IRCode* code,
                                          MethodStats* method_stats) {
  if (method_stats != nullptr) {
    *method_stats = {};
  }
  auto cfg = cfg::ScopedCFG(code);
  if (cfg->num_blocks() != 1) {
    return MethodResult::kNotOneBlock;
  }

  Rearranger rearranger(m, *cfg);
  auto res = rearranger.run();
  if (method_stats != nullptr) {
    *method_stats = rearranger.method_stats;
  }

  return res ? MethodResult::kChanged : MethodResult::kFailed;
}

void RearrangeEnumClinitPass::run_pass(DexStoresVector& stores,
                                       ConfigFiles&,
                                       PassManager& mgr) {
  std::atomic<size_t> cnt_all{0};
  std::atomic<size_t> cnt_not_one_block{0};
  std::atomic<size_t> cnt_no_clinit{0};
  std::atomic<size_t> cnt_below_threshold{0};
  std::atomic<size_t> cnt_failed{0};
  std::atomic<size_t> cnt_changed{0};
  AtomicStatCounter<size_t> cnt_unsupported_array_uses{0};
  AtomicStatCounter<size_t> cnt_retained_field_stores{0};
  AtomicStatCounter<size_t> cnt_arrays_with_retained_field_stores{0};
  AtomicStatCounter<size_t> cnt_array_aliases{0};
  AtomicStatCounter<size_t> cnt_arrays_with_aliases{0};
  AtomicStatCounter<size_t> cnt_values_without_code{0};
  AtomicStatCounter<size_t> cnt_values_without_return{0};
  std::atomic<size_t> cnt_no_optimizations{0};

  walk::parallel::classes(build_class_scope(stores), [&](DexClass* c) {
    if (c->is_external() || !is_enum(c)) {
      return;
    }

    cnt_all.fetch_add(1, std::memory_order_relaxed);

    auto* m = c->get_clinit();
    if (m == nullptr) {
      // This case can happen for anonymous classes used when an enum case is
      // specialized.
      cnt_no_clinit.fetch_add(1, std::memory_order_relaxed);
      return;
    }

    if (m->get_code()->count_opcodes() < m_threshold) {
      cnt_below_threshold.fetch_add(1, std::memory_order_relaxed);
      return;
    }

    if (m->rstate.no_optimizations()) {
      cnt_no_optimizations.fetch_add(1, std::memory_order_relaxed);
      return;
    }

    MethodStats method_stats;
    auto res = run(m, m->get_code(), &method_stats);
    cnt_unsupported_array_uses += method_stats.unsupported_uses;
    cnt_retained_field_stores += method_stats.retained_field_stores;
    cnt_array_aliases += method_stats.aliases;
    if (method_stats.retained_field_stores != 0) {
      ++cnt_arrays_with_retained_field_stores;
    }
    if (method_stats.aliases != 0) {
      ++cnt_arrays_with_aliases;
    }
    cnt_values_without_code += method_stats.values_without_code;
    cnt_values_without_return += method_stats.values_without_return;

    switch (res) {
    case MethodResult::kUnknown:
      not_reached();

    case MethodResult::kNotOneBlock:
      cnt_not_one_block.fetch_add(1, std::memory_order_relaxed);
      break;

    case MethodResult::kFailed:
      cnt_failed.fetch_add(1, std::memory_order_relaxed);
      break;

    case MethodResult::kChanged:
      cnt_changed.fetch_add(1, std::memory_order_relaxed);
      break;
    }
  });

  mgr.set_metric("unsupported_array_uses", cnt_unsupported_array_uses.load());
  mgr.set_metric("retained_field_stores", cnt_retained_field_stores.load());
  mgr.set_metric("changed_with_retained_field_stores",
                 cnt_arrays_with_retained_field_stores.load());
  mgr.set_metric("retargeted_array_aliases", cnt_array_aliases.load());
  mgr.set_metric("changed_with_array_aliases", cnt_arrays_with_aliases.load());
  mgr.set_metric("values_without_code", cnt_values_without_code.load());
  mgr.set_metric("values_without_return", cnt_values_without_return.load());
  mgr.set_metric("changed", cnt_changed.load());
  mgr.set_metric("failed", cnt_failed.load());
  mgr.set_metric("no_clinit", cnt_no_clinit.load());
  mgr.set_metric("below_threshold", cnt_below_threshold.load());
  mgr.set_metric("no_optimizations", cnt_no_optimizations.load());
  mgr.set_metric("not_one_block", cnt_not_one_block.load());
  mgr.set_metric("all_enum", cnt_all.load());
}

static RearrangeEnumClinitPass s_pass;

} // namespace rearrange_enum_clinit
