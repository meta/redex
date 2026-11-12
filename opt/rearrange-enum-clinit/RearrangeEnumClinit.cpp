/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "RearrangeEnumClinit.h"
#include "ControlFlow.h"

#include <algorithm>
#include <atomic>
#include <memory>
#include <optional>
#include <vector>

#include "AtomicStatCounter.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexPosition.h"
#include "DexUtil.h"
#include "IRCode.h"
#include "LiveRange.h"
#include "MethodUtil.h"
#include "PassManager.h"
#include "ScopedCFG.h"
#include "Show.h"
#include "SourceBlocks.h"
#include "Trace.h"
#include "TypeUtil.h"
#include "Walkers.h"

namespace rearrange_enum_clinit {
namespace {

// Rearranges one enum <clinit>. RearrangeEnumClinitPass::run creates a
// Rearranger only for a <clinit> that is a single block without a back edge,
// so `b` is the whole method body, instruction order is execution order, and
// each instruction runs at most once. The checks below rely on that.
struct Rearranger {
  DexMethod* m;
  cfg::ControlFlowGraph& cfg;
  cfg::Block* b; // The entry block, which is the whole method.

  live_range::MoveAwareChains mac;
  live_range::DefUseChains def_use;
  live_range::UseDefChains use_def;

  // Maps each instruction in `b` to its entry. Only MFLOW_OPCODE entries are
  // included, so a looked-up iterator always holds an instruction. Built once
  // at construction; inserted instructions are not added.
  UnorderedMap<const IRInstruction*, IRList::iterator> insn_map;

  IRInstruction* array_sput{nullptr};
  IRList::iterator array_new_array;
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
    for (auto& mie : InstructionIterable(b).reversed()) {
      if (mie.insn->opcode() == OPCODE_SPUT_OBJECT) {
        auto* f = mie.insn->get_field();
        if (f->get_class() == m->get_class() &&
            f->get_name()->str() == "$VALUES") {
          return mie.insn;
        }
      }
    }

    // Look for the `values()` function and analyze it.
    auto* c = type_class(m->get_class());
    if (c == nullptr) {
      return nullptr;
    }

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

    for (auto& mie : InstructionIterable(b).reversed()) {
      if (mie.insn->opcode() == OPCODE_SPUT_OBJECT) {
        if (field == mie.insn->get_field()) {
          return mie.insn;
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
            type::make_element_type_if_array(f->get_type()) == f->get_class()) {
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

  using Insertion = std::vector<cfg::ControlFlowGraph::InsertVariant>;

  static bool precedes_instruction(IRList::iterator it,
                                   const IRList::iterator& end) {
    while (it != end && it->type != MFLOW_POSITION &&
           it->type != MFLOW_OPCODE) {
      ++it;
    }
    return it != end && it->type == MFLOW_OPCODE;
  }

  // A position applies to the instructions after it, so a moved instruction
  // would take its destination's position and lose its own, including the
  // inlining parents of an instruction inlined into the initializer. A moved
  // allocation or store, with the constant it uses, is preceded by a copy of
  // its own position, and the destination's position is restored for any
  // instruction that follows. Instructions that had no position get the
  // synthetic entry position, which has no line either.
  void append_with_position(Insertion& insertion,
                            std::initializer_list<IRInstruction*> moved,
                            const DexPosition* own,
                            const DexPosition* destination,
                            bool followed_by_instruction) const {
    const bool keep =
        own != nullptr && (destination == nullptr || !(*own == *destination));
    if (keep) {
      insertion.emplace_back(std::make_unique<DexPosition>(*own));
    }
    for (auto* insn : moved) {
      insertion.emplace_back(insn);
    }
    if (keep && followed_by_instruction) {
      insertion.emplace_back(
          destination != nullptr
              ? std::make_unique<DexPosition>(*destination)
              : DexPosition::make_synthetic_entry_position(m));
    }
  }

  const DexPosition* position_of(const IRList::iterator& it) {
    return cfg.get_dbg_pos(b->to_cfg_instruction_iterator(it));
  }

  reg_t move_new_array_to_front() {
    auto new_array_it = b->begin();
    while (new_array_it->type != MFLOW_OPCODE) {
      ++new_array_it;
    }
    // Should not be necessary, but for safety.
    const auto size_reg = cfg.allocate_temp();
    const auto new_reg = cfg.allocate_temp();
    Insertion insertion;
    append_with_position(
        insertion,
        {(new IRInstruction(*array_size_definition))->set_dest(size_reg),
         (new IRInstruction(*array_new_array->insn))->set_src(0, size_reg),
         (new IRInstruction(IOPCODE_MOVE_RESULT_PSEUDO_OBJECT))
             ->set_dest(new_reg)},
        position_of(array_new_array), position_of(new_array_it),
        /* followed_by_instruction */ true);
    b->insert_before(b->to_cfg_instruction_iterator(new_array_it),
                     insertion.begin(), insertion.end());
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

  struct StorePlan {
    IRInstruction& store;
    IRInstruction& value;
    IRInstruction& index;
    std::optional<std::pair<IRList::iterator, reg_t>> insertion;
  };

  IRInstruction* array_size_definition{nullptr};
  std::vector<StorePlan> stores;
  const live_range::Uses* array_uses{nullptr};
  UnorderedSet<const IRInstruction*> post_publication_uses;
  FailureReason failure_reason{FailureReason::NoMovableElements};

  IRInstruction* find_singleton_def(IRInstruction* use_insn,
                                    src_index_t src_index) const {
    auto it = use_def.find({use_insn, src_index});
    return it == use_def.end() || it->second.size() != 1 ? nullptr
                                                         : *it->second.begin();
  }

  static bool is_constructor_receiver_use(const live_range::Use& use) {
    return use.src_index == 0 && use.insn->srcs_size() != 0 &&
           use.insn->opcode() == OPCODE_INVOKE_DIRECT &&
           method::is_constructor(use.insn->get_method()) &&
           method::is_init(use.insn->get_method());
  }

  // Whether the declared type of the value `producer` defines (a new
  // instance's class, an invoke's return type or a cast's type) makes it null
  // or an instance of the enum class, so storing it cannot throw
  // ArrayStoreException.
  bool produces_element(const IRInstruction& producer) const {
    const DexType* type = nullptr;
    if (producer.opcode() == OPCODE_NEW_INSTANCE ||
        producer.opcode() == OPCODE_CHECK_CAST) {
      type = producer.get_type();
    } else if (opcode::is_an_invoke(producer.opcode())) {
      type = producer.get_method()->get_proto()->get_rtype();
    }
    return type != nullptr && type::check_cast(type, m->get_class());
  }

  std::optional<std::pair<IRList::iterator, reg_t>> find_move_point(
      IRInstruction& value) const {
    auto position = insn_map.find(&value);
    if (position == insn_map.end()) {
      return std::nullopt;
    }
    if (value.opcode() == OPCODE_NEW_INSTANCE) {
      // A constructor returns void: the store cannot split off a move-result.
      auto uses = def_use.find(&value);
      if (uses == def_use.end()) {
        return std::nullopt;
      }
      std::optional<std::pair<IRList::iterator, reg_t>> result;
      for (const auto& use : UnorderedIterable(uses->second)) {
        if (!is_constructor_receiver_use(use)) {
          continue;
        }
        auto constructor = insn_map.find(use.insn);
        if (result || constructor == insn_map.end()) {
          return std::nullopt;
        }
        result = std::make_pair(constructor->second, use.insn->src(0));
      }
      return result;
    }
    auto it = position->second;
    if (value.has_move_result_any()) {
      do {
        ++it;
      } while (it != b->end() && it->type != MFLOW_OPCODE);
      if (it == b->end() || !opcode::is_move_result_any(it->insn->opcode())) {
        return std::nullopt;
      }
    }
    if (!it->insn->has_dest()) {
      return std::nullopt;
    }
    return std::make_pair(it, it->insn->dest());
  }

  bool validate_array_uses() {
    auto uses = def_use.find(array_new_array->insn);
    if (uses == def_use.end()) {
      failure_reason = FailureReason::NoArrayUses;
      return false;
    }
    array_uses = &uses->second;
    // Every store precedes the publication of the array in both the original
    // and the rearranged initializer, and `b` has no back edge, so an
    // instruction after the publication runs after it and observes the
    // completed array either way. A store after the publication is not such a
    // use; the store checks reject it.
    const auto publication = insn_map.at(array_sput);
    UnorderedSet<const IRInstruction*> after_publication;
    for (auto it = std::next(publication); it != b->end(); ++it) {
      // The block also holds positions and source blocks.
      if (it->type == MFLOW_OPCODE) {
        after_publication.insert(it->insn);
      }
    }
    method_stats.unsupported_uses = static_cast<size_t>(
        unordered_count_if(uses->second, [&](const live_range::Use& use) {
          if (use.insn == array_sput ||
              use.insn->opcode() == OPCODE_MOVE_OBJECT) {
            return use.src_index != 0;
          }
          if (use.insn->opcode() == OPCODE_APUT_OBJECT && use.src_index == 1) {
            return false;
          }
          if (after_publication.find(use.insn) != after_publication.end()) {
            post_publication_uses.insert(use.insn);
            return false;
          }
          return true;
        }));
    // Observers can see partial contents; changing their register is not
    // enough.
    if (method_stats.unsupported_uses != 0) {
      failure_reason = FailureReason::ArrayEscapes;
      return false;
    }
    return true;
  }

  bool prepare() {
    // Find a sput-object for `$VALUES`.
    array_sput = find_values_sput();
    if (array_sput == nullptr) {
      failure_reason = FailureReason::NoValuesStore;
      return false;
    }
    // Find the definition of the field object.
    auto* array = find_singleton_def(array_sput, 0);
    auto position = insn_map.find(array);
    if (array == nullptr || position == insn_map.end()) {
      failure_reason = FailureReason::AmbiguousArray;
      return false;
    }
    if (array->opcode() != OPCODE_NEW_ARRAY) {
      // Possibly Kotlin enum with `.$values()` not inlined, yet.
      failure_reason = FailureReason::ValuesNotNewArray;
      return false;
    }
    array_new_array = position->second;
    array_size_definition = find_singleton_def(array, 0);
    if (array_size_definition == nullptr ||
        array_size_definition->opcode() != OPCODE_CONST ||
        array_size_definition->get_literal() < 0 ||
        type::make_array_component_type(array->get_type()) != m->get_class() ||
        insn_map.find(array_size_definition) == insn_map.end()) {
      failure_reason = FailureReason::UnsupportedArraySizeOrType;
      return false;
    }
    if (!validate_array_uses()) {
      return false;
    }
    // Find all the users of the array. This should be aput-object things.
    UnorderedSet<IRInstruction*> selected_stores;
    for (const auto& use : UnorderedIterable(*array_uses)) {
      // Skip the sput.
      if (use.insn == array_sput || use.insn->opcode() == OPCODE_MOVE_OBJECT) {
        continue;
      }
      if (find_singleton_def(use.insn, use.src_index) != array) {
        failure_reason = FailureReason::AmbiguousArray;
        return false;
      }
      if (post_publication_uses.find(use.insn) != post_publication_uses.end() &&
          (use.insn->opcode() != OPCODE_APUT_OBJECT || use.src_index != 1)) {
        continue;
      }
      selected_stores.insert(use.insn);
    }
    UnorderedSet<int64_t> indices;
    UnorderedSet<IRInstruction*> seen;
    bool published = false;
    for (auto& mie : InstructionIterable(b)) {
      seen.insert(mie.insn);
      if (mie.insn == array_sput) {
        published = true;
      }
      if (selected_stores.find(mie.insn) == selected_stores.end()) {
        continue;
      }
      if (published) {
        failure_reason = FailureReason::InitializationAfterPublication;
        return false;
      }
      // See if we can hoist it. Check the input parameters.
      // 1. First parameter is object.
      auto* object_insn = find_singleton_def(mie.insn, 0);
      // 2. Third parameter is index, should be const.
      auto* index_insn = find_singleton_def(mie.insn, 2);
      if (object_insn == nullptr || index_insn == nullptr ||
          index_insn->opcode() != OPCODE_CONST ||
          index_insn->get_literal() < 0 ||
          index_insn->get_literal() >= array_size_definition->get_literal() ||
          !indices.insert(index_insn->get_literal()).second) {
        failure_reason = FailureReason::UnsupportedElementOrIndex;
        return false;
      }
      if (object_insn->opcode() != OPCODE_SGET_OBJECT &&
          !produces_element(*object_insn)) {
        failure_reason = FailureReason::UnsupportedElementProducer;
        return false;
      }
      std::optional<std::pair<IRList::iterator, reg_t>> point;
      // Check what the definition is.
      // Field read style, does not really benefit from moving.
      if (object_insn->opcode() != OPCODE_SGET_OBJECT) {
        // OK, may be beneficial.
        // We need to find the point where the object is fully
        // constructed. If the object_insn is a NEW_INSTANCE, search for the
        // following <init> call. Otherwise just use the result.
        point = find_move_point(*object_insn);
        if (!point) {
          failure_reason = FailureReason::AmbiguousConstructor;
          return false;
        }
        if (object_insn->opcode() == OPCODE_NEW_INSTANCE &&
            !type::check_cast(object_insn->get_type(),
                              point->first->insn->get_method()->get_class())) {
          failure_reason = FailureReason::UnsupportedConstructor;
          return false;
        }
        if (seen.find(point->first->insn) == seen.end()) {
          failure_reason = FailureReason::UninitializedElement;
          return false;
        }
      }
      stores.push_back(StorePlan{*mie.insn, *object_insn, *index_insn, point});
    }
    if (indices.size() !=
        static_cast<uint64_t>(array_size_definition->get_literal())) {
      failure_reason = FailureReason::IncompleteArray;
      return false;
    }
    return true;
  }

  bool run() {
    if (!prepare()) {
      return false;
    }
    std::optional<reg_t> alloc_reg;
    std::optional<reg_t> extra_reg;
    UnorderedMap<IRInstruction*, IRList::iterator> last_insertions;
    for (const auto& plan : stores) {
      if (!plan.insertion) {
        continue;
      }
      if (!alloc_reg) {
        method_stats.retained_field_stores = static_cast<size_t>(
            std::count_if(stores.begin(), stores.end(),
                          [](const auto& item) { return !item.insertion; }));
        const auto& uses = *array_uses;
        method_stats.aliases =
            static_cast<size_t>(unordered_count_if(uses, [](const auto& use) {
              return use.insn->opcode() == OPCODE_MOVE_OBJECT;
            }));
        method_stats.post_publication_uses = post_publication_uses.size();
        // Move array to front, use a new register.
        alloc_reg = move_new_array_to_front();
        for (const auto& use : UnorderedIterable(uses)) {
          use.insn->set_src(use.src_index, *alloc_reg);
        }
        extra_reg = cfg.allocate_temp();
      }
      auto [insert_after_it, obj_reg] = *plan.insertion;
      auto* anchor = insert_after_it->insn;
      auto previous = last_insertions.find(anchor);
      if (previous != last_insertions.end()) {
        insert_after_it = previous->second;
      }
      auto* moved_store = (new IRInstruction(plan.store))
                              ->set_src(0, obj_reg)
                              ->set_src(1, *alloc_reg)
                              ->set_src(2, *extra_reg);
      Insertion insertion;
      append_with_position(
          insertion,
          {(new IRInstruction(plan.index))->set_dest(*extra_reg), moved_store},
          position_of(insn_map.at(&plan.store)), position_of(insert_after_it),
          precedes_instruction(std::next(insert_after_it), b->end()));
      b->insert_after(b->to_cfg_instruction_iterator(insert_after_it),
                      insertion.begin(), insertion.end());
      auto inserted_store =
          std::next(b->to_cfg_instruction_iterator(insert_after_it), 2)
              .unwrap();
      // INVOKE_DIRECT is throwable -- insert a source block after it
      // to cover the segment up to APUT_OBJECT.
      auto* sb = source_blocks::find_between(
          IRList::reverse_iterator(insert_after_it), b->rend());
      if (sb != nullptr) {
        source_blocks::impl::BlockAccessor::insert_source_block_after(
            b, insert_after_it, source_blocks::clone_as_synthetic(sb));
      }
      last_insertions[anchor] = inserted_store;
      // Remove the old aput.
      b->remove_insn(insn_map.at(&plan.store));
    }
    if (!alloc_reg) {
      failure_reason = FailureReason::NoMovableElements;
      return false;
    }
    // Finally remove the old new-array. Do it late so there's no undefined
    // behavior with deleted things.
    b->remove_insn(array_new_array);
    return true;
  }
};

} // namespace

std::string_view describe(FailureReason reason) {
  switch (reason) {
  case FailureReason::None:
    return "none";
  case FailureReason::ClinitWithoutCode:
    return "clinit_without_code";
  case FailureReason::NotOneBlock:
    return "not_one_block";
  case FailureReason::CyclicInitializer:
    return "cyclic_initializer";
  case FailureReason::NoMovableElements:
    return "no_movable_elements";
  case FailureReason::NoValuesStore:
    return "no_values_store";
  case FailureReason::AmbiguousArray:
    return "ambiguous_array";
  case FailureReason::ValuesNotNewArray:
    return "values_not_new_array";
  case FailureReason::UnsupportedArraySizeOrType:
    return "unsupported_array_size_or_type";
  case FailureReason::NoArrayUses:
    return "no_array_uses";
  case FailureReason::ArrayEscapes:
    return "array_escapes";
  case FailureReason::UnsupportedElementOrIndex:
    return "unsupported_element_or_index";
  case FailureReason::UnsupportedElementProducer:
    return "unsupported_element_producer";
  case FailureReason::UninitializedElement:
    return "uninitialized_element";
  case FailureReason::AmbiguousConstructor:
    return "ambiguous_constructor";
  case FailureReason::UnsupportedConstructor:
    return "unsupported_constructor";
  case FailureReason::IncompleteArray:
    return "incomplete_array";
  case FailureReason::InitializationAfterPublication:
    return "initialization_after_publication";
  }
  not_reached();
}

MethodResult RearrangeEnumClinitPass::run(DexMethod* m,
                                          IRCode* code,
                                          MethodStats* method_stats,
                                          FailureReason* failure_reason) {
  if (method_stats != nullptr) {
    *method_stats = {};
  }
  if (failure_reason != nullptr) {
    *failure_reason = FailureReason::None;
  }
  if (code == nullptr) {
    if (method_stats != nullptr) {
      method_stats->failed_preflight = 1;
    }
    if (failure_reason != nullptr) {
      *failure_reason = FailureReason::ClinitWithoutCode;
    }
    return MethodResult::kFailed;
  }
  auto cfg = cfg::ScopedCFG(code);
  if (cfg->num_blocks() != 1) {
    if (failure_reason != nullptr) {
      *failure_reason = FailureReason::NotOneBlock;
    }
    TRACE(ENUM, 2, "RearrangeEnumClinit: %s: %.*s", SHOW(m),
          static_cast<int>(describe(FailureReason::NotOneBlock).size()),
          describe(FailureReason::NotOneBlock).data());
    return MethodResult::kNotOneBlock;
  }
  auto* block = cfg->entry_block();
  if (std::any_of(
          block->succs().begin(), block->succs().end(),
          [block](const auto* edge) { return edge->target() == block; })) {
    if (method_stats != nullptr) {
      method_stats->failed_preflight = 1;
    }
    if (failure_reason != nullptr) {
      *failure_reason = FailureReason::CyclicInitializer;
    }
    TRACE(ENUM, 2, "RearrangeEnumClinit: %s: %.*s", SHOW(m),
          static_cast<int>(describe(FailureReason::CyclicInitializer).size()),
          describe(FailureReason::CyclicInitializer).data());
    return MethodResult::kFailed;
  }
  Rearranger rearranger(m, *cfg);
  auto res = rearranger.run();
  rearranger.method_stats.failed_preflight = res ? 0 : 1;
  if (method_stats != nullptr) {
    *method_stats = rearranger.method_stats;
  }
  if (!res) {
    if (failure_reason != nullptr) {
      *failure_reason = rearranger.failure_reason;
    }
    TRACE(ENUM, 2, "RearrangeEnumClinit: %s: %.*s", SHOW(m),
          static_cast<int>(describe(rearranger.failure_reason).size()),
          describe(rearranger.failure_reason).data());
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
  AtomicStatCounter<size_t> cnt_failed_preflight{0};
  AtomicStatCounter<size_t> cnt_unsupported_array_uses{0};
  AtomicStatCounter<size_t> cnt_clinit_without_code{0};
  AtomicStatCounter<size_t> cnt_retained_field_stores{0};
  AtomicStatCounter<size_t> cnt_arrays_with_retained_field_stores{0};
  AtomicStatCounter<size_t> cnt_array_aliases{0};
  AtomicStatCounter<size_t> cnt_arrays_with_aliases{0};
  AtomicStatCounter<size_t> cnt_post_publication_uses{0};
  AtomicStatCounter<size_t> cnt_arrays_with_post_publication_uses{0};
  AtomicStatCounter<size_t> cnt_values_not_new_array{0};
  AtomicStatCounter<size_t> cnt_no_values_store{0};
  AtomicStatCounter<size_t> cnt_no_movable_elements{0};
  AtomicStatCounter<size_t> cnt_unsupported_shape{0};
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

    if (m->get_code() == nullptr) {
      ++cnt_clinit_without_code;
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
    FailureReason failure_reason{FailureReason::None};
    auto res = run(m, m->get_code(), &method_stats, &failure_reason);
    cnt_failed_preflight += method_stats.failed_preflight;
    cnt_unsupported_array_uses += method_stats.unsupported_uses;
    cnt_retained_field_stores += method_stats.retained_field_stores;
    cnt_array_aliases += method_stats.aliases;
    if (method_stats.retained_field_stores != 0) {
      ++cnt_arrays_with_retained_field_stores;
    }
    if (method_stats.aliases != 0) {
      ++cnt_arrays_with_aliases;
    }
    cnt_post_publication_uses += method_stats.post_publication_uses;
    if (method_stats.post_publication_uses != 0) {
      ++cnt_arrays_with_post_publication_uses;
    }
    cnt_values_without_code += method_stats.values_without_code;
    cnt_values_without_return += method_stats.values_without_return;

    if (res == MethodResult::kFailed) {
      switch (failure_reason) {
      case FailureReason::ValuesNotNewArray:
        ++cnt_values_not_new_array;
        break;
      case FailureReason::NoValuesStore:
        ++cnt_no_values_store;
        break;
      case FailureReason::NoMovableElements:
        ++cnt_no_movable_elements;
        break;
      case FailureReason::ClinitWithoutCode:
      case FailureReason::CyclicInitializer:
      case FailureReason::AmbiguousArray:
      case FailureReason::UnsupportedArraySizeOrType:
      case FailureReason::NoArrayUses:
      case FailureReason::ArrayEscapes:
      case FailureReason::UnsupportedElementOrIndex:
      case FailureReason::UnsupportedElementProducer:
      case FailureReason::UninitializedElement:
      case FailureReason::AmbiguousConstructor:
      case FailureReason::UnsupportedConstructor:
      case FailureReason::IncompleteArray:
      case FailureReason::InitializationAfterPublication:
        ++cnt_unsupported_shape;
        break;
      // run() records a reason with every kFailed: the rearranger starts from
      // NoMovableElements and each rejection sets its own, and NotOneBlock
      // comes only with kNotOneBlock.
      case FailureReason::None:
      case FailureReason::NotOneBlock:
        not_reached();
      }
    }

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

  mgr.set_metric("failed_preflight", cnt_failed_preflight.load());
  mgr.set_metric("unsupported_array_uses", cnt_unsupported_array_uses.load());
  mgr.set_metric("clinit_without_code", cnt_clinit_without_code.load());
  mgr.set_metric("retained_field_stores", cnt_retained_field_stores.load());
  mgr.set_metric("changed_with_retained_field_stores",
                 cnt_arrays_with_retained_field_stores.load());
  mgr.set_metric("retargeted_array_aliases", cnt_array_aliases.load());
  mgr.set_metric("changed_with_array_aliases", cnt_arrays_with_aliases.load());
  mgr.set_metric("retargeted_post_publication_uses",
                 cnt_post_publication_uses.load());
  mgr.set_metric("changed_with_post_publication_uses",
                 cnt_arrays_with_post_publication_uses.load());
  mgr.set_metric("values_without_code", cnt_values_without_code.load());
  mgr.set_metric("values_without_return", cnt_values_without_return.load());
  mgr.set_metric("failed.values_not_new_array",
                 cnt_values_not_new_array.load());
  mgr.set_metric("failed.no_values_store", cnt_no_values_store.load());
  mgr.set_metric("failed.no_movable_elements", cnt_no_movable_elements.load());
  mgr.set_metric("failed.unsupported_shape", cnt_unsupported_shape.load());
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
