/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <bit>
#include <boost/intrusive/list.hpp>
#include <boost/range/sub_range.hpp>
#include <functional>
#include <iosfwd>
#include <iterator>
#include <limits>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <string>
#include <type_traits>
#include <vector>

#include "Debug.h"
#include "DeterministicContainers.h"
#include "StlUtil.h"

class DexCallSite;
class DexDebugInstruction;
class DexFieldRef;
class DexInstruction;
class DexMethodHandle;
class DexMethodRef;
struct DexPosition;
class DexString;
class DexType;
class IRCode;
class IRInstruction;
struct MethodItemEntry;

using reg_t = uint32_t;

namespace opcode {
enum Branchingness : uint8_t;
} // namespace opcode

enum TryEntryType {
  TRY_START = 0,
  TRY_END = 1,
};

std::string show(TryEntryType t);

struct TryEntry {
  TryEntryType type;
  MethodItemEntry* catch_start;
  TryEntry(TryEntryType type, MethodItemEntry* catch_start)
      : type(type), catch_start(catch_start) {
    always_assert(catch_start != nullptr);
  }

  bool operator==(const TryEntry& other) const;
};

struct CatchEntry {
  DexType* catch_type;
  MethodItemEntry* next; // always null for catchall
  explicit CatchEntry(DexType* catch_type)
      : catch_type(catch_type), next(nullptr) {}

  bool operator==(const CatchEntry& other) const;
};

/**
 * A SwitchIndices represents the set of int values matching a packed switch
 * case. It could be the only value matching one case. There could also be a set
 * of values matching a switch case.
 */
using SwitchIndices = std::set<int>;

using InstructionEquality =
    std::function<bool(const IRInstruction&, const IRInstruction&)>;

/*
 * Multi is where an opcode encodes more than
 * one branch end-point.  This is for packed
 * and sparse switch.  The index is only relevant
 * for multi-branch encodings.  The target is
 * implicit in the flow, where the target is from
 * i.e. what has to be re-written is what is recorded
 * in IRInstruction*.
 */
enum BranchTargetType {
  BRANCH_SIMPLE = 0,
  BRANCH_MULTI = 1,
};

struct BranchTarget {
  MethodItemEntry* src;
  BranchTargetType type;

  // The key that a value must match to take this case in a switch statement.
  int32_t case_key;

  BranchTarget() = default;
  explicit BranchTarget(MethodItemEntry* src) : src(src), type(BRANCH_SIMPLE) {}

  BranchTarget(MethodItemEntry* src, int32_t case_key)
      : src(src), type(BRANCH_MULTI), case_key(case_key) {}

  bool operator==(const BranchTarget& other) const;
};

/**
 * A SourceBlock refers to a method and block ID that the following code came
 * from. It also has a float payload at the moment (though that is in flow),
 * which will be used for profiling information.
 */
struct SourceBlock {
  const DexString* src{nullptr};
  std::unique_ptr<SourceBlock> next;
  // Large methods exist, but a 32-bit integer is safe.
  // Use the maximum for things that we do not want to emit at this point.
  static constexpr uint32_t kSyntheticId = std::numeric_limits<uint32_t>::max();
  // Per-method source-block id, assigned by one of three mechanisms:
  //  - source_blocks::insert_source_blocks (the profiling-insertion flow) hands
  //    out dense ids 0,1,2,... in visit_in_order/DFS order;
  //    SourceBlockConsistencyCheck relies on that density (id < num_src_blks).
  //  - the IRAssembler preserves an authored id verbatim (it never renumbers),
  //    so ids in assembled test fixtures are stable handles.
  //  - clone helpers stamp kSyntheticId on copies.
  uint32_t id{0};
  // Float has enough precision.
  class Val {
    static constexpr float kNoneVal = std::numeric_limits<float>::quiet_NaN();

   public:
    Val() = default;

    constexpr Val(float v, float a) noexcept : m_val({v, a}) {}

    static constexpr Val none() { return Val(kNoneVal, kNoneVal); }

    static constexpr Val default_value() { return Val(0, 0); }

    bool is_default_value() const {
      return m_val.val == 0 && m_val.appear100 == 0;
    }

    // NOLINTNEXTLINE
    /* implicit */ operator bool() const { return m_val.val == m_val.val; };

    bool operator==(const Val& other) const {
      return (m_val.val == other.m_val.val &&
              m_val.appear100 == other.m_val.appear100) ||
             (m_val.val != m_val.val && other.m_val.val != other.m_val.val);
    }

    bool operator!=(const Val& other) const { return !(*this == other); }

    // To access like an `optional`.

    struct ValPair {
      float val;
      float appear100;
    };

    ValPair& operator*() {
      redex_assert(operator bool());
      return m_val;
    }
    const ValPair& operator*() const {
      redex_assert(operator bool());
      return m_val;
    }

    ValPair* operator->() {
      redex_assert(operator bool());
      return &m_val;
    }
    const ValPair* operator->() const {
      redex_assert(operator bool());
      return &m_val;
    }

   private:
    ValPair m_val;
  };
  const uint32_t vals_size{0};

  SourceBlock() = default;
  SourceBlock(const DexString* src, size_t id) : src(src), id(id) {}
  SourceBlock(const DexString* src, size_t id, const std::vector<Val>& v)
      : src(src),
        id(id),
        vals_size((uint32_t)v.size()),
        m_storage(make_storage(v)) {}
  SourceBlock(const SourceBlock& other)
      : src(other.src),
        next(other.next == nullptr ? nullptr : new SourceBlock(*other.next)),
        id(other.id),
        vals_size(other.vals_size),
        m_storage(make_storage(other.m_storage.get())) {}
  SourceBlock& operator=(const SourceBlock&);

  std::optional<float> get_val(size_t i) const {
    const auto& val = get_at(i);
    return val ? std::optional<float>(val->val) : std::nullopt;
  }
  std::optional<float> get_appear100(size_t i) const {
    const auto& val = get_at(i);
    return val ? std::optional<float>(val->appear100) : std::nullopt;
  }

  const Val& get_at(size_t i) const {
    if (m_storage) {
      if (m_storage->bits.contains_index(i)) {
        size_t idx = m_storage->bits.count_before_index(i);
        return m_storage->data[idx];
      }
    }
    return default_value;
  }

  void set_at(size_t i, const Val& val) {
    if (!m_storage || !m_storage->bits.contains_index(i)) {
      if (val.is_default_value()) {
        return;
      }
      expand_storage();
    }
    size_t idx = m_storage->bits.count_before_index(i);
    m_storage->data[idx] = val;
  }

  void fill(const Val& val);

  template <typename Fn>
  void apply_at(size_t i, const Fn& fn) {
    if (!m_storage || !m_storage->bits.contains_index(i)) {
      Val val = Val::default_value();
      fn(val);
      if (val.is_default_value()) {
        return;
      }
      expand_storage();
      m_storage->data[i] = val;
      return;
    }
    size_t idx = m_storage->bits.count_before_index(i);
    fn(m_storage->data[idx]);
  }

  template <typename Fn>
  void foreach_val(const Fn& fn) const {
    if (!m_storage) {
      for (size_t i = 0; i < vals_size; i++) {
        const Val val = Val::default_value();
        invoke_fn(fn, i, val);
      }
      return;
    }
    for (size_t i = 0; i < vals_size; i++) {
      if (m_storage->bits.contains_index(i)) {
        size_t idx = m_storage->bits.count_before_index(i);
        const Val& val = m_storage->data[idx];
        invoke_fn(fn, i, val);
      } else {
        const Val val = Val::default_value();
        invoke_fn(fn, i, val);
      }
    }
  }

  template <typename Fn>
  void foreach_val(const Fn& fn) {
    if (!m_storage) {
      for (size_t i = 0; i < vals_size; i++) {
        Val val = Val::default_value();
        invoke_fn(fn, i, val);
        if (!val.is_default_value()) {
          expand_storage();
          m_storage->data[i] = val;
        }
      }
      return;
    }
    for (size_t i = 0; i < vals_size; i++) {
      if (m_storage->bits.contains_index(i)) {
        size_t idx = m_storage->bits.count_before_index(i);
        Val& val = m_storage->data[idx];
        invoke_fn(fn, i, val);
      } else {
        Val val = Val::default_value();
        invoke_fn(fn, i, val);
        if (!val.is_default_value()) {
          expand_storage();
          m_storage->data[i] = val;
        }
      }
    }
  }

  template <typename Fn>
  bool foreach_val_early(const Fn& fn) const {
    if (!m_storage) {
      for (size_t i = 0; i < vals_size; i++) {
        const Val val = Val::default_value();
        if (invoke_fn(fn, i, val)) {
          return true;
        }
      }
      return false;
    }
    for (size_t i = 0; i < vals_size; i++) {
      if (m_storage->bits.contains_index(i)) {
        size_t idx = m_storage->bits.count_before_index(i);
        const Val& val = m_storage->data[idx];
        if (invoke_fn(fn, i, val)) {
          return true;
        }
      } else {
        const Val val = Val::default_value();
        if (invoke_fn(fn, i, val)) {
          return true;
        }
      }
    }
    return false;
  }

  template <typename Fn>
  bool foreach_val_early(const Fn& fn) {
    if (!m_storage) {
      for (size_t i = 0; i < vals_size; i++) {
        Val val = Val::default_value();
        bool res = invoke_fn(fn, i, val);
        if (!val.is_default_value()) {
          expand_storage();
          m_storage->data[i] = val;
        }
        if (res) {
          return true;
        }
      }
      return false;
    }
    for (size_t i = 0; i < vals_size; i++) {
      if (m_storage->bits.contains_index(i)) {
        size_t idx = m_storage->bits.count_before_index(i);
        Val& val = m_storage->data[idx];
        if (invoke_fn(fn, i, val)) {
          return true;
        }
      } else {
        Val val = Val::default_value();
        bool res = invoke_fn(fn, i, val);
        if (!val.is_default_value()) {
          expand_storage();
          m_storage->data[i] = val;
        }
        if (res) {
          return true;
        }
      }
    }
    return false;
  }

  template <typename Fn>
  std::optional<size_t> find_val(const Fn& pred) const {
    if (!m_storage) {
      for (size_t i = 0; i < vals_size; i++) {
        const Val val = Val::default_value();
        if (invoke_fn(pred, i, val)) {
          return i;
        }
      }
      return std::nullopt;
    }
    for (size_t i = 0; i < vals_size; i++) {
      if (m_storage->bits.contains_index(i)) {
        size_t idx = m_storage->bits.count_before_index(i);
        const Val& val = m_storage->data[idx];
        if (invoke_fn(pred, i, val)) {
          return i;
        }
      } else {
        const Val val = Val::default_value();
        if (invoke_fn(pred, i, val)) {
          return i;
        }
      }
    }
    return std::nullopt;
  }

  bool operator==(const SourceBlock& other) const;

  bool operator!=(const SourceBlock& other) const { return !(*this == other); }

  size_t hash_ids() const;

  void append(std::unique_ptr<SourceBlock> sb) {
    SourceBlock* last = this;
    while (last->next != nullptr) {
      last = last->next.get();
    }
    last->next = std::move(sb);
  }

  SourceBlock* get_last_in_chain() {
    auto* last = this;
    while (last->next != nullptr) {
      last = last->next.get();
    }
    return last;
  }
  const SourceBlock* get_last_in_chain() const {
    const auto* last = this;
    while (last->next != nullptr) {
      last = last->next.get();
    }
    return last;
  }

  std::string show(bool quoted_src = false) const;

  void max(const SourceBlock& other);

  void min(const SourceBlock& other);

  // Additive combine: sums `val` (a count) and maxes `appear100` (an appearance
  // probability, which must never be summed). Use when combining the counts of
  // distinct control-flow paths that accumulate (a true merge / outline over N
  // sites); use `max` when reconciling two observations of the SAME point.
  void add(const SourceBlock& other);

  bool normalize(size_t* elided_vals, size_t* unelided_vals);

 private:
  static const Val default_value;

  class InteractionBitSet {
   private:
    uint64_t m_bits;
    explicit InteractionBitSet(uint64_t bits) : m_bits(bits) {}

   public:
    // We are not including `sizeof(m_bits) * 8` itself, as that would lead to
    // undefined behavior in the expression `((uint64_t)1 << 64) - 1` in
    // C++ (although completely fine as far as the realizing X86 instruction are
    // concerned).
    static const constexpr size_t MAX_SIZE = sizeof(m_bits) * 8 - 1;

    InteractionBitSet() : m_bits(0) {}

    static InteractionBitSet from_index(size_t i) {
      return InteractionBitSet(((uint64_t)1) << i);
    }

    static InteractionBitSet all(size_t size) {
      return InteractionBitSet((((uint64_t)1) << size) - 1);
    }

    InteractionBitSet first() { return InteractionBitSet(m_bits & -m_bits); }

    bool contains(const InteractionBitSet& other) const {
      return (m_bits & other.m_bits) != 0;
    }

    bool contains_index(size_t i) const { return contains(from_index(i)); }

    bool operator==(const InteractionBitSet& other) const {
      return m_bits == other.m_bits;
    }

    // NOLINTNEXTLINE
    /* implicit */ operator bool() const { return m_bits != 0; }

    size_t first_index() const { return std::countr_zero(m_bits); }

    size_t count() const { return std::popcount(m_bits); }

    size_t count_before_index(size_t i) const {
      return count_before(from_index(i));
    }

    size_t count_before(InteractionBitSet other) const {
      return std::popcount(m_bits & (other.m_bits - 1));
    }

    void add(InteractionBitSet other) { m_bits |= other.m_bits; }

    void intersect_with(InteractionBitSet other) { m_bits &= other.m_bits; }

    void remove(InteractionBitSet other) { m_bits &= ~other.m_bits; }

    void remove_first() { m_bits &= (m_bits - 1); }
  };

  struct Storage {
    InteractionBitSet bits; // for each set bit, we have a data entry
    Val data[1]; // variable sized, matching number of bits set
  };

  struct FreeDeleter {
    void operator()(void* p) const { std::free(p); }
  };

  // nullptr m_storage represents vals_size many Val::default_value() values.
  std::unique_ptr<Storage, FreeDeleter> m_storage;

  template <typename Fn, typename ValType>
  static auto invoke_fn(const Fn& fn, size_t i, ValType& val) {
    if constexpr (std::is_invocable_v<Fn, size_t, ValType&>) {
      return fn(i, val);
    } else {
      return fn(val);
    }
  }

  static std::unique_ptr<Storage, FreeDeleter> make_storage(
      size_t vals_size, const Val& val = Val::default_value());

  static std::unique_ptr<Storage, FreeDeleter> make_storage(
      const Storage* other);

  static std::unique_ptr<Storage, FreeDeleter> make_storage(
      const std::vector<Val>& vals);

  static bool has_all_default_values(const Storage* storage);

  static bool has_default_value(const Storage* storage);

  bool is_storage_expanded() const {
    return vals_size == 0 ||
           (m_storage && m_storage->bits == InteractionBitSet::all(vals_size));
  }

  void expand_storage();
};

static_assert(sizeof(void*) != 8 || sizeof(SourceBlock) == 32);

/*
 * A Remark is a redex-internal, block-anchored breadcrumb that optimization
 * passes can stamp onto the code they touch and later passes can read. Like a
 * SourceBlock it rides through the whole pipeline (cloned by deep_copy, carried
 * through split/inline/merge) and is NEVER serialized to dex -- the strings are
 * deliberately excluded from gather_strings and the MIE is stripped in
 * IRCode::try_sync before emission. The fields carry no baked-in semantics
 * beyond `producer`; their meaning is defined by the producing/consuming pass:
 *   - producer: the producing pass, e.g. "InsertRemarksForTracingPass".
 *   - val_str:  a producer-defined label, e.g. the deobfuscated method name.
 *   - val_int:  a producer-defined integer, e.g. the block id.
 *
 * The strings are `const DexString*` (not std::string) to reuse Redex's
 * existing string interning: producers hand us already-interned DexStrings, so
 * a Remark stores a single pooled pointer instead of owning a heap buffer, and
 * equality is a cheap pointer compare. (The interned strings are still excluded
 * from gather_strings, so nothing new is emitted to the dex string pool.)
 */
struct Remark {
  const DexString* producer{nullptr};
  const DexString* val_str{nullptr};
  int64_t val_int{0};
  // ~8 bytes of headroom: a Remark is heap-allocated and, at 24 bytes, rounds
  // up to a 32-byte allocation, so a future field (another int64_t or a
  // DexString*) can be added here at no allocation cost.

  Remark(const DexString* producer, const DexString* val_str, int64_t val_int)
      : producer(producer), val_str(val_str), val_int(val_int) {}

  bool operator==(const Remark& other) const {
    return producer == other.producer && val_str == other.val_str &&
           val_int == other.val_int;
  }
  bool operator!=(const Remark& other) const { return !(*this == other); }
};

/*
 * MethodItemEntry (and the IRLists that it gets linked into) is a data
 * structure of DEX methods that is easier to modify than DexMethod.
 *
 * For example, when inserting a new instruction into a DexMethod, one needs
 * to recalculate branch offsets, try-catch regions, and debug info. None of
 * that is necessary when inserting into an IRList; it gets done when the
 * IRList gets translated back into a DexMethod by IRCode::sync().
 */

enum MethodItemType {
  // Begins or ends a try region. Points to the first associated catch block
  MFLOW_TRY,

  // Found at the beginning of an exception handler block. Points to the next
  // catch block (in case this one does not match)
  MFLOW_CATCH,

  // The actual instructions
  MFLOW_OPCODE,
  MFLOW_DEX_OPCODE,

  // The target of a goto, if, or switch. Also known as a "label"
  MFLOW_TARGET,

  // These hold information about the following `MFLOW_(DEX_)OPCODE`s
  MFLOW_DEBUG,
  MFLOW_POSITION,

  // This holds information about the source block.
  MFLOW_SOURCE_BLOCK,

  // A redex-internal breadcrumb; never serialized to dex (see struct Remark).
  MFLOW_REMARK,

  // A no-op
  MFLOW_FALLTHROUGH,
};

std::ostream& operator<<(std::ostream&, const MethodItemType& type);

// A metadata entry annotates the following instruction but is itself neither
// code nor control flow: debug info, source position, source block, or remark.
// These are skipped when comparing two IRLists for structural equality.
inline bool is_metadata(MethodItemType type) {
  return type == MFLOW_DEBUG || type == MFLOW_POSITION ||
         type == MFLOW_SOURCE_BLOCK || type == MFLOW_REMARK;
}

// Whether a `code_only` show() view prints this entry. Such views drop the
// source-position / redex-internal annotations (position, source block, remark)
// but keep debug info and everything else.
inline bool shown_in_code_only(MethodItemType type) {
  return !is_metadata(type) || type == MFLOW_DEBUG;
}

struct MethodItemEntry {
  boost::intrusive::list_member_hook<> list_hook_;
  MethodItemType type;

  union {
    TryEntry* tentry{nullptr};
    CatchEntry* centry;
    IRInstruction* insn;
    // dex_insn should only ever be used by the instruction lowering / output
    // code. Do NOT use it in passes!
    DexInstruction* dex_insn;
    BranchTarget* target;
    std::unique_ptr<DexDebugInstruction> dbgop;
    std::unique_ptr<DexPosition> pos;
    std::unique_ptr<SourceBlock> src_block;
    std::unique_ptr<Remark> remark;
  };
  MethodItemEntry(const MethodItemEntry&);
  MethodItemEntry& operator=(const MethodItemEntry&);
  explicit MethodItemEntry(DexInstruction* dex_insn) {
    this->type = MFLOW_DEX_OPCODE;
    this->dex_insn = dex_insn;
  }
  explicit MethodItemEntry(IRInstruction* insn) {
    this->type = MFLOW_OPCODE;
    this->insn = insn;
  }
  MethodItemEntry(TryEntryType try_type, MethodItemEntry* catch_start)
      : type(MFLOW_TRY), tentry(new TryEntry(try_type, catch_start)) {}
  explicit MethodItemEntry(DexType* catch_type)
      : type(MFLOW_CATCH), centry(new CatchEntry(catch_type)) {}
  explicit MethodItemEntry(BranchTarget* bt) {
    this->type = MFLOW_TARGET;
    this->target = bt;
  }
  explicit MethodItemEntry(std::unique_ptr<DexDebugInstruction> dbgop);
  explicit MethodItemEntry(std::unique_ptr<DexPosition> pos);
  explicit MethodItemEntry(std::unique_ptr<SourceBlock> src_block);
  explicit MethodItemEntry(std::unique_ptr<Remark> remark);

  bool operator==(const MethodItemEntry&) const;

  bool operator!=(const MethodItemEntry& that) const {
    return !(*this == that);
  }

  MethodItemEntry() : type(MFLOW_FALLTHROUGH) {}
  ~MethodItemEntry();

  /*
   * This should only ever be used by the instruction lowering step. Do NOT use
   * it in passes!
   */
  void replace_ir_with_dex(DexInstruction* dex_insn);

  void gather_strings(std::vector<const DexString*>& lstring) const;
  void gather_types(std::vector<const DexType*>& ltype) const;
  void gather_init_classes(std::vector<const DexType*>& ltype) const;
  void gather_fields(std::vector<DexFieldRef*>& lfield) const;
  void gather_methods(std::vector<DexMethodRef*>& lmethod) const;
  void gather_callsites(std::vector<DexCallSite*>& lcallsite) const;
  void gather_methodhandles(std::vector<DexMethodHandle*>& lmethodhandle) const;

  opcode::Branchingness branchingness() const;
};

class MethodItemEntryCloner {
  // We need a map of MethodItemEntry we have created because a branch
  // points to another MethodItemEntry which may have been created or not
  UnorderedMap<const MethodItemEntry*, MethodItemEntry*> m_entry_map;
  // for remapping the parent position pointers
  UnorderedMap<DexPosition*, DexPosition*> m_pos_map;
  std::vector<DexPosition*> m_positions_to_fix;

 public:
  MethodItemEntryCloner();
  MethodItemEntry* clone(const MethodItemEntry* mie);

  /*
   * This should to be called after the whole method is already cloned so that
   * m_pos_map has all the positions in the method.
   *
   * Don't change any parent pointers that point to `ignore_pos`. This is used
   * for inlining because the invoke position is the parent but it isn't in the
   * callee. If you don't have any positions to ignore, nullptr is a safe
   * default.
   */
  void fix_parent_positions(const DexPosition* ignore_pos = nullptr);
};

using MethodItemMemberListOption =
    boost::intrusive::member_hook<MethodItemEntry,
                                  boost::intrusive::list_member_hook<>,
                                  &MethodItemEntry::list_hook_>;

class IRList {
 private:
  using IntrusiveList =
      boost::intrusive::list<MethodItemEntry, MethodItemMemberListOption>;

  IntrusiveList m_list;
  void remove_branch_targets(IRInstruction* branch_inst);

  static void disposer(MethodItemEntry* mie) { delete mie; }

 public:
  using iterator = IntrusiveList::iterator;
  using const_iterator = IntrusiveList::const_iterator;
  using reverse_iterator = IntrusiveList::reverse_iterator;
  using const_reverse_iterator = IntrusiveList::const_reverse_iterator;
  using difference_type = IntrusiveList::difference_type;

  IRList::iterator main_block();
  IRList::iterator make_if_block(const IRList::iterator& cur,
                                 IRInstruction* insn,
                                 IRList::iterator* false_block);
  IRList::iterator make_if_else_block(const IRList::iterator& cur,
                                      IRInstruction* insn,
                                      IRList::iterator* false_block,
                                      IRList::iterator* true_block);
  IRList::iterator make_switch_block(
      const IRList::iterator& cur,
      IRInstruction* insn,
      IRList::iterator* default_block,
      std::map<SwitchIndices, IRList::iterator>& cases);

  size_t size() const { return m_list.size(); }
  bool empty() const { return m_list.empty(); }

  /*
   * Removes a subset of MFLOW_DEBUG instructions.
   */
  void cleanup_debug();

  /*
   * Removes a subset of MFLOW_DEBUG instructions. valid_regs
   * is an accumulator set of registers used by either DBG_START_LOCAL
   * or DBG_START_LOCAL_EXTENDED. The DBG_END_LOCAL and DBG_RESTART_LOCAL
   * instructions are erased, unless valid_regs contains the registers they use.
   */
  void cleanup_debug(UnorderedSet<reg_t>& valid_regs);

  /* DEPRECATED! Use the version below that passes in the iterator instead,
   * which is O(1) instead of O(n). */
  /* Passes memory ownership of "from" to callee.  It will delete it. */
  void replace_opcode(IRInstruction* from, IRInstruction* to);

  /* DEPRECATED! Use the version below that passes in the iterator instead,
   * which is O(1) instead of O(n). */
  /* Passes memory ownership of "from" to callee.  It will delete it. */
  void replace_opcode(IRInstruction* to_delete,
                      const std::vector<IRInstruction*>& replacements);

  /* Passes memory ownership of "from" to callee.  It will delete it. */
  void replace_opcode(const IRList::iterator& it,
                      const std::vector<IRInstruction*>& replacements);

  /*
   * Does exactly what it says and you SHOULD be afraid. This is mainly useful
   * to appease the compiler in various scenarios of unreachable code.
   */
  void replace_opcode_with_infinite_loop(IRInstruction* from);

  /* Like replace_opcode, but both :from and :to must be branch opcodes.
   * :to will end up jumping to the same destination as :from. */
  void replace_branch(IRInstruction* from, IRInstruction* to);

  /*
   * Find the subrange of load-param instructions. These instructions should
   * always be at the beginning of the method.
   */
  boost::sub_range<IRList> get_param_instructions();

  bool structural_equals(const IRList& other,
                         const InstructionEquality& instruction_equals) const;

  /* Passes memory ownership of "mie" to callee. */
  void push_back(MethodItemEntry& mie) { m_list.push_back(mie); }

  /* Passes memory ownership of "mie" to callee. */
  void push_front(MethodItemEntry& mie) { m_list.push_front(mie); }

  /*
   * Insert after instruction :position.
   *
   * position = nullptr means we insert at the head
   *
   * If position is an instruction that has a move-result-pseudo suffix, we
   * will do the insertion after the move-result-pseudo.
   */
  void insert_after(IRInstruction* position,
                    const std::vector<IRInstruction*>& opcodes);

  IRList::iterator insert_before(const IRList::iterator& position,
                                 MethodItemEntry&);

  IRList::iterator insert_after(const IRList::iterator& position,
                                MethodItemEntry&);

  template <class... Args>
  IRList::iterator insert_before(const IRList::iterator& position,
                                 Args&&... args) {
    return insert_before(position,
                         *(new MethodItemEntry(std::forward<Args>(args)...)));
  }

  template <class... Args>
  IRList::iterator insert_after(const IRList::iterator& position,
                                Args&&... args) {
    always_assert(position != this->end());
    return insert_after(position,
                        *(new MethodItemEntry(std::forward<Args>(args)...)));
  }

  /* DEPRECATED! Use the version below that passes in the iterator instead,
   * which is O(1) instead of O(n). */
  /* Memory ownership of "insn" passes to callee, it will delete it. */
  void remove_opcode(IRInstruction* insn);

  /*
   * Remove the instruction that :it points to.
   *
   * If :it points to an instruction that has a move-result-pseudo suffix, we
   * remove both that instruction and the move-result-pseudo that follows.
   */
  void remove_opcode(const IRList::iterator& it);

  /*
   * Returns an estimate of the number of 2-byte code units needed to encode
   * all the instructions.
   */
  size_t sum_opcode_sizes() const;

  // similar to sum_opcode_sizes, but takes into account non-opcode payloads
  uint32_t estimate_code_units() const;

  /*
   * Returns the number of instructions.
   */
  size_t count_opcodes() const;

  // transfer all of `other` into `this` starting at `pos`
  // memory ownership is also transferred
  void splice(const IRList::const_iterator& pos, IRList& other) {
    m_list.splice(pos, other.m_list);
  }

  // transfer `other[begin]` to `other[end]` into `this` starting at `pos`
  // memory ownership is also transferred
  void splice_selection(const IRList::const_iterator& pos,
                        IRList& other,
                        const IRList::const_iterator& begin,
                        const IRList::const_iterator& end) {
    m_list.splice(pos, other.m_list, begin, end);
  }

  template <typename Predicate>
  void remove_and_dispose_if(Predicate predicate) {
    m_list.remove_and_dispose_if(predicate, disposer);
  }

  void sanity_check() const;

  IRList::iterator begin() { return m_list.begin(); }
  IRList::iterator end() { return m_list.end(); }
  IRList::const_iterator begin() const { return m_list.begin(); }
  IRList::const_iterator end() const { return m_list.end(); }
  IRList::const_iterator cbegin() const { return m_list.cbegin(); }
  IRList::const_iterator cend() const { return m_list.cend(); }
  IRList::reverse_iterator rbegin() { return m_list.rbegin(); }
  IRList::reverse_iterator rend() { return m_list.rend(); }
  IRList::const_reverse_iterator rbegin() const { return m_list.rbegin(); }
  IRList::const_reverse_iterator rend() const { return m_list.rend(); }

  void gather_catch_types(std::vector<const DexType*>& ltype) const;
  void gather_strings(std::vector<const DexString*>& lstring) const;
  void gather_types(std::vector<const DexType*>& ltype) const;
  void gather_init_classes(std::vector<const DexType*>& ltype) const;
  void gather_fields(std::vector<DexFieldRef*>& lfield) const;
  void gather_methods(std::vector<DexMethodRef*>& lmethod) const;
  void gather_callsites(std::vector<DexCallSite*>& lcallsite) const;
  void gather_methodhandles(std::vector<DexMethodHandle*>& lmethodhandle) const;

  IRList::iterator erase(const IRList::iterator& it) {
    return m_list.erase(it);
  }
  IRList::iterator erase_and_dispose(const IRList::iterator& it) {
    return m_list.erase_and_dispose(it, disposer);
  }
  IRList::iterator insn_erase_and_dispose(const IRList::iterator& it);

  void clear_and_dispose() { m_list.clear_and_dispose(disposer); }
  void insn_clear_and_dispose();

  IRList::iterator iterator_to(MethodItemEntry& mie) {
    return m_list.iterator_to(mie);
  }

  IRList::const_iterator iterator_to(const MethodItemEntry& mie) const {
    return m_list.iterator_to(mie);
  }

  enum class ConsecutiveStyle {
    kChain,
    kDrop,
    kMax, // This is for as long as kDrop is not correct because of profile
          // issues.
  };
  static ConsecutiveStyle CONSECUTIVE_STYLE;

  void chain_consecutive_source_blocks(
      ConsecutiveStyle style = CONSECUTIVE_STYLE);

  friend std::string show(const IRCode*, bool code_only);
};

std::string show(const IRList*, bool code_only = false);

namespace ir_list {

template <bool is_const>
class InstructionIteratorImpl {
  using Iterator = typename std::
      conditional<is_const, IRList::const_iterator, IRList::iterator>::type;
  using Mie = typename std::
      conditional<is_const, const MethodItemEntry, MethodItemEntry>::type;

 private:
  Iterator m_it;
  Iterator m_end;
  /*
   * If m_it doesn't point to an MIE of type MFLOW_OPCODE, increment it until
   * it does. Otherwise do nothing.
   */
  void to_next_instruction() {
    while (m_it != m_end && m_it->type != MFLOW_OPCODE) {
      ++m_it;
    }
  }
  /*
   * If m_it doesn't point to an MIE of type MFLOW_OPCODE, decrement it until
   * it does. Otherwise do nothing.
   */
  void to_prev_instruction() {
    while (m_it->type != MFLOW_OPCODE) {
      --m_it;
    }
  }

 public:
  using difference_type = long;
  using value_type = MethodItemEntry;
  using pointer = Mie*;
  using reference = Mie&;
  using iterator_category = std::bidirectional_iterator_tag;

  InstructionIteratorImpl() {}
  InstructionIteratorImpl(const Iterator& it, const Iterator& end)
      : m_it(it), m_end(end) {
    to_next_instruction();
  }

  // NOLINTNEXTLINE(google-explicit-constructor)
  InstructionIteratorImpl(const InstructionIteratorImpl<false>& rhs)
      : m_it(rhs.m_it), m_end(rhs.m_end) {}

  InstructionIteratorImpl& operator=(
      const InstructionIteratorImpl<false>& rhs) {
    m_it = rhs.m_it;
    m_end = rhs.m_end;
    return *this;
  }

  InstructionIteratorImpl& operator++() {
    ++m_it;
    to_next_instruction();
    return *this;
  }

  InstructionIteratorImpl operator++(int) {
    auto rv = *this;
    ++(*this);
    return rv;
  }

  InstructionIteratorImpl& operator--() {
    --m_it;
    to_prev_instruction();
    return *this;
  }

  InstructionIteratorImpl operator--(int) {
    auto rv = *this;
    --(*this);
    return rv;
  }

  reference operator*() const { return *m_it; }

  pointer operator->() const { return &*m_it; }

  bool operator==(const InstructionIteratorImpl& ii) const {
    return m_it == ii.m_it;
  }

  bool operator!=(const InstructionIteratorImpl& ii) const {
    return !(m_it == ii.m_it);
  }

  Iterator unwrap() const { return m_it; }

  void reset(Iterator it) {
    m_it = it;
    to_next_instruction();
  }

  template <bool kConst>
  friend class InstructionIteratorImpl;
};

template <bool is_const>
class InstructionIterableImpl {
 protected:
  using Iterator = typename std::
      conditional<is_const, IRList::const_iterator, IRList::iterator>::type;
  Iterator m_begin;
  Iterator m_end;

  // Only callable by ConstInstructionIterable. If this were public, we may try
  // to bind const iterators to non-const members
  template <class T>
  InstructionIterableImpl(const T& mentry_list,
                          // we add this unused parameter so we don't
                          // accidentally resolve to this constructor when we
                          // meant to call the non-const version
                          bool /* unused */)
      : m_begin(mentry_list.begin()), m_end(mentry_list.end()) {}

 public:
  template <class T>
  explicit InstructionIterableImpl(T& mentry_list)
      : m_begin(mentry_list.begin()), m_end(mentry_list.end()) {}

  template <typename T>
  explicit InstructionIterableImpl(T* mentry_list)
      : InstructionIterableImpl(*mentry_list) {}

  InstructionIteratorImpl<is_const> begin() const {
    return InstructionIteratorImpl<is_const>(m_begin, m_end);
  }

  InstructionIteratorImpl<is_const> end() const {
    return InstructionIteratorImpl<is_const>(m_end, m_end);
  }

  // The same instructions, last to first.
  auto reversed() const {
    return boost::make_iterator_range(std::make_reverse_iterator(end()),
                                      std::make_reverse_iterator(begin()));
  }

  bool empty() const { return begin() == end(); }
};

using InstructionIterator = InstructionIteratorImpl<false>;
using ConstInstructionIterator = InstructionIteratorImpl<true>;

using InstructionIterable = InstructionIterableImpl<false>;
class ConstInstructionIterable : public InstructionIterableImpl<true> {
 public:
  // We extend the Impl so we can add the const versions of the constructors.
  // We can't have the const constructors on the non-const iterables
  template <class T>
  explicit ConstInstructionIterable(const T& mentry_list)
      : InstructionIterableImpl<true>(mentry_list, false) {}

  template <class T>
  explicit ConstInstructionIterable(const T* mentry_list)
      : ConstInstructionIterable(*mentry_list) {}
};

IRInstruction* primary_instruction_of_move_result_pseudo(IRList::iterator it);

IRInstruction* primary_instruction_of_move_result(IRList::iterator it);

IRInstruction* move_result_pseudo_of(IRList::iterator it);

} // namespace ir_list

template <class T>
inline ir_list::InstructionIterable InstructionIterable(T& t) {
  return ir_list::InstructionIterable(t);
}

template <class T>
inline ir_list::InstructionIterable InstructionIterable(T* t) {
  return ir_list::InstructionIterable(*t);
}

template <class T>
inline ir_list::ConstInstructionIterable InstructionIterable(const T& t) {
  return ir_list::ConstInstructionIterable(t);
}

template <class T>
inline ir_list::ConstInstructionIterable InstructionIterable(const T* t) {
  return ir_list::ConstInstructionIterable(*t);
}
