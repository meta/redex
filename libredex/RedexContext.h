/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <array>
#include <atomic>
#include <boost/functional/hash.hpp>
#include <cstring>
#include <deque>
#include <functional>
#include <limits>
#include <list>
#include <map>
#include <mutex>
#include <queue>
#include <set>
#include <sstream>
#include <string_view>
#include <vector>

#include "ConcurrentContainers.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexMemberRefs.h"
#include "FrequentlyUsedPointersCache.h"

class DexCallSite;
class DexClass;
class DexLocation;
class DexDebugInstruction;
class DexField;
class DexFieldRef;
class DexMethod;
class DexMethodHandle;
class DexMethodRef;
class DexProto;
class DexString;
struct DexStringRepr;
class DexType;
class DexTypeList;
class PositionPatternSwitchManager;
struct DexDebugEntry;
struct DexFieldSpec;
struct DexPosition;
struct RedexContext;
namespace keep_rules {
struct AssumeReturnValue;
} // namespace keep_rules

extern RedexContext* g_redex;

#if defined(__SSE4_2__) && defined(__linux__) && defined(__STRCMP_LESS__)
extern "C" bool strcmp_less(const char* str1, const char* str2);
#endif

struct RedexContext {
  explicit RedexContext(bool allow_class_duplicates = false);
  ~RedexContext();

  const DexString* make_string(std::string_view s);
  const DexString* get_string(std::string_view s);

  DexType* make_type(const DexString* dstring);
  DexType* get_type(const DexString* dstring);

  /**
   * Change the name of a type, but do not remove the old name from the mapping
   */
  void set_type_name(DexType* type, const DexString* new_name);
  /**
   * Add an additional name to refer to a type (a deobfuscated name for example)
   */
  void alias_type_name(DexType* type, const DexString* new_name);
  /**
   * Remove a name -> type entry from the map
   */
  void remove_type_name(const DexString* name);

  DexFieldRef* make_field(const DexType* container,
                          const DexString* name,
                          const DexType* type);
  DexFieldRef* get_field(const DexType* container,
                         const DexString* name,
                         const DexType* type);

  /**
   * Add an additional name to refer to a field (a deobfuscated name for
   * example)
   */
  void alias_field_name(DexFieldRef* field, const DexString* new_name);

  void erase_field(DexFieldRef*);
  void erase_field(const DexType* container,
                   const DexString* name,
                   const DexType* type);
  void mutate_field(DexFieldRef* field,
                    const DexFieldSpec& ref,
                    bool rename_on_collision);

  using DexTypeListContainerType = std::vector<const DexType*>;

  DexTypeList* make_type_list(DexTypeListContainerType&& p);
  DexTypeList* get_type_list(const DexTypeListContainerType& p);

  DexProto* make_proto(const DexType* rtype,
                       const DexTypeList* args,
                       const DexString* shorty);
  DexProto* get_proto(const DexType* rtype, const DexTypeList* args);

  DexMethodRef* make_method(const DexType* type,
                            const DexString* name,
                            const DexProto* proto);
  DexMethodRef* get_method(const DexType* type,
                           const DexString* name,
                           const DexProto* proto);
  UnorderedMap<std::string, UnorderedMap<std::string, DexMethodRef*>>
  get_baseline_profile_method_map(
      std::unordered_set<DexMethodRef*>& parsed_methods);

  /**
   * Add an additional name to refer to a method (a deobfuscated name for
   * example)
   */
  void alias_method_name(DexMethodRef* method, const DexString* new_name);

  void erase_method(DexMethodRef*);
  void erase_method(const DexType* type,
                    const DexString* name,
                    const DexProto* proto);
  void mutate_method(DexMethodRef* method,
                     const DexMethodSpec& new_spec,
                     bool rename_on_collision);

  // Registers a method as leaked. This is because
  // `DexMethod::delete_method(DexMethodRef)` does not currently delete a given
  // method, as there may still be references. Until that is addressed, we store
  // a reference to the method here to make sure that lsan doesn't find any
  // actual leak.
  void leak_method(DexMethodRef*);

  size_t leaked_methods();

  DexLocation* make_location(std::string_view store_name,
                             std::string_view file_name);
  DexLocation* get_location(std::string_view store_name,
                            std::string_view file_name);

  PositionPatternSwitchManager* get_position_pattern_switch_manager();

  // Return false on unique classes
  // Return true on benign duplicate classes
  // Throw RedexException on problematic duplicate classes
  bool class_already_loaded(DexClass* cls);

  void publish_class(DexClass* cls);

  // Call sites and method handles are created by the dex loader (DexIdx) and
  // referenced by non-owning raw pointers throughout the IR; they are not
  // interned by value. RedexContext takes ownership of each (as publish_class
  // does for classes) so it can be freed at teardown. Thread-safe: called from
  // the parallel dex-load path.
  void publish_callsite(DexCallSite* callsite);
  void publish_methodhandle(DexMethodHandle* methodhandle);

  DexClass* type_class(const DexType* t) const;
  DexType* class_type(const DexClass* cls) const;
  template <class TypeClassWalkerFn = void(const DexType*, const DexClass*)>
  void walk_type_class(TypeClassWalkerFn walker) {
    for (auto* cls : UnorderedIterable(m_classes)) {
      walker(class_type(cls), cls);
    }
  }

  const std::vector<DexClass*>& external_classes() const {
    return m_external_classes;
  }

  // Add a lambda to be called when RedexContext is destructed. This is
  // especially useful for resetting caches/singletons in tests.
  using Task = std::function<void(void)>;
  void add_destruction_task(const Task& t);

  static constexpr bool kDebugPointersCacheLoad = false;
  // Thread-safe; loads the cache at most once.
  void load_pointers_cache() {
    std::lock_guard<std::mutex> lock(m_pointers_cache_lock);
    if (m_pointers_cache_loaded.load(std::memory_order_relaxed)) {
      return;
    }
    m_pointers_cache.load();
    m_pointers_cache_loaded.store(true, std::memory_order_release);
  }
  const FrequentlyUsedPointers& pointers_cache() {
    if (!m_pointers_cache_loaded.load(std::memory_order_acquire)) {
      redex_assert(!kDebugPointersCacheLoad);
      load_pointers_cache();
    }
    return m_pointers_cache;
  }

  // Set and return field values keep_rules::AssumeReturnValue provided by
  // proguard rules.
  void set_field_value(DexField* field, keep_rules::AssumeReturnValue& val);
  keep_rules::AssumeReturnValue* get_field_value(DexField* field);
  void unset_field_value(DexField* field);

  // Set and return method's keep_rules::AssumeReturnValue provided by proguard
  // rules.
  void set_return_value(DexMethod* method, keep_rules::AssumeReturnValue& val);
  keep_rules::AssumeReturnValue* get_return_value(DexMethod* method);
  void unset_return_value(DexMethod* method);

  size_t num_sb_interaction_indices() const {
    return m_sb_interaction_indices.size();
  }
  size_t get_sb_interaction_index(const std::string& interaction) const {
    auto it = m_sb_interaction_indices.find(interaction);
    if (it == m_sb_interaction_indices.end()) {
      return std::numeric_limits<size_t>::max();
    }
    return it->second;
  }
  const UnorderedMap<std::string, size_t>& get_sb_interaction_indices() const {
    return m_sb_interaction_indices;
  }
  void set_sb_interaction_index(const UnorderedMap<std::string, size_t>& input);

  // This is for convenience.
  bool instrument_mode{false};
  bool slow_invariants_debug{false};
  bool disable_violation_fixes{false};

  // Off by default while the corrected behaviour is being measured; a
  // supported flag for as long as both behaviours need to coexist.
  // When set, transforms preserve the INTEGRITY of SourceBlock execution
  // counts rather than treating `val` as 0/1 coverage: a duplicated block has
  // its count apportioned across the copies instead of copied verbatim, a
  // block that loses a predecessor sheds the inflow that departed instead of
  // being clamped to the MAX over the survivors, and a synthesized callsite
  // takes its count from the profile instead of a literal. All three are
  // correct for coverage and wrong once vals carry counts.
  //
  // Named to pair with `run_count_integrity_after_each_pass`, which checks the
  // same invariant this maintains.
  //
  // Global rather than per-pass, following disable_violation_fixes above,
  // because the affected code is shared services with several owners:
  // constant propagation runs in ConstantPropagationPass,
  // InterproceduralConstantPropagationPass AND the inliner's shrinker, and
  // SwitchEquivFinder has no owning pass at all. A per-pass knob could also be
  // left half-set by a local `-J` arm override, silently measuring a
  // partially-corrected state.
  bool preserve_count_integrity{false};
  bool insert_remarks{false};

  bool ordering_changes_allowed() const { return m_ordering_changes_allowed; }
  void set_ordering_changes_allowed(bool new_val) {
    m_ordering_changes_allowed = new_val;
  }

  ConcurrentSet<const DexClass*> blanket_native_root_classes;
  ConcurrentSet<const DexMethod*> blanket_native_root_methods;

  // Release memory used by erased items and old ConcurrentHashtable storage
  // versions.
  void compact();

  InsertOnlyConcurrentSet<const DexString*> library_names;

 private:
  struct Strcmp;
  struct TruncatedStringHash;

  // A thread-safe container for raw string storage
  struct ConcurrentStringStorage {
    static constexpr size_t n_slots = 11;
    // A not thread-safe container, holding individually allocated buffers
    struct Container {
      struct Buffer {
        const size_t allocated;
        size_t used{0};
        size_t remaining() const { return allocated - used; }
        const std::unique_ptr<char[]> chars;
        const Buffer* next;
        Buffer(size_t size, Buffer* next)
            : allocated(size),
              chars(std::make_unique<char[]>(size)),
              next(next) {}
      };
      // Default size for buffers, or 0 to create one perfectly sized buffer per
      // allocation
      const size_t default_size;
      Buffer* buffer{nullptr};
      explicit Container(size_t default_size) : default_size(default_size) {}
      ~Container();
      char* allocate(size_t length);
    };
    // A context for a temporarily acquired container that will be released to
    // its owner when the context is destructed
    struct Context {
      ConcurrentStringStorage* owner;
      size_t index;
      Container* container;
      ~Context();
    };
    struct Stats {
      size_t allocated{0};
      size_t used{0};
      size_t containers{0};
      size_t buffers{0};
      size_t waited{0};
      size_t contention{0};
      size_t sorted{0};
    };
    const size_t default_buffer_size;
    // Largest allowed individual allocation, or 0 to create arbitrarily
    // perfectly sized buffers
    const size_t max_allocation;
    // How many containers can be active concurrently
    const size_t max_containers;
    std::atomic<size_t> created{0};
    std::atomic<size_t> waited{0};
    std::atomic<size_t> contention{0};
    std::atomic<size_t> sorted{0};
    struct Slot {
      std::atomic<Container*> container{nullptr};
      uint8_t padding[64 - sizeof(std::atomic<Container*>)];
    };
    std::array<Slot, n_slots> slots;
    std::mutex pool_lock;
    std::vector<std::unique_ptr<Container>> pool;
    ConcurrentStringStorage(size_t default_buffer_size,
                            size_t max_allocation,
                            size_t max_containers)
        : default_buffer_size(default_buffer_size),
          max_allocation(max_allocation),
          max_containers(std::max(max_containers, n_slots)) {}
    Context get_context();
    Stats get_stats() const;
    ~ConcurrentStringStorage() {
      for (auto& slot : slots) {
        delete slot.container.load();
      }
    }
  };

  // Hashing is expensive on large strings (long Java type names, string
  // literals), so we avoid using `UnorderedMap` directly.
  //
  // For leaf-level storage we use `std::set` (i.e., a tree). In a sparse
  // string keyset with large keys this performs better as only the suffix
  // until first change needs to be compared.
  //
  // For sharding, we use two layers. The first layer is a partial string
  // hash as defined by `TruncatedStringHash`. It picks a segment "close"
  // to the front and performs reasonably well. A std::array is used for
  // sharding here (see `LargeStringMap`).
  //
  // The second layer optimizes the string comparison. We have additional
  // data besides the string data pointer, namely the UTF size. We can
  // avoid comparisons for different string lengths. The second layer
  // thus shards over it. We use the `ConcurrentContainer` sharding for
  // this (see `ConcurrentProjectedStringSet`).
  //
  // The two layers give infrastructure overhead, however, the base size
  // of a `std::set` and `ConcurrentContainer` is quite small.
  //
  // We use `const DexString*` for the keys, however, we have to be careful not
  // to assume that the referenced `const char*` data is zero-terminated.
  using StringSetKey = const DexString*;
  struct StringSetKeyHash {
    size_t operator()(StringSetKey k) const;
  };
  struct StringSetKeyCompare {
    bool operator()(StringSetKey a, StringSetKey b) const;
  };

  template <size_t n_slots = 31>
  class ConcurrentProjectedStringSet {
    std::array<std::set<StringSetKey, StringSetKeyCompare>, n_slots> m_slots;
    mutable std::array<std::mutex, n_slots> m_locks;

   public:
    const StringSetKey* get(StringSetKey str) const {
      size_t i = StringSetKeyHash()(str) % n_slots;
      auto& map = m_slots[i];
      std::lock_guard<std::mutex> lock(m_locks[i]);
      auto it = map.find(str);
      return it == map.end() ? nullptr : &*it;
    }

    std::pair<const StringSetKey*, bool> insert(StringSetKey str) {
      size_t i = StringSetKeyHash()(str) % n_slots;
      auto& map = m_slots[i];
      std::lock_guard<std::mutex> lock(m_locks[i]);
      auto [it, emplaced] = map.emplace(str);
      return std::make_pair(&*it, emplaced);
    }

    size_t size() const {
      size_t res = 0;
      for (auto& set : m_slots) {
        res += set.size();
      }
      return res;
    }

    void release() {
      for (auto& set : m_slots) {
        for (auto* s : set) {
          delete s;
        }
        set.clear();
      }
    }
  };

  template <size_t n_slots, size_t m_slots>
  struct LargeStringSet {
    using AType = std::array<ConcurrentProjectedStringSet<n_slots>, m_slots>;

    AType sets;

    ConcurrentProjectedStringSet<n_slots>& at(StringSetKey k) {
      size_t hashed = TruncatedStringHash()(k) % m_slots;
      return sets[hashed];
    }

    typename AType::iterator begin() { return sets.begin(); }
    typename AType::iterator end() { return sets.end(); }

    size_t slots() const { return sets.size(); }
  };

  // Hash a 32-byte subsequence of a given string, offset by 32 bytes from the
  // start. Dex files tend to contain many strings with the same prefixes,
  // because every class / method under a given package will share the same
  // prefix. The offset ensures that we have more unique subsequences to hash.
  //
  // An offset of 32 and hash prefix length of 32 seemed to perform best on the
  // typical strings in an android app. It's important to remain within one
  // cache line (offset + hash_prefix_len <= 64) and hash enough of the string
  // to minimize the chance of duplicate sections
  struct TruncatedStringHash {
    size_t operator()(StringSetKey k);
  };

  struct DexStringReprHash {
    size_t operator()(const DexStringRepr& k) const;
  };
  struct DexStringReprEqual {
    bool operator()(const DexStringRepr& a, const DexStringRepr& b) const;
  };

  // DexString
  LargeStringSet<31, 127> s_large_string_set;
  std::array<InsertOnlyConcurrentSet<DexStringRepr,
                                     DexStringReprHash,
                                     DexStringReprEqual>*,
             128>
      s_small_string_set;

  // We maintain three kinds of raw string storage
  ConcurrentStringStorage s_small_string_storage;
  ConcurrentStringStorage s_medium_string_storage;
  ConcurrentStringStorage s_large_string_storage;

  char* store_string(std::string_view);

  // DexType
  AtomicMap<const DexString*, DexType*> s_type_map;

  // DexFieldRef
  AtomicMap<DexFieldSpec, DexFieldRef*> s_field_map;
  std::mutex s_field_lock;

  // DexTypeList
  struct DexTypeListContainerTypePtrHash {
    size_t operator()(const DexTypeListContainerType* d) const {
      return boost::hash<DexTypeListContainerType>()(*d);
    }
  };
  struct DexTypeListContainerTypePtrEquals {
    size_t operator()(const DexTypeListContainerType* lhs,
                      const DexTypeListContainerType* rhs) const {
      return static_cast<size_t>(lhs == rhs || *lhs == *rhs);
    }
  };
  AtomicMap<const DexTypeListContainerType*,
            DexTypeList*,
            DexTypeListContainerTypePtrHash,
            DexTypeListContainerTypePtrEquals>
      s_typelist_map;

  // DexProto
  struct DexProtoKeyHash {
    size_t operator()(DexProto* k) const;
  };
  struct DexProtoKeyEqual {
    bool operator()(DexProto* a, DexProto* b) const;
  };
  InsertOnlyConcurrentSet<DexProto*, DexProtoKeyHash, DexProtoKeyEqual>
      s_proto_set;

  // DexMethod
  AtomicMap<DexMethodSpec, DexMethodRef*> s_method_map;
  std::mutex s_method_lock;

  // DexLocation
  using ClassLocationKey = std::pair<std::string_view, std::string_view>;
  struct ClassLocationKeyHash {
    size_t operator()(const ClassLocationKey& k) const {
      return std::hash<std::string_view>()(k.second);
    }
  };
  AtomicMap<ClassLocationKey, DexLocation*, ClassLocationKeyHash>
      s_location_map;

  // DexPositionSwitch and DexPositionPattern
  PositionPatternSwitchManager* m_position_pattern_switch_manager{nullptr};

  // Type-to-class map
  InsertOnlyConcurrentSet<DexClass*> m_classes;
  std::mutex m_external_classes_mutex;
  std::vector<DexClass*> m_external_classes;

  // DexCallSite / DexMethodHandle, owned (not interned) so teardown can free
  // them; see publish_callsite/publish_methodhandle.
  InsertOnlyConcurrentSet<DexCallSite*> m_callsites;
  InsertOnlyConcurrentSet<DexMethodHandle*> m_methodhandles;

  const std::vector<const DexType*> m_empty_types;

  // These functions will be called when ~RedexContext() is called
  std::mutex m_destruction_tasks_lock;
  std::vector<Task> m_destruction_tasks;

  UnorderedMap<std::string, size_t> m_sb_interaction_indices;

  bool m_allow_class_duplicates;

  std::atomic<bool> m_pointers_cache_loaded{false};
  std::mutex m_pointers_cache_lock;
  FrequentlyUsedPointers m_pointers_cache;

  // Field values map specified by Proguard assume value
  ConcurrentMap<DexField*, std::unique_ptr<keep_rules::AssumeReturnValue>>
      field_values;
  // Return values map specified by Proguard assume value
  ConcurrentMap<DexMethod*, std::unique_ptr<keep_rules::AssumeReturnValue>>
      method_return_values;

  bool m_ordering_changes_allowed{true};

  std::atomic<size_t> m_leaked_methods_count{0};
};
