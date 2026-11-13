/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "RedexContext.h"

#include <boost/algorithm/string.hpp>
#include <boost/thread/thread.hpp> // NOLINT
#include <mutex>
#include <regex>
#include <sstream>

#include "Debug.h"
#include "DexCallSite.h"
#include "DexClass.h"
#include "DexMethodHandle.h"
#include "DexPosition.h"
#include "DuplicateClasses.h"
#include "KeepReason.h"
#include "ProguardConfiguration.h"
#include "Sanitizers.h"
#include "Show.h"
#include "Timer.h"
#include "Trace.h"
#include "WorkQueue.h"

static_assert(std::is_same<DexTypeList::ContainerType,
                           RedexContext::DexTypeListContainerType>::value);

RedexContext* g_redex;

RedexContext::RedexContext(bool allow_class_duplicates)
    : s_small_string_storage{16384, 111,
                             boost::thread::hardware_concurrency() / 2},
      s_medium_string_storage{65536, 2000,
                              boost::thread::hardware_concurrency() / 4},
      s_large_string_storage{0, 0, boost::thread::hardware_concurrency()},
      m_allow_class_duplicates(allow_class_duplicates) {
  for (size_t i = 0; i < s_small_string_set.size(); ++i) {
    s_small_string_set[i] =
        new InsertOnlyConcurrentSet<DexStringRepr, DexStringReprHash,
                                    DexStringReprEqual>();
  }
}

// NOLINTNEXTLINE(bugprone-exception-escape)
RedexContext::~RedexContext() {
  // We parallelize destruction for efficiency.
  auto parallel_run = [](const std::vector<std::function<void()>>& fns,
                         const char* timer_name) {
    if (timer_name != nullptr) {
      Timer timer(timer_name, /*indent=*/false);
      workqueue_run<std::function<void()>>(
          [](const std::function<void()>& fn) { fn(); }, fns);
    } else {
      workqueue_run<std::function<void()>>(
          [](const std::function<void()>& fn) { fn(); }, fns);
    }
  };

  size_t small_strings_size = 0;
  size_t large_strings_size = 0;

  parallel_run({[&] {
                  Timer timer("Delete DexTypes", /* indent */ false);
                  // NB: This table intentionally contains aliases (multiple
                  // DexStrings map to the same DexType), so we have to dedup
                  // the set of types before deleting to avoid double-frees.
                  UnorderedSet<DexType*> delete_types;
                  for (auto const& p : UnorderedIterable(s_type_map)) {
                    if (delete_types.emplace(p.second).second) {
                      delete p.second;
                    }
                  }
                  s_type_map.clear();
                },
                [&] {
                  Timer timer("Delete DexTypeLists", /* indent */ false);
                  for (auto const& p : UnorderedIterable(s_typelist_map)) {
                    delete p.second;
                  }
                  s_typelist_map.clear();
                },
                [&] {
                  Timer timer("Delete DexProtos", /* indent */ false);
                  for (auto* proto : UnorderedIterable(s_proto_set)) {
                    delete proto;
                  }
                  s_proto_set.clear();
                },
                [&] {
                  Timer timer("Delete DexClasses", /* indent */ false);
                  for (auto* cls : UnorderedIterable(m_classes)) {
                    delete cls;
                  }
                  m_classes.clear();
                },
                [&] {
                  Timer timer("Delete DexLocations", /* indent */ false);
                  for (auto const& p : UnorderedIterable(s_location_map)) {
                    delete p.second;
                  }
                  s_location_map.clear();
                },
                [&] {
                  Timer timer("m_destruction_tasks", /* indent */ false);
                  for (const Task& t : m_destruction_tasks) {
                    t();
                  }
                  m_destruction_tasks.clear();
                },
                [&] {
                  Timer timer("delete m_position_pattern_switch_manager",
                              /* indent */ false);
                  delete m_position_pattern_switch_manager;
                },
                [&] {
                  Timer timer("misc", /* indent */ false);
                  m_external_classes.clear();
                  field_values.clear();
                  method_return_values.clear();
                }},
               nullptr);

  // Deleting fields and methods is especially expensive, so we do it by
  // "buckets". For timer clarity we do them serially, even if we could
  // save a little bit of time.
  parallel_run(
      [&]() {
        const size_t method_buckets_count = 16;
        std::vector<std::function<void()>> fns;
        fns.reserve(method_buckets_count);
        for (size_t bucket = 0; bucket < method_buckets_count; bucket++) {
          fns.emplace_back([bucket, this]() {
            // Delete DexMethods. Use set to prevent double freeing aliases
            UnorderedSet<DexMethod*> delete_methods;
            for (auto&& [_, loc] : UnorderedIterable(s_method_map)) {
              // Check bucket using the base pointer before downcasting,
              // to avoid reading a potentially freed object's vptr
              // (another bucket thread may have already deleted it).
              auto* ref = loc.load();
              if ((reinterpret_cast<size_t>(ref) >> 16) %
                      method_buckets_count !=
                  bucket) {
                continue;
              }
              // NOLINTNEXTLINE(cppcoreguidelines-pro-type-static-cast-downcast)
              auto* method = static_cast<DexMethod*>(ref);
              if (delete_methods.emplace(method).second) {
                delete method;
              }
            }
          });
        }
        return fns;
      }(),
      "Delete DexMethods");

  parallel_run(
      [&]() {
        const size_t field_buckets_count = 4;
        std::vector<std::function<void()>> fns;
        fns.reserve(field_buckets_count);
        for (size_t bucket = 0; bucket < field_buckets_count; bucket++) {
          fns.emplace_back([bucket, this]() {
            // Delete DexFields. Use set to prevent double freeing aliases
            UnorderedSet<DexField*> delete_fields;
            for (auto&& [_, loc] : UnorderedIterable(s_field_map)) {
              // Check bucket using the base pointer before downcasting,
              // to avoid reading a potentially freed object's vptr
              // (another bucket thread may have already deleted it).
              auto* ref = loc.load();
              if ((reinterpret_cast<size_t>(ref) >> 16) % field_buckets_count !=
                  bucket) {
                continue;
              }
              // NOLINTNEXTLINE(cppcoreguidelines-pro-type-static-cast-downcast)
              auto* field = static_cast<DexField*>(ref);
              if (delete_fields.emplace(field).second) {
                delete field;
              }
            }
          });
        }
        return fns;
      }(),
      "Delete DexFields");

  // Must run after all DexClass/DexMethod/DexField deletion above: each
  // ReferencedState holds non-owning const Reason* aliases into s_keep_reasons,
  // and release_keep_reasons() deletes the pointed-to Reasons. Freeing them
  // earlier would leave those still-live holders dangling.
  {
    Timer timer("release_keep_reasons", /* indent */ false);
    keep_reason::Reason::release_keep_reasons();
  }

  // Same ordering requirement as release_keep_reasons above: DexCallSite and
  // DexMethodHandle are referenced by non-owning raw pointers from the IR
  // (IRInstruction / DexOpcode*), from DexCallSite's linker method handle, and
  // from DexEncodedValueMethodHandle. Delete them only after every such holder
  // (DexClass/DexMethod/DexField and their IRCode) is already gone.
  {
    Timer timer("Delete DexCallSites and DexMethodHandles", /* indent */ false);
    for (auto* callsite : UnorderedIterable(m_callsites)) {
      delete callsite;
    }
    m_callsites.clear();
    for (auto* methodhandle : UnorderedIterable(m_methodhandles)) {
      delete methodhandle;
    }
    m_methodhandles.clear();
  }

  parallel_run(
      [&]() {
        std::vector<std::function<void()>> fns;
        fns.reserve(s_small_string_set.size() + s_large_string_set.slots());
        for (size_t i = 0; i < s_small_string_set.size(); ++i) {
          auto* small_string_set = s_small_string_set[i];
          small_strings_size += small_string_set->size();
          fns.emplace_back([small_string_set]() {
            small_string_set->clear();
            delete small_string_set;
          });
        }
        for (auto& segment : s_large_string_set) {
          large_strings_size += segment.size();
          fns.emplace_back([&segment]() { segment.release(); });
        }
        return fns;
      }(),
      "Delete DexStrings");

  s_method_map.clear();

  std::ostringstream oss;
  auto log_stats = [&oss](auto* name, ConcurrentStringStorage& storage) {
    auto stats = storage.get_stats();
    oss << "\n  " << name << ": " << stats.containers << " containers with "
        << stats.buffers << " buffers, " << stats.used << " / "
        << stats.allocated << " bytes used / allocated ("
        << (stats.allocated == 0 ? 100 : (100 * stats.used / stats.allocated))
        << "%%), " << stats.waited << " / " << stats.contention
        << " times waited / contended, " << stats.sorted << " times sorted";
  };
  log_stats("small", s_small_string_storage);
  log_stats("medium", s_medium_string_storage);
  log_stats("large", s_large_string_storage);
  TRACE(PM, 1,
        "String storage of %zu + %zu strings @ %u hardware concurrency:%s",
        small_strings_size, large_strings_size,
        boost::thread::hardware_concurrency(), oss.str().c_str());
}

/*
 * Try and insert :key into :container. This insertion may fail if
 * another thread has already inserted that key. In that case, return the
 * existing value and discard the one we were trying to insert.
 */
template <class Key, class Deleter = std::default_delete<Key>, class Container>
static const Key* const* try_insert(std::unique_ptr<Key, Deleter> key,
                                    Container* container) {
  auto [rv_ptr, inserted] = container->insert(key.get());
  if (inserted) {
    (void)key.release();
  }
  return rv_ptr;
}

/*
 * Try and insert (:key, :value) into :container. This insertion may fail if
 * another thread has already inserted that key. In that case, return the
 * existing value and discard the one we were trying to insert.
 *
 * We distinguish between the types of the inserted and stored values to handle
 * DexFields and DexMethods, where we upcast the inserted value into a
 * DexFieldRef / DexMethodRef respectively when storing it.
 */
template <class InsertValue,
          class StoredValue = InsertValue,
          class Deleter = std::default_delete<InsertValue>,
          class Key,
          class Container>
static StoredValue* try_insert(Key key,
                               std::unique_ptr<InsertValue, Deleter> value,
                               Container* container) {
  auto [ptr, success] = container->emplace(key, value.get());
  if (success) {
    return value.release();
  }
  return ptr->load();
}

RedexContext::ConcurrentStringStorage::Container::~Container() {
  for (const auto* p = buffer; p != nullptr;) {
    const auto* next = p->next;
    delete p;
    p = next;
  }
}

char* RedexContext::ConcurrentStringStorage::Container::allocate(
    size_t length) {
  if (buffer == nullptr || buffer->used + length > buffer->allocated) {
    buffer = new Buffer(default_size == 0 ? length : default_size, buffer);
  }
  auto* storage = buffer->chars.get() + buffer->used;
  buffer->used += length;
  return storage;
}

RedexContext::ConcurrentStringStorage::Context
RedexContext::ConcurrentStringStorage::get_context() {
#if !IS_WINDOWS
  static std::atomic<size_t> next_index = 0;
  thread_local size_t index_plus_1 = 0;
  if (index_plus_1 == 0) {
    index_plus_1 = (next_index++ % n_slots) + 1;
  }
  size_t index = index_plus_1 - 1;
#else
  size_t index = 0;
#endif

  while (true) {
    auto* string_storage = slots[index].container.exchange(nullptr);
    if (string_storage != nullptr) {
      std::atomic_thread_fence(std::memory_order_acquire);
      return {this, index, string_storage};
    }
    contention++;
    std::lock_guard<std::mutex> mutex(pool_lock);
    if (!pool.empty()) {
      string_storage = pool.back().release();
      pool.pop_back();
      return {this, index, string_storage};
    }
    if (created.fetch_add(1) < max_containers) {
      contention--;
      // add one more
      return {this, index, new Container(default_buffer_size)};
    }
    created.fetch_sub(1);
    // we know we just have to wait, so spin until we get something
    waited++;
#if !IS_WINDOWS
    // Apparently we are fighting against some other thread; move on to next
    // slot to reduce fighting odds
    index_plus_1 = (next_index++ % n_slots) + 1;
    index = index_plus_1 - 1;
#else
    index = (index + 1) % n_slots;
#endif
  }
}

RedexContext::ConcurrentStringStorage::Stats
RedexContext::ConcurrentStringStorage::get_stats() const {
  Stats stats;
  stats.waited = waited.load();
  stats.contention = contention.load();
  stats.sorted = sorted.load();
  auto add = [&stats](auto* storage) {
    if (!storage) {
      return;
    }
    for (const auto* p = storage->buffer; p; p = p->next) {
      stats.allocated += p->allocated;
      stats.used += p->used;
      stats.buffers++;
    }
    stats.containers++;
  };
  for (const auto& slot : slots) {
    add(slot.container.load());
  }
  for (const auto& storage : pool) {
    add(storage.get());
  }
  return stats;
}

RedexContext::ConcurrentStringStorage::Context::~Context() {
  auto* other_container = owner->slots[index].container.exchange(container);
  if (other_container == nullptr) {
    std::atomic_thread_fence(std::memory_order_release);
    return;
  }
  std::lock_guard<std::mutex> mutex(owner->pool_lock);
  auto& owner_pool = owner->pool;
  owner_pool.emplace_back(other_container);
  if (other_container->buffer->remaining() < owner->max_allocation &&
      owner_pool.size() >= 2) {
    owner->sorted++;
    std::sort(owner_pool.begin(), owner_pool.end(), [](auto& a, auto& b) {
      return a->buffer->remaining() < b->buffer->remaining();
    });
  }
}

char* RedexContext::store_string(std::string_view str) {
  ConcurrentStringStorage& concurrent_string_storage =
      str.length() < s_small_string_storage.max_allocation
          ? s_small_string_storage
      : str.length() < s_medium_string_storage.max_allocation
          ? s_medium_string_storage
          : s_large_string_storage;

  char* storage;
  {
    auto storage_context = concurrent_string_storage.get_context();

    // Note that DexStrings are keyed by a string_view created from the actual
    // storage. The string_view is valid until the storage is destroyed.
    storage = storage_context.container->allocate(str.length() + 1);
  }
  memcpy(storage, str.data(), str.length());
  storage[str.length()] = 0;
  return storage;
}

const DexString* RedexContext::make_string(std::string_view str) {
  auto mutf8_next_cp = [](const char*& s) -> uint32_t {
    uint8_t v = *s++;
    /* Simple common case first, a utf8 char... */
    if ((v & 0x80) == 0) {
      return v;
    }
    uint8_t v2 = *s++;
    always_assert_type_log((v2 & 0xc0) == 0x80, INVALID_DEX,
                           "Invalid 2nd byte on mutf8 string");
    /* Two byte code point */
    if ((v & 0xe0) == 0xc0) {
      return (v & 0x1f) << 6 | (v2 & 0x3f);
    }
    /* Three byte code point */
    always_assert_type_log((v & 0xf0) == 0xe0, INVALID_DEX,
                           "Invalid size encoding mutf8 string");
    uint8_t v3 = *s++;
    always_assert_type_log((v3 & 0xc0) == 0x80, INVALID_DEX,
                           "Invalid 3rd byte on mutf8 string");
    return (v & 0x1f) << 12 | (v2 & 0x3f) << 6 | (v3 & 0x3f);
  };

  auto length_of_utf8_string = [&](const char* s) -> uint32_t {
    if (s == nullptr) {
      return 0;
    }
    uint32_t len = 0;
    while (*s != '\0') {
      ++len;
      mutf8_next_cp(s);
    }
    return len;
  };

  // We are creating a DexString key that is just "defined enough" to be used as
  // a key into our string set. The provided string does not have to be zero
  // terminated, and we won't compute the utf size, as neither is needed for
  // this purpose.
  uint32_t dummy_utfsize{0};
  DexStringRepr repr{str.data(), (uint32_t)str.size(), dummy_utfsize};
  if (str.size() < s_small_string_set.size()) {
    const auto* rv_ptr = s_small_string_set[str.size()]->get(repr);
    if (rv_ptr != nullptr) {
      return reinterpret_cast<const DexString*>(rv_ptr);
    }
    char* storage = store_string(str);
    uint32_t utfsize = length_of_utf8_string(storage);
    return reinterpret_cast<const DexString*>(
        s_small_string_set[str.size()]
            ->insert(DexStringRepr{storage, (uint32_t)str.length(), utfsize})
            .first);
    // If unsuccessful, we have wasted a bit of string storage. Oh well...
  }

  const auto* key = reinterpret_cast<const DexString*>(&repr);
  auto& segment = s_large_string_set.at(key);
  const auto* rv_ptr = segment.get(key);
  if (rv_ptr != nullptr) {
    return *rv_ptr;
  }
  char* storage = store_string(str);
  uint32_t utfsize = length_of_utf8_string(storage);
  std::unique_ptr<DexString> string(
      new DexString(storage, str.length(), utfsize));
  return *try_insert(std::move(string), &segment);
  // If unsuccessful, we have wasted a bit of string storage. Oh well...
}

size_t RedexContext::StringSetKeyHash::operator()(StringSetKey k) const {
  return k->size();
}

bool RedexContext::StringSetKeyCompare::operator()(StringSetKey a,
                                                   StringSetKey b) const {
  if (a->size() != b->size()) {
    return a->size() < b->size();
  }
  return memcmp(a->c_str(), b->c_str(), a->size()) < 0;
}

size_t RedexContext::TruncatedStringHash::operator()(StringSetKey k) {
  const char* s = k->c_str();
  uint32_t string_size = k->size();
  constexpr size_t hash_prefix_len = 32;
  constexpr size_t offset = 32;
  size_t len = std::min<size_t>(string_size, offset + hash_prefix_len);
  size_t start = std::max<int64_t>(0, int64_t(len - hash_prefix_len));
  return boost::hash_range(s + start, s + len);
}

size_t RedexContext::DexStringReprHash::operator()(
    const DexStringRepr& k) const {
  return boost::hash_range(k.storage, k.storage + k.length);
}

bool RedexContext::DexStringReprEqual::operator()(
    const DexStringRepr& a, const DexStringRepr& b) const {
  if (a.length != b.length) {
    return false;
  }
  return memcmp(a.storage, b.storage, a.length) == 0;
}

const DexString* RedexContext::get_string(std::string_view str) {
  uint32_t dummy_utfsize{0};
  DexStringRepr repr{str.data(), (uint32_t)str.size(), dummy_utfsize};
  if (str.size() < s_small_string_set.size()) {
    return reinterpret_cast<const DexString*>(
        s_small_string_set[str.size()]->get(repr));
  }

  const auto* key = reinterpret_cast<const DexString*>(&repr);
  const auto& segment = s_large_string_set.at(key);
  const auto* rv_ptr = segment.get(key);
  return rv_ptr == nullptr ? nullptr : *rv_ptr;
}

DexType* RedexContext::make_type(const DexString* dstring) {
  always_assert(dstring != nullptr);
  auto* rv = s_type_map.load(dstring, nullptr);
  if (rv != nullptr) {
    return rv;
  }
  std::unique_ptr<DexType> type(new DexType(dstring));
  return try_insert(dstring, std::move(type), &s_type_map);
}

DexType* RedexContext::get_type(const DexString* dstring) {
  if (dstring == nullptr) {
    return nullptr;
  }
  return s_type_map.load(dstring, nullptr);
}

void RedexContext::set_type_name(DexType* type, const DexString* new_name) {
  alias_type_name(type, new_name);
  type->m_name = new_name;
}

void RedexContext::alias_type_name(DexType* type, const DexString* new_name) {
  always_assert_log(
      !s_type_map.count(new_name),
      "Bailing, attempting to alias a symbol that already exists! '%s'\n",
      new_name->c_str());
  s_type_map.emplace(new_name, type);
}

void RedexContext::remove_type_name(const DexString* name) {
  s_type_map.erase(name);
}

void RedexContext::walk_types(const std::function<void(DexType*)>& walker) {
  for (auto const& [name, atomic_type] : UnorderedIterable(s_type_map)) {
    DexType* type = atomic_type.load();
    // A type's current name is never removed from the map, so this visits
    // each type exactly once and skips its aliases.
    if (type->get_name() == name) {
      walker(type);
    }
  }
}

DexFieldRef* RedexContext::make_field(const DexType* container,
                                      const DexString* name,
                                      const DexType* type) {
  always_assert(container != nullptr && name != nullptr && type != nullptr);
  DexFieldSpec r(container->to_mutable(), name, type->to_mutable());
  auto* rv = s_field_map.load(r, nullptr);
  if (rv != nullptr) {
    return rv;
  }
  std::unique_ptr<DexField, DexField::Deleter> field(
      new DexField(container->to_mutable(), name, type->to_mutable()));
  return try_insert<DexField, DexFieldRef>(r, std::move(field), &s_field_map);
}

DexFieldRef* RedexContext::get_field(const DexType* container,
                                     const DexString* name,
                                     const DexType* type) {
  if (container == nullptr || name == nullptr || type == nullptr) {
    return nullptr;
  }
  DexFieldSpec r(const_cast<DexType*>(container), name,
                 const_cast<DexType*>(type));
  return s_field_map.load(r, nullptr);
}

void RedexContext::alias_field_name(DexFieldRef* field,
                                    const DexString* new_name) {
  DexFieldSpec r(field->m_spec.cls, new_name, field->m_spec.type);
  always_assert_log(
      !s_field_map.count(r),
      "Bailing, attempting to alias a symbol that already exists! '%s'\n",
      new_name->c_str());
  s_field_map.emplace(r, field);
}

void RedexContext::erase_field(DexFieldRef* field) {
  s_field_map.erase(field->m_spec);
  if (field->is_def()) {
    unset_field_value(field->as_def());
  }
}

void RedexContext::erase_field(const DexType* container,
                               const DexString* name,
                               const DexType* type) {
  DexFieldSpec r(const_cast<DexType*>(container), name,
                 const_cast<DexType*>(type));
  auto* f = s_field_map.load(r, nullptr);
  s_field_map.erase(r);
  if (f != nullptr && f->is_def()) {
    unset_field_value(f->as_def());
  }
}

void RedexContext::mutate_field(DexFieldRef* field,
                                const DexFieldSpec& ref,
                                bool rename_on_collision) {
  std::lock_guard<std::mutex> lock(s_field_lock);
  DexFieldSpec& r = field->m_spec;
  s_field_map.erase(r);
  r.cls = ref.cls != nullptr ? ref.cls : field->m_spec.cls;
  r.name = ref.name != nullptr ? ref.name : field->m_spec.name;
  r.type = ref.type != nullptr ? ref.type : field->m_spec.type;
  field->m_spec = r;

  if (rename_on_collision && (s_field_map.count(r) != 0u)) {
    uint32_t i = 0;
    while (true) {
      r.name = DexString::make_string("f$" + std::to_string(i++));
      if (s_field_map.count(r) == 0u) {
        break;
      }
    }
  }
  always_assert_log(!s_field_map.count(r),
                    "Another field with the same signature already exists %s",
                    SHOW(s_field_map.load(r)));
  s_field_map.emplace(r, field);
}

DexTypeList* RedexContext::make_type_list(
    RedexContext::DexTypeListContainerType&& p) {
  auto* rv = s_typelist_map.load(&p, nullptr);
  if (rv != nullptr) {
    return rv;
  }
  std::unique_ptr<DexTypeList> typelist(new DexTypeList(std::move(p)));
  const auto* key = &typelist->m_list;
  return try_insert(key, std::move(typelist), &s_typelist_map);
}

DexTypeList* RedexContext::get_type_list(
    const RedexContext::DexTypeListContainerType& p) {
  return s_typelist_map.load(&p, nullptr);
}

size_t RedexContext::DexProtoKeyHash::operator()(DexProto* k) const {
  return (size_t)k->get_rtype() ^ (size_t)k->get_args();
}
bool RedexContext::DexProtoKeyEqual::operator()(DexProto* a,
                                                DexProto* b) const {
  return a->get_rtype() == b->get_rtype() && a->get_args() == b->get_args();
}

DexProto* RedexContext::make_proto(const DexType* rtype,
                                   const DexTypeList* args,
                                   const DexString* shorty) {
  always_assert(rtype != nullptr && args != nullptr && shorty != nullptr);
  DexProto key(const_cast<DexType*>(rtype), const_cast<DexTypeList*>(args),
               nullptr);
  const auto* rv_ptr = s_proto_set.get(&key);
  if (rv_ptr != nullptr) {
    return const_cast<DexProto*>(*rv_ptr);
  }
  std::unique_ptr<DexProto> proto(new DexProto(
      const_cast<DexType*>(rtype), const_cast<DexTypeList*>(args), shorty));
  return const_cast<DexProto*>(*try_insert(std::move(proto), &s_proto_set));
}

DexProto* RedexContext::get_proto(const DexType* rtype,
                                  const DexTypeList* args) {
  if (rtype == nullptr || args == nullptr) {
    return nullptr;
  }
  DexProto key(const_cast<DexType*>(rtype), const_cast<DexTypeList*>(args),
               nullptr);
  const auto* rv_ptr = s_proto_set.get(&key);
  return rv_ptr == nullptr ? nullptr : const_cast<DexProto*>(*rv_ptr);
}

DexMethodRef* RedexContext::make_method(const DexType* type_,
                                        const DexString* name_,
                                        const DexProto* proto_) {
  // Ideally, DexMethodSpec would store const types, then these casts wouldn't
  // be necessary, but that would involve cleaning up quite a bit of existing
  // code.
  auto* type = const_cast<DexType*>(type_);
  const auto* name = name_;
  auto* proto = const_cast<DexProto*>(proto_);
  always_assert(type != nullptr && name != nullptr && proto != nullptr);
  DexMethodSpec r(type, name, proto);
  auto* rv = s_method_map.load(r, nullptr);
  if (rv != nullptr) {
    return rv;
  }
  std::unique_ptr<DexMethod, DexMethod::Deleter> method(
      new DexMethod(type, name, proto));
  return try_insert<DexMethod, DexMethodRef>(r, std::move(method),
                                             &s_method_map);
}

DexMethodRef* RedexContext::get_method(const DexType* type,
                                       const DexString* name,
                                       const DexProto* proto) {
  if (type == nullptr || name == nullptr || proto == nullptr) {
    return nullptr;
  }
  DexMethodSpec r(const_cast<DexType*>(type), name,
                  const_cast<DexProto*>(proto));
  return s_method_map.load(r, nullptr);
}

UnorderedMap<std::string, UnorderedMap<std::string, DexMethodRef*>>
RedexContext::get_baseline_profile_method_map(
    std::unordered_set<DexMethodRef*>& parsed_methods) {
  auto baseline_profile_method_map =
      UnorderedMap<std::string, UnorderedMap<std::string, DexMethodRef*>>();
  for (auto&& [method_spec, method] : UnorderedIterable(s_method_map)) {
    if (parsed_methods.count(method) != 0u) {
      continue;
    }
    std::string descriptor = show_deobfuscated(method);
    boost::replace_all(descriptor, ":(", "(");
    std::vector<std::string> class_and_method;
    boost::split(class_and_method, descriptor, boost::is_any_of("."));
    always_assert(class_and_method.size() == 2);
    baseline_profile_method_map[class_and_method[0]][class_and_method[1]] =
        method;
    parsed_methods.emplace(method);
  }
  return baseline_profile_method_map;
}

void RedexContext::alias_method_name(DexMethodRef* method,
                                     const DexString* new_name) {
  DexMethodSpec r(method->m_spec.cls, new_name, method->m_spec.proto);
  always_assert_log(
      !s_method_map.count(r),
      "Bailing, attempting to alias a symbol that already exists! '%s'\n",
      new_name->c_str());
  s_method_map.emplace(r, method);
}

void RedexContext::erase_method(DexMethodRef* method) {
  s_method_map.erase(method->m_spec);
  // Also remove the alias from the map
  if (method->is_def()) {
    if (method->DexMethodRef::as_def()->get_deobfuscated_name_or_null() !=
        nullptr) {
      DexMethodSpec r(method->m_spec.cls,
                      &method->DexMethodRef::as_def()->get_deobfuscated_name(),
                      method->m_spec.proto);
      s_method_map.erase(r);
    }
    unset_return_value(method->as_def());
  }
}

void RedexContext::erase_method(const DexType* type,
                                const DexString* name,
                                const DexProto* proto) {
  DexMethodSpec r(const_cast<DexType*>(type), name,
                  const_cast<DexProto*>(proto));
  auto* m = s_method_map.load(r, nullptr);
  s_method_map.erase(r);
  if (m != nullptr && m->is_def()) {
    unset_return_value(m->as_def());
  }
}

void RedexContext::leak_method(DexMethodRef* method) {
  sanitizers::lsan_ignore_object(method);
  m_leaked_methods_count.fetch_add(1, std::memory_order_relaxed);
}

size_t RedexContext::leaked_methods() {
  return m_leaked_methods_count.load(std::memory_order_relaxed);
}

// TODO: Need a better interface.
void RedexContext::mutate_method(DexMethodRef* method,
                                 const DexMethodSpec& new_spec,
                                 bool rename_on_collision) {
  std::lock_guard<std::mutex> lock(s_method_lock);
  DexMethodSpec old_spec = method->m_spec;
  s_method_map.erase(method->m_spec);

  DexMethodSpec& r = method->m_spec;
  r.cls = new_spec.cls != nullptr ? new_spec.cls : method->m_spec.cls;
  r.name = new_spec.name != nullptr ? new_spec.name : method->m_spec.name;
  r.proto = new_spec.proto != nullptr ? new_spec.proto : method->m_spec.proto;

  if ((s_method_map.count(r) != 0u) && rename_on_collision) {
    // Never rename constructors, which causes runtime verification error:
    // "Method 42(Foo;.$init$$0) is marked constructor, but doesn't match name"
    always_assert_log(
        show(r.name) != "<init>" && show(r.name) != "<clinit>",
        "you should not rename constructor on a collision, %s.%s:%s exists",
        SHOW(r.cls), SHOW(r.name), SHOW(r.proto));
    if (new_spec.cls == nullptr || new_spec.cls == old_spec.cls) {
      // Either method prototype or name is going to be changed, and we hit a
      // collision. Make an unique name: "name$[0-9]+". But in case of <clinit>,
      // libdex rejects a name like "<clinit>$1". See:
      // http://androidxref.com/9.0.0_r3/xref/dalvik/libdex/DexUtf.cpp#115
      // Valid characters can be found here: [_a-zA-Z0-9$\-]
      // http://androidxref.com/9.0.0_r3/xref/dalvik/libdex/DexUtf.cpp#50
      // If a method name begins with "<", it must end with ">". We generate a
      // name like "$clinit$$42" by replacing <, > with $.
      uint32_t i = 0;
      std::string prefix;
      if (r.name->str().front() == '<') {
        redex_assert(r.name->str().back() == '>');
        prefix =
            "$" + r.name->str().substr(1, r.name->str().length() - 2) + "$$";
      } else {
        prefix = r.name->str() + "$";
      }
      do {
        r.name = DexString::make_string(prefix + std::to_string(i++));
      } while (s_method_map.count(r) != 0u);
    } else {
      // We are about to change its class. Use a better name to remember its
      // original source class on a collision. Tokenize the class name into
      // parts, and use them until no more collision.
      //
      // "com/facebook/foo/Bar;" => {"com", "facebook", "foo", "Bar"}
      std::string cls_name = show_deobfuscated(old_spec.cls);
      std::regex separator{"[/;]"};
      std::vector<std::string> parts;
      parts.insert(parts.end(),
                   std::sregex_token_iterator(cls_name.begin(), cls_name.end(),
                                              separator, -1),
                   std::sregex_token_iterator());
      // Make a name like "name$Bar$foo", or "$clinit$$Bar$foo".
      std::stringstream ss;
      if (old_spec.name->str().front() == '<') {
        ss << "$"
           << old_spec.name->str().substr(1, old_spec.name->str().length() - 2)
           << "$";
      } else {
        ss << *old_spec.name;
      }
      for (auto part = parts.rbegin(); part != parts.rend(); ++part) {
        ss << "$" << *part;
        r.name = DexString::make_string(ss.str());
        if (s_method_map.count(r) == 0u) {
          break;
        }
      }
    }
  }

  // We might still miss name collision cases. As of now, let's just assert.
  if (s_method_map.count(r) != 0u) {
    always_assert_log(!s_method_map.count(r),
                      "Another method of the same signature already exists %s"
                      " %s %s",
                      SHOW(r.cls), SHOW(r.name), SHOW(r.proto));
  }
  s_method_map.emplace(r, method);
}

DexLocation* RedexContext::make_location(std::string_view store_name,
                                         std::string_view file_name) {
  auto key = std::make_pair(store_name, file_name);
  auto* rv = s_location_map.load(key, nullptr);
  if (rv != nullptr) {
    return rv;
  }
  std::unique_ptr<DexLocation> value(
      new DexLocation(std::string(store_name), std::string(file_name)));
  key = std::make_pair(std::string_view(value->get_store_name()),
                       std::string_view(value->get_file_name()));
  always_assert(key.first.data() == value->get_store_name().data());
  always_assert(key.second.data() == value->get_file_name().data());
  return try_insert(key, std::move(value), &s_location_map);
}

DexLocation* RedexContext::get_location(std::string_view store_name,
                                        std::string_view file_name) {
  auto key = std::make_pair(store_name, file_name);
  return s_location_map.load(key, nullptr);
}

PositionPatternSwitchManager*
RedexContext::get_position_pattern_switch_manager() {
  std::call_once(m_position_pattern_switch_manager_once, [this]() {
    m_position_pattern_switch_manager = new PositionPatternSwitchManager();
  });
  return m_position_pattern_switch_manager;
}

// Return false on unique classes
// Return true on benign duplicate classes
// Throw RedexException on problematic duplicate classes
bool RedexContext::class_already_loaded(DexClass* cls) {
  const DexType* type = cls->get_type();
  auto* prev_cls = type->m_self.load(std::memory_order_acquire);
  if (prev_cls == nullptr) {
    return false;
  } else {
    const auto& prev_loc = prev_cls->get_location()->get_file_name();
    const auto& cur_loc = cls->get_location()->get_file_name();
    if (prev_loc == cur_loc || dup_classes::is_known_dup(cls)) {
      // benign duplicates
      TRACE(MAIN, 1, "Warning: found a duplicate class: %s", SHOW(cls));
    } else {
      const std::string& class_name = show(cls);
      TRACE(MAIN,
            1,
            "Found a duplicate class: %s in two dexes:\ndex 1: %s\ndex "
            "2: %s\n",
            class_name.c_str(),
            prev_loc.c_str(),
            cur_loc.c_str());

      if (!m_allow_class_duplicates) {
        throw RedexException(
            RedexError::DUPLICATE_CLASSES,
            "Found duplicate class in two different files.",
            {{"class", class_name}, {"dex1", prev_loc}, {"dex2", cur_loc}});
      }
    }
    return true;
  }
}

void RedexContext::publish_callsite(DexCallSite* callsite) {
  m_callsites.insert(callsite);
}

void RedexContext::publish_methodhandle(DexMethodHandle* methodhandle) {
  m_methodhandles.insert(methodhandle);
}

void RedexContext::publish_class(DexClass* cls) {
  DexType* type = cls->get_type();
  DexClass* expected = nullptr;
  bool insertion_took_place =
      type->m_self.compare_exchange_strong(expected, cls);
  always_assert_log(insertion_took_place,
                    "No insertion for class: %s with deobfuscated name: %s",
                    cls->get_name()->c_str(),
                    cls->get_deobfuscated_name().c_str());
  m_classes.insert(cls);
  if (cls->is_external()) {
    std::lock_guard<std::mutex> l(m_external_classes_mutex);
    m_external_classes.emplace_back(cls);
  }
}

DexClass* RedexContext::type_class(const DexType* t) const {
  return t != nullptr ? t->m_self.load(std::memory_order_relaxed) : nullptr;
}

DexType* RedexContext::class_type(const DexClass* cls) const {
  return cls != nullptr ? cls->get_type() : nullptr;
}

void RedexContext::set_field_value(DexField* field,
                                   keep_rules::AssumeReturnValue& val) {
  field_values.emplace(field,
                       std::make_unique<keep_rules::AssumeReturnValue>(val));
}

keep_rules::AssumeReturnValue* RedexContext::get_field_value(DexField* field) {
  auto it = field_values.find(field);
  if (it != field_values.end()) {
    return it->second.get();
  }
  return nullptr;
}

void RedexContext::unset_field_value(DexField* field) {
  field_values.erase(field);
}

void RedexContext::set_return_value(DexMethod* method,
                                    keep_rules::AssumeReturnValue& val) {
  method_return_values.emplace(
      method, std::make_unique<keep_rules::AssumeReturnValue>(val));
}

keep_rules::AssumeReturnValue* RedexContext::get_return_value(
    DexMethod* method) {
  auto it = method_return_values.find(method);
  if (it != method_return_values.end()) {
    return it->second.get();
  }
  return nullptr;
}

void RedexContext::unset_return_value(DexMethod* method) {
  method_return_values.erase(method);
}

void RedexContext::add_destruction_task(const Task& t) {
  std::unique_lock<std::mutex> lock{m_destruction_tasks_lock};
  m_destruction_tasks.push_back(t);
}

void RedexContext::set_sb_interaction_index(
    const UnorderedMap<std::string, size_t>& input) {
  m_sb_interaction_indices = input;
}

void RedexContext::compact() {
  // We parallelize destruction for efficiency.
  auto parallel_run = [](const std::vector<std::function<void()>>& fns) {
    workqueue_run<std::function<void()>>(
        [](const std::function<void()>& fn) { fn(); }, fns);
  };

  parallel_run({
      [&] { s_type_map.compact(); },
      [&] { s_field_map.compact(); },
      [&] { s_typelist_map.compact(); },
      [&] { s_proto_set.compact(); },
      [&] { s_method_map.compact(); },
      [&] { s_location_map.compact(); },
      [&] { field_values.compact(); },
      [&] { method_return_values.compact(); },
  });
}
