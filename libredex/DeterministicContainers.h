/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

/*
 * This file defines zero-cost wrappers around std::unordered_map and
 * std::unordered_set that prevent accidental non-deterministic iteration.
 *
 * TODO: Define UnorderedMultiMap.
 * TODO: Replace (virtually) all usages of std::unordered_x with UnorderedX in
 * the codebase.
 *
 * Some std::unordered_map operations technically expose an iterator, but are
 * not typically used in a way that would require full iteration functionality.
 * The functions provided on the unordered collection instead return a fixed
 * iterator that doesn't allow stepping to other elements. This affects the
 * following functions:
 * - `insert()` (and its variants).
 * - `find()`
 * - `erase()`
 * - `end()`
 *
 * There are various global helper functions with the word "unordered" in their
 * names to make it very obvious that they involve operations on (potentially)
 * unordered collections. All uses of these functions should be closely reviewed
 * for potential order dependencies and thus source of non-determinism.
 * - `UnorderedIterable(collection)` exposes iterators (and associated mutation
 *   operations) of an unordered collection. In fact, `UnorderedIterable` can
 *   also forward any other (iterable) collection iterator. This is used by
 *   order- and collection-type-agnostic algorithms such as workqueue_run. (I am
 *   aware that Pascal-casing this function goes against our style guide, but
 *   it's nicely symmetric to common InstructionIterable constructor calls.)
 * - `unordered_any(collection)` is a short-hand version to select an arbitrary
 *   element of a (potentially) unordered collection.
 * - `unordered_accumulate(collection, ...)` provides the same functionality as
 *   `std::accumulate`, except that it works on (potentially) unordered
 *   collections.
 * - `unordered_copy(collection, ...)` / `unordered_copy_if(collection, ...)`
 *   provides the same functionality as `std::copy` / `std::copy_if`, except
 *   that it works on (potentially) unordered collections.
 * - `unordered_count(collection, ...)` / `unordered_count_if(collection, ...)`
 *   provides the same functionality as `std::count` / `std::count_if`, except
 *   that it works on (potentially) unordered collections.
 * - `unordered_erase_if(collection, ...)` provides the same functionality as
 *   `std::erase_if`, except that it works on (potentially) unordered
 *   collections.
 * - `transform(collection, ...)` provides the same functionality as
 *   `std::transform`, except that it works on (potentially) unordered
 *   collections.
 * - `unordered_all_of(collection, ...)` / `unordered_any_of` /
 *   `unordered_all_of` / `unordered_for_each` provide the same functionality as
 *   `std::all_of` / `std::any_of` / `std::none_of` / `std::for_each`, except
 *   that they work on (potentially) unordered collections.
 * - `insert_unordered_iterable(target, source)` allows inserting elements of a
 *   (potentially) unordered source into a target collection.
 *
 * A few additional global functions are provided that realize common operations
 * that use iterators, but don't ultimately rely on their order:
 * - `unordered_to_ordered_keys(collection, compare)`: Returns a vector of all
 *   keys, sorted.
 * - `unordered_to_ordered(collection, compare)`: Returns a vector of all
 *   key-value pairs, sorted by key.
 *
 * The global function `unordered_unsafe_unwrap(collection)` provides the
 * ultimate escape mechanism to expose the raw unordered collection, or simply
 * passes through any other collection. Use at your own risk.
 *
 * The new unordered collection wrapper types don't provide wrappers for all
 * members yet; filling that in is a work-in-progress.
 *
 * TODO: An intention of the design is to largely keep open the option of
 * redefining UnorderedX as std::unordered_x, disabling all UnorderedX
 * specific function overloads, to get back the vanilla performance.
 */

/*
 * Best practices
 *
 * - Use `UnorderedSet` / `UnorderedMap` instead of `std::unordered_set` /
 *   `std::unordered_map`.
 * - Use `UnorderedBag` instead of `std::vector` if the order of the elements
 *   within the vector is non-deterministic.
 * - If you want to iterate over an unordered collection, and you are certain
 *   that the iteration order does not matter to produce ultimately
 *   deterministic results, then use the `UnorderedIterable(...)` wrapper.
 *   Examples:
 *     - `for (auto x : UnorderedIterable(my_unordered_set)) ...`
 *     - `auto&& ui = UnorderedIterable(my_unordered_set);`
 *        `auto it = ui.begin();`
 *        `while (it != ui.end()) ...`
 * - Avoid storing `UnorderedIterable(...)` in a local variable.
 *     - Instead, prefer using any of the `unordered_...` helper functions.
 *     - If you must store the result of `UnorderedIterable(...)` in a local
 *       variable, always use `auto&&` to deal with the possibility that
 *       `UnorderedIterable(...)` returns a reference to the original collection
 *       that you don't want to copy.
 *     - If you must refer to the type of an unordered iterator associated
 *       with a `auto&& ui`, use
 *       `using iterator = std::remove_reference_t<decltype(ui)>::iterator;`
 * - If you need to sort an unordered collection, see if the
 *   `unordered_to_ordered` or `ordered_order_keys` helper functions work for
 *   you.
 */

#pragma once

#include <algorithm>
#include <cerrno>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <iterator>
#include <numeric>
#include <random>
#include <thread>
#include <type_traits>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "Debug.h"
#include "TemplateUtil.h"

// Redex must produce bit-for-bit reproducible APKs: reproducible builds, build
// caching, and verifiable releases all rely on the same input always yielding
// the same output. Iterating a hash container in its incidental order is a
// silent way to break that -- the output can then change from one run to the
// next for no visible reason, surfacing later as a flaky build or a cache miss.
//
// The Unordered* wrappers already force such iteration to be spelled out (via
// UnorderedIterable) so it gets reviewed, but they cannot verify the reviewer's
// "order doesn't matter here" judgment. With REDEX_PERTURB_UNORDERED on
// (CI/debug only), we deliberately scramble that order per container per run,
// so any code that still depends on it diverges and is caught by Redex's
// reproducibility signals in CI -- before it ships. Off by default =>
// byte-identical, zero-cost.
#ifndef REDEX_PERTURB_UNORDERED
#define REDEX_PERTURB_UNORDERED 0
#endif
inline constexpr bool kPerturbUnordered = REDEX_PERTURB_UNORDERED;

namespace det_perturb {
inline uint64_t splitmix64(uint64_t x) {
  x ^= x >> 30;
  x *= 0xbf58476d1ce4e5b9ULL;
  x ^= x >> 27;
  x *= 0x94d049bb133111ebULL;
  x ^= x >> 31;
  return x;
}
// The base seed for a thread's salt counter. When REDEX_PERTURB_SEED is set it
// is used verbatim (strtoull base 0 accepts decimal and 0x-hex) AND the
// thread-id is deliberately dropped, so a single-threaded run reproduces an
// identical salt stream. Otherwise every thread seeds from random_device XOR
// its thread-id for per-run, per-thread variation. Note: even with a fixed seed
// a full run is only best-effort reproducible -- pointer-keyed containers hash
// raw addresses (ASLR/allocator) and parallel walkers draw salts in a
// nondeterministic order. The seed's real value is detection variety plus
// partial, value-keyed reproducibility.
inline uint64_t perturb_base_seed() {
  if (const char* env = std::getenv("REDEX_PERTURB_SEED")) {
    // strtoull returns 0 for unparseable input and does not distinguish that
    // from a literal "0", so a typo would silently pin every thread to seed 0
    // -- a reproducible run that is not the one asked for, which is worse than
    // no seed at all for the debugging this exists to serve. Require the whole
    // string to parse, and say so loudly otherwise rather than guessing.
    char* end = nullptr;
    errno = 0;
    const unsigned long long parsed = std::strtoull(env, &end, 0);
    const bool ok =
        *env != '\0' && end != nullptr && *end == '\0' && errno == 0;
    if (ok) {
      return static_cast<uint64_t>(parsed);
    }
    fprintf(
        stderr,
        "[redex] WARNING: REDEX_PERTURB_SEED=\"%s\" is not a valid integer; "
        "ignoring it and seeding randomly. Runs will NOT be reproducible.\n",
        env);
  }
  return std::random_device{}() ^
         static_cast<uint64_t>(
             std::hash<std::thread::id>{}(std::this_thread::get_id()));
}

// Per-container salt from a thread_local splitmix64 counter (~0.7ns/draw, no
// large RNG state). Only ever called when perturbation is enabled.
inline uint64_t new_salt() {
  // The per-thread counter is intentional: an inline function's thread_local
  // has one instance per thread across all TUs ([dcl.fct.spec]), which is
  // exactly the reproducible per-thread salt stream we want.
  // NOLINTNEXTLINE(facebook-hte-InlinedStaticLocalVariableWarning)
  thread_local uint64_t state = perturb_base_seed();
  state += 0x9e3779b97f4a7c15ULL;
  return splitmix64(state);
}

} // namespace det_perturb

// A hasher that salts and avalanche-mixes the underlying hash. The salt is
// drawn once at construction and is read-only afterwards, so it is safe to hash
// on any thread. operator() MUST be noexcept: libstdc++ caches hash codes for
// non-noexcept hashers, and a code cached under one container's salt would make
// cross-container operator== (which re-buckets into the other container)
// spuriously report inequality.
template <class Hash>
struct PerturbHasher {
  Hash base{};
  uint64_t salt{det_perturb::new_salt()};

  PerturbHasher() = default;
  // Implicit so the wrappers' (bucket_count, const Hash&) ctors keep compiling
  // when EffectiveHash_t<Hash> resolves to PerturbHasher<Hash>.
  // NOLINTNEXTLINE(google-explicit-constructor,hicpp-explicit-conversions)
  /* implicit */ PerturbHasher(const Hash& h) : base(h) {}

  // The noexcept below is UNCONDITIONAL, deliberately, even though `base(k)`
  // is not noexcept for every Hash: `boost::hash<...>` and some hand-written
  // ones (e.g. `keep_reason::ReasonPtrHash`) lack the annotation, so a throwing
  // base hasher would std::terminate here rather than propagate.
  //
  // Accepted rather than fixed, having tried both alternatives:
  //   - Propagating instead, via `noexcept(noexcept(base(k)))`, makes
  //     PerturbHasher non-noexcept for exactly those hashers, which re-enables
  //     the libstdc++ hash-code caching described above and with it the
  //     cross-container operator== bug. That trades a theoretical terminate for
  //     a real wrong-answer bug.
  //   - Demanding noexcept via static_assert does not compile: it fires on the
  //     boost hashers, which are third-party and not ours to annotate.
  //
  // Safe in practice: the hashers concerned hash pointers and integers and
  // cannot throw, they merely lack the annotation. And this code only exists in
  // perturbed builds, which are debug/CI tools that never ship.
  template <class K>
  size_t operator()(const K& k) const noexcept {
    return static_cast<size_t>(
        det_perturb::splitmix64(static_cast<uint64_t>(base(k)) ^ salt));
  }
};

// The hasher actually installed in the underlying std::unordered_* container:
// the plain Hash in normal builds, its salted form when perturbation is on.
template <class Hash>
using EffectiveHash_t =
    std::conditional_t<kPerturbUnordered, PerturbHasher<Hash>, Hash>;

template <class UnorderedDerived>
class UnorderedBase {};

template <class Key,
          class Value,
          class Hash = std::hash<Key>,
          class KeyEqual = std::equal_to<Key>>
class UnorderedMap : UnorderedBase<UnorderedMap<Key, Value, Hash, KeyEqual>> {
  using Type = std::unordered_map<Key, Value, EffectiveHash_t<Hash>, KeyEqual>;
  Type m_data;

 public:
  using key_type = typename Type::key_type;
  using mapped_type = typename Type::mapped_type;
  using value_type = typename Type::value_type;
  using size_type = typename Type::size_type;
  using difference_type = typename Type::difference_type;
  using hasher = Hash;
  using key_equal = KeyEqual;
  using reference = typename Type::reference;
  using const_reference = typename Type::const_reference;
  using pointer = typename Type::pointer;

  class FixedIterator;

  class ConstFixedIterator {
    typename Type::const_iterator m_entry;

   public:
    const value_type* operator->() const { return &*m_entry; }

    const value_type& operator*() const { return *m_entry; }

    bool operator==(const FixedIterator& other) const {
      return m_entry == other._internal_unsafe_unwrap();
    }

    bool operator!=(const FixedIterator& other) const {
      return m_entry != other._internal_unsafe_unwrap();
    }

    bool operator==(const ConstFixedIterator& other) const {
      return m_entry == other.m_entry;
    }

    bool operator!=(const ConstFixedIterator& other) const {
      return m_entry != other.m_entry;
    }

    explicit ConstFixedIterator(typename Type::const_iterator entry)
        : m_entry(entry) {}

    // Allows a mutable end()/find() FixedIterator to be used where a
    // ConstFixedIterator is expected (e.g. as a hint to insert), mirroring the
    // STL's mutable-to-const iterator conversion. Intentionally non-explicit,
    // and intentionally one-directional (no const-to-mutable conversion).
    // NOLINTNEXTLINE(google-explicit-constructor,hicpp-explicit-conversions)
    /* implicit */ ConstFixedIterator(const FixedIterator& other)
        : m_entry(other._internal_unsafe_unwrap()) {}

    typename Type::const_iterator _internal_unsafe_unwrap() const {
      return m_entry;
    }
  };

  class FixedIterator {
    typename Type::iterator m_entry;

   public:
    value_type* operator->() const { return &*m_entry; }

    value_type& operator*() const { return *m_entry; }

    bool operator==(const FixedIterator& other) const {
      return m_entry == other.m_entry;
    }

    bool operator!=(const FixedIterator& other) const {
      return m_entry != other.m_entry;
    }

    bool operator==(const ConstFixedIterator& other) const {
      return m_entry == other._internal_unsafe_unwrap();
    }

    bool operator!=(const ConstFixedIterator& other) const {
      return m_entry != other._internal_unsafe_unwrap();
    }

    explicit FixedIterator(typename Type::iterator entry) : m_entry(entry) {}

    typename Type::iterator _internal_unsafe_unwrap() const { return m_entry; }
  };

  // TODO: Make extra non-deterministic in debug builds
  class UnorderedIterable {
    Type& m_data;

   public:
    using iterator = typename Type::iterator;
    using const_iterator = typename Type::const_iterator;

    explicit UnorderedIterable(Type& data) : m_data(data) {}

    iterator begin() { return m_data.begin(); }

    iterator end() { return m_data.end(); }

    const_iterator begin() const { return m_data.begin(); }

    const_iterator end() const { return m_data.end(); }

    const_iterator cbegin() const { return m_data.cbegin(); }

    const_iterator cend() const { return m_data.cend(); }

    iterator find(const Key& key) { return m_data.find(key); }

    const_iterator find(const Key& key) const { return m_data.find(key); }

    template <typename possibly_const_iterator>
    iterator erase(possibly_const_iterator position) {
      return m_data.erase(position);
    }
  };

  // TODO: Make extra non-deterministic in debug builds
  class ConstUnorderedIterable {
    const Type& m_data;

   public:
    using const_iterator = typename Type::const_iterator;

    explicit ConstUnorderedIterable(const Type& data) : m_data(data) {}

    const_iterator begin() const { return m_data.begin(); }

    const_iterator end() const { return m_data.end(); }

    const_iterator cbegin() const { return m_data.cbegin(); }

    const_iterator cend() const { return m_data.cend(); }

    const_iterator find(const Key& key) const { return m_data.find(key); }
  };

  UnorderedMap() : m_data() {}

  explicit UnorderedMap(size_t bucket_count) : m_data(bucket_count) {}

  UnorderedMap(size_t bucket_count, const Hash& hash)
      : m_data(bucket_count, hash) {}

  UnorderedMap(size_t bucket_count, const Hash& hash, const KeyEqual& equal)
      : m_data(bucket_count, hash, equal) {}

  UnorderedMap(const UnorderedMap& other) = default;

  UnorderedMap(UnorderedMap&& other) noexcept = default;

  // NOLINTNEXTLINE(google-explicit-constructor,hicpp-explicit-conversions)
  /* implicit */ UnorderedMap(
      std::initializer_list<std::pair<const Key, Value>> init)
      : m_data(init) {}

  template <class InputIt>
  UnorderedMap(InputIt first, InputIt last) : m_data(first, last) {}

  UnorderedMap& operator=(const UnorderedMap& other) = default;

  UnorderedMap& operator=(UnorderedMap&& other) noexcept = default;

  Value& at(const Key& key) { return m_data.at(key); }

  const Value& at(const Key& key) const { return m_data.at(key); }

  template <typename... Args>
  std::pair<FixedIterator, bool> emplace(Args&&... args) {
    auto [it, success] = m_data.emplace(std::forward<Args>(args)...);
    return std::pair<FixedIterator, bool>(FixedIterator(it), success);
  }

  template <typename... Args>
  std::pair<FixedIterator, bool> try_emplace(Key&& k, Args&&... args) {
    auto [it, success] =
        m_data.try_emplace(std::forward<Key>(k), std::forward<Args>(args)...);
    return std::pair<FixedIterator, bool>(FixedIterator(it), success);
  }

  template <typename... Args>
  std::pair<FixedIterator, bool> try_emplace(const Key& k, Args&&... args) {
    auto [it, success] = m_data.try_emplace(k, std::forward<Args>(args)...);
    return std::pair<FixedIterator, bool>(FixedIterator(it), success);
  }

  std::pair<FixedIterator, bool> insert(const std::pair<Key, Value>& value) {
    auto [it, success] = m_data.insert(value);
    return std::pair<FixedIterator, bool>(FixedIterator(it), success);
  }

  std::pair<FixedIterator, bool> insert(std::pair<Key, Value>&& value) {
    auto [it, success] =
        m_data.insert(std::forward<std::pair<Key, Value>>(value));
    return std::pair<FixedIterator, bool>(FixedIterator(it), success);
  }

  template <typename P>
  std::pair<FixedIterator, bool> insert(P&& value) {
    auto [it, success] = m_data.insert(std::forward<P>(value));
    return std::pair<FixedIterator, bool>(FixedIterator(it), success);
  }

  FixedIterator insert(ConstFixedIterator hint,
                       const std::pair<Key, Value>& value) {
    auto it = m_data.insert(hint._internal_unsafe_unwrap(), value);
    return FixedIterator(it);
  }

  FixedIterator insert(ConstFixedIterator hint, std::pair<Key, Value>&& value) {
    auto it = m_data.insert(hint._internal_unsafe_unwrap(),
                            std::forward<std::pair<Key, Value>>(value));
    return FixedIterator(it);
  }

  template <typename P>
  FixedIterator insert(ConstFixedIterator hint, P&& value) {
    auto it =
        m_data.insert(hint._internal_unsafe_unwrap(), std::forward<P>(value));
    return FixedIterator(it);
  }

  template <class InputIt>
  void insert(InputIt first, InputIt last) {
    m_data.insert(first, last);
  }

  void insert(std::initializer_list<value_type> ilist) { m_data.insert(ilist); }

  Value& operator[](const Key& key) { return m_data[key]; }

  Value& operator[](Key&& key) { return m_data[std::forward<Key>(key)]; }

  FixedIterator _internal_unordered_any() {
    return FixedIterator(m_data.begin());
  }

  ConstFixedIterator _internal_unordered_any() const {
    return ConstFixedIterator(m_data.begin());
  }

  FixedIterator find(const Key& key) { return FixedIterator(m_data.find(key)); }

  ConstFixedIterator find(const Key& key) const {
    return ConstFixedIterator(m_data.find(key));
  }

  ConstFixedIterator end() const { return ConstFixedIterator(m_data.end()); }

  FixedIterator end() { return FixedIterator(m_data.end()); }

  ConstFixedIterator cend() const { return ConstFixedIterator(m_data.end()); }

  size_t erase(const Key& key) { return m_data.erase(key); }

  void erase(FixedIterator position) {
    // We intentionally do not return the iterator here, as it is not
    // ordered.
    (void)m_data.erase(position._internal_unsafe_unwrap());
  }

  void erase(ConstFixedIterator position) {
    // We intentionally do not return the iterator here, as it is not
    // ordered.
    m_data.erase(position._internal_unsafe_unwrap());
  }

  void clear() { m_data.clear(); }

  size_t count(const Key& key) const { return m_data.count(key); }

  void reserve(size_t size) { m_data.reserve(size); }

  size_t size() const { return m_data.size(); }

  bool empty() const { return m_data.empty(); }

  UnorderedIterable _internal_unordered_iterable() {
    return UnorderedIterable(m_data);
  }

  ConstUnorderedIterable _internal_unordered_iterable() const {
    return ConstUnorderedIterable(m_data);
  }

  template <typename possibly_const_iterator>
  auto _internal_to_fixed_iterator(possibly_const_iterator it) const {
    if constexpr (std::is_same_v<possibly_const_iterator,
                                 typename Type::const_iterator>) {
      return ConstFixedIterator(it);
    } else {
      return FixedIterator(it);
    }
  }

  const Type& _internal_unsafe_unwrap() const { return m_data; }

  Type& _internal_unsafe_unwrap() { return m_data; }
};

template <class Key, class Value, class Hash, class KeyEqual>
bool operator==(const UnorderedMap<Key, Value, Hash, KeyEqual>& lhs,
                const UnorderedMap<Key, Value, Hash, KeyEqual>& rhs) {
  return lhs._internal_unsafe_unwrap() == rhs._internal_unsafe_unwrap();
}

template <class Key, class Value, class Hash, class KeyEqual>
bool operator!=(const UnorderedMap<Key, Value, Hash, KeyEqual>& lhs,
                const UnorderedMap<Key, Value, Hash, KeyEqual>& rhs) {
  return lhs._internal_unsafe_unwrap() != rhs._internal_unsafe_unwrap();
}

template <class Key,
          class Value,
          class Hash = std::hash<Key>,
          class KeyEqual = std::equal_to<Key>>
class UnorderedMultiMap
    : UnorderedBase<UnorderedMultiMap<Key, Value, Hash, KeyEqual>> {
  using Type =
      std::unordered_multimap<Key, Value, EffectiveHash_t<Hash>, KeyEqual>;
  Type m_data;

 public:
  using key_type = typename Type::key_type;
  using mapped_type = typename Type::mapped_type;
  using value_type = typename Type::value_type;
  using size_type = typename Type::size_type;
  using difference_type = typename Type::difference_type;
  using hasher = Hash;
  using key_equal = KeyEqual;
  using reference = typename Type::reference;
  using const_reference = typename Type::const_reference;
  using pointer = typename Type::pointer;

  class FixedIterator;

  class ConstFixedIterator {
    typename Type::const_iterator m_entry;

   public:
    const value_type* operator->() const { return &*m_entry; }

    const value_type& operator*() const { return *m_entry; }

    bool operator==(const FixedIterator& other) const {
      return m_entry == other._internal_unsafe_unwrap();
    }

    bool operator!=(const FixedIterator& other) const {
      return m_entry != other._internal_unsafe_unwrap();
    }

    bool operator==(const ConstFixedIterator& other) const {
      return m_entry == other.m_entry;
    }

    bool operator!=(const ConstFixedIterator& other) const {
      return m_entry != other.m_entry;
    }

    explicit ConstFixedIterator(typename Type::const_iterator entry)
        : m_entry(entry) {}

    // Allows a mutable end()/find() FixedIterator to be used where a
    // ConstFixedIterator is expected (e.g. as a hint to insert), mirroring the
    // STL's mutable-to-const iterator conversion. Intentionally non-explicit,
    // and intentionally one-directional (no const-to-mutable conversion).
    // NOLINTNEXTLINE(google-explicit-constructor,hicpp-explicit-conversions)
    /* implicit */ ConstFixedIterator(const FixedIterator& other)
        : m_entry(other._internal_unsafe_unwrap()) {}

    typename Type::const_iterator _internal_unsafe_unwrap() const {
      return m_entry;
    }
  };

  class FixedIterator {
    typename Type::iterator m_entry;

   public:
    value_type* operator->() const { return &*m_entry; }

    value_type& operator*() const { return *m_entry; }

    bool operator==(const FixedIterator& other) const {
      return m_entry == other.m_entry;
    }

    bool operator!=(const FixedIterator& other) const {
      return m_entry != other.m_entry;
    }

    bool operator==(const ConstFixedIterator& other) const {
      return m_entry == other._internal_unsafe_unwrap();
    }

    bool operator!=(const ConstFixedIterator& other) const {
      return m_entry != other._internal_unsafe_unwrap();
    }

    explicit FixedIterator(typename Type::iterator entry) : m_entry(entry) {}

    typename Type::iterator _internal_unsafe_unwrap() const { return m_entry; }
  };

  // TODO: Make extra non-deterministic in debug builds
  class UnorderedIterable {
    Type& m_data;

   public:
    using iterator = typename Type::iterator;
    using const_iterator = typename Type::const_iterator;

    explicit UnorderedIterable(Type& data) : m_data(data) {}

    iterator begin() { return m_data.begin(); }

    iterator end() { return m_data.end(); }

    const_iterator begin() const { return m_data.begin(); }

    const_iterator end() const { return m_data.end(); }

    const_iterator cbegin() const { return m_data.cbegin(); }

    const_iterator cend() const { return m_data.cend(); }

    iterator find(const Key& key) { return m_data.find(key); }

    const_iterator find(const Key& key) const { return m_data.find(key); }

    template <typename possibly_const_iterator>
    iterator erase(possibly_const_iterator position) {
      return m_data.erase(position);
    }
  };

  // TODO: Make extra non-deterministic in debug builds
  class ConstUnorderedIterable {
    const Type& m_data;

   public:
    using const_iterator = typename Type::const_iterator;

    explicit ConstUnorderedIterable(const Type& data) : m_data(data) {}

    const_iterator begin() const { return m_data.begin(); }

    const_iterator end() const { return m_data.end(); }

    const_iterator cbegin() const { return m_data.cbegin(); }

    const_iterator cend() const { return m_data.cend(); }

    const_iterator find(const Key& key) const { return m_data.find(key); }
  };

  UnorderedMultiMap() = default;

  explicit UnorderedMultiMap(size_t bucket_count) : m_data(bucket_count) {}

  UnorderedMultiMap(size_t bucket_count, const Hash& hash)
      : m_data(bucket_count, hash) {}

  UnorderedMultiMap(size_t bucket_count,
                    const Hash& hash,
                    const KeyEqual& equal)
      : m_data(bucket_count, hash, equal) {}

  UnorderedMultiMap(const UnorderedMultiMap& other) = default;

  UnorderedMultiMap(UnorderedMultiMap&& other) noexcept = default;

  // NOLINTNEXTLINE(google-explicit-constructor,hicpp-explicit-conversions)
  /* implicit */ UnorderedMultiMap(
      std::initializer_list<std::pair<const Key, Value>> init)
      : m_data(init) {}

  template <class InputIt>
  UnorderedMultiMap(InputIt first, InputIt last) : m_data(first, last) {}

  UnorderedMultiMap& operator=(const UnorderedMultiMap& other) = default;

  UnorderedMultiMap& operator=(UnorderedMultiMap&& other) noexcept = default;

  template <typename... Args>
  FixedIterator emplace(Args&&... args) {
    auto it = m_data.emplace(std::forward<Args>(args)...);
    return FixedIterator(it);
  }

  template <typename... Args>
  FixedIterator emplace_hint(ConstFixedIterator hint, Args&&... args) {
    auto it = m_data.emplace_hint(hint._internal_unsafe_unwrap(),
                                  std::forward<Args>(args)...);
    return FixedIterator(it);
  }

  FixedIterator insert(const std::pair<Key, Value>& value) {
    auto it = m_data.insert(value);
    return FixedIterator(it);
  }

  FixedIterator insert(std::pair<Key, Value>&& value) {
    auto it = m_data.insert(std::forward<std::pair<Key, Value>>(value));
    return FixedIterator(it);
  }

  template <typename P>
  FixedIterator insert(P&& value) {
    auto it = m_data.insert(std::forward<P>(value));
    return FixedIterator(it);
  }

  FixedIterator insert(ConstFixedIterator hint,
                       const std::pair<Key, Value>& value) {
    auto it = m_data.insert(hint._internal_unsafe_unwrap(), value);
    return FixedIterator(it);
  }

  FixedIterator insert(ConstFixedIterator hint, std::pair<Key, Value>&& value) {
    auto it = m_data.insert(hint._internal_unsafe_unwrap(),
                            std::forward<std::pair<Key, Value>>(value));
    return FixedIterator(it);
  }

  template <typename P>
  FixedIterator insert(ConstFixedIterator hint, P&& value) {
    auto it =
        m_data.insert(hint._internal_unsafe_unwrap(), std::forward<P>(value));
    return FixedIterator(it);
  }

  template <class InputIt>
  void insert(InputIt first, InputIt last) {
    m_data.insert(first, last);
  }

  void insert(std::initializer_list<value_type> ilist) { m_data.insert(ilist); }

  FixedIterator _internal_unordered_any() {
    return FixedIterator(m_data.begin());
  }

  ConstFixedIterator _internal_unordered_any() const {
    return ConstFixedIterator(m_data.begin());
  }

  FixedIterator find(const Key& key) { return FixedIterator(m_data.find(key)); }

  ConstFixedIterator find(const Key& key) const {
    return ConstFixedIterator(m_data.find(key));
  }

  // This only returns FixedPointer Iterators, meaning it cannot be used to
  // iterate over the actual range, to do so, unordered_equal_range has to be
  // used
  std::pair<FixedIterator, FixedIterator> equal_range(const Key& key) {
    auto [first, last] = m_data.equal_range(key);
    return std::make_pair(FixedIterator(first), FixedIterator(last));
  }

  std::pair<ConstFixedIterator, ConstFixedIterator> equal_range(
      const Key& key) const {
    auto [first, last] = m_data.equal_range(key);
    return std::make_pair(ConstFixedIterator(first), ConstFixedIterator(last));
  }

  ConstFixedIterator end() const { return ConstFixedIterator(m_data.end()); }

  FixedIterator end() { return FixedIterator(m_data.end()); }

  ConstFixedIterator cend() const { return ConstFixedIterator(m_data.end()); }

  size_t erase(const Key& key) { return m_data.erase(key); }

  void erase(FixedIterator position) {
    // We intentionally do not return the iterator here, as it is not
    // ordered.
    (void)m_data.erase(position._internal_unsafe_unwrap());
  }

  void erase(ConstFixedIterator position) {
    // We intentionally do not return the iterator here, as it is not
    // ordered.
    m_data.erase(position._internal_unsafe_unwrap());
  }

  void clear() { m_data.clear(); }

  size_t count(const Key& key) const { return m_data.count(key); }

  void reserve(size_t size) { m_data.reserve(size); }

  size_t size() const { return m_data.size(); }

  bool empty() const { return m_data.empty(); }

  // Not perturbed: the order ACROSS keys is already perturbed by the salted
  // EffectiveHash_t, but the order of values WITHIN one key's equal_range is
  // left in insertion order.
  //
  // This is a deliberate limitation rather than an oversight, so it is stated
  // here rather than tracked as work to do. Perturbing the within-key order
  // would require this pair-of-iterators contract to become an owning range
  // holding a shuffled buffer -- a bare iterator pair owns nothing, so
  // iterators into a temporary buffer would dangle -- which is a
  // caller-visible API change. Intra-equal-key-group order dependence is rare
  // and UnorderedMultiMap is itself uncommon, so the payoff does not justify
  // that churn. Revisit if a real divergence is ever traced to this gap.
  std::pair<typename Type::const_iterator, typename Type::const_iterator>
  _internal_unordered_equal_range(const Key& key) const {
    return m_data.equal_range(key);
  }

  UnorderedIterable _internal_unordered_iterable() {
    return UnorderedIterable(m_data);
  }

  ConstUnorderedIterable _internal_unordered_iterable() const {
    return ConstUnorderedIterable(m_data);
  }

  template <typename possibly_const_iterator>
  auto _internal_to_fixed_iterator(possibly_const_iterator it) const {
    if constexpr (std::is_same_v<possibly_const_iterator,
                                 typename Type::const_iterator>) {
      return ConstFixedIterator(it);
    } else {
      return FixedIterator(it);
    }
  }

  const Type& _internal_unsafe_unwrap() const { return m_data; }

  Type& _internal_unsafe_unwrap() { return m_data; }
};

template <class Key, class Value, class Hash, class KeyEqual>
bool operator==(const UnorderedMultiMap<Key, Value, Hash, KeyEqual>& lhs,
                const UnorderedMultiMap<Key, Value, Hash, KeyEqual>& rhs) {
  return lhs._internal_unsafe_unwrap() == rhs._internal_unsafe_unwrap();
}

template <class Key, class Value, class Hash, class KeyEqual>
bool operator!=(const UnorderedMultiMap<Key, Value, Hash, KeyEqual>& lhs,
                const UnorderedMultiMap<Key, Value, Hash, KeyEqual>& rhs) {
  return lhs._internal_unsafe_unwrap() != rhs._internal_unsafe_unwrap();
}

// A forward-only iterator over an UnorderedBag's elements. A bag's iteration
// order carries no meaning, so its view deliberately exposes only forward
// traversal (no random access), in both build modes: code that would depend on
// element position fails to compile everywhere rather than only under
// perturbation in CI. When perturbation is off it is a zero-cost pass-through
// that holds and advances the real vector iterator, so ++/*/== compile to
// exactly the same code as iterating the backing vector directly. When on it
// walks the range [base, base + n) from a salted offset and wraps around,
// visiting every element exactly once but in a rotated order (a bag is a
// std::vector, so it has no hasher to salt like the hash-based wrappers).
//
// Forward-only is sufficient: no bag consumer needs random access -- min/max/
// find/copy/accumulate are all single-pass, and callers that sort go through
// unordered_to_ordered, which copies into a fresh vector first.
template <class VecIter>
class BagViewIterator {
 public:
  using iterator_category = std::forward_iterator_tag;
  using value_type = typename std::iterator_traits<VecIter>::value_type;
  using difference_type =
      typename std::iterator_traits<VecIter>::difference_type;
  using pointer = typename std::iterator_traits<VecIter>::pointer;
  using reference = typename std::iterator_traits<VecIter>::reference;

  BagViewIterator() = default;

#if REDEX_PERTURB_UNORDERED
  BagViewIterator(VecIter base, size_t n, size_t off, size_t pos)
      : m_base(base), m_n(n), m_off(off), m_pos(pos) {}

  reference operator*() const { return *underlying(); }
  pointer operator->() const { return &*underlying(); }

  BagViewIterator& operator++() {
    ++m_pos;
    return *this;
  }
  BagViewIterator operator++(int) {
    BagViewIterator tmp = *this;
    ++m_pos;
    return tmp;
  }

  bool operator==(const BagViewIterator& other) const {
    return m_pos == other.m_pos;
  }
  bool operator!=(const BagViewIterator& other) const {
    return m_pos != other.m_pos;
  }

  // The real range iterator for the current logical position. A past-the-end
  // position maps to base + n (the range's real end()), so a not-found result
  // maps back to the container's end().
  VecIter underlying() const {
    size_t phys = m_pos >= m_n ? m_n : (m_off + m_pos) % m_n;
    return m_base + static_cast<difference_type>(phys);
  }

 private:
  VecIter m_base{};
  size_t m_n{0};
  size_t m_off{0};
  size_t m_pos{0};
#else
  explicit BagViewIterator(VecIter it) : m_it(it) {}

  reference operator*() const { return *m_it; }
  pointer operator->() const { return &*m_it; }

  BagViewIterator& operator++() {
    ++m_it;
    return *this;
  }
  BagViewIterator operator++(int) {
    BagViewIterator tmp = *this;
    ++m_it;
    return tmp;
  }

  bool operator==(const BagViewIterator& other) const {
    return m_it == other.m_it;
  }
  bool operator!=(const BagViewIterator& other) const {
    return m_it != other.m_it;
  }

  // The underlying vector iterator for the current position, used to map a view
  // iterator back to a (non-steppable) FixedIterator.
  VecIter underlying() const { return m_it; }

 private:
  VecIter m_it{};
#endif
};

template <class T>
struct is_bag_view_iterator : std::false_type {};
template <class VecIter>
struct is_bag_view_iterator<BagViewIterator<VecIter>> : std::true_type {};
template <class T>
inline constexpr bool is_bag_view_iterator_v = is_bag_view_iterator<T>::value;

class UnorderedBagBase {};

template <class Value>
class UnorderedBag : UnorderedBase<UnorderedBag<Value>>, UnorderedBagBase {
  using Type = std::vector<Value>;
  Type m_data;
#if REDEX_PERTURB_UNORDERED
  // Per-bag salt for iteration-order perturbation (a bag has no hasher to salt,
  // unlike the hash-based wrappers). Absent -> byte-identical when off. It
  // perturbs only iteration order, not the bag's value, so it does not affect
  // unordered_equal (which compares the raw elements as an order-independent
  // multiset).
  uint64_t m_salt{det_perturb::new_salt()};
#endif

 public:
  using key_type = void;
  using value_type = typename Type::value_type;
  using size_type = typename Type::size_type;
  using difference_type = typename Type::difference_type;
  using reference = typename Type::reference;
  using const_reference = typename Type::const_reference;
  using pointer = typename Type::pointer;
  using const_pointer = typename Type::const_pointer;

  class FixedIterator;

  class ConstFixedIterator {
    typename Type::const_iterator m_entry;

   public:
    const value_type* operator->() const { return &*m_entry; }

    const value_type& operator*() const { return *m_entry; }

    bool operator==(const FixedIterator& other) const {
      return m_entry == other._internal_unsafe_unwrap();
    }

    bool operator!=(const FixedIterator& other) const {
      return m_entry != other._internal_unsafe_unwrap();
    }

    bool operator==(const ConstFixedIterator& other) const {
      return m_entry == other.m_entry;
    }

    bool operator!=(const ConstFixedIterator& other) const {
      return m_entry != other.m_entry;
    }

    explicit ConstFixedIterator(typename Type::const_iterator entry)
        : m_entry(entry) {}

    // Allows a mutable end()/find() FixedIterator to be used where a
    // ConstFixedIterator is expected (e.g. as a hint to insert), mirroring the
    // STL's mutable-to-const iterator conversion. Intentionally non-explicit,
    // and intentionally one-directional (no const-to-mutable conversion).
    // NOLINTNEXTLINE(google-explicit-constructor,hicpp-explicit-conversions)
    /* implicit */ ConstFixedIterator(const FixedIterator& other)
        : m_entry(other._internal_unsafe_unwrap()) {}

    typename Type::const_iterator _internal_unsafe_unwrap() const {
      return m_entry;
    }
  };

  class FixedIterator {
    typename Type::iterator m_entry;

   public:
    value_type* operator->() const { return &*m_entry; }

    value_type& operator*() const { return *m_entry; }

    bool operator==(const FixedIterator& other) const {
      return m_entry == other.m_entry;
    }

    bool operator!=(const FixedIterator& other) const {
      return m_entry != other.m_entry;
    }

    bool operator==(const ConstFixedIterator& other) const {
      return m_entry == other._internal_unsafe_unwrap();
    }

    bool operator!=(const ConstFixedIterator& other) const {
      return m_entry != other._internal_unsafe_unwrap();
    }

    explicit FixedIterator(typename Type::iterator entry) : m_entry(entry) {}

    typename Type::iterator _internal_unsafe_unwrap() const { return m_entry; }
  };

  class UnorderedIterable {
    Type& m_data;
#if REDEX_PERTURB_UNORDERED
    uint64_t m_salt;

    size_t offset() const {
      size_t n = m_data.size();
      return n == 0 ? 0 : m_salt % n;
    }
#endif

   public:
    using iterator = BagViewIterator<typename Type::iterator>;
    using const_iterator = BagViewIterator<typename Type::const_iterator>;

#if REDEX_PERTURB_UNORDERED
    UnorderedIterable(Type& data, uint64_t salt) : m_data(data), m_salt(salt) {}

    iterator begin() {
      return iterator(m_data.begin(), m_data.size(), offset(), 0);
    }
    iterator end() {
      return iterator(m_data.begin(), m_data.size(), offset(), m_data.size());
    }
    const_iterator begin() const {
      return const_iterator(m_data.cbegin(), m_data.size(), offset(), 0);
    }
    const_iterator end() const {
      return const_iterator(m_data.cbegin(), m_data.size(), offset(),
                            m_data.size());
    }
    const_iterator cbegin() const { return begin(); }
    const_iterator cend() const { return end(); }
#else
    explicit UnorderedIterable(Type& data) : m_data(data) {}

    iterator begin() { return iterator(m_data.begin()); }

    iterator end() { return iterator(m_data.end()); }

    const_iterator begin() const { return const_iterator(m_data.cbegin()); }

    const_iterator end() const { return const_iterator(m_data.cend()); }

    const_iterator cbegin() const { return const_iterator(m_data.cbegin()); }

    const_iterator cend() const { return const_iterator(m_data.cend()); }
#endif
  };

  class ConstUnorderedIterable {
    const Type& m_data;
#if REDEX_PERTURB_UNORDERED
    uint64_t m_salt;

    size_t offset() const {
      size_t n = m_data.size();
      return n == 0 ? 0 : m_salt % n;
    }
#endif

   public:
    using const_iterator = BagViewIterator<typename Type::const_iterator>;

#if REDEX_PERTURB_UNORDERED
    ConstUnorderedIterable(const Type& data, uint64_t salt)
        : m_data(data), m_salt(salt) {}

    const_iterator begin() const {
      return const_iterator(m_data.begin(), m_data.size(), offset(), 0);
    }
    const_iterator end() const {
      return const_iterator(m_data.begin(), m_data.size(), offset(),
                            m_data.size());
    }
    const_iterator cbegin() const { return begin(); }
    const_iterator cend() const { return end(); }
#else
    explicit ConstUnorderedIterable(const Type& data) : m_data(data) {}

    const_iterator begin() const { return const_iterator(m_data.begin()); }

    const_iterator end() const { return const_iterator(m_data.end()); }

    const_iterator cbegin() const { return const_iterator(m_data.cbegin()); }

    const_iterator cend() const { return const_iterator(m_data.cend()); }
#endif
  };

  UnorderedBag() : m_data() {}

  explicit UnorderedBag(size_type count) : m_data(count) {}

  explicit UnorderedBag(size_type count, const Value& value = Value())
      : m_data(count, value) {}

  UnorderedBag(const UnorderedBag& other) = default;

  UnorderedBag(UnorderedBag&& other) noexcept = default;

  // NOLINTNEXTLINE(google-explicit-constructor,hicpp-explicit-conversions)
  /* implicit */ UnorderedBag(std::initializer_list<Value> init)
      : m_data(init) {}

  template <class InputIt>
  UnorderedBag(InputIt first, InputIt last) : m_data(first, last) {}

  UnorderedBag& operator=(const UnorderedBag& other) = default;

  UnorderedBag& operator=(UnorderedBag&& other) noexcept = default;

  template <typename... Args>
  reference emplace(Args&&... args) {
    return m_data.emplace_back(std::forward<Args>(args)...);
  }

  void insert(const Value& value) { m_data.push_back(value); }

  void insert(Value&& value) { m_data.push_back(std::forward<Value>(value)); }

  template <class InputIt>
  void insert(InputIt first, InputIt last) {
    m_data.insert(m_data.end(), first, last);
  }

  void insert(std::initializer_list<Value> ilist) {
    m_data.insert(m_data.end(), ilist);
  }

  FixedIterator _internal_unordered_any() {
#if REDEX_PERTURB_UNORDERED
    if (!m_data.empty()) {
      return FixedIterator(m_data.begin() + static_cast<difference_type>(
                                                m_salt % m_data.size()));
    }
#endif
    return FixedIterator(m_data.begin());
  }

  ConstFixedIterator _internal_unordered_any() const {
#if REDEX_PERTURB_UNORDERED
    if (!m_data.empty()) {
      return ConstFixedIterator(m_data.begin() + static_cast<difference_type>(
                                                     m_salt % m_data.size()));
    }
#endif
    return ConstFixedIterator(m_data.begin());
  }

  ConstFixedIterator end() const { return ConstFixedIterator(m_data.end()); }

  FixedIterator end() { return FixedIterator(m_data.end()); }

  ConstFixedIterator cend() const { return ConstFixedIterator(m_data.end()); }

  void clear() { m_data.clear(); }

  void reserve(size_t size) { m_data.reserve(size); }

  void shrink_to_fit() { m_data.shrink_to_fit(); }

  size_type size() const { return m_data.size(); }

  size_type capacity() const { return m_data.capacity(); }

  bool empty() const { return m_data.empty(); }

  UnorderedIterable _internal_unordered_iterable() {
#if REDEX_PERTURB_UNORDERED
    return UnorderedIterable(m_data, m_salt);
#else
    return UnorderedIterable(m_data);
#endif
  }

  ConstUnorderedIterable _internal_unordered_iterable() const {
#if REDEX_PERTURB_UNORDERED
    return ConstUnorderedIterable(m_data, m_salt);
#else
    return ConstUnorderedIterable(m_data);
#endif
  }

  template <typename possibly_const_iterator>
  auto _internal_to_fixed_iterator(possibly_const_iterator it) const {
    if constexpr (is_bag_view_iterator_v<possibly_const_iterator>) {
      // A bag view yields BagViewIterators; map back to the real vector
      // iterator before building the (non-steppable) FixedIterator.
      auto entry = it.underlying();
      if constexpr (std::is_same_v<decltype(entry),
                                   typename Type::const_iterator>) {
        return ConstFixedIterator(entry);
      } else {
        return FixedIterator(entry);
      }
    } else if constexpr (std::is_same_v<possibly_const_iterator,
                                        typename Type::const_iterator>) {
      return ConstFixedIterator(it);
    } else {
      return FixedIterator(it);
    }
  }

  const Type& _internal_unsafe_unwrap() const { return m_data; }

  Type& _internal_unsafe_unwrap() { return m_data; }
};

// UnorderedBag intentionally provides no operator==/operator!=. A bag's element
// order is non-deterministic, so sequence equality (delegating to the backing
// std::vector) would depend on that order, and there is no meaningful
// order-independent default. Callers that need to compare bags must pick
// explicit semantics (e.g. compare unordered_to_ordered(...) results, or pass a
// custom order-independent equality to APIs like
// InsertOnlyConcurrentMap::get_or_create_and_assert_equal).

template <class Key,
          class Hash = std::hash<Key>,
          class KeyEqual = std::equal_to<Key>>
class UnorderedSet : UnorderedBase<UnorderedSet<Key, Hash, KeyEqual>> {
  using Type = std::unordered_set<Key, EffectiveHash_t<Hash>, KeyEqual>;
  Type m_data;

 public:
  using key_type = typename Type::key_type;
  using value_type = typename Type::value_type;
  using size_type = typename Type::size_type;
  using difference_type = typename Type::difference_type;
  using hasher = Hash;
  using key_equal = KeyEqual;
  using reference = typename Type::reference;
  using const_reference = typename Type::const_reference;
  using pointer = typename Type::pointer;

  class FixedIterator;

  class ConstFixedIterator {
    typename Type::const_iterator m_entry;

   public:
    const Key* operator->() const { return &*m_entry; }

    const Key& operator*() const { return *m_entry; }

    bool operator==(const FixedIterator& other) const {
      return m_entry == other._internal_unsafe_unwrap();
    }

    bool operator!=(const FixedIterator& other) const {
      return m_entry != other._internal_unsafe_unwrap();
    }

    bool operator==(const ConstFixedIterator& other) const {
      return m_entry == other.m_entry;
    }

    bool operator!=(const ConstFixedIterator& other) const {
      return m_entry != other.m_entry;
    }

    explicit ConstFixedIterator(typename Type::const_iterator entry)
        : m_entry(entry) {}

    // Allows a mutable end()/find() FixedIterator to be used where a
    // ConstFixedIterator is expected (e.g. as a hint to insert), mirroring the
    // STL's mutable-to-const iterator conversion. Intentionally non-explicit,
    // and intentionally one-directional (no const-to-mutable conversion).
    // NOLINTNEXTLINE(google-explicit-constructor,hicpp-explicit-conversions)
    /* implicit */ ConstFixedIterator(const FixedIterator& other)
        : m_entry(other._internal_unsafe_unwrap()) {}

    typename Type::const_iterator _internal_unsafe_unwrap() const {
      return m_entry;
    }
  };

  class FixedIterator {
    typename Type::iterator m_entry;

   public:
    // Note that the Set iterator doesn't expose mutable values at all.

    const Key* operator->() const { return &*m_entry; }

    const Key& operator*() const { return *m_entry; }

    bool operator==(const FixedIterator& other) const {
      return m_entry == other.m_entry;
    }

    bool operator!=(const FixedIterator& other) const {
      return m_entry != other.m_entry;
    }

    bool operator==(const ConstFixedIterator& other) const {
      return m_entry == other._internal_unsafe_unwrap();
    }

    bool operator!=(const ConstFixedIterator& other) const {
      return m_entry != other._internal_unsafe_unwrap();
    }

    explicit FixedIterator(typename Type::iterator entry) : m_entry(entry) {}

    typename Type::iterator _internal_unsafe_unwrap() const { return m_entry; }
  };

  // TODO: Make extra non-deterministic in debug builds
  class UnorderedIterable {
    Type& m_data;

   public:
    using iterator = typename Type::iterator;
    using const_iterator = typename Type::const_iterator;

    explicit UnorderedIterable(Type& data) : m_data(data) {}

    iterator begin() { return m_data.begin(); }

    iterator end() { return m_data.end(); }

    const_iterator begin() const { return m_data.begin(); }

    const_iterator end() const { return m_data.end(); }

    const_iterator cbegin() const { return m_data.cbegin(); }

    const_iterator cend() const { return m_data.cend(); }

    iterator find(const Key& key) { return m_data.find(key); }

    const_iterator find(const Key& key) const { return m_data.find(key); }

    template <typename possibly_const_iterator>
    iterator erase(possibly_const_iterator position) {
      return m_data.erase(position);
    }
  };

  // TODO: Make extra non-deterministic in debug builds
  class ConstUnorderedIterable {
    const Type& m_data;

   public:
    using const_iterator = typename Type::const_iterator;

    explicit ConstUnorderedIterable(const Type& data) : m_data(data) {}

    const_iterator begin() const { return m_data.begin(); }

    const_iterator end() const { return m_data.end(); }

    const_iterator cbegin() const { return m_data.cbegin(); }

    const_iterator cend() const { return m_data.cend(); }

    const_iterator find(const Key& key) const { return m_data.find(key); }
  };

  UnorderedSet() : m_data() {}

  explicit UnorderedSet(size_t bucket_count) : m_data(bucket_count) {}

  UnorderedSet(size_t bucket_count, const Hash& hash)
      : m_data(bucket_count, hash) {}

  UnorderedSet(size_t bucket_count, const Hash& hash, const KeyEqual& equal)
      : m_data(bucket_count, hash, equal) {}

  UnorderedSet(const UnorderedSet& other) = default;

  UnorderedSet(UnorderedSet&& other) noexcept = default;

  // NOLINTNEXTLINE(google-explicit-constructor,hicpp-explicit-conversions)
  /* implicit */ UnorderedSet(std::initializer_list<Key> init) : m_data(init) {}

  template <class InputIt>
  UnorderedSet(InputIt first, InputIt last) : m_data(first, last) {}

  UnorderedSet& operator=(const UnorderedSet& other) = default;

  UnorderedSet& operator=(UnorderedSet&& other) noexcept = default;

  template <typename... Args>
  std::pair<FixedIterator, bool> emplace(Args&&... args) {
    auto [it, success] = m_data.emplace(std::forward<Args>(args)...);
    return std::pair<FixedIterator, bool>(FixedIterator(it), success);
  }

  std::pair<FixedIterator, bool> insert(const Key& value) {
    auto [it, success] = m_data.insert(value);
    return std::pair<FixedIterator, bool>(FixedIterator(it), success);
  }

  std::pair<FixedIterator, bool> insert(Key&& value) {
    auto [it, success] = m_data.insert(std::forward<Key>(value));
    return std::pair<FixedIterator, bool>(FixedIterator(it), success);
  }

  FixedIterator insert(FixedIterator hint, const Key& value) {
    auto it = m_data.insert(hint._internal_unsafe_unwrap(), value);
    return FixedIterator(it);
  }

  FixedIterator insert(FixedIterator hint, Key&& value) {
    auto it =
        m_data.insert(hint._internal_unsafe_unwrap(), std::forward<Key>(value));
    return FixedIterator(it);
  }

  template <class InputIt>
  void insert(InputIt first, InputIt last) {
    m_data.insert(first, last);
  }

  void insert(std::initializer_list<Key> ilist) { m_data.insert(ilist); }

  FixedIterator _internal_unordered_any() {
    return FixedIterator(m_data.begin());
  }

  ConstFixedIterator _internal_unordered_any() const {
    return ConstFixedIterator(m_data.begin());
  }

  FixedIterator find(const Key& key) { return FixedIterator(m_data.find(key)); }

  ConstFixedIterator find(const Key& key) const {
    return ConstFixedIterator(m_data.find(key));
  }

  ConstFixedIterator end() const { return ConstFixedIterator(m_data.end()); }

  FixedIterator end() { return FixedIterator(m_data.end()); }

  ConstFixedIterator cend() const { return ConstFixedIterator(m_data.end()); }

  size_t erase(const Key& key) { return m_data.erase(key); }

  void erase(FixedIterator position) {
    // We intentionally do not return the iterator here, as it is not
    // ordered.
    (void)m_data.erase(position._internal_unsafe_unwrap());
  }

  void erase(ConstFixedIterator position) {
    // We intentionally do not return the iterator here, as it is not
    // ordered.
    (void)m_data.erase(position._internal_unsafe_unwrap());
  }

  void clear() { m_data.clear(); }

  size_t count(const Key& key) const { return m_data.count(key); }

  bool contains(const Key& key) const { return m_data.count(key) != 0; }

  void reserve(size_t size) { m_data.reserve(size); }

  size_t size() const { return m_data.size(); }

  bool empty() const { return m_data.empty(); }

  UnorderedIterable _internal_unordered_iterable() {
    return UnorderedIterable(m_data);
  }

  ConstUnorderedIterable _internal_unordered_iterable() const {
    return ConstUnorderedIterable(m_data);
  }

  template <typename possibly_const_iterator>
  auto _internal_to_fixed_iterator(possibly_const_iterator it) const {
    if constexpr (std::is_same_v<possibly_const_iterator,
                                 typename Type::const_iterator>) {
      return ConstFixedIterator(it);
    } else {
      return FixedIterator(it);
    }
  }

  const Type& _internal_unsafe_unwrap() const { return m_data; }

  Type& _internal_unsafe_unwrap() { return m_data; }
};

template <class Key, class Hash, class KeyEqual>
bool operator==(const UnorderedSet<Key, Hash, KeyEqual>& lhs,
                const UnorderedSet<Key, Hash, KeyEqual>& rhs) {
  return lhs._internal_unsafe_unwrap() == rhs._internal_unsafe_unwrap();
}

template <class Key, class Hash, class KeyEqual>
bool operator!=(const UnorderedSet<Key, Hash, KeyEqual>& lhs,
                const UnorderedSet<Key, Hash, KeyEqual>& rhs) {
  return lhs._internal_unsafe_unwrap() != rhs._internal_unsafe_unwrap();
}

template <class UnorderedCollection,
          std::enable_if_t<std::is_base_of_v<UnorderedBase<UnorderedCollection>,
                                             UnorderedCollection>,
                           bool> = true>
auto unordered_any(UnorderedCollection& collection) {
  return collection._internal_unordered_any();
}

template <class UnorderedCollection,
          std::enable_if_t<std::is_base_of_v<UnorderedBase<UnorderedCollection>,
                                             UnorderedCollection>,
                           bool> = true>
auto unordered_any(const UnorderedCollection& collection) {
  return collection._internal_unordered_any();
}

template <
    class Collection,
    std::enable_if_t<!std::is_base_of_v<UnorderedBase<Collection>, Collection>,
                     bool> = true>
auto unordered_any(Collection& collection) {
  return collection.begin();
}

template <
    class Collection,
    std::enable_if_t<!std::is_base_of_v<UnorderedBase<Collection>, Collection>,
                     bool> = true>
auto unordered_any(const Collection& collection) {
  return collection.begin();
}

// Reject rvalues: an iterator into a temporary would dangle once the enclosing
// full-expression ends. Callers must bind the collection to a variable first.
// (Safe inline uses such as `*unordered_any(x)` where x is an lvalue are
// unaffected, as they select the lvalue overloads above.)
template <class Collection, bool skip_assert = false>
auto unordered_any(Collection&& collection) {
  static_assert(skip_assert,
                "unordered_any from an rvalue collection would return an "
                "iterator into a destroyed temporary; store the collection in "
                "a variable first.");
  // Only present so that a return type can be inferred; never reached.
  return collection.end();
}

// Return the sole element by reference, preserving iterator constness. Maps
// return a key-value pair; use .first or .second to select the key or value.
// Requires size() == 1 in opt builds too. Selection is deterministic because
// there is no choice of element. Accepts lvalue Unordered* wrappers and
// ordinary containers supported by unordered_any whose iterators return
// references. Temporaries are rejected; the reference follows the container's
// invalidation rules and must not outlive it.
template <class Collection>
auto& only(Collection& collection) {
  always_assert_log(collection.size() == 1,
                    "only requires exactly one element, got %zu",
                    static_cast<size_t>(collection.size()));
  return *unordered_any(collection);
}

template <class Collection>
void only(const Collection&&) = delete;

template <class UnorderedCollection,
          std::enable_if_t<std::is_base_of_v<UnorderedBase<UnorderedCollection>,
                                             UnorderedCollection>,
                           bool> = true>
auto UnorderedIterable(UnorderedCollection& collection) {
  return collection._internal_unordered_iterable();
}

template <class UnorderedCollection,
          std::enable_if_t<std::is_base_of_v<UnorderedBase<UnorderedCollection>,
                                             UnorderedCollection>,
                           bool> = true>
auto UnorderedIterable(const UnorderedCollection& collection) {
  return collection._internal_unordered_iterable();
}

template <class UnorderedCollection,
          std::enable_if_t<std::is_base_of_v<UnorderedBase<UnorderedCollection>,
                                             UnorderedCollection>,
                           bool> = true,
          bool skip_assert = false>
auto UnorderedIterable(UnorderedCollection&& collection) {
  // This templated function gets selected in an expression like the following,
  // where the argument is a temporary (an rvalue) collection:
  // for (auto x : UnorderedIterable(make_unordered_map())) { ... }
  // The temporary collection may get destroyed before the end of the loop. We
  // want to avoid that, as the UnorderedIterable() only captures a reference to
  // the collection.
  static_assert(
      skip_assert,
      "Creating an UnorderedIterable from an rvalue is not implemented. Store "
      "the collection as temporary value in a variable instead, and ensure "
      "that the lifetime of the variable exceeds the lifetime of the "
      "iterable.");
  // We only leave this return-statement here so that a reasonable return type
  // can be inferred.
  return collection._internal_unordered_iterable();
}

template <
    class Collection,
    std::enable_if_t<!std::is_base_of_v<UnorderedBase<Collection>, Collection>,
                     bool> = true>
Collection& UnorderedIterable(Collection& collection) {
  return collection;
}

template <
    class Collection,
    std::enable_if_t<!std::is_base_of_v<UnorderedBase<Collection>, Collection>,
                     bool> = true>
const Collection& UnorderedIterable(const Collection& collection) {
  return collection;
}

// Reject rvalues of ordinary (non-wrapper) collections too: returning a
// reference to a temporary would dangle (the wrapper overload above already
// rejects wrapper rvalues). The !is_base_of constraint keeps this disjoint from
// that wrapper rvalue overload so the two never overlap.
template <
    class Collection,
    std::enable_if_t<!std::is_base_of_v<UnorderedBase<Collection>, Collection>,
                     bool> = true,
    bool skip_assert = false>
Collection& UnorderedIterable(Collection&& collection) {
  static_assert(skip_assert,
                "Creating an UnorderedIterable from an rvalue ordinary "
                "collection would return a reference to a destroyed temporary; "
                "store the collection in a variable first.");
  // Only present so that a return type can be inferred; never reached.
  return collection;
}

template <class UnorderedCollection,
          class Key,
          std::enable_if_t<std::is_base_of_v<UnorderedBase<UnorderedCollection>,
                                             UnorderedCollection>,
                           bool> = true>
auto unordered_equal_range(const UnorderedCollection& collection,
                           const Key& key) {
  return collection._internal_unordered_equal_range(key);
}

template <
    class Collection,
    class Key,
    std::enable_if_t<!std::is_base_of_v<UnorderedBase<Collection>, Collection>,
                     bool> = true>
auto unordered_equal_range(const Collection& collection, const Key& key) {
  return collection.equal_range(key);
}

template <class UnorderedCollection,
          class UnorderedIt,
          std::enable_if_t<std::is_base_of_v<UnorderedBase<UnorderedCollection>,
                                             UnorderedCollection>,
                           bool> = true>
auto unordered_to_fixed_iterator(const UnorderedCollection& collection,
                                 UnorderedIt it) {
  return collection._internal_to_fixed_iterator(it);
}

template <
    class Collection,
    class It,
    std::enable_if_t<!std::is_base_of_v<UnorderedBase<Collection>, Collection>,
                     bool> = true>
It unordered_to_fixed_iterator(const Collection&, It it) {
  return it;
}

template <class UnorderedCollection,
          std::enable_if_t<std::is_base_of_v<UnorderedBase<UnorderedCollection>,
                                             UnorderedCollection>,
                           bool> = true>
const auto& unordered_unsafe_unwrap(const UnorderedCollection& collection) {
  return collection._internal_unsafe_unwrap();
}

template <class UnorderedCollection,
          std::enable_if_t<std::is_base_of_v<UnorderedBase<UnorderedCollection>,
                                             UnorderedCollection>,
                           bool> = true>
auto& unordered_unsafe_unwrap(UnorderedCollection& collection) {
  return collection._internal_unsafe_unwrap();
}

template <
    class Collection,
    std::enable_if_t<!std::is_base_of_v<UnorderedBase<Collection>, Collection>,
                     bool> = true>
Collection& unordered_unsafe_unwrap(Collection& collection) {
  return collection;
}

template <
    class Collection,
    std::enable_if_t<!std::is_base_of_v<UnorderedBase<Collection>, Collection>,
                     bool> = true>
const Collection& unordered_unsafe_unwrap(const Collection& collection) {
  return collection;
}

template <
    class Collection,
    class Compare,
    class Key = typename std::remove_const<typename Collection::key_type>::type,
    class Value =
        typename std::remove_const<typename Collection::mapped_type>::type,
    std::enable_if_t<!std::is_same_v<typename Collection::key_type,
                                     typename Collection::value_type>,
                     bool> = true>
std::vector<std::pair<Key, Value>> unordered_to_ordered(Collection& collection,
                                                        Compare comp) {
  std::vector<std::pair<Key, Value>> result;
  result.reserve(collection.size());
  for (auto& entry : UnorderedIterable(collection)) {
    result.emplace_back(entry);
  }
  std::sort(result.begin(), result.end(), std::move(comp));
  return result;
}

template <class Collection,
          class Value =
              typename std::remove_const<typename Collection::value_type>::type,
          std::enable_if_t<std::is_same_v<typename Collection::key_type,
                                          typename Collection::value_type> ||
                               std::is_base_of_v<UnorderedBagBase, Collection>,
                           bool> = true>
std::vector<Value> unordered_to_ordered(Collection& collection) {
  static_assert(
      !std::is_pointer_v<Value>,
      "unordered_to_ordered on a collection of raw pointers would order by "
      "address, which is non-deterministic across runs; pass an explicit "
      "comparator (e.g. compare_dexmethods) to the two-argument overload. Note "
      "this guard only catches raw pointers, not smart pointers or "
      "pointer-containing pairs/tuples.");
  std::vector<Value> result;
  result.reserve(collection.size());
  for (auto& entry : UnorderedIterable(collection)) {
    result.emplace_back(entry);
  }
  std::sort(result.begin(), result.end());
  return result;
}

template <class Collection,
          class Compare,
          class Value =
              typename std::remove_const<typename Collection::value_type>::type,
          std::enable_if_t<std::is_base_of_v<UnorderedBagBase, Collection> ||
                               std::is_same_v<typename Collection::key_type,
                                              typename Collection::value_type>,
                           bool> = true>
std::vector<Value> unordered_to_ordered(Collection& collection, Compare comp) {
  std::vector<Value> result;
  result.reserve(collection.size());
  for (auto& entry : UnorderedIterable(collection)) {
    result.emplace_back(entry);
  }
  std::sort(result.begin(), result.end(), std::move(comp));
  return result;
}

template <
    class Collection,
    class Key = typename std::remove_const<typename Collection::key_type>::type>
std::vector<Key> unordered_to_ordered_keys(Collection& collection) {
  static_assert(
      !std::is_pointer_v<Key>,
      "unordered_to_ordered_keys on raw pointer keys would order by address, "
      "which is non-deterministic across runs; pass an explicit comparator to "
      "the two-argument overload. Note this guard only catches raw pointers, "
      "not smart pointers or pointer-containing pairs/tuples.");
  std::vector<Key> result;
  result.reserve(collection.size());
  for (auto& entry : UnorderedIterable(collection)) {
    result.emplace_back(entry.first);
  }
  std::sort(result.begin(), result.end());
  return result;
}

template <
    class Collection,
    class Compare,
    class Key = typename std::remove_const<typename Collection::key_type>::type>
std::vector<Key> unordered_to_ordered_keys(Collection& collection,
                                           Compare comp) {
  std::vector<Key> result;
  result.reserve(collection.size());
  for (auto& entry : UnorderedIterable(collection)) {
    result.emplace_back(entry.first);
  }
  std::sort(result.begin(), result.end(), std::move(comp));
  return result;
}

template <
    class Collection,
    class Key = typename std::remove_const<typename Collection::key_type>::type>
auto unordered_keys(Collection& collection) {
  UnorderedSet<Key, typename Collection::hasher, typename Collection::key_equal>
      result;
  result.reserve(collection.size());
  for (auto& entry : UnorderedIterable(collection)) {
    result.insert(entry.first);
  }
  return result;
}

template <class Collection, class T>
T unordered_accumulate(const Collection& collection, T init) {
  auto&& ui = UnorderedIterable(collection);
  return std::accumulate(ui.begin(), ui.end(), std::move(init));
}

template <class Collection, class T, class BinaryOp>
T unordered_accumulate(const Collection& collection, T init, BinaryOp op) {
  auto&& ui = UnorderedIterable(collection);
  return std::accumulate(ui.begin(), ui.end(), std::move(init), std::move(op));
}

template <class Collection, class UnaryPred>
bool unordered_all_of(const Collection& collection, UnaryPred p) {
  auto&& ui = UnorderedIterable(collection);
  return std::all_of(ui.begin(), ui.end(), std::move(p));
}

template <class Collection, class UnaryPred>
bool unordered_any_of(const Collection& collection, UnaryPred p) {
  auto&& ui = UnorderedIterable(collection);
  return std::any_of(ui.begin(), ui.end(), std::move(p));
}

template <class Collection, class UnaryPred>
bool unordered_none_of(const Collection& collection, UnaryPred p) {
  auto&& ui = UnorderedIterable(collection);
  return std::none_of(ui.begin(), ui.end(), std::move(p));
}

template <class Collection, class UnaryFunc>
UnaryFunc unordered_for_each(const Collection& collection, UnaryFunc f) {
  auto&& ui = UnorderedIterable(collection);
  return std::for_each(ui.begin(), ui.end(), std::move(f));
}

template <class Collection, class OutputIt>
OutputIt unordered_copy(const Collection& collection, OutputIt target) {
  auto&& ui = UnorderedIterable(collection);
  return std::copy(ui.begin(), ui.end(), target);
}

template <class Collection, class OutputIt, class UnaryPred>
OutputIt unordered_copy_if(const Collection& collection,
                           OutputIt target,
                           UnaryPred pred) {
  auto&& ui = UnorderedIterable(collection);
  return std::copy_if(ui.begin(), ui.end(), target, std::move(pred));
}

template <class Collection, class T>
auto unordered_find(Collection& collection, const T& value) {
  auto&& ui = UnorderedIterable(collection);
  return unordered_to_fixed_iterator(collection,
                                     std::find(ui.begin(), ui.end(), value));
}

template <class Collection, class T>
auto unordered_find(const Collection& collection, const T& value) {
  auto&& ui = UnorderedIterable(collection);
  return unordered_to_fixed_iterator(collection,
                                     std::find(ui.begin(), ui.end(), value));
}

template <class Collection, class T, bool skip_assert = false>
auto unordered_find(Collection&& collection, const T& /*value*/) {
  static_assert(skip_assert,
                "find_if from an rvalue collection would return an "
                "undefined iterator");
  return collection.end();
}

template <class Collection, class UnaryPred>
auto unordered_find_if(Collection& collection, UnaryPred pred) {
  auto&& ui = UnorderedIterable(collection);
  return unordered_to_fixed_iterator(
      collection, std::find_if(ui.begin(), ui.end(), std::move(pred)));
}

template <class Collection, class UnaryPred>
auto unordered_find_if(const Collection& collection, UnaryPred pred) {
  auto&& ui = UnorderedIterable(collection);
  return unordered_to_fixed_iterator(
      collection, std::find_if(ui.begin(), ui.end(), std::move(pred)));
}

template <class Collection, class UnaryPred, bool skip_assert = false>
auto unordered_find_if(Collection&& collection, UnaryPred /*pred*/) {
  static_assert(skip_assert,
                "find_if from an rvalue collection would return an "
                "undefined iterator");
  return collection.end();
}

template <class Collection, class UnaryPred>
auto unordered_find_if_not(Collection& collection, UnaryPred pred) {
  auto&& ui = UnorderedIterable(collection);
  return unordered_to_fixed_iterator(
      collection, std::find_if_not(ui.begin(), ui.end(), std::move(pred)));
}

template <class Collection, class UnaryPred>
auto unordered_find_if_not(const Collection& collection, UnaryPred pred) {
  auto&& ui = UnorderedIterable(collection);
  return unordered_to_fixed_iterator(
      collection, std::find_if_not(ui.begin(), ui.end(), std::move(pred)));
}

template <class Collection, class UnaryPred, bool skip_assert = false>
auto unordered_find_if_not(Collection&& collection, UnaryPred /*pred*/) {
  static_assert(skip_assert,
                "find_if from an rvalue collection would return an "
                "undefined iterator");
  return collection.end();
}

template <class Collection, class T>
typename Collection::difference_type unordered_count(
    const Collection& collection, const T& value) {
  auto&& ui = UnorderedIterable(collection);
  return std::count(ui.begin(), ui.end(), value);
}

template <class Collection, class UnaryPred>
typename Collection::difference_type unordered_count_if(
    const Collection& collection, UnaryPred pred) {
  auto&& ui = UnorderedIterable(collection);
  return std::count_if(ui.begin(), ui.end(), std::move(pred));
}

template <class Collection>
auto unordered_min_element(Collection& collection) {
  static_assert(
      !std::is_pointer_v<typename Collection::value_type>,
      "unordered_min_element on raw pointers selects by address, which is "
      "non-deterministic across runs; pass an explicit comparator to the "
      "overload that takes one.");
  auto&& ui = UnorderedIterable(collection);
  return unordered_to_fixed_iterator(collection,
                                     std::min_element(ui.begin(), ui.end()));
}

template <class Collection>
auto unordered_min_element(const Collection& collection) {
  static_assert(
      !std::is_pointer_v<typename Collection::value_type>,
      "unordered_min_element on raw pointers selects by address, which is "
      "non-deterministic across runs; pass an explicit comparator to the "
      "overload that takes one.");
  auto&& ui = UnorderedIterable(collection);
  return unordered_to_fixed_iterator(collection,
                                     std::min_element(ui.begin(), ui.end()));
}

template <class Collection, bool skip_assert = false>
auto unordered_min_element(Collection&& collection) {
  static_assert(skip_assert,
                "min_element from an rvalue collection would return an "
                "undefined iterator");
  return collection.end();
}

template <class Collection, class Compare>
auto unordered_min_element(Collection& collection, Compare comp) {
  auto&& ui = UnorderedIterable(collection);
  return unordered_to_fixed_iterator(
      collection, std::min_element(ui.begin(), ui.end(), std::move(comp)));
}

template <class Collection, class Compare>
auto unordered_min_element(const Collection& collection, Compare comp) {
  auto&& ui = UnorderedIterable(collection);
  return unordered_to_fixed_iterator(
      collection, std::min_element(ui.begin(), ui.end(), std::move(comp)));
}

template <class Collection, class Compare, bool skip_assert = false>
auto unordered_min_element(Collection&& collection, Compare) {
  static_assert(skip_assert,
                "min_element from an rvalue collection would return an "
                "undefined iterator");
  return collection.end();
}

template <class Collection>
auto unordered_max_element(Collection& collection) {
  static_assert(
      !std::is_pointer_v<typename Collection::value_type>,
      "unordered_max_element on raw pointers selects by address, which is "
      "non-deterministic across runs; pass an explicit comparator to the "
      "overload that takes one.");
  auto&& ui = UnorderedIterable(collection);
  return unordered_to_fixed_iterator(collection,
                                     std::max_element(ui.begin(), ui.end()));
}

template <class Collection>
auto unordered_max_element(const Collection& collection) {
  static_assert(
      !std::is_pointer_v<typename Collection::value_type>,
      "unordered_max_element on raw pointers selects by address, which is "
      "non-deterministic across runs; pass an explicit comparator to the "
      "overload that takes one.");
  auto&& ui = UnorderedIterable(collection);
  return unordered_to_fixed_iterator(collection,
                                     std::max_element(ui.begin(), ui.end()));
}

template <class Collection, bool skip_assert = false>
auto unordered_max_element(Collection&& collection) {
  static_assert(skip_assert,
                "max_element from an rvalue collection would return an "
                "undefined iterator");
  return collection.end();
}

template <class Collection, class Compare>
auto unordered_max_element(Collection& collection, Compare comp) {
  auto&& ui = UnorderedIterable(collection);
  return unordered_to_fixed_iterator(
      collection, std::max_element(ui.begin(), ui.end(), std::move(comp)));
}

template <class Collection, class Compare>
auto unordered_max_element(const Collection& collection, Compare comp) {
  auto&& ui = UnorderedIterable(collection);
  return unordered_to_fixed_iterator(
      collection, std::max_element(ui.begin(), ui.end(), std::move(comp)));
}

template <class Collection, class Compare, bool skip_assert = false>
auto unordered_max_element(Collection&& collection, Compare) {
  static_assert(skip_assert,
                "max_element from an rvalue collection would return an "
                "undefined iterator");
  return collection.end();
}

template <class UnorderedCollection,
          typename Pred,
          std::enable_if_t<
              std::is_base_of_v<UnorderedBase<UnorderedCollection>,
                                UnorderedCollection> &&
                  !std::is_base_of_v<UnorderedBagBase, UnorderedCollection>,
              bool> = true>
size_t unordered_erase_if(UnorderedCollection& collection, const Pred& pred) {
  size_t removed = 0;
  auto&& ui = UnorderedIterable(collection);
  for (auto it = ui.begin(), end = ui.end(); it != end;) {
    if (pred(*it)) {
      it = ui.erase(it);
      removed++;
    } else {
      ++it;
    }
  }
  return removed;
}

template <class UnorderedCollection,
          typename Pred,
          std::enable_if_t<
              std::is_base_of_v<UnorderedBase<UnorderedCollection>,
                                UnorderedCollection> &&
                  std::is_base_of_v<UnorderedBagBase, UnorderedCollection>,
              bool> = true>
size_t unordered_erase_if(UnorderedCollection& collection, const Pred& pred) {
  auto& vec = unordered_unsafe_unwrap(collection);
  auto it = std::remove_if(vec.begin(), vec.end(), pred);
  auto removed = std::distance(it, vec.end());
  vec.erase(it, vec.end());
  return removed;
}

template <class Collection, class OutputIt, class UnaryOp>
OutputIt unordered_transform(const Collection& collection,
                             OutputIt target,
                             UnaryOp unary_op) {
  auto&& ui = UnorderedIterable(collection);
  return std::transform(ui.begin(), ui.end(), target, std::move(unary_op));
}

template <class Target, class Source>
void insert_unordered_iterable(Target& target, const Source& source) {
  auto&& ui = UnorderedIterable(source);
  target.insert(ui.begin(), ui.end());
}

template <class Target, class TargetIt, class Source>
void insert_unordered_iterable(Target& target,
                               const TargetIt& target_it,
                               const Source& source) {
  auto&& ui = UnorderedIterable(source);
  target.insert(target_it, ui.begin(), ui.end());
}

template <class Collection>
struct UnorderedMergeContainers {
  void operator()(const Collection& addend, Collection* accumulator) {
    insert_unordered_iterable(*accumulator, addend);
  }
};

// Order-independent (multiset) equality of two unordered collections of the
// same type: they are equal iff they hold the same elements with the same
// multiplicities, regardless of iteration order. Use this instead of `==` when
// comparing collections whose element order is non-deterministic (e.g.
// UnorderedBag, or the mapped values of a concurrent map).
//
// Default (hashing) form, O(n):
//  - For associative Unordered wrappers (UnorderedSet/UnorderedMap/
//    UnorderedMultiMap), whose own `operator==` is already order-independent,
//    this delegates to it (so it also works for maps, whose element type isn't
//    hashable).
//  - Otherwise (UnorderedBag, or a plain hashable sequence), it compares
//  element
//    multiplicities via a hash map, so it requires the element type to be
//    hashable and equality-comparable (pointers, ints, strings, ...). For
//    interned pointers (e.g. DexMethod*) this is pointer identity.
template <class Collection>
bool unordered_equal(const Collection& a, const Collection& b) {
  if constexpr (std::is_base_of_v<UnorderedBase<Collection>, Collection> &&
                !std::is_base_of_v<UnorderedBagBase, Collection>) {
    return a == b;
  } else {
    if (a.size() != b.size()) {
      return false;
    }
    UnorderedMap<typename Collection::value_type, size_t> counts;
    counts.reserve(a.size());
    for (const auto& x : UnorderedIterable(a)) {
      ++counts[x];
    }
    for (const auto& x : UnorderedIterable(b)) {
      auto it = counts.find(x);
      if (it == counts.end() || it->second == 0) {
        return false;
      }
      --it->second;
    }
    return true;
  }
}

// Comparator form, O(n log n): for element types that are orderable but not
// hashable, or when a specific canonical order is wanted. `comp` is a strict
// weak ordering over elements.
template <class Collection, class Compare>
bool unordered_equal(const Collection& a, const Collection& b, Compare comp) {
  if (a.size() != b.size()) {
    return false;
  }
  return unordered_to_ordered(a, comp) == unordered_to_ordered(b, comp);
}

// Default-constructible functor form of `unordered_equal`, for APIs that take
// an equality *type* rather than a callable -- e.g. the `ValueEqual` template
// parameter of `InsertOnlyConcurrentMap::get_or_create_and_assert_equal` when
// the mapped value is an unordered collection. `Compare = void` selects the
// hashing form; otherwise a default-constructed `Compare` selects the
// comparator form.
template <class Collection, class Compare = void>
struct UnorderedEqual {
  bool operator()(const Collection& a, const Collection& b) const {
    if constexpr (std::is_void_v<Compare>) {
      return unordered_equal(a, b);
    } else {
      return unordered_equal(a, b, Compare());
    }
  }
};
