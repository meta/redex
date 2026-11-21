/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <cstdlib>
#include <cstring>
#include <initializer_list>
#include <limits>
#include <memory>
#include <optional>
#include <string>
#include <utility>

#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexAccess.h"
#include "DexMemberRefs.h"
#include "NoDefaultComparator.h"
#include "ReferencedState.h"
#include "StringUtil.h"

/*
 * The structures defined here are literal representations
 * of what can be represented in a dex.  The main purpose of
 * the translations present here are to decouple the limitations
 * of "Idx" representation.  All of the "Idx"'s are indexes into
 * arrays of types in the dex format.  They are specific to each
 * dexfile.  So, we transform them in a way that we can load
 * multiple dexes in memory and compare them symbolically.
 *
 * In doing so, we enforce the uniqueness requirements of Idx's
 * within dexes.  There's only one DexString* with the same
 * set of characters.  Only one DexType* that has name "Foo;".
 * That simplifies the process of re-marshalling to dex after
 * we've completed whatever transforms we are going to do.
 *
 * UNIQUENESS:
 * The private constructor pattern enforces the uniqueness of
 * the pointer values of each type that has a uniqueness requirement.
 *
 *
 *
 * Gather methods:
 * Most `gather_X` methods are templated over the container type.
 * Currently only `std::vector` and `std::unordered_set` are supported.
 * The definitions are not in the header so as to avoid overly broad
 * imports.
 */

class DexAnnotationDirectory;
class DexAnnotationSet;
class DexCallSite;
class DexClass;
class DexDebugInstruction;
class DexEncodedValue;
class DexEncodedValueArray;
class DexField;
class DexIdx;
class DexInstruction;
class DexMethodHandle;
class DexMethodRef;
class DexOutputIdx;
struct DexPosition;
class DexProto;
class DexString;
class DexType;
class PositionMapper;
struct SourceBlock;

namespace source_debug_extension {
class SourceDebugExtension;
} // namespace source_debug_extension

struct dex_class_def;

// Must be same as in DexAnnotations.h!
using ParamAnnotations = std::map<int, std::unique_ptr<DexAnnotationSet>>;

constexpr bool kInsertDeobfuscatedNameLinks = false;

using Scope = std::vector<DexClass*>;

#if defined(__SSE4_2__) && defined(__linux__) && defined(__STRCMP_LESS__)
extern "C" bool strcmp_less(const char* str1, const char* str2);
#endif

// Internal representation of a DexString; used by RedexContext to construct
// DexString instances.
struct DexStringRepr {
  const char* storage;
  const uint32_t length;
  const uint32_t utfsize;
};

class DexString {
  // See UNIQUENESS above for the rationale for the private constructor pattern.
  explicit DexString(const char* storage, uint32_t length, uint32_t utfsize)
      : m_repr({storage, length, utfsize}) {}

 public:
  DexString() = delete;
  DexString(DexString&&) = delete;
  DexString(const DexString&) = delete;
  DexString& operator=(DexString&&) = delete;
  DexString& operator=(const DexString&) = delete;

  uint32_t size() const { return m_repr.length; }

  // UTF-aware length
  uint32_t length() const { return m_repr.utfsize; }

  int32_t java_hashcode() const;

  // DexString retrieval/creation

  // If the DexString exists, return it, otherwise create it and return it.
  // See also get_string()
  static const DexString* make_string(std::string_view nstr);

  // Return an existing DexString or nullptr if one does not exist.
  static const DexString* get_string(std::string_view s);

  static const std::string EMPTY;

  bool is_simple() const { return size() == m_repr.utfsize; }

  const char* c_str() const { return m_repr.storage; }
  std::string_view str() const {
    return std::string_view(m_repr.storage, m_repr.length);
  }
  std::string str_copy() const {
    return std::string(m_repr.storage, m_repr.length);
  }

  uint32_t get_entry_size() const;

  void encode(uint8_t* output) const;

 private:
  DexStringRepr m_repr;

  friend struct RedexContext;
};

namespace dexstrings::details {

bool compare_dexstrings_slowpath(const DexString* a, const DexString* b);

} // namespace dexstrings::details

/* Non-optimizing DexSpec compliant ordering */
inline bool compare_dexstrings(const DexString* a, const DexString* b) {
  if (a == nullptr) {
    return b != nullptr;
  } else if (b == nullptr) {
    return false;
  }
  if (a->is_simple() && b->is_simple()) {
#if defined(__SSE4_2__) && defined(__linux__) && defined(__STRCMP_LESS__)
    return strcmp_less(a->c_str(), b->c_str());
#else
    return (strcmp(a->c_str(), b->c_str()) < 0);
#endif
  }
  /*
   * Bother, need to do code-point character-by-character
   * comparison.
   */
  return dexstrings::details::compare_dexstrings_slowpath(a, b);
}

struct dexstrings_comparator {
  bool operator()(const DexString* a, const DexString* b) const {
    return compare_dexstrings(a, b);
  }
};

class DexType {
  friend struct RedexContext;

  const DexString* m_name;
  std::atomic<DexClass*> m_self{nullptr};

  // See UNIQUENESS above for the rationale for the private constructor pattern.
  explicit DexType(const DexString* dstring) { m_name = dstring; }

 public:
  DexType() = delete;
  DexType(DexType&&) = delete;
  DexType(const DexType&) = delete;
  DexType& operator=(DexType&&) = delete;
  DexType& operator=(const DexType&) = delete;

  // DexType retrieval/creation

  // If the DexType exists, return it, otherwise create it and return it.
  // See also get_type()
  static DexType* make_type(const DexString* dstring);

  static DexType* make_type(std::string_view str) {
    return make_type(DexString::make_string(str));
  }

  // Always makes a new type that is unique.
  static DexType* make_unique_type(const std::string_view type_name) {
    const auto* ret = DexString::make_string(type_name);
    for (uint32_t i = 0; get_type(ret) != nullptr; i++) {
      ret = DexString::make_string(type_name.substr(0, type_name.size() - 1) +
                                   "r$" + std::to_string(i) + ";");
    }
    return make_type(ret);
  }

  // Return an existing DexType or nullptr if one does not exist.
  static DexType* get_type(const DexString* dstring);

  static DexType* get_type(std::string_view str) {
    return get_type(DexString::get_string(str));
  }

  void set_name(const DexString* new_name);

  const DexString* get_name() const { return m_name; }
  const char* c_str() const { return get_name()->c_str(); }
  std::string_view str() const { return get_name()->str(); }
  std::string str_copy() const { return get_name()->str_copy(); }
  DexProto* get_non_overlapping_proto(const DexString*, DexProto*);
  DexType* to_mutable() const {
    // This method can be implemented without const_cast:
    //   return DexType::get_type(this->get_name());
    // But this doesn't make sense performance wise, and the return value is
    // always the same. For this reason, the constness of DexType doesn't make a
    // difference in redex in terms of constness safety.
    //
    // Rather than letting const_cast scatter everywhere, we contain the
    // const_cast call here -- const_cast can now remain a red flag of code
    // correctness.
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-const-cast)
    return const_cast<DexType*>(this);
  }
};

/* Non-optimizing DexSpec compliant ordering */
inline bool compare_dextypes(const DexType* a, const DexType* b) {
  return compare_dexstrings(a->get_name(), b->get_name());
}

struct dextypes_comparator {
  bool operator()(const DexType* a, const DexType* b) const {
    return compare_dextypes(a, b);
  }
};

/**
 * A DexFieldRef is a reference to a DexField.
 * A reference may or may not map to a definition.
 * Consider the following:
 * class A { public int i; }
 * class B extends A {}
 * B b = ...;
 * b.i = 0;
 * the code compiles to
 * iput v0, v1 LB;.i:I
 * B.i does not exist and it's a reference.
 * The type of the reference is effectively the scope where resolution starts.
 * DexFieldRef are never really materialized and everything is a DexField.
 * The API however returns DexFieldRef for references thus imposing some
 * kind of resolution to get to a definition if needed.
 */
class DexFieldRef {
  friend struct RedexContext;
  friend class DexClass;

 protected:
  DexFieldSpec m_spec;
  bool m_concrete;
  bool m_external;

  virtual ~DexFieldRef() = default;
  DexFieldRef(DexType* container, const DexString* name, DexType* type) {
    m_spec.cls = container;
    m_spec.name = name;
    m_spec.type = type;
    m_concrete = false;
    m_external = false;
  }

 public:
  DexFieldRef() = delete;
  DexFieldRef(DexFieldRef&&) = delete;
  DexFieldRef(const DexFieldRef&) = delete;
  DexFieldRef& operator=(DexFieldRef&&) = delete;
  DexFieldRef& operator=(const DexFieldRef&) = delete;

  bool is_concrete() const { return m_concrete; }
  bool is_external() const { return m_external; }
  bool is_def() const { return is_concrete() || is_external(); }
  const DexField* as_def() const;
  DexField* as_def();

  DexType* get_class() const { return m_spec.cls; }
  const DexString* get_name() const { return m_spec.name; }
  const char* c_str() const { return get_name()->c_str(); }
  std::string_view str() const { return get_name()->str(); }
  std::string str_copy() const { return get_name()->str_copy(); }
  DexType* get_type() const { return m_spec.type; }

  template <typename C>
  void gather_types_shallow(C& ltype) const;
  void gather_strings_shallow(std::vector<const DexString*>& lstring) const;
  void gather_strings_shallow(UnorderedSet<const DexString*>& lstring) const;

  void change(const DexFieldSpec& ref, bool rename_on_collision = false);

  DexField* make_concrete(DexAccessFlags access_flags);
  DexField* make_concrete(DexAccessFlags access_flags,
                          std::unique_ptr<DexEncodedValue> v);

  static void erase_field(DexFieldRef* f);

  dex_member_refs::FieldDescriptorTokens get_descriptor_tokens() const;

  // This method frees the given `DexFieldRef` - different from `erase_field`,
  // which only removes the field from the `RedexContext`.
  //
  // BE SURE YOU REALLY WANT TO DO THIS! Many Redex passes and structures
  // currently cache references and do not clean up, including global ones.
  static void delete_field_DO_NOT_USE(DexFieldRef* field);
};

class DexField : public DexFieldRef {
  friend struct RedexContext;
  friend class DexFieldRef;

  /* Concrete method members */
  DexAccessFlags m_access;
  std::unique_ptr<DexAnnotationSet> m_anno;
  std::unique_ptr<DexEncodedValue> m_value; /* Static Only */
  std::string m_deobfuscated_name;

  // See UNIQUENESS above for the rationale for the private constructor pattern.
  DexField(DexType* container, const DexString* name, DexType* type);

  std::string self_show() const; // To avoid "Show.h" in the header.

 public:
  DexField() = delete;
  DexField(DexField&&) = delete;
  DexField(const DexField&) = delete;
  ~DexField();

  // For friend classes to use with smart pointers.
  struct Deleter {
    void operator()(DexField* f) { delete f; }
  };

  ReferencedState rstate =
      ReferencedState(RefStateType::FieldState); // Tracks whether this field
                                                 // can be deleted or renamed

  // DexField retrieval/creation

  // If the DexField exists, return it, otherwise create it and return it.
  // See also get_field()
  static DexFieldRef* make_field(const DexType* container,
                                 const DexString* name,
                                 const DexType* type);

  // Return an existing DexField or nullptr if one does not exist.
  static DexFieldRef* get_field(const DexType* container,
                                const DexString* name,
                                const DexType* type);

  static DexFieldRef* get_field(const dex_member_refs::FieldDescriptorTokens&);

  /**
   * Get a field using a full descriptor: Lcls;.name:type
   */
  static DexFieldRef* get_field(std::string_view);

  /**
   * Make a field using a full descriptor: Lcls;.name:type
   */
  static DexFieldRef* make_field(std::string_view);

  static const DexString* get_unique_name(DexType* container,
                                          const DexString* name,
                                          DexType* type) {
    const auto* ret = name;
    for (uint32_t i = 0; get_field(container, ret, type) != nullptr; i++) {
      ret = DexString::make_string(name->str() + "r$" + std::to_string(i));
    }
    return ret;
  }

  DexAnnotationSet* get_anno_set() const { return m_anno.get(); }
  DexEncodedValue* get_static_value() const { return m_value.get(); }
  DexAccessFlags get_access() const {
    always_assert(is_def());
    return m_access;
  }

  void set_access(DexAccessFlags access) {
    always_assert_log(!m_external, "Unexpected external field %s\n",
                      self_show().c_str());
    m_access = access;
  }

  void set_external();

  void set_deobfuscated_name(std::string name) {
    m_deobfuscated_name = std::move(name);
  }
  const std::string& get_deobfuscated_name() const {
    return m_deobfuscated_name;
  }
  const std::string& get_deobfuscated_name_or_empty() const {
    return m_deobfuscated_name;
  }

  // Return just the name of the field.
  std::string get_simple_deobfuscated_name() const;

  void set_value(std::unique_ptr<DexEncodedValue> v);

  std::unique_ptr<DexAnnotationSet> release_annotations();
  void clear_annotations();

  [[nodiscard]] bool attach_annotation_set(
      std::unique_ptr<DexAnnotationSet> aset);

  template <typename C>
  void gather_types(C& ltype) const;
  void gather_strings(std::vector<const DexString*>& lstring) const;
  void gather_strings(UnorderedSet<const DexString*>& lstring) const;
  template <typename C>
  void gather_fields(C& lfield) const;
  template <typename C>
  void gather_methods(C& lmethod) const;

 private:
  template <typename C>
  void gather_strings_internal(C& lstring) const;
};

/* Non-optimizing DexSpec compliant ordering */
inline bool compare_dexfields(const DexFieldRef* a, const DexFieldRef* b) {
  if (a == nullptr) {
    return b != nullptr;
  } else if (b == nullptr) {
    return false;
  }
  if (a->get_class() != b->get_class()) {
    return compare_dextypes(a->get_class(), b->get_class());
  }
  if (a->get_name() != b->get_name()) {
    return compare_dexstrings(a->get_name(), b->get_name());
  }
  return compare_dextypes(a->get_type(), b->get_type());
}

struct dexfields_comparator {
  bool operator()(const DexFieldRef* a, const DexFieldRef* b) const {
    return compare_dexfields(a, b);
  }
};

class DexTypeList {
 public:
  using ContainerType = std::vector<const DexType*>;

  using value_type = const DexType*;
  using iterator = typename ContainerType::iterator;
  using const_iterator = typename ContainerType::const_iterator;

  const_iterator begin() const { return m_list.begin(); }
  const_iterator end() const { return m_list.end(); }

  size_t size() const { return m_list.size(); }
  bool empty() const { return m_list.empty(); }

  const DexType* at(size_t i) const { return m_list.at(i); }

  // DexTypeList retrieval/creation

  // If the DexTypeList exists, return it, otherwise create it and return it.
  // See also get_type_list()
  static DexTypeList* make_type_list(ContainerType&& p);

  // Return an existing DexTypeList or nullptr if one does not exist.
  static DexTypeList* get_type_list(const ContainerType& p);

  /**
   * Returns size of the encoded typelist in bytes, input
   * pointer must be aligned.
   */
  int encode(DexOutputIdx* dodx, uint32_t* output) const;

  friend bool operator<(const DexTypeList& a, const DexTypeList& b) {
    auto ita = a.m_list.begin();
    auto itb = b.m_list.begin();
    while (true) {
      if (itb == b.m_list.end()) {
        return false;
      }
      if (ita == a.m_list.end()) {
        return true;
      }
      if (*ita != *itb) {
        const DexType* ta = *ita;
        const DexType* tb = *itb;
        return compare_dextypes(ta, tb);
      }
      ita++;
      itb++;
    }
  }

  template <typename C>
  void gather_types(C& ltype) const;

  bool equals(const std::vector<const DexType*>& vec) const {
    return std::equal(m_list.begin(), m_list.end(), vec.begin(), vec.end());
  }

  DexTypeList* push_front(const DexType* t) const;
  DexTypeList* pop_front() const;
  DexTypeList* pop_front(size_t n) const;
  DexTypeList* pop_back(size_t n) const;

  DexTypeList* push_back(const DexType* t) const;
  DexTypeList* push_back(const std::vector<const DexType*>& t) const;

  DexTypeList* replace_head(const DexType* new_head) const;

 private:
  // See UNIQUENESS above for the rationale for the private constructor pattern.
  explicit DexTypeList(ContainerType list) : m_list(std::move(list)) {}

  const ContainerType m_list;

  friend struct RedexContext;
};

inline bool compare_dextypelists(const DexTypeList* a, const DexTypeList* b) {
  if (a == nullptr) {
    return b != nullptr;
  } else if (b == nullptr) {
    return false;
  }
  return *a < *b;
}

struct dextypelists_comparator {
  bool operator()(const DexTypeList* a, const DexTypeList* b) const {
    return compare_dextypelists(a, b);
  }
};

class DexProto {
  friend struct RedexContext;

  DexTypeList* m_args;
  DexType* m_rtype;
  const DexString* m_shorty;

  // See UNIQUENESS above for the rationale for the private constructor pattern.
  DexProto(DexType* rtype, DexTypeList* args, const DexString* shorty) {
    m_rtype = rtype;
    m_args = args;
    m_shorty = shorty;
  }

 public:
  DexProto() = delete;
  DexProto(DexProto&&) = delete;
  DexProto(const DexProto&) = delete;
  DexProto& operator=(DexProto&&) = delete;
  DexProto& operator=(const DexProto&) = delete;

  // DexProto retrieval/creation

  // If the DexProto exists, return it, otherwise create it and return it.
  // See also get_proto()
  static DexProto* make_proto(const DexType* rtype,
                              const DexTypeList* args,
                              const DexString* shorty);

  static DexProto* make_proto(const DexType* rtype, const DexTypeList* args);

  // The proto of a descriptor such as "(I[Ljava/lang/String;)V".
  static DexProto* make_proto(std::string_view descriptor);

  // Return an existing DexProto or nullptr if one does not exist.
  static DexProto* get_proto(const DexType* rtype, const DexTypeList* args);

  DexType* get_rtype() const { return m_rtype; }
  DexTypeList* get_args() const { return m_args; }
  const DexString* get_shorty() const { return m_shorty; }
  bool is_void() const;

  template <typename C>
  void gather_types(C& ltype) const;
  void gather_strings(std::vector<const DexString*>& lstring) const;
  void gather_strings(UnorderedSet<const DexString*>& lstring) const;
};

/* Non-optimizing DexSpec compliant ordering */
inline bool compare_dexprotos(const DexProto* a, const DexProto* b) {
  if (a == nullptr) {
    return b != nullptr;
  } else if (b == nullptr) {
    return false;
  }
  if (a->get_rtype() != b->get_rtype()) {
    return compare_dextypes(a->get_rtype(), b->get_rtype());
  }
  return (*(a->get_args()) < *(b->get_args()));
}

struct dexprotos_comparator {
  bool operator()(const DexProto* a, const DexProto* b) const {
    return compare_dexprotos(a, b);
  }
};

struct DebugLineItem {
  uint32_t offset;
  uint32_t line;
  DebugLineItem(uint32_t offset, uint32_t line) : offset(offset), line(line) {}
};

/*
 * Dex files encode debug information as a series of opcodes. Internally, we
 * convert the opcodes that delta-encode position into absolute DexPositions.
 * The other opcodes get passed directly through.
 */
enum class DexDebugEntryType { Instruction, Position };

enum class PerfSensitiveGroup : uint8_t {
  NONE,
  BETAMAP_ORDERED,
  OUTLINED,
  STRINGS_LOOKUP,
  UNREACHABLE,
};

struct DexDebugEntry final {
  DexDebugEntryType type;
  uint32_t addr;
  union {
    std::unique_ptr<DexPosition> pos;
    std::unique_ptr<DexDebugInstruction> insn;
  };
  DexDebugEntry(uint32_t addr, std::unique_ptr<DexPosition> pos);
  DexDebugEntry(uint32_t addr, std::unique_ptr<DexDebugInstruction> insn);
  // should only be copied via DexDebugItem's copy ctor, which is responsible
  // for remapping DexPositions' parent pointer
  DexDebugEntry(const DexDebugEntry&) = delete;
  DexDebugEntry(DexDebugEntry&& other) noexcept;
  ~DexDebugEntry();
  void gather_strings(std::vector<const DexString*>& lstring) const;
  void gather_types(std::vector<const DexType*>& ltype) const;
};

class DexDebugItem {
  std::vector<const DexString*> m_param_names;
  std::vector<DexDebugEntry> m_dbg_entries;
  uint32_t m_on_disk_size{0};
  uint32_t m_source_checksum{0};
  uint32_t m_source_offset{0};
  DexDebugItem(DexIdx* idx, uint32_t offset);

 public:
  DexDebugItem() = default;
  DexDebugItem(const DexDebugItem&);
  static std::unique_ptr<DexDebugItem> get_dex_debug(DexIdx* idx,
                                                     uint32_t offset);
  std::vector<DexDebugEntry>& get_entries() { return m_dbg_entries; }
  const auto& get_entries() const { return m_dbg_entries; }
  void set_entries(std::vector<DexDebugEntry> dbg_entries) {
    m_dbg_entries.swap(dbg_entries);
  }
  uint32_t get_line_start() const;
  const std::vector<const DexString*>& get_param_names() const {
    return m_param_names;
  }
  uint32_t get_on_disk_size() const { return m_on_disk_size; }
  uint32_t get_source_checksum() const { return m_source_checksum; }
  uint32_t get_source_offset() const { return m_source_offset; }
  void bind_positions(DexMethod* method,
                      const DexString* file,
                      const source_debug_extension::SourceDebugExtension*
                          source_debug_extension);

  // Upper bound on the bytes `encode` writes. Computable before the write,
  // which is what lets DexOutput check that the item fits.
  static size_t max_encoded_size(
      uint32_t num_params,
      const std::vector<std::unique_ptr<DexDebugInstruction>>& dbgops);

  /* Returns number of bytes encoded, *output has no alignment requirements */
  static int encode(
      DexOutputIdx* dodx,
      uint8_t* output,
      uint32_t line_start,
      uint32_t num_params,
      const std::vector<std::unique_ptr<DexDebugInstruction>>& dbgops);

  void gather_types(std::vector<const DexType*>& ltype) const;
  void gather_strings(std::vector<const DexString*>& lstring) const;
};

std::vector<std::unique_ptr<DexDebugInstruction>> generate_debug_instructions(
    DexDebugItem* debugitem,
    PositionMapper* pos_mapper,
    uint32_t* line_start,
    std::vector<DebugLineItem>* line_info,
    uint32_t line_addin);

using DexCatches = std::vector<std::pair<DexType*, uint32_t>>;

struct DexTryItem {
  uint32_t m_start_addr;
  uint16_t m_insn_count;
  DexCatches m_catches;
  DexTryItem(uint32_t start_addr, uint32_t insn_count)
      : m_start_addr(start_addr) {
    always_assert_log(insn_count <= std::numeric_limits<uint16_t>::max(),
                      "too many instructions in a single try region %u > 2^16",
                      insn_count);
    m_insn_count = insn_count;
  }
};

class IRCode;

struct DexInvokeId {
  bool invoke_interface;
  DexMethodRef* method;
  std::unique_ptr<DexPosition> position;
  std::unique_ptr<SourceBlock> src_block;

  DexInvokeId(bool invoke_interface,
              DexMethodRef* method,
              DexPosition* position,
              SourceBlock* src_block);
  DexInvokeId(DexInvokeId&&) = default;
  DexInvokeId& operator=(DexInvokeId&&) = default;
  DexInvokeId(const DexInvokeId&) = delete;
  DexInvokeId& operator=(const DexInvokeId&) = delete;

  ~DexInvokeId();
};

class DexCode {
  friend class DexMethod;

  uint16_t m_registers_size;
  uint16_t m_ins_size;
  uint16_t m_outs_size;
  std::optional<std::vector<DexInstruction*>> m_insns{std::nullopt};
  std::vector<std::unique_ptr<DexTryItem>> m_tries;
  std::vector<std::pair<uint32_t, DexInvokeId>> m_invoke_ids;
  std::unique_ptr<DexDebugItem> m_dbg;

 public:
  static std::unique_ptr<DexCode> get_dex_code(DexIdx* idx, uint32_t offset);

  // TODO: make it private and find a better way to allow code creation
  DexCode()
      : m_registers_size(0),
        m_ins_size(0),
        m_outs_size(0),
        m_insns(std::vector<DexInstruction*>()),
        m_dbg(nullptr) {}

  DexCode(const DexCode&);

  ~DexCode();

  const DexDebugItem* get_debug_item() const { return m_dbg.get(); }
  void set_debug_item(std::unique_ptr<DexDebugItem> dbg) {
    m_dbg = std::move(dbg);
  }
  DexDebugItem* get_debug_item() { return m_dbg.get(); }
  std::unique_ptr<DexDebugItem> release_debug_item() {
    return std::move(m_dbg);
  }
  std::vector<DexInstruction*> release_instructions() {
    redex_assert(m_insns);
    auto ret = std::move(*m_insns);
    m_insns = std::nullopt;
    return ret;
  }
  std::vector<DexInstruction*>& reset_instructions() {
    m_insns = std::vector<DexInstruction*>{};
    return *m_insns;
  }
  std::vector<DexInstruction*>& get_instructions() {
    redex_assert(m_insns);
    return *m_insns;
  }
  const std::vector<DexInstruction*>& get_instructions() const {
    redex_assert(m_insns);
    return *m_insns;
  }
  void set_instructions(std::vector<DexInstruction*> insns) {
    m_insns.emplace(std::move(insns));
  }
  std::vector<std::unique_ptr<DexTryItem>>& get_tries() { return m_tries; }
  const std::vector<std::unique_ptr<DexTryItem>>& get_tries() const {
    return m_tries;
  }
  uint16_t get_registers_size() const { return m_registers_size; }
  uint16_t get_ins_size() const { return m_ins_size; }
  uint16_t get_outs_size() const { return m_outs_size; }

  void set_registers_size(uint16_t sz) { m_registers_size = sz; }
  void set_ins_size(uint16_t sz) { m_ins_size = sz; }
  void set_outs_size(uint16_t sz) { m_outs_size = sz; }

  auto& get_invoke_ids() { return m_invoke_ids; }
  /*
   * Returns number of bytes in encoded output, passed in
   * pointer must be aligned.  Does not encode debugitem,
   * that must be done later.
   */
  int encode(DexOutputIdx* dodx, uint32_t* output);

  // Upper bound on the bytes `encode` writes. Note this is NOT `size()`, which
  // filters fopcodes and so under-counts every switch and array-data payload;
  // `encode` emits them. Computable before the write, which is what lets
  // DexOutput check that the item fits.
  size_t max_encoded_size() const;

  /*
   * Returns the number of 2-byte code units needed to encode all the
   * instructions.
   */
  uint32_t size() const;

  friend std::string show(const DexCode*);
};

/**
 * A DexMethodRef is a reference to a DexMethod.
 * A reference may or may not map to a definition.
 * Consider the following:
 * class A { public void m() {} }
 * class B extends A {}
 * B b = ...;
 * b.m();
 * the code compiles to
 * invoke-virtual {v0} LB;.m:()V
 * B.m() does not exist and it's a reference.
 * The type of the reference is effectively the scope where resolution starts.
 * DexMethodRef are never really materialized and everything is a DexMethod.
 * The API however returns DexMethodRef for references thus imposing some
 * kind of resolution to get to a definition if needed.
 */
class DexMethodRef {
  friend struct RedexContext;
  friend class DexClass;

 protected:
  DexMethodSpec m_spec;
  bool m_concrete;
  bool m_external;

  virtual ~DexMethodRef() = default;
  DexMethodRef(DexType* type, const DexString* name, DexProto* proto)
      : m_spec(type, name, proto) {
    m_concrete = false;
    m_external = false;
  }

 public:
  DexMethodRef() = delete;
  DexMethodRef(DexMethodRef&&) = delete;
  DexMethodRef(const DexMethodRef&) = delete;
  DexMethodRef& operator=(DexMethodRef&&) = delete;
  DexMethodRef& operator=(const DexMethodRef&) = delete;

  bool is_concrete() const { return m_concrete; }
  bool is_external() const { return m_external; }
  bool is_def() const { return is_concrete() || is_external(); }
  const DexMethod* as_def() const;
  DexMethod* as_def();

  DexType* get_class() const { return m_spec.cls; }
  const DexString* get_name() const { return m_spec.name; }
  const char* c_str() const { return get_name()->c_str(); }
  std::string_view str() const { return get_name()->str(); }
  std::string str_copy() const { return get_name()->str_copy(); }
  DexProto* get_proto() const { return m_spec.proto; }

  template <typename C>
  void gather_types_shallow(C& ltype) const;
  void gather_strings_shallow(std::vector<const DexString*>& lstring) const;
  void gather_strings_shallow(UnorderedSet<const DexString*>& lstring) const;

  void change(const DexMethodSpec& ref, bool rename_on_collision);

  DexMethod* make_concrete(DexAccessFlags,
                           std::unique_ptr<DexCode>,
                           bool is_virtual);

  DexMethod* make_concrete(DexAccessFlags,
                           std::unique_ptr<IRCode>,
                           bool is_virtual);

  DexMethod* make_concrete(DexAccessFlags access, bool is_virtual);

  // This only removes the given method reference from the `RedexContext`, but
  // does not free the method.
  static void erase_method(DexMethodRef* mref);

  // This method frees the given `DexMethod` - different from `erase_method`,
  // which only removes the method from the `RedexContext`.
  //
  // BE SURE YOU REALLY WANT TO DO THIS! Many Redex passes and structures
  // currently cache references and do not clean up, including global ones like
  // `MethodProfiles` which maps `DexMethodRef`s to data.
  static void delete_method_DO_NOT_USE(DexMethodRef* method);

  // This method currently does *NOT* free the `DexMethod`, as there may still
  // be references. This will free most resources associated with the
  // DexMethod, though. Eventually this will become a full delete. For now, the
  // leaked methods are registered with the RedexContext for tracking.
  static void delete_method(DexMethodRef* method);

  dex_member_refs::MethodDescriptorTokens get_descriptor_tokens() const;

  static bool is_valid_name(std::string_view name);
};

class DexMethod : public DexMethodRef {
  friend struct RedexContext;
  friend class DexMethodRef;

  /* Concrete method members */

  // Place these first to avoid/fill padding from DexMethodRef.
  bool m_virtual{false};
  DexAccessFlags m_access;

  std::unique_ptr<DexAnnotationSet> m_anno;
  std::unique_ptr<DexCode> m_dex_code;
  std::unique_ptr<IRCode> m_code;
  std::unique_ptr<ParamAnnotations> m_param_anno;
  const DexString* m_deobfuscated_name{nullptr};

  // See UNIQUENESS above for the rationale for the private constructor pattern.
  DexMethod(DexType* type, const DexString* name, DexProto* proto);
  ~DexMethod();

  // For friend classes to use with smart pointers.
  struct Deleter {
    void operator()(DexMethod* m) { delete m; }
  };

  std::string self_show() const; // To avoid "Show.h" in the header.

 public:
  DexMethod() = delete;
  DexMethod(DexMethodRef&&) = delete;
  DexMethod(const DexMethodRef&) = delete;

  // Tracks whether this method can be deleted or renamed
  ReferencedState rstate = ReferencedState(RefStateType::MethodState);

  // DexMethod retrieval/creation

  // If the DexMethod exists, return it, otherwise create it and return it.
  // See also get_method()
  static DexMethodRef* make_method(const DexType* type,
                                   const DexString* name,
                                   const DexProto* proto);

  static DexMethodRef* make_method(const DexMethodSpec& spec);

  // Similar to make_method but return DexMethod* instead of DexMethodRef*.
  // Use those only if you are expecting a DexMethod* not a DexMethodRef*
  // because these methods do runtime check with dynamic_cast.
  static DexMethod* make_method_downcast(const DexType* type,
                                         const DexString* name,
                                         const DexProto* proto);

  static DexMethod* make_method_downcast(const DexMethodSpec& spec);

  /**
   * Create a copy of method `that`. This excludes `rstate`.
   */
  static DexMethod* make_method_from(DexMethod* that,
                                     DexType* target_cls,
                                     const DexString* name);
  // Make a copy of method `that`, including the `rstate`.
  static DexMethod* make_full_method_from(DexMethod* that,
                                          DexType* target_cls,
                                          const DexString* name);

  /**
   * This creates everything along the chain of Dex<Member>, so it should
   * be used for members that either exist or would be created anyway.
   */
  static DexMethodRef* make_method(const char* cls_name,
                                   const char* meth_name,
                                   const char* rtype_str,
                                   const std::vector<const char*>& arg_strs) {
    DexType* cls = DexType::make_type(cls_name);
    const auto* name = DexString::make_string(meth_name);
    DexType* rtype = DexType::make_type(rtype_str);
    DexTypeList::ContainerType args;
    for (const auto* const arg_str : arg_strs) {
      DexType* arg = DexType::make_type(arg_str);
      args.push_back(arg);
    }
    DexTypeList* dtl = DexTypeList::make_type_list(std::move(args));
    return make_method(cls, name, DexProto::make_proto(rtype, dtl));
  }

  /**
   * Creates a method reference from its signature given as a collection of
   * strings.
   */
  static DexMethodRef* make_method(const std::string& class_type,
                                   const std::string& name,
                                   std::initializer_list<std::string> arg_types,
                                   const std::string& return_type);

  static DexMethodRef* get_method(
      const dex_member_refs::MethodDescriptorTokens&);

  /**
   * Get a method using a full descriptor: Lcls;.name:(args)rtype
   *
   * When `kCheckFormat` = true, syntactical issues in the string
   * will lead to asserts, i.e., throws.
   */
  template <bool kCheckFormat = false>
  static DexMethodRef* get_method(std::string_view);

  /**
   * Make a method using a full descriptor: Lcls;.name:(args)rtype
   */
  static DexMethodRef* make_method(std::string_view);

  // Return an existing DexMethod or nullptr if one does not exist.
  static DexMethodRef* get_method(const DexType* type,
                                  const DexString* name,
                                  const DexProto* proto);

  static DexMethodRef* get_method(const DexMethodSpec& spec);

  static const DexString* get_unique_name(DexType* type,
                                          const DexString* name,
                                          DexProto* proto) {
    const auto* ret = name;
    for (uint32_t i = 0; get_method(type, ret, proto) != nullptr; i++) {
      ret = DexString::make_string(name->str() + "r$" + std::to_string(i));
    }
    return ret;
  }

  const DexAnnotationSet* get_anno_set() const { return m_anno.get(); }
  DexAnnotationSet* get_anno_set() { return m_anno.get(); }
  const DexCode* get_dex_code() const { return m_dex_code.get(); }
  DexCode* get_dex_code() { return m_dex_code.get(); }
  IRCode* get_code() { return m_code.get(); }
  const IRCode* get_code() const { return m_code.get(); }
  std::unique_ptr<IRCode> release_code();
  bool is_virtual() const { return m_virtual; }
  DexAccessFlags get_access() const {
    always_assert(is_def());
    return m_access;
  }
  const ParamAnnotations* get_param_anno() const { return m_param_anno.get(); }
  ParamAnnotations* get_param_anno() { return m_param_anno.get(); }
  std::unique_ptr<ParamAnnotations> release_param_anno();

  void set_deobfuscated_name(const std::string& name);
  void set_deobfuscated_name(const DexString* name);
  void set_deobfuscated_name(const DexString& name);

  const DexString& get_deobfuscated_name() const {
    redex_assert(m_deobfuscated_name != nullptr);
    return *m_deobfuscated_name;
  }
  const DexString* get_deobfuscated_name_or_null() const {
    return m_deobfuscated_name;
  }
  std::string_view get_deobfuscated_name_or_empty() const {
    if (m_deobfuscated_name == nullptr) {
      return DexString::EMPTY;
      ;
    }
    return m_deobfuscated_name->str();
  }
  std::string get_deobfuscated_name_or_empty_copy() const {
    return ::str_copy(get_deobfuscated_name_or_empty());
  }

  // Return just the name of the method.
  std::string get_simple_deobfuscated_name() const;

  // Return a really fully deobfuscated name, even for a generated method.
  // TODO(redex): this can be removed now.
  std::string get_fully_deobfuscated_name() const;

  void set_access(DexAccessFlags access) {
    always_assert_log(!m_external, "Unexpected external method %s\n",
                      self_show().c_str());
    m_access = access;
  }

  void set_virtual(bool is_virtual) {
    always_assert_log(!m_external, "Unexpected external method %s\n",
                      self_show().c_str());
    m_virtual = is_virtual;
  }

  void set_external();
  void set_dex_code(std::unique_ptr<DexCode> code) {
    m_dex_code = std::move(code);
  }
  void set_code(std::unique_ptr<IRCode> code);

  void make_non_concrete();

  void become_virtual();
  std::unique_ptr<DexAnnotationSet> release_annotations();
  void clear_annotations();

  /**
   * Note that this is to combine annotation for two methods that should
   * have same set of parameters. This is used in vertical merging when
   * merging parent and child's inherited method. If you want to use this
   * method you should check if their protos are the same before using this.
   */
  void combine_annotations_with(DexMethod* other);

  void add_load_params(size_t num_add_loads);
  [[nodiscard]] bool attach_annotation_set(
      std::unique_ptr<DexAnnotationSet> aset);
  void attach_param_annotation_set(int paramno,
                                   std::unique_ptr<DexAnnotationSet> aset);

  template <typename C>
  void gather_types(C& ltype) const;
  template <typename C>
  void gather_fields(C& lfield) const;
  template <typename C>
  void gather_methods(C& lmethod) const;
  template <typename C>
  void gather_methods_from_annos(C& lmethod) const;
  void gather_strings(std::vector<const DexString*>& lstring,
                      bool exclude_loads = false) const;
  void gather_strings(UnorderedSet<const DexString*>& lstring,
                      bool exclude_loads = false) const;
  template <typename C>
  void gather_callsites(C& lcallsite) const;
  template <typename C>
  void gather_protos(C& lproto) const;
  template <typename C>
  void gather_methodhandles(C& lmethodhandle) const;

  void gather_init_classes(std::vector<const DexType*>& ltype) const;

  /*
   * DexCode <-> IRCode conversion methods.
   *
   * In general DexCode is only used in the load / output phases, and in tests
   * when we wish to verify that we have generated specific instructions.
   *
   * Most operations can and should use IRCode. Optimizations should never
   * have to call sync().
   */
  void balloon();
  void sync();

 private:
  template <typename C>
  void gather_strings_internal(C& lstring, bool exclude_loads) const;
};

using dexcode_to_offset = UnorderedMap<DexCode*, uint32_t>;

class DexLocation {
  friend struct RedexContext;

 private:
  std::string m_store_name;
  std::string m_file_name;
  DexLocation(std::string m_store_name, std::string m_file_name);

 public:
  // If the DexLocation exists, return it, otherwise create it and return
  // it. See also get_()
  static const DexLocation* make_location(std::string_view store_name,
                                          std::string_view file_name);

  // Return an existing DexLocation or nullptr if one does not exist.
  static const DexLocation* get_location(std::string_view store_name,
                                         std::string_view file_name);

  const std::string& get_store_name() const { return m_store_name; }
  // Returns the location of this class - can be dex/jar file.
  const std::string& get_file_name() const { return m_file_name; }
};

class DexClass {
 private:
  DexType* m_super_class;
  DexType* m_self;
  DexTypeList* m_interfaces;
  const DexString* m_source_file;
  std::unique_ptr<DexAnnotationSet> m_anno;
  const DexString* m_deobfuscated_name{nullptr};
  const DexLocation* m_location{nullptr};
  std::vector<DexField*> m_sfields;
  std::vector<DexField*> m_ifields;
  std::vector<DexMethod*> m_dmethods;
  std::vector<DexMethod*> m_vmethods;
  DexAccessFlags m_access_flags;
  bool m_external;
  PerfSensitiveGroup m_perf_sensitive;
  bool m_dynamically_dead;

  DexClass(DexType* type, const DexLocation* location);
  void load_class_annotations(DexIdx* idx, uint32_t anno_off);
  void load_class_data_item(DexIdx* idx,
                            uint32_t cdi_off,
                            std::unique_ptr<DexEncodedValueArray> svalues);

  friend struct ClassCreator;

  // This constructor is private on purpose, use DexClass::create instead
  DexClass(DexType* super_type,
           DexType* self_type,
           DexTypeList* interfaces,
           const DexString* source_file,
           const DexLocation* location,
           DexAccessFlags access_flags);

  std::string self_show() const; // To avoid "Show.h" in the header.

 public:
  ReferencedState rstate = ReferencedState(RefStateType::ClassState);

  ~DexClass();

  // May return nullptr on benign duplicate class
  static DexClass* create(DexIdx* idx,
                          const dex_class_def* cdef,
                          const DexLocation* location);

  const std::vector<DexMethod*>& get_dmethods() const { return m_dmethods; }
  std::vector<DexMethod*>& get_dmethods() {
    always_assert_log(!m_external, "Unexpected external class %s\n",
                      self_show().c_str());
    return m_dmethods;
  }
  const std::vector<DexMethod*>& get_vmethods() const { return m_vmethods; }
  std::vector<DexMethod*>& get_vmethods() {
    always_assert_log(!m_external, "Unexpected external class %s\n",
                      self_show().c_str());
    return m_vmethods;
  }

  std::vector<DexMethod*> get_all_methods() const;

  /* Gets the clinit method, aka the class initializer method.
   *
   * Unlike constructors, there's only ever one clinit method.
   * It takes no arguments and returns void.
   */
  DexMethod* get_clinit() const {
    for (auto* meth : get_dmethods()) {
      if (strcmp(meth->get_name()->c_str(), "<clinit>") == 0) {
        return meth;
      }
    }
    return nullptr;
  }

  std::vector<DexMethod*> get_ctors() const {
    std::vector<DexMethod*> ctors;
    for (auto* meth : get_dmethods()) {
      if (strcmp(meth->get_name()->c_str(), "<init>") == 0) {
        ctors.push_back(meth);
      }
    }
    return ctors;
  }

  bool has_ctors() const {
    // TODO: There must be a logarithmic approach to this. dmethods are sorted!
    return !get_ctors().empty();
  }

  void add_method(DexMethod* m);
  // Removes the method from this class
  void remove_method(const DexMethod* m);

  const std::vector<DexField*>& get_sfields() const { return m_sfields; }
  std::vector<DexField*>& get_sfields() {
    redex_assert(!m_external);
    return m_sfields;
  }
  const std::vector<DexField*>& get_ifields() const { return m_ifields; }
  std::vector<DexField*>& get_ifields() {
    redex_assert(!m_external);
    return m_ifields;
  }

  std::vector<DexField*> get_all_fields() const;
  void add_field(DexField* f);
  // Removes the field from this class
  void remove_field(const DexField* f);
  // Remove the field from the class and delete the definition.
  void remove_field_definition(DexField* f);
  DexField* find_ifield(const char* name, const DexType* field_type) const;
  DexField* find_sfield(const char* name, const DexType* field_type) const;

  DexAnnotationDirectory* get_annotation_directory();
  DexAccessFlags get_access() const { return m_access_flags; }
  DexType* get_super_class() const { return m_super_class; }
  DexType* get_type() const { return m_self; }
  const DexString* get_name() const { return m_self->get_name(); }
  const char* c_str() const { return get_name()->c_str(); }
  std::string_view str() const { return get_name()->str(); }
  std::string str_copy() const { return get_name()->str_copy(); }
  DexTypeList* get_interfaces() const { return m_interfaces; }
  const DexString* get_source_file() const { return m_source_file; }
  bool has_class_data() const;
  bool is_def() const { return true; }
  bool is_external() const { return m_external; }
  std::unique_ptr<DexEncodedValueArray> get_static_values();
  const DexAnnotationSet* get_anno_set() const { return m_anno.get(); }
  DexAnnotationSet* get_anno_set() { return m_anno.get(); }
  [[nodiscard]] bool attach_annotation_set(
      std::unique_ptr<DexAnnotationSet> anno);
  void set_source_file(const DexString* source_file) {
    m_source_file = source_file;
  }

  /**
   * This also adds `name` as an alias for this DexType in the g_redex global
   * type map.
   */
  void set_deobfuscated_name(std::string_view name);
  void set_deobfuscated_name(const DexString* name);
  void set_deobfuscated_name(const DexString& name);

  const DexString& get_deobfuscated_name() const {
    redex_assert(m_deobfuscated_name != nullptr);
    return *m_deobfuscated_name;
  }
  const DexString* get_deobfuscated_name_or_null() const {
    return m_deobfuscated_name;
  }
  std::string_view get_deobfuscated_name_or_empty() const {
    if (m_deobfuscated_name == nullptr) {
      return DexString::EMPTY;
    }
    return m_deobfuscated_name->str();
  }
  std::string get_deobfuscated_name_or_empty_copy() const {
    return ::str_copy(get_deobfuscated_name_or_empty());
  }

  // Retrieves the (original) location.
  const DexLocation* get_location() const { return m_location; }

  void set_access(DexAccessFlags access) {
    always_assert_log(!m_external, "Unexpected external class %s\n",
                      self_show().c_str());
    m_access_flags = access;
  }

  void set_external();

  void set_super_class(DexType* super_class) {
    always_assert_log(!m_external, "Unexpected external class %s\n",
                      self_show().c_str());
    m_super_class = super_class;
  }

  void combine_annotations_with(DexClass* other);
  void combine_annotations_with(DexAnnotationSet* other);

  void set_interfaces(DexTypeList* intfs) {
    always_assert_log(!m_external, "Unexpected external class %s\n",
                      self_show().c_str());
    m_interfaces = intfs;
  }

  void clear_annotations();
  /* Encodes class_data_item, returns size in bytes.  No
   * alignment requirements on *output
   */
  // Upper bound on the bytes `encode` writes: four uleb128 counts, then per
  // field an index delta and access flags, and per method those plus a code
  // offset.
  size_t max_encoded_size() const;

  int encode(DexOutputIdx* dodx, dexcode_to_offset& dco, uint8_t* output);

  template <typename C>
  void gather_types(C& ltype) const;
  void gather_strings(std::vector<const DexString*>& lstring,
                      bool exclude_loads = false) const;
  void gather_strings(UnorderedSet<const DexString*>& lstring,
                      bool exclude_loads = false) const;
  template <typename C>
  void gather_fields(C& lfield) const;
  template <typename C>
  void gather_methods(C& lmethod) const;
  template <typename C>
  void gather_callsites(C& lcallsite) const;
  template <typename C>
  void gather_protos(C& lproto) const;
  template <typename C>
  void gather_methodhandles(C& lmethodhandle) const;

  void gather_load_types(UnorderedSet<const DexType*>& ltype) const;
  void gather_init_classes(std::vector<const DexType*>& ltype) const;

  // Whether to optimize for perf, instead of space.
  // This bit is only set by the InterDex pass and not available earlier.
  bool is_perf_sensitive() const {
    return m_perf_sensitive != PerfSensitiveGroup::NONE;
  }
  void set_perf_sensitive(PerfSensitiveGroup value) {
    m_perf_sensitive = value;
  }
  PerfSensitiveGroup get_perf_sensitive() { return m_perf_sensitive; }

  bool is_dynamically_dead() const { return m_dynamically_dead; }
  void set_dynamically_dead(bool value = true) { m_dynamically_dead = value; }

  // Find methods and fields from a class using its obfuscated name.
  DexField* find_field_from_simple_deobfuscated_name(
      const std::string& field_name);
  DexMethod* find_method_from_simple_deobfuscated_name(
      const std::string& method_name);

  // In code units. Estimated by accounting 48 code units for the class
  // metadata, 8 for each field and sum up all methods with
  // DexMethod::estimated_size().
  size_t estimated_size() const;

  std::string show_structure() const;

 private:
  void sort_methods();
  void sort_fields();

  template <typename C>
  void gather_strings_internal(C& lstring, bool exclude_loads) const;
};

inline bool compare_dexclasses(const DexClass* a, const DexClass* b) {
  return compare_dextypes(a->get_type(), b->get_type());
}

struct dexclasses_comparator {
  bool operator()(const DexClass* a, const DexClass* b) const {
    return compare_dexclasses(a, b);
  }
};

using DexClasses = std::vector<DexClass*>;
using DexClassesVector = std::vector<DexClasses>;

/* Non-optimizing DexSpec compliant ordering */
inline bool compare_dexmethods(const DexMethodRef* a, const DexMethodRef* b) {
  if (a == nullptr) {
    return b != nullptr;
  } else if (b == nullptr) {
    return false;
  }
  if (a->get_class() != b->get_class()) {
    return compare_dextypes(a->get_class(), b->get_class());
  }
  if (a->get_name() != b->get_name()) {
    return compare_dexstrings(a->get_name(), b->get_name());
  }
  return compare_dexprotos(a->get_proto(), b->get_proto());
}

struct dexmethods_comparator {
  bool operator()(const DexMethodRef* a, const DexMethodRef* b) const {
    return compare_dexmethods(a, b);
  }
};

/**
 * Return the DexClass that represents the DexType in input or nullptr if
 * no such DexClass exists.
 */
DexClass* type_class(const DexType* t);

/**
 * Return the DexClass that represents an internal DexType or nullptr if
 * no such DexClass exists.
 */
inline DexClass* type_class_internal(const DexType* t) {
  auto* dc = type_class(t);
  if (dc == nullptr || dc->is_external()) {
    return nullptr;
  }
  return dc;
}

/**
 * For a set of classes, compute all referenced strings, types, fields,
 * methods, call sites, method handles and protos (those referenced directly,
 * see Gatherable::gather_protos), such that components are sorted and unique.
 */
void gather_components(std::vector<const DexString*>& lstring,
                       std::vector<const DexType*>& ltype,
                       std::vector<DexFieldRef*>& lfield,
                       std::vector<DexMethodRef*>& lmethod,
                       std::vector<DexCallSite*>& lcallsite,
                       std::vector<DexMethodHandle*>& lmethodhandle,
                       std::vector<DexProto*>& lproto,
                       const DexClasses& classes,
                       bool exclude_loads = false);

DISALLOW_DEFAULT_COMPARATOR(DexClass)
DISALLOW_DEFAULT_COMPARATOR(DexCode)
DISALLOW_DEFAULT_COMPARATOR(DexDebugInstruction)
DISALLOW_DEFAULT_COMPARATOR(DexDebugItem)
DISALLOW_DEFAULT_COMPARATOR(DexFieldRef)
DISALLOW_DEFAULT_COMPARATOR(DexField)
DISALLOW_DEFAULT_COMPARATOR(DexMethodRef)
DISALLOW_DEFAULT_COMPARATOR(DexMethod)
DISALLOW_DEFAULT_COMPARATOR(DexOutputIdx)
DISALLOW_DEFAULT_COMPARATOR(DexProto)
DISALLOW_DEFAULT_COMPARATOR(DexString)
DISALLOW_DEFAULT_COMPARATOR(DexType)
DISALLOW_DEFAULT_COMPARATOR(DexTypeList)
