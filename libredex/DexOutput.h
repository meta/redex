/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <cstdint>
#include <functional>
#include <memory>
#include <string>
#include <vector>

#include "ConfigFiles.h"
#include "DeterministicContainers.h"
#include "DexClass.h"
#include "DexMethodHandle.h"
#include "DexStats.h"
#include "GlobalConfig.h"

class DexAnnotation;
class DexCallSite;

enum class DebugInfoKind : uint32_t;

using dexstring_to_idx = UnorderedMap<const DexString*, uint32_t>;
using dextype_to_idx = UnorderedMap<const DexType*, uint16_t>;
using dexproto_to_idx = UnorderedMap<DexProto*, uint32_t>;
using dexfield_to_idx = UnorderedMap<DexFieldRef*, uint32_t>;
using dexmethod_to_idx = UnorderedMap<DexMethodRef*, uint32_t>;
using dexcallsite_to_idx = UnorderedMap<DexCallSite*, uint32_t>;
using dexmethodhandle_to_idx = UnorderedMap<DexMethodHandle*, uint32_t>;

enum class SortMode {
  CLASS_ORDER,
  CLASS_STRINGS,
  CLINIT_FIRST,
  METHOD_COLDSTART_ORDER,
  METHOD_PROFILED_ORDER,
  METHOD_SIMILARITY,
  DEFAULT
};

class DexOutputIdx {
 private:
  dexstring_to_idx m_string;
  dextype_to_idx m_type;
  dexproto_to_idx m_proto;
  dexfield_to_idx m_field;
  dexmethod_to_idx m_method;
  std::vector<DexTypeList*> m_typelist;
  dexcallsite_to_idx m_callsite;
  dexmethodhandle_to_idx m_methodhandle;

 public:
  DexOutputIdx(dexstring_to_idx string,
               dextype_to_idx type,
               dexproto_to_idx proto,
               dexfield_to_idx field,
               dexmethod_to_idx method,
               std::vector<DexTypeList*> typelist,
               dexcallsite_to_idx callsite,
               dexmethodhandle_to_idx methodhandle)
      : m_string(std::move(string)),
        m_type(std::move(type)),
        m_proto(std::move(proto)),
        m_field(std::move(field)),
        m_method(std::move(method)),
        m_typelist(std::move(typelist)),
        m_callsite(std::move(callsite)),
        m_methodhandle(std::move(methodhandle)) {}

  DexOutputIdx(const DexOutputIdx&) = delete;
  DexOutputIdx& operator=(const DexOutputIdx&) = delete;

  DexOutputIdx(DexOutputIdx&&) = default;
  DexOutputIdx& operator=(DexOutputIdx&&) = default;

  const dexstring_to_idx& string_to_idx() const { return m_string; }
  const dextype_to_idx& type_to_idx() const { return m_type; }
  const dexproto_to_idx& proto_to_idx() const { return m_proto; }
  const dexfield_to_idx& field_to_idx() const { return m_field; }
  const dexmethod_to_idx& method_to_idx() const { return m_method; }
  const std::vector<DexTypeList*>& typelist_list() const { return m_typelist; }
  const dexcallsite_to_idx& callsite_to_idx() const { return m_callsite; }
  const dexmethodhandle_to_idx& methodhandle_to_idx() const {
    return m_methodhandle;
  }

  uint32_t stringidx(const DexString* s) const { return m_string.at(s); }
  uint16_t typeidx(const DexType* t) const { return m_type.at(t); }
  uint16_t protoidx(DexProto* p) const { return m_proto.at(p); }
  uint32_t fieldidx(DexFieldRef* f) const { return m_field.at(f); }
  uint32_t methodidx(DexMethodRef* m) const { return m_method.at(m); }
  uint32_t callsiteidx(DexCallSite* c) const { return m_callsite.at(c); }
  uint32_t methodhandleidx(DexMethodHandle* c) const {
    return m_methodhandle.at(c);
  }

  size_t stringsize() const { return m_string.size(); }
  size_t typesize() const { return m_type.size(); }
  size_t protosize() const { return m_proto.size(); }
  size_t fieldsize() const { return m_field.size(); }
  size_t methodsize() const { return m_method.size(); }
  size_t callsitesize() const { return m_callsite.size(); }
  size_t methodhandlesize() const { return m_methodhandle.size(); }
};

class IODIMetadata;
class GatheredTypes;

struct enhanced_dex_stats_t : public dex_stats_t {
  UnorderedMap<const DexClass*, size_t> class_size;
  // Authoritative post-lowering per-method code_item byte size (return of
  // DexMethod code->encode()); populated only when write_method_sizes is set.
  UnorderedMap<const DexMethod*, size_t> method_size;

  enhanced_dex_stats_t& operator+=(const enhanced_dex_stats_t& rhs) {
    dex_stats_t::operator+=(rhs);
    insert_unordered_iterable(class_size, rhs.class_size);
    insert_unordered_iterable(method_size, rhs.method_size);
    return *this;
  }
};

SortMode get_string_sort_mode(ConfigFiles& conf);
std::vector<SortMode> get_code_sort_mode(ConfigFiles& conf,
                                         const std::string& store_name);

enhanced_dex_stats_t write_classes_to_dex(
    const std::string& filename,
    DexClasses* classes,
    std::shared_ptr<GatheredTypes> gtypes,
    size_t store_number,
    const std::string* store_name,
    size_t dex_number,
    ConfigFiles& conf,
    PositionMapper* pos_mapper,
    DebugInfoKind debug_info_kind,
    UnorderedMap<DexMethod*, uint64_t>* method_to_id,
    UnorderedMap<DexCode*, std::vector<DebugLineItem>>* code_debug_lines,
    IODIMetadata* iodi_metadata,
    const std::string& dex_magic,
    const DexOutputConfig& dex_output_config = DexOutputConfig{},
    int min_sdk = 0,
    const std::vector<SortMode>& code_sort_mode = {SortMode::CLASS_ORDER},
    SortMode string_sort_mode = SortMode::DEFAULT);

using cmp_dstring = bool (*)(const DexString*, const DexString*);
using cmp_dtype = bool (*)(const DexType*, const DexType*);
using cmp_dproto = bool (*)(const DexProto*, const DexProto*);
using cmp_dfield = bool (*)(const DexFieldRef*, const DexFieldRef*);
using cmp_dmethod = bool (*)(const DexMethodRef*, const DexMethodRef*);
using cmp_dtypelist = bool (*)(const DexTypeList*, const DexTypeList*);
using cmp_callsite = bool (*)(const DexCallSite*, const DexCallSite*);
using cmp_methodhandle = bool (*)(const DexMethodHandle*,
                                  const DexMethodHandle*);

inline bool compare_dexcallsites(const DexCallSite* a, const DexCallSite* b) {
  if (a == nullptr) {
    return b != nullptr;
  } else if (b == nullptr) {
    return false;
  }
  // TODO(T59683693) -- need real ordering
  return a < b;
}

inline bool compare_dexmethodhandles(const DexMethodHandle* a,
                                     const DexMethodHandle* b) {
  if (a == nullptr) {
    return b != nullptr;
  } else if (b == nullptr) {
    return false;
  }
  if (a->type() != b->type()) {
    return a->type() < b->type();
  }
  if (DexMethodHandle::isInvokeType(a->type())) {
    return compare_dexmethods(a->methodref(), b->methodref());
  } else {
    return compare_dexfields(a->fieldref(), b->fieldref());
  }
}

/*
 * This API gathers all of the data referred to by a set of DexClasses in
 * preparation for emitting a dex file and provides the symbol tables in indexed
 * form for encoding.
 *
 * The gather algorithm implemented in gather_components() traverses the tree of
 * DexFoo objects rooted at each DexClass.  The individual gather methods,
 * gather_{strings,types,fields,methods}, (see Gatherable.h and DexClass.h) find
 * references to each type, respectively, that the object needs.
 *
 * Fields and methods need special consideration: those that are defined by a
 * DexClass need to emit more data (for example, methods must emit their code).
 * Fields and methods that are merely referenced by this DexClass (for example,
 * a call into the Android library) only need the types and strings necessary to
 * represent the reference.  To handle these divergent cases, gather_foo gathers
 * all of the data, while gather_foo_shallow gathers only what is needed for
 * references.
 *
 * Another subtlety is that gather_foo only follows fields of type foo.  For
 * example, DexField contains both a DexType (m_type) and a DexString (m_name).
 * Even though DexType also contains a string, DexField::gather_strings will
 * only gather m_name; it does not follow m_type to find more strings.  This
 * design simplifies the implementation of the gather methods since it breaks
 * cycles in the reference graph, but it makes finding a "complete" set more
 * involved.  To gather all strings, for instance, one must not only gather all
 * strings at the class level, but also gather strings for all types discovered
 * at the class level.
 */

class GatheredTypes {
 private:
  std::vector<const DexString*> m_lstring;
  std::vector<const DexType*> m_ltype;
  std::vector<DexFieldRef*> m_lfield;
  std::vector<DexMethodRef*> m_lmethod;
  std::vector<DexCallSite*> m_lcallsite;
  std::vector<DexMethodHandle*> m_lmethodhandle;
  std::vector<DexProto*> m_lproto;
  DexClasses* m_classes;
  UnorderedMap<const DexString*, unsigned int> m_cls_load_strings;
  UnorderedMap<const DexString*, unsigned int> m_cls_strings;
  UnorderedMap<const DexMethod*, unsigned int> m_methods_in_cls_order;
  ConfigFiles* m_config{nullptr};

  dexstring_to_idx get_string_index(cmp_dstring cmp = compare_dexstrings);
  dextype_to_idx get_type_index(cmp_dtype cmp = compare_dextypes);
  dexproto_to_idx get_proto_index(cmp_dproto cmp = compare_dexprotos);
  dexfield_to_idx get_field_index(cmp_dfield cmp = compare_dexfields);
  dexmethod_to_idx get_method_index(cmp_dmethod cmp = compare_dexmethods);
  std::vector<DexTypeList*> get_typelist_list(
      dexproto_to_idx* protos, cmp_dtypelist cmp = compare_dextypelists);
  dexcallsite_to_idx get_callsite_index(
      cmp_callsite cmp = compare_dexcallsites);
  dexmethodhandle_to_idx get_methodhandle_index(
      cmp_methodhandle cmp = compare_dexmethodhandles);

  void build_cls_load_map();
  void build_cls_map();
  void build_method_map();

 public:
  explicit GatheredTypes(DexClasses* classes);

  DexOutputIdx get_dodx();
  template <class T = decltype(compare_dexstrings)>
  std::vector<const DexString*> get_dexstring_emitlist(
      T cmp = compare_dexstrings);
  std::vector<const DexString*> get_cls_order_dexstring_emitlist();
  std::vector<const DexString*> keep_cls_strings_together_emitlist();
  std::vector<DexMethod*> get_dexmethod_emitlist();
  std::vector<DexMethodHandle*> get_dexmethodhandle_emitlist();
  std::vector<DexCallSite*> get_dexcallsite_emitlist();

  void gather_class(int num);

  void sort_dexmethod_emitlist_method_similarity_order(
      std::vector<DexMethod*>& lmeth);
  void sort_dexmethod_emitlist_coldstart_order(std::vector<DexMethod*>& lmeth);
  void sort_dexmethod_emitlist_default_order(std::vector<DexMethod*>& lmeth);
  void sort_dexmethod_emitlist_cls_order(std::vector<DexMethod*>& lmeth);
  void sort_dexmethod_emitlist_clinit_order(std::vector<DexMethod*>& lmeth);
  void sort_dexmethod_emitlist_profiled_order(std::vector<DexMethod*>& lmeth);
  void set_config(ConfigFiles* config);

  UnorderedSet<const DexString*> index_type_names();
};

template <class T>
std::vector<const DexString*> GatheredTypes::get_dexstring_emitlist(T cmp) {
  std::vector<const DexString*> strlist(m_lstring);
  std::sort(strlist.begin(), strlist.end(), std::cref(cmp));
  return strlist;
}

using annomap_t = UnorderedMap<DexAnnotation*, uint32_t>;
using asetmap_t = UnorderedMap<DexAnnotationSet*, uint32_t>;
using xrefmap_t = UnorderedMap<ParamAnnotations*, uint32_t>;
using adirmap_t = UnorderedMap<DexAnnotationDirectory*, uint32_t>;

struct CodeItemEmit {
  DexMethod* method;
  DexCode* code;
  dex_code_item* code_item;

  CodeItemEmit(DexMethod* meth, DexCode* c, dex_code_item* ci);
};

struct DexOutputTestHelper;

class DexOutput {
  friend class DexOutputTest;

 public:
  enhanced_dex_stats_t m_stats;

  static constexpr size_t kIODILayerBits = 4;
  static constexpr size_t kIODILayerBound = 1ul << (kIODILayerBits - 1);
  static constexpr size_t kIODILayerShift =
      sizeof(uint32_t) * 8 - kIODILayerBits;
  static constexpr uint32_t kIODIDataMask = (1u << kIODILayerShift) - 1;
  static constexpr uint32_t kIODILayerMask = ((1u << kIODILayerBits) - 1)
                                             << kIODILayerShift;

 private:
  DexClasses* m_classes;
  // The ALLOCATION -- the configured dex_output_buffer_size plus
  // k_output_margin. Not the size policy: that is policy_cap(), below.
  const size_t m_output_size;
  std::unique_ptr<uint8_t[]> m_output;
  std::shared_ptr<GatheredTypes> m_gtypes;
  DexOutputIdx m_dodx;
  uint32_t m_offset;
  const char* m_filename;
  size_t m_store_number;
  const std::string* m_store_name;
  size_t m_dex_number;
  DebugInfoKind m_debug_info_kind;
  IODIMetadata* m_iodi_metadata;
  PositionMapper* m_pos_mapper;
  std::string m_method_mapping_filename;
  std::string m_class_mapping_filename;
  std::string m_pg_mapping_filename;
  std::string m_invoke_mapping_filename;
  std::string m_full_mapping_filename;
  std::string m_bytecode_offset_filename;
  UnorderedMap<DexTypeList*, uint32_t> m_tl_emit_offsets;
  std::vector<CodeItemEmit> m_code_item_emits;
  UnorderedMap<DexMethod*, uint64_t>* m_method_to_id;
  UnorderedMap<DexCode*, std::vector<DebugLineItem>>* m_code_debug_lines;
  std::vector<std::pair<std::string, uint32_t>> m_method_bytecode_offsets;
  UnorderedMap<DexClass*, uint32_t> m_static_values;
  UnorderedMap<DexCallSite*, uint32_t> m_call_site_items;
  // Where the call site and method handle id tables start. The dex header has
  // no field for either -- the format records them only in the map list -- so
  // the emitters used to reconstruct the offsets from hdr.class_defs_*, which
  // silently collapses to 0 when there are no class defs. Capturing them where
  // they are reserved makes the emitters read the same number that was
  // reserved, rather than one derived by a different route.
  uint32_t m_callsite_start{0};
  uint32_t m_methodhandle_start{0};
  dex_header hdr;
  std::vector<dex_map_item> m_map_items;
  bool m_normal_primary_dex;
  const ConfigFiles& m_config_files;
  int m_min_sdk;
  const DexOutputConfig m_dex_output_config;

  void insert_map_item(uint16_t maptype,
                       uint32_t size,
                       uint32_t offset,
                       uint32_t bytes);
  void generate_string_data(SortMode mode = SortMode::DEFAULT);
  void generate_type_data();
  void generate_proto_data();
  void generate_field_data();
  void generate_method_data();
  void generate_class_data();
  void generate_class_data_items();
  void generate_callsite_data();
  void generate_methodhandle_data();

  // Sort code according to a sequence of sorting modes, ordered by precedence.
  // e.g. passing {SortMode::CLINIT_FIRST, SortMode::CLASS_ORDER} means that
  // clinit methods come before all other methods, and remaining methods are
  // sorted by class.
  void generate_code_items(const std::vector<SortMode>& modes);
  void generate_static_values();
  void unique_annotations(annomap_t& annomap,
                          std::vector<DexAnnotation*>& annolist);
  void unique_asets(annomap_t& annomap,
                    asetmap_t& asetmap,
                    std::vector<DexAnnotationSet*>& asetlist);
  void unique_xrefs(asetmap_t& asetmap,
                    xrefmap_t& xrefmap,
                    std::vector<ParamAnnotations*>& xreflist);
  void unique_adirs(asetmap_t& asetmap,
                    xrefmap_t& xrefmap,
                    adirmap_t& adirmap,
                    std::vector<DexAnnotationDirectory*>& adirlist);
  void generate_annotations();
  void generate_debug_items();
  void generate_typelist_data();
  void generate_map();
  void finalize_header();
  void init_header_offsets(const std::string& dex_magic);
  void write_symbol_files();
  uint32_t align(uint32_t offset) { return (offset + 3) & ~3; }
  void align_output();

  void inc_offset(uint64_t v);

  // The size policy the cursor is held below, as distinct from the allocation.
  // Derived rather than stored so the two cannot drift apart.
  uint64_t policy_cap() const;

  // Aborts unless `bytes` can be written at the current cursor, and records
  // that the cursor is checked that far. Every producer that advances a raw
  // pointer with no notion of an end goes through this first.
  void ensure_fits(uint64_t bytes, const char* what, const char* subject);
  void ensure_fits(uint64_t bytes,
                   const char* what,
                   const std::function<std::string()>& describe_subject);

  // Cursor extent granted by the most recent producer check. The next cursor
  // advance consumes it so slack cannot cover another producer.
  uint64_t m_checked_through{0};

  friend struct DexOutputTestHelper;

 public:
  DexOutput(
      const char* path,
      DexClasses* classes,
      std::shared_ptr<GatheredTypes> gtypes,
      bool normal_primary_dex,
      size_t store_number,
      const std::string* store_name,
      size_t dex_number,
      DebugInfoKind debug_info_kind,
      IODIMetadata* iodi_metadata,
      const ConfigFiles& config_files,
      PositionMapper* pos_mapper,
      UnorderedMap<DexMethod*, uint64_t>* method_to_id,
      UnorderedMap<DexCode*, std::vector<DebugLineItem>>* code_debug_lines,
      DexOutputConfig dex_output_config = DexOutputConfig{},
      int min_sdk = 0);
  void prepare(SortMode string_mode,
               const std::vector<SortMode>& code_mode,
               ConfigFiles& conf,
               const std::string& dex_magic);
  void write();
  void metrics();
  static void check_method_instruction_size_limit(
      const ConfigFiles& conf,
      int size,
      const std::function<std::string()>& describe_method);
};
