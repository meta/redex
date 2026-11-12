/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "DexOutput.h"

#include <algorithm>
#include <assert.h>
#include <bitset>
#include <boost/filesystem.hpp>
#include <fcntl.h>
#include <fstream>
#include <functional>
#include <inttypes.h>
#include <json/json.h>
#include <limits>
#include <memory>
#include <stdlib.h>
#include <sys/stat.h>
#include <utility>

#ifdef _MSC_VER
// TODO: Rewrite open/write/close with C/C++ standards. But it works for now.
#include <io.h>
#define open _open
#define write _write
#define close _close
#define fstat _fstat64i32
#define stat _stat64i32
#define O_CREAT _O_CREAT
#define O_TRUNC _O_TRUNC
#define O_WRONLY _O_WRONLY
#endif

#include "Debug.h"
#include "DexCallSite.h"
#include "DexClass.h"
#include "DexInstruction.h"
#include "DexLimits.h"
#include "DexMethodHandle.h"
#include "DexPosition.h"
#include "DexUtil.h"
#include "GlobalConfig.h"
#include "IODIMetadata.h"
#include "IODIPlan.h"
#include "IRCode.h"
#include "Macros.h"
#include "MethodProfiles.h"
#include "MethodSimilarityCompressionConsciousOrderer.h"
#include "MethodSimilarityGreedyOrderer.h"
#include "MethodUtil.h"
#include "RedexOptions.h" // For DebugInfoKind
#include "Resolver.h"
#include "Sha1.h"
#include "Show.h"
#include "Trace.h"
#include "TypeUtil.h"
#include "Walkers.h"

/*
 * For adler32...
 */
#include <zlib.h>

namespace {

// Hash functor for std::vector<T> to enable use as keys in UnorderedMap.
// Uses FNV-1a-inspired hash combining over the raw element values.
template <typename T>
struct VectorHash {
  size_t operator()(const std::vector<T>& v) const {
    size_t seed = v.size();
    for (const auto& elem : v) {
      seed ^= std::hash<T>{}(elem) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
    }
    return seed;
  }
};

template <class T, class U>
class CustomSort {
 private:
  const UnorderedMap<const T*, unsigned int>& m_map;
  U m_cmp;

 public:
  CustomSort(const UnorderedMap<const T*, unsigned int>& input_map, U cmp)
      : m_map(input_map) {
    m_cmp = cmp;
  }

  bool operator()(const T* a, const T* b) const {
    const auto end_it = m_map.end();
    const auto a_it = m_map.find(a);
    const auto b_it = m_map.find(b);
    if (a_it == end_it && b_it == end_it) {
      return m_cmp(a, b);
    }
    if (a_it != end_it && b_it != end_it) {
      const auto a_idx = a_it->second;
      const auto b_idx = b_it->second;
      if (a_idx != b_idx) {
        return a_idx < b_idx;
      }
      return m_cmp(a, b);
    }
    if (a_it != end_it) {
      return true;
    }
    return false;
  }
};

} // namespace

GatheredTypes::GatheredTypes(DexClasses* classes) : m_classes(classes) {
  // ensure that the string id table contains the empty string, which is used
  // for the DexPosition mapping
  m_lstring.push_back(DexString::make_string(""));

  // build maps for the different custom sorting options
  build_cls_load_map();
  build_cls_map();
  build_method_map();

  gather_components(m_lstring, m_ltype, m_lfield, m_lmethod, m_lcallsite,
                    m_lmethodhandle, *m_classes);
}

UnorderedSet<const DexString*> GatheredTypes::index_type_names() {
  UnorderedSet<const DexString*> type_names;
  for (auto it = m_ltype.begin(); it != m_ltype.end(); ++it) {
    type_names.insert((*it)->get_name());
  }
  return type_names;
}

std::vector<const DexString*>
GatheredTypes::get_cls_order_dexstring_emitlist() {
  return get_dexstring_emitlist(CustomSort<DexString, cmp_dstring>(
      m_cls_load_strings, compare_dexstrings));
}

std::vector<const DexString*>
GatheredTypes::keep_cls_strings_together_emitlist() {
  return get_dexstring_emitlist(
      CustomSort<DexString, cmp_dstring>(m_cls_strings, compare_dexstrings));
}

std::vector<DexMethodHandle*> GatheredTypes::get_dexmethodhandle_emitlist() {
  return m_lmethodhandle;
}

std::vector<DexCallSite*> GatheredTypes::get_dexcallsite_emitlist() {
  return m_lcallsite;
}

std::vector<DexMethod*> GatheredTypes::get_dexmethod_emitlist() {
  std::vector<DexMethod*> methlist;
  for (auto* cls : UnorderedIterable(*m_classes)) {
    TRACE(OPUT, 3, "[dexmethod_emitlist][class] %s", cls->c_str());
    auto const& dmethods = cls->get_dmethods();
    auto const& vmethods = cls->get_vmethods();
    if (traceEnabled(OPUT, 3)) {
      for (const auto& dmeth : dmethods) {
        TRACE(OPUT, 3, "  [dexmethod_emitlist][dmethod] %s", dmeth->c_str());
      }
      for (const auto& vmeth : vmethods) {
        TRACE(OPUT, 3, "  [dexmethod_emitlist][vmethod] %s", vmeth->c_str());
      }
    }
    for (auto* m : dmethods) {
      always_assert(!m->is_external());
    }
    for (auto* m : vmethods) {
      always_assert(!m->is_external());
    }
    methlist.insert(methlist.end(), dmethods.begin(), dmethods.end());
    methlist.insert(methlist.end(), vmethods.begin(), vmethods.end());
  }
  return methlist;
}

void GatheredTypes::sort_dexmethod_emitlist_method_similarity_order(
    std::vector<DexMethod*>& lmeth) {
  // We keep "perf sensitive methods" together in front, and only order by
  // similarity the remaining methods. Here, we consider as "perf sensitive
  // methods" any methods in a class that...
  // - is perf sensitive, which in particular includes all classes that are
  //   ordered by beta maps
  // - contains methods that contain any profiled methods with a very
  //   conservative min-appear cut-off.
  //
  // This is similar to the exclusions that the InterDex pass applies when
  // sorting remaining classes for better compression.
  redex_assert(m_config != nullptr);
  UnorderedSet<DexType*> perf_sensitive_classes;

  const auto& global_config = m_config->get_global_config();
  MethodProfileOrderingConfig* profiles_config{nullptr};
  if (global_config.has_config_by_name("method_profile_order")) {
    profiles_config =
        global_config.get_config_by_name<MethodProfileOrderingConfig>(
            "method_profile_order");
  }

  if (profiles_config != nullptr &&
      profiles_config->skip_similarity_reordering) {
    auto& method_profiles = m_config->get_method_profiles();
    // Some builds might not have method profiles information.
    if (method_profiles.is_initialized()) {
      method_profiles::dexmethods_profiled_comparator comparator(
          lmeth,
          /*method_profiles=*/&method_profiles,
          profiles_config);

      for (auto* meth : lmeth) {
        auto method_sort_num = comparator.get_overall_method_sort_num(meth);
        if (method_sort_num <
            method_profiles::dexmethods_profiled_comparator::VERY_END) {
          perf_sensitive_classes.insert(meth->get_class());
        }
      }
    }
  }

  bool use_compression_conscious_order{false};
  MethodSimilarityOrderingConfig* similarity_config{nullptr};
  if (global_config.has_config_by_name("method_similarity_order")) {
    similarity_config =
        global_config.get_config_by_name<MethodSimilarityOrderingConfig>(
            "method_similarity_order");
    use_compression_conscious_order =
        similarity_config->use_compression_conscious_order;
  }

  if (similarity_config != nullptr &&
      similarity_config->use_class_level_perf_sensitivity) {
    for (auto* meth : lmeth) {
      auto* cls = type_class(meth->get_class());
      if (!cls->is_perf_sensitive()) {
        continue;
      }
      perf_sensitive_classes.insert(meth->get_class());
    }
  }

  std::vector<DexMethod*> perf_sensitive_methods;
  std::vector<DexMethod*> remaining_methods;
  remaining_methods.reserve(lmeth.size());
  for (auto* meth : lmeth) {
    if (perf_sensitive_classes.count(meth->get_class()) != 0u) {
      perf_sensitive_methods.push_back(meth);
    } else {
      remaining_methods.push_back(meth);
    }
  }

  TRACE(
      OPUT, 2,
      "Skipping %zu perf sensitive methods, ordering %zu methods by similarity",
      perf_sensitive_methods.size(), remaining_methods.size());

  if (use_compression_conscious_order) {
    MethodSimilarityCompressionConsciousOrderer method_orderer;
    method_orderer.order(remaining_methods, this);
  } else {
    MethodSimilarityGreedyOrderer method_orderer;
    method_orderer.order(remaining_methods);
  }

  lmeth.clear();
  lmeth.insert(lmeth.end(), perf_sensitive_methods.begin(),
               perf_sensitive_methods.end());
  lmeth.insert(lmeth.end(), remaining_methods.begin(), remaining_methods.end());
}

void GatheredTypes::sort_dexmethod_emitlist_default_order(
    std::vector<DexMethod*>& lmeth) {
  std::stable_sort(lmeth.begin(), lmeth.end(), compare_dexmethods);
}

void GatheredTypes::sort_dexmethod_emitlist_cls_order(
    std::vector<DexMethod*>& lmeth) {
  std::stable_sort(lmeth.begin(), lmeth.end(),
                   CustomSort<DexMethod, cmp_dmethod>(m_methods_in_cls_order,
                                                      compare_dexmethods));
}

void GatheredTypes::sort_dexmethod_emitlist_coldstart_order(
    std::vector<DexMethod*>& lmeth) {
  const auto& coldstart_methods = m_config->get_coldstart_methods();

  if (coldstart_methods.empty()) {
    return;
  }

  UnorderedMap<const DexMethod*, unsigned int> coldstart_method_ordering;
  for (const auto& method : coldstart_methods) {
    DexMethodRef* method_ref = DexMethod::get_method(method);
    if (method_ref == nullptr || !method_ref->is_def()) {
      continue;
    }
    auto* meth = method_ref->as_def();
    always_assert_log(coldstart_method_ordering.count(meth) == 0,
                      "%s already found at position %u", SHOW(meth),
                      coldstart_method_ordering.at(meth));
    coldstart_method_ordering[meth] = coldstart_method_ordering.size();
  }

  UnorderedMap<const DexMethodRef*, size_t> initial_ordering;
  for (auto* m : lmeth) {
    initial_ordering[m] = initial_ordering.size();
  }

  auto coldstart_cmp = [&initial_ordering, &coldstart_method_ordering](
                           const DexMethod* a, const DexMethod* b) {
    const auto end_it = coldstart_method_ordering.end();
    const auto a_it = coldstart_method_ordering.find(a);
    const auto b_it = coldstart_method_ordering.find(b);
    if (a_it == end_it && b_it == end_it) {
      return initial_ordering.at(a) < initial_ordering.at(b);
    }
    if (a_it != end_it && b_it != end_it) {
      const auto a_idx = a_it->second;
      const auto b_idx = b_it->second;
      if (a_idx != b_idx) {
        return a_idx < b_idx;
      }
      return initial_ordering.at(a) < initial_ordering.at(b);
    }
    if (a_it != end_it) {
      return true;
    }
    return false;
  };

  std::stable_sort(lmeth.begin(), lmeth.end(), coldstart_cmp);
}

void GatheredTypes::sort_dexmethod_emitlist_profiled_order(
    std::vector<DexMethod*>& lmeth) {
  // Use std::ref to avoid comparator copies.
  redex_assert(m_config != nullptr);

  MethodProfileOrderingConfig* config =
      m_config->get_global_config()
          .get_config_by_name<MethodProfileOrderingConfig>(
              "method_profile_order");

  method_profiles::dexmethods_profiled_comparator comparator(
      lmeth,
      /*method_profiles=*/&m_config->get_method_profiles(),
      config);
  std::stable_sort(lmeth.begin(), lmeth.end(), std::ref(comparator));
}

void GatheredTypes::sort_dexmethod_emitlist_clinit_order(
    std::vector<DexMethod*>& lmeth) {
  std::stable_sort(lmeth.begin(), lmeth.end(),
                   [](const DexMethod* a, const DexMethod* b) {
                     return method::is_clinit(a) && !method::is_clinit(b);
                   });
}

DexOutputIdx GatheredTypes::get_dodx() {
  /*
   * These are symbol table indices.  Symbols which are used
   * should be bunched together.  We will pass a different
   * sort routine here to optimize.  Doing so does violate
   * the dex spec.  However, that aspect of the spec is only
   * used in certain scenarios.  For strings, types, and protos
   * that aspect of the spec has no runtime dependency.  For
   * methods and fields, only dexes with annotations have a
   * dependency on ordering.
   */
  auto proto = get_proto_index();
  auto typelist = get_typelist_list(&proto);
  return DexOutputIdx(get_string_index(),
                      get_type_index(),
                      std::move(proto),
                      get_field_index(),
                      get_method_index(),
                      std::move(typelist),
                      get_callsite_index(),
                      get_methodhandle_index());
}

namespace {

template <typename Cout, typename Cin, typename Cmp>
Cout create_index(Cin& in, const Cmp& cmp) {
  std::sort(in.begin(), in.end(), cmp);
  Cout sidx{};
  sidx.reserve(in.size());
  uint32_t idx = 0;
  for (auto it = in.begin(); it != in.end(); it++) {
    sidx.insert(std::make_pair(*it, idx++));
  }
  return sidx;
}

} // namespace

dexstring_to_idx GatheredTypes::get_string_index(cmp_dstring cmp) {
  return create_index<dexstring_to_idx>(m_lstring, cmp);
}

dextype_to_idx GatheredTypes::get_type_index(cmp_dtype cmp) {
  return create_index<dextype_to_idx>(m_ltype, cmp);
}

dexfield_to_idx GatheredTypes::get_field_index(cmp_dfield cmp) {
  return create_index<dexfield_to_idx>(m_lfield, cmp);
}

dexmethod_to_idx GatheredTypes::get_method_index(cmp_dmethod cmp) {
  return create_index<dexmethod_to_idx>(m_lmethod, cmp);
}

dexproto_to_idx GatheredTypes::get_proto_index(cmp_dproto cmp) {
  // TODO: Profile and see whether a set first would be more efficient.
  std::vector<DexProto*> protos;
  protos.reserve(m_lmethod.size() + m_lcallsite.size());
  for (auto const& m : m_lmethod) {
    protos.push_back(m->get_proto());
  }
  for (auto const& c : m_lcallsite) {
    protos.push_back(c->method_type());
    for (const auto& arg : c->args()) {
      // n.b. how deep could this recursion go? what if there was a method
      // handle here?
      if (arg->evtype() == DEVT_METHOD_TYPE) {
        protos.push_back(
            (dynamic_cast<DexEncodedValueMethodType*>(arg.get()))->proto());
      }
    }
  }
  std::sort(protos.begin(), protos.end());
  protos.erase(std::unique(protos.begin(), protos.end()), protos.end());
  return create_index<dexproto_to_idx>(protos, cmp);
}

std::vector<DexTypeList*> GatheredTypes::get_typelist_list(
    dexproto_to_idx* protos, cmp_dtypelist /*cmp*/) {
  std::vector<DexTypeList*> typel{};
  auto class_defs_size = (uint32_t)m_classes->size();
  typel.reserve(protos->size() + class_defs_size);

  for (auto& it : UnorderedIterable(*protos)) {
    auto* proto = it.first;
    typel.push_back(proto->get_args());
  }
  for (uint32_t i = 0; i < class_defs_size; i++) {
    DexClass* clz = m_classes->at(i);
    typel.push_back(clz->get_interfaces());
  }
  sort_unique(typel, compare_dextypelists);
  return typel;
}

dexcallsite_to_idx GatheredTypes::get_callsite_index(cmp_callsite cmp) {
  return create_index<dexcallsite_to_idx>(m_lcallsite, cmp);
}

dexmethodhandle_to_idx GatheredTypes::get_methodhandle_index(
    cmp_methodhandle cmp) {
  return create_index<dexmethodhandle_to_idx>(m_lmethodhandle, cmp);
}

void GatheredTypes::build_cls_load_map() {
  unsigned int index = 0;
  int type_strings = 0;
  int init_strings = 0;
  int total_strings = 0;
  for (const auto& cls : *m_classes) {
    // gather type first, assuming class load will check all components of a
    // class first
    std::vector<const DexType*> cls_types;
    cls->gather_types(cls_types);
    std::sort(cls_types.begin(), cls_types.end(), compare_dextypes);
    for (const auto& t : cls_types) {
      if (m_cls_load_strings.count(t->get_name()) == 0u) {
        m_cls_load_strings[t->get_name()] = index;
        index++;
        type_strings++;
      }
    }
    // now add in any strings found in <clinit>
    // since they are likely to be accessed during class load
    for (const auto& m : cls->get_dmethods()) {
      if (method::is_clinit(m)) {
        std::vector<const DexString*> method_strings;
        m->gather_strings(method_strings);
        for (const auto& s : method_strings) {
          if (m_cls_load_strings.count(s) == 0u) {
            m_cls_load_strings[s] = index;
            index++;
            init_strings++;
          }
        }
      }
    }
  }
  total_strings += type_strings + init_strings;
  for (const auto& cls : *m_classes) {
    // now add all other strings in class order. This way we get some
    // locality if a random class in a dex is loaded and then executes some
    // methods
    std::vector<const DexClass*> v;
    v.push_back(cls);
    walk::methods(v, [&](DexMethod* m) {
      std::vector<const DexString*> method_strings;
      m->gather_strings(method_strings);
      for (const auto& s : method_strings) {
        if (m_cls_load_strings.count(s) == 0u) {
          m_cls_load_strings[s] = index;
          index++;
          total_strings++;
        }
      }
    });
  }

  TRACE(CUSTOMSORT, 1,
        "found %d strings from types, %d from strings in init methods, %d "
        "total strings",
        type_strings, init_strings, total_strings);
}

void GatheredTypes::build_cls_map() {
  int index = 0;
  for (const auto& cls : *m_classes) {
    if (m_cls_strings.count(cls->get_name()) == 0u) {
      m_cls_strings[cls->get_name()] = index++;
    }
  }
}

void GatheredTypes::build_method_map() {
  unsigned int index = 0;
  for (const auto& cls : *m_classes) {
    for (const auto& m : cls->get_dmethods()) {
      if (m_methods_in_cls_order.count(m) == 0u) {
        m_methods_in_cls_order[m] = index;
      }
    }
    for (const auto& m : cls->get_vmethods()) {
      if (m_methods_in_cls_order.count(m) == 0u) {
        m_methods_in_cls_order[m] = index;
      }
    }
    index++;
  }
}

namespace {

// Headroom past the size policy, so that an item which overshoots the policy
// still lands inside the allocation and is reported by inc_offset with its
// actionable message, rather than by ensure_fits as a memory-safety failure.
//
// INVARIANT: this must be at least the largest single encoded item. It is not
// checked -- no static bound on item size exists -- so if a producer can emit
// more than this, the diagnostic silently degrades to the allocation check.
// Not a "red zone": nothing overshoots into it accidentally any more, because
// every write is bounds-checked before it happens.
constexpr uint32_t k_output_margin = 250000;

constexpr uint32_t k_default_max_dex_size = 64 * 1024 * 1024;

// Upper bound on the configured value. The whole allocation -- the configured
// value, doubled for BytecodeDebugger, plus the red zone -- has to fit in a
// 32-bit byte count: m_offset is a uint32_t cursor into it, and m_output_size
// is a size_t, which is 32 bits on the i686 OSS CI configuration.
//
// Bounding only the configured value is not enough. At (2^31 - 4) the doubled
// total is 4295217288, which truncates to 249992 there and makes
// `m_output_size - k_output_margin` underflow to ~1.8e19 -- disarming the
// very check this is meant to arm.
//
// uint64_t rather than size_t for the same reason: a size_t return would leave
// the caller's `* 2` wrapping in 32-bit arithmetic on i686.
constexpr uint64_t k_max_dex_output_size =
    (uint64_t{UINT32_MAX} - k_output_margin) / 2;

uint64_t get_dex_output_size(const ConfigFiles& conf) {
  size_t output_size;
  conf.get_json_config().get("dex_output_buffer_size", k_default_max_dex_size,
                             output_size);
  always_assert_log(
      output_size <= k_max_dex_output_size,
      "dex_output_buffer_size is %zu, above the maximum of %" PRIu64
      ". Lower `-J dex_output_buffer_size=`.",
      output_size, k_max_dex_output_size);
  return output_size;
}

// Keep signed-result validation and bound validation inseparable so a new
// bounded encoder cannot adopt one without the other.
uint64_t checked_encoded_size_within(
    int size,
    uint64_t bound,
    const char* producer,
    const std::function<std::string()>& describe_subject) {
  always_assert_log(size >= 0, "%s returned %d for %s", producer, size,
                    describe_subject().c_str());
  auto encoded = static_cast<uint64_t>(size);
  always_assert_log(encoded <= bound,
                    "%s wrote %" PRIu64
                    " bytes but its bound promised at most %" PRIu64 " for %s",
                    producer, encoded, bound, describe_subject().c_str());
  return encoded;
}

} // namespace

CodeItemEmit::CodeItemEmit(DexMethod* meth, DexCode* c, dex_code_item* ci)
    : method(meth), code(c), code_item(ci) {}

namespace {
// DO NOT CHANGE THESE VALUES! Many services will break if you do.
constexpr const char* METHOD_MAPPING = "redex-method-id-map.txt";
constexpr const char* CLASS_MAPPING = "redex-class-id-map.txt";
constexpr const char* BYTECODE_OFFSET_MAPPING = "redex-bytecode-offset-map.txt";
constexpr const char* REDEX_PG_MAPPING = "redex-class-rename-map.txt";
constexpr const char* REDEX_INVOKE_MAPPING = "redex-invoke-map.jsonl";
constexpr const char* REDEX_FULL_MAPPING = "redex-full-rename-map.txt";
} // namespace

DexOutput::DexOutput(
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
    DexOutputConfig dex_output_config,
    int min_sdk)
    : m_classes(classes),
      m_output_size((debug_info_kind == DebugInfoKind::BytecodeDebugger
                         ? get_dex_output_size(config_files) * 2
                         : get_dex_output_size(config_files)) +
                    k_output_margin),
      m_output(std::make_unique<uint8_t[]>(m_output_size)),
      m_gtypes(std::move(gtypes)),
      m_dodx(m_gtypes->get_dodx()),
      // Required because the BytecodeDebugger setting creates huge amounts
      // of debug information (multiple dex debug entries per instruction)
      m_offset(0),
      m_iodi_metadata(iodi_metadata),
      m_config_files(config_files),
      m_min_sdk(min_sdk),
      m_dex_output_config(std::move(dex_output_config)) {
  // The buffer is not memset here: std::make_unique<uint8_t[]> already
  // value-initializes it. The zero fill is load-bearing, not hygiene --
  // align_output() advances the cursor without writing, and finalize_header
  // hashes the gaps it leaves behind.
  always_assert_log(
      m_dodx.method_to_idx().size() <= kMaxMethodRefs,
      "Trying to encode too many method refs in dex %s: %zu (limit: %zu). Run "
      "with check_properties_deep turned on.",
      boost::filesystem::path(path).filename().c_str(),
      m_dodx.method_to_idx().size(),
      kMaxMethodRefs);
  always_assert_log(
      m_dodx.field_to_idx().size() <= kMaxFieldRefs,
      "Trying to encode too many field refs in dex %s: %zu (limit: %zu). Run "
      "with check_properties_deep turned on.",
      boost::filesystem::path(path).filename().c_str(),
      m_dodx.field_to_idx().size(),
      kMaxFieldRefs);

  m_filename = path;
  m_pos_mapper = pos_mapper;
  m_method_to_id = method_to_id;
  m_code_debug_lines = code_debug_lines;
  m_method_mapping_filename = config_files.metafile(METHOD_MAPPING);
  m_class_mapping_filename = config_files.metafile(CLASS_MAPPING);
  m_pg_mapping_filename = config_files.metafile(REDEX_PG_MAPPING);
  m_invoke_mapping_filename = config_files.metafile(REDEX_INVOKE_MAPPING);
  m_full_mapping_filename = config_files.metafile(REDEX_FULL_MAPPING);
  m_bytecode_offset_filename = config_files.metafile(BYTECODE_OFFSET_MAPPING);
  m_store_number = store_number;
  m_store_name = store_name;
  m_dex_number = dex_number;
  m_normal_primary_dex = normal_primary_dex;
  m_debug_info_kind = debug_info_kind;
}

void DexOutput::insert_map_item(uint16_t maptype,
                                uint32_t size,
                                uint32_t offset,
                                uint32_t bytes) {
  if (size == 0) {
    return;
  }
  dex_map_item item{};
  item.type = maptype;
  item.size = size;
  item.offset = offset;
  m_map_items.emplace_back(item);

  switch (maptype) {
  case TYPE_HEADER_ITEM:
    m_stats.header_item_count += size;
    m_stats.header_item_bytes += bytes;
    break;
  case TYPE_STRING_ID_ITEM:
    m_stats.string_id_count += size;
    m_stats.string_id_bytes += bytes;
    break;
  case TYPE_TYPE_ID_ITEM:
    m_stats.type_id_count += size;
    m_stats.type_id_bytes += bytes;
    break;
  case TYPE_PROTO_ID_ITEM:
    m_stats.proto_id_count += size;
    m_stats.proto_id_bytes += bytes;
    break;
  case TYPE_FIELD_ID_ITEM:
    m_stats.field_id_count += size;
    m_stats.field_id_bytes += bytes;
    break;
  case TYPE_METHOD_ID_ITEM:
    m_stats.method_id_count += size;
    m_stats.method_id_bytes += bytes;
    break;
  case TYPE_CLASS_DEF_ITEM:
    m_stats.class_def_count += size;
    m_stats.class_def_bytes += bytes;
    break;
  case TYPE_CALL_SITE_ID_ITEM:
    m_stats.call_site_id_count += size;
    m_stats.call_site_id_bytes += bytes;
    break;
  case TYPE_METHOD_HANDLE_ITEM:
    m_stats.method_handle_count += size;
    m_stats.method_handle_bytes += bytes;
    break;
  case TYPE_MAP_LIST:
    m_stats.map_list_count += size;
    m_stats.map_list_bytes += bytes;
    break;
  case TYPE_TYPE_LIST:
    m_stats.type_list_count += size;
    m_stats.type_list_bytes += bytes;
    break;
  case TYPE_ANNOTATION_SET_REF_LIST:
    m_stats.annotation_set_ref_list_count += size;
    m_stats.annotation_set_ref_list_bytes += bytes;
    break;
  case TYPE_ANNOTATION_SET_ITEM:
    m_stats.annotation_set_count += size;
    m_stats.annotation_set_bytes += bytes;
    break;
  case TYPE_CLASS_DATA_ITEM:
    m_stats.class_data_count += size;
    m_stats.class_data_bytes += bytes;
    break;
  case TYPE_CODE_ITEM:
    m_stats.code_count += size;
    m_stats.code_bytes += bytes;
    break;
  case TYPE_STRING_DATA_ITEM:
    m_stats.string_data_count += size;
    m_stats.string_data_bytes += bytes;
    break;
  case TYPE_DEBUG_INFO_ITEM:
    m_stats.debug_info_count += size;
    m_stats.debug_info_bytes += bytes;
    break;
  case TYPE_ANNOTATION_ITEM:
    m_stats.annotation_count += size;
    m_stats.annotation_bytes += bytes;
    break;
  case TYPE_ENCODED_ARRAY_ITEM:
    m_stats.encoded_array_count += size;
    m_stats.encoded_array_bytes += bytes;
    break;
  case TYPE_ANNOTATIONS_DIR_ITEM:
    m_stats.annotations_directory_count += size;
    m_stats.annotations_directory_bytes += bytes;
    break;
  default:
    break;
  }
}

void DexOutput::generate_string_data(SortMode mode) {
  /*
   * This is an index to position within the string data.  There
   * is no specific ordering specified here for the dex spec.
   * The optimized sort here would be different than the one
   * for the symbol table.  The symbol table should be packed
   * for strings that are used by the opcode const-string.  Whereas
   * this should be ordered by access for page-cache efficiency.
   */
  std::vector<const DexString*> string_order;
  if (mode == SortMode::CLASS_ORDER) {
    TRACE(CUSTOMSORT, 2, "using class order for string pool sorting");
    string_order = m_gtypes->get_cls_order_dexstring_emitlist();
  } else if (mode == SortMode::CLASS_STRINGS) {
    TRACE(CUSTOMSORT, 2, "using class names pack for string pool sorting");
    string_order = m_gtypes->keep_cls_strings_together_emitlist();
  } else {
    TRACE(CUSTOMSORT, 2, "using default string pool sorting");
    string_order = m_gtypes->get_dexstring_emitlist();
  }
  dex_string_id* stringids =
      (dex_string_id*)(m_output.get() + hdr.string_ids_off);

  UnorderedSet<const DexString*> type_names = m_gtypes->index_type_names();

  size_t nrstr = string_order.size();
  const uint32_t str_data_start = m_offset;

  for (const auto* str : string_order) {
    uint32_t idx = m_dodx.stringidx(str);
    TRACE(CUSTOMSORT, 3, "str emit %s", SHOW(str));
    stringids[idx].offset = m_offset;
    ensure_fits(str->get_entry_size(), "string", str->c_str());
    str->encode(m_output.get() + m_offset);
    inc_offset(str->get_entry_size());
    m_stats.num_strings++;
  }

  insert_map_item(TYPE_STRING_DATA_ITEM, (uint32_t)nrstr, str_data_start,
                  m_offset - str_data_start);
}

void DexOutput::generate_type_data() {
  always_assert_log(
      m_dodx.type_to_idx().size() < get_max_type_refs(m_min_sdk),
      "Trying to encode too many type refs in dex %zu: %zu (limit: %zu).\n"
      "NOTE: Please check InterDexPass config flags and set: "
      "`reserved_trefs: %zu` (or larger, until the issue goes away)",
      m_dex_number,
      m_dodx.type_to_idx().size(),
      get_max_type_refs(m_min_sdk),
      m_dodx.type_to_idx().size() - get_max_type_refs(m_min_sdk));

  dex_type_id* typeids = (dex_type_id*)(m_output.get() + hdr.type_ids_off);
  for (const auto& p : UnorderedIterable(m_dodx.type_to_idx())) {
    const auto* t = p.first;
    auto idx = p.second;
    typeids[idx].string_idx = m_dodx.stringidx(t->get_name());
    m_stats.num_types++;
  }
}

void DexOutput::generate_typelist_data() {
  const auto& typel = m_dodx.typelist_list();
  uint32_t tl_start = align(m_offset);
  size_t num_tls = 0;
  for (DexTypeList* tl : typel) {
    if (tl->empty()) {
      m_tl_emit_offsets[tl] = 0;
      continue;
    }
    ++num_tls;
    align_output();
    m_tl_emit_offsets[tl] = m_offset;
    const std::function<std::string()> describe_subject = [tl]() {
      return show(tl);
    };
    uint64_t tl_bound = sizeof(uint32_t) + tl->size() * sizeof(uint16_t);
    ensure_fits(tl_bound, "type list", describe_subject);
    int size = tl->encode(&m_dodx, (uint32_t*)(m_output.get() + m_offset));
    inc_offset(checked_encoded_size_within(
        size, tl_bound, "DexTypeList::encode", describe_subject));
    m_stats.num_type_lists++;
  }
  /// insert_map_item returns early if num_tls is zero
  insert_map_item(TYPE_TYPE_LIST, (uint32_t)num_tls, tl_start,
                  m_offset - tl_start);
}

void DexOutput::generate_proto_data() {
  auto* protoids = (dex_proto_id*)(m_output.get() + hdr.proto_ids_off);
  for (const auto& it : UnorderedIterable(m_dodx.proto_to_idx())) {
    auto* proto = it.first;
    auto idx = it.second;
    protoids[idx].shortyidx = m_dodx.stringidx(proto->get_shorty());
    protoids[idx].rtypeidx = m_dodx.typeidx(proto->get_rtype());
    protoids[idx].param_off = m_tl_emit_offsets.at(proto->get_args());
    m_stats.num_protos++;
  }
}

void DexOutput::generate_field_data() {
  auto* fieldids = (dex_field_id*)(m_output.get() + hdr.field_ids_off);
  for (const auto& it : UnorderedIterable(m_dodx.field_to_idx())) {
    auto* field = it.first;
    auto idx = it.second;
    fieldids[idx].classidx = m_dodx.typeidx(field->get_class());
    fieldids[idx].typeidx = m_dodx.typeidx(field->get_type());
    fieldids[idx].nameidx = m_dodx.stringidx(field->get_name());
    m_stats.num_field_refs++;
  }
}

void DexOutput::generate_method_data() {
  auto* methodids = (dex_method_id*)(m_output.get() + hdr.method_ids_off);
  for (const auto& it : UnorderedIterable(m_dodx.method_to_idx())) {
    auto* method = it.first;
    auto idx = it.second;
    methodids[idx].classidx = m_dodx.typeidx(method->get_class());
    methodids[idx].protoidx = m_dodx.protoidx(method->get_proto());
    methodids[idx].nameidx = m_dodx.stringidx(method->get_name());
    m_stats.num_method_refs++;
  }
}

void DexOutput::generate_class_data() {
  dex_class_def* cdefs = (dex_class_def*)(m_output.get() + hdr.class_defs_off);
  for (uint32_t i = 0; i < hdr.class_defs_size; i++) {
    m_stats.num_classes++;
    DexClass* clz = m_classes->at(i);
    cdefs[i].typeidx = m_dodx.typeidx(clz->get_type());
    cdefs[i].access_flags = clz->get_access();
    cdefs[i].super_idx = m_dodx.typeidx(clz->get_super_class());
    cdefs[i].interfaces_off = 0;
    cdefs[i].annotations_off = 0;
    cdefs[i].interfaces_off = m_tl_emit_offsets[clz->get_interfaces()];
    const auto* source_file = m_pos_mapper->get_source_file(clz);
    if (source_file != nullptr) {
      cdefs[i].source_file_idx = m_dodx.stringidx(source_file);
    } else {
      cdefs[i].source_file_idx = DEX_NO_INDEX;
    }
    if (m_static_values.count(clz) != 0u) {
      cdefs[i].static_values_off = m_static_values[clz];
    } else {
      cdefs[i].static_values_off = 0;
    }
    m_stats.num_fields += static_cast<int64_t>(clz->get_ifields().size() +
                                               clz->get_sfields().size());
    m_stats.num_methods += static_cast<int64_t>(clz->get_vmethods().size() +
                                                clz->get_dmethods().size());
  }
}

void DexOutput::generate_class_data_items() {
  /*
   * First generate a dexcode_to_offset needed for the encoding
   * of class_data_items
   */
  dexcode_to_offset dco;
  uint32_t cdi_start = m_offset;
  for (auto& it : m_code_item_emits) {
    uint32_t offset = (uint32_t)(((uint8_t*)it.code_item) - m_output.get());
    dco[it.code] = offset;
  }
  dex_class_def* cdefs = (dex_class_def*)(m_output.get() + hdr.class_defs_off);
  uint32_t count = 0;
  for (uint32_t i = 0; i < hdr.class_defs_size; i++) {
    DexClass* clz = m_classes->at(i);
    if (!clz->has_class_data()) {
      continue;
    }
    /* No alignment constraints for this data */
    const std::function<std::string()> describe_subject = [clz]() {
      return show(clz);
    };
    uint64_t class_bound = clz->max_encoded_size();
    ensure_fits(class_bound, "class data item", describe_subject);
    int size = clz->encode(&m_dodx, dco, m_output.get() + m_offset);
    uint64_t encoded = checked_encoded_size_within(
        size, class_bound, "DexClass::encode", describe_subject);
    if (m_dex_output_config.write_class_sizes) {
      m_stats.class_size[clz] = encoded;
    }
    cdefs[i].class_data_offset = m_offset;
    inc_offset(encoded);
    count += 1;
  }
  insert_map_item(TYPE_CLASS_DATA_ITEM, count, cdi_start, m_offset - cdi_start);
}

static void sync_all(const Scope& scope) {
  constexpr bool serial = false; // for debugging
  auto fn = [&](DexMethod* m, IRCode&) {
    if (serial) {
      TRACE(MTRANS, 2, "Syncing %s", SHOW(m));
    }
    m->sync();
  };
  if (serial) {
    walk::code(scope, fn);
  } else {
    walk::parallel::code(scope, fn);
  }
}

void DexOutput::generate_code_items(const std::vector<SortMode>& mode) {
  TRACE(MAIN, 2, "generate_code_items");
  /*
   * Optimization note:  We should pass a sort routine to the
   * emitlist to optimize pagecache efficiency.
   */
  uint32_t ci_start = align(m_offset);
  sync_all(*m_classes);

  // Get all methods.
  std::vector<DexMethod*> lmeth = m_gtypes->get_dexmethod_emitlist();

  // Repeatedly perform stable sorts starting with the last (least important)
  // sorting method specified.
  for (auto it = mode.rbegin(); it != mode.rend(); ++it) {
    switch (*it) {
    case SortMode::CLASS_ORDER:
      TRACE(CUSTOMSORT, 2, "using class order for bytecode sorting");
      m_gtypes->sort_dexmethod_emitlist_cls_order(lmeth);
      break;
    case SortMode::METHOD_PROFILED_ORDER:
      TRACE(CUSTOMSORT, 2, "using method profiled order for bytecode sorting");
      m_gtypes->sort_dexmethod_emitlist_profiled_order(lmeth);
      break;
    case SortMode::METHOD_COLDSTART_ORDER:
      TRACE(CUSTOMSORT, 2, "using bps ordering for coldstart");
      m_gtypes->sort_dexmethod_emitlist_coldstart_order(lmeth);
      break;
    case SortMode::CLINIT_FIRST:
      TRACE(CUSTOMSORT, 2,
            "sorting <clinit> sections before all other bytecode");
      m_gtypes->sort_dexmethod_emitlist_clinit_order(lmeth);
      break;
    case SortMode::CLASS_STRINGS:
      TRACE(CUSTOMSORT, 2,
            "Unsupported bytecode sorting method SortMode::CLASS_STRINGS");
      break;
    case SortMode::METHOD_SIMILARITY:
      TRACE(CUSTOMSORT, 2, "using method similarity order");
      m_gtypes->sort_dexmethod_emitlist_method_similarity_order(lmeth);
      break;
    case SortMode::DEFAULT:
      TRACE(CUSTOMSORT, 2, "using default sorting order");
      m_gtypes->sort_dexmethod_emitlist_default_order(lmeth);
      break;
    }
  }
  for (DexMethod* meth : lmeth) {
    if ((meth->get_access() & (ACC_ABSTRACT | ACC_NATIVE)) != 0u) {
      // There is no code item for ABSTRACT or NATIVE methods.
      continue;
    }
    TRACE(CUSTOMSORT, 3, "method emit %s %s", SHOW(meth->get_class()),
          SHOW(meth));
    DexCode* code = meth->get_dex_code();
    always_assert_log(
        meth->is_concrete() && code != nullptr,
        "Undefined method in generate_code_items()\n\t prototype: %s\n",
        SHOW(meth));
    align_output();
    const std::function<std::string()> describe_method = [meth]() {
      return show(meth);
    };
    uint64_t code_bound = code->max_encoded_size();
    ensure_fits(code_bound, "code item", describe_method);
    int size = code->encode(
        &m_dodx, reinterpret_cast<uint32_t*>(m_output.get() + m_offset));
    uint64_t encoded = checked_encoded_size_within(
        size, code_bound, "DexCode::encode", describe_method);
    check_method_instruction_size_limit(m_config_files, size, describe_method);
    if (m_dex_output_config.write_method_sizes) {
      m_stats.method_size[meth] = encoded;
    }
    m_method_bytecode_offsets.emplace_back(meth->get_name()->c_str(), m_offset);
    m_code_item_emits.emplace_back(meth, code,
                                   (dex_code_item*)(m_output.get() + m_offset));
    auto insns_size =
        ((const dex_code_item*)(m_output.get() + m_offset))->insns_size;
    inc_offset(encoded);
    m_stats.num_instructions +=
        static_cast<int64_t>(code->get_instructions().size());
    m_stats.num_tries += static_cast<int64_t>(code->get_tries().size());
    m_stats.instruction_bytes += static_cast<int64_t>(insns_size) * 2;
  }
  /// insert_map_item returns early if m_code_item_emits is empty
  insert_map_item(TYPE_CODE_ITEM, (uint32_t)m_code_item_emits.size(), ci_start,
                  m_offset - ci_start);
}

void DexOutput::generate_callsite_data() {
  auto callsites = m_gtypes->get_dexcallsite_emitlist();
  // Redundant on today's code -- gather_components sort_uniques the list, so
  // the emit list and the reserved id count are equal by construction -- but
  // they are two different quantities arriving by two different routes, and
  // this is the assertion that says so.
  always_assert_log(callsites.size() == m_dodx.callsitesize(),
                    "call site emit list has %zu entries but %zu ids were "
                    "reserved",
                    callsites.size(), m_dodx.callsitesize());
  auto* dexcallsites =
      reinterpret_cast<dex_callsite_id*>(m_output.get() + m_callsite_start);
  for (uint32_t i = 0; i < callsites.size(); i++) {
    m_stats.num_callsites++;
    DexCallSite* callsite = callsites.at(i);
    dexcallsites[i].callsite_off = m_call_site_items[callsite];
  }
}

void DexOutput::generate_methodhandle_data() {
  auto* dexmethodhandles = reinterpret_cast<dex_methodhandle_id*>(
      m_output.get() + m_methodhandle_start);
  // No count assertion to match the call site one: the indices written here
  // come from the same map that sized the reservation, so the two cannot
  // disagree. Drive this loop from an independent list and it would need the
  // same trip-wire.
  for (auto it : UnorderedIterable(m_dodx.methodhandle_to_idx())) {
    m_stats.num_methodhandles++;
    DexMethodHandle* methodhandle = it.first;
    uint32_t idx = it.second;
    dexmethodhandles[idx].method_handle_type = methodhandle->type();
    if (DexMethodHandle::isInvokeType(methodhandle->type())) {
      dexmethodhandles[idx].field_or_method_id =
          m_dodx.methodidx(methodhandle->methodref());
    } else {
      dexmethodhandles[idx].field_or_method_id =
          m_dodx.fieldidx(methodhandle->fieldref());
    }
    dexmethodhandles[idx].unused1 = 0;
    dexmethodhandles[idx].unused2 = 0;
  }
}

void DexOutput::check_method_instruction_size_limit(
    const ConfigFiles& conf,
    int size,
    const std::function<std::string()>& describe_method) {
  always_assert_log(size >= 0, "DexCode::encode returned %d for %s", size,
                    describe_method().c_str());
  const auto encoded = static_cast<uint64_t>(size);
  uint32_t instruction_size_bitwidth_limit =
      conf.get_instruction_size_bitwidth_limit();

  if (instruction_size_bitwidth_limit != 0u) {
    uint64_t hard_instruction_size_limit = 1L
                                           << instruction_size_bitwidth_limit;
    always_assert_log(encoded <= hard_instruction_size_limit,
                      "Size of method exceeded limit. size: %" PRIu64
                      ", limit: %" PRIu64 ", method: %s\n",
                      encoded, hard_instruction_size_limit,
                      describe_method().c_str());
  }
}

void DexOutput::generate_static_values() {
  constexpr size_t initial_buffer_reserve = static_cast<size_t>(32 * 1024);
  uint32_t sv_start = m_offset;
  UnorderedMap<DexEncodedValueArray, uint32_t,
               boost::hash<DexEncodedValueArray>>
      enc_arrays;
  for (uint32_t i = 0; i < hdr.class_defs_size; i++) {
    DexClass* clz = m_classes->at(i);
    // Fields need to be sorted otherwise static values may end up out of order
    auto& sfields = clz->get_sfields();
    std::sort(sfields.begin(), sfields.end(), compare_dexfields);
    auto& ifields = clz->get_ifields();
    std::sort(ifields.begin(), ifields.end(), compare_dexfields);
    std::unique_ptr<DexEncodedValueArray> deva(clz->get_static_values());
    if (!deva) {
      continue;
    }
    if (enc_arrays.count(*deva) != 0u) {
      m_static_values[clz] = enc_arrays.at(*deva);
    } else {
      std::vector<uint8_t> encdata;
      encdata.reserve(initial_buffer_reserve);
      deva->encode(&m_dodx, encdata);
      size_t encdatasize = encdata.size();
      always_assert_log((((uint64_t)encdatasize) >> 32) == 0,
                        "buffer size (%zu) is too big", encdatasize);
      /* No alignment requirements */
      ensure_fits(encdatasize, "static value array",
                  [clz]() { return show(clz); });
      memcpy(m_output.get() + m_offset, encdata.data(), encdatasize);
      enc_arrays.emplace(std::move(*deva), m_offset);
      m_static_values[clz] = m_offset;
      inc_offset(encdatasize);
      m_stats.num_static_values++;
    }
  }
  {
    auto callsites = m_gtypes->get_dexcallsite_emitlist();
    for (uint32_t i = 0; i < callsites.size(); i++) {
      auto* callsite = callsites[i];
      auto eva = callsite->as_encoded_value_array();
      if (enc_arrays.count(eva) != 0u) {
        m_call_site_items[callsite] = enc_arrays.at(eva);
      } else {
        std::vector<uint8_t> encdata;
        encdata.reserve(initial_buffer_reserve);
        eva.encode(&m_dodx, encdata);
        size_t encdatasize = encdata.size();
        always_assert_log((((uint64_t)encdatasize) >> 32) == 0,
                          "buffer size (%zu) is too big", encdatasize);
        ensure_fits(encdatasize, "call site value array", "call site");
        memcpy(m_output.get() + m_offset, encdata.data(), encdatasize);
        enc_arrays.emplace(std::move(eva), m_offset);
        m_call_site_items[callsite] = m_offset;
        inc_offset(encdatasize);
        m_stats.num_static_values++;
      }
    }
  }
  if (!m_static_values.empty() || !m_call_site_items.empty()) {
    insert_map_item(TYPE_ENCODED_ARRAY_ITEM, (uint32_t)enc_arrays.size(),
                    sv_start, m_offset - sv_start);
  }
}

static bool annotation_cmp(const DexAnnotationDirectory* a,
                           const DexAnnotationDirectory* b) {
  return (a->viz_score() < b->viz_score());
}

void DexOutput::unique_annotations(annomap_t& annomap,
                                   std::vector<DexAnnotation*>& annolist) {
  int annocnt = 0;
  uint32_t mentry_offset = m_offset;
  UnorderedMap<std::vector<uint8_t>, uint32_t, VectorHash<uint8_t>>
      annotation_byte_offsets;
  for (auto* anno : annolist) {
    if (annomap.count(anno) != 0u) {
      continue;
    }
    std::vector<uint8_t> annotation_bytes;
    anno->vencode(&m_dodx, annotation_bytes);
    if (annotation_byte_offsets.count(annotation_bytes) != 0u) {
      annomap[anno] = annotation_byte_offsets[annotation_bytes];
      continue;
    }
    /* Insert new annotation in tracking structs */
    annotation_byte_offsets[annotation_bytes] = m_offset;
    annomap[anno] = m_offset;
    /* Not a dupe, encode... */
    ensure_fits(annotation_bytes.size(), "annotation", "annotation");
    uint8_t* annoout = (uint8_t*)(m_output.get() + m_offset);
    memcpy(annoout, annotation_bytes.data(), annotation_bytes.size());
    inc_offset(annotation_bytes.size());
    annocnt++;
  }
  if (annocnt != 0) {
    insert_map_item(TYPE_ANNOTATION_ITEM, annocnt, mentry_offset,
                    m_offset - mentry_offset);
  }
  m_stats.num_annotations += annocnt;
}

void DexOutput::unique_asets(annomap_t& annomap,
                             asetmap_t& asetmap,
                             std::vector<DexAnnotationSet*>& asetlist) {
  int asetcnt = 0;
  uint32_t mentry_offset = align(m_offset);
  UnorderedMap<std::vector<uint32_t>, uint32_t, VectorHash<uint32_t>>
      aset_offsets;
  for (auto* aset : asetlist) {
    if (asetmap.count(aset) != 0u) {
      continue;
    }
    std::vector<uint32_t> aset_bytes;
    aset->vencode(&m_dodx, aset_bytes, annomap);
    if (aset_offsets.count(aset_bytes) != 0u) {
      asetmap[aset] = aset_offsets[aset_bytes];
      continue;
    }
    /* Insert new aset in tracking structs */
    align_output();
    aset_offsets[aset_bytes] = m_offset;
    asetmap[aset] = m_offset;
    /* Not a dupe, encode... */
    ensure_fits(aset_bytes.size() * sizeof(uint32_t), "annotation set",
                "annotation set");
    uint8_t* asetout = (uint8_t*)(m_output.get() + m_offset);
    memcpy(asetout, aset_bytes.data(), aset_bytes.size() * sizeof(uint32_t));
    inc_offset(aset_bytes.size() * sizeof(uint32_t));
    asetcnt++;
  }
  if (asetcnt != 0) {
    insert_map_item(TYPE_ANNOTATION_SET_ITEM, asetcnt, mentry_offset,
                    m_offset - mentry_offset);
  }
}

void DexOutput::unique_xrefs(asetmap_t& asetmap,
                             xrefmap_t& xrefmap,
                             std::vector<ParamAnnotations*>& xreflist) {
  int xrefcnt = 0;
  uint32_t mentry_offset = align(m_offset);
  UnorderedMap<std::vector<uint32_t>, uint32_t, VectorHash<uint32_t>>
      xref_offsets;
  for (auto* xref : xreflist) {
    if (xrefmap.count(xref) != 0u) {
      continue;
    }
    std::vector<uint32_t> xref_bytes;
    xref_bytes.push_back((unsigned int)xref->size());
    for (auto& param : *xref) {
      auto& das = param.second;
      always_assert_log(asetmap.count(das.get()) != 0,
                        "Uninitialized aset %p '%s'", das.get(), SHOW(das));
      xref_bytes.push_back(asetmap[das.get()]);
    }
    if (xref_offsets.count(xref_bytes) != 0u) {
      xrefmap[xref] = xref_offsets[xref_bytes];
      continue;
    }
    /* Insert new xref in tracking structs */
    align_output();
    xref_offsets[xref_bytes] = m_offset;
    xrefmap[xref] = m_offset;
    /* Not a dupe, encode... */
    ensure_fits(xref_bytes.size() * sizeof(uint32_t), "param annotations",
                "param annotations");
    uint8_t* xrefout = (uint8_t*)(m_output.get() + m_offset);
    memcpy(xrefout, xref_bytes.data(), xref_bytes.size() * sizeof(uint32_t));
    inc_offset(xref_bytes.size() * sizeof(uint32_t));
    xrefcnt++;
  }
  if (xrefcnt != 0) {
    insert_map_item(TYPE_ANNOTATION_SET_REF_LIST, xrefcnt, mentry_offset,
                    m_offset - mentry_offset);
  }
}

void DexOutput::unique_adirs(asetmap_t& asetmap,
                             xrefmap_t& xrefmap,
                             adirmap_t& adirmap,
                             std::vector<DexAnnotationDirectory*>& adirlist) {
  int adircnt = 0;
  uint32_t mentry_offset = align(m_offset);
  UnorderedMap<std::vector<uint32_t>, uint32_t, VectorHash<uint32_t>>
      adir_offsets;
  for (auto* adir : adirlist) {
    if (adirmap.count(adir) != 0u) {
      continue;
    }
    std::vector<uint32_t> adir_bytes;
    adir->vencode(&m_dodx, adir_bytes, xrefmap, asetmap);
    if (adir_offsets.count(adir_bytes) != 0u) {
      adirmap[adir] = adir_offsets[adir_bytes];
      continue;
    }
    /* Insert new adir in tracking structs */
    align_output();
    adir_offsets[adir_bytes] = m_offset;
    adirmap[adir] = m_offset;
    /* Not a dupe, encode... */
    ensure_fits(adir_bytes.size() * sizeof(uint32_t), "annotation directory",
                "annotation directory");
    uint8_t* adirout = (uint8_t*)(m_output.get() + m_offset);
    memcpy(adirout, adir_bytes.data(), adir_bytes.size() * sizeof(uint32_t));
    inc_offset(adir_bytes.size() * sizeof(uint32_t));
    adircnt++;
  }
  if (adircnt != 0) {
    insert_map_item(TYPE_ANNOTATIONS_DIR_ITEM, adircnt, mentry_offset,
                    m_offset - mentry_offset);
  }
}

void DexOutput::generate_annotations() {
  /*
   * There are five phases to generating annotations:
   * 1) Emit annotations
   * 2) Emit annotation_sets
   * 3) Emit annotation xref lists for method params
   * 4) Emit annotation_directories
   * 5) Attach annotation_directories to the classdefs
   */
  std::vector<DexAnnotationDirectory*> lad;
  lad.reserve(hdr.class_defs_size);
  UnorderedMap<DexAnnotationDirectory*, int> ad_to_classnum;
  annomap_t annomap;
  asetmap_t asetmap;
  xrefmap_t xrefmap;
  adirmap_t adirmap;

  for (uint32_t i = 0; i < hdr.class_defs_size; i++) {
    DexClass* clz = m_classes->at(i);
    DexAnnotationDirectory* ad = clz->get_annotation_directory();
    if (ad != nullptr) {
      lad.push_back(ad);
      ad_to_classnum[ad] = static_cast<int>(i);
    }
  }
  std::sort(lad.begin(), lad.end(), annotation_cmp);
  for (auto* ad : lad) {
    ad->sort_members();
  }
  std::vector<DexAnnotation*> annolist;
  std::vector<DexAnnotationSet*> asetlist;
  std::vector<ParamAnnotations*> xreflist;
  for (auto* ad : lad) {
    ad->gather_asets(asetlist);
    ad->gather_annotations(annolist);
    ad->gather_xrefs(xreflist);
  }
  // Sort annolist by encoded content to ensure deterministic emission order.
  // Without this, annotation offsets depend on gather order which can vary
  // due to parallel pass execution modifying annotation vectors.
  std::sort(annolist.begin(), annolist.end(),
            [this](DexAnnotation* a, DexAnnotation* b) {
              std::vector<uint8_t> a_bytes, b_bytes;
              a->vencode(&m_dodx, a_bytes);
              b->vencode(&m_dodx, b_bytes);
              return a_bytes < b_bytes;
            });
  unique_annotations(annomap, annolist);
  unique_asets(annomap, asetmap, asetlist);
  unique_xrefs(asetmap, xrefmap, xreflist);
  unique_adirs(asetmap, xrefmap, adirmap, lad);
  for (auto* ad : lad) {
    int class_num = ad_to_classnum[ad];
    dex_class_def* cdefs =
        (dex_class_def*)(m_output.get() + hdr.class_defs_off);
    cdefs[class_num].annotations_off = adirmap[ad];
    delete ad;
  }
}

namespace {
struct DebugMetadata {
  DexDebugItem* dbg{nullptr};
  dex_code_item* dci{nullptr};
  uint32_t line_start{0};
  uint32_t num_params{0};
  size_t bound{0};
  uint64_t size{0};
  uint32_t dex_size{0};
  std::vector<std::unique_ptr<DexDebugInstruction>> dbgops;
};

DebugMetadata calculate_debug_metadata(
    DexDebugItem* dbg,
    DexCode* dc,
    dex_code_item* dci,
    PositionMapper* pos_mapper,
    uint32_t num_params,
    UnorderedMap<DexCode*, std::vector<DebugLineItem>>* dbg_lines,
    uint32_t line_addin) {
  std::vector<DebugLineItem> debug_line_info;
  DebugMetadata metadata;
  metadata.dbg = dbg;
  metadata.dci = dci;
  metadata.num_params = num_params;
  metadata.dbgops = generate_debug_instructions(
      dbg, pos_mapper, &metadata.line_start, &debug_line_info, line_addin);
  metadata.bound =
      DexDebugItem::max_encoded_size(metadata.num_params, metadata.dbgops);
  if (dbg_lines != nullptr) {
    (*dbg_lines)[dc] = debug_line_info;
  }
  return metadata;
}

// Check before calling `DexDebugItem::encode`, whose raw output pointer has no
// end. Return the bound so callers can verify the reported size afterwards.
uint64_t check_debug_item_fits(uint64_t bound,
                               uint64_t offset,
                               uint64_t capacity,
                               uint64_t* checked_through) {
  always_assert_log(offset + bound <= capacity,
                    "A debug program of up to %" PRIu64
                    " bytes does not fit at offset %" PRIu64 " of a %" PRIu64
                    "-byte buffer.",
                    bound, offset, capacity);
  if (checked_through != nullptr) {
    // Each check covers only this write.
    *checked_through = offset + bound;
  }
  return bound;
}

uint64_t emit_debug_info_for_metadata(DexOutputIdx* dodx,
                                      const DebugMetadata& metadata,
                                      const DexMethod* method,
                                      uint8_t* output,
                                      uint64_t offset,
                                      uint64_t capacity,
                                      uint64_t* checked_through,
                                      bool set_dci_offset = true) {
  uint64_t bound =
      check_debug_item_fits(metadata.bound, offset, capacity, checked_through);
  int size = DexDebugItem::encode(dodx, output + offset, metadata.line_start,
                                  metadata.num_params, metadata.dbgops);
  uint64_t encoded = checked_encoded_size_within(
      size, bound, "DexDebugItem::encode", [method]() { return show(method); });
  if (set_dci_offset) {
    // debug_info_off is a 32-bit dex field, so the 64-bit cursor has to narrow
    // here. Assert rather than truncate: a wrapped value is a valid-looking
    // offset that points at the header.
    always_assert_log(offset <= UINT32_MAX,
                      "debug program sits at offset %" PRIu64
                      ", past what debug_info_off can address",
                      offset);
    metadata.dci->debug_info_off = (uint32_t)offset;
  }
  return encoded;
}

uint64_t emit_debug_info(
    DexOutputIdx* dodx,
    bool emit_positions,
    DexDebugItem* dbg,
    const DexMethod* method,
    DexCode* dc,
    dex_code_item* dci,
    PositionMapper* pos_mapper,
    uint8_t* output,
    uint64_t offset,
    uint64_t capacity,
    uint64_t* checked_through,
    uint32_t num_params,
    UnorderedMap<DexCode*, std::vector<DebugLineItem>>* dbg_lines) {
  // No align requirement for debug items.
  DebugMetadata metadata = calculate_debug_metadata(
      dbg, dc, dci, pos_mapper, num_params, dbg_lines, /*line_addin=*/0);
  return emit_positions
             ? emit_debug_info_for_metadata(dodx, metadata, method, output,
                                            offset, capacity, checked_through)
             : 0;
}

struct MethodKey {
  const DexMethod* method;
  uint32_t size;
};
struct MethodKeyCompare {
  // We want to sort using size as a major key and method as a minor key. The
  // minor key only exists to ensure different methods get different entries,
  // even if they have the same size as another method.
  bool operator()(const MethodKey& left, const MethodKey& right) const {
    if (left.size == right.size) {
      return compare_dexmethods(left.method, right.method);
    } else {
      return left.size > right.size;
    }
  }
};
using DebugSize = uint64_t;
using DebugMethodMap = std::map<MethodKey, DebugSize, MethodKeyCompare>;

// Iterator-like struct that gives an order of param-sizes to visit induced
// by unvisited cluster methods.
struct ParamSizeOrder {
  // This is OK. Java methods are limited to 256 parameters.
  std::bitset<257> param_size_done;

  const UnorderedMap<const DexMethod*, DebugMetadata>& method_data;

  std::vector<const DexMethod*>::const_iterator method_cur;
  std::vector<const DexMethod*>::const_iterator method_end;
  UnorderedSet<const DexMethod*> skip_methods;

  std::map<uint32_t, DebugMethodMap>::const_iterator map_cur, map_end;

  ParamSizeOrder(
      const UnorderedMap<const DexMethod*, DebugMetadata>& method_data,
      const std::vector<const DexMethod*>& methods,
      std::map<uint32_t, DebugMethodMap>::const_iterator begin,
      std::map<uint32_t, DebugMethodMap>::const_iterator end)
      : method_data(method_data),
        method_cur(methods.begin()),
        method_end(methods.end()),
        map_cur(begin),
        map_end(end) {}

  void skip(const DexMethod* m) { skip_methods.insert(m); }

  int32_t next() {
    auto get_size = [&](const DexMethod* m) {
      return method_data.at(m).num_params;
    };
    while (method_cur != method_end) {
      const auto* m = *method_cur;
      ++method_cur;

      if (skip_methods.count(m) != 0) {
        continue;
      }

      auto size = get_size(m);
      if (param_size_done.test(size)) {
        continue;
      }

      param_size_done.set(size);
      return static_cast<int32_t>(size);
    }

    while (map_cur != map_end) {
      auto size = map_cur->first;
      ++map_cur;

      if (param_size_done.test(size)) {
        continue;
      }

      param_size_done.set(size);
      return static_cast<int32_t>(size);
    }

    return -1;
  }
};

uint64_t emit_instruction_offset_debug_info_helper(
    DexOutputIdx* dodx,
    PositionMapper* pos_mapper,
    std::vector<CodeItemEmit*>& code_items,
    IODIMetadata& iodi_metadata,
    size_t iodi_layer,
    uint32_t line_addin,
    size_t store_number,
    size_t dex_number,
    uint8_t* output,
    uint64_t offset,
    uint64_t capacity,
    uint64_t* checked_through,
    int* dbgcount,
    UnorderedMap<DexCode*, std::vector<DebugLineItem>>* code_debug_map) {
  // Algo is as follows:
  // 1) Collect method sizes for each method of N params
  // 2) For each arity:
  //   2.1) Determine the biggest methods that we will support (see below)
  //   2.2) Emit one debug program that will emit a position for each pc up to
  //        the size calculated in 2.1
  // 3) Tie all code items back to debug program emitted in (2) and emit
  //    any normal debug info for any methods that can't use IODI (either due
  //    to being too big or being unsupported)

  // 1)
  std::map<uint32_t, DebugMethodMap> param_to_sizes;
  UnorderedMap<const DexMethod*, DebugMetadata> method_to_debug_meta;
  // Scratch for measuring normal debug programs. Growth need not preserve or
  // initialize its contents.
  std::unique_ptr<uint8_t[]> temporary_buffer;
  size_t temporary_buffer_size = 0;
  UnorderedMap<const DexMethod*, std::vector<const DexMethod*>>
      clustered_methods;

  for (auto& it : code_items) {
    DexCode* dc = it->code;
    auto* const dbg_item = dc->get_debug_item();
    redex_assert(dbg_item);
    DexMethod* method = it->method;
    redex_assert(!iodi_metadata.is_huge(method));
    uint32_t param_size =
        static_cast<uint32_t>(method->get_proto()->get_args()->size());
    // We still want to fill in pos_mapper and code_debug_map, so run the
    // usual code to emit debug info. We cache this and use it later if
    // it turns out we want to emit normal debug info for a given method.
    DebugMetadata metadata =
        calculate_debug_metadata(dbg_item, dc, it->code_item, pos_mapper,
                                 param_size, code_debug_map, line_addin);

    size_t required = metadata.bound;
    if (temporary_buffer_size < required) {
      size_t new_size = temporary_buffer_size <= SIZE_MAX / 2
                            ? std::max(required, temporary_buffer_size * 2)
                            : required;
      temporary_buffer.reset();
      temporary_buffer.reset(new uint8_t[new_size]);
      temporary_buffer_size = new_size;
    }
    uint64_t debug_size = emit_debug_info_for_metadata(
        dodx, metadata, method, temporary_buffer.get(), 0,
        temporary_buffer_size, /*checked_through=*/nullptr, false);
    metadata.size = debug_size;
    const auto dex_size = dc->size();
    metadata.dex_size = dex_size;
    method_to_debug_meta.emplace(method, std::move(metadata));
    if (iodi_metadata.is_huge(method)) {
      continue;
    }
    auto res = param_to_sizes[param_size].emplace(MethodKey{method, dex_size},
                                                  debug_size);
    always_assert_log(res.second, "Failed to insert %s, %u pair", SHOW(method),
                      dc->size());
    if (iodi_metadata.is_in_global_cluster(method)) {
      clustered_methods[iodi_metadata.get_canonical_method(method)].push_back(
          method);
    }
  }
  // Release the scratch before the rest of the function runs; it can be the
  // largest single allocation here and nothing below reads it.
  temporary_buffer.reset();
  temporary_buffer_size = 0;

  unordered_erase_if(clustered_methods,
                     [](auto& p) { return p.second.size() <= 1; });

  std::vector<const DexMethod*> cluster_induced_order;
  for (const auto& p : UnorderedIterable(clustered_methods)) {
    cluster_induced_order.insert(cluster_induced_order.end(), p.second.begin(),
                                 p.second.end());
  }
  std::sort(
      cluster_induced_order.begin(), cluster_induced_order.end(),
      [&method_to_debug_meta](const DexMethod* lhs, const DexMethod* rhs) {
        if (lhs == rhs) {
          return false;
        }
        const auto& lhs_dbg = method_to_debug_meta.at(lhs);
        const auto& rhs_dbg = method_to_debug_meta.at(rhs);

        // Larger debug programs first.
        if (lhs_dbg.size != rhs_dbg.size) {
          return lhs_dbg.size > rhs_dbg.size;
        }

        // More parameters next.
        if (lhs_dbg.num_params != rhs_dbg.num_params) {
          return lhs_dbg.num_params > rhs_dbg.num_params;
        }

        // Some stable order.
        return compare_dexmethods(lhs, rhs);
      });

  ParamSizeOrder pso{method_to_debug_meta, cluster_induced_order,
                     param_to_sizes.begin(), param_to_sizes.end()};

  // 2)
  bool requires_iodi_programs =
      iodi_layer > 0 ||
      (iodi_metadata.layer_mode == IODIMetadata::IODILayerMode::kFull) ||
      (iodi_metadata.layer_mode ==
           IODIMetadata::IODILayerMode::kSkipLayer0AtApi26 &&
       iodi_metadata.min_sdk < 26) ||
      (iodi_metadata.layer_mode ==
           IODIMetadata::IODILayerMode::kAlwaysSkipLayer0ExceptPrimary &&
       store_number == 0 && dex_number == 0);
  uint64_t initial_offset = offset;
  for (int32_t size = pso.next(); size != -1; size = pso.next()) {
    auto param_size = size;
    const auto& dbg_sizes = param_to_sizes.at(size);

    if (dbg_sizes.empty()) {
      // May happen through cluster removal.
      continue;
    }

    // Find clustered methods in this param size.
    UnorderedMap<const DexMethod*, std::vector<MethodKey>> clusters_in_sizes;
    for (const auto& p : dbg_sizes) {
      clusters_in_sizes[iodi_metadata.get_canonical_method(p.first.method)]
          .push_back(p.first);
    }
    unordered_erase_if(clusters_in_sizes,
                       [](auto& p) { return p.second.size() == 1; });
    size_t combinations = 1;
    for (const auto& p : UnorderedIterable(clusters_in_sizes)) {
      combinations *= p.second.size();
    }
    TRACE(IODI, 4, "Cluster combinations=%zu size=%zu", combinations,
          clusters_in_sizes.size());

    // 2.1) We determine the methods to use IODI with a single plan, which
    // has to satisfy two constraints:
    //   2.1.1) Do not cause an OOM in dexlayout on Android 8+
    //   2.1.2) Do not increase uncompressed APK size

    // 2.1.1) Android 8+ dexlayout inflates each shared debug program once per
    // referencing method. Bound both each program and the total footprint so
    // this repeated work cannot exhaust the optimizer. `plan_programs` owns
    // those limits and splits one arity across several programs when needed.
    using Iter = DebugMethodMap::const_iterator;

    // Returns the plan's byte cost; unless this is a dry run, also emits the
    // programs and records each method's assignment.
    auto compute = [&](const auto& sizes, bool dry_run) -> uint64_t {
      std::vector<uint32_t> method_sizes;
      std::vector<uint64_t> normal_debug_sizes;
      method_sizes.reserve(sizes.size());
      normal_debug_sizes.reserve(sizes.size());
      for (const auto& entry : sizes) {
        method_sizes.push_back(entry.first.size);
        normal_debug_sizes.push_back(entry.second);
      }

      // 2.1.2) Whether a method pays for IODI is decided against the programs
      // that are actually emitted: a method using IODI costs nothing beyond
      // the program it shares, while excluding it costs its normal debug
      // program but can shorten, merge or remove a program. The plan weighs
      // those alternatives in encoded bytes, and so also opts out of IODI for
      // the whole arity when normal debug info is no larger.
      const auto plan = iodi::plan_programs(method_sizes, normal_debug_sizes,
                                            static_cast<uint32_t>(param_size),
                                            line_addin, requires_iodi_programs);
      if (dry_run) {
        return plan.total_debug_size;
      }

      const Iter end = sizes.end();
      const Iter first_iodi = std::next(sizes.begin(), plan.first_iodi_index);
      // Mark excluded methods to emit normal debug info below.
      for (auto big = sizes.begin(); big != first_iodi; ++big) {
        iodi_metadata.mark_method_huge(big->first.method);
        TRACE(IODI, 3,
              "[IODI] %s is too large to benefit from IODI: %u vs %" PRIu64,
              SHOW(big->first.method), big->first.size, big->second);
      }
      const size_t num_users = sizes.size() - plan.first_iodi_index;
      TRACE(IODI, 2,
            "[IODI] @%" PRIu64
            "(%d): Of %zu methods %zu were too big, %zu use %zu "
            "programs inflating to %zu entries and costing %zu bytes",
            offset, param_size, sizes.size(), plan.first_iodi_index, num_users,
            plan.programs.size(), plan.total_inflated_footprint,
            plan.total_debug_size);

      // 2.2) Emit the planned IODI programs.
      const uint64_t programs_start = offset;
      std::vector<uint64_t> program_offsets;
      program_offsets.reserve(plan.programs.size());
      for (const auto& program : plan.programs) {
        TRACE(IODI, 3, "  - %u methods in program of size %u @ %" PRIu64,
              program.user_count, program.size, offset);
        program_offsets.push_back(offset);
        std::vector<std::unique_ptr<DexDebugInstruction>> dbgops;
        dbgops.reserve(program.size);
        if (program.size > 0) {
          // First emit an entry for pc = 0 -> line = start
          dbgops.push_back(DexDebugInstruction::create_line_entry(0, 0));
          // Now emit an entry for each pc thereafter
          // (0x1e increments addr+line by 1)
          for (size_t i = 1; i < program.size; i++) {
            dbgops.push_back(DexDebugInstruction::create_line_entry(1, 1));
          }
        }
        const auto arity = static_cast<uint32_t>(param_size);
        uint64_t bound =
            check_debug_item_fits(DexDebugItem::max_encoded_size(arity, dbgops),
                                  offset, capacity, checked_through);
        const std::function<std::string()> describe_program =
            [arity, program_size = program.size,
             user_count = program.user_count, offset]() {
              return "IODI program: arity=" + std::to_string(arity) +
                     ", method_size=" + std::to_string(program_size) +
                     ", methods=" + std::to_string(user_count) +
                     ", offset=" + std::to_string(offset);
            };
        uint64_t encoded = checked_encoded_size_within(
            DexDebugItem::encode(nullptr, output + offset, line_addin, arity,
                                 dbgops),
            bound, "DexDebugItem::encode", describe_program);
        always_assert_log(
            encoded == program.encoded_size,
            "IODI planner predicted %zu bytes for arity %u, size %u, and %u "
            "users, but DexDebugItem::encode wrote %" PRIu64,
            program.encoded_size, arity, program.size, program.user_count,
            encoded);
        offset += encoded;
        *dbgcount += 1;
      }

      size_t method_index = 0;
      for (const auto& entry : sizes) {
        const auto program_index = plan.program_of_method[method_index++];
        if (program_index == iodi::Plan::kNoProgram) {
          continue;
        }
        always_assert_log(program_index < plan.programs.size(),
                          "Expected an IODI program for %s",
                          SHOW(entry.first.method));
        const auto& program = plan.programs[program_index];
        always_assert_log(
            program.size >= entry.first.size,
            "Expected an IODI program of at least %u for %s, got %u",
            entry.first.size, SHOW(entry.first.method), program.size);
        uint64_t program_offset = program_offsets[program_index];
        // Same 32-bit dex field as in emit_debug_info_for_metadata: program
        // offsets are tracked in 64 bits, so narrowing here is checked rather
        // than silent.
        always_assert_log(program_offset <= UINT32_MAX,
                          "IODI program for %s sits at offset %" PRIu64
                          ", past what debug_info_off can address",
                          SHOW(entry.first.method), program_offset);
        method_to_debug_meta.at(entry.first.method).dci->debug_info_off =
            static_cast<uint32_t>(program_offset);
      }

      if (traceEnabled(IODI, 4)) {
        double ammortized_cost =
            num_users > 0
                ? (double)(offset - programs_start) / (double)num_users
                : 0;
        for (auto it = first_iodi; it != end; it++) {
          TRACE(IODI, 4,
                "[IODI][savings] %s saved %" PRIu64
                " bytes (%u), cost of %f, net %f",
                SHOW(it->first.method), it->second, it->first.size,
                ammortized_cost, (double)it->second - ammortized_cost);
        }
      }

      return plan.total_debug_size;
    };
    auto mark_clusters_as_skip = [&](const auto& sizes) {
      // Mark methods in clusters as skip and remove them from param_to_sizes.
      for (const auto& p : sizes) {
        const auto* emitted_method = p.first.method;
        const auto* canonical =
            iodi_metadata.get_canonical_method(emitted_method);
        auto cluster_it = clustered_methods.find(canonical);
        if (cluster_it == clustered_methods.end()) {
          continue;
        }

        for (const auto* m : cluster_it->second) {
          if (m != emitted_method) {
            pso.skip(m);
            TRACE(IODI, 4, "Skipping %s for %s", SHOW(m), SHOW(emitted_method));
            auto& m_dbg = method_to_debug_meta.at(m);
            auto& param_methods = param_to_sizes.at(m_dbg.num_params);
            auto param_it = param_methods.find(MethodKey{m, m_dbg.dex_size});
            if (param_it != param_methods.end()) {
              param_methods.erase(param_it);
            }
          }
        }
      }
    };
    if (combinations == 1) {
      compute(dbg_sizes, /*dry_run=*/false);
      mark_clusters_as_skip(dbg_sizes);
    } else {
      auto sizes_wo_clusters = dbg_sizes;
      size_t max_cluster_len{0};
      uint64_t sum_cluster_sizes{0};
      for (auto& p : UnorderedIterable(clusters_in_sizes)) {
        for (const auto& k : p.second) {
          sizes_wo_clusters.erase(k);
        }
        std::sort(p.second.begin(), p.second.end(), MethodKeyCompare());
        max_cluster_len = std::max(max_cluster_len, p.second.size());
        for (const auto& k : p.second) {
          sum_cluster_sizes += dbg_sizes.at(k);
        }
      }
      TRACE(IODI, 3, "max_cluster_len=%zu sum_cluster_sizes=%" PRIu64,
            max_cluster_len, sum_cluster_sizes);

      // Very simple heuristic, "walk" in lock-step, do not try all combinations
      // (too expensive).
      size_t best_iter{0};
      uint64_t best_size{0};

      auto add_iteration = [&dbg_sizes, &clusters_in_sizes,
                            max_cluster_len](auto& cur_sizes, size_t iter) {
        uint64_t added_sizes{0};
        for (const auto& p : UnorderedIterable(clusters_in_sizes)) {
          size_t p_idx = p.second.size() -
                         std::min(p.second.size(), max_cluster_len - iter);
          const auto& k = p.second[p_idx];
          auto k_size = dbg_sizes.at(k);
          cur_sizes[k] = k_size;
          added_sizes += k_size;
        }
        return added_sizes;
      };

      for (size_t iter = 0; iter != max_cluster_len; ++iter) {
        auto cur_sizes = sizes_wo_clusters;
        auto added_sizes = add_iteration(cur_sizes, iter);

        auto out_size = compute(cur_sizes, /*dry_run=*/true) +
                        (sum_cluster_sizes - added_sizes);
        TRACE(IODI, 3,
              "Iteration %zu: added_sizes=%" PRIu64 " out_size=%" PRIu64
              " extra_size=%" PRIu64,
              iter, added_sizes, out_size, sum_cluster_sizes - added_sizes);
        if (iter == 0) {
          best_size = out_size;
        } else if (out_size < best_size) {
          best_size = out_size;
          best_iter = iter;
        }
      }

      TRACE(IODI, 3, "Best iteration %zu (%" PRIu64 ")", best_iter, best_size);
      auto cur_sizes = sizes_wo_clusters;
      add_iteration(cur_sizes, best_iter);
      compute(cur_sizes, /*dry_run=*/false);
      mark_clusters_as_skip(cur_sizes);

      // Mark other cluster methods as skips.
      for (const auto& p : UnorderedIterable(clusters_in_sizes)) {
        size_t p_idx = p.second.size() -
                       std::min(p.second.size(), max_cluster_len - best_iter);
        for (size_t i = 0; i != p.second.size(); ++i) {
          if (i == p_idx) {
            continue;
          }
          pso.skip(p.second[i].method);
        }
      }
    }
  }

  auto post_iodi_offset = offset;
  TRACE(IODI, 2, "[IODI] IODI programs took up %" PRIu64 " bytes\n",
        post_iodi_offset - initial_offset);
  // 3)
  UnorderedSet<const DexMethod*> to_remove;
  for (auto& it : code_items) {
    if (pso.skip_methods.count(it->method) != 0u) {
      continue;
    }

    DexCode* dc = it->code;
    auto* const dbg = dc->get_debug_item();
    redex_assert(dbg != nullptr);
    auto code_size = dc->size();
    redex_assert(code_size != 0);
    // If a method is too big then it's been marked as so internally, so this
    // will return false.
    DexMethod* method = it->method;
    if (!iodi_metadata.is_huge(method)) {
      iodi_metadata.set_iodi_layer(method, iodi_layer);
      TRACE(IODI, 3, "Emitting %s as IODI", SHOW(method));
      if (!requires_iodi_programs) {
        it->code_item->debug_info_off = 0;
      }
    } else {
      TRACE(IODI, 3, "Emitting %s as non-IODI", SHOW(method));
      // Recompute the debug data with no line add-in if not in a cluster.
      // TODO: If a whole cluster does not have IODI, we should emit base
      //       versions for all of them.
      DebugMetadata no_line_addin_metadata;
      const DebugMetadata* metadata = &method_to_debug_meta.at(method);
      if (!iodi_metadata.is_in_global_cluster(method) && line_addin != 0) {
        no_line_addin_metadata =
            calculate_debug_metadata(dbg, dc, it->code_item, pos_mapper,
                                     metadata->num_params, code_debug_map,
                                     /*line_addin=*/0);
        metadata = &no_line_addin_metadata;
      }
      offset +=
          emit_debug_info_for_metadata(dodx, *metadata, method, output, offset,
                                       capacity, checked_through, true);
      *dbgcount += 1;
    }
    to_remove.insert(method);
  }
  code_items.erase(std::remove_if(code_items.begin(), code_items.end(),
                                  [&to_remove](const CodeItemEmit* cie) {
                                    return to_remove.count(cie->method) > 0;
                                  }),
                   code_items.end());
  TRACE(IODI, 2, "[IODI] Non-IODI programs took up %" PRIu64 " bytes\n",
        offset - post_iodi_offset);
  // Return how much data we've encoded
  // The absolute cursor is what gets narrowed back into m_offset, so that is
  // what has to fit -- not merely this layer's length.
  always_assert_log(offset >= initial_offset,
                    "IODI debug layer wrapped the output cursor from %" PRIu64
                    " to %" PRIu64,
                    initial_offset,
                    offset);
  always_assert_log(offset <= UINT32_MAX,
                    "IODI debug layer ran the output cursor to %" PRIu64
                    ", past the 32-bit dex offset domain",
                    offset);
  return offset - initial_offset;
}

uint64_t emit_instruction_offset_debug_info(
    DexOutputIdx* dodx,
    PositionMapper* pos_mapper,
    std::vector<CodeItemEmit>& code_items,
    IODIMetadata& iodi_metadata,
    bool iodi_layers,
    size_t store_number,
    size_t dex_number,
    uint8_t* output,
    uint64_t offset,
    uint64_t capacity,
    uint64_t* checked_through,
    int* dbgcount,
    UnorderedMap<DexCode*, std::vector<DebugLineItem>>* code_debug_map) {
  // IODI only supports non-ambiguous methods, i.e., an overload cluster is
  // only a single method. Layered IODI supports as many overloads as can
  // be encoded.
  const size_t large_bound = iodi_layers ? DexOutput::kIODILayerBound : 1;

  const auto& too_large_cluster_canonical_methods =
      iodi_metadata.get_too_large_cluster_canonical_methods();
  TRACE(IODI, 1, "%zu too-large method clusters.",
        too_large_cluster_canonical_methods.size());

  std::vector<CodeItemEmit*> code_items_tmp;
  code_items_tmp.reserve(code_items.size());
  std::transform(code_items.begin(), code_items.end(),
                 std::back_inserter(code_items_tmp),
                 [](CodeItemEmit& cie) { return &cie; });
  // Remove all items without debug info or no code.
  code_items_tmp.erase(std::remove_if(code_items_tmp.begin(),
                                      code_items_tmp.end(),
                                      [](auto cie) {
                                        if (!cie->code->get_debug_item()) {
                                          return true;
                                        };
                                        if (cie->code->size() == 0) {
                                          // If there are no instructions then
                                          // we don't need any debug info!
                                          cie->code_item->debug_info_off = 0;
                                          return true;
                                        }
                                        return false;
                                      }),
                       code_items_tmp.end());
  TRACE(IODI, 1, "Removed %zu CIEs w/o debug data.",
        code_items.size() - code_items_tmp.size());
  // Remove all unsupported items.
  std::vector<CodeItemEmit*> unsupported_code_items;
  if (!too_large_cluster_canonical_methods.empty()) {
    code_items_tmp.erase(
        std::remove_if(
            code_items_tmp.begin(), code_items_tmp.end(),
            [&](CodeItemEmit* cie) {
              bool supported =
                  too_large_cluster_canonical_methods.count(
                      iodi_metadata.get_canonical_method(cie->method)) == 0;
              if (!supported) {
                iodi_metadata.mark_method_huge(cie->method);
                unsupported_code_items.push_back(cie);
              }
              return !supported;
            }),
        code_items_tmp.end());
  }

  const uint64_t initial_offset = offset;
  if (!code_items_tmp.empty()) {
    for (size_t i = 0; i < large_bound; ++i) {
      if (code_items_tmp.empty()) {
        break;
      }
      TRACE(IODI, 1, "IODI iteration %zu", i);
      const size_t before_size = code_items_tmp.size();
      offset += emit_instruction_offset_debug_info_helper(
          dodx, pos_mapper, code_items_tmp, iodi_metadata, i,
          i << DexOutput::kIODILayerShift, store_number, dex_number, output,
          offset, capacity, checked_through, dbgcount, code_debug_map);
      const size_t after_size = code_items_tmp.size();
      redex_assert(after_size < before_size);
    }
  }
  const bool code_items_tmp_is_empty = code_items_tmp.empty();
  redex_assert(code_items_tmp_is_empty);

  // Emit the methods we could not handle.
  for (auto* cie : unsupported_code_items) {
    DexCode* dc = cie->code;
    redex_assert(dc->size() != 0);
    auto* const dbg_item = dc->get_debug_item();
    redex_assert(dbg_item);
    DexMethod* method = cie->method;
    uint32_t param_size = method->get_proto()->get_args()->size();
    DebugMetadata metadata =
        calculate_debug_metadata(dbg_item, dc, cie->code_item, pos_mapper,
                                 param_size, code_debug_map, /*line_addin=*/0);
    offset +=
        emit_debug_info_for_metadata(dodx, metadata, method, output, offset,
                                     capacity, checked_through, true);
    *dbgcount += 1;
    iodi_metadata.mark_method_huge(method);
  }

  // The configured buffer cap keeps this cursor in the 32-bit DEX domain
  // today. Keep the representation check local because debug_info_off fields
  // and DexOutput's cursor are 32-bit.
  always_assert_log(offset >= initial_offset,
                    "IODI debug section wrapped the output cursor from %" PRIu64
                    " to %" PRIu64,
                    initial_offset,
                    offset);
  always_assert_log(offset <= UINT32_MAX,
                    "IODI debug section ran the output cursor to %" PRIu64
                    ", past the 32-bit dex offset domain",
                    offset);
  return offset - initial_offset;
}

} // namespace

void DexOutput::generate_debug_items() {
  uint32_t dbg_start = m_offset;
  int dbgcount = 0;
  bool emit_positions = m_debug_info_kind != DebugInfoKind::NoPositions;
  bool use_iodi = is_iodi(m_debug_info_kind);
  if (use_iodi && (m_iodi_metadata != nullptr)) {
    inc_offset(emit_instruction_offset_debug_info(
        &m_dodx,
        m_pos_mapper,
        m_code_item_emits,
        *m_iodi_metadata,
        m_debug_info_kind == DebugInfoKind::InstructionOffsetsLayered,
        m_store_number,
        m_dex_number,
        m_output.get(),
        m_offset,
        m_output_size,
        &m_checked_through,
        &dbgcount,
        m_code_debug_lines));
  } else {
    if (use_iodi) {
      fprintf(stderr,
              "[IODI] WARNING: Not using IODI because no iodi metadata file was"
              " specified.\n");
    }
    for (auto& it : m_code_item_emits) {
      DexCode* dc = it.code;
      dex_code_item* dci = it.code_item;
      auto* dbg = dc->get_debug_item();
      if (dbg == nullptr) {
        continue;
      }
      dbgcount++;
      uint32_t num_params =
          static_cast<uint32_t>(it.method->get_proto()->get_args()->size());
      uint64_t dbg_size =
          emit_debug_info(&m_dodx, emit_positions, dbg, it.method, dc, dci,
                          m_pos_mapper, m_output.get(), m_offset, m_output_size,
                          &m_checked_through, num_params, m_code_debug_lines);
      inc_offset(dbg_size);
    }
  }
  if (emit_positions) {
    insert_map_item(TYPE_DEBUG_INFO_ITEM, dbgcount, dbg_start,
                    m_offset - dbg_start);
  }
  m_stats.num_dbg_items += dbgcount;
  m_stats.dbg_total_size += m_offset - dbg_start;
}

void DexOutput::generate_map() {
  align_output();
  uint32_t* mapout = (uint32_t*)(m_output.get() + m_offset);
  hdr.map_off = m_offset;
  insert_map_item(TYPE_MAP_LIST, 1, m_offset,
                  sizeof(uint32_t) + m_map_items.size() * sizeof(dex_map_item));
  // The map list is itself a map item, so the insert above grew the vector the
  // loop below writes. Bound the write against that final vector, not the one
  // we arrived with. Nothing has reached the buffer yet, so the guard still
  // precedes every write.
  ensure_fits(sizeof(uint32_t) + m_map_items.size() * sizeof(dex_map_item),
              "map list", "map list");
  *mapout = (uint32_t)m_map_items.size();
  dex_map_item* map = (dex_map_item*)(mapout + 1);
  for (auto const& mit : m_map_items) {
    *map++ = mit;
  }
  inc_offset(static_cast<uint64_t>(reinterpret_cast<uint8_t*>(map) -
                                   reinterpret_cast<uint8_t*>(mapout)));
}

/**
 * When things move around in redex, we might find ourselves in a situation
 * where a regular OPCODE_CONST_STRING is now referring to a jumbo string,
 * or vice versa. This fixup ensures that all const string opcodes agree
 * with the jumbo-ness of their stridx.
 */
static void fix_method_jumbos(DexMethod* method, const DexOutputIdx* dodx) {
  auto* code = method->get_code();
  if (code == nullptr) {
    return; // nothing to do for native methods
  }

  for (auto& mie : *code) {
    if (mie.type != MFLOW_DEX_OPCODE) {
      continue;
    }
    auto* insn = mie.dex_insn;
    auto op = insn->opcode();
    if (op != DOPCODE_CONST_STRING && op != DOPCODE_CONST_STRING_JUMBO) {
      continue;
    }

    const auto* str = dynamic_cast<DexOpcodeString*>(insn)->get_string();
    uint32_t stridx = dodx->stringidx(str);
    bool jumbo = ((stridx >> 16) != 0);

    if (jumbo) {
      insn->set_opcode(DOPCODE_CONST_STRING_JUMBO);
    } else if (!jumbo) {
      insn->set_opcode(DOPCODE_CONST_STRING);
    }
  }
}

static void fix_jumbos(DexClasses* classes, DexOutputIdx* dodx) {
  walk::methods(*classes, [&](DexMethod* m) { fix_method_jumbos(m, dodx); });
}

void DexOutput::init_header_offsets(const std::string& dex_magic) {
  always_assert_log(!dex_magic.empty(), "Invalid dex magic from input APK\n");
  memcpy(hdr.magic, dex_magic.c_str(), sizeof(hdr.magic));
  uint32_t total_hdr_size = sizeof(dex_header);
  insert_map_item(TYPE_HEADER_ITEM, 1, 0, total_hdr_size);

  m_offset = hdr.header_size = total_hdr_size;
  hdr.endian_tag = ENDIAN_CONSTANT;
  /* Link section was never used */
  hdr.link_size = hdr.link_off = 0;
  hdr.string_ids_size = (uint32_t)m_dodx.stringsize();
  hdr.string_ids_off = hdr.string_ids_size != 0u ? m_offset : 0;
  uint64_t total_string_size =
      (uint64_t)m_dodx.stringsize() * sizeof(dex_string_id);
  insert_map_item(TYPE_STRING_ID_ITEM, (uint32_t)m_dodx.stringsize(), m_offset,
                  (uint32_t)total_string_size);

  ensure_fits(total_string_size, "string ids table", "header");
  inc_offset(total_string_size);
  hdr.type_ids_size = (uint32_t)m_dodx.typesize();
  hdr.type_ids_off = hdr.type_ids_size != 0u ? m_offset : 0;
  uint64_t total_type_size = (uint64_t)m_dodx.typesize() * sizeof(dex_type_id);
  insert_map_item(TYPE_TYPE_ID_ITEM, (uint32_t)m_dodx.typesize(), m_offset,
                  (uint32_t)total_type_size);

  ensure_fits(total_type_size, "type ids table", "header");
  inc_offset(total_type_size);
  hdr.proto_ids_size = (uint32_t)m_dodx.protosize();
  hdr.proto_ids_off = hdr.proto_ids_size != 0u ? m_offset : 0;
  uint64_t total_proto_size =
      (uint64_t)m_dodx.protosize() * sizeof(dex_proto_id);
  insert_map_item(TYPE_PROTO_ID_ITEM, (uint32_t)m_dodx.protosize(), m_offset,
                  (uint32_t)total_proto_size);

  ensure_fits(total_proto_size, "proto ids table", "header");
  inc_offset(total_proto_size);
  hdr.field_ids_size = (uint32_t)m_dodx.fieldsize();
  hdr.field_ids_off = hdr.field_ids_size != 0u ? m_offset : 0;
  uint64_t total_field_size =
      (uint64_t)m_dodx.fieldsize() * sizeof(dex_field_id);
  insert_map_item(TYPE_FIELD_ID_ITEM, (uint32_t)m_dodx.fieldsize(), m_offset,
                  (uint32_t)total_field_size);

  ensure_fits(total_field_size, "field ids table", "header");
  inc_offset(total_field_size);
  hdr.method_ids_size = (uint32_t)m_dodx.methodsize();
  hdr.method_ids_off = hdr.method_ids_size != 0u ? m_offset : 0;
  uint64_t total_method_size =
      (uint64_t)m_dodx.methodsize() * sizeof(dex_method_id);
  insert_map_item(TYPE_METHOD_ID_ITEM, (uint32_t)m_dodx.methodsize(), m_offset,
                  (uint32_t)total_method_size);

  ensure_fits(total_method_size, "method ids table", "header");
  inc_offset(total_method_size);
  hdr.class_defs_size = (uint32_t)m_classes->size();
  hdr.class_defs_off = hdr.class_defs_size != 0u ? m_offset : 0;
  uint64_t total_class_size =
      (uint64_t)m_classes->size() * sizeof(dex_class_def);
  insert_map_item(TYPE_CLASS_DEF_ITEM, (uint32_t)m_classes->size(), m_offset,
                  (uint32_t)total_class_size);

  ensure_fits(total_class_size, "class defs table", "header");
  inc_offset(total_class_size);

  uint64_t total_callsite_size =
      (uint64_t)m_dodx.callsitesize() * sizeof(dex_callsite_id);
  m_callsite_start = m_offset;
  insert_map_item(TYPE_CALL_SITE_ID_ITEM, (uint32_t)m_dodx.callsitesize(),
                  m_offset, (uint32_t)total_callsite_size);
  ensure_fits(total_callsite_size, "call site ids table", "header");
  inc_offset(total_callsite_size);

  uint64_t total_methodhandle_size =
      (uint64_t)m_dodx.methodhandlesize() * sizeof(dex_methodhandle_id);
  m_methodhandle_start = m_offset;
  insert_map_item(TYPE_METHOD_HANDLE_ITEM, (uint32_t)m_dodx.methodhandlesize(),
                  m_offset, (uint32_t)total_methodhandle_size);
  ensure_fits(total_methodhandle_size, "method handles table", "header");
  inc_offset(total_methodhandle_size);

  hdr.data_off = m_offset;
  /* Todo... */
  hdr.map_off = 0;
  hdr.data_size = 0;
  hdr.file_size = 0;
}

void DexOutput::finalize_header() {
  hdr.data_size = m_offset - hdr.data_off;
  hdr.file_size = m_offset;
  int skip;
  skip = sizeof(hdr.magic) + sizeof(hdr.checksum) + sizeof(hdr.signature);
  memcpy(m_output.get(), &hdr, sizeof(hdr));
  Sha1Context context;
  sha1_init(&context);
  sha1_update(&context, m_output.get() + skip, hdr.file_size - skip);
  sha1_final(hdr.signature, &context);
  memcpy(m_output.get(), &hdr, sizeof(hdr));
  uint32_t adler = (uint32_t)adler32(0L, Z_NULL, 0);
  skip = sizeof(hdr.magic) + sizeof(hdr.checksum);
  adler = (uint32_t)adler32(adler, (const Bytef*)(m_output.get() + skip),
                            hdr.file_size - skip);
  hdr.checksum = adler;
  memcpy(m_output.get(), &hdr, sizeof(hdr));
}

namespace {

void compute_method_to_id_map(
    DexOutputIdx* dodx,
    const DexClasses* classes,
    uint8_t* dex_signature,
    UnorderedMap<DexMethod*, uint64_t>* method_to_id) {
  if (method_to_id == nullptr) {
    return;
  }

  UnorderedSet<DexClass*> dex_classes(classes->begin(), classes->end());
  for (const auto& it : UnorderedIterable(dodx->method_to_idx())) {
    auto* method = it.first;
    auto idx = it.second;

    auto const& typecls = method->get_class();
    auto const& cls = type_class(typecls);
    if (dex_classes.count(cls) == 0) {
      continue;
    }

    auto* resolved_method = [&]() -> DexMethodRef* {
      if (cls != nullptr) {
        auto* resm = resolve_method_deprecated(
            method,
            is_interface(cls) ? MethodSearch::Interface : MethodSearch::Any);
        if (resm != nullptr) {
          return resm;
        }
      }
      return method;
    }();

    // Turns out, the checksum can change on-device. (damn you dexopt)
    // The signature, however, is never recomputed. Let's log the top 4 bytes,
    // in little-endian (since that's faster to compute on-device).
    uint32_t signature = *reinterpret_cast<uint32_t*>(dex_signature);

    if (resolved_method == method) {
      // Not recording it if method reference is not referring to
      // concrete method, otherwise will have key overlapped.
      auto* dexmethod = dynamic_cast<DexMethod*>(resolved_method);
      (*method_to_id)[dexmethod] = ((uint64_t)idx << 32) | (uint64_t)signature;
    }
  }
}

void write_method_mapping(const std::string& filename,
                          const DexOutputIdx* dodx,
                          const DexClasses* classes,
                          uint8_t* dex_signature) {
  always_assert(!filename.empty());
  FILE* fd = fopen(filename.c_str(), "a");
  assert_log(fd, "Can't open method mapping file %s: %s\n", filename.c_str(),
             strerror(errno));
  UnorderedSet<DexClass*> classes_in_dex(classes->begin(), classes->end());
  for (const auto& it : UnorderedIterable(dodx->method_to_idx())) {
    auto* method = it.first;
    auto idx = it.second;

    // Types (and methods) internal to our app have a cached deobfuscated name
    // that comes from the proguard map.  If we don't have one, it's a
    // system/framework class, so we can just return the name.
    auto const& typecls = method->get_class();
    auto const& cls = type_class(typecls);
    if (classes_in_dex.count(cls) == 0) {
      // We only want to emit IDs for the methods that are defined in this dex,
      // and not for references to methods in other dexes.
      continue;
    }
    auto deobf_class = [&] {
      if (cls != nullptr) {
        auto deobname = cls->get_deobfuscated_name_or_empty();
        if (!deobname.empty()) {
          return str_copy(deobname);
        }
      }
      return show(typecls);
    }();

    // Some method refs aren't "concrete" (e.g., referring to a method defined
    // by a superclass via a subclass).  We only know how to deobfuscate
    // concrete names, so resolve this ref to an actual definition.
    auto* resolved_method = [&]() -> DexMethodRef* {
      if (cls != nullptr) {
        auto* resm = resolve_method_deprecated(
            method,
            is_interface(cls) ? MethodSearch::Interface : MethodSearch::Any);
        if (resm != nullptr) {
          return resm;
        }
      }
      return method;
    }();

    // Consult the cached method names, or just give it back verbatim.
    auto deobf_method = [&] {
      if (resolved_method->is_def()) {
        const auto& deobfname =
            resolved_method->as_def()->get_deobfuscated_name_or_empty();
        if (!deobfname.empty()) {
          return str_copy(deobfname);
        }
      }
      return show(resolved_method);
    }();

    // Format is <cls>.<name>:(<args>)<ret>
    // We only want the name here.
    auto begin = deobf_method.find('.') + 1;
    auto end = deobf_method.rfind(':');
    auto deobf_method_name = deobf_method.substr(begin, end - begin);

    // Turns out, the checksum can change on-device. (damn you dexopt)
    // The signature, however, is never recomputed. Let's log the top 4 bytes,
    // in little-endian (since that's faster to compute on-device).
    uint32_t signature = *reinterpret_cast<uint32_t*>(dex_signature);

    fprintf(fd, "%u %u %s %s\n", idx, signature, deobf_method_name.c_str(),
            deobf_class.c_str());
  }
  fclose(fd);
}

void write_class_mapping(const std::string& filename,
                         DexClasses* classes,
                         const size_t class_defs_size,
                         uint8_t* dex_signature) {
  always_assert(!filename.empty());
  FILE* fd = fopen(filename.c_str(), "a");

  for (uint32_t idx = 0; idx < class_defs_size; idx++) {

    DexClass* cls = classes->at(idx);
    auto deobf_class = [&] {
      if (cls != nullptr) {
        auto deobname = cls->get_deobfuscated_name_or_empty();
        if (!deobname.empty()) {
          return str_copy(deobname);
        }
      }
      return show(cls);
    }();

    //
    // See write_method_mapping above for why checksum is insufficient.
    //
    uint32_t signature = *reinterpret_cast<uint32_t*>(dex_signature);
    fprintf(fd, "%u %u %s\n", idx, signature, deobf_class.c_str());
  }

  fclose(fd);
}

const char* deobf_primitive(char type) {
  switch (type) {
  case 'B':
    return "byte";
  case 'C':
    return "char";
  case 'D':
    return "double";
  case 'F':
    return "float";
  case 'I':
    return "int";
  case 'J':
    return "long";
  case 'S':
    return "short";
  case 'Z':
    return "boolean";
  case 'V':
    return "void";
  default:
    not_reached_log("Illegal type: %c", type);
  }
}

void write_invoke_mapping(const std::string& filename, DexClasses* classes) {
  if (filename.empty()) {
    return;
  }

  std::ofstream ofs(filename.c_str(), std::ofstream::out | std::ofstream::app);
  Json::FastWriter writer; // minimal formatting and no intermittent new-lines

  auto* position_manager = g_redex->get_position_pattern_switch_manager();
  auto is_outlined_position = [&](DexPosition* pos) {
    return position_manager->is_pattern_position(pos) ||
           position_manager->is_switch_position(pos);
  };
  auto position_to_json = [&](DexPosition* pos) {
    Json::Value position_entry;
    if (pos->file != nullptr) {
      position_entry["file"] = show(pos->file);
    }
    if (pos->method != nullptr) {
      position_entry["method"] = show(pos->method);
    }
    position_entry["line"] = show(pos->line);
    return position_entry;
  };
  auto src_block_to_json = [&](const SourceBlock* src_block) {
    Json::Value src_block_entry;
    src_block_entry["src"] = show(src_block->src);
    src_block_entry["id"] = show(src_block->id);
    return src_block_entry;
  };

  walk::methods(*classes, [&](DexMethod* m) {
    auto* dex_code = m->get_dex_code();
    if (dex_code == nullptr) {
      return;
    }
    auto& invoke_ids = dex_code->get_invoke_ids();
    if (invoke_ids.empty()) {
      return;
    }
    Json::Value method_entry;
    method_entry["caller"] = show(m);
    Json::Value invoke_array{Json::ValueType::arrayValue};
    for (auto&& [addr, id] : invoke_ids) {
      Json::Value invoke_entry;
      invoke_entry["offset"] = addr;
      invoke_entry["kind"] = id.invoke_interface ? "interface" : "virtual";
      invoke_entry["callee"] = show(id.method);
      if (id.position && !is_outlined_position(id.position.get())) {
        invoke_entry["position"] = position_to_json(id.position.get());
      }
      if (id.src_block) {
        if (id.src_block->next == nullptr) {
          invoke_entry["src_block"] = src_block_to_json(id.src_block.get());
        } else {
          Json::Value src_block_array{Json::ValueType::arrayValue};
          for (const auto* cur = id.src_block.get(); cur != nullptr;
               cur = cur->next.get()) {
            src_block_array.append(src_block_to_json(cur));
          }
          invoke_entry["src_block"] = std::move(src_block_array);
        }
      }
      invoke_array.append(std::move(invoke_entry));
    }
    method_entry["invokes"] = std::move(invoke_array);
    ofs << writer.write(method_entry); // the writer ends with a new-line
  });
}

void write_pg_mapping(const std::string& filename, DexClasses* classes) {
  if (filename.empty()) {
    return;
  }

  auto deobf_class = [&](DexClass* cls) {
    if (cls != nullptr) {
      auto deobname = cls->get_deobfuscated_name_or_empty();
      if (!deobname.empty()) {
        return str_copy(deobname);
      }
    }
    return show(cls);
  };

  auto deobf_type = [&](const DexType* type) {
    if (type != nullptr) {
      if (type::is_array(type)) {
        const auto* type_str = type->c_str();
        uint32_t dim = type::get_array_level(type);
        const DexType* inner_type = type::get_array_element_type(type);
        DexClass* inner_cls =
            inner_type != nullptr ? type_class(inner_type) : nullptr;
        std::string result;
        if (inner_cls != nullptr) {
          result = java_names::internal_to_external(deobf_class(inner_cls));
        } else if ((inner_type != nullptr) && type::is_primitive(inner_type)) {
          result = deobf_primitive(type_str[dim]);
        } else {
          result = java_names::internal_to_external(&type_str[dim]);
        }
        result.reserve(result.size() + static_cast<size_t>(2 * dim));
        for (uint32_t i = 0; i < dim; ++i) {
          result += "[]";
        }
        return result;
      } else {
        DexClass* cls = type_class(type);
        if (cls != nullptr) {
          return java_names::internal_to_external(deobf_class(cls));
        } else if (type::is_primitive(type)) {
          return std::string(deobf_primitive(type->c_str()[0]));
        }
        return java_names::internal_to_external(type->str());
      }
    }
    return show(type);
  };

  auto deobf_meth = [&](DexMethod* method) {
    if (method != nullptr) {
      /* clang-format off */
      // Example: 672:672:boolean customShouldDelayInitMessage(android.os.Handler,android.os.Message)
      /* clang-format on */
      auto* proto = method->get_proto();
      std::ostringstream ss;
      auto* code = method->get_dex_code();
      auto* dbg = code != nullptr ? code->get_debug_item() : nullptr;
      if (dbg != nullptr) {
        uint32_t line_start = code->get_debug_item()->get_line_start();
        uint32_t line_end = line_start;
        for (auto& entry : dbg->get_entries()) {
          if (entry.type == DexDebugEntryType::Position) {
            if (entry.pos->line > line_end) {
              line_end = entry.pos->line;
            }
          }
        }
        // Treat anything bigger than 2^31 as 0
        if (line_start >
            static_cast<uint32_t>(std::numeric_limits<int32_t>::max())) {
          line_start = 0;
        }
        if (line_end >
            static_cast<uint32_t>(std::numeric_limits<int32_t>::max())) {
          line_end = 0;
        }
        ss << line_start << ":" << line_end << ":";
      }
      auto* rtype = proto->get_rtype();
      auto rtype_str = deobf_type(rtype);
      ss << rtype_str;
      ss << " " << method->get_simple_deobfuscated_name() << "(";
      auto* args = proto->get_args();
      for (auto iter = args->begin(); iter != args->end(); ++iter) {
        const auto* atype = *iter;
        auto atype_str = deobf_type(atype);
        ss << atype_str;
        if (iter + 1 != args->end()) {
          ss << ",";
        }
      }
      ss << ")";
      return ss.str();
    }
    return show(method);
  };

  auto deobf_field = [&](DexField* field) {
    if (field != nullptr) {
      std::ostringstream ss;
      ss << deobf_type(field->get_type()) << " "
         << field->get_simple_deobfuscated_name();
      return ss.str();
    }
    return show(field);
  };

  std::ofstream ofs(filename.c_str(), std::ofstream::out | std::ofstream::app);

  for (auto* cls : *classes) {
    auto deobf_cls = deobf_class(cls);
    ofs << java_names::internal_to_external(deobf_cls) << " -> "
        << java_names::internal_to_external(cls->get_type()->str()) << ":"
        << "\n";
    for (auto* field : cls->get_ifields()) {
      auto deobf = deobf_field(field);
      ofs << "    " << deobf << " -> " << field->c_str() << "\n";
    }
    for (auto* field : cls->get_sfields()) {
      auto deobf = deobf_field(field);
      ofs << "    " << deobf << " -> " << field->c_str() << "\n";
    }
    for (auto* meth : cls->get_dmethods()) {
      auto deobf = deobf_meth(meth);
      ofs << "    " << deobf << " -> " << meth->c_str() << "\n";
    }
    for (auto* meth : cls->get_vmethods()) {
      auto deobf = deobf_meth(meth);
      ofs << "    " << deobf << " -> " << meth->c_str() << "\n";
    }
  }
}

void write_full_mapping(const std::string& filename,
                        DexClasses* classes,
                        const std::string* store_name) {
  if (filename.empty()) {
    return;
  }

  std::ofstream ofs(filename.c_str(), std::ofstream::out | std::ofstream::app);
  for (auto* cls : *classes) {
    ofs << "type " << cls->get_deobfuscated_name_or_empty() << " -> "
        << show(cls) << "\n";
    if (store_name != nullptr) {
      const auto& original_store_name = cls->get_location()->get_store_name();
      ofs << "store " << std::quoted(original_store_name) << " -> "
          << std::quoted(*store_name) << "\n";
    }
    for (auto* field : cls->get_ifields()) {
      ofs << "ifield " << field->get_deobfuscated_name_or_empty() << " -> "
          << show(field) << "\n";
    }
    for (auto* field : cls->get_sfields()) {
      ofs << "sfield " << field->get_deobfuscated_name_or_empty() << " -> "
          << show(field) << "\n";
    }
    for (auto* method : cls->get_dmethods()) {
      ofs << "dmethod " << method->get_deobfuscated_name_or_empty() << " -> "
          << show(method) << "\n";
    }
    for (auto* method : cls->get_vmethods()) {
      ofs << "vmethod " << method->get_deobfuscated_name_or_empty() << " -> "
          << show(method) << "\n";
    }
  }
}

void write_bytecode_offset_mapping(
    const std::string& filename,
    const std::vector<std::pair<std::string, uint32_t>>& method_offsets) {
  if (filename.empty()) {
    return;
  }

  auto* fd = fopen(filename.c_str(), "a");
  assert_log(fd, "Can't open bytecode offset file %s: %s\n", filename.c_str(),
             strerror(errno));

  for (const auto& item : method_offsets) {
    fprintf(fd, "%u %s\n", item.second, item.first.c_str());
  }

  fclose(fd);
}

int check_class_order(DexClasses* dex) {
  auto valid_ordering =
      [](const UnorderedMap<const DexType*, uint32_t>& dexes_class_order,
         const DexType* cls_to_check,
         uint32_t cur_index) -> bool {
    auto find = dexes_class_order.find(cls_to_check);
    if (find == dexes_class_order.end()) {
      // Not defined in same dex, valid
      return true;
    }
    // If cls_to_check was defined before cur_index, valid
    // otherwise, invalid.
    return find->second < cur_index;
  };
  UnorderedMap<const DexType*, uint32_t> dexes_class_order;
  int violation_count = 0;
  for (uint32_t index = 0; index < dex->size(); ++index) {
    dexes_class_order[dex->at(index)->get_type()] = index;
  }
  for (uint32_t index = 0; index < dex->size(); ++index) {
    auto* cur_cls = dex->at(index);
    if (!valid_ordering(dexes_class_order, cur_cls->get_super_class(), index)) {
      violation_count++;
    }
    for (const auto* intf : *cur_cls->get_interfaces()) {
      if (!valid_ordering(dexes_class_order, intf, index)) {
        violation_count++;
      }
    }
  }
  return violation_count;
}

} // namespace

void DexOutput::write_symbol_files() {
  if (m_debug_info_kind != DebugInfoKind::NoCustomSymbolication) {
    write_method_mapping(m_method_mapping_filename, &m_dodx, m_classes,
                         hdr.signature);
    write_class_mapping(m_class_mapping_filename, m_classes,
                        hdr.class_defs_size, hdr.signature);
    // XXX: should write_bytecode_offset_mapping be included here too?
  }
  write_pg_mapping(m_pg_mapping_filename, m_classes);
  write_invoke_mapping(m_invoke_mapping_filename, m_classes);
  write_full_mapping(m_full_mapping_filename, m_classes, m_store_name);
  write_bytecode_offset_mapping(m_bytecode_offset_filename,
                                m_method_bytecode_offsets);
}

void GatheredTypes::set_config(ConfigFiles* config) { m_config = config; }

void DexOutput::prepare(SortMode string_mode,
                        const std::vector<SortMode>& code_mode,
                        ConfigFiles& conf,
                        const std::string& dex_magic) {
  m_gtypes->set_config(&conf);

  fix_jumbos(m_classes, &m_dodx);
  init_header_offsets(dex_magic);
  generate_static_values();
  generate_typelist_data();
  generate_string_data(string_mode);
  generate_code_items(code_mode);
  generate_class_data_items();
  generate_type_data();
  generate_proto_data();
  generate_field_data();
  generate_method_data();
  generate_class_data();
  generate_callsite_data();
  generate_methodhandle_data();
  generate_annotations();
  generate_debug_items();
  generate_map();
  finalize_header();
  compute_method_to_id_map(&m_dodx, m_classes, hdr.signature, m_method_to_id);
}

void DexOutput::write() {
  struct stat st;
  int fd = open(m_filename, O_CREAT | O_TRUNC | O_WRONLY | O_BINARY, 0660);
  if (fd == -1) {
    perror("Error writing dex");
    return;
  }
  ::write(fd, m_output.get(), m_offset);
  if (0 == fstat(fd, &st)) {
    m_stats.num_bytes = st.st_size;
  }
  close(fd);

  write_symbol_files();
}

namespace {

class UniqueReferences {
 public:
  UnorderedSet<const DexString*> strings;
  UnorderedSet<const DexType*> types;
  UnorderedSet<const DexProto*> protos;
  UnorderedSet<const DexFieldRef*> fields;
  UnorderedSet<const DexMethodRef*> methods;
  int64_t total_strings_size{0};
  int64_t total_types_size{0};
  int64_t total_protos_size{0};
  int64_t total_fields_size{0};
  int64_t total_methods_size{0};
  int dexes{0};
};
UniqueReferences s_unique_references;

} // namespace

void DexOutput::metrics() {
  if (s_unique_references.dexes++ == 1 && !m_normal_primary_dex) {
    // clear out info from first (primary) dex
    s_unique_references.strings.clear();
    s_unique_references.types.clear();
    s_unique_references.protos.clear();
    s_unique_references.fields.clear();
    s_unique_references.methods.clear();
    s_unique_references.total_strings_size = 0;
    s_unique_references.total_types_size = 0;
    s_unique_references.total_protos_size = 0;
    s_unique_references.total_fields_size = 0;
    s_unique_references.total_methods_size = 0;
  }
  memcpy(m_stats.signature, hdr.signature, 20);

  for (const auto& p : UnorderedIterable(m_dodx.string_to_idx())) {
    s_unique_references.strings.insert(p.first);
  }
  m_stats.num_unique_strings =
      static_cast<int64_t>(s_unique_references.strings.size());
  s_unique_references.total_strings_size +=
      static_cast<int64_t>(m_dodx.string_to_idx().size());
  m_stats.strings_total_size = s_unique_references.total_strings_size;

  for (const auto& p : UnorderedIterable(m_dodx.type_to_idx())) {
    s_unique_references.types.insert(p.first);
  }
  m_stats.num_unique_types =
      static_cast<int64_t>(s_unique_references.types.size());
  s_unique_references.total_types_size +=
      static_cast<int64_t>(m_dodx.type_to_idx().size());
  m_stats.types_total_size = s_unique_references.total_types_size;

  for (const auto& p : UnorderedIterable(m_dodx.proto_to_idx())) {
    s_unique_references.protos.insert(p.first);
  }
  m_stats.num_unique_protos =
      static_cast<int64_t>(s_unique_references.protos.size());
  s_unique_references.total_protos_size +=
      static_cast<int64_t>(m_dodx.proto_to_idx().size());
  m_stats.protos_total_size = s_unique_references.total_protos_size;

  for (const auto& p : UnorderedIterable(m_dodx.field_to_idx())) {
    s_unique_references.fields.insert(p.first);
  }
  m_stats.num_unique_field_refs =
      static_cast<int64_t>(s_unique_references.fields.size());
  s_unique_references.total_fields_size +=
      static_cast<int64_t>(m_dodx.field_to_idx().size());
  m_stats.field_refs_total_size = s_unique_references.total_fields_size;

  for (const auto& p : UnorderedIterable(m_dodx.method_to_idx())) {
    s_unique_references.methods.insert(p.first);
  }
  m_stats.num_unique_method_refs =
      static_cast<int64_t>(s_unique_references.methods.size());
  s_unique_references.total_methods_size +=
      static_cast<int64_t>(m_dodx.method_to_idx().size());
  m_stats.method_refs_total_size = s_unique_references.total_methods_size;
}

static SortMode make_sort_bytecode(const std::string& sort_bytecode) {
  if (sort_bytecode == "class_order") {
    return SortMode::CLASS_ORDER;
  } else if (sort_bytecode == "clinit_order") {
    return SortMode::CLINIT_FIRST;
  } else if (sort_bytecode == "method_profiled_order") {
    return SortMode::METHOD_PROFILED_ORDER;
  } else if (sort_bytecode == "method_similarity_order") {
    return SortMode::METHOD_SIMILARITY;
  } else if (sort_bytecode == "method_coldstart_order") {
    return SortMode::METHOD_COLDSTART_ORDER;
  } else {
    return SortMode::DEFAULT;
  }
}

std::vector<SortMode> get_code_sort_mode(ConfigFiles& conf,
                                         const std::string& store_name) {
  const JsonWrapper& json_cfg = conf.get_json_config();
  auto sort_bytecode_cfg = json_cfg.get("bytecode_sort_mode", Json::Value());
  std::vector<SortMode> code_sort_mode;

  if (sort_bytecode_cfg.isString()) {
    code_sort_mode.push_back(make_sort_bytecode(sort_bytecode_cfg.asString()));
  } else if (sort_bytecode_cfg.isArray()) {
    for (const auto& val : sort_bytecode_cfg) {
      code_sort_mode.push_back(make_sort_bytecode(val.asString()));
    }
  }

  MethodSimilarityOrderingConfig* similarity_config{nullptr};
  const auto& global_config = conf.get_global_config();
  if (global_config.has_config_by_name("method_similarity_order")) {
    similarity_config =
        global_config.get_config_by_name<MethodSimilarityOrderingConfig>(
            "method_similarity_order");
  }
  if (similarity_config == nullptr || similarity_config->disable ||
      similarity_config->store_name_to_disable == store_name) {
    TRACE(OPUT, 3, "[write_classes_to_dex] disable_method_similarity_order");
    code_sort_mode.erase(
        std::remove_if(
            code_sort_mode.begin(), code_sort_mode.end(),
            [&](SortMode sm) { return sm == SortMode::METHOD_SIMILARITY; }),
        code_sort_mode.end());
  }
  if (code_sort_mode.empty()) {
    code_sort_mode.push_back(SortMode::DEFAULT);
  }

  return code_sort_mode;
}

SortMode get_string_sort_mode(ConfigFiles& conf) {
  const JsonWrapper& json_cfg = conf.get_json_config();
  auto sort_strings = json_cfg.get("string_sort_mode", std::string());
  SortMode string_sort_mode = SortMode::DEFAULT;
  if (sort_strings == "class_strings") {
    string_sort_mode = SortMode::CLASS_STRINGS;
  } else if (sort_strings == "class_order") {
    string_sort_mode = SortMode::CLASS_ORDER;
  }
  return string_sort_mode;
}

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
    const DexOutputConfig& dex_output_config,
    int min_sdk,
    const std::vector<SortMode>& code_sort_mode,
    SortMode string_sort_mode) {
  const JsonWrapper& json_cfg = conf.get_json_config();
  bool force_single_dex = json_cfg.get("force_single_dex", false);
  if (force_single_dex) {
    always_assert_log(dex_number == 0, "force_single_dex requires one dex");
  }

  TRACE(OPUT, 2, "[write_classes_to_dex][filename] %s", filename.c_str());
  auto this_class_order_violations = check_class_order(classes);
  if (this_class_order_violations > 0) {
    // If enforce_class_order was enabled we fail the program if there exist any
    // violations, otherwise we just record the number of violation.
    always_assert_log(!conf.enforce_class_order(),
                      "Dex %s - %zu has %d class order violations",
                      store_name->c_str(), dex_number,
                      this_class_order_violations);
  }

  DexOutput dout(filename.c_str(), classes, std::move(gtypes),
                 conf.normal_primary_dex(), store_number, store_name,
                 dex_number, debug_info_kind, iodi_metadata, conf, pos_mapper,
                 method_to_id, code_debug_lines, dex_output_config, min_sdk);

  dout.prepare(string_sort_mode, code_sort_mode, conf, dex_magic);
  dout.write();
  dout.metrics();

  dout.m_stats.class_order_violations = this_class_order_violations;
  return dout.m_stats;
}

uint64_t DexOutput::policy_cap() const {
  return m_output_size - k_output_margin;
}

void DexOutput::align_output() {
  uint64_t aligned = (m_offset + uint64_t{3}) & ~uint64_t{3};
  always_assert_log(aligned < policy_cap(),
                    "Running into output safety margin while aligning the dex "
                    "output cursor from %u to %" PRIu64 " of %" PRIu64
                    " (%zu). Increase the buffer size with "
                    "`-J dex_output_buffer_size=`.",
                    m_offset, aligned, policy_cap(), m_output_size);
  m_offset = static_cast<uint32_t>(aligned);
  // Alignment moves the cursor without writing, so consume any prior check.
  m_checked_through = m_offset;
}

void DexOutput::ensure_fits(uint64_t bytes,
                            const char* what,
                            const char* subject) {
  uint64_t end = (uint64_t)m_offset + bytes;
  always_assert_log(end <= m_output_size,
                    "A %s of up to %" PRIu64
                    " bytes does not fit at offset %u of the %zu-byte dex "
                    "output buffer: %s",
                    what, bytes, m_offset, m_output_size, subject);
  // Do not let slack in this bound cover a later producer.
  m_checked_through = end;
}

void DexOutput::ensure_fits(
    uint64_t bytes,
    const char* what,
    const std::function<std::string()>& describe_subject) {
  uint64_t end = (uint64_t)m_offset + bytes;
  if (end > m_output_size) {
    const auto subject = describe_subject();
    always_assert_log(false,
                      "A %s of up to %" PRIu64
                      " bytes does not fit at offset %u of the %zu-byte dex "
                      "output buffer: %s",
                      what, bytes, m_offset, m_output_size, subject.c_str());
  }
  m_checked_through = end;
}

void DexOutput::inc_offset(uint64_t v) {
  // m_offset is uint32_t, so `m_offset + v` would wrap mod 2^32 before it could
  // exceed m_output_size. Widen first.
  uint64_t next = (uint64_t)m_offset + v;
  // Two distinct bounds, in order of what they protect.
  //
  // First: nothing may advance the cursor that was not bounds-checked before it
  // was written. This is the memory-safety invariant.
  always_assert_log(next <= m_checked_through,
                    "Cursor advance to %" PRIu64
                    " exceeds checked extent %" PRIu64 ".",
                    next, m_checked_through);
  // Second: the size policy. Distinct from the allocation, which is larger by
  // k_output_margin -- that headroom is what lets an item overshooting the
  // policy land safely, so this reports it rather than ensure_fits failing
  // first with a memory-safety message.
  always_assert_log(next < policy_cap(),
                    "Running into output safety margin: %" PRIu64 " of %" PRIu64
                    "(%zu). Increase the buffer "
                    "size with `-J dex_output_buffer_size=`.",
                    next, policy_cap(), m_output_size);
  m_offset = (uint32_t)next;
  // Consume this producer's check so its slack cannot cover the next one.
  m_checked_through = m_offset;
}
