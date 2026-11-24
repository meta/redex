/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "DexIdx.h"

#include "Debug.h"
#include "DexAnnotation.h"
#include "DexCallSite.h"
#include "DexClass.h"
#include "DexMethodHandle.h"
#include "TypeUtil.h"

#define INIT_DMAP_ID(TYPE)                                                \
  always_assert_type_log(dh->TYPE##_ids_off < dh->file_size, INVALID_DEX, \
                         #TYPE " section offset out of range");           \
  m_##TYPE##_ids = reinterpret_cast<const dex_##TYPE##_id*>(              \
      m_dexbase + dh->TYPE##_ids_off);                                    \
  m_##TYPE##_ids_size = dh->TYPE##_ids_size;                              \
  m_##TYPE##_cache.resize(dh->TYPE##_ids_size)

DexIdx::DexIdx(const dex_header* dh) {
  m_dexbase = reinterpret_cast<const uint8_t*>(dh);
  INIT_DMAP_ID(string);
  INIT_DMAP_ID(type);
  INIT_DMAP_ID(field);
  INIT_DMAP_ID(method);
  INIT_DMAP_ID(proto);

  const dex_map_list* map_list =
      reinterpret_cast<const dex_map_list*>(m_dexbase + dh->map_off);
  for (uint32_t i = 0; i < map_list->size; i++) {
    const auto& item = map_list->items[i];
    switch (item.type) {
    case TYPE_CALL_SITE_ID_ITEM: {
      const dex_callsite_id* callsite_ids =
          reinterpret_cast<const dex_callsite_id*>(
              reinterpret_cast<const uint8_t*>(dh) + item.offset);
      m_callsite_ids = const_cast<dex_callsite_id*>(callsite_ids);
      m_callsite_ids_size = item.size;
      m_callsite_cache.resize(m_callsite_ids_size);
    } break;
    case TYPE_METHOD_HANDLE_ITEM: {
      const dex_methodhandle_id* methodhandle_ids =
          reinterpret_cast<const dex_methodhandle_id*>(
              reinterpret_cast<const uint8_t*>(dh) + item.offset);
      m_methodhandle_ids = const_cast<dex_methodhandle_id*>(methodhandle_ids);
      m_methodhandle_ids_size = item.size;
      m_methodhandle_cache.resize(m_methodhandle_ids_size);
    } break;
    default:
      break;
    }
  }
}

DexCallSite* DexIdx::get_callsiteidx_fromdex(uint32_t csidx) {
  redex_assert(csidx < m_callsite_ids_size);
  // callsites are indirected through the callsite_id table, because
  // they are variable length. so first find the real offset of this
  // callsite
  const uint8_t* callsite_data = m_dexbase + m_callsite_ids[csidx].callsite_off;
  auto callsite_eva = get_encoded_value_array(this, callsite_data);
  auto* evalues = callsite_eva->evalues();
  redex_assert(evalues != nullptr);
  // A call site starts with the bootstrap method handle, method name and
  // method type.
  always_assert_type_log(
      evalues->size() >= 3, INVALID_DEX,
      "Callsite item has too few values (%zu), expected at least 3",
      evalues->size());
  DexEncodedValue* ev_linker_method_handle = evalues->at(0).get();
  always_assert_type_log(ev_linker_method_handle->evtype() ==
                             DEVT_METHOD_HANDLE,
                         INVALID_DEX,
                         "Unexpected evtype callsite item arg 0: %d",
                         ev_linker_method_handle->evtype());
  DexEncodedValue* ev_linker_method_name = evalues->at(1).get();
  always_assert_type_log(ev_linker_method_name->evtype() == DEVT_STRING,
                         INVALID_DEX,
                         "Unexpected evtype callsite item arg 1: %d",
                         ev_linker_method_name->evtype());
  DexEncodedValue* ev_linker_method_type = evalues->at(2).get();
  always_assert_type_log(ev_linker_method_type->evtype() == DEVT_METHOD_TYPE,
                         INVALID_DEX,
                         "Unexpected evtype callsite item arg 2: %d",
                         ev_linker_method_type->evtype());
  DexMethodHandle* linker_method_handle =
      (dynamic_cast<DexEncodedValueMethodHandle*>(ev_linker_method_handle))
          ->methodhandle();
  const auto* linker_method_name =
      (dynamic_cast<DexEncodedValueString*>(ev_linker_method_name))->string();
  DexProto* linker_method_proto =
      (dynamic_cast<DexEncodedValueMethodType*>(ev_linker_method_type))
          ->proto();
  std::vector<std::unique_ptr<DexEncodedValue>> linker_args;
  for (unsigned long i = 3; i < evalues->size(); ++i) {
    auto& ev = evalues->at(i);
    linker_args.emplace_back(std::move(ev));
  }
  auto* callsite = new DexCallSite(linker_method_handle,
                                   linker_method_name,
                                   linker_method_proto,
                                   std::move(linker_args));
  g_redex->publish_callsite(callsite);
  return callsite;
}

DexMethodHandle* DexIdx::get_methodhandleidx_fromdex(uint32_t mhidx) {
  redex_assert(mhidx < m_methodhandle_ids_size);
  auto type_uint16 = m_methodhandle_ids[mhidx].method_handle_type;
  always_assert_type_log(
      type_uint16 >= MethodHandleType::METHOD_HANDLE_TYPE_STATIC_PUT &&
          type_uint16 <= MethodHandleType::METHOD_HANDLE_TYPE_INVOKE_INTERFACE,
      INVALID_DEX,
      "Invalid MethodHandle type");
  MethodHandleType method_handle_type = (MethodHandleType)type_uint16;
  auto id = m_methodhandle_ids[mhidx].field_or_method_id;
  if (DexMethodHandle::isInvokeType(method_handle_type)) {
    return DexMethodHandle::make_method_handle(method_handle_type,
                                               get_methodidx(id));
  }
  return DexMethodHandle::make_method_handle(method_handle_type,
                                             get_fieldidx(id));
}

std::string_view DexIdx::get_string_data(uint32_t stridx,
                                         uint32_t* utfsize) const {
  redex_assert(stridx < m_string_ids_size);
  uint32_t stroff = m_string_ids[stridx].offset;
  // Bounds check is conservative. May incorrectly reject short strings
  // at the end of the file.
  always_assert_type_log(
      stroff < reinterpret_cast<const dex_header*>(m_dexbase)->file_size - 5,
      INVALID_DEX, "String data offset out of range");
  const uint8_t* dstr = m_dexbase + stroff;
  /* Strip off uleb128 size encoding */

  uint32_t utfsize_local = read_uleb128(&dstr);
  // Just double-check that we really read 5B max.
  redex_assert(dstr <= m_dexbase + get_file_size());
  if (utfsize != nullptr) {
    *utfsize = utfsize_local;
  }
  // Find null terminator.
  const auto* null_cur = dstr;
  while (null_cur < m_dexbase + get_file_size() && *null_cur != '\0') {
    ++null_cur;
  }
  always_assert_type_log(null_cur < m_dexbase + get_file_size(), INVALID_DEX,
                         "Missing null terminator");
  return std::string_view(reinterpret_cast<const char*>(dstr), null_cur - dstr);
}
const DexString* DexIdx::get_stringidx_fromdex(uint32_t stridx) {
  uint32_t utfsize;
  auto str_data = get_string_data(stridx, &utfsize);
  const auto* ret = DexString::make_string(str_data);
  always_assert_type_log(
      ret->length() == utfsize,
      INVALID_DEX,
      "Parsed string UTF size is not the same as stringidx size. %u != %u",
      ret->length(),
      utfsize);
  return ret;
}

DexType* DexIdx::get_typeidx_fromdex(uint32_t typeidx) {
  redex_assert(typeidx < m_type_ids_size);
  uint32_t stridx = m_type_ids[typeidx].string_idx;
  const auto* dexstr = get_stringidx(stridx);
  always_assert_type_log(type::is_valid(dexstr->str()), INVALID_DEX,
                         "Not a valid type descriptor");
  return DexType::make_type(dexstr);
}

DexFieldRef* DexIdx::get_fieldidx_fromdex(uint32_t fidx) {
  redex_assert(fidx < m_field_ids_size);
  DexType* container = get_typeidx(m_field_ids[fidx].classidx);
  DexType* ftype = get_typeidx(m_field_ids[fidx].typeidx);
  const auto* name = get_stringidx(m_field_ids[fidx].nameidx);
  return DexField::make_field(container, name, ftype);
}

DexMethodRef* DexIdx::get_methodidx_fromdex(uint32_t midx) {
  redex_assert(midx < m_method_ids_size);
  DexType* container = get_typeidx(m_method_ids[midx].classidx);
  DexProto* proto = get_protoidx(m_method_ids[midx].protoidx);
  const auto* name = get_stringidx(m_method_ids[midx].nameidx);
  return DexMethod::make_method(container, name, proto);
}

DexProto* DexIdx::get_protoidx_fromdex(uint32_t pidx) {
  redex_assert(pidx < m_proto_ids_size);
  DexType* rtype = get_typeidx(m_proto_ids[pidx].rtypeidx);
  const auto* shorty = get_stringidx(m_proto_ids[pidx].shortyidx);
  DexTypeList* args = get_type_list(m_proto_ids[pidx].param_off);
  return DexProto::make_proto(rtype, args, shorty);
}

DexTypeList* DexIdx::get_type_list(uint32_t offset) {
  if (offset == 0) {
    return DexTypeList::make_type_list({});
  }
  const uint32_t* tlp = get_uint_data(offset);
  uint32_t size = *tlp++;
  // T137425749
  always_assert_type_log(size < get_file_size() - offset, INVALID_DEX,
                         "Size too big");
  always_assert_type_log(offset <= get_file_size() - 2 * size, INVALID_DEX,
                         "Offset out of bounds");
  const uint16_t* typep = reinterpret_cast<const uint16_t*>(tlp);
  DexTypeList::ContainerType tlist;
  tlist.reserve(size);
  for (uint32_t i = 0; i < size; i++) {
    tlist.push_back(get_typeidx(typep[i]));
  }
  return DexTypeList::make_type_list(std::move(tlist));
}
