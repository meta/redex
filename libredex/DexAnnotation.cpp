/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "DexAnnotation.h"

#include <sstream>

#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexClass.h"
#include "DexIdx.h"
#include "DexOutput.h"
#include "Show.h"
#include "TypeUtil.h"

void DexEncodedValueMethodType::gather_strings(
    std::vector<const DexString*>& lstring) const {
  proto()->gather_strings(lstring);
}

void DexEncodedValueMethodType::gather_types(
    std::vector<const DexType*>& ltype) const {
  proto()->gather_types(ltype);
}

void DexEncodedValueMethodType::gather_protos(
    std::vector<DexProto*>& lproto) const {
  lproto.push_back(proto());
}

void DexEncodedValueString::gather_strings(
    std::vector<const DexString*>& lstring) const {
  lstring.push_back(string());
}

void DexEncodedValueType::gather_types(
    std::vector<const DexType*>& ltype) const {
  ltype.push_back(type());
}

void DexEncodedValueField::gather_fields(
    std::vector<DexFieldRef*>& lfield) const {
  lfield.push_back(field());
}

void DexEncodedValueMethod::gather_methods(
    std::vector<DexMethodRef*>& lmethod) const {
  lmethod.push_back(method());
}

void DexEncodedValueMethodHandle::gather_methods(
    std::vector<DexMethodRef*>& lmethod) const {
  methodhandle()->gather_methods(lmethod);
}

void DexEncodedValueMethodHandle::gather_fields(
    std::vector<DexFieldRef*>& lfield) const {
  methodhandle()->gather_fields(lfield);
}

void DexEncodedValueMethodHandle::gather_methodhandles(
    std::vector<DexMethodHandle*>& lhandles) const {
  lhandles.push_back(methodhandle());
}

void DexEncodedValueArray::gather_strings(
    std::vector<const DexString*>& lstring) const {
  for (auto& ev : *evalues()) {
    ev->gather_strings(lstring);
  }
}

void DexEncodedValueArray::gather_types(
    std::vector<const DexType*>& ltype) const {
  for (auto& ev : *evalues()) {
    ev->gather_types(ltype);
  }
}

void DexEncodedValueArray::gather_fields(
    std::vector<DexFieldRef*>& lfield) const {
  for (auto& ev : *evalues()) {
    ev->gather_fields(lfield);
  }
}

void DexEncodedValueArray::gather_methods(
    std::vector<DexMethodRef*>& lmethod) const {
  for (auto& ev : *evalues()) {
    ev->gather_methods(lmethod);
  }
}

void DexEncodedValueArray::gather_methodhandles(
    std::vector<DexMethodHandle*>& lmethodhandle) const {
  for (auto& ev : *evalues()) {
    ev->gather_methodhandles(lmethodhandle);
  }
}

void DexEncodedValueArray::gather_protos(std::vector<DexProto*>& lproto) const {
  for (auto& ev : *evalues()) {
    ev->gather_protos(lproto);
  }
}

void DexEncodedValueAnnotation::gather_strings(
    std::vector<const DexString*>& lstring) const {
  for (auto const& elem : m_annotations) {
    lstring.push_back(elem.string);
    elem.encoded_value->gather_strings(lstring);
  }
}

void DexEncodedValueAnnotation::gather_types(
    std::vector<const DexType*>& ltype) const {
  ltype.push_back(m_type);
  for (auto const& anno : m_annotations) {
    anno.encoded_value->gather_types(ltype);
  }
}

void DexEncodedValueAnnotation::gather_fields(
    std::vector<DexFieldRef*>& lfield) const {
  for (auto const& anno : m_annotations) {
    anno.encoded_value->gather_fields(lfield);
  }
}

void DexEncodedValueAnnotation::gather_methods(
    std::vector<DexMethodRef*>& lmethod) const {
  for (auto const& anno : m_annotations) {
    anno.encoded_value->gather_methods(lmethod);
  }
}

void DexEncodedValueAnnotation::gather_methodhandles(
    std::vector<DexMethodHandle*>& lmethodhandle) const {
  for (auto const& anno : m_annotations) {
    anno.encoded_value->gather_methodhandles(lmethodhandle);
  }
}

void DexEncodedValueAnnotation::gather_protos(
    std::vector<DexProto*>& lproto) const {
  for (auto const& anno : m_annotations) {
    anno.encoded_value->gather_protos(lproto);
  }
}

void DexAnnotation::gather_strings(
    std::vector<const DexString*>& lstring) const {
  for (auto const& anno : m_anno_elems) {
    lstring.push_back(anno.string);
    anno.encoded_value->gather_strings(lstring);
  }
}

void DexAnnotation::gather_types(std::vector<const DexType*>& ltype) const {
  ltype.push_back(m_type);
  for (auto const& anno : m_anno_elems) {
    anno.encoded_value->gather_types(ltype);
  }
}

void DexAnnotation::gather_fields(std::vector<DexFieldRef*>& lfield) const {
  for (auto const& anno : m_anno_elems) {
    anno.encoded_value->gather_fields(lfield);
  }
}

void DexAnnotation::gather_methods(std::vector<DexMethodRef*>& lmethod) const {
  for (auto const& anno : m_anno_elems) {
    anno.encoded_value->gather_methods(lmethod);
  }
}

void DexAnnotation::gather_methodhandles(
    std::vector<DexMethodHandle*>& lmethodhandle) const {
  for (auto const& anno : m_anno_elems) {
    anno.encoded_value->gather_methodhandles(lmethodhandle);
  }
}

void DexAnnotation::gather_protos(std::vector<DexProto*>& lproto) const {
  for (auto const& anno : m_anno_elems) {
    anno.encoded_value->gather_protos(lproto);
  }
}

void DexAnnotationSet::combine_with(const DexAnnotationSet& other) {
  UnorderedSet<DexType*> existing_annos_type;
  for (const auto& existing_anno : m_annotations) {
    existing_annos_type.emplace(existing_anno->type());
  }
  auto const& other_annos = other.m_annotations;
  for (auto const& anno : other_annos) {
    if (existing_annos_type.count(anno->type()) == 0) {
      m_annotations.emplace_back(new DexAnnotation(anno->clone()));
    }
  }
}

void DexAnnotationSet::gather_strings(
    std::vector<const DexString*>& lstring) const {
  for (auto const& anno : m_annotations) {
    anno->gather_strings(lstring);
  }
}

void DexAnnotationSet::gather_types(std::vector<const DexType*>& ltype) const {
  for (auto const& anno : m_annotations) {
    anno->gather_types(ltype);
  }
}

void DexAnnotationSet::gather_methods(
    std::vector<DexMethodRef*>& lmethod) const {
  for (auto const& anno : m_annotations) {
    anno->gather_methods(lmethod);
  }
}

void DexAnnotationSet::gather_fields(std::vector<DexFieldRef*>& lfield) const {
  for (auto const& anno : m_annotations) {
    anno->gather_fields(lfield);
  }
}

void DexAnnotationSet::gather_methodhandles(
    std::vector<DexMethodHandle*>& lmethodhandle) const {
  for (auto const& anno : m_annotations) {
    anno->gather_methodhandles(lmethodhandle);
  }
}

void DexAnnotationSet::gather_protos(std::vector<DexProto*>& lproto) const {
  for (auto const& anno : m_annotations) {
    anno->gather_protos(lproto);
  }
}

uint64_t read_evarg(const uint8_t*& encdata,
                    uint8_t evarg,
                    bool sign_extend /* = false */
) {
  uint64_t v = *encdata++;
  int shift = 8;
  while ((evarg--) != 0u) {
    v |= uint64_t(*encdata++) << shift;
    shift += 8;
  }
  if (sign_extend) {
    v = (int64_t)(v << (64 - shift)) >> (64 - shift);
  }
  return v;
}

void type_encoder(std::vector<uint8_t>& encdata, uint8_t type, uint64_t val) {
  uint8_t devtb = DEVT_HDR_TYPE(type);
  int count = 0;
  uint64_t t = (val >> 8);
  while (t != 0u) {
    count++;
    t >>= 8;
  }
  devtb |= TO_DEVT_HDR_ARG(count);
  encdata.push_back(devtb);
  t = (val >> 8);
  encdata.push_back(val & 0xff);
  while (t != 0u) {
    encdata.push_back(t & 0xff);
    t >>= 8;
  }
}

void type_encoder_signext(std::vector<uint8_t>& encdata,
                          uint8_t type,
                          uint64_t val) {
  size_t mp = encdata.size();
  encdata.push_back(0);
  int64_t sval = static_cast<int64_t>(val);
  int64_t t = sval;
  int bytes = 0;
  while (true) {
    uint8_t emit = t & 0xff;
    int64_t rest = t >> 8;
    encdata.push_back(emit);
    bytes++;
    if (rest == 0) {
      if ((emit & 0x80) == 0) {
        break;
      }
    }
    if (rest == -1) {
      if ((emit & 0x80) == 0x80) {
        break;
      }
    }
    t = rest;
  }
  encdata[mp] = DEVT_HDR_TYPE(type) | TO_DEVT_HDR_ARG(bytes - 1);
}

void type_encoder_fp(std::vector<uint8_t>& encdata,
                     uint8_t type,
                     uint64_t val) {
  // Ignore trailing zero bytes.
  int bytes = 0;
  while ((val != 0u) && ((val & 0xff) == 0)) {
    val >>= 8;
    bytes++;
  }
  int encbytes;
  switch (type) {
  case DEVT_FLOAT:
    encbytes = 4 - bytes;
    break;
  case DEVT_DOUBLE:
    encbytes = 8 - bytes;
    break;
  default:
    not_reached();
  }
  if (val == 0) {
    encbytes = 1;
  }
  // Encode.
  encdata.push_back(DEVT_HDR_TYPE(type) | TO_DEVT_HDR_ARG(encbytes - 1));
  for (int i = 0; i < encbytes; i++) {
    encdata.push_back(val & 0xff);
    val >>= 8;
  }
}

static void uleb_append(std::vector<uint8_t>& bytes, uint32_t v) {
  std::array<uint8_t, 5> tarray{};
  uint8_t* pend = write_uleb128(tarray.data(), v);
  for (uint8_t* p = tarray.data(); p < pend; p++) {
    bytes.push_back(*p);
  }
}

void DexEncodedValue::encode(DexOutputIdx* /*dodx*/,
                             std::vector<uint8_t>& encdata) {
  switch (m_evtype) {
  case DEVT_BYTE:
  case DEVT_SHORT:
  case DEVT_INT:
  case DEVT_LONG:
    type_encoder_signext(encdata, m_evtype, m_val.m_value);
    return;
  case DEVT_FLOAT:
  case DEVT_DOUBLE:
    type_encoder_fp(encdata, m_evtype, m_val.m_value);
    return;
  default:
    // TOOD: Should this really be here?
    type_encoder(encdata, m_evtype, as_value());
    return;
  }
}

void DexEncodedValue::vencode(DexOutputIdx* dodx, std::vector<uint8_t>& bytes) {
  encode(dodx, bytes);
}

void DexEncodedValueBit::encode(DexOutputIdx* /*dodx*/,
                                std::vector<uint8_t>& encdata) {
  uint8_t devtb = DEVT_HDR_TYPE(m_evtype);
  if (m_val.m_value != 0u) {
    devtb |= TO_DEVT_HDR_ARG(1);
  }
  encdata.push_back(devtb);
}

void DexEncodedValueString::encode(DexOutputIdx* dodx,
                                   std::vector<uint8_t>& encdata) {
  uint32_t sidx = dodx->stringidx(string());
  type_encoder(encdata, m_evtype, sidx);
}

void DexEncodedValueType::encode(DexOutputIdx* dodx,
                                 std::vector<uint8_t>& encdata) {
  uint32_t tidx = dodx->typeidx(type());
  type_encoder(encdata, m_evtype, tidx);
}

void DexEncodedValueField::encode(DexOutputIdx* dodx,
                                  std::vector<uint8_t>& encdata) {
  uint32_t fidx = dodx->fieldidx(field());
  type_encoder(encdata, m_evtype, fidx);
}

void DexEncodedValueMethod::encode(DexOutputIdx* dodx,
                                   std::vector<uint8_t>& encdata) {
  uint32_t midx = dodx->methodidx(method());
  type_encoder(encdata, m_evtype, midx);
}

void DexEncodedValueMethodType::encode(DexOutputIdx* dodx,
                                       std::vector<uint8_t>& encdata) {
  uint32_t pidx = dodx->protoidx(proto());
  type_encoder(encdata, m_evtype, pidx);
}

void DexEncodedValueMethodHandle::encode(DexOutputIdx* dodx,
                                         std::vector<uint8_t>& encdata) {
  uint32_t mhidx = dodx->methodhandleidx(methodhandle());
  type_encoder(encdata, m_evtype, mhidx);
}

void DexEncodedValueArray::encode(DexOutputIdx* dodx,
                                  std::vector<uint8_t>& encdata) {
  /*
   * Static values are implied to be DEVT_ARRAY, and thus don't
   * have a type byte.
   */
  if (!m_static_val) {
    uint8_t devtb = DEVT_HDR_TYPE(m_evtype);
    encdata.push_back(devtb);
  }
  uleb_append(encdata, (uint32_t)evalues()->size());
  for (auto const& ev : *evalues()) {
    ev->encode(dodx, encdata);
  }
}

void DexEncodedValueAnnotation::encode(DexOutputIdx* dodx,
                                       std::vector<uint8_t>& encdata) {
  uint8_t devtb = DEVT_HDR_TYPE(m_evtype);
  uint32_t tidx = dodx->typeidx(m_type);
  encdata.push_back(devtb);
  uleb_append(encdata, tidx);
  uleb_append(encdata, (uint32_t)m_annotations.size());
  for (auto const& dae : m_annotations) {
    const auto* str = dae.string;
    DexEncodedValue* dev = dae.encoded_value.get();
    uint32_t sidx = dodx->stringidx(str);
    uleb_append(encdata, sidx);
    dev->encode(dodx, encdata);
  }
}

static DexAnnotationElement get_annotation_element(DexIdx* idx,
                                                   const uint8_t*& encdata) {
  uint32_t sidx = idx->read_uleb128_checked(&encdata);
  const auto* name = idx->get_stringidx(sidx);
  always_assert_type_log(name != nullptr, INVALID_DEX,
                         "Invalid string idx in annotation element");
  return DexAnnotationElement(name,
                              DexEncodedValue::get_encoded_value(idx, encdata));
}

std::unique_ptr<DexEncodedValueArray> get_encoded_value_array(
    DexIdx* idx, const uint8_t*& encdata) {
  uint32_t size = idx->read_uleb128_checked(&encdata);
  using Vec = std::vector<std::unique_ptr<DexEncodedValue>>;
  auto evlist = Vec{};
  always_assert_type_log(size <= static_cast<uint64_t>(idx->end() - encdata),
                         INVALID_DEX,
                         "Encoded value array size exceeds dex size");
  evlist.reserve(size);
  for (uint32_t i = 0; i < size; i++) {
    evlist.emplace_back(DexEncodedValue::get_encoded_value(idx, encdata));
  }
  return std::make_unique<DexEncodedValueArray>(new Vec{std::move(evlist)});
}

bool DexEncodedValue::is_evtype_primitive() const {
  switch (m_evtype) {
  case DEVT_BYTE:
  case DEVT_SHORT:
  case DEVT_CHAR:
  case DEVT_INT:
  case DEVT_LONG:
  case DEVT_FLOAT:
  case DEVT_DOUBLE:
  // case DEVT_NULL:
  case DEVT_BOOLEAN:
    return true;
  default:
    return false;
  };
}

bool DexEncodedValue::is_zero() const {
  switch (m_evtype) {
  case DEVT_BYTE:
  case DEVT_SHORT:
  case DEVT_CHAR:
  case DEVT_INT:
  case DEVT_LONG:
  case DEVT_FLOAT:
  case DEVT_DOUBLE:
  case DEVT_BOOLEAN:
    return m_val.m_value == 0;
  case DEVT_NULL:
    return true;
  default:
    return false;
  }
}

bool DexEncodedValue::is_wide() const {
  return m_evtype == DEVT_LONG || m_evtype == DEVT_DOUBLE;
}

std::unique_ptr<DexEncodedValue> DexEncodedValue::zero_for_type(DexType* type) {
  if (type == type::_byte()) {
    return std::unique_ptr<DexEncodedValue>(
        new DexEncodedValuePrimitive(DEVT_BYTE, (uint64_t)0));
  } else if (type == type::_char()) {
    return std::unique_ptr<DexEncodedValue>(
        new DexEncodedValuePrimitive(DEVT_CHAR, (uint64_t)0));
  } else if (type == type::_short()) {
    return std::unique_ptr<DexEncodedValue>(
        new DexEncodedValuePrimitive(DEVT_SHORT, (uint64_t)0));
  } else if (type == type::_int()) {
    return std::unique_ptr<DexEncodedValue>(
        new DexEncodedValuePrimitive(DEVT_INT, (uint64_t)0));
  } else if (type == type::_long()) {
    return std::unique_ptr<DexEncodedValue>(
        new DexEncodedValuePrimitive(DEVT_LONG, (uint64_t)0));
  } else if (type == type::_float()) {
    return std::unique_ptr<DexEncodedValue>(
        new DexEncodedValuePrimitive(DEVT_FLOAT, (uint64_t)0));
  } else if (type == type::_double()) {
    return std::unique_ptr<DexEncodedValue>(
        new DexEncodedValuePrimitive(DEVT_DOUBLE, (uint64_t)0));
  } else if (type == type::_boolean()) {
    return std::unique_ptr<DexEncodedValue>(
        new DexEncodedValueBit(DEVT_BOOLEAN, false));
  } else {
    // not a primitive
    return std::unique_ptr<DexEncodedValue>(
        new DexEncodedValueBit(DEVT_NULL, false));
  }
}

std::unique_ptr<DexEncodedValue> DexEncodedValue::get_encoded_value(
    DexIdx* idx, const uint8_t*& encdata) {
  always_assert_type_log(encdata < idx->end(), INVALID_DEX, "Dex overflow");
  uint8_t evhdr = *encdata++;
  DexEncodedValueTypes evt = (DexEncodedValueTypes)DEVT_HDR_TYPE(evhdr);
  uint8_t evarg = DEVT_HDR_ARG(evhdr);
  switch (evt) {
  case DEVT_BYTE:
    always_assert_type_log(evarg == 0, INVALID_DEX, "evarg out of bounds");
    [[fallthrough]];
  case DEVT_SHORT:
    always_assert_type_log(evarg <= 1, INVALID_DEX, "evarg out of bounds");
    [[fallthrough]];
  case DEVT_INT:
    always_assert_type_log(evarg <= 3, INVALID_DEX, "evarg out of bounds");
    [[fallthrough]];
  case DEVT_LONG: {
    always_assert_type_log(evarg <= 7, INVALID_DEX, "evarg out of bounds");
    always_assert_type_log(encdata + evarg < idx->end(), INVALID_DEX,
                           "Dex overflow");
    uint64_t v = read_evarg(encdata, evarg, true /* sign_extend */);
    return std::unique_ptr<DexEncodedValue>(
        new DexEncodedValuePrimitive(evt, v));
  }
  case DEVT_CHAR: {
    always_assert_type_log(evarg <= 1, INVALID_DEX, "evarg out of bounds");
    always_assert_type_log(encdata + evarg < idx->end(), INVALID_DEX,
                           "Dex overflow");
    uint64_t v = read_evarg(encdata, evarg, false /* sign_extend */);
    return std::unique_ptr<DexEncodedValue>(
        new DexEncodedValuePrimitive(evt, v));
  }
  case DEVT_FLOAT: {
    always_assert_type_log(evarg <= 3, INVALID_DEX, "Unexpected float size: %u",
                           evarg);
    // We sign extend floats so that they can be treated just like signed ints
    always_assert_type_log(encdata + evarg < idx->end(), INVALID_DEX,
                           "Dex overflow");
    uint64_t v = read_evarg(encdata, evarg, true /* sign_extend */)
                 << ((3 - evarg) * 8);
    return std::unique_ptr<DexEncodedValue>(
        new DexEncodedValuePrimitive(evt, v));
  }
  case DEVT_DOUBLE: {
    always_assert_type_log(evarg <= 7, INVALID_DEX, "evarg out of bounds");
    always_assert_type_log(encdata + evarg < idx->end(), INVALID_DEX,
                           "Dex overflow");
    uint64_t v = read_evarg(encdata, evarg, false /* sign_extend */)
                 << ((7 - evarg) * 8);
    return std::unique_ptr<DexEncodedValue>(
        new DexEncodedValuePrimitive(evt, v));
  }
  case DEVT_METHOD_TYPE: {
    always_assert_type_log(evarg <= 3, INVALID_DEX, "evarg out of bounds");
    always_assert_type_log(encdata + evarg < idx->end(), INVALID_DEX,
                           "Dex overflow");
    uint32_t evidx = (uint32_t)read_evarg(encdata, evarg);
    DexProto* evproto = idx->get_protoidx(evidx);
    return std::unique_ptr<DexEncodedValue>(
        new DexEncodedValueMethodType(evproto));
  }
  case DEVT_METHOD_HANDLE: {
    always_assert_type_log(evarg <= 3, INVALID_DEX, "evarg out of bounds");
    always_assert_type_log(encdata + evarg < idx->end(), INVALID_DEX,
                           "Dex overflow");
    uint32_t evidx = (uint32_t)read_evarg(encdata, evarg);
    DexMethodHandle* evmethodhandle = idx->get_methodhandleidx(evidx);
    return std::unique_ptr<DexEncodedValue>(
        new DexEncodedValueMethodHandle(evmethodhandle));
  }

  case DEVT_NULL:
    always_assert_type_log(evarg == 0, INVALID_DEX, "evarg out of bounds");
    return std::unique_ptr<DexEncodedValue>(new DexEncodedValueBit(evt, false));
  case DEVT_BOOLEAN:
    always_assert_type_log(evarg <= 1, INVALID_DEX, "evarg out of bounds");
    return std::unique_ptr<DexEncodedValue>(
        new DexEncodedValueBit(evt, evarg > 0));
  case DEVT_STRING: {
    always_assert_type_log(evarg <= 3, INVALID_DEX, "evarg out of bounds");
    always_assert_type_log(encdata + evarg < idx->end(), INVALID_DEX,
                           "Dex overflow");
    uint32_t evidx = (uint32_t)read_evarg(encdata, evarg);
    const auto* evstring = idx->get_stringidx(evidx);
    always_assert_type_log(evstring != nullptr, INVALID_DEX,
                           "Invalid string idx in annotation element");
    return std::unique_ptr<DexEncodedValue>(
        new DexEncodedValueString(evstring));
  }
  case DEVT_TYPE: {
    always_assert_type_log(evarg <= 3, INVALID_DEX, "evarg out of bounds");
    always_assert_type_log(encdata + evarg < idx->end(), INVALID_DEX,
                           "Dex overflow");
    uint32_t evidx = (uint32_t)read_evarg(encdata, evarg);
    DexType* evtype = idx->get_typeidx(evidx);
    always_assert_type_log(evtype != nullptr, INVALID_DEX,
                           "Invalid type idx in annotation element");
    return std::unique_ptr<DexEncodedValue>(new DexEncodedValueType(evtype));
  }
  case DEVT_FIELD:
    always_assert_type_log(evarg <= 3, INVALID_DEX, "evarg out of bounds");
    [[fallthrough]];
  case DEVT_ENUM: {
    always_assert_type_log(evarg <= 3, INVALID_DEX, "evarg out of bounds");
    always_assert_type_log(encdata + evarg < idx->end(), INVALID_DEX,
                           "Dex overflow");
    uint32_t evidx = (uint32_t)read_evarg(encdata, evarg);
    DexFieldRef* evfield = idx->get_fieldidx(evidx);
    always_assert_type_log(evfield != nullptr, INVALID_DEX,
                           "Invalid field idx in annotation element");
    return std::unique_ptr<DexEncodedValue>(
        new DexEncodedValueField(evt, evfield));
  }
  case DEVT_METHOD: {
    always_assert_type_log(evarg <= 3, INVALID_DEX, "evarg out of bounds");
    always_assert_type_log(encdata + evarg < idx->end(), INVALID_DEX,
                           "Dex overflow");
    uint32_t evidx = (uint32_t)read_evarg(encdata, evarg);
    DexMethodRef* evmethod = idx->get_methodidx(evidx);
    always_assert_type_log(evmethod != nullptr, INVALID_DEX,
                           "Invalid method idx in annotation element");
    return std::unique_ptr<DexEncodedValue>(
        new DexEncodedValueMethod(evmethod));
  }
  case DEVT_ARRAY:
    always_assert_type_log(evarg == 0, INVALID_DEX, "evarg out of bounds");
    return get_encoded_value_array(idx, encdata);
  case DEVT_ANNOTATION: {
    always_assert_type_log(evarg == 0, INVALID_DEX, "evarg out of bounds");
    EncodedAnnotations eanno{};
    uint32_t tidx = idx->read_uleb128_checked(&encdata);
    uint32_t count = idx->read_uleb128_checked(&encdata);
    DexType* type = idx->get_typeidx(tidx);
    always_assert_type_log(type != nullptr, INVALID_DEX,
                           "Invalid DEVT_ANNOTATION within annotation type");
    always_assert_type_log(count <= static_cast<uint64_t>(idx->end() - encdata),
                           INVALID_DEX,
                           "Encoded annotation element count exceeds dex size");
    eanno.reserve(count);
    for (uint32_t i = 0; i < count; i++) {
      eanno.emplace_back(get_annotation_element(idx, encdata));
    }
    return std::unique_ptr<DexEncodedValue>(
        new DexEncodedValueAnnotation(type, std::move(eanno)));
  }
  };
  always_assert_type_log(false, INVALID_DEX, "Bogus annotation type");
}

std::unique_ptr<DexAnnotation> DexAnnotation::get_annotation(
    DexIdx* idx, uint32_t anno_off) {
  if (anno_off == 0) {
    return nullptr;
  }
  const uint8_t* encdata = idx->get_uleb_data(anno_off);
  always_assert_type_log(encdata < idx->end(), INVALID_DEX, "Dex overflow");
  uint8_t viz = *encdata++;
  always_assert_type_log(viz <= DAV_SYSTEM, INVALID_DEX,
                         "Invalid annotation visibility %d", viz);
  uint32_t tidx = idx->read_uleb128_checked(&encdata);
  uint32_t count = idx->read_uleb128_checked(&encdata);
  DexType* type = idx->get_typeidx(tidx);
  always_assert_type_log(type != nullptr, INVALID_DEX,
                         "Invalid annotation type");
  auto anno =
      std::make_unique<DexAnnotation>(type, (DexAnnotationVisibility)viz);
  always_assert_type_log(count <= static_cast<uint64_t>(idx->end() - encdata),
                         INVALID_DEX,
                         "Annotation element count exceeds dex size");
  anno->m_anno_elems.reserve(count);
  for (uint32_t i = 0; i < count; i++) {
    anno->m_anno_elems.emplace_back(get_annotation_element(idx, encdata));
  }
  return anno;
}

void DexAnnotation::add_element(const char* key,
                                std::unique_ptr<DexEncodedValue> value) {
  m_anno_elems.emplace_back(DexString::make_string(key), std::move(value));
}
void DexAnnotation::add_element(DexAnnotationElement elem) {
  m_anno_elems.emplace_back(std::move(elem));
}

std::unique_ptr<DexAnnotationSet> DexAnnotationSet::get_annotation_set(
    DexIdx* idx, uint32_t aset_off) {
  if (aset_off == 0) {
    return nullptr;
  }
  const uint32_t* adata = idx->get_uint_data(aset_off);
  auto aset = std::make_unique<DexAnnotationSet>();
  uint32_t count = *adata++;
  always_assert_type_log(adata <= adata + count, INVALID_DEX, "Dex overflow");
  always_assert_type_log(reinterpret_cast<const uint8_t*>(adata + count) <=
                             idx->end(),
                         INVALID_DEX, "Dex overflow");

  aset->m_annotations.reserve(count - std::count(adata, adata + count, 0));

  for (uint32_t i = 0; i < count; i++) {
    uint32_t off = adata[i];
    auto anno = DexAnnotation::get_annotation(idx, off);
    if (anno != nullptr) {
      aset->m_annotations.emplace_back(std::move(anno));
    }
  }
  return aset;
}

void DexAnnotationDirectory::calc_internals() {
  int cntviz = 0;
  auto updateCount = [this](DexAnnotationSet* das) {
    unsigned long ca, cv;
    das->viz_counts(ca, cv);
    m_anno_count += static_cast<int>(ca);
    m_aset_size += static_cast<int>(4 + 4 * ca);
    m_aset_count++;
    return cv;
  };
  if (m_class != nullptr) {
    cntviz += static_cast<int>(updateCount(m_class));
  }
  if (m_field) {
    for (auto const& p : *m_field) {
      DexAnnotationSet* das = p.second;
      cntviz += static_cast<int>(updateCount(das));
    }
  }
  if (m_method) {
    for (auto const& p : *m_method) {
      DexAnnotationSet* das = p.second;
      cntviz += static_cast<int>(updateCount(das));
    }
  }
  if (m_method_param) {
    for (auto const& p : *m_method_param) {
      ParamAnnotations* pa = p.second;
      m_xref_size += static_cast<int>(4 + 4 * pa->size());
      m_xref_count++;
      for (auto const& pp : *pa) {
        const auto& das = pp.second;
        cntviz += static_cast<int>(updateCount(das.get()));
      }
    }
  }
  if (m_anno_count != 0) {
    m_viz = (double)cntviz / m_anno_count;
  }
}

bool method_annotation_compare(std::pair<DexMethod*, DexAnnotationSet*> a,
                               std::pair<DexMethod*, DexAnnotationSet*> b) {
  return compare_dexmethods(a.first, b.first);
}

bool method_param_annotation_compare(
    std::pair<DexMethod*, ParamAnnotations*> a,
    std::pair<DexMethod*, ParamAnnotations*> b) {
  return compare_dexmethods(a.first, b.first);
}

bool field_annotation_compare(std::pair<DexFieldRef*, DexAnnotationSet*> a,
                              std::pair<DexFieldRef*, DexAnnotationSet*> b) {
  return compare_dexfields(a.first, b.first);
}

namespace {
void sort_annotation_set(DexAnnotationSet* aset) {
  if (aset == nullptr) {
    return;
  }
  auto& annos = aset->get_annotations();
  std::sort(annos.begin(), annos.end(), [](const auto& a, const auto& b) {
    return compare_dextypes(a->type(), b->type());
  });
}
} // namespace

void DexAnnotationDirectory::sort_members() {
  sort_annotation_set(m_class);
  if (m_field) {
    std::sort(m_field->begin(), m_field->end(), field_annotation_compare);
    for (auto& fanno : *m_field) {
      sort_annotation_set(fanno.second);
    }
  }
  if (m_method) {
    std::sort(m_method->begin(), m_method->end(), method_annotation_compare);
    for (auto& manno : *m_method) {
      sort_annotation_set(manno.second);
    }
  }
  if (m_method_param) {
    std::sort(m_method_param->begin(),
              m_method_param->end(),
              method_param_annotation_compare);
    for (auto& mpanno : *m_method_param) {
      ParamAnnotations* params = mpanno.second;
      for (auto& param : *params) {
        sort_annotation_set(param.second.get());
      }
    }
  }
}

// Precondition: sort_members() must have been called before any gather call.
void DexAnnotationDirectory::gather_asets(
    std::vector<DexAnnotationSet*>& aset) {
  if (m_class != nullptr) {
    aset.push_back(m_class);
  }
  if (m_field) {
    for (auto fanno : *m_field) {
      aset.push_back(fanno.second);
    }
  }
  if (m_method) {
    for (auto manno : *m_method) {
      aset.push_back(manno.second);
    }
  }
  if (m_method_param) {
    for (auto mpanno : *m_method_param) {
      ParamAnnotations* params = mpanno.second;
      for (auto& param : *params) {
        aset.push_back(param.second.get());
      }
    }
  }
}

// Precondition: sort_members() must have been called before any gather call.
void DexAnnotationDirectory::gather_xrefs(
    std::vector<ParamAnnotations*>& xrefs) {
  if (m_method_param) {
    for (auto param : *m_method_param) {
      ParamAnnotations* pa = param.second;
      xrefs.push_back(pa);
    }
  }
}

// Precondition: sort_members() must have been called before any gather call.
void DexAnnotationDirectory::gather_annotations(
    std::vector<DexAnnotation*>& alist) {
  if (m_class != nullptr) {
    m_class->gather_annotations(alist);
  }
  if (m_field) {
    for (auto fanno : *m_field) {
      DexAnnotationSet* das = fanno.second;
      das->gather_annotations(alist);
    }
  }
  if (m_method) {
    for (auto manno : *m_method) {
      DexAnnotationSet* das = manno.second;
      das->gather_annotations(alist);
    }
  }
  if (m_method_param) {
    for (auto mpanno : *m_method_param) {
      ParamAnnotations* params = mpanno.second;
      for (auto& param : *params) {
        auto& das = param.second;
        das->gather_annotations(alist);
      }
    }
  }
}

// Precondition: sort_members() must have been called before vencode.
void DexAnnotationDirectory::vencode(
    DexOutputIdx* dodx,
    std::vector<uint32_t>& annodirout,
    UnorderedMap<ParamAnnotations*, uint32_t>& xrefmap,
    UnorderedMap<DexAnnotationSet*, uint32_t>& asetmap) {
  uint32_t classoff = 0;
  uint32_t cntaf = 0;
  uint32_t cntam = 0;
  uint32_t cntamp = 0;
  if (m_class != nullptr) {
    always_assert_log(asetmap.count(m_class) != 0, "Uninitialized aset %p '%s'",
                      m_class, show(m_class).c_str());
    classoff = asetmap[m_class];
  }
  if (m_field) {
    cntaf = (uint32_t)m_field->size();
  }
  if (m_method) {
    cntam = (uint32_t)m_method->size();
  }
  if (m_method_param) {
    cntamp = (uint32_t)m_method_param->size();
  }
  annodirout.push_back(classoff);
  annodirout.push_back(cntaf);
  annodirout.push_back(cntam);
  annodirout.push_back(cntamp);
  if (m_field) {
    /* Optimization note:
     * A tape sort could be used instead as there are two different
     * ordered lists here.
     */
    for (auto const& p : *m_field) {
      DexAnnotationSet* das = p.second;
      annodirout.push_back(dodx->fieldidx(p.first));
      always_assert_log(asetmap.count(das) != 0, "Uninitialized aset %p '%s'",
                        das, show(das).c_str());
      annodirout.push_back(asetmap[das]);
    }
  }
  if (m_method) {
    for (auto const& p : *m_method) {
      DexMethod* m = p.first;
      DexAnnotationSet* das = p.second;
      uint32_t midx = dodx->methodidx(m);
      annodirout.push_back(midx);
      always_assert_log(asetmap.count(das) != 0, "Uninitialized aset %p '%s'",
                        das, show(das).c_str());
      annodirout.push_back(asetmap[das]);
    }
  }
  if (m_method_param) {
    for (auto const& p : *m_method_param) {
      ParamAnnotations* pa = p.second;
      annodirout.push_back(dodx->methodidx(p.first));
      always_assert_log(xrefmap.count(pa) != 0,
                        "Uninitialized ParamAnnotations %p", pa);
      annodirout.push_back(xrefmap[pa]);
    }
  }
}

void DexAnnotationSet::gather_annotations(std::vector<DexAnnotation*>& list) {
  for (auto& annotation : m_annotations) {
    list.push_back(annotation.get());
  }
}

void DexAnnotationSet::vencode(
    DexOutputIdx* /*dodx*/,
    std::vector<uint32_t>& asetout,
    UnorderedMap<DexAnnotation*, uint32_t>& annoout) {
  asetout.push_back((uint32_t)m_annotations.size());
  for (auto& anno : m_annotations) {
    always_assert_log(annoout.count(anno.get()) != 0,
                      "Uninitialized annotation %p '%s', bailing\n",
                      anno.get(),
                      show(anno.get()).c_str());
    asetout.push_back(annoout[anno.get()]);
  }
}

void DexAnnotation::vencode(DexOutputIdx* dodx, std::vector<uint8_t>& bytes) {
  bytes.push_back(m_viz);
  uleb_append(bytes, dodx->typeidx(m_type));
  uleb_append(bytes, (uint32_t)m_anno_elems.size());
  for (auto& elem : m_anno_elems) {
    const auto* string = elem.string;
    DexEncodedValue* ev = elem.encoded_value.get();
    uleb_append(bytes, dodx->stringidx(string));
    ev->vencode(dodx, bytes);
  }
}

namespace {
std::string show_helper(const DexEncodedValueArray* a, bool deobfuscated) {
  std::ostringstream ss;
  ss << (a->is_static_val() ? "(static) " : "");
  if (a->evalues() != nullptr) {
    bool first = true;
    for (const auto& evalue : *a->evalues()) {
      if (!first) {
        ss << ' ';
      }
      if (deobfuscated) {
        ss << evalue->show_deobfuscated();
      } else {
        ss << evalue->show();
      }
      first = false;
    }
  }
  return ss.str();
}

std::string show_helper(const EncodedAnnotations* annos, bool deobfuscated) {
  if (annos == nullptr) {
    return "";
  }
  std::ostringstream ss;
  bool first = true;
  for (auto const& pair : *annos) {
    if (!first) {
      ss << ", ";
    }
    ss << show(pair.string) << ":";
    if (deobfuscated) {
      ss << pair.encoded_value->show_deobfuscated();
    } else {
      ss << pair.encoded_value->show();
    }
    first = false;
  }
  return ss.str();
}
} // namespace

std::string show(const EncodedAnnotations* annos) {
  return show_helper(annos, false);
}

std::string show_deobfuscated(const EncodedAnnotations* annos) {
  return show_helper(annos, true);
}

std::string show(const EncodedAnnotations& annos) {
  return show_helper(&annos, false);
}

std::string show_deobfuscated(const EncodedAnnotations& annos) {
  return show_helper(&annos, true);
}

std::string DexEncodedValue::show() const {
  std::ostringstream ss;
  ss << as_value();
  return ss.str();
}

std::string DexEncodedValueAnnotation::show() const {
  std::ostringstream ss;
  ss << "type:" << ::show(m_type) << " annotations:" << ::show(m_annotations);
  return ss.str();
}

std::string DexEncodedValueAnnotation::show_deobfuscated() const {
  std::ostringstream ss;
  ss << "type:" << ::show(m_type)
     << " annotations:" << ::show_deobfuscated(m_annotations);
  return ss.str();
}

std::string DexEncodedValueArray::show() const {
  return show_helper(this, false);
}

std::string DexEncodedValueArray::show_deobfuscated() const {
  return show_helper(this, true);
}

std::string DexEncodedValueString::show() const {
  return ::show_escaped(string());
}

std::string DexEncodedValueString::show_deobfuscated() const {
  const auto* dex_string = string();
  auto starts_with_type_name = [](const std::string_view& s) {
    const auto* i = s.begin();
    while (i != s.end() && *i == '[') {
      i++;
    }
    return i != s.end() && *i == 'L';
  };
  // Check if this is possibly an obfuscated type name. At least length of LX/0;
  if (dex_string->is_simple() && dex_string->length() >= 5) {
    auto s = dex_string->str();
    auto last_char = s.back();
    if (starts_with_type_name(s) && (last_char == ';' || last_char == '<')) {
      // Note that array types should pass above check, which should get handled
      // gracefully by show_deobfuscated(const DexType*).
      std::string maybe_type_name(s);
      if (last_char == '<') {
        maybe_type_name.pop_back();
        maybe_type_name.push_back(';');
      }
      auto* maybe_type = DexType::get_type(maybe_type_name);
      if (maybe_type != nullptr) {
        auto result = ::show_deobfuscated(maybe_type);
        always_assert(!result.empty());
        if (last_char == '<') {
          result.pop_back();
          result.push_back('<');
        }
        return result;
      }
    }
  }
  return show();
}

std::string DexEncodedValueType::show() const { return ::show(type()); }
std::string DexEncodedValueType::show_deobfuscated() const {
  return ::show_deobfuscated(type());
}

std::string DexEncodedValueField::show() const { return ::show(field()); }
std::string DexEncodedValueField::show_deobfuscated() const {
  return ::show_deobfuscated(field());
}

std::string DexEncodedValueMethod::show() const { return ::show(method()); }
std::string DexEncodedValueMethod::show_deobfuscated() const {
  return ::show_deobfuscated(method());
}

std::string DexEncodedValueMethodType::show() const { return ::show(proto()); }
std::string DexEncodedValueMethodType::show_deobfuscated() const {
  return ::show_deobfuscated(proto());
}

std::string DexEncodedValueMethodHandle::show() const {
  return ::show(methodhandle());
}
std::string DexEncodedValueMethodHandle::show_deobfuscated() const {
  return ::show_deobfuscated(methodhandle());
}
