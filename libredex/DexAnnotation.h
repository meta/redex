/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <algorithm>
#include <boost/functional/hash.hpp>
#include <cstring>
#include <deque>
#include <map>
#include <vector>

#include "DeterministicContainers.h"
#include "Gatherable.h"

class DexFieldRef;
class DexIdx;
class DexMethod;
class DexMethodRef;
class DexOutputIdx;
class DexString;
class DexType;

enum DexEncodedValueTypes : uint8_t {
  DEVT_BYTE = 0x00,
  DEVT_SHORT = 0x02,
  DEVT_CHAR = 0x03,
  DEVT_INT = 0x04,
  DEVT_LONG = 0x06,
  DEVT_FLOAT = 0x10,
  DEVT_DOUBLE = 0x11,
  DEVT_METHOD_TYPE = 0x15,
  DEVT_METHOD_HANDLE = 0x16,
  DEVT_STRING = 0x17,
  DEVT_TYPE = 0x18,
  DEVT_FIELD = 0x19,
  DEVT_METHOD = 0x1a,
  DEVT_ENUM = 0x1b,
  DEVT_ARRAY = 0x1c,
  DEVT_ANNOTATION = 0x1d,
  DEVT_NULL = 0x1e,
  DEVT_BOOLEAN = 0x1f
};

inline uint8_t DEVT_HDR_TYPE(uint8_t x) { return x & 0x1f; }
inline uint8_t DEVT_HDR_ARG(uint8_t x) { return (x >> 5) & 0x7; }
inline uint8_t TO_DEVT_HDR_ARG(uint8_t x) { return (x & 0x7) << 5; }

enum DexAnnotationVisibility : uint8_t {
  DAV_BUILD = 0,
  DAV_RUNTIME = 1,
  DAV_SYSTEM = 2,
};

class DexEncodedValue : public Gatherable {
 protected:
  union Val {
    explicit Val(uint64_t v) { m_value = v; }
    explicit Val(void* v) { m_value_ptr = v; }
    explicit Val(const void* v) { m_value_ptr_const = v; }

    uint64_t m_value;
    void* m_value_ptr;
    const void* m_value_ptr_const;
  } m_val;
  DexEncodedValueTypes m_evtype;

  explicit DexEncodedValue(DexEncodedValueTypes type, uint64_t value = 0)
      : m_val(value), m_evtype(type) {}

  DexEncodedValue(DexEncodedValueTypes type, void* value_ptr)
      : m_val(value_ptr), m_evtype(type) {}

  DexEncodedValue(DexEncodedValueTypes type, const void* value_ptr)
      : m_val(value_ptr), m_evtype(type) {}

 public:
  virtual ~DexEncodedValue() = default;

  DexEncodedValueTypes evtype() const { return m_evtype; }
  bool is_evtype_primitive() const;
  void value(uint64_t value) { m_val = Val(value); }
  uint64_t value() const { return m_val.m_value; }
  static std::unique_ptr<DexEncodedValue> get_encoded_value(
      DexIdx* idx, const uint8_t*& encdata);
  virtual void encode(DexOutputIdx* dodx, std::vector<uint8_t>& encdata);
  void vencode(DexOutputIdx* dodx, std::vector<uint8_t>& bytes);

  // Deal with undefined behavior of reading the inactive member of a struct.
  uint64_t as_value() const {
    uint64_t tmp;
    memcpy(&tmp, &m_val, sizeof(uint64_t));
    return tmp;
  }

  virtual std::string show() const;
  virtual std::string show_deobfuscated() const { return show(); }
  virtual bool operator==(const DexEncodedValue& that) const {
    return m_evtype == that.m_evtype && as_value() == that.as_value();
  }
  virtual bool operator!=(const DexEncodedValue& that) const {
    return !(*this == that);
  }
  virtual size_t hash_value() const {
    size_t seed = boost::hash<uint8_t>()(m_evtype);
    boost::hash_combine(seed, as_value());
    return seed;
  }

  virtual std::unique_ptr<DexEncodedValue> clone() const = 0;

  bool is_zero() const;
  bool is_wide() const;
  static std::unique_ptr<DexEncodedValue> zero_for_type(DexType* type);
};

class DexEncodedValuePrimitive final : public DexEncodedValue {
 public:
  explicit DexEncodedValuePrimitive(DexEncodedValueTypes type,
                                    uint64_t value = 0)
      : DexEncodedValue(type, value) {}

  std::unique_ptr<DexEncodedValue> clone() const override {
    return std::make_unique<DexEncodedValuePrimitive>(*this);
  }
};

inline size_t hash_value(const DexEncodedValue& v) { return v.hash_value(); }

class DexEncodedValueBit : public DexEncodedValue {
 public:
  DexEncodedValueBit(DexEncodedValueTypes type, bool bit)
      : DexEncodedValue(type, static_cast<uint64_t>(bit)) {}

  void encode(DexOutputIdx* dodx, std::vector<uint8_t>& encdata) override;

  std::unique_ptr<DexEncodedValue> clone() const override {
    return std::unique_ptr<DexEncodedValue>(new DexEncodedValueBit(*this));
  }
};

class DexEncodedValueString : public DexEncodedValue {
 public:
  explicit DexEncodedValueString(const DexString* string)
      : DexEncodedValue(DEVT_STRING, string) {}

  const DexString* string() const {
    return static_cast<const DexString*>(m_val.m_value_ptr_const);
  }
  void string(const DexString* string) { m_val.m_value_ptr_const = string; }
  void gather_strings(std::vector<const DexString*>& lstring) const override;
  void encode(DexOutputIdx* dodx, std::vector<uint8_t>& encdata) override;

  std::string show() const override;
  std::string show_deobfuscated() const override;
  bool operator==(const DexEncodedValue& that) const override {
    if (m_evtype != that.evtype()) {
      return false;
    }
    return m_val.m_value_ptr_const ==
           dynamic_cast<const DexEncodedValueString*>(&that)
               ->m_val.m_value_ptr_const;
  }
  size_t hash_value() const override {
    size_t seed = boost::hash<uint8_t>()(m_evtype);
    boost::hash_combine(seed,
                        reinterpret_cast<uintptr_t>(m_val.m_value_ptr_const));
    return seed;
  }

  std::unique_ptr<DexEncodedValue> clone() const override {
    return std::unique_ptr<DexEncodedValue>(new DexEncodedValueString(*this));
  }
};

class DexEncodedValuePtr : public DexEncodedValue {
 protected:
  DexEncodedValuePtr(DexEncodedValueTypes type, void* data)
      : DexEncodedValue(type, data) {}

 public:
  bool operator==(const DexEncodedValue& that) const override {
    if (m_evtype != that.evtype()) {
      return false;
    }
    return m_val.m_value_ptr_const ==
           dynamic_cast<const DexEncodedValuePtr*>(&that)->m_val.m_value_ptr;
  }
  size_t hash_value() const override {
    size_t seed = boost::hash<uint8_t>()(m_evtype);
    boost::hash_combine(seed, reinterpret_cast<uintptr_t>(m_val.m_value_ptr));
    return seed;
  }

  std::unique_ptr<DexEncodedValue> clone() const override {
    return std::unique_ptr<DexEncodedValue>(new DexEncodedValuePtr(*this));
  }
};

class DexEncodedValueType : public DexEncodedValuePtr {
 public:
  explicit DexEncodedValueType(DexType* type)
      : DexEncodedValuePtr(DEVT_TYPE, type) {}

  void gather_types(std::vector<const DexType*>& ltype) const override;
  void encode(DexOutputIdx* dodx, std::vector<uint8_t>& encdata) override;

  DexType* type() const { return static_cast<DexType*>(m_val.m_value_ptr); }
  void set_type(DexType* type) { m_val.m_value_ptr = type; }
  std::string show() const override;
  std::string show_deobfuscated() const override;

  std::unique_ptr<DexEncodedValue> clone() const override {
    return std::unique_ptr<DexEncodedValue>(new DexEncodedValueType(*this));
  }
};

class DexEncodedValueField : public DexEncodedValuePtr {
 public:
  DexEncodedValueField(DexEncodedValueTypes type, DexFieldRef* field)
      : DexEncodedValuePtr(type, field) {}

  void gather_fields(std::vector<DexFieldRef*>& lfield) const override;
  void encode(DexOutputIdx* dodx, std::vector<uint8_t>& encdata) override;

  DexFieldRef* field() const {
    return static_cast<DexFieldRef*>(m_val.m_value_ptr);
  }
  void set_field(DexFieldRef* field) { m_val.m_value_ptr = field; }
  std::string show() const override;
  std::string show_deobfuscated() const override;

  std::unique_ptr<DexEncodedValue> clone() const override {
    return std::unique_ptr<DexEncodedValue>(new DexEncodedValueField(*this));
  }
};

class DexEncodedValueMethod : public DexEncodedValuePtr {
 public:
  explicit DexEncodedValueMethod(DexMethodRef* method)
      : DexEncodedValuePtr(DEVT_METHOD, method) {}

  void gather_methods(std::vector<DexMethodRef*>& lmethod) const override;
  void encode(DexOutputIdx* dodx, std::vector<uint8_t>& encdata) override;

  DexMethodRef* method() const {
    return static_cast<DexMethodRef*>(m_val.m_value_ptr);
  }
  void set_method(DexMethodRef* method) { m_val.m_value_ptr = method; }
  std::string show() const override;
  std::string show_deobfuscated() const override;

  std::unique_ptr<DexEncodedValue> clone() const override {
    return std::unique_ptr<DexEncodedValue>(new DexEncodedValueMethod(*this));
  }
};

class DexEncodedValueMethodType : public DexEncodedValuePtr {
 public:
  explicit DexEncodedValueMethodType(DexProto* proto)
      : DexEncodedValuePtr(DEVT_METHOD_TYPE, proto) {}

  void gather_strings(std::vector<const DexString*>& lstring) const override;
  void gather_types(std::vector<const DexType*>& ltype) const override;
  void gather_protos(std::vector<DexProto*>& lproto) const override;
  void encode(DexOutputIdx* dodx, std::vector<uint8_t>& encdata) override;

  DexProto* proto() const { return static_cast<DexProto*>(m_val.m_value_ptr); }
  void set_proto(DexProto* proto) { m_val.m_value_ptr = proto; }
  std::string show() const override;
  std::string show_deobfuscated() const override;

  std::unique_ptr<DexEncodedValue> clone() const override {
    return std::unique_ptr<DexEncodedValue>(
        new DexEncodedValueMethodType(*this));
  }
};

class DexEncodedValueMethodHandle : public DexEncodedValuePtr {
 public:
  explicit DexEncodedValueMethodHandle(DexMethodHandle* methodhandle)
      : DexEncodedValuePtr(DEVT_METHOD_HANDLE, methodhandle) {}

  void gather_fields(std::vector<DexFieldRef*>& lfield) const override;
  void gather_methods(std::vector<DexMethodRef*>& lmethod) const override;
  void gather_methodhandles(
      std::vector<DexMethodHandle*>& lhandles) const override;
  void encode(DexOutputIdx* dodx, std::vector<uint8_t>& encdata) override;

  DexMethodHandle* methodhandle() const {
    return static_cast<DexMethodHandle*>(m_val.m_value_ptr);
  }
  void set_methodhandle(DexMethodHandle* methodhandle) {
    m_val.m_value_ptr = methodhandle;
  }
  std::string show() const override;
  std::string show_deobfuscated() const override;

  std::unique_ptr<DexEncodedValue> clone() const override {
    return std::unique_ptr<DexEncodedValue>(
        new DexEncodedValueMethodHandle(*this));
  }
};

// NOTE: Different from the other values, this one owns the given vector.
class DexEncodedValueArray : public DexEncodedValue {
  bool m_static_val;

 public:
  using DexEncodedValue::operator==; // Inherit all parent ops
  using Storage = std::vector<std::unique_ptr<DexEncodedValue>>;

  /*
   * Static values are encoded without a DEVT_ARRAY header byte
   * so we differentiate that here.
   */
  explicit DexEncodedValueArray(Storage* evalues, bool static_val = false)
      : DexEncodedValue(DEVT_ARRAY, evalues), m_static_val(static_val) {}
  ~DexEncodedValueArray() override {
    delete static_cast<Storage*>(m_val.m_value_ptr);
  }

  // May not copy or assign, as the element is owned.
  DexEncodedValueArray(const DexEncodedValueArray&) = delete;
  DexEncodedValueArray& operator=(const DexEncodedValueArray&) = delete;

  // May move.
  DexEncodedValueArray(DexEncodedValueArray&& rhs) noexcept
      : DexEncodedValue(DEVT_ARRAY, rhs.m_val.m_value_ptr),
        m_static_val(rhs.m_static_val) {
    rhs.m_val.m_value_ptr = nullptr;
  }
  DexEncodedValueArray& operator=(DexEncodedValueArray&& rhs) noexcept {
    if (this == &rhs) {
      return *this;
    }
    delete static_cast<Storage*>(m_val.m_value_ptr);
    m_val.m_value_ptr = rhs.m_val.m_value_ptr;
    m_static_val = rhs.m_static_val;
    rhs.m_val.m_value_ptr = nullptr;
    return *this;
  }

  std::vector<std::unique_ptr<DexEncodedValue>>* evalues() const {
    return static_cast<Storage*>(m_val.m_value_ptr);
  }
  bool is_static_val() const { return m_static_val; }

  void gather_types(std::vector<const DexType*>& ltype) const override;
  void gather_fields(std::vector<DexFieldRef*>& lfield) const override;
  void gather_methods(std::vector<DexMethodRef*>& lmethod) const override;
  void gather_strings(std::vector<const DexString*>& lstring) const override;
  void gather_methodhandles(
      std::vector<DexMethodHandle*>& lmethodhandle) const override;
  void gather_protos(std::vector<DexProto*>& lproto) const override;
  void encode(DexOutputIdx* dodx, std::vector<uint8_t>& encdata) override;

  std::string show() const override;
  std::string show_deobfuscated() const override;

  bool operator==(const DexEncodedValueArray& that) const {
    if (evalues()->size() != that.evalues()->size()) {
      return false;
    }
    auto it = that.evalues()->begin();
    for (const auto& elem : *evalues()) {
      if (*elem != **it) {
        return false;
      }
      it = std::next(it);
    }
    return m_evtype == that.m_evtype && m_static_val == that.m_static_val;
  }

  size_t hash_value() const override {
    size_t seed = boost::hash<uint8_t>()(m_evtype);
    boost::hash_combine(seed, m_static_val);
    for (const auto& elem : *evalues()) {
      boost::hash_combine(seed, *elem);
    }
    return seed;
  }

  std::unique_ptr<DexEncodedValue> clone() const override {
    // Need to copy the array, if any.
    Storage* evalues_copy;
    if (m_val.m_value_ptr == nullptr) {
      evalues_copy = nullptr;
    } else {
      auto* old = static_cast<Storage*>(m_val.m_value_ptr);
      evalues_copy = new Storage();
      evalues_copy->reserve(old->size());
      for (auto& orig : *old) {
        evalues_copy->emplace_back(orig->clone());
      }
    }
    return std::unique_ptr<DexEncodedValue>(
        new DexEncodedValueArray(evalues_copy, m_static_val));
  }
};

/* For loading static values */
std::unique_ptr<DexEncodedValueArray> get_encoded_value_array(
    DexIdx* idx, const uint8_t*& encdata);

/*
 * These are not "full blown" annotations, they are
 * key/value pairs of encoded values.  They inherit
 * visibility from the referrer.  Preserving the odd
 * naming from the spec.  In practice, these are the
 * InnerClass annotations things like access flags
 * or defining method/class.
 */
class DexAnnotationElement final {
 public:
  DexAnnotationElement(const DexString* s, std::unique_ptr<DexEncodedValue> ev)
      : string(s), encoded_value(std::move(ev)) {}

  DexAnnotationElement(const DexAnnotationElement&) = delete;
  DexAnnotationElement& operator=(const DexAnnotationElement&) = delete;

  DexAnnotationElement(DexAnnotationElement&& other) noexcept
      : string(other.string), encoded_value(std::move(other.encoded_value)) {}
  DexAnnotationElement& operator=(DexAnnotationElement&& other) noexcept {
    string = other.string;
    encoded_value = std::move(other.encoded_value);
    return *this;
  }

  DexAnnotationElement clone() const {
    return DexAnnotationElement(string, encoded_value->clone());
  }

  const DexString* string;
  std::unique_ptr<DexEncodedValue> encoded_value;
};

using EncodedAnnotations = std::vector<DexAnnotationElement>;

std::string show(const EncodedAnnotations*);
std::string show_deobfuscated(const EncodedAnnotations*);

std::string show(const EncodedAnnotations&);
std::string show_deobfuscated(const EncodedAnnotations&);

class DexEncodedValueAnnotation : public DexEncodedValue {
  DexType* m_type;
  EncodedAnnotations m_annotations;

 public:
  DexEncodedValueAnnotation(DexType* type, EncodedAnnotations annotations)
      : DexEncodedValue(DEVT_ANNOTATION),
        m_type(type),
        m_annotations(std::move(annotations)) {}

  DexType* type() const { return m_type; }
  void set_type(DexType* type) { m_type = type; }
  const EncodedAnnotations& annotations() const { return m_annotations; }

  void gather_types(std::vector<const DexType*>& ltype) const override;
  void gather_fields(std::vector<DexFieldRef*>& lfield) const override;
  void gather_methods(std::vector<DexMethodRef*>& lmethod) const override;
  void gather_strings(std::vector<const DexString*>& lstring) const override;
  void gather_methodhandles(
      std::vector<DexMethodHandle*>& lmethodhandle) const override;
  void gather_protos(std::vector<DexProto*>& lproto) const override;
  void encode(DexOutputIdx* dodx, std::vector<uint8_t>& encdata) override;

  std::string show() const override;
  std::string show_deobfuscated() const override;

  std::unique_ptr<DexEncodedValue> clone() const override {
    EncodedAnnotations copy;
    std::transform(m_annotations.begin(),
                   m_annotations.end(),
                   std::back_inserter(copy),
                   [](const auto& a) { return a.clone(); });
    return std::make_unique<DexEncodedValueAnnotation>(m_type, std::move(copy));
  }
};

class DexAnnotation : public Gatherable {
  EncodedAnnotations m_anno_elems;
  DexType* m_type;
  DexAnnotationVisibility m_viz;

 public:
  DexAnnotation(DexType* type, DexAnnotationVisibility viz)
      : m_type(type), m_viz(viz) {}

  DexAnnotation(const DexAnnotation&) = delete;
  DexAnnotation(DexAnnotation&&) = default;

  static std::unique_ptr<DexAnnotation> get_annotation(DexIdx* idx,
                                                       uint32_t anno_off);
  void gather_types(std::vector<const DexType*>& ltype) const override;
  void gather_fields(std::vector<DexFieldRef*>& lfield) const override;
  void gather_methods(std::vector<DexMethodRef*>& lmethod) const override;
  void gather_strings(std::vector<const DexString*>& lstring) const override;
  void gather_methodhandles(
      std::vector<DexMethodHandle*>& lmethodhandle) const override;
  void gather_protos(std::vector<DexProto*>& lproto) const override;

  const EncodedAnnotations& anno_elems() const { return m_anno_elems; }
  void set_type(DexType* type) { m_type = type; }
  DexType* type() const { return m_type; }
  DexAnnotationVisibility viz() const { return m_viz; }
  bool runtime_visible() const { return m_viz == DAV_RUNTIME; }
  bool build_visible() const { return m_viz == DAV_BUILD; }
  bool system_visible() const { return m_viz == DAV_SYSTEM; }

  void vencode(DexOutputIdx* dodx, std::vector<uint8_t>& bytes);
  void add_element(const char* key, std::unique_ptr<DexEncodedValue> value);
  void add_element(DexAnnotationElement elem);

  DexAnnotation clone() const {
    EncodedAnnotations copy;
    std::transform(m_anno_elems.begin(),
                   m_anno_elems.end(),
                   std::back_inserter(copy),
                   [](const auto& a) { return a.clone(); });
    return DexAnnotation(std::move(copy), m_type, m_viz);
  }

 private:
  DexAnnotation(EncodedAnnotations anno_elems,
                DexType* type,
                DexAnnotationVisibility viz)
      : m_anno_elems(std::move(anno_elems)), m_type(type), m_viz(viz) {}
};

class DexAnnotationSet : public Gatherable {
  std::vector<std::unique_ptr<DexAnnotation>> m_annotations;

 public:
  DexAnnotationSet() = default;
  DexAnnotationSet(const DexAnnotationSet& that) {
    for (const auto& anno : that.m_annotations) {
      m_annotations.emplace_back(new DexAnnotation(anno->clone()));
    }
  }

  void gather_types(std::vector<const DexType*>& ltype) const override;
  void gather_fields(std::vector<DexFieldRef*>& lfield) const override;
  void gather_methods(std::vector<DexMethodRef*>& lmethod) const override;
  void gather_strings(std::vector<const DexString*>& lstring) const override;
  void gather_methodhandles(
      std::vector<DexMethodHandle*>& lmethodhandle) const override;
  void gather_protos(std::vector<DexProto*>& lproto) const override;

  static std::unique_ptr<DexAnnotationSet> get_annotation_set(
      DexIdx* idx, uint32_t aset_off);
  unsigned long size() const { return m_annotations.size(); }
  void viz_counts(unsigned long& cntanno, unsigned long& cntviz) {
    cntanno = m_annotations.size();
    cntviz = 0;
    for (auto const& da : m_annotations) {
      if (da->runtime_visible()) {
        cntviz++;
      }
    }
  }

  /**
   * Add in annotation missing from other annotation set.
   */
  void combine_with(const DexAnnotationSet& other);

  const std::vector<std::unique_ptr<DexAnnotation>>& get_annotations() const {
    return m_annotations;
  }
  std::vector<std::unique_ptr<DexAnnotation>>& get_annotations() {
    return m_annotations;
  }
  void add_annotation(std::unique_ptr<DexAnnotation> anno) {
    m_annotations.emplace_back(std::move(anno));
  }
  void vencode(DexOutputIdx* dodx,
               std::vector<uint32_t>& asetout,
               UnorderedMap<DexAnnotation*, uint32_t>& annoout);
  void gather_annotations(std::vector<DexAnnotation*>& alist);
};

using ParamAnnotations = std::map<int, std::unique_ptr<DexAnnotationSet>>;
using DexFieldAnnotations =
    std::vector<std::pair<DexFieldRef*, DexAnnotationSet*>>;
using DexMethodAnnotations =
    std::vector<std::pair<DexMethod*, DexAnnotationSet*>>;
using DexMethodParamAnnotations =
    std::vector<std::pair<DexMethod*, ParamAnnotations*>>;

class DexAnnotationDirectory {
  double m_viz;
  DexAnnotationSet* m_class;
  std::unique_ptr<DexFieldAnnotations> m_field;
  std::unique_ptr<DexMethodAnnotations> m_method;
  std::unique_ptr<DexMethodParamAnnotations> m_method_param;
  int m_aset_size;
  int m_xref_size;
  int m_anno_count;
  int m_aset_count;
  int m_xref_count;
  void calc_internals();

 public:
  DexAnnotationDirectory(DexAnnotationSet* c,
                         std::unique_ptr<DexFieldAnnotations> f,
                         std::unique_ptr<DexMethodAnnotations> m,
                         std::unique_ptr<DexMethodParamAnnotations> mp)
      : m_class(c),
        m_field(std::move(f)),
        m_method(std::move(m)),
        m_method_param(std::move(mp)),
        m_aset_size(0),
        m_xref_size(0),
        m_anno_count(0),
        m_aset_count(0),
        m_xref_count(0) {
    calc_internals();
  }

  double viz_score() const { return m_viz; }

  /* Encoded sizes */
  int aset_size() { return m_aset_size; }
  int xref_size() { return m_xref_size; }

  int annodir_size() {
    int size = 4 * sizeof(uint32_t);
    if (m_field) {
      size += static_cast<int>(m_field->size() * 2 * sizeof(uint32_t));
    }
    if (m_method) {
      size += static_cast<int>(m_method->size() * 2 * sizeof(uint32_t));
    }
    if (m_method_param) {
      size += static_cast<int>(m_method_param->size() * 2 * sizeof(uint32_t));
    }
    return size;
  }

  int aset_count() { return m_aset_count; }
  int anno_count() { return m_anno_count; }
  int xref_count() { return m_xref_count; }
  void sort_members();
  void gather_annotations(std::vector<DexAnnotation*>& alist);
  void gather_asets(std::vector<DexAnnotationSet*>& aset);
  void gather_xrefs(std::vector<ParamAnnotations*>& xrefs);
  void vencode(DexOutputIdx* dodx,
               std::vector<uint32_t>& annodirout,
               UnorderedMap<ParamAnnotations*, uint32_t>& xrefmap,
               UnorderedMap<DexAnnotationSet*, uint32_t>& asetmap);

  friend std::string show(const DexAnnotationDirectory*);
};

uint64_t read_evarg(const uint8_t*& encdata,
                    uint8_t evarg,
                    bool sign_extend = false);

void type_encoder(std::vector<uint8_t>& encdata, uint8_t type, uint64_t val);
void type_encoder_signext(std::vector<uint8_t>& encdata,
                          uint8_t type,
                          uint64_t val);
void type_encoder_fp(std::vector<uint8_t>& encdata, uint8_t type, uint64_t val);
