/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "DexClass.h"

#include "ControlFlow.h"
#include "CppUtil.h"
#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexAccess.h"
#include "DexAnnotation.h"
#include "DexDebugInstruction.h"
#include "DexDefs.h"
#include "DexEncoding.h"
#include "DexIdx.h"
#include "DexInstruction.h"
#include "DexMemberRefs.h"
#include "DexOutput.h"
#include "DexPosition.h"
#include "DexSignaturePolymorphicRef.h"
#include "DexUtil.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "RedexContext.h"
#include "Show.h"
#include "SourceDebugExtension.h"
#include "StringBuilder.h"
#include "Trace.h"
#include "TypeUtil.h"
#include "Util.h"
#include "Warning.h"

#include <algorithm>
#include <memory>
#include <unordered_set>

#define INSTANTIATE1(METHOD, TYPE)                       \
  template void METHOD(std::vector<TYPE>&) const;        \
  template void METHOD(std::unordered_set<TYPE>&) const; \
  template void METHOD(UnorderedSet<TYPE>&) const;

#define INSTANTIATE(METHOD, TYPE)                              \
  template void METHOD(std::vector<TYPE>&) const;              \
  template void METHOD(std::unordered_set<TYPE>&) const;       \
  template void METHOD(UnorderedSet<TYPE>&) const;             \
  template void METHOD(std::vector<const TYPE>&) const;        \
  template void METHOD(std::unordered_set<const TYPE>&) const; \
  template void METHOD(UnorderedSet<const TYPE>&) const;

#define INSTANTIATE2(METHOD, TYPE, OTYPE)                             \
  template void METHOD(std::vector<TYPE>&, OTYPE) const;              \
  template void METHOD(std::unordered_set<TYPE>&, OTYPE) const;       \
  template void METHOD(UnorderedSet<TYPE>&, OTYPE) const;             \
  template void METHOD(std::vector<const TYPE>&, OTYPE) const;        \
  template void METHOD(std::unordered_set<const TYPE>&, OTYPE) const; \
  template void METHOD(UnorderedSet<const TYPE>&, OTYPE) const;

namespace {

std::optional<source_debug_extension::SourceDebugExtension>
get_source_debug_extension(const DexAnnotationSet* annotations) {
  if (annotations == nullptr) {
    return std::nullopt;
  }
  constexpr std::string_view type_name =
      "Ldalvik/annotation/SourceDebugExtension;";
  for (const auto& annotation_owner : annotations->get_annotations()) {
    const auto* annotation = annotation_owner.get();
    if (annotation == nullptr) {
      continue;
    }
    const auto* annotation_type = annotation->type();
    if (annotation_type == nullptr) {
      continue;
    }
    const auto* annotation_type_name = annotation_type->get_name();
    if (annotation_type_name == nullptr ||
        annotation_type_name->str() != type_name) {
      continue;
    }
    for (const auto& element : annotation->anno_elems()) {
      const auto* element_name = element.string;
      const auto* element_value = element.encoded_value.get();
      if (element_name == nullptr || element_value == nullptr ||
          element_name->str() != "value" ||
          element_value->evtype() != DEVT_STRING) {
        continue;
      }
      const auto* encoded_value =
          dynamic_cast<const DexEncodedValueString*>(element_value);
      if (encoded_value == nullptr) {
        return std::nullopt;
      }
      const auto* value = encoded_value->string();
      if (value == nullptr) {
        return std::nullopt;
      }
      return source_debug_extension::SourceDebugExtension::parse(value->str());
    }
    return std::nullopt;
  }
  return std::nullopt;
}

template <typename C, typename T>
struct InsertionHelper;

template <typename T>
struct InsertionHelper<std::vector<T>, T> {
  void append(std::vector<T>& c, T t) { c.emplace_back(std::move(t)); }
  template <typename It>
  void append_all(std::vector<T>& c, It first, It last) {
    c.insert(c.end(), first, last);
  }
};

template <typename T>
struct InsertionHelper<std::unordered_set<T>, T> {
  void append(std::unordered_set<T>& c, T t) { c.emplace(std::move(t)); }
  template <typename It>
  void append_all(std::unordered_set<T>& c, It first, It last) {
    c.insert(first, last);
  }
};

template <typename T>
struct InsertionHelper<UnorderedSet<T>, T> {
  void append(UnorderedSet<T>& c, T t) { c.emplace(std::move(t)); }
  template <typename It>
  void append_all(UnorderedSet<T>& c, It first, It last) {
    c.insert(first, last);
  }
};

template <typename C>
void c_append(C& c, typename C::value_type t) {
  InsertionHelper<C, typename C::value_type>().append(c, t);
}
template <typename C, typename It>
void c_append_all(C& c, It first, It last) {
  InsertionHelper<C, typename C::value_type>().append_all(c, first, last);
}

} // namespace

namespace {
// Why? get_deobfuscated_name and show_deobfuscated are not enough. deobfuscated
// names could be empty, e.g., when Redex-created methods. So we need a better
// job. And proto and type are still obfuscated in some cases. We also implement
// show_deobfuscated for DexProto.
std::string build_fully_deobfuscated_name(const DexMethod* m) {
  string_builders::StaticStringBuilder<5> b;
  DexClass* cls = type_class(m->get_class());
  if (cls == nullptr) {
    // Well, just for safety.
    b << "<null>";
  } else {
    b << std::string(cls->get_deobfuscated_name_or_empty().empty()
                         ? cls->get_name()->str()
                         : cls->get_deobfuscated_name_or_empty());
  }

  b << "." << m->get_simple_deobfuscated_name() << ":"
    << show_deobfuscated(m->get_proto());
  return b.str();
}

// Return just the name of the method/field.
template <typename T>
std::string get_simple_deobf_name(const T* ref) {
  const auto& full_name = ref->get_deobfuscated_name_or_empty();
  if (full_name.empty()) {
    // This comes up for redex-created methods/fields.
    return ref->str_copy();
  }
  auto dot_pos = full_name.find('.');
  auto colon_pos = full_name.find(':');
  if (dot_pos == std::string::npos || colon_pos == std::string::npos) {
    return str_copy(full_name);
  }
  return str_copy(full_name.substr(dot_pos + 1, colon_pos - dot_pos - 1));
}
} // namespace

static_assert(sizeof(DexString) == sizeof(DexStringRepr));

const std::string DexString::EMPTY;

const DexString* DexString::make_string(std::string_view nstr) {
  return g_redex->make_string(nstr);
}

// Return an existing DexString or nullptr if one does not exist.
const DexString* DexString::get_string(std::string_view s) {
  return g_redex->get_string(s);
}

int32_t DexString::java_hashcode() const {
  return java_hashcode_of_utf8_string(c_str());
}

uint32_t DexString::get_entry_size() const {
  uint32_t len = uleb128_encoding_size(m_repr.utfsize);
  len += size();
  len++; // NULL byte
  return len;
}

void DexString::encode(uint8_t* output) const {
  output = write_uleb128(output, m_repr.utfsize);
  strcpy((char*)output, c_str());
}

namespace dexstrings::details {

bool compare_dexstrings_slowpath(const DexString* a, const DexString* b) {
  const char* sa = a->c_str();
  const char* sb = b->c_str();
  /* Equivalence test first, so we don't worry about walking
   * off the end.
   */
  if (strcmp(sa, sb) == 0) {
    return false;
  }
  if (strlen(sa) == 0) {
    return true;
  }
  if (strlen(sb) == 0) {
    return false;
  }
  while (true) {
    uint32_t cpa = mutf8_next_code_point(sa);
    uint32_t cpb = mutf8_next_code_point(sb);
    if (cpa == cpb) {
      if (*sa == '\0') {
        return true;
      }
      if (*sb == '\0') {
        return false;
      }
      continue;
    }
    return (cpa < cpb);
  }
}

} // namespace dexstrings::details

int DexTypeList::encode(DexOutputIdx* dodx, uint32_t* output) const {
  uint16_t* typep = (uint16_t*)(output + 1);
  *output = (uint32_t)m_list.size();
  for (auto const& type : m_list) {
    *typep++ = dodx->typeidx(type);
  }
  return (int)(((uint8_t*)typep) - (uint8_t*)output);
}

DexTypeList* DexTypeList::push_front(const DexType* t) const {
  ContainerType new_list;
  new_list.push_back(t);
  new_list.insert(new_list.end(), m_list.begin(), m_list.end());
  return make_type_list(std::move(new_list));
}

DexTypeList* DexTypeList::pop_front() const {
  redex_assert(!m_list.empty());
  ContainerType new_list{m_list.begin() + 1, m_list.end()};
  return make_type_list(std::move(new_list));
}
DexTypeList* DexTypeList::pop_front(size_t n) const {
  redex_assert(m_list.size() >= n);
  ContainerType new_list{m_list.begin() + static_cast<ptrdiff_t>(n),
                         m_list.end()};
  return make_type_list(std::move(new_list));
}

DexTypeList* DexTypeList::pop_back(size_t n) const {
  redex_assert(m_list.size() >= n);
  ContainerType new_list{m_list.begin(),
                         m_list.end() - static_cast<ptrdiff_t>(n)};
  return make_type_list(std::move(new_list));
}

DexTypeList* DexTypeList::push_back(const DexType* t) const {
  ContainerType new_list{m_list};
  new_list.push_back(t);
  return make_type_list(std::move(new_list));
}
DexTypeList* DexTypeList::push_back(
    const std::vector<const DexType*>& t) const {
  ContainerType new_list{m_list};
  new_list.insert(new_list.end(), t.begin(), t.end());
  return make_type_list(std::move(new_list));
}

DexTypeList* DexTypeList::replace_head(const DexType* new_head) const {
  redex_assert(!m_list.empty());
  ContainerType new_list{m_list};
  new_list[0] = new_head;
  return make_type_list(std::move(new_list));
}

DexTypeList* DexTypeList::make_type_list(ContainerType&& p) {
  return g_redex->make_type_list(std::move(p));
}

DexTypeList* DexTypeList::get_type_list(const ContainerType& p) {
  return g_redex->get_type_list(p);
}

DexField::DexField(DexType* container, const DexString* name, DexType* type)
    : DexFieldRef(container, name, type),
      m_access(static_cast<DexAccessFlags>(0)),
      m_value(nullptr) {}
DexField::~DexField() = default; // For forwarding.

DexField* DexFieldRef::make_concrete(DexAccessFlags access_flags) {
  return make_concrete(access_flags, nullptr);
}

DexField* DexFieldRef::make_concrete(DexAccessFlags access_flags,
                                     std::unique_ptr<DexEncodedValue> v) {
  // FIXME assert if already concrete
  auto* that = dynamic_cast<DexField*>(this);
  that->m_access = access_flags;
  that->m_concrete = true;
  if (is_static(access_flags)) {
    that->set_value(std::move(v));
  } else {
    always_assert(v == nullptr);
  }
  return that;
}

void DexFieldRef::change(const DexFieldSpec& ref, bool rename_on_collision) {
  g_redex->mutate_field(this, ref, rename_on_collision);
}

void DexFieldRef::erase_field(DexFieldRef* f) {
  return g_redex->erase_field(f);
}

dex_member_refs::FieldDescriptorTokens DexFieldRef::get_descriptor_tokens()
    const {
  dex_member_refs::FieldDescriptorTokens res;
  res.cls = get_class()->str();
  res.name = get_name()->str();
  res.type = get_type()->str();
  return res;
}

void DexFieldRef::delete_field_DO_NOT_USE(DexFieldRef* field) {
  erase_field(field);
  delete dynamic_cast<DexField*>(field);
}

DexFieldRef* DexField::get_field(
    const dex_member_refs::FieldDescriptorTokens& fdt) {
  auto* cls = DexType::get_type(fdt.cls);
  const auto* name = DexString::get_string(fdt.name);
  auto* type = DexType::get_type(fdt.type);
  return DexField::get_field(cls, name, type);
}

DexFieldRef* DexField::get_field(std::string_view full_descriptor) {
  return get_field(dex_member_refs::parse_field(full_descriptor));
}

DexFieldRef* DexField::make_field(const DexType* container,
                                  const DexString* name,
                                  const DexType* type) {
  return g_redex->make_field(container, name, type);
}

DexFieldRef* DexField::get_field(const DexType* container,
                                 const DexString* name,
                                 const DexType* type) {
  return g_redex->get_field(container, name, type);
}

DexFieldRef* DexField::make_field(std::string_view full_descriptor) {
  auto fdt = dex_member_refs::parse_field(full_descriptor);
  auto* cls = DexType::make_type(fdt.cls);
  const auto* name = DexString::make_string(fdt.name);
  auto* type = DexType::make_type(fdt.type);
  return DexField::make_field(cls, name, type);
}

void DexField::set_external() {
  always_assert_log(!m_concrete, "Unexpected concrete field %s\n",
                    self_show().c_str());
  m_deobfuscated_name = self_show();
  m_external = true;
}

void DexField::set_value(std::unique_ptr<DexEncodedValue> v) {
  always_assert_log(
      m_concrete,
      "Field needs to be concrete to be attached an encoded value.");
  always_assert(is_static(m_access));
  // The last contiguous block of static fields with null values are not
  // represented in the encoded value array. OTOH null-initialized static
  // fields that appear earlier in the static field list have explicit values.
  // Let's standardize things here.
  m_value =
      v != nullptr ? std::move(v) : DexEncodedValue::zero_for_type(get_type());
}

void DexField::clear_annotations() { m_anno.reset(); }

bool DexField::attach_annotation_set(std::unique_ptr<DexAnnotationSet> aset) {
  if (m_concrete && !is_synthetic(get_access())) {
    return false;
  }
  if (m_anno != nullptr) {
    return false;
  }
  m_anno = std::move(aset);
  return true;
}

std::unique_ptr<DexAnnotationSet> DexField::release_annotations() {
  return std::move(m_anno);
}

DexDebugEntry::DexDebugEntry(uint32_t addr,
                             std::unique_ptr<DexDebugInstruction> insn)
    : type(DexDebugEntryType::Instruction), addr(addr), insn(std::move(insn)) {}

DexDebugEntry::DexDebugEntry(uint32_t addr, std::unique_ptr<DexPosition> pos)
    : type(DexDebugEntryType::Position), addr(addr), pos(std::move(pos)) {}

DexDebugEntry::DexDebugEntry(DexDebugEntry&& other) noexcept
    : type(other.type), addr(other.addr) {
  switch (type) {
  case DexDebugEntryType::Position:
    new (&pos) std::unique_ptr<DexPosition>(std::move(other.pos));
    break;
  case DexDebugEntryType::Instruction:
    new (&insn) std::unique_ptr<DexDebugInstruction>(std::move(other.insn));
    break;
  }
}

DexDebugEntry::~DexDebugEntry() {
  switch (type) {
  case DexDebugEntryType::Position:
    pos.~unique_ptr<DexPosition>();
    break;
  case DexDebugEntryType::Instruction:
    insn.~unique_ptr<DexDebugInstruction>();
    break;
  }
}

void DexDebugEntry::gather_strings(
    std::vector<const DexString*>& lstring) const {
  if (type == DexDebugEntryType::Instruction) {
    insn->gather_strings(lstring);
  }
}
void DexDebugEntry::gather_types(std::vector<const DexType*>& ltype) const {
  if (type == DexDebugEntryType::Instruction) {
    insn->gather_types(ltype);
  }
}

/*
 * Evaluate the debug opcodes to figure out their absolute addresses and line
 * numbers.
 */
static std::vector<DexDebugEntry> eval_debug_instructions(
    DexIdx* idx, std::string_view& encdata_ptr, uint32_t absolute_line) {
  std::vector<DexDebugEntry> entries;
  // Likely overallocate and then shrink down in an effort to avoid the
  // resize overhead.
  constexpr size_t kReserveSize = 10000;
  entries.reserve(kReserveSize);

  uint32_t pc = 0;

  while (true) {
    std::unique_ptr<DexDebugInstruction> opcode(
        DexDebugInstruction::make_instruction(idx, encdata_ptr));
    if (opcode == nullptr) {
      break;
    }
    auto op = opcode->opcode();
    switch (op) {
    case DBG_ADVANCE_LINE: {
      absolute_line += opcode->value();
      continue;
    }
    case DBG_END_LOCAL:
    case DBG_RESTART_LOCAL:
    case DBG_START_LOCAL:
    case DBG_START_LOCAL_EXTENDED:
    case DBG_SET_FILE:
    case DBG_END_SEQUENCE:
    case DBG_SET_PROLOGUE_END:
    case DBG_SET_EPILOGUE_BEGIN: {
      entries.emplace_back(pc, std::move(opcode));
      break;
    }
    case DBG_ADVANCE_PC: {
      pc += opcode->uvalue();
      continue;
    }
    default: {
      uint8_t adjustment = op - DBG_FIRST_SPECIAL;
      absolute_line += DBG_LINE_BASE + (adjustment % DBG_LINE_RANGE);
      pc += adjustment / DBG_LINE_RANGE;
      entries.emplace_back(
          pc, std::make_unique<DexPosition>(
                  DexString::make_string("UnknownSource"), absolute_line));
      break;
    }
    }
  }

  entries.shrink_to_fit();
  return entries;
}

DexDebugItem::DexDebugItem(DexIdx* idx, uint32_t offset)
    : m_source_checksum(idx->get_checksum()), m_source_offset(offset) {
  const uint8_t* encdata_ptr = idx->get_uleb_data(offset);
  always_assert_type_log(encdata_ptr < idx->end(), INVALID_DEX, "Dex overflow");
  std::string_view encdata{(const char*)encdata_ptr,
                           (size_t)(idx->end() - encdata_ptr)};
  const auto orig_size = encdata.size();
  uint32_t line_start = read_uleb128_checked<redex::DexAssert>(encdata);
  uint32_t paramcount = read_uleb128_checked<redex::DexAssert>(encdata);
  while ((paramcount--) != 0u) {
    // We keep the parameter string name for printing debug info in our
    // checkers. However, we do not write them out into the output. We emit
    // matching number of nulls as method arguments at the end.
    const DexString* param_name = decode_noindexable_string(idx, encdata);
    // param_name can be nullptr !!!
    m_param_names.push_back(param_name);
  }
  m_dbg_entries = eval_debug_instructions(idx, encdata, line_start);
  m_on_disk_size = orig_size - encdata.size();
}

uint32_t DexDebugItem::get_line_start() const {
  for (const auto& entry : m_dbg_entries) {
    switch (entry.type) {
    case DexDebugEntryType::Position: {
      return entry.pos->line;
    default:
      break;
    }
    }
  }
  return 0;
}

DexDebugItem::DexDebugItem(const DexDebugItem& that)
    : m_param_names(that.m_param_names) {
  UnorderedMap<DexPosition*, DexPosition*> pos_map;
  m_dbg_entries.reserve(that.m_dbg_entries.size());
  for (const auto& entry : that.m_dbg_entries) {
    switch (entry.type) {
    case DexDebugEntryType::Position: {
      auto pos = std::make_unique<DexPosition>(*entry.pos);
      pos_map[entry.pos.get()] = pos.get();
      pos->parent = pos_map[pos->parent];
      m_dbg_entries.emplace_back(entry.addr, std::move(pos));
      break;
    }
    case DexDebugEntryType::Instruction:
      m_dbg_entries.emplace_back(entry.addr, entry.insn->clone());
      break;
    }
  }
}

std::unique_ptr<DexDebugItem> DexDebugItem::get_dex_debug(DexIdx* idx,
                                                          uint32_t offset) {
  if (offset == 0) {
    return nullptr;
  }
  return std::unique_ptr<DexDebugItem>(new DexDebugItem(idx, offset));
}

/*
 * Convert DexDebugEntries into debug opcodes.
 */
std::vector<std::unique_ptr<DexDebugInstruction>> generate_debug_instructions(
    DexDebugItem* debugitem,
    PositionMapper* pos_mapper,
    uint32_t* line_start,
    std::vector<DebugLineItem>* line_info,
    uint32_t line_addin) {
  std::vector<std::unique_ptr<DexDebugInstruction>> dbgops;
  uint32_t prev_addr = 0;
  std::optional<uint32_t> prev_line;
  auto& entries = debugitem->get_entries();

  for (auto it = entries.begin(); it != entries.end(); ++it) {
    // find all entries that belong to the same address, and group them by type
    auto addr = it->addr;
    std::vector<DexPosition*> positions;
    std::vector<DexDebugInstruction*> insns;
    for (; it != entries.end() && it->addr == addr; ++it) {
      switch (it->type) {
      case DexDebugEntryType::Position:
        always_assert_log(it->pos->file != nullptr,
                          "Position file has nullptr");
        positions.push_back(it->pos.get());
        break;
      case DexDebugEntryType::Instruction:
        insns.push_back(it->insn.get());
        break;
      }
    }
    --it;
    auto addr_delta = addr - prev_addr;
    prev_addr = addr;

    for (auto* pos : positions) {
      pos_mapper->register_position(pos);
    }
    // only emit the last position entry for a given address
    if (!positions.empty()) {
      auto line_base = pos_mapper->position_to_line(positions.back());
      auto line = line_base | line_addin;
      line_info->emplace_back(it->addr, line_base);
      int32_t line_delta;
      if (prev_line) {
        line_delta = static_cast<int32_t>(line - *prev_line);
      } else {
        *line_start = line;
        line_delta = 0;
      }
      prev_line = line;
      if (line_delta < DBG_LINE_BASE ||
          line_delta >= (DBG_LINE_RANGE + DBG_LINE_BASE)) {
        dbgops.emplace_back(
            new DexDebugInstruction(DBG_ADVANCE_LINE, line_delta));
        line_delta = 0;
      }
      auto special = (line_delta - DBG_LINE_BASE) +
                     (addr_delta * DBG_LINE_RANGE) + DBG_FIRST_SPECIAL;
      if ((special & ~0xff) != 0u) {
        dbgops.emplace_back(
            new DexDebugInstruction(DBG_ADVANCE_PC, addr_delta));
        special = line_delta - DBG_LINE_BASE + DBG_FIRST_SPECIAL;
      }
      dbgops.emplace_back(
          new DexDebugInstruction(static_cast<DexDebugItemOpcode>(special)));
      line_delta = 0;
      addr_delta = 0;
    }

    for (auto* insn : insns) {
      if (addr_delta != 0) {
        dbgops.emplace_back(
            new DexDebugInstruction(DBG_ADVANCE_PC, addr_delta));
        addr_delta = 0;
      }
      dbgops.emplace_back(insn->clone());
    }
  }
  return dbgops;
}

size_t DexDebugItem::max_encoded_size(
    uint32_t num_params,
    const std::vector<std::unique_ptr<DexDebugInstruction>>& dbgops) {
  // line_start + num_params + one uleb128p1 per parameter, then the ops, then
  // DBG_END_SEQUENCE.
  size_t size = 2 * kMaxLeb128Size + (size_t)num_params * kMaxLeb128Size + 1;
  for (const auto& dbgop : dbgops) {
    size += dbgop->max_encoded_size();
  }
  return size;
}

int DexDebugItem::encode(
    DexOutputIdx* dodx,
    uint8_t* output,
    uint32_t line_start,
    uint32_t num_params,
    const std::vector<std::unique_ptr<DexDebugInstruction>>& dbgops) {
  uint8_t* encdata = output;
  encdata = write_uleb128(encdata, line_start);
  encdata = write_uleb128(encdata, num_params);
  for (uint32_t i = 0; i < num_params; ++i) {
    encdata = write_uleb128p1(encdata, DEX_NO_INDEX);
  }
  for (const auto& dbgop : dbgops) {
    dbgop->encode(dodx, encdata);
  }
  encdata = write_uleb128(encdata, DBG_END_SEQUENCE);
  return (int)(encdata - output);
}

void DexDebugItem::bind_positions(
    DexMethod* method,
    const DexString* file,
    const source_debug_extension::SourceDebugExtension*
        source_debug_extension) {
  const auto* method_str = DexString::make_string(show(method));
  if (source_debug_extension == nullptr) {
    for (auto& entry : m_dbg_entries) {
      if (entry.type != DexDebugEntryType::Position) {
        continue;
      }
      if (file != nullptr) {
        entry.pos->bind(method_str, file);
      } else {
        entry.pos->bind(method_str);
      }
    }
    return;
  }

  std::vector<DexDebugEntry> entries;
  entries.reserve(m_dbg_entries.size() * 2);
  UnorderedMap<
      const DexPosition*,
      UnorderedMap<const DexString*, UnorderedMap<uint32_t, DexPosition*>>>
      caller_positions;
  for (auto& entry : m_dbg_entries) {
    switch (entry.type) {
    case DexDebugEntryType::Position: {
      auto position = std::move(entry.pos);
      if (position == nullptr) {
        not_reached();
      }
      if (file != nullptr) {
        position->bind(method_str, file);
      } else {
        position->bind(method_str);
      }
      auto mapped = source_debug_extension->map(position->line);
      if (mapped) {
        DexPosition* parent = nullptr;
        for (auto caller = mapped->callers.rbegin();
             caller != mapped->callers.rend();
             ++caller) {
          const auto* caller_file = DexString::make_string(caller->file);
          auto& positions_by_line = caller_positions[parent][caller_file];
          auto [it, inserted] =
              positions_by_line.emplace(caller->line, nullptr);
          if (inserted) {
            auto caller_position = std::make_unique<DexPosition>(
                method_str, caller_file, caller->line);
            caller_position->parent = parent;
            it->second = caller_position.get();
            entries.emplace_back(entry.addr, std::move(caller_position));
          }
          parent = it->second;
        }
        position->parent = parent;
        position->file = DexString::make_string(mapped->source.file);
        position->line = mapped->source.line;
        caller_positions[parent][position->file].try_emplace(position->line,
                                                             position.get());
      }
      entries.emplace_back(entry.addr, std::move(position));
      break;
    }
    case DexDebugEntryType::Instruction:
      entries.emplace_back(entry.addr, std::move(entry.insn));
      break;
    }
  }
  m_dbg_entries = std::move(entries);
}

void DexDebugItem::gather_types(std::vector<const DexType*>& ltype) const {
  for (const auto& entry : m_dbg_entries) {
    entry.gather_types(ltype);
  }
}

void DexDebugItem::gather_strings(
    std::vector<const DexString*>& lstring) const {
  for (const auto& entry : m_dbg_entries) {
    entry.gather_strings(lstring);
  }
}

DexInvokeId::DexInvokeId(bool invoke_interface,
                         DexMethodRef* method,
                         DexPosition* position,
                         SourceBlock* src_block)
    : invoke_interface(invoke_interface),
      method(method),
      position(position != nullptr ? std::make_unique<DexPosition>(*position)
                                   : nullptr),
      src_block(src_block != nullptr ? std::make_unique<SourceBlock>(*src_block)
                                     : nullptr) {}

DexInvokeId::~DexInvokeId() {}

DexCode::DexCode(const DexCode& that)
    : m_registers_size(that.m_registers_size),
      m_ins_size(that.m_ins_size),
      m_outs_size(that.m_outs_size),
      m_insns(that.m_insns ? std::make_optional<std::vector<DexInstruction*>>()
                           : std::nullopt) {
  if (that.m_insns) {
    m_insns->reserve(that.m_insns->size());
    for (const auto& insn : *that.m_insns) {
      m_insns->emplace_back(insn->clone());
    }
  }
  m_tries.reserve(that.m_tries.size());
  for (const auto& try_ : that.m_tries) {
    m_tries.emplace_back(new DexTryItem(*try_));
  }
  if (that.m_dbg) {
    m_dbg.reset(new DexDebugItem(*that.m_dbg));
  }
}

DexCode::~DexCode() {
  if (m_insns) {
    for (auto const& op : *m_insns) {
      delete op;
    }
  }
}

std::unique_ptr<DexCode> DexCode::get_dex_code(DexIdx* idx, uint32_t offset) {
  if (offset == 0) {
    return std::unique_ptr<DexCode>();
  }
  always_assert_type_log(offset <= idx->get_file_size() - sizeof(dex_code_item),
                         INVALID_DEX, "Dex overflow");
  always_assert_type_log(offset % 4 == 0, INVALID_DEX, "Alignment violation");
  const dex_code_item* code = idx->get_data<dex_code_item>(offset);
  std::unique_ptr<DexCode> dc(new DexCode());
  dc->m_registers_size = code->registers_size;
  dc->m_ins_size = code->ins_size;
  dc->m_outs_size = code->outs_size;
  dc->m_insns = std::vector<DexInstruction*>();
  const uint16_t* cdata = (const uint16_t*)(code + 1);
  uint32_t tries = code->tries_size;
  if (code->insns_size != 0u) {
    always_assert_type_log(
        code->insns_size * sizeof(uint16_t) <=
            idx->get_file_size() - offset - sizeof(dex_code_item),
        INVALID_DEX, "Dex overflow");
    // The spec does not restrict this, but this improves things like fuzzing.
    always_assert_type_log(code->insns_size <= 1000000, INVALID_DEX,
                           "Too many instructions");

    // On average there seem to be about two code units per instruction
    dc->m_insns->reserve(code->insns_size / 2);
    const uint16_t* end = cdata + code->insns_size;

    while (cdata < end) {
      DexInstruction* dop = DexInstruction::make_instruction(idx, &cdata, end);
      always_assert_type_log(dop != nullptr, INVALID_DEX,
                             "Failed to parse method at offset 0x%08x", offset);
      dc->m_insns->push_back(dop);
    }
    /*
     * Padding, see dex-spec.
     * Per my memory, there are dex-files where the padding is
     * implemented not according to spec.  Just FYI in case
     * something weird happens in the future.
     */
    if (((code->insns_size & 1) != 0u) && (tries != 0u)) {
      cdata++;
    }
  }

  if (tries != 0u) {
    const dex_tries_item* dti = (const dex_tries_item*)cdata;
    always_assert_type_log(dti <= dti + tries, INVALID_DEX, "Dex overflow");
    always_assert_type_log((uint8_t*)(dti + tries) <= idx->end(), INVALID_DEX,
                           "Dex overflow");
    const uint8_t* handlers = (const uint8_t*)(dti + tries);
    for (uint32_t i = 0; i < tries; i++) {
      DexTryItem* dextry = new DexTryItem(dti[i].start_addr, dti[i].insn_count);
      auto handler = [&]() {
        auto offset = dti[i].handler_off;
        always_assert_type_log(handlers + offset < idx->end(), INVALID_DEX,
                               "Dex overflow");
        return std::string_view((const char*)handlers + offset,
                                idx->end() - handlers - offset);
      }();
      int32_t count = read_sleb128_checked<redex::DexAssert>(handler);
      bool has_catchall = false;
      if (count <= 0) {
        count = -count;
        has_catchall = true;
      }
      while ((count--) != 0) {
        uint32_t tidx = read_uleb128_checked<redex::DexAssert>(handler);
        uint32_t hoff = read_uleb128_checked<redex::DexAssert>(handler);
        DexType* dt = idx->get_nullable_typeidx(tidx);
        dextry->m_catches.emplace_back(dt, hoff);
      }
      if (has_catchall) {
        auto hoff = read_uleb128_checked<redex::DexAssert>(handler);
        dextry->m_catches.emplace_back(nullptr, hoff);
      }
      dc->m_tries.emplace_back(dextry);
    }
  }
  dc->m_dbg = DexDebugItem::get_dex_debug(idx, code->debug_info_off);
  return dc;
}

size_t DexCode::max_encoded_size() const {
  // The header, then every instruction -- unfiltered, so that DexOpcodeData's
  // payload (m_data_count + 1 code units) is included exactly as `encode`
  // writes it.
  size_t size = sizeof(dex_code_item);
  for (auto const& opc : get_instructions()) {
    size += opc->size() * sizeof(uint16_t);
  }
  if (m_tries.empty()) {
    return size;
  }
  // The uint16 pad that 4-aligns the tries table, the table itself, then the
  // handler stream: one uleb128 for the distinct-handler count, and per try a
  // sleb128 count followed by a type index and an address per catch.
  size += sizeof(uint16_t);
  size += m_tries.size() * sizeof(dex_tries_item);
  size += kMaxLeb128Size;
  for (auto const& dextry : m_tries) {
    size += kMaxLeb128Size + dextry->m_catches.size() * 2 * kMaxLeb128Size;
  }
  return size;
}

int DexCode::encode(DexOutputIdx* dodx, uint32_t* output) {
  dex_code_item* code = (dex_code_item*)output;
  code->registers_size = m_registers_size;
  code->ins_size = m_ins_size;
  code->outs_size = m_outs_size;
  code->tries_size = 0;
  /* Debug info is added later */
  code->debug_info_off = 0;
  uint16_t* insns = reinterpret_cast<uint16_t*>(code + 1);
  for (auto const& opc : get_instructions()) {
    opc->encode(dodx, insns);
  }
  code->insns_size =
      static_cast<uint32_t>(insns - reinterpret_cast<uint16_t*>(code + 1));
  if (m_tries.empty()) {
    return static_cast<int>((code->insns_size * sizeof(uint16_t)) +
                            sizeof(dex_code_item));
  }
  /*
   * Now the tries..., obscenely messy encoding :(
   * Pad tries to uint32_t
   */
  if ((code->insns_size & 1) != 0u) {
    insns++;
  }
  int tries = code->tries_size = static_cast<int>(m_tries.size());
  dex_tries_item* dti = reinterpret_cast<dex_tries_item*>(insns);
  uint8_t* handler_base = reinterpret_cast<uint8_t*>(dti + tries);
  uint8_t* hemit = handler_base;
  std::unordered_set<DexCatches, boost::hash<DexCatches>> catches_set;
  for (auto& dextry : m_tries) {
    catches_set.insert(dextry->m_catches);
  }
  hemit = write_uleb128(hemit, static_cast<uint32_t>(catches_set.size()));
  int tryno = 0;
  UnorderedMap<DexCatches, uint32_t, boost::hash<DexCatches>> catches_map;
  for (auto it = m_tries.begin(); it != m_tries.end(); ++it, ++tryno) {
    auto& dextry = *it;
    always_assert(dextry->m_start_addr < code->insns_size);
    dti[tryno].start_addr = dextry->m_start_addr;
    always_assert(dextry->m_start_addr + dextry->m_insn_count <=
                  code->insns_size);
    dti[tryno].insn_count = dextry->m_insn_count;
    auto [cm_it, inserted] = catches_map.emplace(
        dextry->m_catches, static_cast<uint32_t>(hemit - handler_base));
    if (inserted) {
      size_t catchcount = dextry->m_catches.size();
      bool has_catchall = dextry->m_catches.back().first == nullptr;
      if (has_catchall) {
        // -1 because the catch-all address is last (without an address)
        catchcount = -(catchcount - 1);
      }
      hemit = write_sleb128(hemit, (int32_t)catchcount);
      for (auto const& cit : dextry->m_catches) {
        auto* type = cit.first;
        auto catch_addr = cit.second;
        if (type != nullptr) {
          // Assumption: The only catch-all is at the end of the list
          hemit = write_uleb128(hemit, dodx->typeidx(type));
        }
        always_assert(catch_addr < code->insns_size);
        hemit = write_uleb128(hemit, catch_addr);
      }
    }
    dti[tryno].handler_off = cm_it->second;
  }
  return static_cast<int>(hemit - reinterpret_cast<uint8_t*>(output));
}

DexMethod::DexMethod(DexType* type, const DexString* name, DexProto* proto)
    : DexMethodRef(type, name, proto) {
  m_virtual = false;
  m_anno = nullptr;
  m_dex_code = nullptr;
  m_code = nullptr;
  m_access = static_cast<DexAccessFlags>(0);
}

DexMethod::~DexMethod() = default;

void DexMethodRef::delete_method(DexMethodRef* m) {
  erase_method(m);
  if (m->is_def()) {
    m->as_def()->make_non_concrete();
  }
  g_redex->leak_method(m);
}

std::string DexMethod::get_fully_deobfuscated_name() const {
  if (m_deobfuscated_name != nullptr &&
      get_deobfuscated_name().str() == show(this)) {
    return get_deobfuscated_name().str_copy();
  }
  return build_fully_deobfuscated_name(this);
}

void DexMethod::set_code(std::unique_ptr<IRCode> code) {
  m_code = std::move(code);
}

void DexMethod::balloon() {
  redex_assert(m_code == nullptr);
  m_code = IRCode::for_method(this);
  m_dex_code.reset();
}

void DexMethod::sync() {
  redex_assert(m_dex_code == nullptr);
  m_dex_code = m_code->sync(this);
  m_code.reset();
}

size_t hash_value(const DexMethodSpec& r) {
  size_t seed = boost::hash<DexType*>()(r.cls);
  boost::hash_combine(seed, r.name);
  boost::hash_combine(seed, r.proto);
  return seed;
}

DexMethodRef* DexMethod::make_method(const DexType* type,
                                     const DexString* name,
                                     const DexProto* proto) {
  return g_redex->make_method(type, name, proto);
}

DexMethodRef* DexMethod::make_method(const DexMethodSpec& spec) {
  return g_redex->make_method(spec.cls, spec.name, spec.proto);
}

DexMethod* DexMethod::make_method_downcast(const DexType* type,
                                           const DexString* name,
                                           const DexProto* proto) {
  return dynamic_cast<DexMethod*>(g_redex->make_method(type, name, proto));
}

DexMethod* DexMethod::make_method_downcast(const DexMethodSpec& spec) {
  return dynamic_cast<DexMethod*>(
      g_redex->make_method(spec.cls, spec.name, spec.proto));
}

DexMethod* DexMethod::make_method_from(DexMethod* that,
                                       DexType* target_cls,
                                       const DexString* name) {
  auto* m = dynamic_cast<DexMethod*>(
      DexMethod::make_method(target_cls, name, that->get_proto()));
  redex_assert(m != that);
  if (that->m_anno) {
    m->m_anno = std::make_unique<DexAnnotationSet>(*that->m_anno);
  }

  if (!is_abstract(that)) {
    always_assert_log(that->get_code() != nullptr, "%s", vshow(that).c_str());
    m->set_code(std::make_unique<IRCode>(*that->get_code()));
  } else {
    redex_assert(CONSTP(that)->get_code() == nullptr);
  }

  m->m_access = that->m_access;
  m->m_concrete = that->m_concrete;
  m->m_virtual = that->m_virtual;
  m->m_external = that->m_external;
  if (that->m_param_anno != nullptr) {
    if (m->m_param_anno == nullptr) {
      m->m_param_anno = std::make_unique<ParamAnnotations>();
    }
    for (auto& pair : *that->m_param_anno) {
      // note: DexAnnotation's copy ctor only does a shallow copy
      m->m_param_anno->emplace(pair.first, new DexAnnotationSet(*pair.second));
    }
  }

  return m;
}

DexMethodRef* DexMethod::get_method(const DexType* type,
                                    const DexString* name,
                                    const DexProto* proto) {
  return g_redex->get_method(type, name, proto);
}

DexMethodRef* DexMethod::get_method(const DexMethodSpec& spec) {
  return g_redex->get_method(spec.cls, spec.name, spec.proto);
}

DexMethod* DexMethod::make_full_method_from(DexMethod* that,
                                            DexType* target_cls,
                                            const DexString* name) {
  auto* m = make_method_from(that, target_cls, name);
  m->rstate = that->rstate;
  return m;
}

DexMethodRef* DexMethod::get_method(
    const dex_member_refs::MethodDescriptorTokens& mdt) {
  auto* cls = DexType::get_type(mdt.cls);
  const auto* name = DexString::get_string(mdt.name);
  DexTypeList::ContainerType args;
  for (const auto& arg_str : mdt.args) {
    args.push_back(DexType::get_type(arg_str));
  }
  auto* dtl = DexTypeList::get_type_list(args);
  if (dtl == nullptr) {
    return nullptr;
  }
  auto* rtype = DexType::get_type(mdt.rtype);
  if (rtype == nullptr) {
    return nullptr;
  }
  return DexMethod::get_method(cls, name, DexProto::get_proto(rtype, dtl));
}

template <bool kCheckFormat>
DexMethodRef* DexMethod::get_method(std::string_view full_descriptor) {
  return get_method(
      dex_member_refs::parse_method<kCheckFormat>(full_descriptor));
}
template DexMethodRef* DexMethod::get_method<false>(std::string_view);
template DexMethodRef* DexMethod::get_method<true>(std::string_view);

namespace {

DexProto* make_proto_from_tokens(const std::vector<std::string_view>& arg_strs,
                                 std::string_view rtype_str) {
  DexTypeList::ContainerType args;
  for (auto arg_str : arg_strs) {
    args.push_back(DexType::make_type(arg_str));
  }
  return DexProto::make_proto(DexType::make_type(rtype_str),
                              DexTypeList::make_type_list(std::move(args)));
}

} // namespace

DexProto* DexProto::make_proto(std::string_view descriptor) {
  auto pdt = dex_member_refs::parse_proto(descriptor);
  return make_proto_from_tokens(pdt.args, pdt.rtype);
}

DexMethodRef* DexMethod::make_method(std::string_view full_descriptor) {
  auto mdt = dex_member_refs::parse_method(full_descriptor);
  auto* cls = DexType::make_type(mdt.cls);
  const auto* name = DexString::make_string(mdt.name);
  return DexMethod::make_method(cls, name,
                                make_proto_from_tokens(mdt.args, mdt.rtype));
}

DexMethodRef* DexMethod::make_method(
    const std::string& class_type,
    const std::string& name,
    std::initializer_list<std::string> arg_types,
    const std::string& return_type) {
  DexTypeList::ContainerType dex_types;
  for (const std::string& type_str : arg_types) {
    dex_types.push_back(DexType::make_type(type_str));
  }
  return DexMethod::make_method(
      DexType::make_type(class_type),
      DexString::make_string(name),
      DexProto::make_proto(DexType::make_type(return_type),
                           DexTypeList::make_type_list(std::move(dex_types))));
}

void DexMethod::combine_annotations_with(DexMethod* other) {
  auto* other_anno_set = other->get_anno_set();
  if (other_anno_set != nullptr) {
    if (m_anno == nullptr) {
      m_anno = std::make_unique<DexAnnotationSet>(*other->m_anno);
    } else {
      m_anno->combine_with(*other->m_anno);
    }
  }
  if (other->m_param_anno != nullptr) {
    if (m_param_anno == nullptr) {
      m_param_anno = std::make_unique<ParamAnnotations>();
    }
    for (auto& pair : *other->m_param_anno) {
      if (m_param_anno->count(pair.first) == 0 ||
          m_param_anno->at(pair.first) == nullptr) {
        m_param_anno->emplace(pair.first, new DexAnnotationSet(*pair.second));
      } else {
        (*m_param_anno)[pair.first]->combine_with(*pair.second);
      }
    }
  }
}

void DexMethod::clear_annotations() { m_anno.reset(); }

std::unique_ptr<ParamAnnotations> DexMethod::release_param_anno() {
  return std::move(m_param_anno);
}

bool DexMethod::attach_annotation_set(std::unique_ptr<DexAnnotationSet> aset) {
  if (m_concrete && !is_synthetic(get_access())) {
    return false;
  }
  if (m_anno != nullptr) {
    return false;
  }
  m_anno = std::move(aset);
  return true;
}
void DexMethod::attach_param_annotation_set(
    int paramno, std::unique_ptr<DexAnnotationSet> aset) {
  always_assert_type_log(!m_concrete || is_synthetic(get_access()),
                         RedexError::BAD_ANNOTATION, "method %s is concrete\n",
                         self_show().c_str());
  always_assert_type_log(
      m_param_anno == nullptr || m_param_anno->count(paramno) == 0,
      RedexError::BAD_ANNOTATION, "param %d annotation to method %s exists\n",
      paramno, self_show().c_str());
  if (m_param_anno == nullptr) {
    m_param_anno = std::make_unique<ParamAnnotations>();
  }
  (*m_param_anno)[paramno] = std::move(aset);
}

std::unique_ptr<DexAnnotationSet> DexMethod::release_annotations() {
  return std::move(m_anno);
}

DexLocation::DexLocation(std::string store_name, std::string file_name)
    : m_store_name(std::move(store_name)), m_file_name(std::move(file_name)) {}

const DexLocation* DexLocation::make_location(std::string_view store_name,
                                              std::string_view file_name) {
  return g_redex->make_location(store_name, file_name);
}

const DexLocation* DexLocation::get_location(std::string_view store_name,
                                             std::string_view file_name) {
  return g_redex->get_location(store_name, file_name);
}

void DexClass::set_deobfuscated_name(std::string_view name) {
  // If the class has an old deobfuscated_name which is not equal to
  // `show(self)`, erase the name mapping from the global type map.
  if (kInsertDeobfuscatedNameLinks && m_deobfuscated_name != nullptr) {
    if (m_deobfuscated_name != m_self->get_name()) {
      g_redex->remove_type_name(m_deobfuscated_name);
    }
  }
  m_deobfuscated_name = DexString::make_string(name);
  if (!kInsertDeobfuscatedNameLinks) {
    return;
  }
  if (m_deobfuscated_name == m_self->get_name()) {
    return;
  }
  auto* existing_type = g_redex->get_type(m_deobfuscated_name);
  if (existing_type != nullptr) {
    TRACE(DC, 5,
          "Unable to alias type '%s' to deobfuscated name '%s' because type "
          "'%s' already exists.\n",
          m_self->c_str(), m_deobfuscated_name->c_str(),
          existing_type->c_str());
    return;
  }
  g_redex->alias_type_name(m_self, m_deobfuscated_name);
}

void DexClass::set_deobfuscated_name(const DexString* name) {
  // If the class has an old deobfuscated_name which is not equal to
  // `show(self)`, erase the name mapping from the global type map.
  if (kInsertDeobfuscatedNameLinks && m_deobfuscated_name != nullptr) {
    if (m_deobfuscated_name != m_self->get_name()) {
      g_redex->remove_type_name(m_deobfuscated_name);
    }
  }
  m_deobfuscated_name = name;
  if (!kInsertDeobfuscatedNameLinks) {
    return;
  }
  if (m_deobfuscated_name == m_self->get_name()) {
    return;
  }
  auto* existing_type = g_redex->get_type(m_deobfuscated_name);
  if (existing_type != nullptr) {
    TRACE(DC, 5,
          "Unable to alias type '%s' to deobfuscated name '%s' because type "
          "'%s' already exists.\n",
          m_self->c_str(), m_deobfuscated_name->c_str(),
          existing_type->c_str());
    return;
  }
  g_redex->alias_type_name(m_self, m_deobfuscated_name);
}
void DexClass::set_deobfuscated_name(const DexString& name) {
  set_deobfuscated_name(&name);
}

void DexClass::set_external() {
  m_deobfuscated_name = DexString::make_string(self_show());
  m_external = true;
}

void DexClass::remove_method(const DexMethod* m) {
  auto& meths = m->is_virtual() ? m_vmethods : m_dmethods;
  auto it = std::find(meths.begin(), meths.end(), m);
  DEBUG_ONLY bool erased = false;
  if (it != meths.end()) {
    erased = true;
    meths.erase(it);
  }
  redex_assert(erased);
}

void DexMethod::become_virtual() {
  redex_assert(!m_virtual);
  auto* cls = type_class(m_spec.cls);
  redex_assert(!cls->is_external());
  cls->remove_method(this);
  m_virtual = true;
  auto& vmethods = cls->get_vmethods();
  insert_sorted(vmethods, this, compare_dexmethods);
}

DexMethod* DexMethodRef::make_concrete(DexAccessFlags access,
                                       std::unique_ptr<DexCode> dc,
                                       bool is_virtual) {
  auto* that = dynamic_cast<DexMethod*>(this);
  that->m_access = access;
  that->m_dex_code = std::move(dc);
  that->m_concrete = true;
  that->m_virtual = is_virtual;
  return that;
}

DexMethod* DexMethodRef::make_concrete(DexAccessFlags access,
                                       std::unique_ptr<IRCode> dc,
                                       bool is_virtual) {
  auto* that = dynamic_cast<DexMethod*>(this);
  that->m_access = access;
  that->m_code = std::move(dc);
  that->m_concrete = true;
  that->m_virtual = is_virtual;
  return that;
}

DexMethod* DexMethodRef::make_concrete(DexAccessFlags access, bool is_virtual) {
  return make_concrete(access, std::unique_ptr<IRCode>(nullptr), is_virtual);
}

void DexMethodRef::change(const DexMethodSpec& ref, bool rename_on_collision) {
  g_redex->mutate_method(this, ref, rename_on_collision);
}

void DexMethod::make_non_concrete() {
  m_access = static_cast<DexAccessFlags>(0);
  m_concrete = false;
  m_code.reset();
  m_virtual = false;
  m_param_anno.reset();
  m_anno.reset();
}

void DexMethod::set_deobfuscated_name(const std::string& name) {
  // If the method has an old deobfuscated_name which is not equal to the name,
  // erase the mapping using the old (and now invalid) deobfuscated_name from
  // the global type map.
  if (kInsertDeobfuscatedNameLinks && m_deobfuscated_name != nullptr &&
      !m_deobfuscated_name->str().empty()) {
    if (m_deobfuscated_name != this->get_name()) {
      g_redex->erase_method(this->get_class(), m_deobfuscated_name,
                            this->get_proto());
    }
  }
  m_deobfuscated_name = DexString::make_string(name);
  if (!kInsertDeobfuscatedNameLinks) {
    return;
  }
  if (m_deobfuscated_name == this->get_name()) {
    return;
  }
  auto* existing_method = g_redex->get_method(
      this->get_class(), m_deobfuscated_name, this->get_proto());
  if (existing_method != nullptr) {
    TRACE(DC, 5,
          "Unable to alias method '%s' to deobfuscated name '%s' because "
          "method '%s' already exists.\n ",
          this->c_str(), m_deobfuscated_name->c_str(),
          existing_method->c_str());
    return;
  }
  g_redex->alias_method_name(this, m_deobfuscated_name);
}

std::string DexMethod::get_simple_deobfuscated_name() const {
  return get_simple_deobf_name(this);
}

/*
 * See class_data_item in Dex spec.
 */
void DexClass::load_class_data_item(
    DexIdx* idx,
    uint32_t cdi_off,
    std::unique_ptr<DexEncodedValueArray> svalues) {
  if (cdi_off == 0) {
    return;
  }
  const uint8_t* encd = idx->get_uleb_data(cdi_off);
  uint32_t sfield_count = idx->read_uleb128_checked(&encd);
  uint32_t ifield_count = idx->read_uleb128_checked(&encd);
  always_assert_type_log(static_cast<uint64_t>(sfield_count) + ifield_count <=
                             idx->get_field_ids_size(),
                         INVALID_DEX,
                         "class_data_item field count exceeds dex field ids");
  uint32_t dmethod_count = idx->read_uleb128_checked(&encd);
  uint32_t vmethod_count = idx->read_uleb128_checked(&encd);
  always_assert_type_log(static_cast<uint64_t>(dmethod_count) + vmethod_count <=
                             idx->get_method_ids_size(),
                         INVALID_DEX,
                         "class_data_item method count exceeds dex method ids");
  uint32_t ndex = 0;

  std::vector<std::unique_ptr<DexEncodedValue>> empty{};
  std::vector<std::unique_ptr<DexEncodedValue>>& used =
      (svalues == nullptr || svalues->evalues() == nullptr)
          ? empty
          : *svalues->evalues();
  auto it = used.begin();

  m_sfields.reserve(sfield_count);
  for (uint32_t i = 0; i < sfield_count; i++) {
    ndex += idx->read_uleb128_checked(&encd);
    auto access_flags = (DexAccessFlags)idx->read_uleb128_checked(&encd);
    always_assert_type_log(is_static(access_flags), INVALID_DEX,
                           "Static field not marked static");
    DexField* df = dynamic_cast<DexField*>(idx->get_fieldidx(ndex));
    always_assert_type_log(df->get_class() == get_type(), INVALID_DEX,
                           "Referenced field does not belong to class");
    std::unique_ptr<DexEncodedValue> ev = nullptr;
    if (it != used.end()) {
      ev = std::move(*it);
      ++it;
    }
    // We are gonna own the element.
    df->make_concrete(access_flags, std::move(ev));
    m_sfields.push_back(df);
  }
  ndex = 0;
  m_ifields.reserve(ifield_count);
  for (uint32_t i = 0; i < ifield_count; i++) {
    ndex += idx->read_uleb128_checked(&encd);
    auto access_flags = (DexAccessFlags)idx->read_uleb128_checked(&encd);
    always_assert_type_log(!is_static(access_flags), INVALID_DEX,
                           "Non-Static field marked static");
    DexField* df = dynamic_cast<DexField*>(idx->get_fieldidx(ndex));
    always_assert_type_log(df->get_class() == get_type(), INVALID_DEX,
                           "Referenced field does not belong to class");
    df->make_concrete(access_flags);
    m_ifields.push_back(df);
  }

  std::unordered_set<DexMethod*> method_pointer_cache;
  method_pointer_cache.reserve(dmethod_count + vmethod_count);
  auto source_debug_extension = get_source_debug_extension(m_anno.get());

  auto process_method = [this, &encd, &idx, &method_pointer_cache,
                         &source_debug_extension](uint32_t& ndex,
                                                  bool is_virtual) {
    ndex += idx->read_uleb128_checked(&encd);
    auto access_flags = (DexAccessFlags)idx->read_uleb128_checked(&encd);
    uint32_t code_off = idx->read_uleb128_checked(&encd);
    // Find method in method index, returns same pointer for same method.
    DexMethod* dm = dynamic_cast<DexMethod*>(idx->get_methodidx(ndex));
    always_assert_type_log(dm->get_class() == get_type(), INVALID_DEX,
                           "Referenced method does not belong to class");
    std::unique_ptr<DexCode> dc = DexCode::get_dex_code(idx, code_off);
    if (dc && (dc->get_debug_item() != nullptr)) {
      dc->get_debug_item()->bind_positions(
          dm, m_source_file,
          source_debug_extension ? &*source_debug_extension : nullptr);
    }
    dm->make_concrete(access_flags, std::move(dc), is_virtual);

    const auto& pair = method_pointer_cache.insert(dm);
    bool insertion_happened = pair.second;
    always_assert_type_log(insertion_happened, RedexError::DUPLICATE_METHODS,
                           "Found duplicate methods in the same class. %s",
                           SHOW(dm));

    return dm;
  };

  m_dmethods.reserve(dmethod_count);
  ndex = 0;
  for (uint32_t i = 0; i < dmethod_count; i++) {
    DexMethod* dm = process_method(ndex, false);
    m_dmethods.push_back(dm);
  }
  m_vmethods.reserve(vmethod_count);
  ndex = 0;
  for (uint32_t i = 0; i < vmethod_count; i++) {
    DexMethod* dm = process_method(ndex, true);
    m_vmethods.push_back(dm);
  }
}

std::unique_ptr<IRCode> DexMethod::release_code() { return std::move(m_code); }

std::vector<DexMethod*> DexClass::get_all_methods() const {
  std::vector<DexMethod*> all_methods(m_vmethods.begin(), m_vmethods.end());
  all_methods.insert(all_methods.end(), m_dmethods.begin(), m_dmethods.end());
  return all_methods;
}

void DexClass::add_method(DexMethod* m) {
  always_assert_log(m->is_concrete() || m->is_external(),
                    "Method %s must be concrete",
                    SHOW(m));
  always_assert(m->get_class() == get_type());
  if (m->is_virtual()) {
    insert_sorted(m_vmethods, m, compare_dexmethods);
  } else {
    insert_sorted(m_dmethods, m, compare_dexmethods);
  }
}

std::vector<DexField*> DexClass::get_all_fields() const {
  std::vector<DexField*> all_fields(m_ifields.begin(), m_ifields.end());
  all_fields.insert(all_fields.end(), m_sfields.begin(), m_sfields.end());
  return all_fields;
}

void DexClass::add_field(DexField* f) {
  always_assert_log(f->is_concrete() || f->is_external(),
                    "Field %s must be concrete",
                    SHOW(f));
  always_assert(f->get_class() == get_type());
  bool is_static = (f->get_access() & DexAccessFlags::ACC_STATIC) != 0u;
  if (is_static) {
    insert_sorted(m_sfields, f, compare_dexfields);
  } else {
    insert_sorted(m_ifields, f, compare_dexfields);
  }
}

void DexClass::remove_field(const DexField* f) {
  bool is_static = (f->get_access() & DexAccessFlags::ACC_STATIC) != 0u;
  auto& fields = is_static ? m_sfields : m_ifields;
  DEBUG_ONLY bool erase = false;
  auto it = std::find(fields.begin(), fields.end(), f);
  if (it != fields.end()) {
    erase = true;
    fields.erase(it);
  }
  redex_assert(erase);
}

void DexClass::remove_field_definition(DexField* f) {
  remove_field(f);
  f->m_concrete = false;
}

void DexClass::sort_fields() {
  auto& sfields = this->get_sfields();
  auto& ifields = this->get_ifields();
  std::sort(sfields.begin(), sfields.end(), compare_dexfields);
  std::sort(ifields.begin(), ifields.end(), compare_dexfields);
}

void DexClass::sort_methods() {
  auto& vmeths = this->get_vmethods();
  auto& dmeths = this->get_dmethods();
  std::sort(vmeths.begin(), vmeths.end(), compare_dexmethods);
  std::sort(dmeths.begin(), dmeths.end(), compare_dexmethods);
}

DexField* DexClass::find_ifield(const char* name,
                                const DexType* field_type) const {
  for (auto* const f : m_ifields) {
    if (std::strcmp(f->c_str(), name) == 0 && f->get_type() == field_type) {
      return f;
    }
  }

  return nullptr;
}

DexField* DexClass::find_sfield(const char* name,
                                const DexType* field_type) const {
  for (auto* const f : m_sfields) {
    if (std::strcmp(f->c_str(), name) == 0 && f->get_type() == field_type) {
      return f;
    }
  }

  return nullptr;
}

bool DexClass::has_class_data() const {
  return !m_vmethods.empty() || !m_dmethods.empty() || !m_ifields.empty() ||
         !m_sfields.empty();
}

size_t DexClass::max_encoded_size() const {
  return 4 * kMaxLeb128Size +
         (m_sfields.size() + m_ifields.size()) * 2 * kMaxLeb128Size +
         (m_dmethods.size() + m_vmethods.size()) * 3 * kMaxLeb128Size;
}

int DexClass::encode(DexOutputIdx* dodx,
                     dexcode_to_offset& dco,
                     uint8_t* output) {
  if (m_sfields.empty() && m_ifields.empty() && m_dmethods.empty() &&
      m_vmethods.empty()) {
    opt_warn(PURE_ABSTRACT_CLASS,
             "'%s' super '%s' flags 0x%08x\n",
             m_self->get_name()->c_str(),
             m_super_class->get_name()->c_str(),
             m_access_flags);
  }

  sort_fields();
  sort_methods();

  uint8_t* encdata = output;
  encdata = write_uleb128(encdata, (uint32_t)m_sfields.size());
  encdata = write_uleb128(encdata, (uint32_t)m_ifields.size());
  encdata = write_uleb128(encdata, (uint32_t)m_dmethods.size());
  encdata = write_uleb128(encdata, (uint32_t)m_vmethods.size());
  uint32_t idxbase;
  idxbase = 0;
  for (auto const& f : m_sfields) {
    uint32_t idx = dodx->fieldidx(f);
    encdata = write_uleb128(encdata, idx - idxbase);
    idxbase = idx;
    encdata = write_uleb128(encdata, f->get_access());
  }
  idxbase = 0;
  for (auto const& f : m_ifields) {
    uint32_t idx = dodx->fieldidx(f);
    encdata = write_uleb128(encdata, idx - idxbase);
    idxbase = idx;
    encdata = write_uleb128(encdata, f->get_access());
  }
  idxbase = 0;
  for (auto const& m : m_dmethods) {
    uint32_t idx = dodx->methodidx(m);
    always_assert_log(!m->is_virtual(),
                      "Virtual method in dmethod."
                      "\nOffending type: %s"
                      "\nOffending method: %s",
                      SHOW(this),
                      SHOW(m));
    redex_assert(!m->is_virtual());
    encdata = write_uleb128(encdata, idx - idxbase);
    idxbase = idx;
    encdata = write_uleb128(encdata, m->get_access());
    uint32_t code_off = 0;
    if (m->get_dex_code() != nullptr && (dco.count(m->get_dex_code()) != 0u)) {
      code_off = dco[m->get_dex_code()];
    }
    encdata = write_uleb128(encdata, code_off);
  }
  idxbase = 0;
  for (auto const& m : m_vmethods) {
    uint32_t idx = dodx->methodidx(m);
    always_assert_log(m->is_virtual(),
                      "Direct method in vmethod."
                      "\nOffending type: %s"
                      "\nOffending method: %s",
                      SHOW(this),
                      SHOW(m));
    redex_assert(m->is_virtual());
    encdata = write_uleb128(encdata, idx - idxbase);
    idxbase = idx;
    encdata = write_uleb128(encdata, m->get_access());
    uint32_t code_off = 0;
    if (m->get_dex_code() != nullptr && (dco.count(m->get_dex_code()) != 0u)) {
      code_off = dco[m->get_dex_code()];
    }
    encdata = write_uleb128(encdata, code_off);
  }
  return (int)(encdata - output);
}

void DexClass::load_class_annotations(DexIdx* idx, uint32_t anno_off) {
  if (anno_off == 0) {
    return;
  }
  const dex_annotations_directory_item* annodir =
      idx->get_data<dex_annotations_directory_item>(anno_off);
  always_assert_type_log(align_ptr<sizeof(uint32_t)>(annodir) == annodir,
                         INVALID_DEX, "Alignment issue");
  m_anno =
      DexAnnotationSet::get_annotation_set(idx, annodir->class_annotations_off);
  const uint32_t* annodata = (uint32_t*)(annodir + 1);

  auto assert_no_overflow = [&](uint64_t size) {
    const uint64_t file_size = idx->get_file_size();
    always_assert_type_log(size * 2 * sizeof(uint32_t) <= file_size,
                           INVALID_DEX, "Dex overflow");
    always_assert_type_log(idx->end() - size * 2 * sizeof(uint32_t) >=
                               reinterpret_cast<const uint8_t*>(annodata),
                           INVALID_DEX, "Dex overflow");
  };

  assert_no_overflow(annodir->fields_size);
  for (uint32_t i = 0; i < annodir->fields_size; i++) {
    uint32_t fidx = *annodata++;
    uint32_t off = *annodata++;
    DexField* field = dynamic_cast<DexField*>(idx->get_fieldidx(fidx));
    always_assert_type_log(field->get_class() == get_type(), INVALID_DEX,
                           "Wrong field");
    auto aset = DexAnnotationSet::get_annotation_set(idx, off);
    auto res = field->attach_annotation_set(std::move(aset));
    always_assert_type_log(res, INVALID_DEX, "Failed to attach annotation set");
  }

  assert_no_overflow(annodir->methods_size);
  for (uint32_t i = 0; i < annodir->methods_size; i++) {
    uint32_t midx = *annodata++;
    uint32_t off = *annodata++;
    DexMethod* method = dynamic_cast<DexMethod*>(idx->get_methodidx(midx));
    always_assert_type_log(method->get_class() == get_type(), INVALID_DEX,
                           "Wrong method");
    auto aset = DexAnnotationSet::get_annotation_set(idx, off);
    auto res = method->attach_annotation_set(std::move(aset));
    always_assert_type_log(res, INVALID_DEX, "Failed to attach method set");
  }

  assert_no_overflow(annodir->parameters_size);
  for (uint32_t i = 0; i < annodir->parameters_size; i++) {
    uint32_t midx = *annodata++;
    uint32_t xrefoff = *annodata++;
    if (xrefoff != 0) {
      DexMethod* method = dynamic_cast<DexMethod*>(idx->get_methodidx(midx));
      always_assert_type_log(method->get_class() == get_type(), INVALID_DEX,
                             "Wrong method");
      const uint32_t* annoxref = idx->get_uint_data(xrefoff);
      uint32_t count = *annoxref++;
      always_assert_type_log(annoxref <= annoxref + count, INVALID_DEX,
                             "Dex overflow");
      always_assert_type_log(
          reinterpret_cast<const uint8_t*>(annoxref + count) <= idx->end(),
          INVALID_DEX, "Dex overflow");
      for (uint32_t j = 0; j < count; j++) {
        uint32_t off = annoxref[j];
        auto aset = DexAnnotationSet::get_annotation_set(idx, off);
        if (aset != nullptr) {
          method->attach_param_annotation_set(static_cast<int>(j),
                                              std::move(aset));
          redex_assert(CONSTP(method)->get_param_anno());
        }
      }
    }
  }
}

void DexClass::combine_annotations_with(DexAnnotationSet* other) {
  if (other != nullptr) {
    if (m_anno == nullptr) {
      m_anno = std::make_unique<DexAnnotationSet>(*other);
    } else {
      m_anno->combine_with(*other);
    }
  }
}

void DexClass::combine_annotations_with(DexClass* other) {
  combine_annotations_with(other->get_anno_set());
}

bool DexClass::attach_annotation_set(std::unique_ptr<DexAnnotationSet> anno) {
  m_anno = std::move(anno);
  return true;
}

void DexClass::clear_annotations() { m_anno.reset(); }

static std::unique_ptr<DexEncodedValueArray> load_static_values(
    DexIdx* idx, uint32_t sv_off) {
  if (sv_off == 0) {
    return nullptr;
  }
  const uint8_t* encd = idx->get_uleb_data(sv_off);
  return get_encoded_value_array(idx, encd);
}

std::unique_ptr<DexEncodedValueArray> DexClass::get_static_values() {
  std::deque<std::unique_ptr<DexEncodedValue>> deque;
  for (auto it = m_sfields.rbegin(); it != m_sfields.rend(); ++it) {
    auto const& f = *it;
    DexEncodedValue* ev = f->get_static_value();
    if (!ev->is_zero() || !deque.empty()) {
      deque.push_front(ev->clone());
    }
  }
  if (deque.empty()) {
    return nullptr;
  }

  auto aev = std::make_unique<std::vector<std::unique_ptr<DexEncodedValue>>>();
  aev->reserve(deque.size());
  for (auto& d : deque) {
    aev->emplace_back(std::move(d));
  }
  return std::make_unique<DexEncodedValueArray>(aev.release(), true);
}

DexAnnotationDirectory* DexClass::get_annotation_directory() {
  /* First scan to see what types of annotations to scan for if any.
   */
  std::unique_ptr<DexFieldAnnotations> fanno = nullptr;
  std::unique_ptr<DexMethodAnnotations> manno = nullptr;
  std::unique_ptr<DexMethodParamAnnotations> mpanno = nullptr;

  for (auto const& f : m_sfields) {
    if (f->get_anno_set() != nullptr) {
      if (fanno == nullptr) {
        fanno = std::make_unique<DexFieldAnnotations>();
      }
      fanno->push_back(std::make_pair(f, f->get_anno_set()));
    }
  }
  for (auto const& f : m_ifields) {
    if (f->get_anno_set() != nullptr) {
      if (fanno == nullptr) {
        fanno = std::make_unique<DexFieldAnnotations>();
      }
      fanno->push_back(std::make_pair(f, f->get_anno_set()));
    }
  }
  for (auto const& m : m_dmethods) {
    if (m->get_anno_set() != nullptr) {
      if (manno == nullptr) {
        manno = std::make_unique<DexMethodAnnotations>();
      }
      manno->push_back(std::make_pair(m, m->get_anno_set()));
    }
    if (m->get_param_anno() != nullptr) {
      if (mpanno == nullptr) {
        mpanno = std::make_unique<DexMethodParamAnnotations>();
      }
      mpanno->push_back(std::make_pair(m, m->get_param_anno()));
    }
  }
  for (auto const& m : m_vmethods) {
    if (m->get_anno_set() != nullptr) {
      if (manno == nullptr) {
        manno = std::make_unique<DexMethodAnnotations>();
      }
      manno->push_back(std::make_pair(m, m->get_anno_set()));
    }
    if (m->get_param_anno() != nullptr) {
      if (mpanno == nullptr) {
        mpanno = std::make_unique<DexMethodParamAnnotations>();
      }
      mpanno->push_back(std::make_pair(m, m->get_param_anno()));
    }
  }
  if (m_anno || fanno || manno || mpanno) {
    return new DexAnnotationDirectory(m_anno.get(), std::move(fanno),
                                      std::move(manno), std::move(mpanno));
  }
  return nullptr;
}

DexClass* DexClass::create(DexIdx* idx,
                           const dex_class_def* cdef,
                           const DexLocation* location) {
  auto cls = [&]() {
    auto check_type = [](const DexType* type) {
      always_assert_type_log(type != nullptr, INVALID_DEX, "no type");
      always_assert_type_log(type::is_object(type), INVALID_DEX,
                             "Not a reference type: %s", SHOW(type));
      always_assert_type_log(!type::is_array(type), INVALID_DEX,
                             "Must not be array type: %s", SHOW(type));
    };

    auto* self_type = idx->get_typeidx(cdef->typeidx);
    check_type(self_type);

    auto* super_type = idx->get_nullable_typeidx(cdef->super_idx);
    if (super_type == nullptr) {
      always_assert_type_log(self_type == type::java_lang_Object(), INVALID_DEX,
                             "Only Object has super=null");
    } else {
      check_type(super_type);
    }

    auto* interfaces = idx->get_type_list(cdef->interfaces_off);
    if (interfaces != nullptr) {
      for (const auto* intf : *interfaces) {
        check_type(intf);
      }
    }
    const auto* source_file =
        idx->get_nullable_stringidx(cdef->source_file_idx);
    // TODO: Check access_flags.
    auto access_flags = (DexAccessFlags)cdef->access_flags;

    return std::unique_ptr<DexClass>{new DexClass(super_type, self_type,
                                                  interfaces, source_file,
                                                  location, access_flags)};
  }();
  if (g_redex->class_already_loaded(cls.get())) {
    // FIXME: This isn't deterministic. We're keeping whichever class we loaded
    // first, which may not always be from the same dex (if we load them in
    // parallel, for example).
    return nullptr;
  }
  cls->load_class_annotations(idx, cdef->annotations_off);
  auto deva = std::unique_ptr<DexEncodedValueArray>(
      load_static_values(idx, cdef->static_values_off));
  cls->load_class_data_item(idx, cdef->class_data_offset, std::move(deva));
  g_redex->publish_class(cls.get());
  return cls.release();
}

DexClass::DexClass(DexType* type, const DexLocation* location)
    : m_super_class(nullptr),
      m_self(type),
      m_interfaces(DexTypeList::make_type_list({})),
      m_source_file(nullptr),
      m_anno(nullptr),
      m_location(location),
      m_access_flags((DexAccessFlags)0),
      m_external(false),
      m_perf_sensitive(PerfSensitiveGroup::NONE),
      m_dynamically_dead(false) {
  always_assert(type != nullptr);
  always_assert_log(type_class(type) == nullptr,
                    "class already exists for %s\n", type->c_str());
  set_deobfuscated_name(type->get_name());
}

DexClass::DexClass(DexType* super_type,
                   DexType* self_type,
                   DexTypeList* interfaces,
                   const DexString* source_file,
                   const DexLocation* location,
                   DexAccessFlags access_flags)
    : m_super_class(super_type),
      m_self(self_type),
      m_interfaces(interfaces),
      m_source_file(source_file),
      m_anno(nullptr),
      m_location(location),
      m_access_flags(access_flags),
      m_external(false),
      m_perf_sensitive(PerfSensitiveGroup::NONE),
      m_dynamically_dead(false) {}

DexClass::~DexClass() = default; // For forwarding.

template <typename C>
void DexTypeList::gather_types(C& ltype) const {
  c_append_all(ltype, m_list.begin(), m_list.end());
}
INSTANTIATE1(DexTypeList::gather_types, const DexType*)

static const DexString* make_shorty(const DexType* rtype,
                                    const DexTypeList* args) {
  std::string s;
  s.push_back(type::type_shorty(rtype));
  if (args != nullptr) {
    for (const auto* arg : *args) {
      s.push_back(type::type_shorty(arg));
    }
  }
  return DexString::make_string(s);
}

DexProto* DexProto::make_proto(const DexType* rtype,
                               const DexTypeList* args,
                               const DexString* shorty) {
  return g_redex->make_proto(rtype, args, shorty);
}

DexProto* DexProto::make_proto(const DexType* rtype, const DexTypeList* args) {
  const auto* shorty = make_shorty(rtype, args);
  return DexProto::make_proto(rtype, args, shorty);
}

DexProto* DexProto::get_proto(const DexType* rtype, const DexTypeList* args) {
  return g_redex->get_proto(rtype, args);
}

bool DexProto::is_void() const { return get_rtype() == type::_void(); }

template <typename C>
void DexProto::gather_types(C& ltype) const {
  if (m_args) {
    m_args->gather_types(ltype);
  }
  if (m_rtype) {
    c_append(ltype, m_rtype);
  }
}
INSTANTIATE1(DexProto::gather_types, const DexType*)

void DexProto::gather_strings(std::vector<const DexString*>& lstring) const {
  if (m_shorty != nullptr) {
    c_append(lstring, m_shorty);
  }
}
void DexProto::gather_strings(UnorderedSet<const DexString*>& lstring) const {
  if (m_shorty != nullptr) {
    c_append(lstring, m_shorty);
  }
}

DexSignaturePolymorphicRef* DexSignaturePolymorphicRef::make(
    DexMethodRef* method, DexProto* callsite_proto) {
  return g_redex->make_signature_polymorphic_ref(method, callsite_proto);
}

namespace {

template <typename C>
void maybe_sort_unique(C&) {}
template <>
void maybe_sort_unique(std::vector<const DexType*>& vec) {
  sort_unique(vec);
}

} // namespace

template <typename C>
void DexClass::gather_types(C& ltype) const {
  for (auto const& m : m_dmethods) {
    m->gather_types(ltype);
  }
  for (auto const& m : m_vmethods) {
    m->gather_types(ltype);
  }
  for (auto const& f : m_sfields) {
    f->gather_types(ltype);
  }
  for (auto const& f : m_ifields) {
    f->gather_types(ltype);
  }

  ltype.insert(ltype.end(), m_super_class);
  ltype.insert(ltype.end(), m_self);
  if (m_interfaces) {
    m_interfaces->gather_types(ltype);
  }
  if (m_anno) {
    std::vector<const DexType*> type_vec;
    m_anno->gather_types(type_vec);
    c_append_all(ltype, type_vec.begin(), type_vec.end());
  }

  // We also need to gather types needed for field and method refs.
  std::vector<DexFieldRef*> lfield;
  gather_fields(lfield);
  for (auto const& f : lfield) {
    f->gather_types_shallow(ltype);
  }

  std::vector<DexMethodRef*> lmethod;
  gather_methods(lmethod);
  for (auto const& m : lmethod) {
    m->gather_types_shallow(ltype);
  }

  // Remove duplicates.
  maybe_sort_unique(ltype);
}
INSTANTIATE1(DexClass::gather_types, const DexType*)

void DexClass::gather_load_types(UnorderedSet<const DexType*>& ltype) const {
  if (is_external()) {
    return;
  }
  if (ltype.count(m_self) != 0) {
    return;
  }
  ltype.emplace(m_self);
  {
    auto* superclass = type_class_internal(m_super_class);
    if (superclass != nullptr) {
      superclass->gather_load_types(ltype);
    }
  }
  if (m_interfaces != nullptr) {
    for (const auto* itype : *m_interfaces) {
      auto* iclass = type_class_internal(itype);
      if (iclass != nullptr) {
        iclass->gather_load_types(ltype);
      }
    }
  }
}

void DexClass::gather_init_classes(std::vector<const DexType*>& ltype) const {
  for (auto const& m : m_dmethods) {
    m->gather_init_classes(ltype);
  }
  for (auto const& m : m_vmethods) {
    m->gather_init_classes(ltype);
  }
}

template <typename C>
void DexClass::gather_strings_internal(C& lstring, bool exclude_loads) const {
  for (auto const& m : m_dmethods) {
    m->gather_strings(lstring, exclude_loads);
  }
  for (auto const& m : m_vmethods) {
    m->gather_strings(lstring, exclude_loads);
  }
  for (auto const& f : m_sfields) {
    f->gather_strings(lstring);
  }
  for (auto const& f : m_ifields) {
    f->gather_strings(lstring);
  }
  if (m_source_file) {
    c_append(lstring, m_source_file);
  }
  if (m_anno) {
    std::vector<const DexString*> strings;
    m_anno->gather_strings(strings);
    c_append_all(lstring, strings.begin(), strings.end());
  }
}
void DexClass::gather_strings(std::vector<const DexString*>& lstring,
                              bool exclude_loads) const {
  gather_strings_internal(lstring, exclude_loads);
}
void DexClass::gather_strings(UnorderedSet<const DexString*>& lstring,
                              bool exclude_loads) const {
  gather_strings_internal(lstring, exclude_loads);
}

template <typename C>
void DexClass::gather_fields(C& lfield) const {
  for (auto const& m : m_dmethods) {
    m->gather_fields(lfield);
  }
  for (auto const& m : m_vmethods) {
    m->gather_fields(lfield);
  }
  for (auto const& f : m_sfields) {
    lfield.insert(lfield.end(), f);
    f->gather_fields(lfield);
  }
  for (auto const& f : m_ifields) {
    lfield.insert(lfield.end(), f);
    f->gather_fields(lfield);
  }
  if (m_anno) {
    std::vector<DexFieldRef*> fields_vec; // Simplify refactor.
    m_anno->gather_fields(fields_vec);
    c_append_all(lfield, fields_vec.begin(), fields_vec.end());
  }
}
INSTANTIATE(DexClass::gather_fields, DexFieldRef*)

template <typename C>
void DexClass::gather_methods(C& lmethod) const {
  for (auto const& m : m_dmethods) {
    lmethod.insert(lmethod.end(), m);
    m->gather_methods(lmethod);
  }
  for (auto const& m : m_vmethods) {
    lmethod.insert(lmethod.end(), m);
    m->gather_methods(lmethod);
  }
  for (auto const& f : m_sfields) {
    f->gather_methods(lmethod);
  }
  for (auto const& f : m_ifields) {
    f->gather_methods(lmethod);
  }
  if (m_anno) {
    std::vector<DexMethodRef*> method_vec; // Simplify refactor.
    m_anno->gather_methods(method_vec);
    c_append_all(lmethod, method_vec.begin(), method_vec.end());
  }
}
INSTANTIATE(DexClass::gather_methods, DexMethodRef*)

const DexField* DexFieldRef::as_def() const {
  if (is_def()) {
    return dynamic_cast<const DexField*>(this);
  } else {
    return nullptr;
  }
}

DexField* DexFieldRef::as_def() {
  if (is_def()) {
    return dynamic_cast<DexField*>(this);
  } else {
    return nullptr;
  }
}

// Find methods and fields from a class using its obfuscated name.
DexField* DexClass::find_field_from_simple_deobfuscated_name(
    const std::string& field_name) {
  for (DexField* f : get_sfields()) {
    if (f->get_simple_deobfuscated_name() == field_name) {
      return f;
    }
  }
  for (DexField* f : get_ifields()) {
    if (f->get_simple_deobfuscated_name() == field_name) {
      return f;
    }
  }
  return nullptr;
}

DexMethod* DexClass::find_method_from_simple_deobfuscated_name(
    const std::string& method_name) {
  for (DexMethod* m : get_dmethods()) {
    if (m->get_simple_deobfuscated_name() == method_name) {
      return m;
    }
  }
  for (DexMethod* m : get_vmethods()) {
    if (m->get_simple_deobfuscated_name() == method_name) {
      return m;
    }
  }
  return nullptr;
}

template <typename C>
void DexClass::gather_callsites(C& lcallsite) const {
  for (auto const& m : m_dmethods) {
    m->gather_callsites(lcallsite);
  }
  for (auto const& m : m_vmethods) {
    m->gather_callsites(lcallsite);
  }
}
INSTANTIATE(DexClass::gather_callsites, DexCallSite*)

template <typename C>
void DexClass::gather_protos(C& lproto) const {
  for (auto const& m : m_dmethods) {
    m->gather_protos(lproto);
  }
  for (auto const& m : m_vmethods) {
    m->gather_protos(lproto);
  }
  for (auto const& f : m_sfields) {
    f->gather_protos(lproto);
  }
  for (auto const& f : m_ifields) {
    f->gather_protos(lproto);
  }
  if (m_anno) {
    std::vector<DexProto*> proto_vec;
    m_anno->gather_protos(proto_vec);
    c_append_all(lproto, proto_vec.begin(), proto_vec.end());
  }
}
INSTANTIATE(DexClass::gather_protos, DexProto*)

template <typename C>
void DexClass::gather_methodhandles(C& lmethodhandle) const {
  for (auto const& m : m_dmethods) {
    m->gather_methodhandles(lmethodhandle);
  }
  for (auto const& m : m_vmethods) {
    m->gather_methodhandles(lmethodhandle);
  }
  for (auto const& f : m_sfields) {
    f->gather_methodhandles(lmethodhandle);
  }
  for (auto const& f : m_ifields) {
    f->gather_methodhandles(lmethodhandle);
  }
  if (m_anno) {
    std::vector<DexMethodHandle*> mhandles_vec;
    m_anno->gather_methodhandles(mhandles_vec);
    c_append_all(lmethodhandle, mhandles_vec.begin(), mhandles_vec.end());
  }
}
INSTANTIATE(DexClass::gather_methodhandles, DexMethodHandle*)

template <typename C>
void DexFieldRef::gather_types_shallow(C& ltype) const {
  ltype.insert(ltype.end(), m_spec.cls);
  ltype.insert(ltype.end(), m_spec.type);
}
INSTANTIATE1(DexFieldRef::gather_types_shallow, const DexType*)

void DexFieldRef::gather_strings_shallow(
    std::vector<const DexString*>& lstring) const {
  c_append(lstring, m_spec.name);
}
void DexFieldRef::gather_strings_shallow(
    UnorderedSet<const DexString*>& lstring) const {
  c_append(lstring, m_spec.name);
}

template <typename C>
void DexField::gather_types(C& ltype) const {
  std::vector<const DexType*> type_vec;
  if (m_value) {
    m_value->gather_types(type_vec);
  }
  if (m_anno) {
    m_anno->gather_types(type_vec);
  }
  c_append_all(ltype, type_vec.begin(), type_vec.end());
}
INSTANTIATE1(DexField::gather_types, const DexType*)

template <typename C>
void DexField::gather_strings_internal(C& lstring) const {
  std::vector<const DexString*> string_vec;
  if (m_value) {
    m_value->gather_strings(string_vec);
  }
  if (m_anno) {
    m_anno->gather_strings(string_vec);
  }
  c_append_all(lstring, string_vec.begin(), string_vec.end());
}
void DexField::gather_strings(std::vector<const DexString*>& lstring) const {
  gather_strings_internal(lstring);
}
void DexField::gather_strings(UnorderedSet<const DexString*>& lstring) const {
  gather_strings_internal(lstring);
}

template <typename C>
void DexField::gather_fields(C& lfield) const {
  std::vector<DexFieldRef*> field_vec;
  if (m_value) {
    m_value->gather_fields(field_vec);
  }
  if (m_anno) {
    m_anno->gather_fields(field_vec);
  }
  c_append_all(lfield, field_vec.begin(), field_vec.end());
}
INSTANTIATE(DexField::gather_fields, DexFieldRef*)

template <typename C>
void DexField::gather_methods(C& lmethod) const {
  std::vector<DexMethodRef*> method_vec;
  if (m_value) {
    m_value->gather_methods(method_vec);
  }
  if (m_anno) {
    m_anno->gather_methods(method_vec);
  }
  c_append_all(lmethod, method_vec.begin(), method_vec.end());
}
INSTANTIATE(DexField::gather_methods, DexMethodRef*)

template <typename C>
void DexField::gather_protos(C& lproto) const {
  std::vector<DexProto*> proto_vec;
  if (m_value) {
    m_value->gather_protos(proto_vec);
  }
  if (m_anno) {
    m_anno->gather_protos(proto_vec);
  }
  c_append_all(lproto, proto_vec.begin(), proto_vec.end());
}
INSTANTIATE(DexField::gather_protos, DexProto*)

template <typename C>
void DexField::gather_methodhandles(C& lmethodhandle) const {
  std::vector<DexMethodHandle*> mhandles_vec;
  if (m_value) {
    m_value->gather_methodhandles(mhandles_vec);
  }
  if (m_anno) {
    m_anno->gather_methodhandles(mhandles_vec);
  }
  c_append_all(lmethodhandle, mhandles_vec.begin(), mhandles_vec.end());
}
INSTANTIATE(DexField::gather_methodhandles, DexMethodHandle*)

std::string DexField::get_simple_deobfuscated_name() const {
  return get_simple_deobf_name(this);
}

void DexMethod::set_external() {
  always_assert_log(!m_concrete, "Unexpected concrete method %s\n",
                    self_show().c_str());
  m_deobfuscated_name = DexString::make_string(self_show());
  m_external = true;
}

template <typename C>
void DexMethod::gather_types(C& ltype) const {
  gather_types_shallow(ltype); // Handle DexMethodRef parts.
  std::vector<const DexType*> type_vec; // Simplify refactor.
  if (m_code) {
    m_code->gather_types(type_vec);
  }
  if (m_anno) {
    m_anno->gather_types(type_vec);
  }
  const auto* param_anno = get_param_anno();
  if (param_anno) {
    for (const auto& pair : *param_anno) {
      const auto& anno_set = pair.second;
      anno_set->gather_types(type_vec);
    }
  }
  c_append_all(ltype, type_vec.begin(), type_vec.end());
}
INSTANTIATE1(DexMethod::gather_types, const DexType*)

void DexMethod::gather_init_classes(std::vector<const DexType*>& ltype) const {
  if (m_code) {
    m_code->gather_init_classes(ltype);
  }
}

template <typename C>
void DexMethod::gather_callsites(C& lcallsite) const {
  // We handle m_spec.cls and proto in the first-layer gather.
  if (m_code) {
    std::vector<DexCallSite*> callsite_vec; // Simplify refactor.
    m_code->gather_callsites(callsite_vec);
    c_append_all(lcallsite, callsite_vec.begin(), callsite_vec.end());
  }
}
INSTANTIATE(DexMethod::gather_callsites, DexCallSite*)

template <typename C>
void DexMethod::gather_protos(C& lproto) const {
  // The method's own proto is handled with the method ref.
  std::vector<DexProto*> proto_vec;
  if (m_code) {
    m_code->gather_protos(proto_vec);
  }
  if (m_anno) {
    m_anno->gather_protos(proto_vec);
  }
  const auto* param_anno = get_param_anno();
  if (param_anno) {
    for (const auto& pair : *param_anno) {
      pair.second->gather_protos(proto_vec);
    }
  }
  c_append_all(lproto, proto_vec.begin(), proto_vec.end());
}
INSTANTIATE(DexMethod::gather_protos, DexProto*)

template <typename C>
void DexMethod::gather_methodhandles(C& lmethodhandle) const {
  // We handle m_spec.cls and proto in the first-layer gather.
  std::vector<DexMethodHandle*> mhandles_vec; // Simplify refactor.
  if (m_code) {
    m_code->gather_methodhandles(mhandles_vec);
  }
  if (m_anno) {
    m_anno->gather_methodhandles(mhandles_vec);
  }
  const auto* param_anno = get_param_anno();
  if (param_anno) {
    for (const auto& pair : *param_anno) {
      pair.second->gather_methodhandles(mhandles_vec);
    }
  }
  c_append_all(lmethodhandle, mhandles_vec.begin(), mhandles_vec.end());
}
INSTANTIATE(DexMethod::gather_methodhandles, DexMethodHandle*)
template <typename C>
void DexMethod::gather_strings_internal(C& lstring, bool exclude_loads) const {
  // We handle m_name and proto in the first-layer gather.
  std::vector<const DexString*> strings_vec; // Simplify refactor.
  if (m_code && !exclude_loads) {
    m_code->gather_strings(strings_vec);
  }
  if (m_anno) {
    m_anno->gather_strings(strings_vec);
  }
  const auto* param_anno = get_param_anno();
  if (param_anno) {
    for (const auto& pair : *param_anno) {
      const auto& anno_set = pair.second;
      anno_set->gather_strings(strings_vec);
    }
  }
  c_append_all(lstring, strings_vec.begin(), strings_vec.end());
}
void DexMethod::gather_strings(std::vector<const DexString*>& lstring,
                               bool exclude_loads) const {
  gather_strings_internal(lstring, exclude_loads);
}
void DexMethod::gather_strings(UnorderedSet<const DexString*>& lstring,
                               bool exclude_loads) const {
  gather_strings_internal(lstring, exclude_loads);
}

template <typename C>
void DexMethod::gather_fields(C& lfield) const {
  std::vector<DexFieldRef*> fields_vec; // Simplify refactor.
  if (m_code) {
    m_code->gather_fields(fields_vec);
  }
  if (m_anno) {
    m_anno->gather_fields(fields_vec);
  }
  const auto* param_anno = get_param_anno();
  if (param_anno) {
    for (const auto& pair : *param_anno) {
      const auto& anno_set = pair.second;
      anno_set->gather_fields(fields_vec);
    }
  }
  c_append_all(lfield, fields_vec.begin(), fields_vec.end());
}
INSTANTIATE(DexMethod::gather_fields, DexFieldRef*)

template <typename C>
void DexMethod::gather_methods(C& lmethod) const {
  if (m_code) {
    std::vector<DexMethodRef*> method_vec; // Simplify refactor.
    m_code->gather_methods(method_vec);
    c_append_all(lmethod, method_vec.begin(), method_vec.end());
  }
  gather_methods_from_annos(lmethod);
}
INSTANTIATE(DexMethod::gather_methods, DexMethodRef*)

template <typename C>
void DexMethod::gather_methods_from_annos(C& lmethod) const {
  std::vector<DexMethodRef*> method_vec; // Simplify refactor.
  if (m_anno) {
    m_anno->gather_methods(method_vec);
  }
  const auto* param_anno = get_param_anno();
  if (param_anno) {
    for (const auto& pair : *param_anno) {
      const auto& anno_set = pair.second;
      anno_set->gather_methods(method_vec);
    }
  }
  c_append_all(lmethod, method_vec.begin(), method_vec.end());
}
INSTANTIATE(DexMethod::gather_methods_from_annos, DexMethodRef*)

const DexMethod* DexMethodRef::as_def() const {
  if (is_def()) {
    return dynamic_cast<const DexMethod*>(this);
  } else {
    return nullptr;
  }
}

DexMethod* DexMethodRef::as_def() {
  if (is_def()) {
    return dynamic_cast<DexMethod*>(this);
  } else {
    return nullptr;
  }
}

template <typename C>
void DexMethodRef::gather_types_shallow(C& ltype) const {
  ltype.insert(ltype.end(), m_spec.cls);
  m_spec.proto->gather_types(ltype);
}
INSTANTIATE1(DexMethodRef::gather_types_shallow, const DexType*)

void DexMethodRef::gather_strings_shallow(
    std::vector<const DexString*>& lstring) const {
  lstring.insert(lstring.end(), m_spec.name);
  m_spec.proto->gather_strings(lstring);
}
void DexMethodRef::gather_strings_shallow(
    UnorderedSet<const DexString*>& lstring) const {
  lstring.insert(lstring.end(), m_spec.name);
  m_spec.proto->gather_strings(lstring);
}

uint32_t DexCode::size() const {
  uint32_t size = 0;
  for (auto const& opc : get_instructions()) {
    if (!dex_opcode::is_fopcode(opc->opcode())) {
      size += opc->size();
    }
  }
  return size;
}

DexType* DexType::make_type(const DexString* dstring) {
  return g_redex->make_type(dstring);
}

DexType* DexType::get_type(const DexString* dstring) {
  return g_redex->get_type(dstring);
}

void DexType::set_name(const DexString* new_name) {
  g_redex->set_type_name(this, new_name);
}

DexProto* DexType::get_non_overlapping_proto(const DexString* method_name,
                                             DexProto* orig_proto) {
  auto* methodref_in_context =
      DexMethod::get_method(this, method_name, orig_proto);
  if (methodref_in_context == nullptr) {
    return orig_proto;
  }
  DexTypeList::ContainerType new_arg_list;
  auto* rtype = orig_proto->get_rtype();
  for (const auto* t : *orig_proto->get_args()) {
    new_arg_list.push_back(t);
  }
  new_arg_list.push_back(type::_int());
  DexTypeList* new_args =
      DexTypeList::make_type_list(DexTypeList::ContainerType{new_arg_list});
  DexProto* new_proto = DexProto::make_proto(rtype, new_args);
  methodref_in_context = DexMethod::get_method(this, method_name, new_proto);
  while (methodref_in_context != nullptr) {
    new_arg_list.push_back(type::_int());
    new_args =
        DexTypeList::make_type_list(DexTypeList::ContainerType{new_arg_list});
    new_proto = DexProto::make_proto(rtype, new_args);
    methodref_in_context = DexMethod::get_method(this, method_name, new_proto);
  }
  return new_proto;
}

void DexMethod::add_load_params(size_t num_add_loads) {
  IRCode* code = this->get_code();
  always_assert_log(code, "Method doesn't have IRCode\n");
  always_assert_log(code->cfg_built(), "should be editable cfg here\n");
  auto& cfg = code->cfg();
  auto* block = cfg.entry_block();
  auto last_loading = block->get_last_param_loading_insn();
  size_t added_params = 0;
  while (added_params < num_add_loads) {
    ++added_params;
    auto temp = cfg.allocate_temp();
    IRInstruction* new_param_load = new IRInstruction(IOPCODE_LOAD_PARAM);
    new_param_load->set_dest(temp);
    if (last_loading != block->end()) {
      cfg.insert_after(block->to_cfg_instruction_iterator(last_loading),
                       new_param_load);
    } else {
      cfg.insert_before(block->to_cfg_instruction_iterator(
                            block->get_first_non_param_loading_insn()),
                        new_param_load);
    }
    last_loading = block->get_last_param_loading_insn();
  }
}

namespace {

// Appends each element of `references` that `list` does not hold yet, in the
// order of its first occurrence.
template <typename T>
void append_first_references(std::vector<T*>& list,
                             const std::vector<T*>& references) {
  UnorderedSet<T*> seen(list.begin(), list.end());
  for (auto* ref : references) {
    if (seen.insert(ref).second) {
      list.push_back(ref);
    }
  }
}

} // namespace

void gather_components(std::vector<const DexString*>& lstring,
                       std::vector<const DexType*>& ltype,
                       std::vector<DexFieldRef*>& lfield,
                       std::vector<DexMethodRef*>& lmethod,
                       std::vector<DexCallSite*>& lcallsite,
                       std::vector<DexMethodHandle*>& lmethodhandle,
                       std::vector<DexProto*>& lproto,
                       const DexClasses& classes,
                       bool exclude_loads) {
  // Gather references reachable from each class.
  UnorderedSet<const DexString*> strings;
  UnorderedSet<const DexType*> types;
  UnorderedSet<DexFieldRef*> fields;
  UnorderedSet<DexMethodRef*> methods;
  // Call sites and method handles are not interned, so equal ones are distinct
  // objects whose address order varies between runs. They are listed in the
  // order the classes first refer to them instead.
  std::vector<DexCallSite*> callsites;
  std::vector<DexMethodHandle*> methodhandles;
  UnorderedSet<DexProto*> protos;
  // Inside a lambda to ensure only visibility of the sets.
  [&classes, &exclude_loads, &strings, &types, &fields, &methods, &callsites,
   &methodhandles, &protos]() {
    for (auto const& cls : classes) {
      cls->gather_strings(strings, exclude_loads);
      cls->gather_types(types);
      cls->gather_fields(fields);
      cls->gather_methods(methods);
      cls->gather_callsites(callsites);
      cls->gather_methodhandles(methodhandles);
      cls->gather_protos(protos);
    }

    // Gather types and strings needed for field and method refs.
    for (auto* meth : UnorderedIterable(methods)) {
      meth->gather_types_shallow(types);
      meth->gather_strings_shallow(strings);
    }

    for (auto* field : UnorderedIterable(fields)) {
      field->gather_types_shallow(types);
      field->gather_strings_shallow(strings);
    }

    for (auto* proto : UnorderedIterable(protos)) {
      proto->gather_types(types);
      proto->gather_strings(strings);
    }

    // Gather strings needed for each type.
    for (const auto* type : UnorderedIterable(types)) {
      if (type != nullptr) {
        strings.insert(type->get_name());
      }
    }
  }();

  insert_unordered_iterable(lstring, lstring.end(), strings);
  insert_unordered_iterable(ltype, ltype.end(), types);
  insert_unordered_iterable(lfield, lfield.end(), fields);
  insert_unordered_iterable(lmethod, lmethod.end(), methods);
  append_first_references(lcallsite, callsites);
  append_first_references(lmethodhandle, methodhandles);
  insert_unordered_iterable(lproto, lproto.end(), protos);

  // This retains pre-set computation behavior.
  sort_unique(lstring);
  sort_unique(ltype);
  sort_unique(lfield);
  sort_unique(lmethod);
  sort_unique(lproto);
}

std::string DexField::self_show() const { return show(this); }
std::string DexMethod::self_show() const { return show(this); }
std::string DexClass::self_show() const { return show(m_self); }

std::string DexClass::show_structure() const {
  std::string tmp = vshow(m_self);
  if (!get_sfields().empty() || !get_ifields().empty()) {
    tmp += "\nFields:";
    auto add_field = [&](auto* f, const char* prefix) {
      tmp += "\n  ";
      tmp += prefix;
      tmp += show(f);
    };
    for (auto* f : get_sfields()) {
      add_field(f, "static ");
    }
    for (auto* f : get_ifields()) {
      add_field(f, "instance ");
    }
  }
  auto ctors = get_ctors();
  if (!ctors.empty()) {
    tmp += "\nConstructors:";
    for (auto* m : ctors) {
      tmp += "\n  ";
      tmp += show(m);
    }
  }

  if (!get_dmethods().empty() || !get_vmethods().empty()) {
    tmp += "\nMethods:";
    auto add_method = [&](auto* m, const char* prefix) {
      if (m->get_name()->str() == "<init>") {
        return;
      }
      tmp += "\n  ";
      tmp += prefix;
      tmp += show(m);
    };
    for (auto* m : get_dmethods()) {
      add_method(m, "direct ");
    }
    for (auto* m : get_vmethods()) {
      add_method(m, "virtual ");
    }
  }
  return tmp;
}

void DexMethodRef::erase_method(DexMethodRef* mref) {
  g_redex->erase_method(mref);
  if (mref->is_def()) {
    auto* m = mref->as_def();
    if (m->get_name() != m->get_deobfuscated_name_or_null()) {
      g_redex->erase_method(m->get_class(), m->get_deobfuscated_name_or_null(),
                            m->get_proto());
    }
  }
}

void DexMethodRef::delete_method_DO_NOT_USE(DexMethodRef* method) {
  erase_method(method);
  delete dynamic_cast<DexMethod*>(method);
}

dex_member_refs::MethodDescriptorTokens DexMethodRef::get_descriptor_tokens()
    const {
  dex_member_refs::MethodDescriptorTokens res;
  res.cls = get_class()->str();
  res.name = get_name()->str();
  for (const auto* t : *get_proto()->get_args()) {
    res.args.push_back(t->str());
  }
  res.rtype = get_proto()->get_rtype()->str();
  return res;
}

DexClass* type_class(const DexType* t) { return g_redex->type_class(t); }

bool DexMethodRef::is_valid_name(std::string_view name) {
  if (name.empty()) {
    return false;
  }
  if (name[0] == '<') {
    return name == "<init>" || name == "<clinit>";
  }
  if (!is_valid_identifier(name)) {
    return false;
  }
  for (auto c : name) {
    if (c == '<' || c == '>') {
      return false;
    }
  }
  return true;
}
