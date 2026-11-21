/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "DexHasher.h"

#include <cinttypes>
#include <ostream>

#include "Debug.h"
#include "DeterministicContainers.h"
#include "DexAccess.h"
#include "DexAnnotation.h"
#include "DexCallSite.h"
#include "DexClass.h"
#include "DexInstruction.h"
#include "DexMethodHandle.h"
#include "DexPosition.h"
#include "IRCode.h"
#include "IRInstruction.h"
#include "Show.h"
#include "StringUtil.h"
#include "Trace.h"
#include "Walkers.h"

namespace hashing {

// A local implementation. Avoids heap allocation for the scope version.
// Impl is an abstract base class with shared hashing infrastructure.

namespace {

class Impl {
 public:
  virtual ~Impl() = default;
  virtual DexHash run() = 0;

 protected:
  DexHash get_hash() const;
  void hash(const std::string_view str);
  void hash(const std::string& str);
  void hash(int value);
  void hash(uint64_t value);
  void hash(uint32_t value);
  void hash(uint16_t value);
  void hash(uint8_t value);
  void hash(bool value);
  void hash(const IRCode* c);
  void hash(const cfg::ControlFlowGraph& cfg);
  void hash_code_init(const IRList::const_iterator& begin,
                      const IRList::const_iterator& end,
                      UnorderedMap<const MethodItemEntry*, uint32_t>* mie_ids,
                      UnorderedMap<DexPosition*, uint32_t>* pos_ids);
  void hash_code_flush(
      const IRList::const_iterator& begin,
      const IRList::const_iterator& end,
      const UnorderedMap<const MethodItemEntry*, uint32_t>& mie_ids,
      const UnorderedMap<DexPosition*, uint32_t>& pos_ids);
  void hash(const IRInstruction* insn);
  void hash(const EncodedAnnotations* a);
  void hash(const ParamAnnotations* m);
  void hash(const DexAnnotation* a);
  void hash(const DexAnnotationSet* s);
  void hash(const DexAnnotationElement& elem);
  void hash(const DexEncodedValue* v);
  void hash(const DexCallSite* c);
  void hash(const DexMethodHandle* h);
  void hash(const DexProto* p);
  void hash(const DexMethodRef* m);
  void hash(const DexMethod* m);
  void hash(const DexFieldRef* f);
  void hash(const DexField* f);
  void hash(const DexType* t);
  void hash(const DexTypeList* l);
  void hash(const DexString* s);
  template <class T>
  void hash(const std::vector<T>& l) {
    hash((uint64_t)l.size());
    for (const auto& elem : l) {
      hash(elem);
    }
  }
  template <class T>
  void hash(const boost::iterator_range<const reg_t*>& l) {
    hash((uint64_t)l.size());
    for (const auto& elem : l) {
      hash(elem);
    }
  }
  template <class T>
  void hash(const std::deque<T>& l) {
    hash((uint64_t)l.size());
    for (const auto& elem : l) {
      hash(elem);
    }
  }
  template <typename T>
  void hash(const std::unique_ptr<T>& uptr) {
    hash(uptr.get());
  }
  template <class K, class V>
  void hash(const std::map<K, V>& l) {
    hash((uint64_t)l.size());
    for (const auto& p : l) {
      hash(p.first);
      hash(p.second);
    }
  }

  // Template magic.
  template <typename, typename = void>
  struct has_size : std::false_type {};
  template <typename T>
  struct has_size<T, std::void_t<decltype(&T::size)>> : std::true_type {};

  // Not applying to map-like things (like UnorderedMap) should be done by
  // failures to hash the elements.
  template <typename T,
            typename std::enable_if<has_size<T>::value, T>::type* = nullptr>
  void hash(const T& c) {
    hash((uint64_t)c.size());
    for (const auto& elem : c) {
      hash(elem);
    }
  }

  // When true, excludes debug info and source blocks from the hash.
  // Used by DexMethodHasher to hash only the actual code instructions.
  Impl& set_code_only(bool code_only) {
    m_code_only = code_only;
    return *this;
  }

  size_t m_hash{0};
  size_t m_code_hash{0};
  size_t m_registers_hash{0};
  size_t m_positions_hash{0};

 private:
  bool m_code_only{false};
};

// Hashes a DexClass including all its methods and fields.
class DexClassImpl final : public Impl {
 public:
  explicit DexClassImpl(DexClass* cls) : m_cls(cls) {}
  DexHash run() override;
  void print(std::ostream&);

 private:
  void hash_metadata();
  DexClass* const m_cls;
};

class DexMethodImpl final : public Impl {
 public:
  explicit DexMethodImpl(const DexMethod* method) : m_method(method) {
    set_code_only(true);
  }
  DexHash run() override;

 private:
  const DexMethod* const m_method;
};

void Impl::hash(const std::string_view str) {
  TRACE(HASHER, 4, "[hasher] %s", str_copy(str).c_str());
  boost::hash_combine(m_hash, str);
}

void Impl::hash(const std::string& str) {
  TRACE(HASHER, 4, "[hasher] %s", str.c_str());
  boost::hash_combine(m_hash, str);
}

void Impl::hash(const DexString* s) { hash(s->str()); }

void Impl::hash(bool value) {
  TRACE(HASHER, 4, "[hasher] %d", value);
  boost::hash_combine(m_hash, value);
}
void Impl::hash(uint8_t value) {
  TRACE(HASHER, 4, "[hasher] %" PRIu8, value);
  boost::hash_combine(m_hash, value);
}

void Impl::hash(uint16_t value) {
  TRACE(HASHER, 4, "[hasher] %" PRIu16, value);
  boost::hash_combine(m_hash, value);
}

void Impl::hash(uint32_t value) {
  TRACE(HASHER, 4, "[hasher] %" PRIu32, value);
  boost::hash_combine(m_hash, value);
}

void Impl::hash(uint64_t value) {
  TRACE(HASHER, 4, "[hasher] %" PRIu64, value);
  boost::hash_combine(m_hash, value);
}

void Impl::hash(int value) {
  if (sizeof(int) == 8) {
    hash((uint64_t)value);
  } else {
    hash((uint32_t)value);
  }
}

void Impl::hash(const IRInstruction* insn) {
  hash((uint16_t)insn->opcode());

  auto old_hash = m_hash;
  m_hash = 0;
  hash(insn->srcs());
  if (insn->has_dest()) {
    hash(insn->dest());
  }
  boost::hash_combine(m_registers_hash, m_hash);
  m_hash = old_hash;

  if (insn->has_literal()) {
    hash((uint64_t)insn->get_literal());
  } else if (insn->has_string()) {
    hash(insn->get_string());
  } else if (insn->has_type()) {
    hash(insn->get_type());
  } else if (insn->has_field()) {
    hash(insn->get_field());
  } else if (insn->has_method()) {
    hash(insn->get_method());
  } else if (insn->has_callsite()) {
    hash(insn->get_callsite());
  } else if (insn->has_methodhandle()) {
    hash(insn->get_methodhandle());
  } else if (insn->has_proto()) {
    hash(insn->get_proto());
  } else if (insn->has_data()) {
    auto* data = insn->get_data();
    hash((uint32_t)data->data_size());
    for (size_t i = 0; i < data->data_size(); i++) {
      hash(data->data()[i]);
    }
  }
}

void Impl::hash(const IRCode* c) {
  if (c == nullptr) {
    return;
  }

  auto old_hash = m_hash;
  m_hash = 0;

  if (c->cfg_built()) {
    hash(c->cfg());
  } else {
    hash(c->get_registers_size());

    UnorderedMap<const MethodItemEntry*, uint32_t> mie_ids;
    UnorderedMap<DexPosition*, uint32_t> pos_ids;

    hash_code_init(c->begin(), c->end(), &mie_ids, &pos_ids);
    hash_code_flush(c->begin(), c->end(), mie_ids, pos_ids);
  }

  boost::hash_combine(m_code_hash, m_hash);
  m_hash = old_hash;
}

void Impl::hash(const cfg::ControlFlowGraph& cfg) {
  hash(cfg.get_registers_size());
  hash((uint32_t)cfg.entry_block()->id());
  UnorderedMap<const MethodItemEntry*, uint32_t> mie_ids;
  UnorderedMap<DexPosition*, uint32_t> pos_ids;
  for (auto* b : cfg.blocks()) {
    hash((uint32_t)b->id());
    hash_code_init(b->begin(), b->end(), &mie_ids, &pos_ids);
    for (auto* e : b->succs()) {
      hash((uint32_t)e->target()->id());
      hash((uint8_t)e->type());
      if (e->type() == cfg::EDGE_THROW) {
        auto* throw_info = e->throw_info();
        hash(throw_info->index);
        if (throw_info->catch_type != nullptr) {
          hash(throw_info->catch_type);
        }
        continue;
      }
      auto case_key = e->case_key();
      if (case_key) {
        hash((uint32_t)*case_key);
      }
    }
  }
  // mie-ids would only be generated by MethodItemEntries that are not present
  // in cfgs.
  always_assert(mie_ids.empty());
  for (auto* b : cfg.blocks()) {
    hash_code_flush(b->begin(), b->end(), mie_ids, pos_ids);
  }
}

void Impl::hash_code_init(
    const IRList::const_iterator& begin,
    const IRList::const_iterator& end,
    UnorderedMap<const MethodItemEntry*, uint32_t>* mie_ids,
    UnorderedMap<DexPosition*, uint32_t>* pos_ids) {
  auto get_mie_id = [mie_ids](const MethodItemEntry* mie) {
    auto it = mie_ids->find(mie);
    if (it != mie_ids->end()) {
      return it->second;
    } else {
      auto id = (uint32_t)mie_ids->size();
      mie_ids->emplace(mie, id);
      return id;
    }
  };

  auto get_pos_id = [pos_ids](DexPosition* pos) {
    auto it = pos_ids->find(pos);
    if (it != pos_ids->end()) {
      return it->second;
    } else {
      auto id = (uint32_t)pos_ids->size();
      pos_ids->emplace(pos, id);
      return id;
    }
  };

  for (auto code_it = begin; code_it != end; code_it++) {
    const MethodItemEntry& mie = *code_it;
    switch (mie.type) {
    case MFLOW_OPCODE:
      hash((uint8_t)MFLOW_OPCODE);
      hash(mie.insn);
      break;
    case MFLOW_TRY:
      hash((uint8_t)MFLOW_TRY);
      hash((uint8_t)mie.tentry->type);
      hash(get_mie_id(mie.tentry->catch_start));
      break;
    case MFLOW_CATCH:
      hash((uint8_t)MFLOW_CATCH);
      if (mie.centry->catch_type != nullptr) {
        hash(mie.centry->catch_type);
      }
      hash(get_mie_id(mie.centry->next));
      break;
    case MFLOW_TARGET:
      hash((uint8_t)MFLOW_TARGET);
      hash((uint8_t)mie.target->type);
      hash(get_mie_id(mie.target->src));
      break;
    case MFLOW_DEBUG:
      if (!m_code_only) {
        hash((uint8_t)MFLOW_DEBUG);
        hash(mie.dbgop->opcode());
        hash(mie.dbgop->uvalue());
      }
      break;
    case MFLOW_POSITION: {
      auto old_hash2 = m_hash;
      m_hash = 0;
      hash((uint8_t)MFLOW_POSITION);
      if (mie.pos->method != nullptr) {
        hash(mie.pos->method);
      }
      if (mie.pos->file != nullptr) {
        hash(mie.pos->file);
      }
      hash(mie.pos->line);
      if (mie.pos->parent != nullptr) {
        hash(get_pos_id(mie.pos->parent));
      }
      boost::hash_combine(m_positions_hash, m_hash);
      m_hash = old_hash2;
      break;
    }
    case MFLOW_SOURCE_BLOCK:
      if (!m_code_only) {
        hash((uint8_t)MFLOW_SOURCE_BLOCK);
        for (auto* sb = mie.src_block.get(); sb != nullptr;
             sb = sb->next.get()) {
          hash(sb->src);
          hash(sb->id);
        }
      }
      break;
    case MFLOW_REMARK:
      if (!m_code_only) {
        hash((uint8_t)MFLOW_REMARK);
        hash(mie.remark->producer);
        hash(mie.remark->val_str);
        hash(static_cast<uint64_t>(mie.remark->val_int));
      }
      break;
    case MFLOW_FALLTHROUGH:
      hash((uint8_t)MFLOW_FALLTHROUGH);
      break;
    case MFLOW_DEX_OPCODE:
      not_reached();
    default:
      not_reached();
    }
  }
}

void Impl::hash_code_flush(
    const IRList::const_iterator& begin,
    const IRList::const_iterator& end,
    const UnorderedMap<const MethodItemEntry*, uint32_t>& mie_ids,
    const UnorderedMap<DexPosition*, uint32_t>& pos_ids) {
  uint32_t mie_index = 0;
  for (auto code_it = begin; code_it != end; code_it++) {
    const MethodItemEntry& mie = *code_it;
    auto it = mie_ids.find(&mie);
    if (it != mie_ids.end()) {
      hash(it->second);
      hash(mie_index);
    }
    if (mie.type == MFLOW_POSITION) {
      auto it2 = pos_ids.find(mie.pos.get());
      if (it2 != pos_ids.end()) {
        auto old_hash2 = m_hash;
        m_hash = 0;
        hash(it2->second);
        hash(mie_index);
        boost::hash_combine(m_positions_hash, m_hash);
        m_hash = old_hash2;
      }
    }
    mie_index++;
  }
}

void Impl::hash(const DexCallSite* c) {
  hash(c->method_handle());
  hash(c->method_name());
  hash(c->method_type());
  hash(c->args());
}

void Impl::hash(const DexMethodHandle* h) {
  hash((uint8_t)h->type());
  if (DexMethodHandle::isInvokeType(h->type())) {
    hash(h->methodref());
  } else {
    hash(h->fieldref());
  }
}

void Impl::hash(const DexProto* p) {
  hash(p->get_rtype());
  hash(p->get_args());
  hash(p->get_shorty());
}

void Impl::hash(const DexMethodRef* m) {
  hash(m->get_class());
  hash(m->get_name());
  hash(m->get_proto());
  hash(m->is_concrete());
  hash(m->is_external());
}

void Impl::hash(const DexMethod* m) {
  hash(static_cast<const DexMethodRef*>(m));
  hash(m->get_anno_set());
  hash(m->get_access());
  hash(m->get_deobfuscated_name_or_empty());
  hash(m->get_param_anno());
  hash(m->get_code());
}

void Impl::hash(const DexFieldRef* f) {
  hash(f->get_name());
  hash(f->is_concrete());
  hash(f->is_external());
  hash(f->get_type());
}

void Impl::hash(const DexType* t) { hash(t->get_name()); }

void Impl::hash(const DexTypeList* l) { hash(*l); }

void Impl::hash(const ParamAnnotations* m) {
  if (m != nullptr) {
    hash(*m);
  }
}

void Impl::hash(const DexAnnotationElement& elem) {
  hash(elem.string);
  hash(elem.encoded_value);
}

void Impl::hash(const EncodedAnnotations* a) {
  if (a != nullptr) {
    hash(*a);
  }
}

void Impl::hash(const DexAnnotation* a) {
  if (a != nullptr) {
    hash(&a->anno_elems());
    hash(a->type());
    hash((uint8_t)a->viz());
  }
}

void Impl::hash(const DexAnnotationSet* s) {
  if (s != nullptr) {
    hash(s->get_annotations());
  }
}

void Impl::hash(const DexEncodedValue* v) {
  if (v == nullptr) {
    return;
  }

  auto evtype = v->evtype();
  hash((uint8_t)evtype);
  switch (evtype) {
  case DEVT_STRING: {
    const auto* s = dynamic_cast<const DexEncodedValueString*>(v);
    hash(s->string());
    break;
  }
  case DEVT_TYPE: {
    const auto* t = dynamic_cast<const DexEncodedValueType*>(v);
    hash(t->type());
    break;
  }
  case DEVT_FIELD:
  case DEVT_ENUM: {
    const auto* f = dynamic_cast<const DexEncodedValueField*>(v);
    hash(f->field());
    break;
  }
  case DEVT_METHOD: {
    const auto* f = dynamic_cast<const DexEncodedValueMethod*>(v);
    hash(f->method());
    break;
  }
  case DEVT_METHOD_TYPE: {
    const auto* t = dynamic_cast<const DexEncodedValueMethodType*>(v);
    hash(t->proto());
    break;
  }
  case DEVT_METHOD_HANDLE: {
    const auto* h = dynamic_cast<const DexEncodedValueMethodHandle*>(v);
    hash(h->methodhandle());
    break;
  }
  case DEVT_ARRAY: {
    const auto* a = dynamic_cast<const DexEncodedValueArray*>(v);
    hash(*a->evalues());
    break;
  }
  case DEVT_ANNOTATION: {
    const auto* a = dynamic_cast<const DexEncodedValueAnnotation*>(v);
    hash(a->type());
    hash(a->annotations()); // const EncodedAnnotations*
    break;
  };
  default:
    hash(v->value());
    break;
  }
}

void Impl::hash(const DexField* f) {
  hash(static_cast<const DexFieldRef*>(f));
  hash(f->get_anno_set());
  hash(f->get_static_value());
  hash(f->get_access());
  hash(f->get_deobfuscated_name_or_empty());
}

void DexClassImpl::hash_metadata() {
  hash(m_cls->get_access());
  hash(m_cls->get_type());
  if (m_cls->get_super_class() != nullptr) {
    hash(m_cls->get_super_class());
  }
  hash(m_cls->get_interfaces());
  hash(m_cls->get_anno_set());
}

DexHash Impl::get_hash() const {
  return DexHash{m_positions_hash, m_registers_hash, m_code_hash, m_hash};
}

DexHash DexClassImpl::run() {
  TRACE(HASHER, 2, "[hasher] ==== hashing class %s", SHOW(m_cls->get_type()));

  hash_metadata();

  TRACE(HASHER, 3, "[hasher] === dmethods: %zu", m_cls->get_dmethods().size());
  hash(m_cls->get_dmethods());

  TRACE(HASHER, 3, "[hasher] === vmethods: %zu", m_cls->get_vmethods().size());
  hash(m_cls->get_vmethods());

  TRACE(HASHER, 3, "[hasher] === sfields: %zu", m_cls->get_sfields().size());
  hash(m_cls->get_sfields());

  TRACE(HASHER, 3, "[hasher] === ifields: %zu", m_cls->get_ifields().size());
  hash(m_cls->get_ifields());

  return get_hash();
}

void DexClassImpl::print(std::ostream& ofs) {
  hash_metadata();
  ofs << "type " << show(m_cls) << " #" << hash_to_string(m_hash) << '\n';
  for (auto* field : m_cls->get_ifields()) {
    m_hash = 0;
    hash(field);
    ofs << "ifield " << show(field) << " #" << hash_to_string(m_hash) << '\n';
  }
  for (auto* field : m_cls->get_sfields()) {
    m_hash = 0;
    hash(field);
    ofs << "sfield " << show(field) << " #" << hash_to_string(m_hash) << '\n';
  }

  for (auto* method : m_cls->get_dmethods()) {
    m_hash = 0;
    hash(method);
    ofs << "dmethod " << show(method) << " " << get_hash() << '\n';
  }
  for (auto* method : m_cls->get_vmethods()) {
    m_hash = 0;
    hash(method);
    ofs << "vmethod " << show(method) << " " << get_hash() << '\n';
  }
}

DexHash DexMethodImpl::run() {
  const auto* code = m_method->get_code();
  if (code != nullptr) {
    hash(code);
  }
  // Include the method prototype in code_hash so that methods with different
  // signatures are never considered identical.
  // m_hash is 0 here: it starts at 0 and hash(IRCode*) saves/restores it.
  hash(m_method->get_proto());
  boost::hash_combine(m_code_hash, m_hash);
  return DexHash{m_positions_hash, m_registers_hash, m_code_hash, 0};
}

} // namespace

std::string hash_to_string(size_t hash) {
  std::ostringstream result;
  result << std::hex << std::setfill('0') << std::setw(sizeof(size_t) * 2)
         << hash;
  return result.str();
}

DexHash DexScopeHasher::run() {
  UnorderedMap<DexClass*, size_t> class_indices;
  walk::classes(m_scope, [&](DexClass* cls) {
    class_indices.emplace(cls, class_indices.size());
  });
  std::vector<size_t> class_positions_hashes(class_indices.size());
  std::vector<size_t> class_registers_hashes(class_indices.size());
  std::vector<size_t> class_code_hashes(class_indices.size());
  std::vector<size_t> class_signature_hashes(class_indices.size());
  walk::parallel::classes(m_scope, [&](DexClass* cls) {
    DexClassImpl class_hasher(cls);
    DexHash class_hash = class_hasher.run();
    auto index = class_indices.at(cls);
    class_positions_hashes.at(index) = class_hash.positions_hash;
    class_registers_hashes.at(index) = class_hash.registers_hash;
    class_code_hashes.at(index) = class_hash.code_hash;
    class_signature_hashes.at(index) = class_hash.signature_hash;
  });

  return DexHash{boost::hash_value(class_positions_hashes),
                 boost::hash_value(class_registers_hashes),
                 boost::hash_value(class_code_hashes),
                 boost::hash_value(class_signature_hashes)};
}

struct DexClassHasher::Fwd final {
  DexClassImpl impl;

  explicit Fwd(DexClass* cls) : impl(cls) {}

  DexHash run() { return impl.run(); }
  void print(std::ostream& os) { impl.print(os); }
};

DexClassHasher::DexClassHasher(DexClass* cls)
    : m_fwd(std::make_unique<Fwd>(cls)) {}
DexClassHasher::~DexClassHasher() = default; // For forwarding.

DexHash DexClassHasher::run() { return m_fwd->run(); }

void DexClassHasher::print(std::ostream& os) { m_fwd->print(os); }

void print_classes(std::ostream& output, const Scope& classes) {
  UnorderedMap<DexClass*, std::stringstream> class_strs;
  walk::classes(classes, [&](DexClass* cls) {
    class_strs.emplace(cls, std::stringstream());
  });
  walk::parallel::classes(classes, [&](DexClass* cls) {
    DexClassHasher(cls).print(class_strs.at(cls));
  });
  walk::classes(classes,
                [&](DexClass* cls) { output << class_strs.at(cls).rdbuf(); });
}

struct DexMethodHasher::Fwd final {
  DexMethodImpl impl;

  explicit Fwd(const DexMethod* m) : impl(m) {}

  DexHash run() { return impl.run(); }
};

DexMethodHasher::DexMethodHasher(const DexMethod* method)
    : m_fwd(std::make_unique<Fwd>(method)) {}
DexMethodHasher::~DexMethodHasher() = default;

DexHash DexMethodHasher::run() { return m_fwd->run(); }

} // namespace hashing

std::ostream& operator<<(std::ostream& os, const hashing::DexHash& hash) {
  os << "(P#" << hashing::hash_to_string(hash.positions_hash) << ", R#"
     << hashing::hash_to_string(hash.registers_hash) << ", C#"
     << hashing::hash_to_string(hash.code_hash) << ", S#"
     << hashing::hash_to_string(hash.signature_hash) << ")";
  return os;
}
