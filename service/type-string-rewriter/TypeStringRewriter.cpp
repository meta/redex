/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "TypeStringRewriter.h"

#include "ControlFlow.h"
#include "Debug.h"
#include "DexUtil.h"
#include "Trace.h"
#include "TypeUtil.h"
#include "Walkers.h"

namespace {

/* In Signature annotations, parameterized types of the form Foo<Bar> get
 * represented as the strings
 *   "Lcom/baz/Foo" "<" "Lcom/baz/Bar;" ">"
 *   or
 *   "Lcom/baz/Foo<" "Lcom/baz/Bar;" ">"
 *
 * Note that "Lcom/baz/Foo" lacks a trailing semicolon.
 * Signature annotations suck.
 *
 * This method transforms the input to the form expected by the alias map:
 *   "Lcom/baz/Foo;"
 * looks that up in the map, then transforms back to the form of the input.
 */
const DexString* lookup_signature_annotation(
    const rewriter::TypeStringMap& mapping, const DexString* anno) {
  bool has_bracket = false;
  bool added_semicolon = false;
  std::string anno_str = anno->str_copy();

  // anno_str is some arbitrary segment of a full signature. We rely on standard
  // dexer behavior that keeps types mostly-intact.

  // We first need to filter at least "<" to avoid undefined behavior below.
  // Take the opportunity to aim for object types and try a simplistic test
  // that our assumptions about how signatures are broken up around arrays
  // are correct.
  redex_assert(!anno_str.empty());
  auto is_object_array = [&]() {
    if (anno_str[0] != '[') {
      return false;
    }
    for (size_t i = 1; i < anno_str.length(); ++i) {
      char c = anno_str[i];
      if (c == '[') {
        continue;
      }
      return c == 'L';
    }
    return false;
  };
  assert_log(!is_object_array(), "%s", anno_str.c_str());
  if (anno_str[0] != 'L') {
    return nullptr;
  }
  // anno_str now likely looks like one of these:
  // Lcom/baz/Foo<
  // Lcom/baz/Foo;
  // Lcom/baz/Foo
  if (anno_str.back() == '<') {
    anno_str.pop_back();
    has_bracket = true;
  }
  // anno_str likely looks like one of these:
  // Lcom/baz/Foo;
  // Lcom/baz/Foo
  if (anno_str.back() != ';') {
    anno_str.push_back(';');
    added_semicolon = true;
  }
  // anno_str likely looks like this:
  // Lcom/baz/Foo;

  // Use get_string because if it's in the map, then it must also already exist
  const auto* transformed_anno = DexString::get_string(anno_str);
  if (transformed_anno == nullptr) {
    return nullptr;
  }
  const auto* obfu = mapping.get_new_type_name(transformed_anno);
  if (obfu == nullptr) {
    return nullptr;
  }
  if (!added_semicolon && !has_bracket) {
    return obfu;
  }
  // We need to transform back to the old_name format of the input
  std::string obfu_str = obfu->str_copy();
  if (added_semicolon) {
    always_assert(obfu_str.back() == ';');
    obfu_str.pop_back();
  }
  if (has_bracket) {
    always_assert(obfu_str.back() != '<');
    obfu_str.push_back('<');
  }
  return DexString::make_string(obfu_str);
}

uint32_t get_array_level(const DexString* name) {
  uint32_t level = 0;
  for (const char c : name->str()) {
    if (c != '[') {
      break;
    }
    ++level;
  }
  return level;
}

const DexString* make_array(const DexString* name, uint32_t level) {
  std::string array;
  array.reserve(name->size() + level + 1);
  array.append(level, '[');
  array.append(name->str());
  return DexString::make_string(array);
}
} // namespace

namespace rewriter {

TypeStringMap::TypeStringMap(
    const UnorderedMap<const DexType*, DexType*>& type_mapping) {
  for (const auto& pair : UnorderedIterable(type_mapping)) {
    add_type_name(pair.first->get_name(), pair.second->get_name());
  }
}

void TypeStringMap::add_type_name(const DexString* old_name,
                                  const DexString* new_name) {
  always_assert(old_name && new_name);
  m_type_name_map[old_name] = new_name;
  if (old_name->str()[0] != '[') {
    return;
  }
  // If old_name is an array, we store the mapping for the component type of the
  // arrays.
  uint32_t old_level = get_array_level(old_name);
  uint32_t new_level = get_array_level(new_name);
  always_assert(old_level == new_level);
  old_name = DexString::make_string(old_name->c_str() + old_level);
  new_name = DexString::make_string(new_name->c_str() + new_level);
  m_type_name_map[old_name] = new_name;
}

const DexString* TypeStringMap::get_new_type_name(
    const DexString* old_name) const {
  auto it = m_type_name_map.find(old_name);
  if (it != m_type_name_map.end()) {
    return it->second;
  }
  auto level = get_array_level(old_name);
  if (level == 0) {
    return nullptr;
  }
  old_name = DexString::get_string(old_name->c_str() + level);
  if (old_name == nullptr) {
    return nullptr;
  }
  it = m_type_name_map.find(old_name);
  if (it != m_type_name_map.end()) {
    return make_array(it->second, level);
  }
  return nullptr;
}

void rewrite_dalvik_annotation_signature(const Scope& scope,
                                         const TypeStringMap& mapping) {
  DexType* dalviksig = type::dalvik_annotation_Signature();
  walk::parallel::annotations(scope, [&](DexAnnotation* anno) {
    if (anno->type() != dalviksig) {
      return;
    }
    const auto& elems = anno->anno_elems();
    for (const auto& elem : elems) {
      const auto& ev = elem.encoded_value;
      if (ev->evtype() != DEVT_ARRAY) {
        continue;
      }
      auto* arrayev = dynamic_cast<DexEncodedValueArray*>(ev.get());
      auto const& evs = arrayev->evalues();
      for (auto& strev : *evs) {
        if (strev->evtype() != DEVT_STRING) {
          continue;
        }
        auto* stringev = dynamic_cast<DexEncodedValueString*>(strev.get());
        const auto* old_str = stringev->string();
        const auto* new_str = lookup_signature_annotation(mapping, old_str);
        if (new_str != nullptr) {
          TRACE(RENAME, 5, "Rewriting Signature from '%s' to '%s'",
                old_str->c_str(), new_str->c_str());
          stringev->string(new_str);
        }
      }
    }
  });
}

uint32_t rewrite_string_literal_instructions(const Scope& scope,
                                             const TypeStringMap& mapping) {
  std::atomic<uint32_t> total_updates(0);
  walk::parallel::code(scope, [&](DexMethod* /*meth*/, IRCode& code) {
    always_assert(code.cfg_built());
    auto& cfg = code.cfg();
    for (const auto& mie : InstructionIterable(cfg)) {
      auto* insn = mie.insn;
      if (insn->opcode() != OPCODE_CONST_STRING) {
        continue;
      }
      const auto* old_str = insn->get_string();
      // An array name such as "[Lcom.foo.Bar;" is a valid class name even
      // when the array type itself appears nowhere else in the program.
      if (java_names::get_element_type_from_external_name(old_str->str()) ==
          nullptr) {
        continue;
      }
      const auto* internal_str = DexString::make_string(
          java_names::external_to_internal(old_str->str()));
      const auto* new_type_name = mapping.get_new_type_name(internal_str);
      if (new_type_name == nullptr) {
        continue;
      }
      const auto* new_str = DexString::make_string(
          java_names::internal_to_external(new_type_name->str()));
      insn->set_string(new_str);
      total_updates++;
      TRACE(RENAME,
            5,
            "Replace const-string from %s to %s",
            old_str->c_str(),
            new_str->c_str());
    }
  });
  return total_updates.load();
}

} // namespace rewriter
