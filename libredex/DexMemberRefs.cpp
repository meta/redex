/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "DexMemberRefs.h"

#include "Debug.h"
#include "DexUtil.h"
#include "Show.h"
#include "TypeUtil.h"

#include <sstream>

namespace dex_member_refs {

template <typename T>
static size_t expect(std::string_view s,
                     const T& needle,
                     size_t start_pos = 0) {
  auto pos = s.find(needle, start_pos);
  auto error_fn = [&]() {
    std::ostringstream ss;
    ss << "Could not find \"" << needle << "\" in \"" << s << "\"";
    return ss.str();
  };
  always_assert_log(pos != std::string::npos, "%s", error_fn().c_str());
  return pos;
}

FieldDescriptorTokens parse_field(std::string_view s) {
  auto cls_end = expect(s, '.');
  auto name_start = cls_end + 1;
  auto name_end = expect(s, ':', name_start);
  auto type_start = name_end + 1;
  always_assert_log(type_start < s.size(), "No type found");

  FieldDescriptorTokens fdt;
  fdt.cls = s.substr(0, cls_end);
  fdt.name = s.substr(name_start, name_end - name_start);
  fdt.type = s.substr(type_start);
  return fdt;
}

namespace {

std::vector<std::string_view> split_args(std::string_view args) {
  std::vector<std::string_view> ret;
  auto begin = size_t{0};
  while (begin < args.length()) {
    auto ch = args[begin];
    auto end = begin + 1;
    if (ch == '[') {
      while (args[end] == '[') {
        ++end;
      }
      ch = args[end];
      ++end;
    }
    if (ch == 'L') {
      auto semipos = args.find(';', end);
      always_assert_log(semipos != std::string::npos,
                        "Unterminated class name in %s",
                        std::string(args).c_str());
      end = semipos + 1;
    }
    ret.emplace_back(args.substr(begin, end - begin));
    begin = end;
  }
  return ret;
}

} // namespace

ProtoDescriptorTokens parse_proto(std::string_view s) {
  always_assert_log(!s.empty() && s[0] == '(', "No argument list found");
  auto args_end = expect(s, ')', 1);
  auto rtype_start = args_end + 1;
  always_assert_log(rtype_start < s.size(), "No return type found");

  ProtoDescriptorTokens pdt;
  pdt.args = split_args(s.substr(1, args_end - 1));
  pdt.rtype = s.substr(rtype_start);
  return pdt;
}

template <bool kCheckFormat>
MethodDescriptorTokens parse_method(std::string_view s) {
  auto cls_end = expect(s, '.');
  auto name_start = cls_end + 1;
  auto name_end = expect(s, ":(", name_start);
  auto pdt = parse_proto(s.substr(name_end + 1));

  MethodDescriptorTokens mdt;
  mdt.cls = s.substr(0, cls_end);
  mdt.name = s.substr(name_start, name_end - name_start);
  mdt.args = std::move(pdt.args);
  mdt.rtype = pdt.rtype;
  if (kCheckFormat) {
    // Macros are ugly, but it will print nicer since asserts are macros, too.
#define context_assert(e, local_ctx) \
  always_assert_log(e, "Invalid: %s (%s)", SHOW(local_ctx), SHOW(s));

    context_assert(type::is_valid(mdt.cls), mdt.cls);
    // Class must not be a primitive.
    context_assert(mdt.cls.at(0) == 'L' || mdt.cls.at(0) == '[', mdt.cls);

    context_assert(!mdt.name.empty(), mdt.name);
    // Name must be a valid identifier.
    context_assert(is_valid_identifier(mdt.name), mdt.name);

    for (std::string_view t : mdt.args) {
      context_assert(type::is_valid(t), t);
    }
    context_assert(type::is_valid(mdt.rtype), mdt.rtype);
  }
  return mdt;
}
template MethodDescriptorTokens parse_method<false>(std::string_view);
template MethodDescriptorTokens parse_method<true>(std::string_view);

} // namespace dex_member_refs
