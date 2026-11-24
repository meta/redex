/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <stdio.h>
#include <string>
#include <string_view>

#include "Debug.h"
#include "Show.h"
#include "SingleImplDefs.h"
#include "TypeUtil.h"

namespace {

bool is_digit(char c) { return c >= '0' && c <= '9'; }

bool is_alpha(char c) {
  return (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z');
}

bool is_word(char c) { return is_digit(c) || is_alpha(c) || c == '_'; }

// ".*\\$\\d+;"
bool is_anonymous(std::string_view name) {
  for (uint32_t i = 0; i < name.length(); ++i) {
    if (name[i] != '$') {
      continue;
    }

    uint32_t j = i + 1;
    for (; j < name.length(); ++j) {
      if (is_digit(name[j])) {
        continue;
      }
    }

    if (j == i + 1) {
      continue;
    }
    if (name[j] == ';') {
      fprintf(stderr, "'%.*s' is anonymous\n", (int)name.size(), name.data());
      return true;
    }
  }

  return false;
}

// ".*\\$\\w+;"
bool is_nested(std::string_view name) {
  for (uint32_t i = 0; i < name.length(); ++i) {
    if (name[i] != '$') {
      continue;
    }

    uint32_t j = i + 1;
    for (; j < name.length(); ++j) {
      if (is_word(name[j])) {
        continue;
      }
    }

    if (j == i + 1) {
      continue;
    }
    if (name[j] == ';') {
      fprintf(stderr, "'%.*s' is nested\n", (int)name.size(), name.data());
      return true;
    }
  }

  return false;
}

void breakup_by_package(SingleImpls& single_impls) {
  struct PackageBreakUp {
    std::string package;
    uint32_t count;
    int package_num;
  };
  std::vector<PackageBreakUp> by_package;
  uint32_t no_package_types = 0;
  for (auto const& intf_it : UnorderedIterable(single_impls)) {
    const auto* const intf_name = intf_it.first->get_name()->c_str();
    auto* ptr = const_cast<char*>(intf_name);
    if (*ptr != 'L') {
      fprintf(stderr, "bad type name %s\n", intf_name);
      continue;
    }
    auto* start = ++ptr;
    int package_num = 0;
    while (*++ptr != 0) {
      if (*ptr == '/') {
        package_num++;
        std::string package = std::string(start, ptr - start);
        const auto& it = std::find_if(
            by_package.begin(),
            by_package.end(),
            [&](const PackageBreakUp& pkg) { return pkg.package == package; });
        if (it == by_package.end()) {
          by_package.emplace_back(PackageBreakUp{package, 1, package_num});
        } else {
          auto& found_package = *it;
          found_package.count++;
        }
      }
    }
    if (package_num == 0) {
      no_package_types++;
    }
  }
  fprintf(stderr, "no package types %u\n", no_package_types);
  fprintf(stderr, "break up by package, %zu packages:\n", by_package.size());
  std::sort(by_package.begin(),
            by_package.end(),
            [](const PackageBreakUp& left, const PackageBreakUp& right) {
              if (left.package_num == right.package_num) {
                return left.count < right.count;
              }
              return left.package_num < right.package_num;
            });
  for (const auto& package_info : by_package) {
    fprintf(stderr,
            "%s (%d) => %u\n",
            package_info.package.c_str(),
            package_info.package_num,
            package_info.count);
  }
}

void class_type_stats(SingleImpls& single_impls) {
  // single impl interface with parent implemented in an anonymous class
  size_t anonymous_count = 0;
  std::ostringstream anonymous;
  // single impl interface with parent implemented in a nested class
  size_t nested_count = 0;
  std::ostringstream nested;
  // single impl interface with parent implemented in top level class
  size_t top_level_count = 0;
  std::ostringstream top_level;
  // single impl interface with no parent implemented in an anonymous class
  size_t anonymous_no_parent_count = 0;
  std::ostringstream anonymous_no_parent;
  // single impl interface with no parent implemented in a nested class
  size_t nested_no_parent_count = 0;
  std::ostringstream nested_no_parent;
  // single impl interface with no parent implemented in top level class
  size_t top_level_no_parent_count = 0;
  std::ostringstream top_level_no_parent;

  for (auto const& intf_it : UnorderedIterable(single_impls)) {
    const auto* name = intf_it.second.cls->get_name()->c_str();
    auto anon = is_anonymous(name);
    auto nested_cls = false;
    if (!anon) {
      nested_cls = is_nested(name);
    }
    const auto& cls = type_class(intf_it.second.cls);
    if (type::is_object(cls->get_super_class()) &&
        cls->get_interfaces()->empty()) {
      if (anon) {
        anonymous_no_parent << "+ " << show(cls) << "\n";
        anonymous_no_parent_count++;
      } else if (nested_cls) {
        nested_no_parent << "+ " << show(cls) << "\n";
        nested_no_parent_count++;
      } else {
        top_level_no_parent << "+ " << show(cls) << "\n";
        top_level_no_parent_count++;
      }
    } else {
      if (anon) {
        anonymous << "+ " << show(cls) << "\n";
        anonymous_count++;
      } else if (nested_cls) {
        nested << "+ " << show(cls) << "\n";
        nested_count++;
      } else {
        top_level << "+ " << show(cls) << "\n";
        top_level_count++;
      }
    }
  }
  fprintf(stderr,
          "anonymous single implemented with no parent count: %zu\n",
          anonymous_no_parent_count);
  fprintf(stderr,
          "nested single implemented with no parent count: %zu\n",
          nested_no_parent_count);
  fprintf(stderr,
          "top level single implemented with no parent count: %zu\n",
          top_level_no_parent_count);
  fprintf(stderr,
          "anonymous single implemented with parent count: %zu\n",
          anonymous_count);
  fprintf(stderr,
          "nested single implemented with parent count: %zu\n",
          nested_count);
  fprintf(stderr,
          "top level single implemented with parent count: %zu\n",
          top_level_count);
  fprintf(stderr, "\n");
  fprintf(stderr,
          "anonymous single implemented with no parent:\n%s",
          anonymous_no_parent.str().c_str());
  fprintf(stderr,
          "nested single implemented with no parent:\n%s",
          nested_no_parent.str().c_str());
  fprintf(stderr,
          "top level single implemented with no parent:\n%s",
          top_level_no_parent.str().c_str());
  fprintf(stderr,
          "anonymous single implemented with parent:\n%s",
          anonymous.str().c_str());
  fprintf(stderr,
          "nested single implemented with parent:\n%s",
          nested.str().c_str());
  fprintf(stderr,
          "top level single implemented with parent:\n%s",
          top_level.str().c_str());
}
} // namespace

void print_stats(SingleImpls& single_impls) {
  // interface stats
  fprintf(
      stderr, "single implemented interface count: %zu\n", single_impls.size());
  for (auto const& intf_it : UnorderedIterable(single_impls)) {
    fprintf(stderr, "+ %s\n", SHOW(intf_it.first));
  }
  if (debug) {
    class_type_stats(single_impls);
    breakup_by_package(single_impls);
  }
}
