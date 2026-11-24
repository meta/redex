/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <boost/filesystem/operations.hpp>
#include <boost/filesystem/path.hpp>

#include <fstream>
#include <map>
#include <memory>
#include <string>
#include <string_view>
#include <vector>

#include "Debug.h"
#include "DexAnnotation.h"
#include "DexDefs.h"

class DexCallSite;
class DexClass;
class DexMethodHandle;
class IRCode;

namespace redex {

using namespace boost::filesystem;

struct TempDir {
  TempDir() = default;
  explicit TempDir(std::string path) : path(std::move(path)), released(false) {}
  TempDir(const TempDir& other) = delete;
  TempDir(TempDir&& other) noexcept
      : path(std::move(other.path)), released{other.released} {
    other.released = true;
  }

  ~TempDir() {
    if (!released) {
      remove_all(path);
    }
  }

  TempDir& operator=(const TempDir& rhs) = delete;
  TempDir& operator=(TempDir&& rhs) noexcept {
    path = std::move(rhs.path);
    released = rhs.released;
    rhs.released = true;
    return *this;
  }

  void release() { released = true; }

  std::string path;
  bool released{true};
};

inline TempDir make_tmp_dir(const char* boost_template_str) {
  auto path = temp_directory_path();
  path += path::preferred_separator;
  path += unique_path(boost_template_str);
  create_directories(path);
  return TempDir(path.string());
}

inline void copy_file(const std::string& from, const std::string& to) {
  std::ifstream src_stream(from, std::ios::binary);
  std::ofstream dest_stream(to, std::ios::binary);
  dest_stream << src_stream.rdbuf();
}

bool are_files_equal(const std::string&, const std::string&);

// Prints the instructions of every method with code, keyed by the method, so
// that code read into different RedexContexts can be compared. The code must
// not have its CFG built.
std::map<std::string, std::vector<std::string>> show_instructions_by_method(
    const std::vector<DexClass*>& classes);

// A method handle of kind `type` for the method or field `ref`, published to
// `g_redex`.
DexMethodHandle* make_method_handle(MethodHandleType type,
                                    std::string_view ref);

// A call site named `method_name` with method type `method_type`, linked by
// the static method `LBoot;.bootstrap` with `args` as its further bootstrap
// arguments, published to `g_redex`. The bootstrap method takes one parameter
// of the matching type for each of `args`.
DexCallSite* make_callsite(
    std::string_view method_name,
    std::string_view method_type,
    std::vector<std::unique_ptr<DexEncodedValue>> args = {});

// S-expressions cannot express call sites, so tests write an `invoke-static`
// in its place. This turns every `invoke-static` in `code` into an
// `invoke-custom` of one new call site, made by `make_callsite` with the given
// arguments, and returns that call site.
DexCallSite* make_invoke_custom(
    IRCode* code,
    std::string_view method_name,
    std::string_view method_type,
    std::vector<std::unique_ptr<DexEncodedValue>> args = {});

// `value` as the subclass `T` of `DexEncodedValue` that it must be.
template <typename T>
const T* encoded_value_as(const DexEncodedValue* value) {
  const auto* result = dynamic_cast<const T*>(value);
  always_assert(result != nullptr);
  return result;
}
} // namespace redex
