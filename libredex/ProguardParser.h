/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include <cstdint>
#include <iosfwd>
#include <string>
#include <vector>

#include "ProguardConfiguration.h"

namespace keep_rules {
namespace proguard_parser {

struct CommandDiagnostic {
  std::string command;
  std::string filename;
  uint32_t line{0};
  std::string context;
};

struct Diagnostics {
  std::vector<CommandDiagnostic> skipped_commands;
  std::vector<CommandDiagnostic> unknown_commands;
};

struct Stats {
  size_t unknown_tokens{0};
  size_t parse_errors{0};
  size_t unimplemented{0};
  size_t skipped_if_rules{0};
  size_t unknown_commands{0};

  Stats& operator+=(const Stats& rhs) {
    unknown_tokens += rhs.unknown_tokens;
    parse_errors += rhs.parse_errors;
    unimplemented += rhs.unimplemented;
    skipped_if_rules += rhs.skipped_if_rules;
    unknown_commands += rhs.unknown_commands;
    return *this;
  }
};

Stats parse_file(const std::string& filename, ProguardConfiguration* pg_config);
Stats parse_file(const std::string& filename,
                 ProguardConfiguration* pg_config,
                 Diagnostics* diagnostics);
Stats parse(std::istream& config,
            ProguardConfiguration* pg_config,
            const std::string& filename = "");
Stats parse(std::istream& config,
            ProguardConfiguration* pg_config,
            const std::string& filename,
            Diagnostics* diagnostics);

/*
 * Typically used to remove keep rules that we wish to apply only to optimizers
 * that run prior to invoking Redex (e.g. ProGuard or R8).
 */
size_t remove_default_blocklisted_rules(ProguardConfiguration* pg_config);

size_t remove_blocklisted_rules(const std::string& rules,
                                ProguardConfiguration* pg_config);

size_t identify_blanket_native_rules(ProguardConfiguration* pg_config);

} // namespace proguard_parser
} // namespace keep_rules
