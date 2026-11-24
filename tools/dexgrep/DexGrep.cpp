/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <cstdio>
#include <getopt.h> // @donotremove
#include <regex>

#include "DexCommon.h"

void print_usage() {
  fprintf(stderr, "Usage: dexgrep <classname> <dexfile 1> <dexfile 2> ...\n");
}

int main(int argc, char* argv[]) {
  bool files_only = false;
  int c;
  static const struct option options[] = {
      {"files-without-match", no_argument, nullptr, 'l'},
  };
  while ((c = getopt_long(argc, argv, "hl", &options[0], nullptr)) != -1) {
    switch (c) {
    case 'l':
      files_only = true;
      break;
    case 'h':
      print_usage();
      return 0;
    default:
      print_usage();
      return 1;
    }
  }

  if (optind == argc) {
    fprintf(stderr, "%s: no dex files given\n", argv[0]);
    print_usage();
    return 1;
  }

  const char* search_str = argv[optind];
  std::regex re(search_str);

  for (int i = optind + 1; i < argc; ++i) {
    const char* dexfile = argv[i];
    ddump_data rd;
    open_dex_file(dexfile, &rd);

    auto size = rd.dexh->class_defs_size;
    for (uint32_t j = 0; j < size; j++) {
      dex_class_def* cls_def = rd.dex_class_defs + j;
      char* name = dex_string_by_type_idx(&rd, cls_def->typeidx);
      if (std::regex_search(name, re)) {
        if (files_only) {
          printf("%s\n", dexfile);
        } else {
          printf("%s: %s\n", dexfile, name);
        }
      }
    }
  }
}
