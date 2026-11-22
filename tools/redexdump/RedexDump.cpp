/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "RedexDump.h"
#include <getopt.h>
#include <stdio.h>
#include <stdlib.h>

#include "Formatters.h"
#include "PrintUtil.h"

static const char ddump_usage_string[] =
    "ReDex, DEX Dump tool\n"
    "\nredexdump pretty prints content of a dexfile. "
    "By default only prints the header\n"
    "\n"
    "Usage:\n"
    "\tredump [-h | --all | [[-string] [-type] [-proto] [-field] [-meth] "
    "[-clsdef] [-clsdata] [-code] [-enarr] [-anno]] [-clean]"
    " <classes.dex>...\n"
    "\n<classes.dex>: path to a dex file (not an APK!)\n"
    "\noptions:\n"
    "--h: help summary\n"
    "\nsections to print:\n"
    "-a, --all: print all items in all sections\n"
    "-s, --string: print items in the string id section\n"
    "-S, --stringdata: print string section (pointee of string ids)\n"
    "-t, --type: print items in the type id section\n"
    "-p, --proto: print items in the proto id section\n"
    "-f, --field: print items in the field id section\n"
    "-m, --meth: print items in the method id section\n"
    "-h, --methodhandle: print items in the methodhandle section\n"
    "-k, --callsite: print items in the callsite section\n"
    "-c, --clsdef: print items in the class def id section\n"
    "-C, --clsdata: print items in the class data section\n"
    "-x, --code: print items in the code data section\n"
    "-e, --enarr: print items in the encoded array section\n"
    "-A, --anno: print items in the annotation section\n"
    "-d, --debug: print debug info items in the data section\n"
    "-D, --ddebug=<addr>: disassemble debug info item at <addr>\n"
    "\n"
    "printing options:\n"
    "--clean: suppress indices and offsets\n"
    "--no-headers: suppress headers\n"
    "--raw: print all bytes, even control characters\n";

int main(int argc, char* argv[]) {

  bool all = false;
  bool string = false;
  bool stringdata = false;
  bool type = false;
  bool proto = false;
  bool field = false;
  bool meth = false;
  bool methodhandle = false;
  bool callsite = false;
  bool clsdef = false;
  bool clsdata = false;
  bool code = false;
  bool enarr = false;
  bool anno = false;
  bool redexdump_debug = false;
  uint32_t ddebug_offset = 0;
  int no_headers = 0;

  int c;
  static const struct option options[] = {
      {"all", no_argument, nullptr, 'a'},
      {"string", no_argument, nullptr, 's'},
      {"stringdata", no_argument, nullptr, 'S'},
      {"type", no_argument, nullptr, 't'},
      {"proto", no_argument, nullptr, 'p'},
      {"field", no_argument, nullptr, 'f'},
      {"meth", no_argument, nullptr, 'm'},
      {"callsite", no_argument, nullptr, 'k'},
      {"methodhandle", no_argument, nullptr, 'H'},
      {"clsdef", no_argument, nullptr, 'c'},
      {"clsdata", no_argument, nullptr, 'C'},
      {"code", no_argument, nullptr, 'x'},
      {"enarr", no_argument, nullptr, 'e'},
      {"anno", no_argument, nullptr, 'A'},
      {"debug", no_argument, nullptr, 'd'},
      {"ddebug", required_argument, nullptr, 'D'},
      {"clean", no_argument, (int*)&clean, 1},
      {"raw", no_argument, (int*)&raw, 1},
      {"escape", no_argument, (int*)&escape, 1},
      {"no-headers", no_argument, &no_headers, 1},
      {"help", no_argument, nullptr, 'h'},
      {nullptr, 0, nullptr, 0},
  };

  while ((c = getopt_long(argc, argv, "asStpfmcCxeAdD:h", &options[0],
                          nullptr)) != -1) {
    switch (c) {
    case 'a':
      all = true;
      break;
    case 's':
      string = true;
      break;
    case 'S':
      stringdata = true;
      break;
    case 't':
      type = true;
      break;
    case 'p':
      proto = true;
      break;
    case 'f':
      field = true;
      break;
    case 'm':
      meth = true;
      break;
    case 'H':
      methodhandle = true;
      break;
    case 'k':
      callsite = true;
      break;
    case 'c':
      clsdef = true;
      break;
    case 'C':
      clsdata = true;
      break;
    case 'x':
      code = true;
      break;
    case 'e':
      enarr = true;
      break;
    case 'A':
      anno = true;
      break;
    case 'd':
      redexdump_debug = true;
      break;
    case 'D':
      sscanf(optarg, "%x", &ddebug_offset);
      break;
    case 'h':
      puts(ddump_usage_string);
      return 0;
    case '?':
      return 1; // getopt_long has printed an error
    case 0:
      // we're handling a long-only option
      break;
    default:
      abort();
    }
  }

  if (optind == argc) {
    fprintf(stderr, "%s: no dex files given; use -h for help\n", argv[0]);
    return 1;
  }

  while (optind < argc) {
    const char* dexfile = argv[optind++];
    ddump_data rd;
    open_dex_file(dexfile, &rd);
    if (no_headers == 0) {
      redump(format_map(&rd).c_str());
    }
    if (string || all) {
      dump_strings(&rd, no_headers == 0);
    }
    if (stringdata || all) {
      dump_stringdata(&rd, no_headers == 0);
    }
    if (type || all) {
      dump_types(&rd);
    }
    if (proto || all) {
      dump_protos(&rd, no_headers == 0);
    }
    if (field || all) {
      dump_fields(&rd, no_headers == 0);
    }
    if (meth || all) {
      dump_methods(&rd, no_headers == 0);
    }
    if (methodhandle || all) {
      dump_methodhandles(&rd, no_headers == 0);
    }
    if (callsite || all) {
      dump_callsites(&rd, no_headers == 0);
    }
    if (clsdef || all) {
      dump_clsdefs(&rd, no_headers == 0);
    }
    if (clsdata || all) {
      dump_clsdata(&rd, no_headers == 0);
    }
    if (code || all) {
      dump_code(&rd);
    }
    if (enarr || all) {
      dump_enarr(&rd);
    }
    if (anno || all) {
      dump_anno(&rd);
    }

    if (redexdump_debug || all) {
      dump_debug(&rd);
    }
    if (ddebug_offset != 0) {
      disassemble_debug(&rd, ddebug_offset);
    }
    fprintf(stdout, "\n");
    fflush(stdout);
  }

  return 0;
}
