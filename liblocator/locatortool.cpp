/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include <cstdlib>
#include <iostream>
#include <vector>

#include <locator.h>

using namespace std;
using namespace facebook;

// clang-format off
void print_usage() {
  cout << "Usage:" << endl;
  cout << "  locatortool d" << endl;
  cout << "  locatortool e [-h|--hex] <class_num> <dex_num> <store_num>" << endl;
  cout << endl;
  cout << endl;
  cout << "  Commands:" << endl;
  cout << "    d              Decode a (raw, not hex) locator string from stdin." << endl;
  cout << "    e              Encode a value" << endl;
  cout << "      -h | --hex   Print a hexdump of the locator instead of the raw string" << endl;
  cout << endl;
}
// clang-format on

int main(int argc, char* argv[]) {
  if (argc < 2) {
    print_usage();
    return 0;
  }

  vector<string> args;
  for (int i = 0; i < argc; i++) {
    args.emplace_back(argv[i]);
  }

  try {
    switch (*argv[1]) {
      case 'd': {
        string locator_str;
        cin >> locator_str;
        Locator locator =
            Locator::decodeBackward(locator_str.c_str() + locator_str.size());
        cout << "class: " << locator.clsnr << endl;
        cout << "dex  : " << locator.dexnr << endl;
        cout << "store: " << locator.strnr << endl;
        break;
      }
      case 'e': {
        int p = 2;
        bool use_hex = args[p] == "-h" || args[p] == "--hex";
        if (use_hex) {
          p++;
        }

        char buf[Locator::encoded_max];
        int clsnr = stoi(args[p++]);
        int dexnr = stoi(args[p++]);
        int strnr = stoi(args[p++]);
        if (!Locator::make(strnr, dexnr, clsnr).encode(buf)) {
          break;
        }
        if (use_hex) {
          for (size_t i = 0; i < strlen(buf) + 1; i++) {
            cout << hex << (int)buf[i] << " ";
          }
          cout << endl;
        } else {
          cout << buf << endl;
        }
        break;
      }
      default: {
        throw 0;
      }
    }
  } catch (...) {
    print_usage();
  }

  return 0;
}
