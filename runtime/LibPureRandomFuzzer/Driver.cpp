//===----------------------------------------------------------------------===//
//
//                        JFS - The JIT Fuzzing Solver
//
// Copyright 2018 J. Ryan Stinnett
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//

#include "Driver.h"

#include "API.h"
#include "Log.h"
#include "TestInput.h"
#include <cassert>
#include <cstdio>
#include <limits>
#include <string>
#include <vector>

namespace prf {

struct Options {
#define PRF_OPTION(_, type, name, value)                                       \
  type name = value;
#include "Options.def"
#undef PRF_OPTION
};

int Driver(int& argc, char**& argv) {
  const Options opts = BuildOptions(argc, argv);

  if (!opts.dataLength) {
    Debug("Test data length currently required");
    exit(1);
  }
  TestInput testInput(opts.dataLength);
  uint maxRuns = std::numeric_limits<uint>::max();
  if (opts.maxRuns >= 0) {
    maxRuns = opts.maxRuns;
  }
  for (uint run = 0; run < maxRuns; run++) {
    testInput.generate();
    LLVMFuzzerTestOneInput(testInput.get(), testInput.size());
  }

  return 0;
}

Options BuildOptions(int& argc, char**& argv) {
  std::vector<std::string> args(argv + 1, argv + argc);
  assert(args.size() == argc - 1);

  Options opts;

  for (auto arg : args) {
    int equals = arg.find('=');
    if (arg[0] != '-' || equals < 2) {
      Debug("Ignored unknown option: ", arg);
      continue;
    }
    auto flagInput = arg.substr(1, equals - 1);
    auto valueInput = arg.substr(equals + 1);
#define PRF_OPTION(flag, type, name, _)                                        \
    if (flagInput == #flag) {                                                  \
      if (#type == "int") {                                                    \
        opts.name = stoi(valueInput);                                          \
      }                                                                        \
      if (#type == "uint") {                                                   \
        opts.name = stoul(valueInput);                                         \
      }                                                                        \
      Debug("opts.", #name, " = ", valueInput);                                \
      continue;                                                                \
    }
#include "Options.def"
#undef PRF_OPTION
    Debug("Ignored unknown option: ", arg);
  }

  return opts;
}

} // prf