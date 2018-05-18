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
#include "Signals.h"
#include "TestInput.h"
#include <cassert>
#include <chrono>
#include <cstdio>
#include <limits>
#include <string>
#include <vector>

namespace prf {

static Options gOpts;

typedef std::chrono::system_clock::time_point time_point;
static const time_point gStartTime = std::chrono::system_clock::now();

static uint gRuns;

static API* gAPI;

int Driver(int& argc, char**& argv) {
  gOpts = BuildOptions(argc, argv);

  if (!gOpts.dataLength) {
    Debug("Test data length currently required");
    exit(1);
  }
  TestInput testInput(gOpts.dataLength, gOpts.seed);
  uint maxRuns = std::numeric_limits<uint>::max();
  if (gOpts.maxRuns >= 0) {
    maxRuns = gOpts.maxRuns;
  }

  // Set all appropriate signal and timer handlers
  Signals signals(gOpts);

  // Load any optional functions
  gAPI = new API();

  TestOneInputT* runTest = gAPI->TestOneInput;
  for (gRuns = 0; gRuns < maxRuns; gRuns++) {
    testInput.generate();
    runTest(testInput.get(), testInput.size());
  }

  PrintFinalStats();
  gAPI->AtExit();
  return 0;
}

void PrintFinalStats() {
  if (!gOpts.printFinalStats) {
    return;
  }
  Print("Runs: ", gRuns);
  std::chrono::duration<float> elapsed =
      std::chrono::system_clock::now() - gStartTime;
  Print("Elapsed Time: ", elapsed.count(), "s");
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
      if (#type == "bool") {                                                   \
        opts.name = !!stoul(valueInput);                                       \
      }                                                                        \
      Debug("opts.", #name, " = ", opts.name);                                 \
      continue;                                                                \
    }
#include "Options.def"
#undef PRF_OPTION
    Debug("Ignored unknown option: ", arg);
  }

  return opts;
}

void AbortHandler(int sig) {
  Debug("Abort occurred!");
  PrintFinalStats();
  gAPI->AtExit();
  exit(gOpts.errorExitCode);
}

void TimeoutHandler(int sig) {
  Debug("Timeout occurred!");
  PrintFinalStats();
  gAPI->AtExit();
  exit(gOpts.timeoutExitCode);
}

} // prf