//===----------------------------------------------------------------------===//
//
//                        JFS - The JIT Fuzzing Solver
//
// Copyright 2017-2018 Daniel Liew
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#include "jfs/FuzzingCommon/CmdLine/LibFuzzerOptionsBuilder.h"
#include "jfs/FuzzingCommon/CommandLineCategory.h"
#include "llvm/Support/CommandLine.h"

using namespace jfs::fuzzingCommon;

namespace {
// Only provide options for fields that are intended to be modified
// publicly.

llvm::cl::opt<unsigned> FuzzerSeed(
    "libfuzzer-seed",
    llvm::cl::desc(
        "LibFuzzer random seed (0 means pick a random seed) (default: 1)"),
    llvm::cl::init(1), llvm::cl::cat(jfs::fuzzingCommon::CommandLineCategory));

llvm::cl::opt<unsigned> MutationDepth(
    "libfuzzer-mutation-depth",
    llvm::cl::desc("Number of mutations to apply to an input (default: 5)"),
    llvm::cl::init(5), llvm::cl::cat(jfs::fuzzingCommon::CommandLineCategory));

llvm::cl::opt<bool>
    CrossOver("libfuzzer-crossover",
              llvm::cl::desc("Enable crossover mutation (default: true)"),
              llvm::cl::init(true),
              llvm::cl::cat(jfs::fuzzingCommon::CommandLineCategory));

llvm::cl::opt<bool> PrintFinalStats(
    "libfuzzer-print-final-stats",
    llvm::cl::desc("Print LibFuzzer stats on exit (default: true)"),
    llvm::cl::init(true),
    llvm::cl::cat(jfs::fuzzingCommon::CommandLineCategory));

llvm::cl::opt<bool>
    AddAllZerosSeed("libfuzzer-zeros-seed",
                    llvm::cl::desc("Add an appropriately sized seed of all "
                                   "zeros to the corpus (default: true)"),
                    llvm::cl::init(true),
                    llvm::cl::cat(jfs::fuzzingCommon::CommandLineCategory));

llvm::cl::opt<bool>
    AddAllOnesSeed("libfuzzer-oness-seed",
                   llvm::cl::desc("Add an appropriately sized seed of all "
                                  "ones to the corpus (default: true)"),
                   llvm::cl::init(true),
                   llvm::cl::cat(jfs::fuzzingCommon::CommandLineCategory));

llvm::cl::opt<bool> DefaultMutationsResizeInput(
    "libfuzzer-default-mutations-resize-input",
    llvm::cl::desc("LibFuzzer mutations resize input (default: false)"),
    llvm::cl::init(false),
    llvm::cl::cat(jfs::fuzzingCommon::CommandLineCategory));
}

namespace jfs {
namespace fuzzingCommon {
namespace cl {

std::unique_ptr<jfs::fuzzingCommon::LibFuzzerOptions>
buildLibFuzzerOptionsFromCmdLine() {
  std::unique_ptr<jfs::fuzzingCommon::LibFuzzerOptions> libFuzzerOptions(
      new jfs::fuzzingCommon::LibFuzzerOptions());

  // Fuzzer seed
  libFuzzerOptions->seed = FuzzerSeed;

  // Mutationd depth
  libFuzzerOptions->mutationDepth = MutationDepth;

  // Crossover
  libFuzzerOptions->crossOver = CrossOver;

  // LibFuzzer statistics printing
  libFuzzerOptions->printFinalStats = PrintFinalStats;

  // In our context it doesn't make sense to reduce inputs
  // because our inputs are always of fixed size.
  libFuzzerOptions->reduceInputs = false;

  libFuzzerOptions->defaultMutationsResizeInput = DefaultMutationsResizeInput;

  // All zeros seed
  libFuzzerOptions->addAllZeroMaxLengthSeed = AddAllZerosSeed;

  // All ones seed
  libFuzzerOptions->addAllOneMaxLengthSeed = AddAllOnesSeed;

  return libFuzzerOptions;
}
}
}
}
