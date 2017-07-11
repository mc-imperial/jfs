//===----------------------------------------------------------------------===//
//
//                        JFS - The JIT Fuzzing Solver
//
// Copyright 2017 Daniel Liew
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#ifndef JFS_FUZZING_COMMON_LIBFUZZER_OPTIONS_H
#define JFS_FUZZING_COMMON_LIBFUZZER_OPTIONS_H
#include <stdint.h>
#include <string>

namespace jfs {
namespace fuzzingCommon {

struct LibFuzzerOptions {
  uint64_t seed;          // Corresponds to `-seed=<N>` option
  uint64_t mutationDepth; // Corresponds to `-mutate_depth=<N>`
  bool crossOver;         // Corresponds to `-cross_over` option
  uint64_t maxLength;     // Corresponds to `-max_len=<N>` option (bytes).

  bool addAllZeroMaxLengthSeed;

  std::string targetBinary;
  std::string artifactDir;
  std::string corpusDir;

  // TODO: We should support LibFuzzer jobs/workers. This
  // will require a vector of seeds rather than a single seed
  LibFuzzerOptions();
};
}
}
#endif
