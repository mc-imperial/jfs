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
#include "jfs/FuzzingCommon/LibFuzzerOptions.h"

namespace jfs {
namespace fuzzingCommon {

LibFuzzerOptions::LibFuzzerOptions()
    : seed(1), mutationDepth(5), crossOver(true), maxLength(0), useCmp(false),
      printFinalStats(true), reduceInputs(false),
      defaultMutationsResizeInput(true), handleSIGABRT(true),
      handleSIGBUS(true), handleSIGFPE(true), handleSIGILL(true),
      handleSIGINT(true), handleSIGSEGV(true), handleSIGXFSZ(true),
      addAllZeroMaxLengthSeed(true), addAllOneMaxLengthSeed(true) {}
} // namespace fuzzingCommon
} // namespace jfs
