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
#include "jfs/FuzzingCommon/FuzzingAnalysisInfo.h"

namespace jfs {
namespace fuzzingCommon {

FuzzingAnalysisInfo::FuzzingAnalysisInfo()
    : equalityExtraction(std::make_shared<EqualityExtractionPass>()) {}

FuzzingAnalysisInfo::~FuzzingAnalysisInfo() {}

void FuzzingAnalysisInfo::addTo(jfs::transform::QueryPassManager &pm) {
  // TODO: Enforce that this can only be called once

  // Look for equalities, extract them and remove them from the constraints
  pm.add(equalityExtraction);

  // TODO: Add pass to extract free variables and assign them a position
  // in the fuzzing buffer.
}
}
}
