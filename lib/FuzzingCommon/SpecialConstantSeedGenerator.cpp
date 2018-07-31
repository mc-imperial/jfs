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

#include "jfs/FuzzingCommon/SpecialConstantSeedGenerator.h"
#include "jfs/FuzzingCommon/SeedManager.h"

namespace jfs {
namespace fuzzingCommon {

void SpecialConstantSeedGenerator::preGenerationCallBack(SeedManager& sm) {
  auto query = sm.getCurrentQuery();

}

bool SpecialConstantSeedGenerator::writeSeed(SeedManager& sm) {

}

bool SpecialConstantSeedGenerator::empty() const { return true; }

} // namespace fuzzingCommon
} // namespace jfs
