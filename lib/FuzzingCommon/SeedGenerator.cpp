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
#include "jfs/FuzzingCommon/SeedGenerator.h"
#include "jfs/FuzzingCommon/SeedManager.h"

namespace jfs {
namespace fuzzingCommon {

void SeedGenerator::preGenerationCallBack(SeedManager& sm) {}

SeedGenerator::SeedGenerator(llvm::StringRef name) : name(name) {}

SeedGenerator::~SeedGenerator() {}

// AllBytesEqualGenerator

AllBytesEqualGenerator::AllBytesEqualGenerator(llvm::StringRef name,
                                               uint8_t byteValue)
    : SeedGenerator(name), byteValue(byteValue), seedWritten(false) {}

bool AllBytesEqualGenerator::writeSeed(SeedManager& sm) {
  auto fob = sm.getBufferForSeed(/*prefix=*/getName());
  if (!fob) {
    return false;
  }
  memset(fob->getBufferStart(), byteValue, fob->getBufferSize());
  fob->commit();
  seedWritten = true;
  return true;
}

bool AllBytesEqualGenerator::empty() const { return seedWritten; }

} // namespace fuzzingCommon
} // namespace jfs
