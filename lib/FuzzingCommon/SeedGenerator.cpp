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
void SeedGenerator::postGenerationCallBack(SeedManager& sm) {}

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
  if (auto error = fob->commit()) {
    // FIXME: This probably isn't the right way to handle the errors
    // but this is good enough to suppress warnings about not using
    // the return value of `commit()`.
    auto errCode = llvm::errorToErrorCode(std::move(error));
    sm.getContext().getErrorStream()
        << "(error Failed to commit seed because \"" << errCode.message()
        << "\")\n";
    return false;
  }
  seedWritten = true;
  return true;
}

bool AllBytesEqualGenerator::empty() const { return seedWritten; }

} // namespace fuzzingCommon
} // namespace jfs
