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
#ifndef JFS_FUZZING_COMMON_SPECIAL_CONSTANT_SEED_GENERATOR_H
#define JFS_FUZZING_COMMON_SPECIAL_CONSTANT_SEED_GENERATOR_H

#include "jfs/FuzzingCommon/SeedGenerator.h"
#include "llvm/ADT/StringRef.h"
#include <string>

namespace jfs {
namespace fuzzingCommon {

class SeedManager;

// A seed generator that emits special constants based on the sorts used in the
// constraints of the query.
class SpecialConstantSeedGenerator : public SeedGenerator {
  // Inherit constructor
  using SeedGenerator::SeedGenerator;

  void preGenerationCallBack(SeedManager& sm) override;
  bool writeSeed(SeedManager& sm) override;
  bool empty() const override;
};

} // namespace fuzzingCommon
} // namespace jfs

#endif
