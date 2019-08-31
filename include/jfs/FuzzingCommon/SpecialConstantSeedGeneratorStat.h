//===----------------------------------------------------------------------===//
//
//                                     JFS
//
// Copyright 2017-2018 Alastair Donaldson
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#ifndef JFS_FUZZING_COMMON_SEED_GENERATOR_STAT_H
#define JFS_FUZZING_COMMON_SEED_GENERATOR_STAT_H
#include "jfs/Core/JFSContext.h"
#include "jfs/Core/Z3NodeMap.h"
#include "jfs/Support/JFSStat.h"

namespace jfs {
namespace fuzzingCommon {
struct SpecialConstantSeedGeneratorStat : public jfs::support::JFSStat {
  jfs::core::Z3SortMap<uint64_t> foundConstantsCount;
  uint64_t totalNumBuiltInBVConstants = 0;
  uint64_t numCoveredBVConstants = 0;
  uint64_t totalNumBuiltInFPConstants = 0;
  uint64_t numCoveredFPConstants = 0;
  uint64_t totalNumBuiltInBoolConstants = 0;
  uint64_t numCoveredBoolConstants = 0;

  SpecialConstantSeedGeneratorStat(llvm::StringRef name);
  virtual ~SpecialConstantSeedGeneratorStat();
  void printYAML(llvm::ScopedPrinter& os) const override;
  static bool classof(const JFSStat* s) {
    return s->getKind() == SEED_GENERATOR;
  }
};
} // namespace fuzzingCommon
} // namespace jfs
#endif
