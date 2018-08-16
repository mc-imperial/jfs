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
#ifndef JFS_FUZZING_COMMON_SEED_GENERATOR_H
#define JFS_FUZZING_COMMON_SEED_GENERATOR_H
#include "llvm/ADT/StringRef.h"
#include <string>

namespace jfs {
namespace fuzzingCommon {

class FuzzingAnalysisInfo;
class SeedManager;

class SeedGenerator {
private:
  std::string name;

public:
  SeedGenerator(llvm::StringRef name);
  virtual ~SeedGenerator();
  // Called once by the SeedManager before any seeds are requested
  virtual void preGenerationCallBack(SeedManager& sm);
  // Called once by the SeedManager after all seeds are requested
  virtual void postGenerationCallBack(SeedManager& sm);
  // Returns true on success
  virtual bool writeSeed(SeedManager& sm) = 0;
  virtual llvm::StringRef getName() const { return name; }
  virtual bool empty() const = 0;
};

// A generator that emits a single seed with all bytes set to
// the supplied byte value.
class AllBytesEqualGenerator : public SeedGenerator {
private:
  uint8_t byteValue;
  bool seedWritten;

public:
  AllBytesEqualGenerator(llvm::StringRef name, uint8_t byteValue);
  void preGenerationCallBack(SeedManager& sm) override {}
  void postGenerationCallBack(SeedManager& sm) override {}
  bool writeSeed(SeedManager& sm) override;
  bool empty() const override;
};

} // namespace fuzzingCommon
} // namespace jfs

#endif
