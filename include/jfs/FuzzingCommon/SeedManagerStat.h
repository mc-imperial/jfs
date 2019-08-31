//===----------------------------------------------------------------------===//
//
//                                     JFS
//
// Copyright 2017-2018 Daniel Liew
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#ifndef JFS_FUZZING_COMMON_SEED_MANAGER_STAT_H
#define JFS_FUZZING_COMMON_SEED_MANAGER_STAT_H
#include "jfs/Core/JFSContext.h"
#include "jfs/FuzzingCommon/FuzzingSolver.h"
#include "jfs/Support/JFSStat.h"
#include "llvm/ADT/StringRef.h"
#include <memory>

namespace jfs {
namespace fuzzingCommon {
struct SeedManagerStat : public jfs::support::JFSStat {
  uint64_t numSeedsGenerated = 0;
  SeedManagerStat(llvm::StringRef name);
  virtual ~SeedManagerStat();
  void printYAML(llvm::ScopedPrinter& os) const override;
  static bool classof(const JFSStat* s) { return s->getKind() == SEED_MANAGER; }
};
} // namespace fuzzingCommon
} // namespace jfs
#endif
