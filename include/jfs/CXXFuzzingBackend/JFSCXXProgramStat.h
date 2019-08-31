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
#ifndef JFS_CXX_FUZZING_BACKEND_JFS_CXX_PROGRAM_STAT_H
#define JFS_CXX_FUZZING_BACKEND_JFS_CXX_PROGRAM_STAT_H
#endif
#include "jfs/Support/JFSStat.h"

namespace jfs {
namespace cxxfb {
class JFSCXXProgramStat : public jfs::support::JFSStat {
public:
  JFSCXXProgramStat(llvm::StringRef name);
  virtual ~JFSCXXProgramStat();
  void printYAML(llvm::ScopedPrinter& os) const override;
  static bool classof(const JFSStat* s) { return s->getKind() == CXX_PROGRAM; }

  // FIMXE: Should not be public
  uint64_t numConstraints = 0;
  uint64_t numEntryFuncStatements = 0;
  // FIXME: Doesn't really belong here. The FuzzingAnalysisInfo should have its
  // own stat
  uint64_t numFreeVars = 0;
  uint64_t bufferStoredWidth = 0;
  uint64_t bufferTypeWidth = 0; // Sum of the type widths of each BufferElement
  uint64_t numEqualitySets = 0;
};
}
}
