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
#ifndef JFS_FUZZING_COMMON_DUMMY_FUZZING_SOLVER
#define JFS_FUZZING_COMMON_DUMMY_FUZZING_SOLVER
#include "jfs/FuzzingCommon/FuzzingSolver.h"

namespace jfs {
namespace fuzzingCommon {

// This solver doesn't do any fuzzing so in effect
// it can only solve trivial constraints
class DummyFuzzingSolver : public FuzzingSolver {
protected:
  std::unique_ptr<jfs::core::SolverResponse>
  fuzz(jfs::core::Query& q, bool produceModel,
       std::shared_ptr<FuzzingAnalysisInfo> info) override;

public:
  DummyFuzzingSolver(const jfs::core::SolverOptions&);
  ~DummyFuzzingSolver();
  llvm::StringRef getName() const;
};
}
}
#endif
