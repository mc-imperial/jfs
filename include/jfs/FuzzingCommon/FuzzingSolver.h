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
#ifndef JFS_FUZZING_COMMON_FUZZING_SOLVER_H
#define JFS_FUZZING_COMMON_FUZZING_SOLVER_H
#include "jfs/Core/Solver.h"
#include <memory>

namespace jfs {
namespace fuzzingCommon {

class FuzzingAnalysisInfo;
class FuzzingSolver : public jfs::core::Solver {
protected:
  virtual std::unique_ptr<jfs::core::SolverResponse>
  fuzz(jfs::core::Query& q, bool produceModel,
       std::shared_ptr<FuzzingAnalysisInfo> info) = 0;

public:
  FuzzingSolver(const jfs::core::SolverOptions&);
  ~FuzzingSolver();
  std::unique_ptr<jfs::core::SolverResponse> solve(const jfs::core::Query& q,
                                                   bool produceModel) override;
  llvm::StringRef getName() const = 0;
};
}
}

#endif
