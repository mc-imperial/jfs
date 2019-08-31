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
#ifndef JFS_FUZZING_COMMON_FUZZING_SOLVER_H
#define JFS_FUZZING_COMMON_FUZZING_SOLVER_H
#include "jfs/Core/Solver.h"
#include "jfs/FuzzingCommon/WorkingDirectoryManager.h"
#include <memory>

namespace jfs {
namespace fuzzingCommon {

class FuzzingAnalysisInfo;
class FuzzingSolverImpl;
class FuzzingSolver : public jfs::core::Solver {
private:
  std::unique_ptr<FuzzingSolverImpl> impl;

protected:
  virtual std::unique_ptr<jfs::core::SolverResponse>
  fuzz(jfs::core::Query& q, bool produceModel,
       std::shared_ptr<FuzzingAnalysisInfo> info) = 0;
  std::unique_ptr<WorkingDirectoryManager> wdm;

public:
  FuzzingSolver(std::unique_ptr<jfs::core::SolverOptions> options,
                std::unique_ptr<WorkingDirectoryManager> wdm,
                jfs::core::JFSContext& ctx);
  ~FuzzingSolver();
  std::unique_ptr<jfs::core::SolverResponse> solve(const jfs::core::Query& q,
                                                   bool produceModel) override;
  void cancel() override;
  friend class FuzzingSolverImpl;
};
}
}

#endif
