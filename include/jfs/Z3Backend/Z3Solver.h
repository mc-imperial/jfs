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
#ifndef JFS_Z3BACKEND_Z3_SOLVER_H
#define JFS_Z3BACKEND_Z3_SOLVER_H
#include "jfs/Core/JFSContext.h"
#include "jfs/Core/Solver.h"
#include <memory>

namespace jfs {
namespace z3Backend {
class Z3Solver : public jfs::core::Solver {
private:
  Z3_context z3Ctx;
  bool cancelled;

public:
  Z3Solver(std::unique_ptr<jfs::core::SolverOptions> options,
           jfs::core::JFSContext& ctx);
  ~Z3Solver();
  std::unique_ptr<jfs::core::SolverResponse> solve(const jfs::core::Query& q,
                                                   bool produceModel) override;
  llvm::StringRef getName() const override;
  void cancel() override;
};
}
}

#endif
