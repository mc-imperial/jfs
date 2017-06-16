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
#ifndef JFS_Z3BACKEND_Z3_SOLVER_H
#define JFS_Z3BACKEND_Z3_SOLVER_H
#include "jfs/Core/Solver.h"
#include <memory>

namespace jfs {
namespace z3Backend {
class Z3Solver : public jfs::core::Solver {
public:
  Z3Solver(const jfs::core::SolverOptions&);
  ~Z3Solver();
  std::unique_ptr<jfs::core::SolverResponse> solve(const jfs::core::Query& q,
                                                   bool produceModel) override;
  llvm::StringRef getName() const override;
};
}
}

#endif
