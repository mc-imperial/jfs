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
#ifndef JFS_CXX_FUZZING_BACKEND_FUZZING_SOLVER_OPTIONS_H
#define JFS_CXX_FUZZING_BACKEND_FUZZING_SOLVER_OPTIONS_H
#include "jfs/Core/SolverOptions.h"
#include <memory>

namespace jfs {
namespace cxxfb {

struct ClangOptions;

class CXXFuzzingSolverOptions : public jfs::core::SolverOptions {
private:
  // Options
  std::unique_ptr<ClangOptions> clangOpt;

public:
  CXXFuzzingSolverOptions(std::unique_ptr<ClangOptions> clangOpt);
  static bool classof(const SolverOptions* so) {
    return so->getKind() == CXX_FUZZING_SOLVER_KIND;
  }
  const ClangOptions* getClangOptions() const { return clangOpt.get(); }
};
}
}

#endif
