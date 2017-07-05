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

namespace jfs {
namespace cxxfb {

class CXXFuzzingSolverOptions : public jfs::core::SolverOptions {
public:
  CXXFuzzingSolverOptions()
      : jfs::core::SolverOptions(CXX_FUZZING_SOLVER_KIND) {}
  static bool classof(const SolverOptions* so) {
    return so->getKind() == CXX_FUZZING_SOLVER_KIND;
  }
};
}
}

#endif
