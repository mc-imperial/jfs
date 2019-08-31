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
#ifndef JFS_CORE_SOLVER_OPTIONS_H
#define JFS_CORE_SOLVER_OPTIONS_H
#include "llvm/Support/Casting.h"
#include <stdint.h>

namespace jfs {
namespace core {

class SolverOptions {
  // START: LLVM RTTI boilerplate code
public:
  // NOTE: When updating this enum make sure you update all implementations
  // of `classof(const SolverOptions* so)`.
  enum SolverOptionKind {
    SOLVER_OPTIONS_KIND,
    FUZZING_SOLVER_KIND,
    CXX_FUZZING_SOLVER_KIND,
    LAST_FUZZING_SOLVER_KIND // This is a dummy entry
  };

private:
  const SolverOptionKind kind;

protected:
  SolverOptions(SolverOptionKind kind) : kind(kind) {}

public:
  SolverOptions() : SolverOptions(SOLVER_OPTIONS_KIND) {}
  virtual ~SolverOptions() {}
  SolverOptionKind getKind() const { return kind; }
  static bool classof(const SolverOptions* so) {
    return so->getKind() == SOLVER_OPTIONS_KIND;
  }
  // END: LLVM RTTI boilerplate code
  // Options common to all solvers
};
}
}

#endif
