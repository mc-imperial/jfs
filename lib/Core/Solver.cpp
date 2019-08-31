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
#include "jfs/Core/Solver.h"

namespace jfs {
  namespace core {

  SolverResponse::SolverResponse(SolverSatisfiability sat) : sat(sat) {}
  SolverResponse::~SolverResponse() {}

  Solver::Solver(std::unique_ptr<SolverOptions> options, JFSContext& ctx)
      : options(std::move(options)), ctx(ctx) {}

  Solver::~Solver() {}

  const SolverOptions* Solver::getOptions() const { return options.get(); }

  llvm::StringRef SolverResponse::getSatString(SolverSatisfiability sat) {
    switch (sat) {
      case SolverResponse::SAT:
        return "sat";
      case SolverResponse::UNSAT:
        return "unsat";
      case SolverResponse::UNKNOWN:
        return "unknown";
      default:
        llvm_unreachable("unknown sat type");
    }
    return "unknown";
  }
}
}
