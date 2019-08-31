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
#ifndef JFS_CORE_SOLVER_H
#define JFS_CORE_SOLVER_H
#include "jfs/Core/Query.h"
#include "jfs/Core/SolverOptions.h"
#include "jfs/Support/ICancellable.h"
#include "llvm/ADT/StringRef.h"
#include <memory>
#include <stdint.h>

namespace jfs {
namespace core {

class Model;

class SolverResponse {
public:
  enum SolverSatisfiability { SAT, UNSAT, UNKNOWN };
  SolverResponse(SolverSatisfiability sat);
  virtual ~SolverResponse();
  const SolverSatisfiability sat;
  virtual Model* getModel() = 0;
  static llvm::StringRef getSatString(SolverSatisfiability);
};

class Solver : public jfs::support::ICancellable {
protected:
  std::unique_ptr<SolverOptions> options;
  JFSContext& ctx;

public:
  Solver(std::unique_ptr<SolverOptions> options, JFSContext& ctx);
  virtual ~Solver();
  Solver(const Solver&) = delete;
  Solver(const Solver&&) = delete;
  Solver& operator=(const Solver&) = delete;
  // Determine the satisfiability of the query.
  // Iff `produceModel` is false then only satisfiability will
  // be available.
  virtual std::unique_ptr<SolverResponse> solve(const Query& q,
                                                bool produceModel) = 0;
  const SolverOptions* getOptions() const;
  virtual llvm::StringRef getName() const = 0;
  JFSContext& getContext() { return ctx; }
};
}
}

#endif
