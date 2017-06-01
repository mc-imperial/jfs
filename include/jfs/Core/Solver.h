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
#ifndef JFS_CORE_SOLVER_H
#define JFS_CORE_SOLVER_H
#include "jfs/Core/Query.h"
#include "llvm/ADT/StringRef.h"
#include <stdint.h>
#include <memory>

namespace jfs {
namespace core {

// TODO: Implement LLVM style RTTI so we
// can have subclasses with solver specific
// options.
class SolverOptions {
public:
  // max time in seconds. Zero means no timeout
  uint64_t maxTime = 0;
};

class Model {
  virtual Z3ASTHandle getAssignment(Z3FuncDeclHandle) = 0;
};

class SolverResponse {
public:
  enum SolverSatisfiability { SAT, UNSAT, UNKNOWN };
  SolverResponse(SolverSatisfiability sat) : sat(sat) {};
  const SolverSatisfiability sat;
  virtual std::shared_ptr<Model> getModel() = 0;
  static llvm::StringRef getSatString(SolverSatisfiability);
};

class Solver {
protected:
  const SolverOptions &options;

public:
  Solver(const SolverOptions&);
  virtual ~Solver();
  Solver(const Solver&) = delete;
  Solver(const Solver&&) = delete;
  Solver& operator=(const Solver&) = delete;
  // Determine the satisfiability of the query.
  // Iff `produceModel` is false then only satisfiability will
  // be available.
  virtual std::unique_ptr<SolverResponse> solve(const Query &q,
                                                bool produceModel) = 0;
  const SolverOptions& getOptions() const;
  virtual llvm::StringRef getName() const = 0;
};
}
}

#endif
