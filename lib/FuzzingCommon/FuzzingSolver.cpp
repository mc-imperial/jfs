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
#include "jfs/FuzzingCommon/FuzzingSolver.h"
#include "jfs/FuzzingCommon/FuzzingAnalysisInfo.h"
#include "jfs/Transform/QueryPassManager.h"

using namespace jfs::core;
using namespace jfs::transform;

namespace jfs {
namespace fuzzingCommon {
FuzzingSolver::FuzzingSolver(const SolverOptions &opts) : Solver(opts) {}
FuzzingSolver::~FuzzingSolver() {}


// This response type is used for the trivial queries
// that we can solve without fuzzing
class FuzzingSolverResponse : public jfs::core::SolverResponse {
public:
  FuzzingSolverResponse(SolverResponse::SolverSatisfiability sat)
      : SolverResponse(sat) {}
  std::shared_ptr<Model> getModel() override {
    // TODO: Figure out how to support Model generation.
    // Can we have common code for all fuzzing backends or
    // will they need their own?
    return nullptr;
  }
};

std::unique_ptr<SolverResponse> FuzzingSolver::solve(const jfs::core::Query &q,
                                                     bool produceModel) {
  // Check for trivial SAT
  if (q.constraints.size() == 0) {
    // Empty constraint set is trivially satisifiable
    assert(!produceModel && "producing models not implemented");
    return std::unique_ptr<SolverResponse>(
        new FuzzingSolverResponse(SolverResponse::SAT));
  }

  // Check for trivial UNSAT
  bool isUnsat = false;
  for (auto ci = q.constraints.cbegin(), ce = q.constraints.cend(); ci != ce;
       ++ci) {
    Z3ASTHandle e = *ci;
    if (e.isFalse()) {
      isUnsat = true;
      break;
    }
  }
  if (isUnsat) {
    return std::unique_ptr<SolverResponse>(
        new FuzzingSolverResponse(SolverResponse::UNSAT));
  }

  // FIXME: Not sure we need to modify the query yet. If not we should
  // change the pass hierarchy so we can have analysis only passes that
  // work on `const Query`.
  // Make a copy of the query to work on. This is so that the client's
  // copy of the query doesn't unexpecte
  Query qCopy(q);

  // Can't trivially prove sat/unsat, so we have to fuzz.
  // Collect the information we need to fuzz and start fuzz
  auto fai = std::make_shared<FuzzingAnalysisInfo>();
  QueryPassManager pm;
  fai->addTo(pm);
  pm.run(qCopy);
  return fuzz(qCopy, produceModel, fai);
}
}
}
