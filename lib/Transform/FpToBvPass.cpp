//===----------------------------------------------------------------------===//
//
//                                     JFS
//
// Copyright 2018 J. Ryan Stinnett
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#include "jfs/Transform/FpToBvPass.h"
#include "jfs/Core/IfVerbose.h"
#include <list>
#include <vector>

using namespace jfs::core;

namespace jfs {
namespace transform {

bool FpToBvPass::run(Query &q) {
  JFSContext& ctx = q.getContext();
  std::vector<Z3ASTHandle> newConstraints;
  z3Ctx = ctx.getZ3Ctx();

  Z3TacticHandle tactic(::Z3_mk_tactic(z3Ctx, "fpa2bv"), z3Ctx);

  Z3GoalHandle initialGoal(::Z3_mk_goal(z3Ctx, /*models=*/false,
                                        /*unsat_cores=*/false,
                                        /*proofs=*/false),
                           z3Ctx);

  for (auto ci = q.constraints.cbegin(), ce = q.constraints.cend(); ci != ce;
       ++ci) {
    initialGoal.addFormula(*ci);
  }

#define CHECK_CANCELED()                                                       \
  if (cancelled) {                                                             \
    IF_VERB(ctx, ctx.getDebugStream() << "(" << getName() << " cancelled)\n"); \
    return false;                                                              \
  }

  CHECK_CANCELED();

  // Apply the tactic and store it for use in convertModel()
  result = tactic.apply(initialGoal);

  CHECK_CANCELED();

  // Collect all the resulting formulas
  result.collectAllFormulas(newConstraints);

  if (Query::areSame(q.constraints, newConstraints, /*ignoreOrder=*/true))
    return false;

  // Something changed
  q.constraints = std::move(newConstraints);
  return true;
}

llvm::StringRef FpToBvPass::getName() { return "FpToBv"; }
}
}
