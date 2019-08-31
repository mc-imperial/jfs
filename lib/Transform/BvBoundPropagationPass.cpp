
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
#include "jfs/Transform/BvBoundPropagationPass.h"
#include "jfs/Core/IfVerbose.h"
#include "jfs/Core/Z3Node.h"
#include "jfs/Core/Z3NodeSet.h"
#include <list>
#include <vector>

using namespace jfs::core;

namespace jfs {
namespace transform {

bool BvBoundPropagationPass::run(Query &q) {
  JFSContext& ctx = q.getContext();
  std::vector<Z3ASTHandle> newConstraints;
  z3Ctx = ctx.getZ3Ctx();
  // NOTE: This tactic only modifies bvule and bvsle so the SimplificationPass
  // needs to be run first.
  Z3TacticHandle propagateValuesTactic(
      ::Z3_mk_tactic(z3Ctx, "propagate-bv-bounds"), z3Ctx);

  Z3GoalHandle initialGoal(::Z3_mk_goal(z3Ctx, /*models=*/false,
                                        /*unsat_cores=*/false,
                                        /*proofs=*/false),
                           z3Ctx);

  // Add the constraints to the goal
  for (auto ci = q.constraints.cbegin(), ce = q.constraints.cend(); ci != ce;
       ++ci) {
    initialGoal.addFormula(*ci);
  }

  if (cancelled) {
    IF_VERB(ctx, ctx.getDebugStream() << "(" << getName() << " cancelled)\n");
    return false;
  }

  // Apply the tactic and store it for use in convertModel()
  result = propagateValuesTactic.apply(initialGoal);

  if (cancelled) {
    IF_VERB(ctx, ctx.getDebugStream() << "(" << getName() << " cancelled)\n");
    return false;
  }

  // Collect all the resulting formulas
  result.collectAllFormulas(newConstraints);

  if (Query::areSame(q.constraints, newConstraints, /*ignoreOrder=*/true))
    return false;

  // Something changed
  q.constraints = std::move(newConstraints);
  return true;
}

llvm::StringRef BvBoundPropagationPass::getName() {
  return "BvBoundPropagation";
}
}
}
