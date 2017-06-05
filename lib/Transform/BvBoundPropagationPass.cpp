
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
#include "jfs/Transform/BvBoundPropagationPass.h"
#include "jfs/Core/Z3Node.h"
#include "jfs/Core/Z3NodeSet.h"
#include <list>
#include <vector>

using namespace jfs::core;

namespace jfs {
namespace transform {

bool BvBoundPropagationPass::run(Query &q) {
  std::vector<Z3ASTHandle> newConstraints;
  Z3_context z3Ctx = q.getContext().z3Ctx;
  // NOTE: This tactic only modifies bvule and bvsle so the SimplificationPass
  // needs to be run first.
  Z3TacticHandle propagateValuesTactic(
      ::Z3_mk_tactic(z3Ctx, "propagate-bv-bounds"), z3Ctx);

  Z3GoalHandle initialGoal(::Z3_mk_goal(z3Ctx, /*models=*/false,
                                        /*unsat_cores=*/false,
                                        /*proofs=*/false),
                           z3Ctx);

  // Add the constraints to the goal
// FIXME: I wish Z3's Goal API didn't do this. I'd like the simplifications
// to come from the tactics I apply and not happen implicitly.
  for (auto ci = q.constraints.cbegin(), ce = q.constraints.cend(); ci != ce;
       ++ci) {
  // I didn't copy the asserts() from `ConstantPropagationPass.cpp` because
  // I don't want to clutter the code here.
    initialGoal.addFormula(*ci);
  }

  // Apply the tactic
  Z3ApplyResultHandle result = propagateValuesTactic.apply(initialGoal);
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
