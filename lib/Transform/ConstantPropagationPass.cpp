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
#include "jfs/Transform/ConstantPropagationPass.h"
#include "jfs/Core/Z3Node.h"
#include <list>
#include <vector>

using namespace jfs::core;

namespace jfs {
namespace transform {

bool ConstantPropagationPass::run(Query &q) {
  std::vector<Z3ASTHandle> newConstraints;
  Z3_context z3Ctx = q.getContext().z3Ctx;
  Z3TacticHandle propagateValuesTactic(
      ::Z3_mk_tactic(z3Ctx, "propagate-values"), z3Ctx);

  Z3GoalHandle initialGoal(::Z3_mk_goal(z3Ctx, /*models=*/false,
                                        /*unsat_cores=*/false,
                                        /*proofs=*/false),
                           z3Ctx);

  // Add the constraints to the goal
  unsigned correctInsertCount = 0;
  for (auto ci = q.constraints.cbegin(), ce = q.constraints.cend(); ci != ce;
       ++ci) {
    // `true` gets ignored when inserted into a goal so don't count it for the
    // assert.
    if (!ci->isTrue())
      ++correctInsertCount;

    initialGoal.addFormula(*ci);
  }

  // NOTE: cannot use `q.constraints.size()` because `true` gets
  // ignored when we try to add it to a goal.
  assert(initialGoal.getNumFormulas() == correctInsertCount);

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

llvm::StringRef ConstantPropagationPass::getName() {
  return "ConstantPropagation";
}
}
}
