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
#include "jfs/Transform/SimplificationPass.h"
#include "jfs/Core/IfVerbose.h"
#include <list>
#include <vector>

using namespace jfs::core;

namespace jfs {
namespace transform {

bool SimplificationPass::run(Query &q) {
  JFSContext& ctx = q.getContext();
  std::vector<Z3ASTHandle> newConstraints;
  z3Ctx = ctx.getZ3Ctx();

  Z3TacticHandle simplifyTactic(::Z3_mk_tactic(z3Ctx, "simplify"), z3Ctx);

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

  // TODO: Investigate the different simplifier parameters and see what
  // is relevant in our use case.
  Z3ParamsHandle params(::Z3_mk_params(z3Ctx), z3Ctx);
  // Enable `bv_ite2id`.
  Z3_symbol bv_ite2id = ::Z3_mk_string_symbol(z3Ctx, "bv_ite2id");
  Z3_params_set_bool(z3Ctx, params, bv_ite2id, true);

  // Apply the tactic and store it for use in convertModel()
  result = simplifyTactic.applyWithParams(initialGoal, params);

  CHECK_CANCELED();

  // Collect all the resulting formulas
  result.collectAllFormulas(newConstraints);

  if (Query::areSame(q.constraints, newConstraints, /*ignoreOrder=*/true))
    return false;

  // Something changed
  q.constraints = std::move(newConstraints);
  return true;
}

llvm::StringRef SimplificationPass::getName() { return "Simplification"; }
}
}
