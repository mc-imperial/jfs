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
#include "jfs/Transform/SimplificationPass.h"
#include "jfs/Core/IfVerbose.h"
#include <list>
#include <vector>

using namespace jfs::core;

namespace jfs {
namespace transform {

bool SimplificationPass::run(Query &q) {
  JFSContext& ctx = q.getContext();
  bool changed = false;
  std::vector<Z3ASTHandle> newConstraints;
  newConstraints.reserve(q.constraints.size());
  for (auto ci = q.constraints.cbegin(), ce = q.constraints.cend(); ci != ce;
       ++ci) {
    Z3ASTHandle current = *ci;

    if (cancelled) {
      IF_VERB(ctx, ctx.getDebugStream() << "(" << getName() << " cancelled)\n");
      return false;
    }

    // TODO: Investigate the different simplifier parameters and see what
    // is relevant in our use case.
    Z3ParamsHandle params(::Z3_mk_params(current.getContext()),
                          current.getContext());
    // Enable `bv_ite2id`.
    Z3_symbol bv_ite2id =
        ::Z3_mk_string_symbol(current.getContext(), "bv_ite2id");
    Z3_params_set_bool(current.getContext(), params, bv_ite2id, true);
    Z3ASTHandle simplified =
        Z3ASTHandle(::Z3_simplify_ex(current.getContext(), current, params),
                    current.getContext());

    if (!changed && !::Z3_is_eq_ast(current.getContext(), current, simplified))
      changed = true;
    newConstraints.push_back(simplified);
  }
  if (!changed)
    return false;

  q.constraints = std::move(newConstraints);
  return true;
}

llvm::StringRef SimplificationPass::getName() { return "Simplification"; }
}
}
