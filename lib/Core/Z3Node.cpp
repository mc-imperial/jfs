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
#include "jfs/Core/Z3Node.h"
#include "llvm/Support/raw_ostream.h"

namespace jfs {
namespace core {
template <> void Z3NodeHandle<Z3_sort>::dump() const {
  llvm::errs() << "Z3SortHandle:\n"
               << ::Z3_sort_to_string(context, node) << "\n";
}
template <> void Z3NodeHandle<Z3_ast>::dump() const {
  llvm::errs() << "Z3ASTHandle:\n" << ::Z3_ast_to_string(context, node) << "\n";
}
template <> void Z3NodeHandle<Z3_solver>::dump() const {
  llvm::errs() << "Z3SolverHandle:\n"
               << ::Z3_solver_to_string(context, node) << "\n";
}
}
}
