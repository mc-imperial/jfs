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
template <> void Z3NodeHandle<Z3_app>::dump() const {
  llvm::errs() << "Z3AppHandle:\n"
               << ::Z3_ast_to_string(context, ::Z3_app_to_ast(context, node))
               << "\n";
}
template <> void Z3NodeHandle<Z3_func_decl>::dump() const {
  llvm::errs() << "Z3FuncDeclHandle:\n"
               << ::Z3_ast_to_string(context,
                                     ::Z3_func_decl_to_ast(context, node))
               << "\n";
}
template <> void Z3NodeHandle<Z3_solver>::dump() const {
  llvm::errs() << "Z3SolverHandle:\n"
               << ::Z3_solver_to_string(context, node) << "\n";
}

template <> void Z3NodeHandle<Z3_params>::dump() const {
  llvm::errs() << "Z3ParamsHandle:\n"
               << ::Z3_params_to_string(context, node) << "\n";
}
}
}
