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
#include "jfs/Core/Query.h"
#include "llvm/Support/raw_ostream.h"
#include <list>

namespace jfs {
namespace core {

llvm::raw_ostream& operator<<(llvm::raw_ostream& os, const Query& q) {
  q.print(os);
  return os;
}

Query::Query(const JFSContext &ctx) : ctx(ctx) {}

Query::~Query() {}

void Query::dump() const {
  llvm::errs() << *this;
}

void Query::print(llvm::raw_ostream& os) const {
  std::list<Z3ASTHandle> workList;
  for (auto bi = constraints.begin(), be = constraints.end(); bi != be; ++bi) {
    workList.push_front(*bi);
  }
  // Do DFS to collect variables
  // FIXME: Not collecting custom sorts or functions
  std::vector<Z3FuncDeclHandle> variables;
  while (workList.size() != 0) {
    Z3ASTHandle node = workList.front();
    workList.pop_front();
    if (::Z3_is_app(ctx.z3Ctx, node)) {
      Z3AppHandle app = Z3AppHandle(::Z3_to_app(ctx.z3Ctx, node), ctx.z3Ctx);
      unsigned numArgs = ::Z3_get_app_num_args(ctx.z3Ctx, app);
      if (numArgs == 0) {
        Z3FuncDeclHandle funcDecl =
            Z3FuncDeclHandle(::Z3_get_app_decl(ctx.z3Ctx, app), ctx.z3Ctx);
        if (::Z3_is_numeral_ast(ctx.z3Ctx, node))
          continue; // Don't print constants
        variables.push_back(funcDecl);
        continue;
      }
      // must be applying a function. Traverse its args
      for (unsigned index = 0; index < numArgs; ++index) {
        workList.push_front(
            Z3ASTHandle(::Z3_get_app_arg(ctx.z3Ctx, app, index), ctx.z3Ctx));
      }
    }
  }
  // Print variables
  os << "; Start decls (" << variables.size() << ")\n";
  for (auto vi = variables.begin(), ve = variables.end(); vi != ve; ++vi) {
    Z3ASTHandle asAst =
        Z3ASTHandle(::Z3_func_decl_to_ast(ctx.z3Ctx, *vi), ctx.z3Ctx);
    os << ::Z3_ast_to_string(ctx.z3Ctx, asAst) << "\n";
  }
  os << "; End decls\n";
  // Print constraints
  os << "; Start constraints (" << constraints.size() << ")\n";
  for (auto bi = constraints.begin(), be = constraints.end(); bi != be; ++bi) {
    os << "(assert " << ::Z3_ast_to_string(ctx.z3Ctx, *bi) << ")\n";
  }
  os << "; End constraints\n";
}
}
}
