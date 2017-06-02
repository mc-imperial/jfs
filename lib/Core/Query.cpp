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
#include "jfs/Core/Z3NodeSet.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <list>

namespace jfs {
namespace core {

llvm::raw_ostream& operator<<(llvm::raw_ostream& os, const Query& q) {
  q.print(os);
  return os;
}

Query::Query(const JFSContext &ctx) : ctx(ctx) {}

Query::~Query() {}

Query::Query(const Query &other) : ctx(other.ctx) {
  this->constraints.reserve(other.constraints.size());
  this->constraints.insert(this->constraints.begin(),
                           other.constraints.cbegin(),
                           other.constraints.cend());
}

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
  jfs::core::Z3FuncDeclSet variables; // Use a set to avoid duplicates
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
        variables.insert(funcDecl);
        continue;
      }
      // must be applying a function. Traverse its args
      for (unsigned index = 0; index < numArgs; ++index) {
        workList.push_front(
            Z3ASTHandle(::Z3_get_app_arg(ctx.z3Ctx, app, index), ctx.z3Ctx));
      }
    }
  }

  // Created a sorted list of variables for printing
  std::vector<Z3FuncDeclHandle> sortedVariables(variables.begin(),
                                                variables.end());
  std::sort(sortedVariables.begin(), sortedVariables.end(),
            [](const Z3FuncDeclHandle &a, const Z3FuncDeclHandle &b) {
              Z3_symbol aName = ::Z3_get_decl_name(a.getContext(), a);
              Z3_symbol bName = ::Z3_get_decl_name(b.getContext(), b);
              // std::string Allocation is necessary because
              // ::Z3_get_symbol_string uses a static
              // allocated buffer that changes between calls.
              std::string aStr(::Z3_get_symbol_string(a.getContext(), aName));
              std::string bStr(::Z3_get_symbol_string(b.getContext(), bName));
              return aStr < bStr;
            });
  // Print variables
  os << "; Start decls (" << variables.size() << ")\n";
  for (auto vi = sortedVariables.begin(), ve = sortedVariables.end(); vi != ve;
       ++vi) {
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
