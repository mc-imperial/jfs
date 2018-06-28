//===----------------------------------------------------------------------===//
//
//                        JFS - The JIT Fuzzing Solver
//
// Copyright 2017-2018 Daniel Liew
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#include "jfs/Core/Query.h"
#include "jfs/Core/Z3NodeSet.h"
#include "jfs/Core/Z3NodeUtil.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <list>

namespace jfs {
namespace core {

llvm::raw_ostream& operator<<(llvm::raw_ostream& os, const Query& q) {
  q.print(os);
  return os;
}

Query::Query(JFSContext &ctx) : ctx(ctx) {}

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

void Query::collectFuncDecls(Z3FuncDeclSet& variables) const {
  std::list<Z3ASTHandle> workList;
  for (auto bi = constraints.begin(), be = constraints.end(); bi != be; ++bi) {
    workList.push_front(*bi);
  }
  Z3NodeUtil::collectFuncDecls(variables, workList);
}

void Query::print(llvm::raw_ostream& os) const {
  Z3_context z3Ctx = ctx.getZ3Ctx();

  // Do DFS to collect variables
  jfs::core::Z3FuncDeclSet variables; // Use a set to avoid duplicates
  collectFuncDecls(variables);

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
    Z3ASTHandle asAst = Z3ASTHandle(::Z3_func_decl_to_ast(z3Ctx, *vi), z3Ctx);
    // FIXME: should really use .toStr() method but I want to avoid alloc
    // overhead for now.
    os << ::Z3_ast_to_string(z3Ctx, asAst) << "\n";
  }
  os << "; End decls\n";
  // Print constraints
  os << "; Start constraints (" << constraints.size() << ")\n";
  for (auto bi = constraints.begin(), be = constraints.end(); bi != be; ++bi) {
    // FIXME: should really use .toStr() method but I want to avoid alloc
    // overhead for now.
    os << "(assert " << ::Z3_ast_to_string(z3Ctx, *bi) << ")\n";
  }
  os << "; End constraints\n";
}

bool Query::areSame(std::vector<Z3ASTHandle> &a, std::vector<Z3ASTHandle> &b,
                    bool ignoreOrder) {
  if (a.size() != b.size())
    return false;

  if (ignoreOrder) {
    Z3ASTSet aExpr(a.cbegin(), a.cend());
    for (auto ci = b.cbegin(), ce = b.cend(); ci != ce; ++ci) {
      if (aExpr.count(*ci) == 0)
        return false;
    }
    return true;
  }

  // Do order sensitive comparison
  for (unsigned index = 0; index < a.size(); ++index) {
    Z3ASTHandle aExpr = a[index];
    Z3ASTHandle bExpr = b[index];
    if (!aExpr.isStructurallyEqualTo(bExpr))
      return false;
  }
  return true;
}
}
}
