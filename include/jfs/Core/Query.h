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
#ifndef JFS_CORE_QUERY_H
#define JFS_CORE_QUERY_H
#include "jfs/Core/JFSContext.h"
#include "jfs/Core/Z3Node.h"
#include "jfs/Core/Z3NodeSet.h"
#include "llvm/Support/raw_ostream.h"
#include <vector>

namespace jfs {
namespace core {
class Query {
private:
  JFSContext& ctx;

public:
  std::vector<Z3ASTHandle> constraints;
  Query(JFSContext& ctx);
  ~Query();
  Query(const Query& other);
  // In principle there's no reason we can't have these deleted methods.
  // However we don't need them yet and I don't want the implicit declarations
  // to accidently be called.
  Query(const Query&&) = delete;
  Query& operator=(const Query&) = delete;
  Query& operator=(const Query&&) = delete;
  void dump() const;
  void collectFuncDecls(Z3FuncDeclSet& variables) const;
  void print(llvm::raw_ostream& os) const;
  JFSContext& getContext() const { return ctx; }

  static bool areSame(std::vector<Z3ASTHandle>& a, std::vector<Z3ASTHandle>& b,
                      bool ignoreOrder = false);
};

// Operator overload for easy printing of queries
llvm::raw_ostream& operator<<(llvm::raw_ostream& os, const Query& q);
}
}
#endif
