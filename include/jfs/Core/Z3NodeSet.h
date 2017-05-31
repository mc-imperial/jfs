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
#ifndef JFS_CORE_Z3_AST_SET_H
#define JFS_CORE_Z3_AST_SET_H
#include "jfs/Core/Z3Node.h"
#include <assert.h>
#include <unordered_set>
#include <z3.h>

namespace jfs {
namespace core {
struct Z3ASTHashGet {
  size_t operator()(const Z3ASTHandle &h) const {
    return ::Z3_get_ast_hash(h.getContext(), h);
  }
};

struct Z3ASTCmp {
  bool operator()(const Z3ASTHandle &a, const Z3ASTHandle b) const {
    assert(a.getContext() == b.getContext() && "Contexts must be equal");
    return ::Z3_is_eq_ast(a.getContext(), a, b);
  }
};

struct Z3FuncDeclHashGet {
  size_t operator()(const Z3FuncDeclHandle &h) const {
    return ::Z3_get_ast_hash(h.getContext(),
                             ::Z3_func_decl_to_ast(h.getContext(), h));
  }
};

struct Z3FuncDeclCmp {
  bool operator()(const Z3FuncDeclHandle &a, const Z3FuncDeclHandle b) const {
    assert(a.getContext() == b.getContext() && "Contexts must be equal");
    return ::Z3_is_eq_ast(a.getContext(),
                          ::Z3_func_decl_to_ast(a.getContext(), a),
                          ::Z3_func_decl_to_ast(b.getContext(), b));
  }
};

// We don't provide a templated Z3NodeSet because not all Z3Node's are ASTs.
// For now doing these aliases is simpler.
using Z3ASTSet = std::unordered_set<Z3ASTHandle, Z3ASTHashGet, Z3ASTCmp>;
using Z3FuncDeclSet =
    std::unordered_set<Z3FuncDeclHandle, Z3FuncDeclHashGet, Z3FuncDeclCmp>;
}
}

#endif
