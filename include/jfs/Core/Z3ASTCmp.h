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
#ifndef JFS_CORE_Z3_AST_CMP
#define JFS_CORE_Z3_AST_CMP
#include "jfs/Core/Z3Node.h"
#include <z3.h>

namespace jfs {
namespace core {
struct Z3ASTHashGet {
  size_t operator()(const Z3ASTHandle& h) const {
    return ::Z3_get_ast_hash(h.getContext(), h);
  }
};

struct Z3ASTCmp {
  bool operator()(const Z3ASTHandle& a, const Z3ASTHandle b) const {
    assert(a.getContext() == b.getContext() && "Contexts must be equal");
    return ::Z3_is_eq_ast(a.getContext(), a, b);
  }
};

struct Z3SortHashGet {
  size_t operator()(const Z3SortHandle& h) const {
    return ::Z3_get_ast_hash(h.getContext(), h.asAST());
  }
};

struct Z3SortCmp {
  bool operator()(const Z3SortHandle& a, const Z3SortHandle b) const {
    assert(a.getContext() == b.getContext() && "Contexts must be equal");
    return ::Z3_is_eq_ast(a.getContext(), a.asAST(), b.asAST());
  }
};

struct Z3FuncDeclHashGet {
  size_t operator()(const Z3FuncDeclHandle& h) const {
    return ::Z3_get_ast_hash(h.getContext(),
                             ::Z3_func_decl_to_ast(h.getContext(), h));
  }
};

struct Z3FuncDeclCmp {
  bool operator()(const Z3FuncDeclHandle& a, const Z3FuncDeclHandle b) const {
    assert(a.getContext() == b.getContext() && "Contexts must be equal");
    return ::Z3_is_eq_ast(a.getContext(),
                          ::Z3_func_decl_to_ast(a.getContext(), a),
                          ::Z3_func_decl_to_ast(b.getContext(), b));
  }
};
}
}
#endif
