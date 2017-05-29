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
#ifndef JFS_CORE_Z3NODE_H
#define JFS_CORE_Z3NODE_H
#include "z3.h"
#include <assert.h>

namespace jfs {
namespace core {

template <typename T> class Z3NodeHandle {
  // Internally these Z3 types are pointers
  // so storing these should be cheap.
  // It would be nice if we could infer the Z3_context from the node
  // but I can't see a way to do this from Z3's API.
protected:
  T node;
  ::Z3_context context;

private:
  // To be specialised
  inline void inc_ref(T node);
  inline void dec_ref(T node);

public:
  Z3NodeHandle() : node(NULL), context(NULL) {}
  Z3NodeHandle(const T _node, const ::Z3_context _context)
      : node(_node), context(_context) {
    if (node && context) {
      inc_ref(node);
    }
  };
  ~Z3NodeHandle() {
    if (node && context) {
      dec_ref(node);
    }
  }
  Z3NodeHandle(const Z3NodeHandle &b) : node(b.node), context(b.context) {
    if (node && context) {
      inc_ref(node);
    }
  }
  Z3NodeHandle &operator=(const Z3NodeHandle &b) {
    if (node == NULL && context == NULL) {
      // Special case for when this object was constructed
      // using the default constructor. Try to inherit a non null
      // context.
      context = b.context;
    }
    assert(context == b.context && "Mismatched Z3 contexts!");
    // node != nullptr ==> context != NULL
    assert((node == NULL || context) &&
           "Can't have non nullptr node with nullptr context");

    if (node && context) {
      dec_ref(node);
    }
    node = b.node;
    if (node && context) {
      inc_ref(node);
    }
    return *this;
  }
  // To be specialised
  void dump() const;

  operator T() { return node; }
};

// Instantiate templates

// Specialise for Z3_sort
template <> inline void Z3NodeHandle<Z3_sort>::inc_ref(Z3_sort node) {
  // In Z3 internally this call is just a cast. We could just do that
  // instead to simplify our implementation but this seems cleaner.
  ::Z3_inc_ref(context, ::Z3_sort_to_ast(context, node));
}
template <> inline void Z3NodeHandle<Z3_sort>::dec_ref(Z3_sort node) {
  // In Z3 internally this call is just a cast. We could just do that
  // instead to simplify our implementation but this seems cleaner.
  ::Z3_dec_ref(context, ::Z3_sort_to_ast(context, node));
}
typedef Z3NodeHandle<Z3_sort> Z3SortHandle;
template <> void Z3NodeHandle<Z3_sort>::dump() const __attribute__((used));

// Specialise for Z3_ast
template <> inline void Z3NodeHandle<Z3_ast>::inc_ref(Z3_ast node) {
  ::Z3_inc_ref(context, node);
}
template <> inline void Z3NodeHandle<Z3_ast>::dec_ref(Z3_ast node) {
  ::Z3_dec_ref(context, node);
}
typedef Z3NodeHandle<Z3_ast> Z3ASTHandle;
template <> void Z3NodeHandle<Z3_ast>::dump() const __attribute__((used));

// Specialise for Z3_app
template <> inline void Z3NodeHandle<Z3_app>::inc_ref(Z3_app node) {
  ::Z3_inc_ref(context, ::Z3_app_to_ast(context, node));
}
template <> inline void Z3NodeHandle<Z3_app>::dec_ref(Z3_app node) {
  ::Z3_dec_ref(context, ::Z3_app_to_ast(context, node));
}
typedef Z3NodeHandle<Z3_app> Z3AppHandle;
template <> void Z3NodeHandle<Z3_app>::dump() const __attribute__((used));

// Specialise for Z3_func_decl
template <> inline void Z3NodeHandle<Z3_func_decl>::inc_ref(Z3_func_decl node) {
  ::Z3_inc_ref(context, ::Z3_func_decl_to_ast(context, node));
}
template <> inline void Z3NodeHandle<Z3_func_decl>::dec_ref(Z3_func_decl node) {
  ::Z3_dec_ref(context, ::Z3_func_decl_to_ast(context, node));
}
typedef Z3NodeHandle<Z3_func_decl> Z3FuncDeclHandle;
template <> void Z3NodeHandle<Z3_func_decl>::dump() const __attribute__((used));

// Specialise for Z3_solver
template <> inline void Z3NodeHandle<Z3_solver>::inc_ref(Z3_solver node) {
  ::Z3_solver_inc_ref(context, node);
}
template <> inline void Z3NodeHandle<Z3_solver>::dec_ref(Z3_solver node) {
  ::Z3_solver_dec_ref(context, node);
}
typedef Z3NodeHandle<Z3_solver> Z3SolverHandle;
template <> void Z3NodeHandle<Z3_solver>::dump() const __attribute__((used));
}
}
#endif
