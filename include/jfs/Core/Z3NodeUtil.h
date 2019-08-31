//===----------------------------------------------------------------------===//
//
//                                     JFS
//
// Copyright 2017-2018 Alastair Donaldson
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#ifndef JFS_CORE_Z3NODE_UTIL_H
#define JFS_CORE_Z3NODE_UTIL_H
#include "jfs/Core/Z3Node.h"
#include "jfs/Core/Z3NodeSet.h"
#include <list>

namespace jfs {
namespace core {

class Z3NodeUtil {
public:
  static void collectFuncDecls(Z3FuncDeclSet& addTo,
                               std::list<Z3ASTHandle>& workList);

  static void collectFuncDecls(Z3FuncDeclSet& addTo, Z3ASTHandle e);

  template <typename IteratorTy>
  static void collectFuncDecls(Z3FuncDeclSet& addTo, IteratorTy begin,
                               IteratorTy end) {
    std::list<Z3ASTHandle> workList;
    for (IteratorTy b = begin, e = end; b != e; ++b) {
      workList.push_back(*b);
    }
    collectFuncDecls(addTo, workList);
  }
};

} // namespace core
} // namespace jfs
#endif
