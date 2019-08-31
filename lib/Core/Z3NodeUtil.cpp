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
#include "jfs/Core/Z3NodeUtil.h"
namespace jfs {
namespace core {

void Z3NodeUtil::collectFuncDecls(Z3FuncDeclSet& variables,
                                  std::list<Z3ASTHandle>& workList) {
  // Do DFS to collect variables
  // FIXME: Not collecting custom sorts or functions
  Z3ASTSet seenExpr;
  while (workList.size() != 0) {
    Z3ASTHandle node = workList.front();
    workList.pop_front();
    if (seenExpr.count(node) > 0) {
      // Already visited
      continue;
    }
    seenExpr.insert(node);

    if (node.isFreeVariable()) {
      variables.insert(node.asApp().getFuncDecl());
      continue;
    }
    if (!node.isApp())
      continue;
    // Must be a function application. Traverse the arguments
    Z3AppHandle app = node.asApp();
    for (unsigned index = 0; index < app.getNumKids(); ++index) {
      workList.push_front(app.getKid(index));
    }
  }
}

void Z3NodeUtil::collectFuncDecls(Z3FuncDeclSet& addTo, Z3ASTHandle e) {
  std::list<Z3ASTHandle> workList;
  workList.push_front(e);
  collectFuncDecls(addTo, workList);
}

} // namespace core
} // namespace jfs
