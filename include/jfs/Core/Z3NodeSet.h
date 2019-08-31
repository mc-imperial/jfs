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
#ifndef JFS_CORE_Z3_AST_SET_H
#define JFS_CORE_Z3_AST_SET_H
#include "jfs/Core/Z3ASTCmp.h"
#include "jfs/Core/Z3Node.h"
#include <assert.h>
#include <unordered_set>

namespace jfs {
namespace core {

// We don't provide a templated Z3NodeSet because not all Z3Node's are ASTs.
// For now doing these aliases is simpler.
using Z3ASTSet = std::unordered_set<Z3ASTHandle, Z3ASTHashGet, Z3ASTCmp>;

using Z3FuncDeclSet =
    std::unordered_set<Z3FuncDeclHandle, Z3FuncDeclHashGet, Z3FuncDeclCmp>;

using Z3SortSet = std::unordered_set<Z3SortHandle, Z3SortHashGet, Z3SortCmp>;
}
}

#endif
