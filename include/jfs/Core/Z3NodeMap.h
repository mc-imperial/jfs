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
#ifndef JFS_CORE_Z3_NODE_MAP_H
#define JFS_CORE_Z3_NODE_MAP_H
#include "jfs/Core/Z3ASTCmp.h"
#include <unordered_map>

namespace jfs {
namespace core {

template <typename T>
using Z3ASTMap = std::unordered_map<Z3ASTHandle, T, Z3ASTHashGet, Z3ASTCmp>;

template <typename T>
using Z3SortMap = std::unordered_map<Z3SortHandle, T, Z3SortHashGet, Z3SortCmp>;

template <typename T>
using Z3FuncDeclMap =
    std::unordered_map<Z3FuncDeclHandle, T, Z3FuncDeclHashGet, Z3FuncDeclCmp>;
}
}
#endif
