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
#ifndef JFS_CORE_Z3_NODE_MAP_H
#define JFS_CORE_Z3_NODE_MAP_H
#include "jfs/Core/Z3ASTCmp.h"
#include <unordered_map>

namespace jfs {
namespace core {

template <typename T>
using Z3ASTMap = std::unordered_map<Z3ASTHandle, T, Z3ASTHashGet, Z3ASTCmp>;
}
}
#endif
