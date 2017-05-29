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
#ifndef JFS_CORE_QUERY_H
#define JFS_CORE_QUERY_H
#include "jfs/Core/JFSContext.h"
#include "jfs/Core/Z3Node.h"
#include <vector>
namespace jfs {
namespace core {
class Query {
private:
  const JFSContext &ctx;

public:
  std::vector<Z3ASTHandle> constraints;
  Query(const JFSContext &ctx);
  ~Query();
  void dump() const;
};
}
}
#endif
