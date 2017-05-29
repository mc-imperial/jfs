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
#include "jfs/Core/Query.h"
#include "llvm/Support/raw_ostream.h"

namespace jfs {
namespace core {

Query::Query(const JFSContext &ctx) : ctx(ctx) {}

Query::~Query() {}

void Query::dump() const {
  llvm::errs() << "Query(" << constraints.size() << " constraints)\n";
  for (auto bi = constraints.begin(), be = constraints.end(); bi != be; ++bi) {
    bi->dump();
  }
}
}
}
