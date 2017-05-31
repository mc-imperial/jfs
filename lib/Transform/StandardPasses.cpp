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
#include "jfs/Transform/StandardPasses.h"
#include "jfs/Transform/AndHoistingPass.h"

namespace jfs {
namespace transform {
void AddStandardPasses(QueryPassManager &pm) {
  pm.add(std::make_shared<AndHoistingPass>());
}
}
}
