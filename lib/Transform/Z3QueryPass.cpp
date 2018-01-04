//===----------------------------------------------------------------------===//
//
//                        JFS - The JIT Fuzzing Solver
//
// Copyright 2017-2018 Daniel Liew
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#include "jfs/Transform/Z3QueryPass.h"

namespace jfs {
namespace transform {

void Z3QueryPass::cancel() {
  cancelled = true;
  // Interupt Z3 just in case we are in the middle
  // of an application.
  // FIXME: This is racey
  if (z3Ctx) {
    ::Z3_interrupt(z3Ctx);
  }
}
}
}
