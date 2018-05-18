//===----------------------------------------------------------------------===//
//
//                        JFS - The JIT Fuzzing Solver
//
// Copyright 2018 J. Ryan Stinnett
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//

#include "API.h"

#include "Log.h"
#include <dlfcn.h>

namespace prf {

API::API() : TestOneInput(LLVMFuzzerTestOneInput) {
  atExit = reinterpret_cast<AtExitT*>(
    dlsym(RTLD_DEFAULT, "LLVMFuzzerAtExit"));
  if (atExit) {
    Debug("Optional user-provided function LLVMFuzzerAtExit found");
  }
}

void API::AtExit() {
  if (!atExit) {
    return;
  }
  atExit();
}

} // prf