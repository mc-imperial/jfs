//===----------------------------------------------------------------------===//
//
//                                     JFS
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
#ifdef __APPLE__
  // On macOS, `dlsym` can access any optional symbols by default
  atExit = reinterpret_cast<AtExitT*>(
    dlsym(RTLD_DEFAULT, "LLVMFuzzerAtExit"));
#elif __linux__
  // On Linux, weak symbols will resolve this to a value only if defined
  atExit = LLVMFuzzerAtExit;
#else
#error "Unsupported platform"
#endif
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