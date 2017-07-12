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
#include "jfs/CXXFuzzingBackend/CmdLine/CommandLineCategory.h"

namespace jfs {
namespace cxxfb {
namespace cl {

llvm::cl::OptionCategory
    CommandLineCategory("CXXFuzzingBackend",
                        "Options that control the CXXFuzzingBackend");
}
}
}
