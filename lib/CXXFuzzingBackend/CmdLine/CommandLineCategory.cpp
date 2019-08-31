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
