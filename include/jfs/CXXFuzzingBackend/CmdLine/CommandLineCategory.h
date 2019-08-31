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
#ifndef JFS_CXX_FUZZING_BACKEND_CMDLINE_COMMAND_LINE_CATEGORY_H
#define JFS_CXX_FUZZING_BACKEND_CMDLINE_COMMAND_LINE_CATEGORY_H
#include "llvm/Support/CommandLine.h"

namespace jfs {
namespace cxxfb {
namespace cl {

extern llvm::cl::OptionCategory CommandLineCategory;
}
}
}
#endif
