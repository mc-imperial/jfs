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
#ifndef JFS_FUZZING_COMMON_COMMAND_LINE_CATEGORY_H
#define JFS_FUZZING_COMMON_COMMAND_LINE_CATEGORY_H
#include "llvm/Support/CommandLine.h"

namespace jfs {
namespace fuzzingCommon {

extern llvm::cl::OptionCategory CommandLineCategory;
}
}
#endif
