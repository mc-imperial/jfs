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
#include "jfs/FuzzingCommon/CommandLineCategory.h"

namespace jfs {
namespace fuzzingCommon {

llvm::cl::OptionCategory CommandLineCategory(
    "Fuzzing Common options",
    "These are options that are common to all fuzzing backends");
}
}
