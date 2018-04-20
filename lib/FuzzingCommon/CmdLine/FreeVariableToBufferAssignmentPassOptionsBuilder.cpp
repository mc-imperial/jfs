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
#include "jfs/FuzzingCommon/CmdLine/FreeVariableToBufferAssignmentPassOptionsBuilder.h"
#include "jfs/FuzzingCommon/CommandLineCategory.h"
#include "llvm/Support/CommandLine.h"

using namespace jfs::fuzzingCommon;

namespace {

llvm::cl::opt<bool> ByteAlignedBufferElements(
    "byte-aligned-buffer-elements",
    llvm::cl::desc(
        "If enabled buffer elements are byte aligned (default: false)"),
    llvm::cl::init(false),
    llvm::cl::cat(jfs::fuzzingCommon::CommandLineCategory));
}

namespace jfs {
namespace fuzzingCommon {
namespace cl {

std::unique_ptr<jfs::fuzzingCommon::FreeVariableToBufferAssignmentPassOptions>
buildFVTBAPOptionsFromCmdLine() {
  auto opts = std::unique_ptr<
      jfs::fuzzingCommon::FreeVariableToBufferAssignmentPassOptions>(
      new FreeVariableToBufferAssignmentPassOptions());

  if (ByteAlignedBufferElements) {
    opts->bufferElementBitAlignment = 8;
  } else {
    opts->bufferElementBitAlignment = 1;
  }
  return opts;
}
} // namespace cl
} // namespace fuzzingCommon
} // namespace jfs
