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
#include "jfs/Support/ErrorMessages.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/YAMLParser.h"
#include "llvm/Support/raw_ostream.h"
#include <string>

namespace {
llvm::cl::opt<std::string> InputFilename(llvm::cl::Positional,
                                         llvm::cl::desc("<input file>"),
                                         llvm::cl::init("-"));
}

int main(int argc, char** argv) {
  llvm::cl::ParseCommandLineOptions(argc, argv,
                                    "Check file has valid YAML syntax");
  auto bufferOrError = llvm::MemoryBuffer::getFileOrSTDIN(InputFilename);
  if (auto error = bufferOrError.getError()) {
    llvm::errs() << jfs::support::getMessageForFailedOpenFileOrSTDIN(
        InputFilename, error);
    return 1;
  }
  auto buffer(std::move(bufferOrError.get()));
  auto mbr = buffer->getMemBufferRef();
  llvm::SourceMgr sm;
  std::error_code ec;
  llvm::yaml::Stream yamlStream(mbr, sm);
  if (ec) {
    llvm::errs() << "Failed to open stream because " << ec.message() << "\n";
    return 1;
  }
  return yamlStream.validate() ? 0 : 1;
}
