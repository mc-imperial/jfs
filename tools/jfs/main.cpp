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

#include "jfs/Support/version.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include <string>

using namespace jfs;

namespace {
llvm::cl::opt<std::string> InputFilename(llvm::cl::Positional,
                                    llvm::cl::desc("<input file>"),
                                    llvm::cl::init("-"));
}

void printVersion() {
  llvm::outs() << support::getVersionString() << "\n";
  llvm::outs() << "\n";
  llvm::cl::PrintVersionMessage();
  return;
}

int main(int argc, char** argv) {
  llvm::cl::SetVersionPrinter(printVersion);
  llvm::cl::ParseCommandLineOptions(argc, argv);
  return 0;
}
