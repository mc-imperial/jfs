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
#include "jfs/CXXFuzzingBackend/JFSCXXProgramStat.h"

namespace jfs {
namespace cxxfb {

JFSCXXProgramStat::JFSCXXProgramStat(llvm::StringRef name)
    : jfs::support::JFSStat(CXX_PROGRAM, name) {}
JFSCXXProgramStat::~JFSCXXProgramStat() {}

void JFSCXXProgramStat::printYAML(llvm::ScopedPrinter& sp) const {
  sp.indent();
  auto& os = sp.getOStream();
  os << "\n";
  sp.startLine() << "name: " << getName() << "\n";
  sp.startLine() << "num_constraints: " << numConstraints << "\n";
  sp.startLine() << "num_entry_func_statements: " << numEntryFuncStatements
                 << "\n";
  sp.startLine() << "num_free_vars: " << numFreeVars << "\n";
  sp.startLine() << "buffer_stored_width: " << bufferStoredWidth << "\n";
  sp.startLine() << "buffer_type_width: " << bufferTypeWidth << "\n";
  sp.startLine() << "num_equality_sets: " << numEqualitySets << "\n";
  sp.unindent();
}
}
}
