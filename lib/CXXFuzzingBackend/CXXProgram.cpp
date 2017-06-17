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
#include "jfs/CXXFuzzingBackend/CXXProgram.h"

namespace jfs {
namespace cxxfb {

// CXXDecl
void CXXDecl::dump() const { print(llvm::errs()); }

CXXDeclRef CXXDecl::getParent() const { return parent; }

CXXDecl::CXXDecl(CXXDeclRef parent) : parent(parent) {}

CXXDecl::~CXXDecl() {}

// CXXIncludeDecl

CXXIncludeDecl::CXXIncludeDecl(CXXDeclRef parent, llvm::StringRef path,
                               bool systemHeader)
    : CXXDecl(parent), path(path.str()), isSystemInclude(systemHeader) {}

void CXXIncludeDecl::print(llvm::raw_ostream& os) const {
  os << "#include " << (isSystemInclude ? "<" : "\"") << path
     << (isSystemInclude ? ">" : "\"") << "\n";
}

// CXXProgram

void CXXProgram::print(llvm::raw_ostream& os) const {
  os << "// Begin program\n";
  for (const auto& decl : decls) {
    decl->print(os);
  }
  os << "// End program\n";
}

void CXXProgram::appendDecl(CXXDeclRef decl) { decls.push_back(decl); }
}
}
