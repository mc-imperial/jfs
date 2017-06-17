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
#ifndef JFS_CXX_FUZZING_BACKEND_CXX_PROGRAM
#define JFS_CXX_FUZZING_BACKEND_CXX_PROGRAM
#include "llvm/Support/raw_ostream.h"
#include <memory>
#include <string>
#include <vector>

namespace jfs {
namespace cxxfb {

class CXXDecl;
using CXXDeclRef = std::shared_ptr<CXXDecl>;

// Base class for all declarations
class CXXDecl {
protected:
  CXXDeclRef parent;

public:
  CXXDecl(CXXDeclRef parent);
  virtual ~CXXDecl();
  virtual void print(llvm::raw_ostream&) const = 0;
  CXXDeclRef getParent() const;
  void dump() const;
};

// Include
class CXXIncludeDecl : public CXXDecl {
private:
  std::string path;
  bool isSystemInclude;

public:
  CXXIncludeDecl(CXXDeclRef parent, llvm::StringRef path, bool systemHeader);
  ~CXXIncludeDecl() {}
  void print(llvm::raw_ostream&) const override;
  const std::string& getPath() const { return path; }
};

class CXXProgram : public CXXDecl {
private:
  typedef std::vector<CXXDeclRef> declStorageTy;
  declStorageTy decls;

public:
  CXXProgram() : CXXDecl(nullptr) {}
  void print(llvm::raw_ostream&) const override;
  void appendDecl(CXXDeclRef);
  // Iterators
  declStorageTy::const_iterator cbegin() const { return decls.cbegin(); }
  declStorageTy::const_iterator cend() const { return decls.cend(); }
};
}
}
#endif
