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
#ifndef JFS_CXX_FUZZING_BACKEND_CXX_PROGRAM
#define JFS_CXX_FUZZING_BACKEND_CXX_PROGRAM
#include "llvm/Support/raw_ostream.h"
#include <list>
#include <memory>
#include <string>
#include <vector>

namespace jfs {
namespace cxxfb {

class CXXDecl;
class CXXCodeBlock;
class CXXType;
class CXXFunctionArgument;
class CXXFunctionDecl;
class CXXStatement;
using CXXDeclRef = std::shared_ptr<CXXDecl>;
using CXXCodeBlockRef = std::shared_ptr<CXXCodeBlock>;
using CXXTypeRef = std::shared_ptr<CXXType>;
using CXXFunctionArgumentRef = std::shared_ptr<CXXFunctionArgument>;
using CXXStatementRef = std::shared_ptr<CXXStatement>;
using CXXFunctionDeclRef = std::shared_ptr<CXXFunctionDecl>;

// Base class for all declarations
class CXXDecl {
protected:
  // CXXDecl's form a tree with parents owning the children.
  // Therefore we don't need to partcipate in ownership (like
  // CXXDeclRef would) and raw pointers are fine.
  CXXDecl* parent;

public:
  CXXDecl(CXXDecl* parent);
  virtual ~CXXDecl();
  virtual void print(llvm::raw_ostream&) const = 0;
  CXXDecl* getParent() const;
  void dump() const;
};

// Include
class CXXIncludeDecl : public CXXDecl {
private:
  std::string path;
  bool isSystemInclude;

public:
  CXXIncludeDecl(CXXDecl* parent, llvm::StringRef path, bool systemHeader);
  ~CXXIncludeDecl() {}
  void print(llvm::raw_ostream&) const override;
  const std::string& getPath() const { return path; }
};

// Statement (for use inside code blocks)
class CXXStatement : public CXXDecl {
public:
  CXXStatement(CXXDecl* parent) : CXXDecl(parent) {}
  ~CXXStatement();
};

// Comment block
class CXXCommentBlock : public CXXStatement {
private:
  std::string comment;

public:
  CXXCommentBlock(CXXDecl* parent, llvm::StringRef comment)
      : CXXStatement(parent), comment(comment) {}
  void print(llvm::raw_ostream&) const override;
  const std::string& getComment() const { return comment; }
};

class CXXCodeBlock;
class CXXType;
class CXXFunctionArgument;
// Function definition
class CXXFunctionDecl : public CXXDecl {
private:
  std::string name;
  CXXTypeRef returnTy;
  std::vector<CXXFunctionArgumentRef> arguments;
  bool hasCVisibility;

public:
  // FIXME: shouldn't be public
  CXXCodeBlockRef defn;
  // Declaration
  CXXFunctionDecl(CXXDecl* parent, llvm::StringRef name, CXXTypeRef returnTy,
                  std::vector<CXXFunctionArgumentRef>& arguments,
                  bool hasCVisibility);
  // Definition
  ~CXXFunctionDecl();
  void print(llvm::raw_ostream&) const override;
  bool isDecl() const { return defn.get() == nullptr; }
  bool isDefn() const { return !isDecl(); }
};

// CXXType
class CXXType : public CXXDecl {
private:
  std::string name;
  bool isConst;

public:
  CXXType(CXXDecl* parent, llvm::StringRef name, bool isConst);
  CXXType(CXXDecl* parent, llvm::StringRef name);
  ~CXXType();
  void print(llvm::raw_ostream&) const override;
  llvm::StringRef getName() const { return name; }
};

// CXXFunctionArgument
class CXXFunctionArgument : public CXXDecl {
private:
  std::string name;
  CXXTypeRef argType;

public:
  CXXFunctionArgument(CXXDecl* parent, llvm::StringRef name,
                      CXXTypeRef argType);
  ~CXXFunctionArgument();
  void print(llvm::raw_ostream&) const override;
};

// CXXCodeBlock
class CXXCodeBlock : public CXXDecl {
public:
  // FIXME: shouldn't be public but its easier to just write to this
  std::list<CXXStatementRef> statements;
  CXXCodeBlock(CXXDecl* parent);
  ~CXXCodeBlock();
  void print(llvm::raw_ostream&) const override;
};

// CXXIfStatement
class CXXIfStatement : public CXXStatement {
private:
  std::string condition;

public:
  CXXIfStatement(CXXCodeBlock* parent, llvm::StringRef condition);
  void print(llvm::raw_ostream&) const override;
  // FIXME: shouldn't be public
  CXXCodeBlockRef trueBlock;
  CXXCodeBlockRef falseBlock;
};

// CXXReturnIntStatement
class CXXReturnIntStatement : public CXXStatement {
private:
  int returnValue;

public:
  CXXReturnIntStatement(CXXCodeBlock* parent, int returnValue);
  void print(llvm::raw_ostream&) const override;
};

// CXXDeclAndDefnVarStatement
class CXXDeclAndDefnVarStatement : public CXXStatement {
private:
  CXXTypeRef ty;
  std::string name;
  std::string valueExpr;

public:
  CXXDeclAndDefnVarStatement(CXXDecl* parent, CXXTypeRef ty,
                             llvm::StringRef name, llvm::StringRef valueExpr);
  llvm::StringRef getName() const { return valueExpr; }
  void print(llvm::raw_ostream&) const override;
};

// This is a hack
// CXXGenericStatement
class CXXGenericStatement : public CXXStatement {
private:
  std::string statement;

public:
  CXXGenericStatement(CXXDecl* parent, llvm::StringRef statement);
  void print(llvm::raw_ostream&) const override;
};

class CXXProgram : public CXXDecl {
private:
  typedef std::vector<CXXDeclRef> declStorageTy;
  declStorageTy decls;
  // FIXME: This should really be a set but we want the order that libraries
  // are requested to be preserved.
  typedef std::vector<std::string> libNameStoreageTy;
  libNameStoreageTy requiredLibs;
  bool recordsRuntimeStats;

public:
  CXXProgram() : CXXDecl(nullptr), recordsRuntimeStats(false) {}
  void print(llvm::raw_ostream&) const override;
  void appendDecl(CXXDeclRef);
  void addRequiredLibrary(llvm::StringRef name); // FIXME: Remove unused feature
  bool
  libraryIsRequired(llvm::StringRef name) const; // FIXME: Remove unused feature
  bool getRecordsRuntimeStats() const { return recordsRuntimeStats; }
  void setRecordsRuntimeStats(bool v) { recordsRuntimeStats = v; }
  // Iterators
  declStorageTy::const_iterator cbegin() const { return decls.cbegin(); }
  declStorageTy::const_iterator cend() const { return decls.cend(); }
};
}
}
#endif
