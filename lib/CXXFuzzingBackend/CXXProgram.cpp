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

// CXXStatement

CXXStatement::~CXXStatement() {}

// CXXCommentBlock

void CXXCommentBlock::print(llvm::raw_ostream& os) const {
  os << "// " << comment << "\n";
}

// CXXFunctionDecl

CXXFunctionDecl::CXXFunctionDecl(CXXDeclRef parent, llvm::StringRef name,
                                 CXXTypeRef returnTy,
                                 std::vector<CXXFunctionArgumentRef>& arguments,
                                 bool hasCVisibility)
    : CXXDecl(parent), name(name.str()), returnTy(returnTy),
      arguments(arguments), hasCVisibility(hasCVisibility), defn(nullptr) {}

CXXFunctionDecl::~CXXFunctionDecl() {}

void CXXFunctionDecl::print(llvm::raw_ostream& os) const {
  if (hasCVisibility)
    os << "extern \"C\" ";

  returnTy->print(os);
  os << " " << name << "(";
  for (unsigned index = 0; index < arguments.size(); ++index) {
    arguments[index]->print(os);
    if (index != (arguments.size() - 1)) {
      os << ", ";
    }
  }
  os << ")";
  if (defn.get() == nullptr) {
    // Just a declaration
    os << ";\n";
    return;
  }
  // print block
  os << "\n";
  defn->print(os);
}

// CXXType
CXXType::CXXType(CXXDeclRef parent, llvm::StringRef name)
    : CXXDecl(parent), name(name.str()) {}
CXXType::~CXXType() {}

void CXXType::print(llvm::raw_ostream& os) const { os << name; }

// CXXFunctionArgument
CXXFunctionArgument::CXXFunctionArgument(CXXDeclRef parent,
                                         llvm::StringRef name,
                                         CXXTypeRef argType)
    : CXXDecl(parent), name(name.str()), argType(argType) {}

CXXFunctionArgument::~CXXFunctionArgument() {}

void CXXFunctionArgument::print(llvm::raw_ostream& os) const {
  argType->print(os);
  os << " " << name;
}

// CXXCodeBlock
CXXCodeBlock::CXXCodeBlock(CXXDeclRef parent) : CXXDecl(parent) {}
CXXCodeBlock::~CXXCodeBlock() {}

void CXXCodeBlock::print(llvm::raw_ostream& os) const {
  os << "{\n";
  for (const auto& st : statements) {
    st->print(os);
  }
  os << "}\n";
}

// CXXIfStatement
CXXIfStatement::CXXIfStatement(CXXCodeBlockRef parent,
                               llvm::StringRef condition)
    : CXXStatement(parent), condition(condition.str()), trueBlock(nullptr),
      falseBlock(nullptr) {}

void CXXIfStatement::print(llvm::raw_ostream& os) const {
  os << "if (" << condition << ")\n";
  trueBlock->print(os);
  if (falseBlock) {
    os << "else ";
    falseBlock->print(os);
  }
}

// CXXReturnIntStatement
CXXReturnIntStatement::CXXReturnIntStatement(CXXCodeBlockRef parent,
                                             int returnValue)
    : CXXStatement(parent), returnValue(returnValue) {}

void CXXReturnIntStatement::print(llvm::raw_ostream& os) const {
  os << "return " << returnValue << ";\n";
}

// CXXDeclAndDefnVarStatement
CXXDeclAndDefnVarStatement::CXXDeclAndDefnVarStatement(
    CXXCodeBlockRef parent, CXXTypeRef ty, llvm::StringRef name,
    llvm::StringRef valueExpr)
    : CXXStatement(parent), ty(ty), name(name.str()),
      valueExpr(valueExpr.str()) {}

void CXXDeclAndDefnVarStatement::print(llvm::raw_ostream& os) const {
  ty->print(os);
  os << " " << name << " = " << valueExpr << ";\n";
}

// CXXGenericStatement
CXXGenericStatement::CXXGenericStatement(CXXCodeBlockRef parent,
                                         llvm::StringRef statement)
    : CXXStatement(parent), statement(statement.str()) {}

void CXXGenericStatement::print(llvm::raw_ostream& os) const {
  os << statement << ";\n";
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
