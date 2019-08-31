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
#include "jfs/CXXFuzzingBackend/CXXProgram.h"

namespace jfs {
namespace cxxfb {

// CXXDecl
void CXXDecl::dump() const { print(llvm::errs()); }

CXXDecl* CXXDecl::getParent() const { return parent; }

CXXDecl::CXXDecl(CXXDecl* parent) : parent(parent) {}

CXXDecl::~CXXDecl() {}

// CXXIncludeDecl

CXXIncludeDecl::CXXIncludeDecl(CXXDecl* parent, llvm::StringRef path,
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

CXXFunctionDecl::CXXFunctionDecl(CXXDecl* parent, llvm::StringRef name,
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
CXXType::CXXType(CXXDecl* parent, llvm::StringRef name, bool isConst)
    : CXXDecl(parent), name(name.str()), isConst(isConst) {}

CXXType::CXXType(CXXDecl* parent, llvm::StringRef name)
    : CXXType(parent, name, /*isConst=*/false) {}

CXXType::~CXXType() {}

void CXXType::print(llvm::raw_ostream& os) const {
  if (isConst) {
    os << "const ";
  }
  os << name;
}

// CXXFunctionArgument
CXXFunctionArgument::CXXFunctionArgument(CXXDecl* parent, llvm::StringRef name,
                                         CXXTypeRef argType)
    : CXXDecl(parent), name(name.str()), argType(argType) {}

CXXFunctionArgument::~CXXFunctionArgument() {}

void CXXFunctionArgument::print(llvm::raw_ostream& os) const {
  argType->print(os);
  os << " " << name;
}

// CXXCodeBlock
CXXCodeBlock::CXXCodeBlock(CXXDecl* parent) : CXXDecl(parent) {}
CXXCodeBlock::~CXXCodeBlock() {}

void CXXCodeBlock::print(llvm::raw_ostream& os) const {
  os << "{\n";
  for (const auto& st : statements) {
    st->print(os);
  }
  os << "}\n";
}

// CXXIfStatement
CXXIfStatement::CXXIfStatement(CXXCodeBlock* parent, llvm::StringRef condition)
    : CXXStatement(parent), condition(condition.str()), trueBlock(nullptr),
      falseBlock(nullptr) {}

void CXXIfStatement::print(llvm::raw_ostream& os) const {
  os << "if (" << condition << ")";
  if (trueBlock) {
    os << "\n";
    trueBlock->print(os);
  } else {
    os << " {}\n";
  }
  if (falseBlock) {
    os << "else ";
    falseBlock->print(os);
  }
}

// CXXReturnIntStatement
CXXReturnIntStatement::CXXReturnIntStatement(CXXCodeBlock* parent,
                                             int returnValue)
    : CXXStatement(parent), returnValue(returnValue) {}

void CXXReturnIntStatement::print(llvm::raw_ostream& os) const {
  os << "return " << returnValue << ";\n";
}

// CXXDeclAndDefnVarStatement
CXXDeclAndDefnVarStatement::CXXDeclAndDefnVarStatement(
    CXXDecl* parent, CXXTypeRef ty, llvm::StringRef name,
    llvm::StringRef valueExpr)
    : CXXStatement(parent), ty(ty), name(name.str()),
      valueExpr(valueExpr.str()) {}

void CXXDeclAndDefnVarStatement::print(llvm::raw_ostream& os) const {
  ty->print(os);
  os << " " << name << " = " << valueExpr << ";\n";
}

// CXXGenericStatement
CXXGenericStatement::CXXGenericStatement(CXXDecl* parent,
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

void CXXProgram::addRequiredLibrary(llvm::StringRef name) {
  requiredLibs.emplace_back(name.data(), name.size());
}

bool CXXProgram::libraryIsRequired(llvm::StringRef name) const {
  // FIXME: We should use a set to avoid being O(N).
  for (const auto& libName : requiredLibs) {
    if (libName == name) {
      return true;
    }
  }
  return false;
}
}
}
