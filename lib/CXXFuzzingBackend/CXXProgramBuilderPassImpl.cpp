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
#include "CXXProgramBuilderPassImpl.h"
#include "jfs/CXXFuzzingBackend/CXXProgram.h"
#include "jfs/Core/Z3Node.h"
#include "jfs/Core/Z3NodeMap.h"
#include <list>

using namespace jfs::core;
using namespace jfs::fuzzingCommon;

namespace jfs {
namespace cxxfb {

CXXProgramBuilderPassImpl::CXXProgramBuilderPassImpl(
    std::shared_ptr<FuzzingAnalysisInfo> info, JFSContext& ctx)
    : ctx(ctx), info(info) {
  program = std::make_shared<CXXProgram>();

  // Setup early exit code block
  earlyExitBlock = std::make_shared<CXXCodeBlock>(program.get());
  auto returnStmt =
      std::make_shared<CXXReturnIntStatement>(earlyExitBlock.get(), 0);
  earlyExitBlock->statements.push_front(returnStmt);
  entryPointMainBlock = nullptr;
}

CXXTypeRef CXXProgramBuilderPassImpl::getOrInsertTy(Z3SortHandle sort) {
  auto cachedIt = sortToCXXTypeCache.find(sort);
  if (cachedIt != sortToCXXTypeCache.end()) {
    return cachedIt->second;
  }
  // Don't have the sort cached. Construct the matching CXXType.
  switch (sort.getKind()) {
  case Z3_BOOL_SORT: {
    // Make const type so that Compiler enforces SSA.
    auto ty =
        std::make_shared<CXXType>(program.get(), "bool", /*isConst=*/true);
    sortToCXXTypeCache.insert(std::make_pair(sort, ty));
    return ty;
  }
  case Z3_BV_SORT: {
    unsigned width = sort.getBitVectorWidth();
    std::string underlyingString;
    llvm::raw_string_ostream ss(underlyingString);
    ss << "BitVector<" << width << ">";
    ss.flush();
    // Make const type so that Compiler enforces SSA.
    auto ty = std::make_shared<CXXType>(program.get(), underlyingString,
                                        /*isConst=*/true);
    sortToCXXTypeCache.insert(std::make_pair(sort, ty));
    return ty;
  }
  default:
    llvm_unreachable("Unhandled sort");
  }
}

CXXFunctionDeclRef CXXProgramBuilderPassImpl::buildEntryPoint() {
  program = std::make_shared<CXXProgram>();
  // Runtime header includes
  // FIXME: We should probe the query and only emit these header includes
  // if we actually need them.
  program->appendDecl(std::make_shared<CXXIncludeDecl>(program.get(),
                                                       "SMTLIB/Core.h",
                                                       /*systemHeader=*/false));
  program->appendDecl(std::make_shared<CXXIncludeDecl>(
      program.get(), "SMTLIB/BitVector.h", /*systemHeader=*/false));
  // Int types header for LibFuzzer entry point definition.
  program->appendDecl(std::make_shared<CXXIncludeDecl>(program.get(),
                                                       "stdint.h",
                                                       /*systemHeader=*/true));
  program->appendDecl(std::make_shared<CXXIncludeDecl>(program.get(),
                                                       "stdlib.h",
                                                       /*systemHeader=*/true));

  // Build entry point for LibFuzzer
  auto retTy = std::make_shared<CXXType>(program.get(), "int");
  auto firstArgTy = std::make_shared<CXXType>(program.get(), "const uint8_t*");
  auto secondArgTy = std::make_shared<CXXType>(program.get(), "size_t");
  entryPointFirstArgName = insertSymbol("data");
  auto firstArg = std::make_shared<CXXFunctionArgument>(
      program.get(), entryPointFirstArgName, firstArgTy);
  entryPointSecondArgName = insertSymbol("size");
  auto secondArg = std::make_shared<CXXFunctionArgument>(
      program.get(), entryPointSecondArgName, secondArgTy);
  auto funcArguments = std::vector<CXXFunctionArgumentRef>();
  funcArguments.push_back(firstArg);
  funcArguments.push_back(secondArg);
  auto funcDefn = std::make_shared<CXXFunctionDecl>(
      program.get(), "LLVMFuzzerTestOneInput", retTy, funcArguments,
      /*hasCVisibility=*/true);
  auto funcBody = std::make_shared<CXXCodeBlock>(funcDefn.get());
  funcDefn->defn = funcBody; // FIXME: shouldn't be done like this
  program->appendDecl(funcDefn);
  return funcDefn;
}

void CXXProgramBuilderPassImpl::insertBufferSizeGuard(CXXCodeBlockRef cb) {
  unsigned bufferWidthInBits =
      info->freeVariableAssignment->bufferAssignment->computeWidth();
  if (bufferWidthInBits == 0) {
    // Don't add guard to avoid Clang warning about
    // checking `size < 0`
    return;
  }
  std::string underlyingString;
  llvm::raw_string_ostream condition(underlyingString);
  // Round up to the number of bytes needed
  unsigned bufferWidthInBytes = (bufferWidthInBits + 7) / 8;
  condition << "size < " << bufferWidthInBytes;
  condition.flush();
  auto ifStatement =
      std::make_shared<CXXIfStatement>(cb.get(), underlyingString);
  ifStatement->trueBlock = earlyExitBlock;
  cb->statements.push_back(ifStatement);
}

std::string
CXXProgramBuilderPassImpl::getSanitizedVariableName(const std::string& name) {
  // TODO:
  // TODO: don't allow the bufferRef
  // TODO: don't allow `size`
  // TODO: don't allow `data`.
  return name;
}

llvm::StringRef
CXXProgramBuilderPassImpl::insertSymbol(const std::string& symbolName) {
  std::string sanitizedName = getSanitizedVariableName(symbolName);
  auto statusPair = usedSymbols.insert(sanitizedName);
  assert(statusPair.second && "cannot insert already used symbolName");
  return llvm::StringRef(*(statusPair.first));
}

llvm::StringRef CXXProgramBuilderPassImpl::insertSSASymbolForExpr(
    Z3ASTHandle e, const std::string& symbolName) {
  llvm::StringRef symbolNameRef = insertSymbol(symbolName);
  assert(!(e.isNull()));
  auto statusPair = exprToSymbolName.insert(std::make_pair(e, symbolNameRef));
  assert(statusPair.second && "expr already has symbol");
  return symbolNameRef;
}

void CXXProgramBuilderPassImpl::insertFreeVariableConstruction(
    CXXCodeBlockRef cb) {
  llvm::StringRef bufferRefName = insertSymbol("jfs_buffer_ref");
  const BufferAssignment& ba =
      *(info->freeVariableAssignment->bufferAssignment.get());
  if (ba.size() == 0) {
    // Don't emit anything if the buffer is empty to avoid
    // clang warnings about unused variables.
    return;
  }

  std::string underlyingString;
  llvm::raw_string_ostream ss(underlyingString);
  // Insert bufferRef.
  // FIXME: We should probably just use C++'s constructor syntax
  // BufferRef<const uint8_t> jfs_buffer_ref<const uint8_t>(data, size)
  auto bufferRefTy =
      std::make_shared<CXXType>(program.get(), "BufferRef<const uint8_t>");
  // Build `BufferRef<uint8_t>(data, size)` string.
  ss << bufferRefTy->getName() << "(" << entryPointFirstArgName << ", "
     << entryPointSecondArgName << ")";
  ss.flush();
  auto bufferRefAssignment = std::make_shared<CXXDeclAndDefnVarStatement>(
      cb.get(), bufferRefTy, bufferRefName, underlyingString);
  cb->statements.push_back(bufferRefAssignment);
  unsigned currentBufferBit = 0;

  // Walk through free variables and construct CXX code to initialize them
  // from the buffer.
  for (const auto& be : ba) {
    // Add assignment
    auto assignmentTy = getOrInsertTy(be.getSort());
    llvm::StringRef sanitizedSymbolName =
        insertSSASymbolForExpr(be.declApp, be.getName());
    unsigned endBufferBit = (currentBufferBit + be.getBitWidth()) - 1;

    // Build string `makeBitVectorFrom<a,b>(jfs_buffer_ref)`
    // where a is min bit and b is max bit from `jfs_buffer_ref`.
    underlyingString.clear();
    switch (be.getSort().getKind()) {
    case Z3_BOOL_SORT: {
      ss << "makeBoolFrom";
      break;
    }
    case Z3_BV_SORT: {
      ss << "makeBitVectorFrom";
      break;
    }
    default:
      llvm_unreachable("Unhandled sort");
    }
    ss << "<" << currentBufferBit << "," << endBufferBit << ">("
       << bufferRefName << ")";
    ss.flush();
    auto assignmentStmt = std::make_shared<CXXDeclAndDefnVarStatement>(
        cb.get(), assignmentTy, sanitizedSymbolName, underlyingString);
    cb->statements.push_back(assignmentStmt);

    currentBufferBit += be.getBitWidth();
    // Add equalities
    // FIXME: When we support casts this code will need to be fixed
    for (const auto& e : be.equalities) {
      assert(e.isFreeVariable() && "should be free variable");

      llvm::StringRef otherVarName =
          insertSSASymbolForExpr(e, e.asApp().getFuncDecl().getName());
      assert(e.getSort() == be.getSort() && "sorts don't match");
      auto equalityAssignmentStmt =
          std::make_shared<CXXDeclAndDefnVarStatement>(
              cb.get(), assignmentTy, otherVarName, sanitizedSymbolName);
      cb->statements.push_back(equalityAssignmentStmt);
    }
  }
}

void CXXProgramBuilderPassImpl::insertConstantAssignments(CXXCodeBlockRef cb) {
  // FIXME: Due to constant propagation constant assignments should not be
  // present. We probably should just remove this entirely.
  const ConstantAssignment& ca =
      *(info->freeVariableAssignment->constantAssignments);
  for (const auto& keyPair : ca.assignments) {
    Z3ASTHandle key = keyPair.first;
    Z3ASTHandle constantExpr = keyPair.second;
    assert(key.isFreeVariable());
    assert(constantExpr.isConstant());
    llvm::StringRef symbolName = key.asApp().getFuncDecl().getName();
    std::string exprAsStr;
    Z3AppHandle constantExprAsApp = constantExpr.asApp();
    switch (constantExprAsApp.getSort().getKind()) {
    case Z3_BOOL_SORT:
      exprAsStr = getboolConstantStr(constantExprAsApp);
      break;
    case Z3_BV_SORT:
      exprAsStr = getBitVectorConstantStr(constantExprAsApp);
      break;
    default:
      llvm_unreachable("Unhandled sort");
    }
    insertSSAStmt(key, exprAsStr, symbolName);
  }
}

void CXXProgramBuilderPassImpl::insertBranchForConstraint(
    Z3ASTHandle constraint) {
  assert(constraint.getSort().isBoolTy());
  // TODO: investigate whether it is better to construct
  // if (!e) { return 0; }
  //
  // or
  //
  // if (e) {} else { return 0;}

  // Construct all SSA variables to get the constraint as a symbol
  doDFSPostOrderTraversal(constraint);
  assert(exprToSymbolName.count(constraint) > 0);

  llvm::StringRef symbolForConstraint = getSymbolFor(constraint);
  auto ifStatement = std::make_shared<CXXIfStatement>(getCurrentBlock().get(),
                                                      symbolForConstraint);
  ifStatement->trueBlock = nullptr;
  ifStatement->falseBlock = earlyExitBlock;
  getCurrentBlock()->statements.push_back(ifStatement);
}

void CXXProgramBuilderPassImpl::insertFuzzingTarget(CXXCodeBlockRef cb) {
  // FIXME: Replace this with something that we can use to
  // communicate LibFuzzer's outcome
  cb->statements.push_back(
      std::make_shared<CXXCommentBlock>(cb.get(), "Fuzzing target"));
  cb->statements.push_back(
      std::make_shared<CXXGenericStatement>(cb.get(), "abort()"));
}

void CXXProgramBuilderPassImpl::build(const Query& q) {
  JFSContext& ctx = q.getContext();
  auto fuzzFn = buildEntryPoint();
  entryPointMainBlock = fuzzFn->defn;

  insertBufferSizeGuard(fuzzFn->defn);
  insertFreeVariableConstruction(fuzzFn->defn);
  insertConstantAssignments(fuzzFn->defn);

  // Generate constraint branches
  for (const auto& constraint : q.constraints) {
    insertBranchForConstraint(constraint);
  }
  insertFuzzingTarget(fuzzFn->defn);
}

const char* CXXProgramBuilderPassImpl::getboolConstantStr(Z3AppHandle e) const {
  switch (e.getKind()) {
  case Z3_OP_TRUE:
    return "true";
  case Z3_OP_FALSE:
    return "false";
  default:
    llvm_unreachable("Unexpected expr");
  }
}

std::string
CXXProgramBuilderPassImpl::getBitVectorConstantStr(Z3AppHandle e) const {
  assert(e.isConstant());
  Z3SortHandle sort = e.getSort();
  assert(sort.isBitVectorTy());
  unsigned bitWidth = sort.getBitVectorWidth();
  assert(bitWidth <= 64 && "Support for wide bitvectors not implemented");
  std::string underlyingString;
  llvm::raw_string_ostream ss(underlyingString);

  ss << "BitVector<" << bitWidth << ">(UINT64_C(";
  // Get constant
  __uint64 value = 0; // Eurgh: Z3's API, can't use uint64_t
  static_assert(sizeof(__uint64) == sizeof(uint64_t), "size mismatch");
  bool success = Z3_get_numeral_uint64(e.getContext(), e.asAST(), &value);
  assert(success && "Failed to get numeral value");
  ss << value;
  ss << "))";
  ss.flush();
  return underlyingString;
}

std::string CXXProgramBuilderPassImpl::getFreshSymbol() {
  // TODO: Do something more sophisticatd
  static uint64_t counter = 0;
  std::string underlyingString;
  llvm::raw_string_ostream ss(underlyingString);
  ss << "jfs_ssa_" << counter;
  ss.flush();
  ++counter;
  assert(getSanitizedVariableName(underlyingString) == underlyingString);
  assert(usedSymbols.count(underlyingString) == 0);
  return underlyingString;
}

void CXXProgramBuilderPassImpl::insertSSAStmt(
    jfs::core::Z3ASTHandle e, llvm::StringRef expr,
    llvm::StringRef preferredSymbolName) {
  auto assignmentTy = getOrInsertTy(e.getSort());
  std::string requestedSymbolName;
  if (preferredSymbolName.data() == nullptr) {
    requestedSymbolName = getFreshSymbol();
  } else {
    requestedSymbolName = preferredSymbolName;
    if (usedSymbols.count(requestedSymbolName) > 0) {
      requestedSymbolName = getFreshSymbol();
    }
  }
  llvm::StringRef usedSymbol = insertSSASymbolForExpr(e, requestedSymbolName);
  auto assignmentStmt = std::make_shared<CXXDeclAndDefnVarStatement>(
      getCurrentBlock().get(), assignmentTy, usedSymbol, expr);
  getCurrentBlock()->statements.push_back(assignmentStmt);
}

void CXXProgramBuilderPassImpl::visitIfNeccesary(jfs::core::Z3ASTHandle e) {
  if (exprToSymbolName.count(e) == 0)
    visit(e);
}

void CXXProgramBuilderPassImpl::doDFSPostOrderTraversal(Z3ASTHandle e) {
  // Do post-order DFS traversal. We do this non-recursively to avoid
  // hitting any recursion bounds.
  std::list<Z3ASTHandle> queue;
  // Used to keep track of when we examine a node with children
  // for a second time. This indicates that the children have been
  // travsersed so that we can now do the "post order" visit
  std::list<Z3ASTHandle> traversingBackUpQueue;
  queue.push_front(e);
  while (queue.size() > 0) {
    Z3ASTHandle node = queue.front();
    assert(node.isApp());

    // Check for leaf node
    if (node.asApp().getNumKids() == 0) {
      queue.pop_front();
      // Do "post order" visit
      visitIfNeccesary(node);
      continue;
    }

    // Must be an internal node
    if (!traversingBackUpQueue.empty() &&
        traversingBackUpQueue.front() == node) {
      // We are visiting the node for a second time. Do "post order" visit
      queue.pop_front();
      traversingBackUpQueue.pop_front();
      visitIfNeccesary(node);
      continue;
    }
    // Visit an internal node for the first time. Add the children to the front
    // of the queue but don't pop this node from the stack so we can visit it a
    // second time when are walking back up the tree.
    traversingBackUpQueue.push_front(node);
    Z3AppHandle nodeAsApp = node.asApp();
    const unsigned numKids = nodeAsApp.getNumKids();
    for (unsigned index = 0; index < numKids; ++index) {
      // Add the operands from right to left so that they popped
      // off in left to right order
      queue.push_front(nodeAsApp.getKid((numKids - 1) - index));
    }
  }
  assert(traversingBackUpQueue.size() == 0);
}

llvm::StringRef
CXXProgramBuilderPassImpl::getSymbolFor(jfs::core::Z3ASTHandle e) const {
  // This is a helper for visitor methods so they can grab symbols without
  // having to check themselves that the key is present. Due to the post
  // order DFS traversal the abort should never be called unless there's
  // a bug in the DFS traversal or visitor methods.
  auto it = exprToSymbolName.find(e);
  if (it == exprToSymbolName.end()) {
    ctx.getErrorStream()
        << "(error attempt to use symbol before it has been defined)\n";
    abort();
  }
  return it->second;
}

// Visitor methods
void CXXProgramBuilderPassImpl::visitEqual(jfs::core::Z3AppHandle e) {
  assert(e.getNumKids() == 2);
  auto arg0 = e.getKid(0);
  auto arg1 = e.getKid(1);
  std::string underlyingString;
  llvm::raw_string_ostream ss(underlyingString);
  ss << getSymbolFor(arg0) << " == " << getSymbolFor(arg1);
  insertSSAStmt(e.asAST(), ss.str());
}
void CXXProgramBuilderPassImpl::visitDistinct(Z3AppHandle e) {
  const unsigned numArgs = e.getNumKids();
  assert(numArgs >= 2);
  std::string underlyingString;
  llvm::raw_string_ostream ss(underlyingString);

  // FIXME: This is terrible and quadratically explodes.  It also doesn't look
  // like the rest of our "three address code" style statements.
  // Output pairwise `!=` combinations.
  bool isFirst = true;
  for (unsigned firstArgIndex = 0; firstArgIndex < numArgs; ++firstArgIndex) {
    for (unsigned secondArgIndex = firstArgIndex + 1; secondArgIndex < numArgs;
         ++secondArgIndex) {
      auto arg0 = e.getKid(firstArgIndex);
      auto arg1 = e.getKid(secondArgIndex);
      if (isFirst) {
        isFirst = false;
      } else {
        ss << " && ";
      }
      ss << "( " << getSymbolFor(arg0) << " != " << getSymbolFor(arg1) << " )";
    }
  }
  insertSSAStmt(e.asAST(), ss.str());
}

void CXXProgramBuilderPassImpl::visitIfThenElse(jfs::core::Z3AppHandle e) {
  assert(e.getNumKids() == 3);
  auto condition = e.getKid(0);
  auto trueExpr = e.getKid(1);
  auto falseExpr = e.getKid(2);
  std::string underlyingString;
  llvm::raw_string_ostream ss(underlyingString);
  ss << "(" << getSymbolFor(condition) << ")?(" << getSymbolFor(trueExpr)
     << "):(" << getSymbolFor(falseExpr) << ")";
  insertSSAStmt(e.asAST(), ss.str());
}

void CXXProgramBuilderPassImpl::visitImplies(jfs::core::Z3AppHandle e) {
  assert(e.getNumKids() == 2);
  auto antecdent = e.getKid(0);
  auto consequent = e.getKid(1);
  std::string underlyingString;
  llvm::raw_string_ostream ss(underlyingString);
  // (a => b) === (!a) | b
  ss << "(!" << getSymbolFor(antecdent) << ") || " << getSymbolFor(consequent);
  insertSSAStmt(e.asAST(), ss.str());
}

void CXXProgramBuilderPassImpl::visitIff(jfs::core::Z3AppHandle e) {
  assert(e.getNumKids() == 2);
  auto arg0 = e.getKid(0);
  auto arg1 = e.getKid(1);
  std::string underlyingString;
  llvm::raw_string_ostream ss(underlyingString);
  // (a <=> b) === (a == b)
  ss << getSymbolFor(arg0) << " == " << getSymbolFor(arg1);
  insertSSAStmt(e.asAST(), ss.str());
}

void CXXProgramBuilderPassImpl::visitAnd(Z3AppHandle e) {
  const unsigned numArgs = e.getNumKids();
  assert(numArgs >= 2);
  std::string underlyingString;
  llvm::raw_string_ostream ss(underlyingString);
  for (unsigned index = 0; index < numArgs; ++index) {
    if (index != 0)
      ss << " && ";
    auto arg = e.getKid(index);
    ss << getSymbolFor(arg);
  }
  insertSSAStmt(e.asAST(), ss.str());
}

void CXXProgramBuilderPassImpl::visitOr(jfs::core::Z3AppHandle e) {
  const unsigned numArgs = e.getNumKids();
  assert(numArgs >= 2);
  std::string underlyingString;
  llvm::raw_string_ostream ss(underlyingString);
  for (unsigned index = 0; index < numArgs; ++index) {
    if (index != 0)
      ss << " || ";
    auto arg = e.getKid(index);
    assert(exprToSymbolName.count(arg) > 0);
    ss << getSymbolFor(arg);
  }
  insertSSAStmt(e.asAST(), ss.str());
}

void CXXProgramBuilderPassImpl::visitXor(jfs::core::Z3AppHandle e) {
  assert(e.getNumKids() == 2);
  std::string underlyingString;
  llvm::raw_string_ostream ss(underlyingString);
  auto arg0 = e.getKid(0);
  auto arg1 = e.getKid(1);
  ss << getSymbolFor(arg0) << " ^ " << getSymbolFor(arg1);
  insertSSAStmt(e.asAST(), ss.str());
}

void CXXProgramBuilderPassImpl::visitNot(jfs::core::Z3AppHandle e) {
  assert(e.getNumKids() == 1);
  std::string underlyingString;
  llvm::raw_string_ostream ss(underlyingString);
  auto arg0 = e.getKid(0);
  assert(exprToSymbolName.count(arg0) > 0);
  ss << "!(" << getSymbolFor(arg0) << ")";
  insertSSAStmt(e.asAST(), ss.str());
}

#define BV_UNARY_OP(NAME, CALL_NAME)                                           \
  void CXXProgramBuilderPassImpl::NAME(Z3AppHandle e) {                        \
    assert(e.getNumKids() == 1);                                               \
    auto arg0 = e.getKid(0);                                                   \
    std::string underlyingString;                                              \
    llvm::raw_string_ostream ss(underlyingString);                             \
    ss << getSymbolFor(arg0) << "." #CALL_NAME "()";                           \
    insertSSAStmt(e.asAST(), ss.str());                                        \
  }
BV_UNARY_OP(visitBvNeg, bvneg)
BV_UNARY_OP(visitBvNot, bvnot)
#undef BV_UNARY_OP

// Convenience macro to avoid writing lots of duplicate code
#define BV_BIN_OP(NAME, CALL_NAME)                                             \
  void CXXProgramBuilderPassImpl::NAME(Z3AppHandle e) {                        \
    assert(e.getNumKids() == 2);                                               \
    auto arg0 = e.getKid(0);                                                   \
    auto arg1 = e.getKid(1);                                                   \
    std::string underlyingString;                                              \
    llvm::raw_string_ostream ss(underlyingString);                             \
    ss << getSymbolFor(arg0) << "." #CALL_NAME "(" << getSymbolFor(arg1)       \
       << ")";                                                                 \
    insertSSAStmt(e.asAST(), ss.str());                                        \
  }

BV_BIN_OP(visitBvAdd, bvadd)
BV_BIN_OP(visitBvSub, bvsub)
BV_BIN_OP(visitBvMul, bvmul)
BV_BIN_OP(visitBvSDiv, bvsdiv)
BV_BIN_OP(visitBvUDiv, bvudiv)
BV_BIN_OP(visitBvSRem, bvsrem)
BV_BIN_OP(visitBvURem, bvurem)
BV_BIN_OP(visitBvSMod, bvsmod)
BV_BIN_OP(visitBvULE, bvule)
BV_BIN_OP(visitBvSLE, bvsle)
BV_BIN_OP(visitBvUGE, bvuge)
BV_BIN_OP(visitBvSGE, bvsge)
BV_BIN_OP(visitBvULT, bvult)
BV_BIN_OP(visitBvSLT, bvslt)
BV_BIN_OP(visitBvUGT, bvugt)
BV_BIN_OP(visitBvSGT, bvsgt)
BV_BIN_OP(visitBvAnd, bvand)
BV_BIN_OP(visitBvOr, bvor)

#undef BV_BIN_OP

void CXXProgramBuilderPassImpl::visitBoolConstant(Z3AppHandle e) {
  insertSSAStmt(e.asAST(), getboolConstantStr(e));
}

void CXXProgramBuilderPassImpl::visitBitVector(Z3AppHandle e) {
  insertSSAStmt(e.asAST(), getBitVectorConstantStr(e));
}
}
}
