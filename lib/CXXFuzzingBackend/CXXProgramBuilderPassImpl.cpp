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
#include <ctype.h>
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
  case Z3_FLOATING_POINT_SORT: {
    unsigned exponentBits = sort.getFloatingPointExponentBitWidth();
    unsigned significandBits = sort.getFloatingPointSignificandBitWidth();
    std::string underlyingString;
    llvm::raw_string_ostream ss(underlyingString);
    ss << "Float<" << exponentBits << "," << significandBits << ">";
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
  program->appendDecl(std::make_shared<CXXIncludeDecl>(
      program.get(), "SMTLIB/Float.h", /*systemHeader=*/false));
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
  // NOTE: Z3's implementation doesn't include the `|` in quoted symbol
  // names. So both quoted and un-quoted symbols are handled in the same
  // way.
  if (name.size() == 0) {
    // This is silly but SMT-LIB seems to allow the empty string (when quoted
    // i.e. `||`) as a symbol name so pick our own name for this.
    return "jfs__empty__";
  }
  std::string buffer;
  // Walkthrough string copying across allowed characters
  // and replacing disallowed characters
  bool requiredChange = false;
  for (const auto& character : name) {
    if (isalnum(character) || character == '_') {
      buffer += character;
      continue;
    }
    requiredChange = true;
    // Valid Simple symbol character in SMT-LIBv2 but not
    // valid for use as an identifier in C++.
    switch (character) {
#define ACTION(SEARCH, REPL)                                                   \
  case SEARCH:                                                                 \
    buffer += REPL;                                                            \
    continue;
      ACTION('~', "_t_");
      ACTION('!', "_ex_");
      ACTION('@', "_at_");
      ACTION('$', "_ds_");
      ACTION('%', "_pc_");
      ACTION('^', "_c_");
      ACTION('&', "_a_");
      ACTION('*', "_s_");
      ACTION('-', "_m_");
      ACTION('+', "_p_");
      ACTION('=', "_e_");
      ACTION('<', "_lt_");
      ACTION('>', "_gt_");
      ACTION('.', "_d_");
      ACTION('?', "_q_");
      ACTION('/', "_fs_");
#undef ACTION
    default:
      // In all other cases just use `_`.
      buffer += '_';
    }
  }

  if (!requiredChange) {
    assert(name.size() > 0);
    return name;
  }

  // FIXME: We need to avoid clashes with our own internal symbols names
  // and C++ keywords.
  assert(buffer.size() > 0);
  return buffer;
}

llvm::StringRef
CXXProgramBuilderPassImpl::insertSymbol(const std::string& symbolName) {
  std::string sanitizedName = getSanitizedVariableName(symbolName);
  // Check the sanitized name isn't already used. If it is
  // apply naive algorithm
  if (usedSymbols.count(sanitizedName) > 0) {
    sanitizedName += "_";
    ssize_t indexToStartAt = sanitizedName.size() - 1;
    char toWrite = '0';
    do {
      if (toWrite == '0') {
        sanitizedName += 'X'; // Write place holder
        ++indexToStartAt;
      }
      sanitizedName[indexToStartAt] = toWrite;
      ++toWrite;
      if (toWrite == ('9' + 1)) {
        // Wrap around
        toWrite = '0';
      }
    } while (usedSymbols.count(sanitizedName) > 0);
  }
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
      assert((endBufferBit - currentBufferBit + 1) <= 8);
      ss << "makeBoolFrom(" << bufferRefName << ", " << currentBufferBit << ", "
         << endBufferBit << ")";
      break;
    }
    case Z3_BV_SORT: {
      ss << "makeBitVectorFrom"
         << "<" << be.getBitWidth() << ">(" << bufferRefName << ", "
         << currentBufferBit << ", " << endBufferBit << ")";
      break;
    }
    case Z3_FLOATING_POINT_SORT: {
      ss << "makeFloatFrom<" << be.getSort().getFloatingPointExponentBitWidth()
         << "," << be.getSort().getFloatingPointSignificandBitWidth() << ">("
         << bufferRefName << ", " << currentBufferBit << ", " << endBufferBit
         << ")";
      break;
    }
    default:
      llvm_unreachable("Unhandled sort");
    }
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
    std::string symbolName = key.asApp().getFuncDecl().getName();
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
  uint64_t value = 0;
  bool success = e.getConstantAsUInt64(&value);
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

bool CXXProgramBuilderPassImpl::hasBeenVisited(jfs::core::Z3ASTHandle e) const {
  return exprToSymbolName.count(e) > 0;
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
      if (!hasBeenVisited(node)) {
        visit(node);
      }
      continue;
    }

    // Must be an internal node
    if (!traversingBackUpQueue.empty() &&
        traversingBackUpQueue.front() == node) {
      // We are visiting the node for a second time. Do "post order" visit
      queue.pop_front();
      traversingBackUpQueue.pop_front();
      if (!hasBeenVisited(node)) {
        visit(node);
      }
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
      Z3ASTHandle childExpr = nodeAsApp.getKid((numKids - 1) - index);
      // Only add the child expr to the queue if it has not been visited
      // before. This is to avoid traversing down a large AST subtree
      // that we've visited before.
      if (!hasBeenVisited(childExpr)) {
        queue.push_front(childExpr);
      }
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

#define BV_NARY_OP(NAME, CALL_NAME)                                            \
  void CXXProgramBuilderPassImpl::NAME(Z3AppHandle e) {                        \
    const unsigned numArgs = e.getNumKids();                                   \
    assert(numArgs >= 2);                                                      \
    std::string underlyingString;                                              \
    llvm::raw_string_ostream ss(underlyingString);                             \
    auto arg0 = e.getKid(0);                                                   \
    /* Correct number of opening braces*/                                      \
    for (unsigned index = 2; index < numArgs; ++index) {                       \
      ss << "(";                                                               \
    }                                                                          \
                                                                               \
    for (unsigned index = 1; index < numArgs; ++index) {                       \
      if (index == 1) {                                                        \
        ss << getSymbolFor(arg0);                                              \
      }                                                                        \
      auto argN = e.getKid(index);                                             \
      if (index > 1) {                                                         \
        /* Closing brace for previous operation */                             \
        ss << ")";                                                             \
      }                                                                        \
      ss << "." #CALL_NAME "(" << getSymbolFor(argN) << ")";                   \
    }                                                                          \
    insertSSAStmt(e.asAST(), ss.str());                                        \
  }

BV_BIN_OP(visitBvSub, bvsub)
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
BV_BIN_OP(visitBvComp, bvcomp)
BV_BIN_OP(visitBvNand, bvnand)
BV_BIN_OP(visitBvNor, bvnor)
BV_BIN_OP(visitBvXnor, bvxnor)
BV_BIN_OP(visitBvShl, bvshl)
BV_BIN_OP(visitBvLShr, bvlshr)
BV_BIN_OP(visitBvAShr, bvashr)

// Bitvector NAry operations. Even though in SMT-LIBv2 these ops are binary Z3
// allows n-ary versions which could be introduced by its simplication steps.
// We assume these operations are associative so it doesn't matter the order we
// apply them in.
BV_NARY_OP(visitBvOr, bvor)
BV_NARY_OP(visitBvAnd, bvand)
BV_NARY_OP(visitBvXor, bvxor)
BV_NARY_OP(visitBvAdd, bvadd)
BV_NARY_OP(visitBvMul, bvmul)

#undef BV_BIN_OP
#undef BV_NARY_OP

void CXXProgramBuilderPassImpl::visitBvRotateLeft(Z3AppHandle e) {
  // The rotation amount is not an argument
  assert(e.getNumKids() == 1);
  std::string underlyingString;
  llvm::raw_string_ostream ss(underlyingString);
  auto arg0 = e.getKid(0);
  auto funcDecl = e.getFuncDecl();

  // Get the rotation count. This is a paramter on the function
  // declaration rather an argument in the application
  assert(funcDecl.getNumParams() == 1);
  assert(funcDecl.getParamKind(0) == Z3_PARAMETER_INT);
  int rotation = funcDecl.getIntParam(0);

  ss << getSymbolFor(arg0) << ".rotate_left(" << rotation << ")";
  insertSSAStmt(e.asAST(), ss.str());
}

void CXXProgramBuilderPassImpl::visitBvRotateRight(Z3AppHandle e) {
  // The rotation amount is not an argument
  assert(e.getNumKids() == 1);
  std::string underlyingString;
  llvm::raw_string_ostream ss(underlyingString);
  auto arg0 = e.getKid(0);
  auto funcDecl = e.getFuncDecl();

  // Get the rotation count. This is a paramter on the function
  // declaration rather an argument in the application
  assert(funcDecl.getNumParams() == 1);
  assert(funcDecl.getParamKind(0) == Z3_PARAMETER_INT);
  int rotation = funcDecl.getIntParam(0);

  ss << getSymbolFor(arg0) << ".rotate_right(" << rotation << ")";
  insertSSAStmt(e.asAST(), ss.str());
}

void CXXProgramBuilderPassImpl::visitBvConcat(jfs::core::Z3AppHandle e) {
  const unsigned numArgs = e.getNumKids();
  assert(numArgs >= 2);
  std::string underlyingString;
  llvm::raw_string_ostream ss(underlyingString);
  auto arg0 = e.getKid(0);

  // Correct number of opening braces
  for (unsigned index = 2; index < numArgs; ++index) {
    ss << "(";
  }

  for (unsigned index = 1; index < numArgs; ++index) {
    if (index == 1) {
      ss << getSymbolFor(arg0);
    }
    auto argN = e.getKid(index);
    if (index > 1) {
      // Closing brace for previous concat
      ss << ")";
    }
    ss << ".concat(" << getSymbolFor(argN) << ")";
  }
  insertSSAStmt(e.asAST(), ss.str());
}

void CXXProgramBuilderPassImpl::visitBvSignExtend(Z3AppHandle e) {
  // The extension amount is not an argument
  assert(e.getNumKids() == 1);
  std::string underlyingString;
  llvm::raw_string_ostream ss(underlyingString);
  auto arg0 = e.getKid(0);
  auto funcDecl = e.getFuncDecl();

  // Get the extension count. This is a paramter on the function
  // declaration rather an argument in the application
  assert(funcDecl.getNumParams() == 1);
  assert(funcDecl.getParamKind(0) == Z3_PARAMETER_INT);
  int numberOfNewBits = funcDecl.getIntParam(0);

  ss << getSymbolFor(arg0) << ".signExtend<" << numberOfNewBits << ">()";
  insertSSAStmt(e.asAST(), ss.str());
}

void CXXProgramBuilderPassImpl::visitBvZeroExtend(Z3AppHandle e) {
  // The extension amount is not an argument
  assert(e.getNumKids() == 1);
  std::string underlyingString;
  llvm::raw_string_ostream ss(underlyingString);
  auto arg0 = e.getKid(0);
  auto funcDecl = e.getFuncDecl();

  // Get the extension count. This is a paramter on the function
  // declaration rather an argument in the application
  assert(funcDecl.getNumParams() == 1);
  assert(funcDecl.getParamKind(0) == Z3_PARAMETER_INT);
  int numberOfNewBits = funcDecl.getIntParam(0);

  ss << getSymbolFor(arg0) << ".zeroExtend<" << numberOfNewBits << ">()";
  insertSSAStmt(e.asAST(), ss.str());
}

void CXXProgramBuilderPassImpl::visitBvExtract(Z3AppHandle e) {
  // The bit indices are not arguments
  assert(e.getNumKids() == 1);
  std::string underlyingString;
  llvm::raw_string_ostream ss(underlyingString);
  auto arg0 = e.getKid(0);
  auto funcDecl = e.getFuncDecl();

  // Get the indicies
  // Get the extension count. This is a paramter on the function
  // declaration rather an argument in the application
  assert(funcDecl.getNumParams() == 2);
  assert(funcDecl.getParamKind(0) == Z3_PARAMETER_INT);
  assert(funcDecl.getParamKind(1) == Z3_PARAMETER_INT);
  int highBit = funcDecl.getIntParam(0);
  int lowBit = funcDecl.getIntParam(1);
  assert(highBit >= lowBit);

  ss << getSymbolFor(arg0) << ".extract<" << ((highBit - lowBit) + 1) << ">("
     << highBit << "," << lowBit << ")";
  insertSSAStmt(e.asAST(), ss.str());
}

void CXXProgramBuilderPassImpl::visitBoolConstant(Z3AppHandle e) {
  insertSSAStmt(e.asAST(), getboolConstantStr(e));
}

void CXXProgramBuilderPassImpl::visitBitVector(Z3AppHandle e) {
  insertSSAStmt(e.asAST(), getBitVectorConstantStr(e));
}

// Floating point
void CXXProgramBuilderPassImpl::visitFloatingPointFromTriple(
    jfs::core::Z3AppHandle e) {
  assert(e.getNumKids() == 3);
  std::string underlyingString;
  llvm::raw_string_ostream ss(underlyingString);
  auto sort = e.getSort();
  auto signValue = e.getKid(0);
  auto exponentValue = e.getKid(1);
  auto significandValue = e.getKid(2);
  ss << "Float<" << sort.getFloatingPointExponentBitWidth() << ","
     << sort.getFloatingPointSignificandBitWidth() << ">("
     << getSymbolFor(signValue) << ", " << getSymbolFor(exponentValue) << ", "
     << getSymbolFor(significandValue) << ")";
  insertSSAStmt(e.asAST(), ss.str());
}

void CXXProgramBuilderPassImpl::visitFloatingPointFromIEEEBitVector(
    Z3AppHandle e) {
  assert(e.getNumKids() == 1);
  auto bvExpr = e.getKid(0);
  assert(bvExpr.getSort().isBitVectorTy());
  auto resultSort = e.getSort();
  assert(resultSort.isFloatingPointTy());
  std::string underlyingString;
  llvm::raw_string_ostream ss(underlyingString);
  ss << "Float<" << resultSort.getFloatingPointExponentBitWidth() << ","
     << resultSort.getFloatingPointSignificandBitWidth() << ">("
     << getSymbolFor(bvExpr) << ")";
  insertSSAStmt(e.asAST(), ss.str());
}
}
}
