//===----------------------------------------------------------------------===//
//
//                        JFS - The JIT Fuzzing Solver
//
// Copyright 2017-2018 Daniel Liew
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#include "jfs/FuzzingCommon/BufferElement.h"
#include "jfs/Core/IfVerbose.h"
#include "jfs/Core/Z3NodeSet.h"
#include "jfs/FuzzingCommon/CommandLineCategory.h"
#include "llvm/Support/CommandLine.h"
#include <algorithm>
#include <list>
#include <vector>

using namespace jfs::core;

namespace jfs {
namespace fuzzingCommon {

BufferElement::BufferElement(const Z3ASTHandle declApp,
                             size_t storeBitAlignment)
    : storeBitAlignment(storeBitAlignment), declApp(declApp) {
  assert(declApp.isApp() && "should be an application");
  assert(declApp.asApp().isFreeVariable() && "should be an application");
  assert(this->storeBitAlignment > 0 && "Alignment must be > 0");
}

unsigned BufferElement::getTypeBitWidth() const {
  Z3SortHandle sort = declApp.getSort();
  switch (sort.getKind()) {
  case Z3_BOOL_SORT:
    return 1;
  case Z3_BV_SORT:
    return sort.getBitVectorWidth();
  case Z3_FLOATING_POINT_SORT:
    return sort.getFloatingPointBitWidth();
  default:
    llvm_unreachable("Unhandled sort");
  }
}

unsigned BufferElement::getStoreBitWidth() const {
  assert(storeBitAlignment > 0);
  unsigned result =
      ((getTypeBitWidth() + (storeBitAlignment - 1)) / storeBitAlignment) *
      storeBitAlignment;
  assert((result % storeBitAlignment) == 0);
  return result;
}

Z3FuncDeclHandle BufferElement::getDecl() const {
  return declApp.asApp().getFuncDecl();
}

std::string BufferElement::getName() const { return getDecl().getName(); }

Z3SortHandle BufferElement::getSort() const { return declApp.getSort(); }

void BufferElement::print(llvm::raw_ostream& os) const {
  os << "(" << getDecl().getName() << ":" << getTypeBitWidth();
  if (getStoreBitWidth() != getTypeBitWidth()) {
    os << " (store width:" << getStoreBitWidth() << ")";
  }
  if (equalities.size() > 0) {
    os << " equalities: ";
    for (const auto& e : equalities) {
      os << " (" << e.toStr() << ")";
    }
  }
  os << ")\n";
}

void BufferElement::dump() const { print(llvm::errs()); }

} // namespace fuzzingCommon
} // namespace jfs
