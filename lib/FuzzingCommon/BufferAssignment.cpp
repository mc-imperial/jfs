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
#include "jfs/FuzzingCommon/BufferAssignment.h"
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

void BufferAssignment::appendElement(BufferElement& el) {
  chunks.push_back(el);
  cachedTypeBitWidth += el.getTypeBitWidth();
  cachedStoreBitWidth += el.getStoreBitWidth();
  assert(cachedTypeBitWidth == computeTypeBitWidth() && "bitwidth mismatch");
  assert(cachedStoreBitWidth == computeStoreBitWidth() && "bitwidth mismatch");
}

uint64_t BufferAssignment::computeTypeBitWidth() const {
  uint64_t totalWidth = 0;
  for (const auto& ba : chunks) {
    totalWidth += ba.getTypeBitWidth();
  }
  return totalWidth;
}

uint64_t BufferAssignment::computeStoreBitWidth() const {
  uint64_t totalWidth = 0;
  for (const auto& ba : chunks) {
    totalWidth += ba.getStoreBitWidth();
  }
  return totalWidth;
}

void BufferAssignment::print(llvm::raw_ostream& os) const {
  os << "(BufferAssignment " << getTypeBitWidth() << " type bits, "
     << getStoreBitWidth() << " store bits)";
  if (chunks.size() > 0) {
    os << "\n";
  }
  for (const auto& be : chunks) {
    os << "  ";
    be.print(os);
  }
  os << ")\n";
}

void BufferAssignment::dump() const { print(llvm::errs()); }

} // namespace fuzzingCommon
} // namespace jfs
