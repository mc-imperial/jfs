//===----------------------------------------------------------------------===//
//
//                        JFS - The JIT Fuzzing Solver
//
// Copyright 2018 J. Ryan Stinnett
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//

#include "jfs/FuzzingCommon/SpecialConstantSeedGenerator.h"
#include "jfs/Core/RNG.h"
#include "jfs/Core/Z3Node.h"
#include "jfs/Core/Z3NodeSet.h"
#include "jfs/FuzzingCommon/BufferElement.h"
#include "jfs/FuzzingCommon/FileSerializableModel.h"
#include "jfs/FuzzingCommon/FuzzingAnalysisInfo.h"
#include "jfs/FuzzingCommon/SeedManager.h"
#include <climits>

using namespace jfs::core;
using namespace jfs::fuzzingCommon;

namespace {

enum class SpecialConstantBitVector : size_t {
  ZERO,
  ONE,
  MAX_UNSIGNED_INT,
  MAX_SIGNED_INT,
  SIZE, // Marks the size of the enum (must be the last entry)
};

enum class SpecialConstantFloatingPoint : size_t {
  POSITIVE_ZERO,
  NEGATIVE_ZERO,
  POSITIVE_INFINITY,
  NEGATIVE_INFINITY,
  NOT_A_NUMBER,
  POSITIVE_ONE,
  NEGATIVE_ONE,
  SMALLEST_POSITIVE_SUBNORMAL,
  LARGEST_POSITIVE_SUBNORMAL,
  SMALLEST_POSITIVE_NORMAL,
  LARGEST_POSITIVE_NORMAL,
  SMALLEST_NEGATIVE_SUBNORMAL,
  LARGEST_NEGATIVE_SUBNORMAL,
  SMALLEST_NEGATIVE_NORMAL,
  LARGEST_NEGATIVE_NORMAL,
  SIZE, // Marks the size of the enum (must be the last entry)
};

uint64_t getMask(const unsigned bitWidth) {
  assert(bitWidth <= 64);
  return (bitWidth >= 64) ? UINT64_MAX : ((UINT64_C(1) << bitWidth) - 1);
}
}

namespace jfs {
namespace fuzzingCommon {

bool SpecialConstantSeedGenerator::chooseBool(JFSContext& ctx,
                                              const BufferElement& be,
                                              Model& model) {
  assert(be.getSort().isBoolTy());
  bool value = ctx.getRNG().generate(2);
  Z3ASTHandle valueAsAST;
  if (value) {
    valueAsAST = Z3ASTHandle::getTrue(ctx.getZ3Ctx());
  } else {
    valueAsAST = Z3ASTHandle::getFalse(ctx.getZ3Ctx());
  }
  return model.addAssignmentFor(be.getDecl(), valueAsAST);
}

bool SpecialConstantSeedGenerator::chooseBitVector(JFSContext& ctx,
                                                   const BufferElement& be,
                                                   Model& model) {
  auto sort = be.getSort();
  unsigned width = sort.getBitVectorWidth();
  assert(sort.isBitVectorTy());
  assert(width > 0);
  assert(width <= 64);

  // Select from special constants for the sort and also any values for the sort
  // found in the constraints.
  const auto& valuesFromConstraints = sortToConstraintConstantMap[be.getSort()];
  const size_t specialConstantsSize =
      static_cast<size_t>(SpecialConstantBitVector::SIZE);
  size_t limit = specialConstantsSize + valuesFromConstraints.size();
  auto value =
      static_cast<SpecialConstantBitVector>(ctx.getRNG().generate(limit));

  // If we selected a value inside the range of the enum, create the selected
  // special constant. Otherwise, we selected a constant from the constraints.
  Z3ASTHandle valueAsAST;
  switch (value) {
  case SpecialConstantBitVector::ZERO:
    valueAsAST = Z3ASTHandle::getBV(sort, 0);
    break;
  case SpecialConstantBitVector::ONE:
    valueAsAST = Z3ASTHandle::getBV(sort, 1);
    break;
  case SpecialConstantBitVector::MAX_UNSIGNED_INT:
    // Max unsigned int is of the form 0b11..11.
    // This is equal to a mask for the full width of the bit vector.
    valueAsAST = Z3ASTHandle::getBV(sort, getMask(width));
    break;
  case SpecialConstantBitVector::MAX_SIGNED_INT:
    // Max unsigned int is of the form 0b01..11.
    // This is equal to a mask for one less than the width of the bit vector.
    valueAsAST = Z3ASTHandle::getBV(sort, getMask(width - 1));
    break;
  default:
    auto index = static_cast<size_t>(value) - specialConstantsSize;
    valueAsAST = valuesFromConstraints[index];
    break;
  }

  return model.addAssignmentFor(be.getDecl(), valueAsAST);
}

bool SpecialConstantSeedGenerator::chooseFloatingPoint(JFSContext& ctx,
                                                       const BufferElement& be,
                                                       Model& model) {
  auto sort = be.getSort();
  assert(sort.isFloatingPointTy());
  unsigned ebits = sort.getFloatingPointExponentBitWidth();
  unsigned sbits = sort.getFloatingPointSignificandBitWidth();
  assert((ebits == 8 && sbits == 24) || (ebits == 11 && sbits == 53));

  // Select from special constants for the sort and also any values for the sort
  // found in the constraints.
  const auto& valuesFromConstraints = sortToConstraintConstantMap[be.getSort()];
  const size_t specialConstantsSize =
      static_cast<size_t>(SpecialConstantFloatingPoint::SIZE);
  size_t limit = specialConstantsSize + valuesFromConstraints.size();
  auto value =
      static_cast<SpecialConstantFloatingPoint>(ctx.getRNG().generate(limit));

  // If we selected a value inside the range of the enum, create the selected
  // special constant. Otherwise, we selected a constant from the constraints.
  Z3ASTHandle valueAsAST;
  switch (value) {
  case SpecialConstantFloatingPoint::POSITIVE_ZERO:
    valueAsAST = Z3ASTHandle::getFloatZero(sort, /*positive=*/true);
    break;
  case SpecialConstantFloatingPoint::NEGATIVE_ZERO:
    valueAsAST = Z3ASTHandle::getFloatZero(sort, /*positive=*/false);
    break;
  case SpecialConstantFloatingPoint::POSITIVE_INFINITY:
    valueAsAST = Z3ASTHandle::getFloatInfinity(sort, /*positive=*/true);
    break;
  case SpecialConstantFloatingPoint::NEGATIVE_INFINITY:
    valueAsAST = Z3ASTHandle::getFloatInfinity(sort, /*positive=*/false);
    break;
  case SpecialConstantFloatingPoint::NOT_A_NUMBER:
    valueAsAST = Z3ASTHandle::getFloatNAN(sort);
    break;
  case SpecialConstantFloatingPoint::POSITIVE_ONE:
    valueAsAST = Z3ASTHandle::getFloatFromInt(sort, 1);
    break;
  case SpecialConstantFloatingPoint::NEGATIVE_ONE:
    valueAsAST = Z3ASTHandle::getFloatFromInt(sort, -1);
    break;
  case SpecialConstantFloatingPoint::SMALLEST_POSITIVE_SUBNORMAL:
    valueAsAST =
        Z3ASTHandle::getFloatAbsoluteSmallestSubnormal(sort, /*positive=*/true);
    break;
  case SpecialConstantFloatingPoint::LARGEST_POSITIVE_SUBNORMAL:
    valueAsAST =
        Z3ASTHandle::getFloatAbsoluteLargestSubnormal(sort, /*positive=*/true);
    break;
  case SpecialConstantFloatingPoint::SMALLEST_POSITIVE_NORMAL:
    valueAsAST =
        Z3ASTHandle::getFloatAbsoluteSmallestNormal(sort, /*positive=*/true);
    break;
  case SpecialConstantFloatingPoint::LARGEST_POSITIVE_NORMAL:
    valueAsAST =
        Z3ASTHandle::getFloatAbsoluteLargestNormal(sort, /*positive=*/true);
    break;
  case SpecialConstantFloatingPoint::SMALLEST_NEGATIVE_SUBNORMAL:
    valueAsAST =
        Z3ASTHandle::getFloatAbsoluteLargestSubnormal(sort, /*positive=*/false);
    break;
  case SpecialConstantFloatingPoint::LARGEST_NEGATIVE_SUBNORMAL:
    valueAsAST = Z3ASTHandle::getFloatAbsoluteSmallestSubnormal(
        sort, /*positive=*/false);
    break;
  case SpecialConstantFloatingPoint::SMALLEST_NEGATIVE_NORMAL:
    valueAsAST =
        Z3ASTHandle::getFloatAbsoluteLargestNormal(sort, /*positive=*/false);
    break;
  case SpecialConstantFloatingPoint::LARGEST_NEGATIVE_NORMAL:
    valueAsAST =
        Z3ASTHandle::getFloatAbsoluteSmallestNormal(sort, /*positive=*/false);
    break;
  default:
    auto index = static_cast<size_t>(value) - specialConstantsSize;
    valueAsAST = valuesFromConstraints[index];
    break;
  }

  return model.addAssignmentFor(be.getDecl(), valueAsAST);
}

void SpecialConstantSeedGenerator::preGenerationCallBack(SeedManager& sm) {
  auto query = sm.getCurrentQuery();
  auto& ctx = sm.getContext();

  // Do a DFS to find any constants in the constraints.
  std::list<Z3ASTHandle> workList;
  Z3ASTSet seenExpr;
  for (const auto& c : query->constraints) {
    workList.push_back(c);
  }
  while (workList.size() != 0) {
    Z3ASTHandle node = workList.front();
    workList.pop_front();
    if (seenExpr.count(node) > 0) {
      // Already visited
      continue;
    }
    seenExpr.insert(node);

    // If this is a constant, track it by sort.
    if (node.isConstant()) {
      auto sort = node.getSort();
      if (!sort.isBitVectorTy() && !sort.isFloatingPointTy()) {
        continue;
      }
      auto& constants = sortToConstraintConstantMap[sort];
      constants.push_back(node);
      continue;
    }

    // If this is a function application, visit the arguments.
    if (node.isApp()) {
      Z3AppHandle app = node.asApp();
      for (size_t index = 0; index < app.getNumKids(); index++) {
        workList.push_front(app.getKid(index));
      }
      continue;
    }

    llvm_unreachable("Unexpected node type");
  }

  if (ctx.getVerbosity() > 1) {
    ctx.getDebugStream() << "(Constants found in constraints:)\n";
    for (const auto& sortVectorPair : sortToConstraintConstantMap) {
      const auto& sort = sortVectorPair.first;
      ctx.getDebugStream() << "(Stored for sort: " << sort.toStr() << ")\n";
      for (const auto& constant : sortVectorPair.second) {
        ctx.getDebugStream() << "  (" << constant.toStr() << ")\n";
      }
    }
  }
}

bool SpecialConstantSeedGenerator::writeSeed(SeedManager& sm) {
  auto& ctx = sm.getContext();
  auto fai = sm.getCurrentFuzzingAnalysisInfo();
  const BufferAssignment* ba =
      fai->freeVariableAssignment->bufferAssignment.get();

  FileSerializableModel fsm(ctx);

  // For each buffer element, randomly choose an assignment from special
  // constants for its sort as well as any constants seen in the constraints.
  for (const auto& be : *ba) {
    auto sort = be.getSort();

    // Dispatch to the appropriate helper function for the expr sort
    bool success;
    switch (sort.getKind()) {
    case Z3_BOOL_SORT: {
      success = chooseBool(ctx, be, fsm);
      break;
    }
    case Z3_BV_SORT: {
      success = chooseBitVector(ctx, be, fsm);
      break;
    }
    case Z3_FLOATING_POINT_SORT: {
      success = chooseFloatingPoint(ctx, be, fsm);
      break;
    }
    default:
      llvm_unreachable("Unhandled sort");
    }

    if (!success) {
      std::string underlyingString;
      llvm::raw_string_ostream ss(underlyingString);
      ss << "Failed to generate assignment for \"";
      be.print(ss);
      ss << "\"";
      ctx.raiseError(ss.str());
      return false;
    }

    if (ctx.getVerbosity() > 1) {
      if (fsm.hasAssignmentFor(be.getDecl())) {
        ctx.getDebugStream()
            << "(Sort: " << sort.toStr()
            << ", Assignment: " << fsm.getAssignmentFor(be.getDecl()).toStr()
            << ")\n";
      } else {
        ctx.getDebugStream() << "(Sort: " << sort.toStr() << ", Unassigned)\n";
      }
    }
  }

  // FIXME: Consider tracking what has been generated to avoid duplicates. For
  // complex benchmarks, it seems simpler to keep selecting seeds randomly up to
  // whatever limit the `SeedManager` has. (This implies though that it must
  // have _some_ limit or else we'll select forever.)

  // Save seed value to disk via the model.
  return fsm.saveTo(sm.getBufferForSeed(getName()).get(), ba, ctx);
}

bool SpecialConstantSeedGenerator::empty() const { return false; }

} // namespace fuzzingCommon
} // namespace jfs
