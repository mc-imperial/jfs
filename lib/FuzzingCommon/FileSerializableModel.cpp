//===----------------------------------------------------------------------===//
//
//                        JFS - The JIT Fuzzing Solver
//
// Copyright 2017-2018 Alastair Donaldson
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#include "jfs/FuzzingCommon/FileSerializableModel.h"

// We reuse the runtime code to also load assignments from disk.
#include "SMTLIB/NativeBitVector.h"

using namespace jfs::core;

namespace {

bool accessInRange(const llvm::MemoryBuffer* mb, unsigned startBit,
                   unsigned endBit) {
  unsigned startByte = startBit / 8;
  unsigned endByte = endBit / 8;
  return endBit >= startBit && startByte < mb->getBufferSize() &&
         endByte < mb->getBufferSize();
}

Z3ASTHandle loadBool(JFSContext& ctx, const llvm::MemoryBuffer* mb,
                     Z3SortHandle sort, unsigned startBit, unsigned endBit) {
  assert(sort.isBoolTy());
  if (!accessInRange(mb, startBit, endBit)) {
    ctx.raiseFatalError("load out of range of buffer");
    return Z3ASTHandle();
  }
  unsigned bitWidth = (endBit - startBit) + 1;
  assert(bitWidth <= 8);
  assert(bitWidth > 0);
  jfs_nr_bitvector_ty rawBits = jfs_nr_make_bitvector(
      /*bufferData=*/reinterpret_cast<const uint8_t*>(mb->getBufferStart()),
      /*bufferSize=*/mb->getBufferSize(),
      /*lowBit=*/startBit,
      /*highBit=*/endBit);
  if (rawBits)
    return Z3ASTHandle::getTrue(ctx.getZ3Ctx());
  return Z3ASTHandle::getFalse(ctx.getZ3Ctx());
}

Z3ASTHandle loadBitVector(JFSContext& ctx, const llvm::MemoryBuffer* mb,
                          Z3SortHandle sort, unsigned startBit,
                          unsigned endBit) {
  assert(sort.isBitVectorTy());
  if (!accessInRange(mb, startBit, endBit)) {
    ctx.raiseFatalError("load out of range of buffer");
    return Z3ASTHandle();
  }
  auto bitWidth = sort.getBitVectorWidth(); // In bits
  assert(bitWidth == (endBit - startBit + 1));
  assert(bitWidth > 0);
  if (bitWidth > 64) {
    // TODO: When we support larger sorts add support here to load them
    // from the buffer.
    ctx.raiseFatalError("Can't load > 64 bit wide bitvector");
    return Z3ASTHandle();
  }
  jfs_nr_bitvector_ty rawBits = jfs_nr_make_bitvector(
      /*bufferData=*/reinterpret_cast<const uint8_t*>(mb->getBufferStart()),
      /*bufferSize=*/mb->getBufferSize(),
      /*lowBit=*/startBit,
      /*highBit=*/endBit);
  return Z3ASTHandle(Z3_mk_unsigned_int64(ctx.getZ3Ctx(), rawBits, sort),
                     ctx.getZ3Ctx());
}

Z3ASTHandle loadFloatingPoint(JFSContext& ctx, const llvm::MemoryBuffer* mb,
                              Z3SortHandle sort, unsigned startBit,
                              unsigned endBit,
                              bool convertedBvAssignment = false) {
  assert(sort.isFloatingPointTy());
  unsigned ebits = sort.getFloatingPointExponentBitWidth();
  unsigned sbits = sort.getFloatingPointSignificandBitWidth();
  Z3ASTHandle e;
  // TODO: When we support other floating-point types add support here too.
  if (ebits == 8 && sbits == 24) {
    // Float32
    e = loadBitVector(ctx, mb, Z3SortHandle::getBitVectorTy(ctx.getZ3Ctx(), 32),
                      startBit, endBit);
  } else if (ebits == 11 && sbits == 53) {
    // Float64
    e = loadBitVector(ctx, mb, Z3SortHandle::getBitVectorTy(ctx.getZ3Ctx(), 64),
                      startBit, endBit);
  } else {
    ctx.raiseFatalError("Can't load unsupport floating-point type");
    return Z3ASTHandle();
  }

  // Create conversion AST node
  Z3ASTHandle convToFp =
      Z3ASTHandle(Z3_mk_fpa_to_fp_bv(ctx.getZ3Ctx(), e, sort), ctx.getZ3Ctx());
  if (convertedBvAssignment) {
    // Return non-constant expression (conversion of a constant)
    return convToFp;
  }
  // Simplify the expression so we have a plain constant.
  Z3ASTHandle simplified =
      Z3ASTHandle(Z3_simplify(ctx.getZ3Ctx(), convToFp), ctx.getZ3Ctx());
  assert(simplified.isConstant());
  return simplified;
}
} // namespace

namespace jfs {
namespace fuzzingCommon {

FileSerializableModel::FileSerializableModel(JFSContext& ctx)
    : jfs::core::Model(ctx) {
  // Empty model
  z3Model = Z3ModelHandle(Z3_mk_model(ctx.getZ3Ctx()), ctx.getZ3Ctx());
}

std::unique_ptr<FileSerializableModel>
FileSerializableModel::loadFrom(const llvm::MemoryBuffer* buf,
                                const BufferAssignment* ba, JFSContext& ctx) {
  assert(buf != nullptr);
  assert(ba != nullptr);
  std::unique_ptr<FileSerializableModel> fsm(new FileSerializableModel(ctx));
  auto z3Model = fsm->z3Model;

  // Check buffer size is as expected
  if (buf->getBufferSize() != ba->getRequiredStoreBytes()) {
    ctx.getWarningStream()
        << "(warning Failed to load model from file due to size mismatch."
           "expected:"
        << ba->getRequiredStoreBytes() << " actual:" << buf->getBufferSize()
        << " bytes)";
    return nullptr;
  }

  unsigned currentBufferBit = 0;
  for (const auto& be : *ba) {
    // Add assignment
    auto assignmentTy = be.getSort();
    unsigned endBufferBit = (currentBufferBit + be.getTypeBitWidth()) - 1;

    Z3ASTHandle assignmentExpr;
    // Dispatch to the appropriate helper function for the expr sort
    switch (be.getSort().getKind()) {
    case Z3_BOOL_SORT: {
      assignmentExpr =
          loadBool(ctx, buf, be.getSort(), currentBufferBit, endBufferBit);
      break;
    }
    case Z3_BV_SORT: {
      assignmentExpr =
          loadBitVector(ctx, buf, be.getSort(), currentBufferBit, endBufferBit);
      break;
    }
    case Z3_FLOATING_POINT_SORT: {
      assignmentExpr = loadFloatingPoint(ctx, buf, be.getSort(),
                                         currentBufferBit, endBufferBit);
      break;
    }
    default:
      llvm_unreachable("Unhandled sort");
    }

    // FIXME: Provide option to fold model assignments to pure constants.
    // Add assignment to Z3 model
    assert(!assignmentExpr.isNull());
    assert(assignmentExpr.isConstant());
    bool success = fsm->addAssignmentFor(be.getDecl(), assignmentExpr);
    assert(success);

    // Notice we use `getStoreBitWidth() and not `getTypeBitWidth()`.
    // This means that if the type has alignment that we will skip
    // some bits.
    currentBufferBit += be.getStoreBitWidth();
  }
  return fsm;
}
} // namespace fuzzingCommon
} // namespace jfs
