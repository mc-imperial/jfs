//===----------------------------------------------------------------------===//
//
//                                     JFS
//
// Copyright 2017-2018 Alastair Donaldson
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#include "jfs/FuzzingCommon/FileSerializableModel.h"

// We reuse the runtime code to also save and load assignments on disk.
#include "SMTLIB/NativeBitVector.h"
#include "SMTLIB/NativeFloat.h"

using namespace jfs::core;

namespace {

bool accessInRange(size_t bufferSize, unsigned startBit, unsigned endBit) {
  unsigned startByte = startBit / 8;
  unsigned endByte = endBit / 8;
  return endBit >= startBit && startByte < bufferSize && endByte < bufferSize;
}

bool accessInRange(const llvm::MemoryBuffer* mb, unsigned startBit,
                   unsigned endBit) {
  return accessInRange(mb->getBufferSize(), startBit, endBit);
}

bool accessInRange(const llvm::FileOutputBuffer* buf, unsigned startBit,
                   unsigned bitWidth) {
  unsigned endBit = startBit + bitWidth - 1;
  return accessInRange(buf->getBufferSize(), startBit, endBit);
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

bool saveBool(JFSContext& ctx, llvm::FileOutputBuffer* buf, Z3SortHandle sort,
              Z3AppHandle assignment, unsigned startBit, unsigned bitWidth) {
  assert(sort.isBoolTy());
  if (!accessInRange(buf, startBit, bitWidth)) {
    ctx.raiseFatalError("save out of range of buffer");
    return false;
  }
  assert(bitWidth <= 8);
  assert(bitWidth > 0);
  jfs_nr_bitvector_ty rawBits = 0;
  if (assignment.asAST().isTrue()) {
    rawBits = 1;
  }
  jfs_nr_write_bitvector(
      /*bv=*/rawBits,
      /*bitWidth=*/bitWidth,
      /*bufferData=*/reinterpret_cast<uint8_t*>(buf->getBufferStart()),
      /*bufferSize=*/buf->getBufferSize(),
      /*bitOffset=*/startBit);
  return true;
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

bool saveBitVector(JFSContext& ctx, llvm::FileOutputBuffer* buf,
                   Z3SortHandle sort, Z3AppHandle assignment, unsigned startBit,
                   unsigned bitWidth) {
  assert(sort.isBitVectorTy());
  if (!accessInRange(buf, startBit, bitWidth)) {
    ctx.raiseFatalError("save out of range of buffer");
    return false;
  }
  assert(bitWidth == sort.getBitVectorWidth());
  assert(bitWidth > 0);
  if (bitWidth > 64) {
    // TODO: When we support larger sorts add support here to save them
    // to the buffer.
    ctx.raiseFatalError("Can't save > 64 bit wide bitvector");
    return false;
  }
  jfs_nr_bitvector_ty bv;
  if (!assignment.getConstantAsUInt64(&bv)) {
    ctx.raiseFatalError("Failed to get bitvector constant while saving");
    return false;
  }
  jfs_nr_write_bitvector(
      /*bv=*/bv,
      /*bitWidth=*/bitWidth,
      /*bufferData=*/reinterpret_cast<uint8_t*>(buf->getBufferStart()),
      /*bufferSize=*/buf->getBufferSize(),
      /*bitOffset=*/startBit);
  return true;
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
    ctx.raiseFatalError("Can't load unsupported floating-point type");
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

bool saveFloatingPointSpecial32(JFSContext& ctx, llvm::FileOutputBuffer* buf,
                                Z3SortHandle sort, Z3AppHandle assignment,
                                unsigned startBit, unsigned bitWidth) {
  jfs_nr_float32 value;
  switch (assignment.getKind()) {
  case Z3_OP_FPA_PLUS_ZERO:
    value = jfs_nr_float32_get_zero(/*positive=*/true);
    break;
  case Z3_OP_FPA_MINUS_ZERO:
    value = jfs_nr_float32_get_zero(/*positive=*/false);
    break;
  case Z3_OP_FPA_PLUS_INF:
    value = jfs_nr_float32_get_infinity(/*positive=*/true);
    break;
  case Z3_OP_FPA_MINUS_INF:
    value = jfs_nr_float32_get_infinity(/*positive=*/false);
    break;
  case Z3_OP_FPA_NAN:
    value = jfs_nr_float32_get_nan(/*quiet=*/true);
    break;
  default:
    llvm_unreachable("Expected special floating point constant");
  }
  jfs_nr_bitvector_ty valueAsBits = 0;
  std::memcpy(&valueAsBits, &value, sizeof value);
  jfs_nr_write_bitvector(
      /*bv=*/valueAsBits,
      /*bitWidth=*/bitWidth,
      /*bufferData=*/reinterpret_cast<uint8_t*>(buf->getBufferStart()),
      /*bufferSize=*/buf->getBufferSize(),
      /*bitOffset=*/startBit);
  return true;
}

bool saveFloatingPointSpecial64(JFSContext& ctx, llvm::FileOutputBuffer* buf,
                                Z3SortHandle sort, Z3AppHandle assignment,
                                unsigned startBit, unsigned bitWidth) {
  jfs_nr_float64 value;
  switch (assignment.getKind()) {
  case Z3_OP_FPA_PLUS_ZERO:
    value = jfs_nr_float64_get_zero(/*positive=*/true);
    break;
  case Z3_OP_FPA_MINUS_ZERO:
    value = jfs_nr_float64_get_zero(/*positive=*/false);
    break;
  case Z3_OP_FPA_PLUS_INF:
    value = jfs_nr_float64_get_infinity(/*positive=*/true);
    break;
  case Z3_OP_FPA_MINUS_INF:
    value = jfs_nr_float64_get_infinity(/*positive=*/false);
    break;
  case Z3_OP_FPA_NAN:
    value = jfs_nr_float64_get_nan(/*quiet=*/true);
    break;
  default:
    llvm_unreachable("Expected special floating point constant");
  }
  jfs_nr_bitvector_ty valueAsBits = 0;
  std::memcpy(&valueAsBits, &value, sizeof value);
  jfs_nr_write_bitvector(
      /*bv=*/valueAsBits,
      /*bitWidth=*/bitWidth,
      /*bufferData=*/reinterpret_cast<uint8_t*>(buf->getBufferStart()),
      /*bufferSize=*/buf->getBufferSize(),
      /*bitOffset=*/startBit);
  return true;
}

bool saveFloatingPoint(JFSContext& ctx, llvm::FileOutputBuffer* buf,
                       Z3SortHandle sort, Z3AppHandle assignment,
                       unsigned startBit, unsigned bitWidth) {
  assert(sort.isFloatingPointTy());
  unsigned ebits = sort.getFloatingPointExponentBitWidth();
  unsigned sbits = sort.getFloatingPointSignificandBitWidth();

  // Handle special constants
  if (assignment.isSpecialFPConstant()) {
    if (ebits == 8 && sbits == 24) {
      // Float32
      return saveFloatingPointSpecial32(ctx, buf, sort, assignment, startBit,
                                        bitWidth);
    } else if (ebits == 11 && sbits == 53) {
      // Float64
      return saveFloatingPointSpecial64(ctx, buf, sort, assignment, startBit,
                                        bitWidth);
    } else {
      ctx.raiseFatalError("Can't save unsupported floating-point type");
      return false;
    }
  }

  // Handle numeric constants through conversion to a bit vector.
  Z3ASTHandle convToBv = Z3ASTHandle(
      Z3_mk_fpa_to_ieee_bv(ctx.getZ3Ctx(), assignment.asAST()), ctx.getZ3Ctx());
  // Simplify the expression so we have a bit vector.
  Z3ASTHandle assignmentBv =
      Z3ASTHandle(Z3_simplify(ctx.getZ3Ctx(), convToBv), ctx.getZ3Ctx());

  assert(assignmentBv.isConstant());
  sort = assignmentBv.getSort();
  assert(sort.isBitVectorTy());

  return saveBitVector(ctx, buf, sort, assignmentBv.asApp(), startBit,
                       bitWidth);
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

bool FileSerializableModel::saveTo(llvm::FileOutputBuffer* buf,
                                   const BufferAssignment* ba,
                                   jfs::core::JFSContext& ctx) {
  assert(buf != nullptr);
  assert(ba != nullptr);

  // Check buffer size is as expected
  if (buf->getBufferSize() != ba->getRequiredStoreBytes()) {
    ctx.getWarningStream()
        << "(warning Failed to save model to file due to size mismatch."
           "expected:"
        << ba->getRequiredStoreBytes() << " actual:" << buf->getBufferSize()
        << " bytes)";
    return false;
  }

  // Initialize the buffer to all zeros because later steps won't write to the
  // padding bits. If we don't do this, those bits will be left uninitialized
  // which could cause non-determinism when seeding the fuzzer with the
  // serialized model.
  memset(buf->getBufferStart(), 0, buf->getBufferSize());

  unsigned currentBufferBit = 0;
  for (const auto& be : *ba) {
    // Save assignment to buffer.
    const unsigned bitWidth = be.getTypeBitWidth();

    Z3ASTHandle assignment = getAssignmentFor(be.getDecl());
    assert(!assignment.isNull());

    // Dispatch to the appropriate helper function for the expr sort
    bool success;
    switch (be.getSort().getKind()) {
    case Z3_BOOL_SORT: {
      success = saveBool(ctx, buf, be.getSort(), assignment.asApp(),
                         currentBufferBit, bitWidth);
      break;
    }
    case Z3_BV_SORT: {
      success = saveBitVector(ctx, buf, be.getSort(), assignment.asApp(),
                              currentBufferBit, bitWidth);
      break;
    }
    case Z3_FLOATING_POINT_SORT: {
      success = saveFloatingPoint(ctx, buf, be.getSort(), assignment.asApp(),
                                  currentBufferBit, bitWidth);
      break;
    }
    default:
      llvm_unreachable("Unhandled sort");
    }

    assert(success);

    // Notice we use `getStoreBitWidth() and not `getTypeBitWidth()`.
    // This means that if the type has alignment that we will skip
    // some bits.
    currentBufferBit += be.getStoreBitWidth();
  }

  // Commit saved contents to disk.
  if (auto error = buf->commit()) {
    auto errCode = llvm::errorToErrorCode(std::move(error));
    ctx.getErrorStream()
        << "(error Failed to commit model because \"" << errCode.message()
        << "\")\n";
    return false;
  }

  return true;
};
} // namespace fuzzingCommon
} // namespace jfs
