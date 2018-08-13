#include "jfs/Core/JFSContext.h"
#include "jfs/Core/Z3Node.h"
#include "gtest/gtest.h"
#include <memory>

using namespace jfs::core;

std::unique_ptr<JFSContext> mkContext() {
  JFSContextConfig config;
  std::unique_ptr<JFSContext> ctx(new JFSContext(config));
  return std::move(ctx);
}

// Float32 subnormal special values.

TEST(Z3ASTNode, Float32AbsSmallestSubnormalPositive) {
  auto ctx = mkContext();
  auto ty = Z3SortHandle::getFloat32Ty(ctx->getZ3Ctx());
  auto e =
      Z3ASTHandle::getFloatAbsoluteSmallestSubnormal(ty, /*positive=*/true);
  ASSERT_STREQ(e.toStr().c_str(), "(fp #b0 #x00 #b00000000000000000000001)");
}

TEST(Z3ASTNode, Float32AbsSmallestSubnormalNegative) {
  auto ctx = mkContext();
  auto ty = Z3SortHandle::getFloat32Ty(ctx->getZ3Ctx());
  auto e =
      Z3ASTHandle::getFloatAbsoluteSmallestSubnormal(ty, /*positive=*/false);
  ASSERT_STREQ(e.toStr().c_str(), "(fp #b1 #x00 #b00000000000000000000001)");
}

TEST(Z3ASTNode, Float32AbsLargestSubnormalPositive) {
  auto ctx = mkContext();
  auto ty = Z3SortHandle::getFloat32Ty(ctx->getZ3Ctx());
  auto e = Z3ASTHandle::getFloatAbsoluteLargestSubnormal(ty, /*positive=*/true);
  ASSERT_STREQ(e.toStr().c_str(), "(fp #b0 #x00 #b11111111111111111111111)");
}

TEST(Z3ASTNode, Float32AbsLargestSubnormalNegative) {
  auto ctx = mkContext();
  auto ty = Z3SortHandle::getFloat32Ty(ctx->getZ3Ctx());
  auto e =
      Z3ASTHandle::getFloatAbsoluteLargestSubnormal(ty, /*positive=*/false);
  ASSERT_STREQ(e.toStr().c_str(), "(fp #b1 #x00 #b11111111111111111111111)");
}

// Float32 Normal special values.

TEST(Z3ASTNode, Float32AbsSmallestNormalPositive) {
  auto ctx = mkContext();
  auto ty = Z3SortHandle::getFloat32Ty(ctx->getZ3Ctx());
  auto e = Z3ASTHandle::getFloatAbsoluteSmallestNormal(ty, /*positive=*/true);
  ASSERT_STREQ(e.toStr().c_str(), "(fp #b0 #x01 #b00000000000000000000000)");
}

TEST(Z3ASTNode, Float32AbsSmallestNormalNegative) {
  auto ctx = mkContext();
  auto ty = Z3SortHandle::getFloat32Ty(ctx->getZ3Ctx());
  auto e = Z3ASTHandle::getFloatAbsoluteSmallestNormal(ty, /*positive=*/false);
  ASSERT_STREQ(e.toStr().c_str(), "(fp #b1 #x01 #b00000000000000000000000)");
}

TEST(Z3ASTNode, Float32AbsLargestNormalPositive) {
  auto ctx = mkContext();
  auto ty = Z3SortHandle::getFloat32Ty(ctx->getZ3Ctx());
  auto e = Z3ASTHandle::getFloatAbsoluteLargestNormal(ty, /*positive=*/true);
  ASSERT_STREQ(e.toStr().c_str(), "(fp #b0 #xfe #b11111111111111111111111)");
}

TEST(Z3ASTNode, Float32AbsLargestNormalNegative) {
  auto ctx = mkContext();
  auto ty = Z3SortHandle::getFloat32Ty(ctx->getZ3Ctx());
  auto e = Z3ASTHandle::getFloatAbsoluteLargestNormal(ty, /*positive=*/false);
  ASSERT_STREQ(e.toStr().c_str(), "(fp #b1 #xfe #b11111111111111111111111)");
}

// Float64 subnormal special values.

TEST(Z3ASTNode, Float64AbsSmallestSubnormalPositive) {
  auto ctx = mkContext();
  auto ty = Z3SortHandle::getFloat64Ty(ctx->getZ3Ctx());
  auto e =
      Z3ASTHandle::getFloatAbsoluteSmallestSubnormal(ty, /*positive=*/true);
  ASSERT_STREQ(e.toStr().c_str(), "(fp #b0 #b00000000000 #x0000000000001)");
}

TEST(Z3ASTNode, Float64AbsSmallestSubnormalNegative) {
  auto ctx = mkContext();
  auto ty = Z3SortHandle::getFloat64Ty(ctx->getZ3Ctx());
  auto e =
      Z3ASTHandle::getFloatAbsoluteSmallestSubnormal(ty, /*positive=*/false);
  ASSERT_STREQ(e.toStr().c_str(), "(fp #b1 #b00000000000 #x0000000000001)");
}

TEST(Z3ASTNode, Float64AbsLargestSubnormalPositive) {
  auto ctx = mkContext();
  auto ty = Z3SortHandle::getFloat64Ty(ctx->getZ3Ctx());
  auto e = Z3ASTHandle::getFloatAbsoluteLargestSubnormal(ty, /*positive=*/true);
  ASSERT_STREQ(e.toStr().c_str(), "(fp #b0 #b00000000000 #xfffffffffffff)");
}

TEST(Z3ASTNode, Float64AbsLargestSubnormalNegative) {
  auto ctx = mkContext();
  auto ty = Z3SortHandle::getFloat64Ty(ctx->getZ3Ctx());
  auto e =
      Z3ASTHandle::getFloatAbsoluteLargestSubnormal(ty, /*positive=*/false);
  ASSERT_STREQ(e.toStr().c_str(), "(fp #b1 #b00000000000 #xfffffffffffff)");
}

// Float64 Normal special values.

TEST(Z3ASTNode, Float64AbsSmallestNormalPositive) {
  auto ctx = mkContext();
  auto ty = Z3SortHandle::getFloat64Ty(ctx->getZ3Ctx());
  auto e = Z3ASTHandle::getFloatAbsoluteSmallestNormal(ty, /*positive=*/true);
  ASSERT_STREQ(e.toStr().c_str(), "(fp #b0 #b00000000001 #x0000000000000)");
}

TEST(Z3ASTNode, Float64AbsSmallestNormalNegative) {
  auto ctx = mkContext();
  auto ty = Z3SortHandle::getFloat64Ty(ctx->getZ3Ctx());
  auto e = Z3ASTHandle::getFloatAbsoluteSmallestNormal(ty, /*positive=*/false);
  ASSERT_STREQ(e.toStr().c_str(), "(fp #b1 #b00000000001 #x0000000000000)");
}

TEST(Z3ASTNode, Float64AbsLargestNormalPositive) {
  auto ctx = mkContext();
  auto ty = Z3SortHandle::getFloat64Ty(ctx->getZ3Ctx());
  auto e = Z3ASTHandle::getFloatAbsoluteLargestNormal(ty, /*positive=*/true);
  ASSERT_STREQ(e.toStr().c_str(), "(fp #b0 #b11111111110 #xfffffffffffff)");
}

TEST(Z3ASTNode, Float64AbsLargestNormalNegative) {
  auto ctx = mkContext();
  auto ty = Z3SortHandle::getFloat64Ty(ctx->getZ3Ctx());
  auto e = Z3ASTHandle::getFloatAbsoluteLargestNormal(ty, /*positive=*/false);
  ASSERT_STREQ(e.toStr().c_str(), "(fp #b1 #b11111111110 #xfffffffffffff)");
}

// TODO: Test other special constants, e.g. Inf, Nan, +zero, -zero.
