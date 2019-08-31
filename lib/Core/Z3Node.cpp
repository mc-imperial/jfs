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
#include "jfs/Core/Z3Node.h"
#include "jfs/Core/Model.h"
#include "llvm/Support/raw_ostream.h"
#include <assert.h>

namespace jfs {
namespace core {

template <> void Z3NodeHandle<Z3_sort>::dump() const {
  llvm::errs() << "Z3SortHandle:\n" << toStr() << "\n";
}
template <> std::string Z3NodeHandle<Z3_sort>::toStr() const {
  // FIXME: We need to grab a lock over all calls to `Z3_*_to_string()`
  // to make this thread safe.
  return ::Z3_sort_to_string(context, node);
}

template <> void Z3NodeHandle<Z3_ast>::dump() const {
  llvm::errs() << "Z3ASTHandle:\n" << toStr() << "\n";
}
template <> std::string Z3NodeHandle<Z3_ast>::toStr() const {
  // FIXME: We need to grab a lock over all calls to `Z3_*_to_string()`
  // to make this thread safe.
  return ::Z3_ast_to_string(context, node);
}

template <> void Z3NodeHandle<Z3_app>::dump() const {
  llvm::errs() << "Z3AppHandle:\n" << toStr() << "\n";
}
template <> std::string Z3NodeHandle<Z3_app>::toStr() const {
  // FIXME: We need to grab a lock over all calls to `Z3_*_to_string()`
  // to make this thread safe.
  return ::Z3_ast_to_string(context, ::Z3_app_to_ast(context, node));
}

template <> void Z3NodeHandle<Z3_func_decl>::dump() const {
  llvm::errs() << "Z3FuncDeclHandle:\n" << toStr() << "\n";
}
template <> std::string Z3NodeHandle<Z3_func_decl>::toStr() const {
  // FIXME: We need to grab a lock over all calls to `Z3_*_to_string()`
  // to make this thread safe.
  return ::Z3_ast_to_string(context, ::Z3_func_decl_to_ast(context, node));
}

template <> void Z3NodeHandle<Z3_solver>::dump() const {
  llvm::errs() << "Z3SolverHandle:\n" << toStr() << "\n";
}
template <> std::string Z3NodeHandle<Z3_solver>::toStr() const {
  // FIXME: We need to grab a lock over all calls to `Z3_*_to_string()`
  // to make this thread safe.
  return ::Z3_solver_to_string(context, node);
}

template <> void Z3NodeHandle<Z3_params>::dump() const {
  llvm::errs() << "Z3ParamsHandle:\n" << toStr() << "\n";
}
template <> std::string Z3NodeHandle<Z3_params>::toStr() const {
  // FIXME: We need to grab a lock over all calls to `Z3_*_to_string()`
  // to make this thread safe.
  return ::Z3_params_to_string(context, node);
}

// Z3ModelHandle helper methods
template <> void Z3NodeHandle<Z3_model>::dump() const {
  llvm::errs() << "Z3ModelHandle:\n" << toStr() << "\n";
}
template <> std::string Z3NodeHandle<Z3_model>::toStr() const {
  // FIXME: We need to grab a lock over all calls to `Z3_*_to_string()`
  // to make this thread safe.
  return ::Z3_model_to_string(context, node);
}

Z3ASTHandle Z3ModelHandle::getAssignmentFor(Z3FuncDeclHandle funcDecl) {
  assert(funcDecl.getContext() == context && "mismatched contexts");
  // TODO: Do we want to support assignments to uninterpreted functions too?
  return Z3ASTHandle(::Z3_model_get_const_interp(context, node, funcDecl),
                     context);
}

bool Z3ModelHandle::hasAssignmentFor(Z3FuncDeclHandle decl) const {
  assert(decl.getContext() == context && "mismached contexts");
  return ::Z3_model_has_interp(context, node, decl);
}

bool Z3ModelHandle::addAssignmentFor(Z3FuncDeclHandle decl, Z3ASTHandle e,
                                     bool allowOverwrite) {
  assert(decl.getContext() == context && "mistached decl and model context");
  assert(e.getContext() == context &&
         "mismatched assignment and model context");
  if (!allowOverwrite) {
    // Check if an assignment already exists
    if (hasAssignmentFor(decl)) {
      return false;
    }
  }
  if (!e.isConstant()) {
    // We only support constant assignments right now.
    // Z3's API allows giving assignments to arrays and
    // uninterpreted functions but let's not worry about that
    // right now.
    return false;
  }
  Z3_add_const_interp(context, node, decl, e);
  return true;
}

uint64_t Z3ModelHandle::getNumAssignments() const {
  if (context == nullptr || node == nullptr) {
    return 0;
  }
  return Z3_model_get_num_consts(context, node);
}

Z3FuncDeclHandle Z3ModelHandle::getVariableDeclForIndex(uint64_t index) {
  assert(index < getNumAssignments());
  return Z3FuncDeclHandle(::Z3_model_get_const_decl(context, node, index),
                          context);
}

Z3ASTHandle Z3ModelHandle::evaluate(Z3ASTHandle e, bool modelCompletion) {
  assert(e.getContext() == context);
  assert(!e.isNull());
  Z3_ast raw_ast = nullptr;
  bool success = ::Z3_model_eval(context, node, e,
                                 /*modelCompletion=*/modelCompletion, &raw_ast);
  if (!success) {
    return Z3ASTHandle();
  }
  return Z3ASTHandle(raw_ast, context);
}

bool Z3ModelHandle::isEmpty() const {
  return getNumAssignments() == 0;
}

// Z3SortHandle helper methods
Z3_sort_kind Z3SortHandle::getKind() const {
  return ::Z3_get_sort_kind(context, node);
}

bool Z3SortHandle::isBoolTy() const { return getKind() == Z3_BOOL_SORT; }

bool Z3SortHandle::isBitVectorTy() const { return getKind() == Z3_BV_SORT; }

bool Z3SortHandle::isFloatingPointTy() const {
  return getKind() == Z3_FLOATING_POINT_SORT;
}

unsigned Z3SortHandle::getWidth() const {
  switch (getKind()) {
  case Z3_BOOL_SORT:
    return 1;
  case Z3_BV_SORT:
    return getBitVectorWidth();
  case Z3_FLOATING_POINT_SORT:
    return getFloatingPointBitWidth();
  default:
    return 0;
  }
}

unsigned Z3SortHandle::getBitVectorWidth() const {
  if (getKind() != Z3_BV_SORT)
    return 0;
  unsigned width = ::Z3_get_bv_sort_size(context, node);
  return width;
}

unsigned Z3SortHandle::getFloatingPointExponentBitWidth() const {
  if (!isFloatingPointTy())
    return 0;
  return ::Z3_fpa_get_ebits(context, node);
}

unsigned Z3SortHandle::getFloatingPointSignificandBitWidth() const {
  if (!isFloatingPointTy())
    return 0;
  return ::Z3_fpa_get_sbits(context, node);
}

unsigned Z3SortHandle::getFloatingPointBitWidth() const {
  if (!isFloatingPointTy())
    return 0;
  return getFloatingPointExponentBitWidth() +
         getFloatingPointSignificandBitWidth();
}

Z3ASTHandle Z3SortHandle::asAST() const {
  return Z3ASTHandle(::Z3_sort_to_ast(context, node), context);
}

Z3SortHandle Z3SortHandle::getBoolTy(Z3_context ctx) {
  return Z3SortHandle(Z3_mk_bool_sort(ctx), ctx);
}

Z3SortHandle Z3SortHandle::getBitVectorTy(Z3_context ctx, unsigned bitWidth) {
  return Z3SortHandle(Z3_mk_bv_sort(ctx, bitWidth), ctx);
}

Z3SortHandle Z3SortHandle::getFloat32Ty(Z3_context ctx) {
  return Z3SortHandle(Z3_mk_fpa_sort_32(ctx), ctx);
}

Z3SortHandle Z3SortHandle::getFloat64Ty(Z3_context ctx) {
  return Z3SortHandle(Z3_mk_fpa_sort_64(ctx), ctx);
}

// Z3ASTHandle helper methods
Z3_ast_kind Z3ASTHandle::getKind() const {
  return ::Z3_get_ast_kind(context, node);
}

bool Z3ASTHandle::isApp() const {
  bool condition = ::Z3_is_app(context, node);
#ifndef NDEBUG
  if (condition)
    assert(getKind() == Z3_APP_AST || getKind() == Z3_NUMERAL_AST);
#endif
  return condition;
}

bool Z3ASTHandle::isFuncDecl() const { return getKind() == Z3_FUNC_DECL_AST; }

bool Z3ASTHandle::isSort() const { return getKind() == Z3_SORT_AST; }

bool Z3ASTHandle::isNumeral() const { return getKind() == Z3_NUMERAL_AST; }

bool Z3ASTHandle::isTrue() const {
#ifdef NDEBUG
  return isAppOf(Z3_OP_TRUE);
#else
  bool condition = isAppOf(Z3_OP_TRUE);
  if (condition)
    assert(isConstant() && "should be constant");

  return condition;
#endif
}

bool Z3ASTHandle::isFalse() const {
#ifdef NDEBUG
  return isAppOf(Z3_OP_FALSE);
#else
  bool condition = isAppOf(Z3_OP_FALSE);
  if (condition)
    assert(isConstant() && "should be constant");

  return condition;
#endif
}

bool Z3ASTHandle::isConstant() const {
  if (!isApp())
    return false;
  return asApp().isConstant();
}

bool Z3ASTHandle::isFreeVariable() const {
  if (!isApp())
    return false;
  return asApp().isFreeVariable();
}

bool Z3ASTHandle::isAppOf(Z3_decl_kind kind) const {
  if (!isApp())
    return false;

  return asApp().getKind() == kind;
}

bool Z3ASTHandle::isStructurallyEqualTo(Z3ASTHandle other) const {
  // Compare pointers
  if (this->node == other.node)
    return true;

  // This is a handle to nullptr. Given the above
  // check failed (i.e. the other is not a handle to nullptr)
  // we can't be equal.
  if (this->node == nullptr)
    return false;

  assert(this->context == other.context && "context mismatch");
  return ::Z3_is_eq_ast(context, *this, other);
}

Z3SortHandle Z3ASTHandle::getSort() const {
  if (isFuncDecl()) {
    // We assume that the client wants the range of the function declaration.
    return asFuncDecl().getSort();
  }
  return Z3SortHandle(::Z3_get_sort(context, node), context);
}

Z3AppHandle Z3ASTHandle::asApp() const {
  if (!isApp())
    return Z3AppHandle();
  return Z3AppHandle(::Z3_to_app(context, node), context);
}

Z3FuncDeclHandle Z3ASTHandle::asFuncDecl() const {
  if (!isFuncDecl())
    return Z3FuncDeclHandle();
  return Z3FuncDeclHandle(::Z3_to_func_decl(context, node), context);
}

Z3ASTHandle Z3ASTHandle::getTrue(Z3_context ctx) {
  return Z3ASTHandle(::Z3_mk_true(ctx), ctx);
}

Z3ASTHandle Z3ASTHandle::getFalse(Z3_context ctx) {
  return Z3ASTHandle(::Z3_mk_false(ctx), ctx);
}

Z3ASTHandle Z3ASTHandle::getBVZero(Z3_context ctx, unsigned width) {
  assert(width > 0);
  return getBVZero(Z3SortHandle::getBitVectorTy(ctx, width));
}

Z3ASTHandle Z3ASTHandle::getBVZero(Z3SortHandle sort) {
  return getBV(sort, 0);
}

Z3ASTHandle Z3ASTHandle::getBV(Z3SortHandle sort, uint64_t value) {
  assert(sort.isBitVectorTy());
  assert(sort.getBitVectorWidth() > 0);
  assert(sort.getBitVectorWidth() <= 64);
  return Z3ASTHandle(::Z3_mk_unsigned_int64(sort.getContext(), value, sort),
                     sort.getContext());
}

Z3ASTHandle Z3ASTHandle::getFloatZero(Z3SortHandle sort, bool positive) {
  assert(sort.isFloatingPointTy());
  return Z3ASTHandle(
      ::Z3_mk_fpa_zero(sort.getContext(), sort, /*negative=*/!positive),
      sort.getContext());
}

Z3ASTHandle Z3ASTHandle::getFloatInfinity(Z3SortHandle sort, bool positive) {
  assert(sort.isFloatingPointTy());
  return Z3ASTHandle(
      ::Z3_mk_fpa_inf(sort.getContext(), sort, /*negative=*/!positive),
      sort.getContext());
}

Z3ASTHandle Z3ASTHandle::getFloatNAN(Z3SortHandle sort) {
  assert(sort.isFloatingPointTy());
  return Z3ASTHandle(::Z3_mk_fpa_nan(sort.getContext(), sort),
                     sort.getContext());
}

Z3ASTHandle Z3ASTHandle::getFloatFromInt(Z3SortHandle sort, signed value) {
  assert(sort.isFloatingPointTy());
  return Z3ASTHandle(::Z3_mk_fpa_numeral_int(sort.getContext(), value, sort),
                     sort.getContext());
}

static size_t getEMax(Z3SortHandle fpSort) {
  assert(fpSort.isFloatingPointTy());
  // IEEE-754 3.4 defines e_max equal to the bias which is
  // 2^(w-1) -1, where `w` is the exponent bit width.
  size_t eBits = fpSort.getFloatingPointExponentBitWidth();
  size_t eMax = (1 << (eBits - 1)) - 1;
  return eMax;
}

static size_t getEMin(Z3SortHandle fpSort) {
  assert(fpSort.isFloatingPointTy());
  // Compute e_min for the floating point sort.
  // IEEE-754 2008 3.3, defines this as (1 - e_max)
  size_t eMax = getEMax(fpSort);
  size_t eMin = 1 - eMax;
  return eMin;
}
Z3ASTHandle Z3ASTHandle::getFloatAbsoluteSmallestSubnormal(Z3SortHandle sort,
                                                           bool positive) {
  assert(sort.isFloatingPointTy());
  size_t eMin = getEMin(sort);
  // Z3's `Z3_mk_fpa_numeral_int64_uint64(..)` is super unclear here.
  // It is not clear if the exponent is biased and whether or not
  // the implicit bit is included in the significand.
  //
  // Observations:
  // * `sig` does not include the implicit bit.
  // * `exp` appears to be signed and is the IEEE-754 binary encoding of the
  //   exponent  minus the bias.
  //
  // Note that the true exponent for the subnormal numbers and normals with the
  // smallest exponent is the same (e.g. for Float32 it's -126).
  //
  // Normals with smallest exp: 1.<significand bits> x 2^(-126)
  // Subnormals               : 0.<significand bits> x 2^(-126)
  //
  // However because the implicit bit is missing in the `sig` argument, the
  // only way to differentiate between subnormal and normal numbers is for the
  // value of `exp` to be different from the smallest exponent for normal
  // numbers. Using the smallest exponent for normal numbers -1 seems to work
  // but this API design is profoundly confusing.
  //
  // I guess the easiest way to think about this is that the `exp` argument is
  // the representation of the exponent in the IEEE-754 binary encoding minus
  // the bias. This is different from the true exponent.
  return Z3ASTHandle(Z3_mk_fpa_numeral_int64_uint64(
                         /*context=*/sort.getContext(),
                         /*sgn=*/!positive,
                         /*exp=*/eMin - 1,
                         /*sig=*/1,
                         /*typ=*/sort),
                     sort.getContext());
}

Z3ASTHandle Z3ASTHandle::getFloatAbsoluteLargestSubnormal(Z3SortHandle sort,
                                                          bool positive) {
  assert(sort.isFloatingPointTy());
  size_t eMin = getEMin(sort);
  // Z3's `Z3_mk_fpa_numeral_int64_uint64(..)` is super unclear here.
  // See getFloatAbsoluteSmallestSubnormal(...) for a discussion.
  // Note: Z3 seems to ignore the irrelevant bits for the sort in `sig`
  // so passing `UINT64_MAX` seems to be okay.
  return Z3ASTHandle(Z3_mk_fpa_numeral_int64_uint64(
                         /*context=*/sort.getContext(),
                         /*sgn=*/!positive,
                         /*exp=*/eMin - 1,
                         /*sig=*/UINT64_MAX,
                         /*typ=*/sort),
                     sort.getContext());
}

Z3ASTHandle Z3ASTHandle::getFloatAbsoluteSmallestNormal(Z3SortHandle sort,
                                                        bool positive) {
  assert(sort.isFloatingPointTy());
  size_t eMin = getEMin(sort);
  // Z3's `Z3_mk_fpa_numeral_int64_uint64(..)` is super unclear here.
  // See getFloatAbsoluteSmallestSubnormal(...) for a discussion.
  return Z3ASTHandle(Z3_mk_fpa_numeral_int64_uint64(
                         /*context=*/sort.getContext(),
                         /*sgn=*/!positive,
                         /*exp=*/eMin,
                         /*sig=*/0,
                         /*typ=*/sort),
                     sort.getContext());
}

Z3ASTHandle Z3ASTHandle::getFloatAbsoluteLargestNormal(Z3SortHandle sort,
                                                       bool positive) {
  assert(sort.isFloatingPointTy());
  size_t eMax = getEMax(sort);
  // Z3's `Z3_mk_fpa_numeral_int64_uint64(..)` is super unclear here.
  // See getFloatAbsoluteSmallestSubnormal(...) for a discussion.
  // Note: Z3 seems to ignore the irrelevant bits for the sort in `sig`
  // so passing `UINT64_MAX` seems to be okay.
  return Z3ASTHandle(Z3_mk_fpa_numeral_int64_uint64(
                         /*context=*/sort.getContext(),
                         /*sgn=*/!positive,
                         /*exp=*/eMax,
                         /*sig=*/UINT64_MAX,
                         /*typ=*/sort),
                     sort.getContext());
}

// Z3AppHandle helpers
Z3FuncDeclHandle Z3AppHandle::getFuncDecl() const {
  return Z3FuncDeclHandle(::Z3_get_app_decl(context, node), context);
}

Z3_decl_kind Z3AppHandle::getKind() const { return getFuncDecl().getKind(); }

unsigned Z3AppHandle::getNumKids() const {
  return ::Z3_get_app_num_args(context, node);
}

Z3ASTHandle Z3AppHandle::getKid(unsigned index) const {
  assert(index < getNumKids() && "accessing invalid kid index");
  return Z3ASTHandle(::Z3_get_app_arg(context, node, index), context);
}

bool Z3AppHandle::isConstant() const {
  if (getKind() == Z3_OP_FPA_FP) {
    // This is weird. If floating point constants have not
    // been run through the simplifier then they are Z3_OP_FPA_FP
    // rather than Z3_OP_FPA_NUM.
    //
    // To handle this case (it is not guaranteed that the simplifier was run) if
    // the operation is of this kind and all
    // three operands are constant then we treat this as a constant
    assert(getNumKids() == 3);
    if (getKid(0).isConstant() && getKid(1).isConstant() &&
        getKid(2).isConstant()) {
      return true;
    }
    return false;
  }
  if (getNumKids() != 0)
    return false;

  if (!::Z3_is_numeral_ast(context, ::Z3_app_to_ast(context, node)))
    return false; // Is free variable

  return true;
}

bool Z3AppHandle::isFreeVariable() const {
  if (getNumKids() != 0)
    return false;

  if (::Z3_is_numeral_ast(context, ::Z3_app_to_ast(context, node)))
    return false; // Is constant

  return true;
}

bool Z3AppHandle::isSpecialFPConstant() const {
  auto kind = getKind();
  return kind == Z3_OP_FPA_PLUS_ZERO || kind == Z3_OP_FPA_MINUS_ZERO ||
         kind == Z3_OP_FPA_PLUS_INF || kind == Z3_OP_FPA_MINUS_INF ||
         kind == Z3_OP_FPA_NAN;
}

Z3ASTHandle Z3AppHandle::asAST() const {
  return Z3ASTHandle(::Z3_app_to_ast(context, node), context);
}

Z3SortHandle Z3AppHandle::getSort() const { return asAST().getSort(); }

bool Z3AppHandle::getConstantAsUInt64(uint64_t* out) const {
  if (!isConstant())
    return false;

  __uint64 value = 0;
  static_assert(sizeof(__uint64) == sizeof(uint64_t), "size mismatch");
  bool success =
      Z3_get_numeral_uint64(context, ::Z3_app_to_ast(context, node), &value);
  if (success && out)
    *out = value;
  return success;
}

// Z3FuncDeclHandle helpers

Z3_decl_kind Z3FuncDeclHandle::getKind() const {
  return ::Z3_get_decl_kind(context, node);
}

Z3SortHandle Z3FuncDeclHandle::getSort() const {
  return Z3SortHandle(::Z3_get_range(context, node), context);
}

std::string Z3FuncDeclHandle::getName() const {
  Z3_symbol sym = ::Z3_get_decl_name(context, node);
  // We have to allocate storage because ::Z3_get_decl_name uses
  // a statically allocated buffer which is invalidated when the
  // next call occurs.
  return std::string(::Z3_get_symbol_string(context, sym));
}

Z3ASTHandle Z3FuncDeclHandle::asAST() const {
  return Z3ASTHandle(::Z3_func_decl_to_ast(context, node), context);
}

unsigned Z3FuncDeclHandle::getNumParams() const {
  return ::Z3_get_decl_num_parameters(context, node);
}

Z3_parameter_kind Z3FuncDeclHandle::getParamKind(unsigned index) const {
  assert(index < getNumParams());
  return ::Z3_get_decl_parameter_kind(context, node, index);
}

int Z3FuncDeclHandle::getIntParam(unsigned index) const {
  assert(getParamKind(index) == Z3_PARAMETER_INT);
  return ::Z3_get_decl_int_parameter(context, node, index);
}

// Z3GoalHandle

template <> void Z3NodeHandle<Z3_goal>::dump() const {
  llvm::errs() << "Z3GoalHandle:\n" << toStr() << "\n";
}

template <> std::string Z3NodeHandle<Z3_goal>::toStr() const {
  return ::Z3_goal_to_string(context, node);
}

void Z3GoalHandle::addFormula(Z3ASTHandle e) {
  assert(e.getContext() == context && "mismatched contexts");
  ::Z3_goal_assert(context, node, e);
}

unsigned Z3GoalHandle::getNumFormulas() const {
  return ::Z3_goal_size(context, node);
}

Z3ASTHandle Z3GoalHandle::getFormula(unsigned index) const {
  assert(index < getNumFormulas() && "bad index");
  return Z3ASTHandle(::Z3_goal_formula(context, node, index), context);
}

// Z3TacticHandle
template <> void Z3NodeHandle<Z3_tactic>::dump() const {
  llvm::errs() << "Z3TacticHandle:\n" << toStr() << "\n";
}

template <> std::string Z3NodeHandle<Z3_tactic>::toStr() const {
  return "<not-available>"; // FIXME
}

Z3ApplyResultHandle Z3TacticHandle::apply(Z3GoalHandle goal) {
  return Z3ApplyResultHandle(::Z3_tactic_apply(context, node, goal), context);
}

Z3ApplyResultHandle Z3TacticHandle::applyWithParams(Z3GoalHandle goal,
                                                    Z3ParamsHandle params) {
  return Z3ApplyResultHandle(::Z3_tactic_apply_ex(context, node, goal, params),
                             context);
}

// Z3ApplyResultHandle
template <> void Z3NodeHandle<Z3_apply_result>::dump() const {
  llvm::errs() << "Z3ApplyResultHandle:\n" << toStr() << "\n";
}

template <> std::string Z3NodeHandle<Z3_apply_result>::toStr() const {
  return ::Z3_apply_result_to_string(context, node);
}

unsigned Z3ApplyResultHandle::getNumGoals() const {
  return ::Z3_apply_result_get_num_subgoals(context, node);
}

Z3GoalHandle Z3ApplyResultHandle::getGoal(unsigned index) const {
  assert(index < getNumGoals());
  return Z3GoalHandle(::Z3_apply_result_get_subgoal(context, node, index),
                      context);
}

void Z3ApplyResultHandle::collectAllFormulas(
    std::vector<Z3ASTHandle> &formulas) const {
  for (unsigned subGoalIndex = 0; subGoalIndex < this->getNumGoals();
       ++subGoalIndex) {
    Z3GoalHandle subGoal = this->getGoal(subGoalIndex);
    for (unsigned formulaIndex = 0; formulaIndex < subGoal.getNumFormulas();
         ++formulaIndex) {
      formulas.push_back(subGoal.getFormula(formulaIndex));
    }
  }
}

Z3ModelHandle
Z3ApplyResultHandle::convertModelForGoal(unsigned index,
                                         Z3ModelHandle toConvert) {
  assert(index < getNumGoals());
  assert(!toConvert.isNull());
  assert(toConvert.getContext() == context);
  return Z3ModelHandle(
      Z3_apply_result_convert_model(context, node, index, toConvert), context);
}
}
}
