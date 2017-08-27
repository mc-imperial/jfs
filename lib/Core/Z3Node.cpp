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
#include "jfs/Core/Z3Node.h"
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

template <> void Z3NodeHandle<Z3_model>::dump() const {
  llvm::errs() << "Z3ModelHandle:\n" << toStr() << "\n";
}
template <> std::string Z3NodeHandle<Z3_model>::toStr() const {
  // FIXME: We need to grab a lock over all calls to `Z3_*_to_string()`
  // to make this thread safe.
  return ::Z3_model_to_string(context, node);
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
}
}
