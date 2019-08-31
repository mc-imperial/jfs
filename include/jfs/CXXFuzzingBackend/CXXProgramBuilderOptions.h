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
#ifndef JFS_CXX_FUZZING_BACKEND_CXX_PROGRAM_BUILDER_OPTIONS_H
#define JFS_CXX_FUZZING_BACKEND_CXX_PROGRAM_BUILDER_OPTIONS_H
#include <memory>

namespace jfs {
namespace cxxfb {

class CXXProgramBuilderOptions {
private:
  bool recordMaxNumSatisifiedConstraints = false;
  bool recordNumberOfInputs = false;
  bool recordNumberOfWrongSizedInputs = false;
  bool traceIncreaseMaxNumSatisfiedConstraints = false;
  bool traceWrongSizedInputs = false;

public:
  CXXProgramBuilderOptions();
  bool getRecordMaxNumSatisfiedConstraints() const {
    return recordMaxNumSatisifiedConstraints;
  }
  void setRecordMaxNumSatisfiedConstraints(bool v) {
    recordMaxNumSatisifiedConstraints = v;
  }

  bool getRecordNumberOfInputs() const { return recordNumberOfInputs; }
  void setRecordNumberOfInputs(bool v) { recordNumberOfInputs = v; }

  bool getRecordNumberOfWrongSizedInputs() const {
    return recordNumberOfWrongSizedInputs;
  }
  void setRecordNumberOfWrongSizedInputs(bool v) {
    recordNumberOfWrongSizedInputs = v;
  }

  bool getTraceIncreaseMaxNumSatisfiedConstraints() const {
    return traceIncreaseMaxNumSatisfiedConstraints;
  }
  void setTraceIncreaseMaxNumSatisfiedConstraints(bool v) {
    traceIncreaseMaxNumSatisfiedConstraints = v;
  }

  bool getTraceWrongSizedInputs() const { return traceWrongSizedInputs; }
  void setTraceWrongSizedInputs(bool v) { traceWrongSizedInputs = v; }

  enum class BranchEncodingTy {
    // Fail fast encoding
    //
    // If a constraint is found to be unsatisfiable fuzzing
    // the current input is immediately halted without checking
    // the remaining constraints.
    //
    // There are several problems with this encoding.
    //
    // * It is sensitive to the order constraints are checked.
    // * Potentially prevents partially satisfying inputs from
    //   being observed which then prevents the input corpus
    //   from growing.
    //
    //   In essence the encoding forces constraints to be solved
    //   in particular order.
    FAIL_FAST,
    // Try all encoding
    //
    // This is the "Serebryany encoding", named after
    // Kostya Serebryany who proposed this.
    //
    // This encoding evaluates all constraints. This encoding
    // addresses problems from the `TRY_ALL` encoding because
    // this approach means that the order that constraints are
    // checked do not matter.
    //
    // However it introduces a new problem in that in some cases
    // inputs that increase the number of satisfied constraints
    // are not added to the input corpus.
    //
    // For example. Let's say there are three constraints C0, C1, C2, C3.
    // Let's say that Input A satisfies {C0, C1} and Input B satisfies {C2}. So
    // Inputs A and B get added to the corpus. Then we try Input C which
    // satisfies {C0, C1, C2}. This input will not be added to the input corpus
    // because the branches for C0, C1, and C2 were already covered.
    TRY_ALL,
    // Try all IMNCSF
    //
    // IMNCSF - Increase in Maximum Number of Constraints Solved is a Feature
    //
    // This is the "Cadar encoding", named after Cristian Cadar
    // who proposed this.
    //
    // This is an enhancement to the `TRY_ALL` encoding that addresses
    // the issue where some inputs that increase the number of solved
    // constraints
    // might not be added to the corpus.
    //
    // This relies on an experimental LibFuzzer feature to treat an increase in
    // the number of solved constraints as a "feature".
    //
    // At the time of writing this feature on works on Linux.
    //
    // FIXME: We should guard this so it is only available on Linux.
    TRY_ALL_IMNCSF,
  };

private:
  BranchEncodingTy branchEncoding = BranchEncodingTy::FAIL_FAST;

public:
  BranchEncodingTy getBranchEncoding() const { return branchEncoding; }
  void setBranchEncoding(BranchEncodingTy ty) { branchEncoding = ty; }
};
} // namespace cxxfb
} // namespace jfs
#endif
