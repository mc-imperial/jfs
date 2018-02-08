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
};
} // namespace cxxfb
} // namespace jfs
#endif
