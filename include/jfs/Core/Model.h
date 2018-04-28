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
#ifndef JFS_CORE_MODEL_H
#define JFS_CORE_MODEL_H
#include "jfs/Core/Z3Node.h"
#include <string>

namespace jfs {
namespace core {

class Model {
protected:
  Z3ModelHandle model;
  Model(Z3ModelHandle m) : model(m) {}
  Model();
  virtual ~Model();

public:
  // Do we really need this method?
  virtual Z3ASTHandle getAssignment(Z3FuncDeclHandle);
  virtual Z3ModelHandle getRepr() { return model; }
  virtual std::string getSMTLIBString();
};

} // namespace core
} // namespace jfs
#endif
