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
#ifndef JFS_CORE_SIMPLE_MODEL_H
#define JFS_CORE_SIMPLE_MODEL_H
#include "jfs/Core/Model.h"

namespace jfs {
namespace core {

// A model that on creation is empty
class SimpleModel : public Model {
public:
  SimpleModel(JFSContext& ctx);
};

} // namespace core
} // namespace jfs

#endif
