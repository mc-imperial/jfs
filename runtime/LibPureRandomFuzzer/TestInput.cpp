//===----------------------------------------------------------------------===//
//
//                                     JFS
//
// Copyright 2018 J. Ryan Stinnett
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//

#include "TestInput.h"

#include <algorithm>
#include <cstring>

namespace prf {

void TestInput::generate() {
  uint8_t* dest = data.data();
  for (uint i = 0; i < data.size(); i += 4) {
    uint32_t newData = randGen();
    std::size_t length = std::min(data.size() - i, 4UL);
    std::memcpy(dest + i, &newData, length);
  }
}

} // prf