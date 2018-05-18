//===----------------------------------------------------------------------===//
//
//                        JFS - The JIT Fuzzing Solver
//
// Copyright 2018 J. Ryan Stinnett
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//

#ifndef PRF_TEST_INPUT_H
#define PRF_TEST_INPUT_H

#include <random>
#include <vector>

namespace prf {

class TestInput {
private:
  std::vector<uint8_t> data;
  std::mt19937 randGen;

public:
  TestInput(std::size_t length) : data(length) {}
  void generate();
  const uint8_t* get() { return data.data(); }
  std::size_t size() { return data.size(); }
};

} // prf

#endif // PRF_TEST_INPUT_H